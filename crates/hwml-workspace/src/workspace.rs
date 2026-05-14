use std::collections::HashMap;
use std::path::{Path, PathBuf};

use indexmap::IndexMap;
use petgraph::algo::toposort;
use petgraph::graph::DiGraph;
use thiserror::Error;

use crate::manifest::{load_manifest, LibraryDepSource, ManifestError};
use crate::{LibraryDep, LibraryManifest};

#[derive(Debug, Error)]
pub enum WorkspaceError {
    #[error("Manifest not found at {0}")]
    ManifestNotFound(PathBuf),
    #[error("Dependency cycle detected: {0}")]
    CycleDetected(String),
    #[error("Library '{name}' found at two different paths: {first} and {second}")]
    DuplicateLibrary {
        name: String,
        first: PathBuf,
        second: PathBuf,
    },
    #[error("Failed to find manifest for dependency '{name}' of '{parent}': {source}")]
    DepManifestNotFound {
        name: String,
        parent: String,
        #[source]
        source: ManifestError,
    },
    #[error("{0}")]
    Manifest(#[from] ManifestError),
}

pub struct Workspace {
    /// All libraries keyed by name, including transitive dependencies.
    pub libraries: IndexMap<String, LibraryManifest>,
    /// Topological order: leaves (no deps) first, root last.
    pub topo_order: Vec<String>,
}

impl Workspace {
    /// Load a workspace starting from the given manifest file.
    pub fn load(root_manifest: PathBuf) -> Result<Workspace, WorkspaceError> {
        let mut libraries: IndexMap<String, LibraryManifest> = IndexMap::new();
        // Maps canonical root path → library name (for dedup detection).
        let mut root_to_name: HashMap<PathBuf, String> = HashMap::new();

        load_recursive(&root_manifest, None, &mut libraries, &mut root_to_name)?;

        let topo_order = topo_sort(&libraries)?;

        Ok(Workspace {
            libraries,
            topo_order,
        })
    }

    /// Search upward from `start` for `hwml.toml` (cargo-style discovery).
    pub fn find_manifest(start: &Path) -> Option<PathBuf> {
        let mut dir = if start.is_file() {
            start.parent()?.to_owned()
        } else {
            start.to_owned()
        };
        loop {
            let candidate = dir.join("hwml.toml");
            if candidate.exists() {
                return Some(candidate);
            }
            if !dir.pop() {
                return None;
            }
        }
    }
}

// ─── Recursive manifest loading ───────────────────────────────────────────────

fn load_recursive(
    manifest_path: &Path,
    _parent_name: Option<&str>,
    libraries: &mut IndexMap<String, LibraryManifest>,
    root_to_name: &mut HashMap<PathBuf, String>,
) -> Result<(), WorkspaceError> {
    if !manifest_path.exists() {
        return Err(WorkspaceError::ManifestNotFound(manifest_path.to_owned()));
    }

    let manifest = load_manifest(manifest_path)?;
    let name = manifest.name.clone();
    let root = manifest.root.clone();

    // Dedup check.
    if let Some(existing_name) = root_to_name.get(&root) {
        if *existing_name != name {
            return Err(WorkspaceError::DuplicateLibrary {
                name: name.clone(),
                first: root.clone(),
                second: manifest_path.to_owned(),
            });
        }
        // Already loaded this library — skip.
        return Ok(());
    }

    if libraries.contains_key(&name) {
        // Same name at different path.
        let existing_root = &libraries[&name].root;
        if *existing_root != root {
            return Err(WorkspaceError::DuplicateLibrary {
                name,
                first: existing_root.clone(),
                second: root,
            });
        }
        return Ok(());
    }

    root_to_name.insert(root, name.clone());
    let deps = manifest.dependencies.clone();
    libraries.insert(name.clone(), manifest);

    // Recurse into dependencies.
    for dep in &deps {
        let dep_manifest_path =
            resolve_dep_manifest_path(dep, &libraries[&name].root).ok_or_else(|| {
                WorkspaceError::DepManifestNotFound {
                    name: dep.name.clone(),
                    parent: name.clone(),
                    source: ManifestError::MissingName(PathBuf::from(&dep.name)),
                }
            })?;
        load_recursive(&dep_manifest_path, Some(&name), libraries, root_to_name).map_err(|e| {
            match e {
                WorkspaceError::ManifestNotFound(p) => WorkspaceError::DepManifestNotFound {
                    name: dep.name.clone(),
                    parent: name.clone(),
                    source: ManifestError::Io(
                        p,
                        std::io::Error::new(std::io::ErrorKind::NotFound, "manifest not found"),
                    ),
                },
                other => other,
            }
        })?;
    }

    Ok(())
}

fn resolve_dep_manifest_path(dep: &LibraryDep, parent_root: &Path) -> Option<PathBuf> {
    match &dep.source {
        LibraryDepSource::Path(rel) => Some(parent_root.join(rel).join("hwml.toml")),
        LibraryDepSource::Registry { .. } => {
            // Registry resolution not yet implemented. Would check installed packages.
            None
        }
    }
}

// ─── Topological sort ─────────────────────────────────────────────────────────

fn topo_sort(libraries: &IndexMap<String, LibraryManifest>) -> Result<Vec<String>, WorkspaceError> {
    let mut graph: DiGraph<&str, ()> = DiGraph::new();
    let mut name_to_node = HashMap::new();

    for name in libraries.keys() {
        let node = graph.add_node(name.as_str());
        name_to_node.insert(name.as_str(), node);
    }

    for (name, manifest) in libraries {
        let from = name_to_node[name.as_str()];
        for dep in &manifest.dependencies {
            if let Some(&to) = name_to_node.get(dep.name.as_str()) {
                // Edge from dependent → dependency (so topo gives leaves first).
                graph.add_edge(from, to, ());
            }
        }
    }

    toposort(&graph, None)
        .map(|order| {
            order
                .into_iter()
                .rev()
                .map(|n| graph[n].to_owned())
                .collect()
        })
        .map_err(|cycle| {
            let name = graph[cycle.node_id()].to_owned();
            WorkspaceError::CycleDetected(name)
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn write(path: &Path, content: &str) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(path, content).unwrap();
    }

    #[test]
    fn single_library_no_deps() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        write(&root.join("hwml.toml"), "[library]\nname = \"mylib\"\n");
        write(&root.join("a.hwml"), "");

        let ws = Workspace::load(root.join("hwml.toml")).unwrap();
        assert_eq!(ws.topo_order, vec!["mylib"]);
        assert_eq!(ws.libraries["mylib"].source_files.len(), 1);
    }

    #[test]
    fn two_libraries_dep_order() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();

        write(
            &root.join("prelude/hwml.toml"),
            "[library]\nname = \"prelude\"\n",
        );
        write(&root.join("prelude/types.hwml"), "");

        write(
            &root.join("mylib/hwml.toml"),
            "[library]\nname = \"mylib\"\n\n[dependencies]\nprelude = { path = \"../prelude\" }\n",
        );
        write(&root.join("mylib/main.hwml"), "");

        let ws = Workspace::load(root.join("mylib/hwml.toml")).unwrap();
        // prelude must come before mylib
        let prelude_pos = ws.topo_order.iter().position(|n| n == "prelude").unwrap();
        let mylib_pos = ws.topo_order.iter().position(|n| n == "mylib").unwrap();
        assert!(prelude_pos < mylib_pos);
    }

    #[test]
    fn cycle_detected() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();

        write(
            &root.join("a/hwml.toml"),
            "[library]\nname = \"a\"\n\n[dependencies]\nb = { path = \"../b\" }\n",
        );
        write(
            &root.join("b/hwml.toml"),
            "[library]\nname = \"b\"\n\n[dependencies]\na = { path = \"../a\" }\n",
        );
        write(&root.join("a/a.hwml"), "");
        write(&root.join("b/b.hwml"), "");

        let result = Workspace::load(root.join("a/hwml.toml"));
        assert!(matches!(result, Err(WorkspaceError::CycleDetected(_))));
    }

    #[test]
    fn find_manifest_searches_upward() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        write(&root.join("hwml.toml"), "[library]\nname = \"x\"\n");
        let subdir = root.join("a/b/c");
        fs::create_dir_all(&subdir).unwrap();

        let found = Workspace::find_manifest(&subdir).unwrap();
        assert_eq!(found, root.join("hwml.toml"));
    }

    #[test]
    fn explicit_sources_respected() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        write(
            &root.join("hwml.toml"),
            "[library]\nname = \"x\"\n\n[sources]\nfiles = [\"b.hwml\", \"a.hwml\"]\n",
        );
        write(&root.join("a.hwml"), "");
        write(&root.join("b.hwml"), "");

        let ws = Workspace::load(root.join("hwml.toml")).unwrap();
        let files = &ws.libraries["x"].source_files;
        // b.hwml first because that's the declared order
        assert!(files[0].ends_with("b.hwml"));
        assert!(files[1].ends_with("a.hwml"));
    }
}
