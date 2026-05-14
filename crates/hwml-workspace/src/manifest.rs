use std::path::{Path, PathBuf};

use serde::Deserialize;
use thiserror::Error;

#[derive(Debug, Clone)]
pub struct LibraryManifest {
    pub name: String,
    pub edition: u32,
    /// Canonical absolute path to library root directory.
    pub root: PathBuf,
    /// Source files in elaboration order, relative to root.
    pub source_files: Vec<PathBuf>,
    pub dependencies: Vec<LibraryDep>,
}

#[derive(Debug, Clone)]
pub struct LibraryDep {
    pub name: String,
    pub source: LibraryDepSource,
}

#[derive(Debug, Clone)]
pub enum LibraryDepSource {
    Path(PathBuf),
    Registry {
        version: String,
        source_hash: Option<[u8; 32]>,
    },
}

#[derive(Debug, Error)]
pub enum ManifestError {
    #[error("IO error reading {0}: {1}")]
    Io(PathBuf, #[source] std::io::Error),
    #[error("TOML parse error in {0}: {1}")]
    Toml(PathBuf, #[source] toml::de::Error),
    #[error("Library name missing in {0}")]
    MissingName(PathBuf),
}

// ─── Raw TOML deserialization types ──────────────────────────────────────────

#[derive(Deserialize)]
struct RawManifest {
    library: RawLibrary,
    #[serde(default)]
    dependencies: std::collections::HashMap<String, RawDep>,
    sources: Option<RawSources>,
}

#[derive(Deserialize)]
struct RawLibrary {
    name: String,
    #[serde(default = "default_edition")]
    edition: u32,
}

fn default_edition() -> u32 {
    1
}

#[derive(Deserialize)]
#[serde(untagged)]
enum RawDep {
    Version(String),
    Table(RawDepTable),
}

#[derive(Deserialize)]
struct RawDepTable {
    path: Option<String>,
    version: Option<String>,
}

#[derive(Deserialize)]
struct RawSources {
    #[serde(default)]
    files: Vec<String>,
}

// ─── Loading ─────────────────────────────────────────────────────────────────

pub fn load_manifest(manifest_path: &Path) -> Result<LibraryManifest, ManifestError> {
    let text = std::fs::read_to_string(manifest_path)
        .map_err(|e| ManifestError::Io(manifest_path.to_owned(), e))?;

    let raw: RawManifest =
        toml::from_str(&text).map_err(|e| ManifestError::Toml(manifest_path.to_owned(), e))?;

    let root = manifest_path
        .parent()
        .unwrap_or(Path::new("."))
        .canonicalize()
        .map_err(|e| ManifestError::Io(manifest_path.to_owned(), e))?;

    let source_files = resolve_source_files(&root, raw.sources, manifest_path)?;
    let dependencies = resolve_dependencies(&root, raw.dependencies);

    Ok(LibraryManifest {
        name: raw.library.name,
        edition: raw.library.edition,
        root,
        source_files,
        dependencies,
    })
}

fn resolve_source_files(
    root: &Path,
    raw: Option<RawSources>,
    manifest_path: &Path,
) -> Result<Vec<PathBuf>, ManifestError> {
    match raw {
        Some(RawSources { files }) if !files.is_empty() => {
            // Explicit list: use as-is (relative to root), canonicalize.
            files
                .into_iter()
                .map(|f| {
                    root.join(&f)
                        .canonicalize()
                        .map_err(|e| ManifestError::Io(root.join(f).to_owned(), e))
                })
                .collect()
        }
        _ => {
            // Auto-discover: all *.hwml files in root, sorted alphabetically.
            discover_hwml_files(root, manifest_path)
        }
    }
}

fn discover_hwml_files(root: &Path, manifest_path: &Path) -> Result<Vec<PathBuf>, ManifestError> {
    let mut files: Vec<PathBuf> = walkdir::WalkDir::new(root)
        .follow_links(false)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| {
            e.file_type().is_file() && e.path().extension().map_or(false, |ext| ext == "hwml")
        })
        .map(|e| e.into_path())
        .collect();

    // Sort for determinism.
    files.sort();

    // Canonicalize.
    files
        .into_iter()
        .map(|p| {
            p.canonicalize()
                .map_err(|e| ManifestError::Io(manifest_path.to_owned(), e))
        })
        .collect()
}

fn resolve_dependencies(
    root: &Path,
    raw: std::collections::HashMap<String, RawDep>,
) -> Vec<LibraryDep> {
    let mut deps: Vec<LibraryDep> = raw
        .into_iter()
        .map(|(name, dep)| {
            let source = match dep {
                RawDep::Version(v) => LibraryDepSource::Registry {
                    version: v,
                    source_hash: None,
                },
                RawDep::Table(t) => {
                    if let Some(path) = t.path {
                        LibraryDepSource::Path(root.join(path))
                    } else if let Some(version) = t.version {
                        LibraryDepSource::Registry {
                            version,
                            source_hash: None,
                        }
                    } else {
                        LibraryDepSource::Registry {
                            version: "*".to_owned(),
                            source_hash: None,
                        }
                    }
                }
            };
            LibraryDep { name, source }
        })
        .collect();

    // Sort for determinism.
    deps.sort_by(|a, b| a.name.cmp(&b.name));
    deps
}
