//! Integration tests for VFS + Salsa interaction
//!
//! These tests verify that the VFS correctly feeds Salsa and that
//! incremental compilation works as expected.

use hwml_db::db::{get_line_info, HwmlDatabase};
use hwml_vfs::{MemoryVfs, OsVfs, Vfs};
use std::path::Path;
use tempfile::TempDir;

/// Test that MemoryVfs correctly triggers Salsa invalidation
#[test]
fn test_memory_vfs_salsa_invalidation() {
    let mut vfs = MemoryVfs::new();
    vfs.add_file("/test.hwml", "original content");

    let mut db = HwmlDatabase::new();

    // Load the file
    let file = vfs
        .get_or_create_file(&db, Path::new("/test.hwml"))
        .unwrap();
    assert_eq!(file.text(&db), "original content");

    // Update the file content
    vfs.update_file(
        &mut db,
        Path::new("/test.hwml"),
        "modified content".to_string(),
    )
    .unwrap();

    // Verify Salsa sees the change
    assert_eq!(file.text(&db), "modified content");
}

/// Test that OsVfs correctly triggers Salsa invalidation
#[test]
fn test_os_vfs_salsa_invalidation() {
    let temp = TempDir::new().unwrap();
    let path = temp.path().join("test.hwml");
    std::fs::write(&path, "original content").unwrap();

    let mut vfs = OsVfs::new();
    let mut db = HwmlDatabase::new();

    // Load the file
    let file = vfs.get_or_create_file(&db, &path).unwrap();
    assert_eq!(file.text(&db), "original content");

    // Update the file content (simulating LSP edit)
    vfs.update_file(&mut db, &path, "modified content".to_string())
        .unwrap();

    // Verify Salsa sees the change
    assert_eq!(file.text(&db), "modified content");
}

/// Test multiple file loads with caching
#[test]
fn test_multiple_files_with_caching() {
    let mut vfs = MemoryVfs::new();
    vfs.add_file("/a.hwml", "content A");
    vfs.add_file("/b.hwml", "content B");
    vfs.add_file("/c.hwml", "content C");

    let db = HwmlDatabase::new();

    // Load all files
    let file_a1 = vfs.get_or_create_file(&db, Path::new("/a.hwml")).unwrap();
    let file_b = vfs.get_or_create_file(&db, Path::new("/b.hwml")).unwrap();
    let file_c = vfs.get_or_create_file(&db, Path::new("/c.hwml")).unwrap();

    // Load file A again - should return cached version
    let file_a2 = vfs.get_or_create_file(&db, Path::new("/a.hwml")).unwrap();

    // Verify same Salsa input ID
    assert_eq!(file_a1, file_a2);

    // Verify content
    assert_eq!(file_a1.text(&db), "content A");
    assert_eq!(file_b.text(&db), "content B");
    assert_eq!(file_c.text(&db), "content C");
}

/// Test incremental updates to multiple files
#[test]
fn test_incremental_multi_file_updates() {
    let mut vfs = MemoryVfs::new();
    vfs.add_file("/main.hwml", "import lib");
    vfs.add_file("/lib.hwml", "def x := 42");

    let mut db = HwmlDatabase::new();

    let main_file = vfs
        .get_or_create_file(&db, Path::new("/main.hwml"))
        .unwrap();
    let lib_file = vfs.get_or_create_file(&db, Path::new("/lib.hwml")).unwrap();

    assert_eq!(main_file.text(&db), "import lib");
    assert_eq!(lib_file.text(&db), "def x := 42");

    // Update lib file
    vfs.update_file(&mut db, Path::new("/lib.hwml"), "def x := 100".to_string())
        .unwrap();

    // Main file should remain unchanged
    assert_eq!(main_file.text(&db), "import lib");
    // Lib file should be updated
    assert_eq!(lib_file.text(&db), "def x := 100");

    // Update main file
    vfs.update_file(&mut db, Path::new("/main.hwml"), "import lib2".to_string())
        .unwrap();

    assert_eq!(main_file.text(&db), "import lib2");
    assert_eq!(lib_file.text(&db), "def x := 100");
}

/// Test that path canonicalization works correctly in OsVfs
#[test]
fn test_os_vfs_path_canonicalization() {
    let temp = TempDir::new().unwrap();
    let file_path = temp.path().join("test.hwml");
    std::fs::write(&file_path, "test content").unwrap();

    let mut vfs = OsVfs::new();
    let db = HwmlDatabase::new();

    // Load with canonical path
    let file1 = vfs.get_or_create_file(&db, &file_path).unwrap();

    // Load again with same path - should return cached
    let file2 = vfs.get_or_create_file(&db, &file_path).unwrap();

    assert_eq!(file1, file2);
    assert_eq!(file1.text(&db), "test content");
}

/// Test error handling for missing files
#[test]
fn test_memory_vfs_missing_file_error() {
    let mut vfs = MemoryVfs::new();
    let db = HwmlDatabase::new();

    let result = vfs.get_or_create_file(&db, Path::new("/missing.hwml"));
    assert!(result.is_err());
    assert!(matches!(result, Err(hwml_vfs::VfsError::FileNotFound(_))));
}

/// Test that Salsa queries are invalidated when file content changes
#[test]
fn test_salsa_query_invalidation() {
    let mut vfs = MemoryVfs::new();
    vfs.add_file("/test.hwml", "line 1\nline 2\nline 3");

    let mut db = HwmlDatabase::new();

    // Load file and compute line info
    let file = vfs
        .get_or_create_file(&db, Path::new("/test.hwml"))
        .unwrap();
    let line_info_1 = get_line_info(&db, file);

    // Check line start positions for 3-line file
    assert_eq!(line_info_1.line_start(0), 0);
    assert_eq!(line_info_1.line_start(1), 7); // after "line 1\n"

    // Update file to have 5 lines
    vfs.update_file(
        &mut db,
        Path::new("/test.hwml"),
        "line 1\nline 2\nline 3\nline 4\nline 5".to_string(),
    )
    .unwrap();

    // Query should be invalidated and return new line info
    let line_info_2 = get_line_info(&db, file);

    // Verify the file content changed by checking offset positions
    assert_eq!(line_info_2.line_start(0), 0);
    assert_eq!(line_info_2.line_start(4), 28); // Start of "line 5"

    // Verify they're different instances (query was re-executed)
    assert_ne!(format!("{:?}", line_info_1), format!("{:?}", line_info_2));
}

/// Test that queries on unchanged files are NOT invalidated
#[test]
fn test_salsa_query_caching() {
    let mut vfs = MemoryVfs::new();
    vfs.add_file("/a.hwml", "content A line 1\ncontent A line 2");
    vfs.add_file("/b.hwml", "content B line 1\ncontent B line 2");

    let mut db = HwmlDatabase::new();

    let file_a = vfs.get_or_create_file(&db, Path::new("/a.hwml")).unwrap();
    let file_b = vfs.get_or_create_file(&db, Path::new("/b.hwml")).unwrap();

    // Compute line info for both files
    let line_info_a1 = get_line_info(&db, file_a);
    let line_info_b1 = get_line_info(&db, file_b);

    // Update only file B to have 3 lines
    vfs.update_file(
        &mut db,
        Path::new("/b.hwml"),
        "line 1\nline 2\nline 3".to_string(),
    )
    .unwrap();

    // Query file A again - should be cached (not re-executed)
    let line_info_a2 = get_line_info(&db, file_a);

    // Query file B - should be invalidated
    let line_info_b2 = get_line_info(&db, file_b);

    // File A's query result should be the same (cached)
    // Both should have same line starts since content didn't change
    assert_eq!(line_info_a1.line_start(0), line_info_a2.line_start(0));
    assert_eq!(line_info_a1.line_start(1), line_info_a2.line_start(1));

    // File B's query result should be different (invalidated)
    // Different line structure now (3 lines vs 2)
    assert_ne!(format!("{:?}", line_info_b1), format!("{:?}", line_info_b2));
}
