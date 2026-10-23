use std::path::{Path, PathBuf};

use globset::{Glob, GlobSet, GlobSetBuilder};
use serde::Deserialize;

pub const PROJECT_FILE: &str = "dfyconfig.toml";
const MAX_PROJECT_FILES: usize = 5000;

/// A Dafny project defined by a dfyconfig.toml file.
#[derive(Debug, Clone)]
pub struct Project {
    pub dir: PathBuf,
    pub files: Vec<PathBuf>,
    /// The [options] table as command line flags.
    pub args: Vec<String>,
}

#[derive(Deserialize, Default)]
struct RawProject {
    includes: Option<Vec<String>>,
    excludes: Option<Vec<String>>,
    options: Option<toml::Table>,
}

/// The nearest dfyconfig.toml in `dir` or one of its parents.
pub fn find_project_file(dir: &Path) -> Option<PathBuf> {
    dir.ancestors().map(|d| d.join(PROJECT_FILE)).find(|p| p.is_file())
}

pub fn load(config_path: &Path) -> Result<Project, String> {
    let dir = config_path.parent().unwrap_or(Path::new(".")).to_path_buf();
    let raw_text = std::fs::read_to_string(config_path).map_err(|e| e.to_string())?;
    let raw: RawProject = toml::from_str(&raw_text).map_err(|e| e.to_string())?;
    let includes = build_globs(raw.includes.unwrap_or_else(|| vec!["**/*.dfy".to_string()]))?;
    let excludes = build_globs(raw.excludes.unwrap_or_default())?;

    let mut files = Vec::new();
    let walker = ignore::WalkBuilder::new(&dir).standard_filters(false).hidden(true).build();
    for entry in walker.flatten() {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("dfy") {
            continue;
        }
        let Ok(rel) = path.strip_prefix(&dir) else { continue };
        if includes.is_match(rel) && !excludes.is_match(rel) {
            files.push(path.to_path_buf());
            if files.len() >= MAX_PROJECT_FILES {
                break;
            }
        }
    }
    files.sort();

    let args = raw.options.map(|o| option_args(&o)).unwrap_or_default();
    Ok(Project { dir, files, args })
}

fn build_globs(patterns: Vec<String>) -> Result<GlobSet, String> {
    let mut builder = GlobSetBuilder::new();
    for p in patterns {
        builder.add(Glob::new(&p).map_err(|e| e.to_string())?);
    }
    builder.build().map_err(|e| e.to_string())
}

fn option_args(options: &toml::Table) -> Vec<String> {
    let mut args = Vec::new();
    for (key, value) in options {
        match value {
            toml::Value::Boolean(true) => args.push(format!("--{key}")),
            toml::Value::Boolean(false) => args.push(format!("--{key}=false")),
            toml::Value::Array(items) => {
                for item in items {
                    args.push(format!("--{key}={}", scalar(item)));
                }
            }
            other => args.push(format!("--{key}={}", scalar(other))),
        }
    }
    args
}

fn scalar(v: &toml::Value) -> String {
    match v {
        toml::Value::String(s) => s.clone(),
        other => other.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn options_become_flags() {
        let table: toml::Table = toml::from_str(
            "warn-shadowing = true\nallow-warnings = false\ncores = 2\nlibrary = [\"a.dfy\", \"b.dfy\"]\nfunction-syntax = \"4\"",
        )
        .unwrap();
        let mut args = option_args(&table);
        args.sort();
        assert_eq!(
            args,
            vec![
                "--allow-warnings=false",
                "--cores=2",
                "--function-syntax=4",
                "--library=a.dfy",
                "--library=b.dfy",
                "--warn-shadowing",
            ]
        );
    }
}
