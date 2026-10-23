use serde::Deserialize;
use serde_json::Value;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum VerifyOn {
    /// Verify after each edit, debounced.
    Change,
    /// Type check after each edit, verify on open and save.
    Save,
    /// Type check only; verification runs through commands.
    Never,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct Config {
    pub dafny_path: String,
    pub verify_on: VerifyOn,
    pub debounce_ms: u64,
    /// Seconds per assertion batch, passed as --verification-time-limit.
    pub verification_time_limit: Option<u32>,
    /// Passed as --cores. A number or a percentage like "50%".
    pub cores: Option<Value>,
    /// Appended to every dafny invocation.
    pub extra_args: Vec<String>,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            dafny_path: "dafny".to_string(),
            verify_on: VerifyOn::Save,
            debounce_ms: 300,
            verification_time_limit: None,
            cores: None,
            extra_args: Vec::new(),
        }
    }
}

impl Config {
    /// Accepts the settings object either as-is or nested under "dafny-lsp" / "dafnyLsp".
    /// Returns None when the value holds no settings for this server.
    pub fn from_value(value: &Value) -> Option<Result<Config, serde_json::Error>> {
        let inner = value.get("dafny-lsp").or_else(|| value.get("dafnyLsp")).unwrap_or(value);
        match inner {
            Value::Object(map) if !map.is_empty() => Some(serde_json::from_value(inner.clone())),
            _ => None,
        }
    }

    pub fn cores_arg(&self) -> Option<String> {
        match &self.cores {
            Some(Value::Number(n)) => Some(n.to_string()),
            Some(Value::String(s)) if !s.is_empty() => Some(s.clone()),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn reads_nested_and_flat_settings() {
        let c = Config::from_value(&json!({"dafny-lsp": {"verifyOn": "change", "cores": 2}})).unwrap().unwrap();
        assert_eq!(c.verify_on, VerifyOn::Change);
        assert_eq!(c.cores_arg().as_deref(), Some("2"));
        let c = Config::from_value(&json!({"verificationTimeLimit": 10})).unwrap().unwrap();
        assert_eq!(c.verification_time_limit, Some(10));
        assert_eq!(c.dafny_path, "dafny");
        assert!(Config::from_value(&json!({})).is_none());
        assert!(Config::from_value(&json!(null)).is_none());
    }
}
