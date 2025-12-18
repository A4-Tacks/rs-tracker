#[derive(Debug, PartialEq, Eq)]
pub enum Debug {
    Inline,
    Expand,
    Disable,
}

impl Default for Debug {
    fn default() -> Self {
        Self::Disable
    }
}

#[derive(Debug, Default)]
pub struct Config {
    pub debug: Debug,
    pub stderr: bool,
    pub label_stmt: bool,
}
