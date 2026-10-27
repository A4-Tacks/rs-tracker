#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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

#[derive(Debug, Default, Clone)]
pub struct Config {
    pub debug: Debug,
    pub inline: bool,
    pub stderr: bool,
    pub label_stmt: bool,
    pub label_lets: bool,
    pub indent_name: bool,
    pub only_fn: bool,
}
