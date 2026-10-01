use log::{Level, LevelFilter, Log, Metadata, Record};
use owo_colors::{AnsiColors, OwoColorize};

pub struct Logger {
    colors_enabled: bool,
}

impl Logger {
    fn prefix(&self, level: Level) -> String {
        let text = format!("{}:", level).to_lowercase();
        if !self.colors_enabled {
            return text;
        }
        let color = match level {
            Level::Error => AnsiColors::Red,
            Level::Warn => AnsiColors::Yellow,
            Level::Info => AnsiColors::Cyan,
            Level::Debug => AnsiColors::Magenta,
            Level::Trace => AnsiColors::Green,
        };
        text.color(color).bold().to_string()
    }
}

impl Log for Logger {
    fn enabled(&self, _: &Metadata) -> bool {
        true
    }

    fn log(&self, record: &Record) {
        eprintln!("{} {}", self.prefix(record.level()), record.args());
    }

    fn flush(&self) {}
}

pub fn init(max_level: LevelFilter, colors_enabled: bool) {
    log::set_boxed_logger(Box::new(Logger { colors_enabled })).expect("couldn't set up logger");
    log::set_max_level(max_level);
}
