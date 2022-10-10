use ansi_term::{ANSIString, Color, Style};
use log::{Level, LevelFilter, Log, Metadata, Record};

pub struct Logger {
    colors_enabled: bool,
}

impl Logger {
    fn prefix(&self, level: Level) -> ANSIString<'static> {
        let style = if self.colors_enabled {
            let color = match level {
                Level::Error => Color::Red,
                Level::Warn => Color::Yellow,
                Level::Info => Color::Cyan,
                Level::Debug => Color::Purple,
                Level::Trace => Color::Green,
            };
            color.bold()
        } else {
            Style::new()
        };
        style.paint(format!("[{}]", level))
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
