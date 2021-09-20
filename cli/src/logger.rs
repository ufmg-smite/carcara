use ansi_term::{ANSIString, Color};
use log::{Level, LevelFilter, Log, Metadata, Record};

pub struct Logger;

impl Logger {
    fn prefix(level: Level) -> ANSIString<'static> {
        let color = match level {
            Level::Error => Color::Red,
            Level::Warn => Color::Yellow,
            Level::Info => Color::Cyan,
            Level::Debug => Color::Purple,
            Level::Trace => Color::Green,
        };
        color.bold().paint(format!("[{}]", level))
    }
}

impl Log for Logger {
    fn enabled(&self, _: &Metadata) -> bool {
        true
    }

    fn log(&self, record: &Record) {
        eprintln!("{} {}", Self::prefix(record.level()), record.args());
    }

    fn flush(&self) {}
}

pub fn init() {
    log::set_boxed_logger(Box::new(Logger {})).expect("couldn't set up logger");
    log::set_max_level(LevelFilter::Info);
}
