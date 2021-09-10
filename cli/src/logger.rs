use log::{Level, LevelFilter, Log, Metadata, Record};

pub struct Logger;

impl Log for Logger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= Level::Warn
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            eprintln!("[{}] {}", record.level(), record.args());
        }
    }

    fn flush(&self) {}
}

pub fn init() {
    log::set_boxed_logger(Box::new(Logger {})).expect("couldn't set up logger");
    log::set_max_level(LevelFilter::Info);
}
