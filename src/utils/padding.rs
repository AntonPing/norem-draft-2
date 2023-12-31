use std::fmt::{self, Debug, Display};

use std::sync::atomic;

static mut INDT_LEVEL: atomic::AtomicUsize = atomic::AtomicUsize::new(0);

pub struct INDT;
pub struct DEDT;
pub struct NWLN;

impl Display for INDT {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe { INDT_LEVEL.fetch_add(1, atomic::Ordering::Relaxed) };
        Ok(())
    }
}

impl Display for DEDT {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe { INDT_LEVEL.fetch_sub(1, atomic::Ordering::Relaxed) };
        Ok(())
    }
}

impl Display for NWLN {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let level = unsafe { INDT_LEVEL.load(atomic::Ordering::Relaxed) };
        write!(f, "\n{:width$}", "", width = level * 2)
    }
}

impl Debug for INDT {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self)
    }
}

impl Debug for DEDT {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self)
    }
}

impl Debug for NWLN {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self)
    }
}
