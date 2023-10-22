use super::intern::InternStr;
use std::fmt;
use std::sync::atomic;

static mut COUNTER: atomic::AtomicUsize = atomic::AtomicUsize::new(0);

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Ident {
    name: InternStr,
    index: usize,
}

impl Ident {
    pub fn new<S: AsRef<str>>(s: &S) -> Ident {
        unsafe {
            let name = InternStr::new(s.as_ref());
            let index = COUNTER.fetch_add(1, atomic::Ordering::Relaxed);
            Ident { name, index }
        }
    }

    pub fn uniquify(&self) -> Ident {
        unsafe {
            let name = self.name;
            let index = COUNTER.fetch_add(1, atomic::Ordering::Relaxed);
            Ident { name, index }
        }
    }

    pub fn as_str(&self) -> &'static str {
        self.name.as_str()
    }
}

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}_{}", self.name, self.index)
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl AsRef<str> for Ident {
    fn as_ref(&self) -> &str {
        self.name.as_str()
    }
}

#[test]
fn uniquify_test() {
    // test function `Ident::uniquify`
    let baz: &str = "baz";
    let s1 = InternStr::new(&baz);
    let x1 = Ident::new(&s1).uniquify();
    let x2 = Ident::new(&s1).uniquify();
    assert_ne!(x1, x2);
    assert_eq!(x1.name, x2.name);
}
