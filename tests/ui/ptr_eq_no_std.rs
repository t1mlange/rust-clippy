#![warn(clippy::ptr_eq)]
#![no_std]
#![feature(lang_items)]

use core::panic::PanicInfo;

#[lang = "eh_personality"]
extern "C" fn eh_personality() {}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    loop {}
}

macro_rules! mac {
    ($a:expr, $b:expr) => {
        $a as *const _ as usize == $b as *const _ as usize
    };
}

macro_rules! another_mac {
    ($a:expr, $b:expr) => {
        $a as *const _ == $b as *const _
    };
}

fn main() {
    let a = &[1, 2, 3];
    let b = &[1, 2, 3];

    let _ = a as *const _ as usize == b as *const _ as usize;
    //~^ ptr_eq
    let _ = a as *const _ == b as *const _;
    //~^ ptr_eq

    // Do not lint: the rhs conversion is needed
    let _ = a.as_ptr() == b as *const _;

    // Do not lint: we have two raw pointers already
    let _ = a.as_ptr() == b.as_ptr();

    // Do not lint
    let _ = mac!(a, b);
    let _ = another_mac!(a, b);

    let a = &mut [1, 2, 3];
    let b = &mut [1, 2, 3];

    // Do not lint: the rhs conversion is needed
    let _ = a.as_mut_ptr() == b as *mut [i32] as *mut _;

    // Do not lint: we have two raw pointers already
    let _ = a.as_mut_ptr() == b.as_mut_ptr();

    let _ = a == b;
    let _ = core::ptr::eq(a, b);
}
