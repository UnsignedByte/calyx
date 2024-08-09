pub use super::{CalyxFFI, CalyxFFIComponent, CalyxFFIComponentRef};
pub use calyx_ffi_macro::{calyx_ffi, calyx_ffi_test, calyx_ffi_tests};

#[macro_export]
macro_rules! declare_calyx_interface {
    ($name:ident($($input:ident),*) -> ($($output:ident),*)) => {
        pub trait $name: CalyxFFIComponent {
            $(
                fn $input(&mut self) -> &mut u64;
            )*
            $(
                fn $output(&self) -> u64;
            )*
        }
    };
}
