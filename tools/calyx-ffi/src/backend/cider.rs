use calyx_ir::Context;
use core::panic;
use interp::{
    flatten::{
        flat_ir,
        structures::{
            context::Context as CiderContext, environment::Simulator,
        },
    },
    values::Value,
};
use std::rc::Rc;

pub struct CiderFFIBackend {
    simulator: Simulator<Rc<CiderContext>>,
}

impl CiderFFIBackend {
    pub fn from(ctx: &Context, name: &'static str) -> Self {
        let ctx = flat_ir::translate(ctx);
        let simulator = Simulator::build_simulator(Rc::new(ctx), &None)
            .expect("we live on the edge");
        Self { simulator }
    }

    pub fn write_port(&mut self, name: &'static str, value: u64) {
        if name == "go" {
            return;
        }
        self.simulator.pin_value(name, Value::from(value, 64));
    }

    pub fn read_port(&self, name: &'static str) -> u64 {
        self.simulator
            .lookup_port_from_string(&String::from(name))
            .expect("wrong port name")
            .as_u64()
    }

    pub fn step(&mut self) {
        self.simulator.step().expect(
            "this function isn't documented so don't know what went wrong",
        );
    }

    pub fn go(&mut self) {
        self.simulator.run_program().expect("failed to run program");
        panic!();
        self.step(); // since griffin said so
    }
}

/// Runs the component using cider2.
#[macro_export]
macro_rules! cider_ffi_backend {
    (@user_data_type) => {
        $crate::backend::cider::CiderFFIBackend
    };
    (@init $dut:ident, $ctx:expr; $($input:ident),*; $($output:ident),*) => {
        $dut.user_data
            .write($crate::backend::cider::CiderFFIBackend::from(
                $ctx,
                $dut.name(),
            ));
    };
    (@reset $dut:ident; $($input:ident),*; $($output:ident),*) => {
        println!("cider_ffi_backend reset. doesn't work LOL");
        // $dut.done = 0;
        // $dut.reset = 1;
        // for i in 0..5 {
        //     $dut.tick();
        // }
        // $dut.reset = 0;
    };
    (@can_tick $dut:ident; $($input:ident),*; $($output:ident),*) => {
        true
    };
    (@tick $dut:ident; $($input:ident),*; $($output:ident),*) => {
        println!("cider_ffi_backend tick");
        let cider = unsafe { $dut.user_data.assume_init_mut() };
        $(
            cider.write_port(stringify!($input), $dut.$input);
        )*
        cider.step();
        $(
            $dut.$output = cider.read_port(stringify!($output));
        )*
    };
    (@go $dut:ident; $($input:ident),*; $($output:ident),*) => {
        println!("cider_ffi_backend go");
        let cider = unsafe { $dut.user_data.assume_init_mut() };
        $(
            cider.write_port(stringify!($input), $dut.$input);
        )*
        cider.go();
        $(
            $dut.$output = cider.read_port(stringify!($output));
        )*
    };
}
