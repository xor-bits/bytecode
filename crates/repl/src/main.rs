use asm::Assembly;
use vm::VirtMachine;

//

fn main() {
    let asm = r#"
    mult:
        
    "#;

    let asm = Assembly::parse(asm);
    let bc = asm.assemble();

    let mut vm = VirtMachine::new();
    vm.set_fuel(Some(100));
    let result = vm.run(&bc);
    // vm.print_state(&bc);
    println!("result = {result:?}");
}
