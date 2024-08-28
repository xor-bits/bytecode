use asm::OpCode;
use std::fmt::Write;

//

#[derive(Debug, PartialEq, Eq)]
pub enum RunError {
    InvalidByteCode,
    InvalidOpCode,
    StackOverflow,
    StackUnderflow,
    SegFault,
    OutOfFuel,
}

//

pub struct VirtMachine {
    ip: usize,
    regs: [i32; 5],
    stack: Vec<i32>,
    call_stack: Vec<usize>,

    fuel: Option<usize>,
    debug: String,
    debugger: bool,
}

impl VirtMachine {
    pub const fn new() -> Self {
        Self {
            ip: 0,
            regs: [0; 5],
            stack: Vec::new(),
            call_stack: Vec::new(),

            fuel: None,
            debug: String::new(),
            debugger: false,
        }
    }

    /// fuel limits the number of instructions that can run
    pub fn set_fuel(&mut self, fuel: Option<usize>) {
        self.fuel = fuel;
    }

    /// debugger prints the cpu state after each instruction
    pub fn set_debugger(&mut self, debugger: bool) {
        self.debugger = debugger;
    }

    pub fn run(&mut self, code: &[u8]) -> Result<i32, RunError> {
        if code.len() < 4 {
            return Err(RunError::InvalidByteCode);
        }

        assert_eq!(&code[..4], b"yeet");

        self.ip = 4usize;
        self.regs = [0i32; 5];
        self.stack.clear();
        self.call_stack.clear();

        while let Some(opcode) = code.get(self.ip).copied() {
            if self.debugger {
                // thread::sleep(Duration::from_millis(100));
                self.print_state(code);
            }

            if let Some(fuel) = self.fuel.as_mut() {
                if *fuel == 0 {
                    return Err(RunError::OutOfFuel);
                }
                *fuel -= 1;
            }

            self.ip += 1;
            match OpCode::from_byte(opcode) {
                OpCode::I32Const0 => self.push(0)?,
                OpCode::I32Const1 => self.push(1)?,
                OpCode::I32Const2 => self.push(2)?,
                OpCode::I32Store0 => self.regs[0] = self.pop()?,
                OpCode::I32Store1 => self.regs[1] = self.pop()?,
                OpCode::I32Store2 => self.regs[2] = self.pop()?,
                OpCode::I32Load0 => self.push(self.regs[0])?,
                OpCode::I32Load1 => self.push(self.regs[1])?,
                OpCode::I32Load2 => self.push(self.regs[2])?,
                OpCode::I32Add => {
                    let lhs = self.pop()?;
                    let rhs = self.pop()?;
                    self.push(lhs.wrapping_add(rhs))?;
                }
                OpCode::I32Inc => {
                    let val = self.pop()?;
                    self.push(val.wrapping_add(1))?;
                }
                OpCode::I32Push => {
                    let val = self.read_operand_i16(code)?;
                    self.push(val as i32)?;

                    self.ip += 2;
                }
                OpCode::I32Debug => {
                    let val = self.stack.pop().ok_or(RunError::StackUnderflow)?;
                    _ = writeln!(&mut self.debug, "{val}");
                    println!("{val}");
                }
                OpCode::Jump => {
                    let delta_ip = self.read_operand_i16(code)?;

                    self.ip = (self.ip - 1)
                        .checked_add_signed(delta_ip as isize)
                        .ok_or(RunError::SegFault)?;
                }
                OpCode::Call => {
                    let delta_ip = self.read_operand_i16(code)?;
                    let new_ip = (self.ip - 1)
                        .checked_add_signed(delta_ip as isize)
                        .ok_or(RunError::SegFault)?;

                    self.call_stack.push(self.ip + 2);
                    self.ip = new_ip;
                }
                OpCode::Return => {
                    self.ip = self.call_stack.pop().ok_or(RunError::StackUnderflow)?;
                }
                OpCode::Exit => {
                    let result = self.pop()?;
                    return Ok(result);
                }
                OpCode::Invalid => return Err(RunError::InvalidOpCode),
            }
        }

        Err(RunError::SegFault)
    }

    pub fn print_state(&self, code: &[u8]) {
        println!(
            "\nCPU:\nip={} sp={} fuel={:?}\nregs={:?}",
            self.ip,
            self.stack.len(),
            self.fuel,
            self.regs
        );
        if let Some(b) = code.get(self.ip) {
            let opcode = OpCode::from_byte(*b).as_str();
            println!("{opcode}");
        }
        // println!("{opcode} = {}", OpCode::from_byte(opcode).as_str());
    }

    fn push(&mut self, v: i32) -> Result<(), RunError> {
        self.stack.push(v);
        Ok(())
    }

    fn pop(&mut self) -> Result<i32, RunError> {
        self.stack.pop().ok_or(RunError::StackUnderflow)
    }

    fn read_operand_i16(&mut self, code: &[u8]) -> Result<i16, RunError> {
        code.get(self.ip..self.ip + 2)
            .and_then(|b| <[u8; 2]>::try_from(b).ok())
            .map(i16::from_le_bytes)
            .ok_or(RunError::SegFault)
    }
}

//

#[cfg(test)]
mod tests {

    use asm::Assembly;

    use super::*;

    #[test]
    fn fuel_test() {
        let asm = r#"
                i32.const.0 // push 0
            loop:
                i32.store.0
                i32.load.0
                i32.debug   // print 0, 1, 2, 3, ..
                i32.load.0

                i32.inc
                jump loop   // infinite loop
            "#;
        let asm = Assembly::parse(asm);
        let bc = asm.assemble();

        let mut vm = VirtMachine::new();
        vm.set_debugger(true);
        vm.set_fuel(Some(100));
        assert_eq!(vm.run(&bc), Err(RunError::OutOfFuel));

        insta::assert_snapshot!(vm.debug);
    }

    #[test]
    fn func_test() {
        let asm = r#"
                  i32.const.1 // push 1i32
                  i32.const.2 // push 2i32
                  call add
                  i32.store.0
                  i32.load.0
                  i32.debug   // print the int in reg0
                  i32.load.0
                  exit

            add:  i32.add
                  return
            "#;
        let asm = Assembly::parse(asm);
        let bc = asm.assemble();

        let mut vm = VirtMachine::new();
        vm.set_debugger(true);
        vm.set_fuel(Some(10));
        assert_eq!(vm.run(&bc), Ok(3));

        insta::assert_snapshot!(vm.debug);
    }

    #[test]
    fn fibonacci() {
        let asm = r#"
            i32.const.1 // push 1i32
            i32.store.0
            i32.const.1 // push 2i32
            i32.store.1

        loop:
            i32.load.0
            i32.debug

            i32.load.0
            i32.load.1
            i32.add
            i32.load.1
            i32.store.0
            i32.store.1
            jump loop
    "#;

        let asm = Assembly::parse(asm);
        let bc = asm.assemble();

        let mut vm = VirtMachine::new();
        vm.set_debugger(true);
        vm.set_fuel(Some(100));
        assert_eq!(vm.run(&bc), Err(RunError::OutOfFuel));
        insta::assert_snapshot!(vm.debug);
    }
}
