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
    fuel: Option<usize>,
    ip: usize,
    regs: [i32; 5],
    stack: Vec<i32>,

    debug: String,
}

impl VirtMachine {
    pub const fn new() -> Self {
        Self {
            fuel: None,
            ip: 0,
            regs: [0; 5],
            stack: Vec::new(),
            debug: String::new(),
        }
    }

    pub fn set_fuel(&mut self, fuel: Option<usize>) {
        self.fuel = fuel;
    }

    pub fn run(&mut self, code: &[u8]) -> Result<(), RunError> {
        if code.len() < 4 {
            return Err(RunError::InvalidByteCode);
        }

        assert_eq!(&code[..4], b"yeet");

        self.ip = 4usize;
        self.regs = [0i32; 5];
        self.stack.clear();

        while let Some(opcode) = code.get(self.ip).copied() {
            // println!("{opcode} = {}", OpCode::from_byte(opcode).as_str());

            if let Some(fuel) = self.fuel.as_mut() {
                if *fuel == 0 {
                    return Err(RunError::OutOfFuel);
                }
                *fuel -= 1;
            }

            self.ip += 1;
            match OpCode::from_byte(opcode) {
                OpCode::I32Const0 => self.stack.push(0),
                OpCode::I32Const1 => self.stack.push(1),
                OpCode::I32Const2 => self.stack.push(2),
                OpCode::I32Store0 => {
                    self.regs[0] = self.stack.pop().ok_or(RunError::StackUnderflow)?
                }
                OpCode::I32Store1 => {
                    self.regs[1] = self.stack.pop().ok_or(RunError::StackUnderflow)?
                }
                OpCode::I32Store2 => {
                    self.regs[2] = self.stack.pop().ok_or(RunError::StackUnderflow)?
                }
                OpCode::I32Load0 => self.stack.push(self.regs[0]),
                OpCode::I32Load1 => self.stack.push(self.regs[1]),
                OpCode::I32Load2 => self.stack.push(self.regs[2]),
                OpCode::I32Add => {
                    let lhs = self.stack.pop().ok_or(RunError::StackUnderflow)?;
                    let rhs = self.stack.pop().ok_or(RunError::StackUnderflow)?;
                    self.stack.push(lhs.wrapping_add(rhs))
                }
                OpCode::I32Inc => {
                    let val = self.stack.pop().ok_or(RunError::StackUnderflow)?;
                    self.stack.push(val.wrapping_add(1))
                }
                OpCode::I32Push => {
                    if let Some(val) = code
                        .get(self.ip..self.ip + 2)
                        .and_then(|b| <[u8; 2]>::try_from(b).ok())
                    {
                        self.stack.push(i16::from_le_bytes(val) as i32);
                    } else {
                        return Err(RunError::SegFault);
                    }

                    self.ip += 2;
                }
                OpCode::I32Debug => {
                    let val = self.stack.pop().ok_or(RunError::StackUnderflow)?;
                    self.stack.push(val);
                    _ = writeln!(&mut self.debug, "{val}");
                }
                OpCode::Jump => {
                    if let Some(new_ip) = code
                        .get(self.ip..self.ip + 2)
                        .and_then(|b| <[u8; 2]>::try_from(b).ok())
                        .and_then(|val| {
                            // println!("ip={}", self.ip);
                            // println!("relative jump: {}", i16::from_le_bytes(val));
                            (self.ip - 1).checked_add_signed(i16::from_le_bytes(val) as isize)
                        })
                    {
                        // println!("code now: {:?}", &code[self.ip..]);
                        // println!("newip={new_ip}");
                        self.ip = new_ip;
                    } else {
                        return Err(RunError::SegFault);
                    }

                    continue;
                }
                OpCode::Invalid => return Err(RunError::InvalidOpCode),
            }
        }

        Err(RunError::SegFault)
    }
}

//

#[cfg(test)]
mod tests {

    use asm::Assembly;

    use super::*;

    #[test]
    fn parse() {
        let asm = r#"
                  i32.const.0 // push 0
            loop: i32.debug   // print 0, 1, 2, 3, ..
                  i32.const.1 // push 1
                  i32.add     // pop 2 ints and push the sum
                  jump loop   // infinite loop
            "#;
        let asm = Assembly::parse(asm);
        let bc = asm.assemble();

        let mut vm = VirtMachine::new();
        vm.set_fuel(Some(50));
        assert_eq!(vm.run(&bc), Err(RunError::OutOfFuel));

        insta::assert_snapshot!(vm.debug);
    }
}
