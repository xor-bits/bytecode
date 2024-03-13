use std::{
    collections::{hash_map::Entry, HashMap},
    fmt,
};

use lalrpop_util::lalrpop_mod;
use num_enum::{FromPrimitive, IntoPrimitive};

//

lalrpop_mod!(pub grammar);

//

#[derive(Debug)]
pub struct Assembly<'input>(pub Vec<Line<'input>>);

impl<'input> Assembly<'input> {
    pub fn parse(input: &'input str) -> Self {
        grammar::AssemblyParser::new().parse(input).unwrap()
    }

    pub fn assemble(&self) -> Vec<u8> {
        let mut code = Vec::new();

        code.extend_from_slice(b"yeet");

        enum Label {
            Fixup(Vec<usize>),
            Result(usize),
        }

        let mut labels = HashMap::new();

        for line in self.0.iter() {
            if let Some(label) = line.label.as_ref() {
                // can shadow older labels
                let dst = code.len();
                if let Some(Label::Fixup(needs_fixing)) = labels.insert(label.0, Label::Result(dst))
                {
                    for needs_fixing_at in needs_fixing {
                        if let Some(code_dst_bytes) = code
                            .get_mut(needs_fixing_at..needs_fixing_at + 8)
                            .and_then(|s| <&mut [u8; 8]>::try_from(s).ok())
                        {
                            if needs_fixing_at.abs_diff(dst) > i16::MAX as usize {
                                panic!("relative jump too large");
                            }
                            let dst_b =
                                ((dst as isize - needs_fixing_at as isize) as i16).to_le_bytes();
                            code_dst_bytes.copy_from_slice(&dst_b);
                        }
                    }
                }
            }

            let num: u8 = line.instr.opcode().into();
            code.push(num);

            match &line.instr {
                Instruction::I32Push(i32) => {
                    for b in i32.to_le_bytes() {
                        code.push(b);
                    }
                }
                Instruction::Jump(l) => match labels.entry(l.0) {
                    Entry::Occupied(mut e) => match e.get_mut() {
                        Label::Fixup(e) => {
                            e.push(code.len());
                            code.extend_from_slice(&[0; 2]);
                        }
                        Label::Result(e) => {
                            if (code.len() - 1).abs_diff(*e) > i16::MAX as usize {
                                panic!("relative jump too large");
                            }
                            code.extend_from_slice(
                                &(((*e) as isize - (code.len() - 1) as isize) as i16).to_le_bytes(),
                            );
                        }
                    },
                    Entry::Vacant(e) => {
                        e.insert(Label::Fixup(vec![code.len()]));
                        code.extend_from_slice(&[0; 2]);
                    }
                },
                _ => {}
            }
        }

        for (sym, unresolved) in labels {
            if let Label::Fixup(..) = unresolved {
                panic!("unresolved symbol `{sym}`");
            }
        }

        code
    }
}

impl fmt::Display for Assembly<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for line in self.0.iter() {
            if let Some(label) = line.label.as_ref() {
                writeln!(f, "{}:", label.0)?;
            }

            write!(f, "{}", line.instr.opcode().as_str())?;
            match &line.instr {
                Instruction::I32Push(i) => write!(f, " {i}")?,
                Instruction::Jump(l) => write!(f, " {}", l.0)?,
                _ => {}
            }

            writeln!(f)?;
        }

        Ok(())
    }
}

//

#[derive(Debug)]
pub struct Line<'input> {
    pub instr: Instruction<'input>,
    pub label: Option<Label<'input>>,
}

//

#[derive(Debug)]
pub enum Instruction<'input> {
    I32Const0,
    I32Const1,
    I32Const2,
    I32Store0,
    I32Store1,
    I32Store2,
    I32Load0,
    I32Load1,
    I32Load2,
    I32Add,
    I32Inc,
    I32Push(i16),
    I32Debug,
    Jump(Label<'input>),
}

impl<'input> Instruction<'input> {
    pub const fn opcode(&self) -> OpCode {
        macro_rules! gen {
            ($($var:ident),* $(,)?) => {
                match self {
                    $(Self::$var { .. } => OpCode::$var,)*
                }
            };
        }
        gen! {
            I32Const0,
            I32Const1,
            I32Const2,
            I32Store0,
            I32Store1,
            I32Store2,
            I32Load0,
            I32Load1,
            I32Load2,
            I32Add,
            I32Inc,
            I32Push,
            I32Debug,
            Jump,
        }
    }
}

//

#[derive(Debug, Clone, Copy, Default, FromPrimitive, IntoPrimitive)]
#[repr(u8)]
pub enum OpCode {
    I32Const0 = 1,
    I32Const1,
    I32Const2,
    I32Store0,
    I32Store1,
    I32Store2,
    I32Load0,
    I32Load1,
    I32Load2,
    I32Add,
    I32Inc,
    I32Push,
    I32Debug,
    Jump,
    #[default]
    Invalid = 255,
}

impl OpCode {
    pub fn from_byte(b: u8) -> Self {
        Self::from_primitive(b)
    }

    pub fn into_byte(self) -> u8 {
        self.into()
    }

    pub const fn as_str(&self) -> &'static str {
        match self {
            OpCode::I32Const0 => "i32.const.0",
            OpCode::I32Const1 => "i32.const.1",
            OpCode::I32Const2 => "i32.const.2",
            OpCode::I32Store0 => "i32.store.0",
            OpCode::I32Store1 => "i32.store.1",
            OpCode::I32Store2 => "i32.store.2",
            OpCode::I32Load0 => "i32.load.0",
            OpCode::I32Load1 => "i32.load.0",
            OpCode::I32Load2 => "i32.load.0",
            OpCode::I32Add => "i32.add",
            OpCode::I32Inc => "i32.inc",
            OpCode::I32Push => "i32.push",
            OpCode::I32Debug => "i32.debug",
            OpCode::Jump => "jump",
            OpCode::Invalid => "",
        }
    }
}

//

#[derive(Debug)]
pub struct Label<'input>(pub &'input str);

//

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse() {
        let asm = r#"
                  i32.const.0
            loop: i32.debug // print 0
                  jump loop
            "#;
        let asm = Assembly::parse(asm);
        insta::assert_snapshot!(asm);
    }

    #[test]
    fn assemble() {
        let asm = r#"
                  i32.const.0 // push 0
            loop: i32.debug   // print 0, 1, 2, 3, ..
                  i32.const.1 // push 1
                  i32.add     // pop 2 ints and push the sum
                  jump loop   // infinite loop
            "#;
        let asm = Assembly::parse(asm);
        let bc = asm.assemble();
        insta::assert_debug_snapshot!(bc);
    }
}
