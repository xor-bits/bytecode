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
        let mut assembler = Assembler::init();

        for line in self.0.iter() {
            if let Some(label) = line.label.as_ref() {
                assembler.insert_label(label.0);
            }

            assembler.insert_opcode(line.instr.opcode());

            match &line.instr {
                Instruction::I32Push(i) => assembler.insert_i16(*i),
                Instruction::Jump(label) => assembler.insert_label_addr(label.0),
                Instruction::Call(label) => assembler.insert_label_addr(label.0),
                _ => {}
            }
        }

        assembler.finish()
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

pub struct Assembler<'a> {
    code: Vec<u8>,
    labels: HashMap<&'a str, LabelReference>,
}

impl<'a> Assembler<'a> {
    pub fn init() -> Self {
        let mut code = Vec::new();
        code.extend_from_slice(b"yeet");
        let labels = HashMap::new();
        Self { code, labels }
    }

    pub fn insert_opcode(&mut self, opcode: OpCode) {
        self.code.push(opcode.into_byte());
    }

    pub fn insert_i16(&mut self, i: i16) {
        for b in i.to_le_bytes() {
            self.code.push(b);
        }
    }

    /// get the current code address and set its label
    pub fn insert_label(&mut self, label: &'a str) {
        let dst = self.code.len();
        if let Some(LabelReference::Fixup(needs_fixing)) =
            self.labels.insert(label, LabelReference::Result(dst))
        {
            // fix all references created before the label was created
            for needs_fixing_at in needs_fixing {
                // println!("fixing {needs_fixing_at}");
                if let Some(code_dst_bytes) = self
                    .code
                    .get_mut(needs_fixing_at..needs_fixing_at + 2)
                    .and_then(|s| <&mut [u8; 2]>::try_from(s).ok())
                {
                    let delta = i16::from_le_bytes(*code_dst_bytes);
                    let delta_ip = dst as isize - needs_fixing_at as isize + delta as isize;
                    let delta_ip: i16 = delta_ip.try_into().expect("relative jump too large");
                    code_dst_bytes.copy_from_slice(&delta_ip.to_le_bytes());
                }
            }
        }
    }

    /// read the address of a label and insert it into code (lazily)
    pub fn insert_label_addr(&mut self, label: &'a str) {
        match self.labels.entry(label) {
            Entry::Occupied(mut e) => match e.get_mut() {
                LabelReference::Fixup(e) => {
                    // this is yet another reference to a label that has not yet been created
                    e.push(self.code.len());
                    self.code.extend_from_slice(&1i16.to_le_bytes());
                }
                LabelReference::Result(e) => {
                    // the label is already known
                    let delta_ip = (*e) as isize - self.code.len() as isize + 1;
                    let delta_ip: i16 = delta_ip.try_into().expect("relative jump too large");
                    self.code.extend_from_slice(&delta_ip.to_le_bytes());
                }
            },
            Entry::Vacant(e) => {
                // fix the address later
                e.insert(LabelReference::Fixup(vec![self.code.len()]));
                self.code.extend_from_slice(&1i16.to_le_bytes());
            }
        }
    }

    pub fn finish(self) -> Vec<u8> {
        for (sym, unresolved) in self.labels {
            if let LabelReference::Fixup(..) = unresolved {
                panic!("unresolved symbol `{sym}`");
            }
        }

        self.code
    }
}

//

enum LabelReference {
    Fixup(Vec<usize>),
    Result(usize),
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
    Call(Label<'input>),
    Return,
    Exit,
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
            Call,
            Return,
            Exit,
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
    Call,
    Return,
    Exit,
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
            OpCode::Call => "call",
            OpCode::Return => "return",
            OpCode::Exit => "exit",
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

    #[test]
    fn back_and_front_refs() {
        let asm = r#"
                  jump loop
            loop: i32.load.0
                  i32.debug
                  jump loop
            "#;
        let asm = Assembly::parse(asm);
        let bc = asm.assemble();
        insta::assert_debug_snapshot!(bc);
    }
}
