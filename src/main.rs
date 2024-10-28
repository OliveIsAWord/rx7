use std::collections::HashMap;

use num_traits::{CheckedDiv as _, CheckedEuclid as _};

type Span = std::ops::Range<usize>;

type Rat = num_rational::BigRational;
type Int = num_bigint::BigInt;

fn main() {
    struct Diagnostic {
        span: Span,
        message: String,
        label: String,
    }
    use std::process::exit;

    use ariadne::{Label, Report, ReportKind, Source};
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: {} <file>", args.first().map_or("rx7", String::as_ref));
        exit(1);
    };
    let file_path = args[1].as_ref();
    let src = match std::fs::read_to_string(file_path) {
        Ok(src) => src,
        Err(e) => {
            let _ = Report::<(&str, Span)>::build(ReportKind::Error, file_path, 0)
                .with_message(format!("could not read file {file_path}: {e}"))
                .finish()
                .eprint((file_path, Source::from("")));
            exit(1);
        }
    };
    let exit_with_error = |e: Diagnostic| -> ! {
        let _ = Report::<(&str, Span)>::build(ReportKind::Error, file_path, e.span.start)
            .with_message(e.message)
            .with_label(Label::new((file_path, e.span)).with_message(e.label))
            .finish()
            .eprint((file_path, Source::from(&src)));
        exit(1);
    };
    let block = match parse(&src) {
        Ok(b) => b,
        Err(ParseError { kind, span }) => exit_with_error(Diagnostic {
            span,
            message: format!("{kind}"),
            label: kind.label().to_owned(),
        }),
    };
    match execute(&block) {
        Ok(()) => {}
        Err(RuntimeError { kind, span, .. }) => exit_with_error(Diagnostic {
            span,
            message: "instruction raised".to_owned(),
            label: format!("{kind}"),
        }),
    }
}

#[derive(Clone, Debug)]
enum Op {
    Int(Int),
    Add,
    Sub,
    Mul,
    Quotient,
    Remainder,
    Div,
    Neg,
    Floor,
    Ceil,
    CompareLt,
    CompareGe,
    CompareEq,
    CompareNe,
    CompareGt,
    CompareLe,
    Box,
    Unbox,
    Group,
    Dup,
    Pop,
    Flip,
    Yank,
    Raise,
    Except(Block, Block),
    Suppress(Block),
    Invert(Block),
    Mask(Block),
    Trace,
}

const OP_CHARS: &[(char, Op)] = &[
    ('+', Op::Add),
    ('-', Op::Sub),
    ('*', Op::Mul),
    ('Q', Op::Quotient),
    ('R', Op::Remainder),
    ('D', Op::Div),
    ('N', Op::Neg),
    ('J', Op::Floor),
    ('K', Op::Ceil),
    ('<', Op::CompareLt),
    ('G', Op::CompareGe),
    ('=', Op::CompareEq),
    ('/', Op::CompareNe),
    ('>', Op::CompareGt),
    ('L', Op::CompareLe),
    ('B', Op::Box),
    ('b', Op::Unbox),
    ('&', Op::Group),
    ('d', Op::Dup),
    ('p', Op::Pop),
    ('f', Op::Flip),
    ('^', Op::Yank),
    ('r', Op::Raise),
    ('v', Op::Trace),
];

const ONE_BLOCK_CHARS: &[(char, fn(Block) -> Op)] =
    &[('s', Op::Suppress), ('!', Op::Invert), ('m', Op::Mask)];

const TWO_BLOCK_CHARS: &[(char, fn(Block, Block) -> Op)] = &[('e', Op::Except)];

#[derive(Clone, Debug)]
struct Block {
    ops: Vec<Op>,
    spans: Vec<Span>,
}

struct ParseError {
    kind: ParseErrorKind,
    span: Span,
}

enum ParseErrorKind {
    UnknownToken(char),
    UnexpectedBacktick,
}

impl ParseErrorKind {
    pub const fn label(&self) -> &'static str {
        match self {
            Self::UnknownToken(_) => "unknown token",
            Self::UnexpectedBacktick => "unexpected backtick",
        }
    }
}

impl std::fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.label())?;
        match self {
            Self::UnknownToken(c) => write!(f, " {c:?}"),
            Self::UnexpectedBacktick => Ok(()),
        }
    }
}

type ParseResult<T> = Result<T, ParseError>;

struct Parser<'a> {
    src: &'a str,
    i: usize,
}

impl Parser<'_> {
    fn trim(&mut self) {
        while self.get_char() == Some(' ') {
            self.next_char();
        }
    }

    fn get_char(&self) -> Option<char> {
        self.src[self.i..].chars().next()
    }

    fn next_char(&mut self) {
        self.i += self.get_char().unwrap().len_utf8();
    }

    fn consume_if(&mut self, c: char) -> bool {
        let is_char = self.get_char() == Some(c);
        if is_char {
            self.next_char();
        }
        is_char
    }

    fn parse_op(&mut self) -> ParseResult<Option<Op>> {
        let ops: HashMap<char, &Op> = OP_CHARS.iter().map(|(c, op)| (*c, op)).collect();
        let one_block_ops: HashMap<char, fn(Block) -> Op> =
            ONE_BLOCK_CHARS.iter().map(|&(c, op)| (c, op)).collect();
        let two_block_ops: HashMap<char, fn(Block, Block) -> Op> =
            TWO_BLOCK_CHARS.iter().map(|&(c, op)| (c, op)).collect();
        let Some(c) = self.get_char() else { return Ok(None) };
        let op = match c {
            '`' => return Ok(None),
            c if c.is_ascii_digit() => {
                if c == '0' {
                    self.next_char();
                    Op::Int(Int::ZERO)
                } else {
                    let rest = &self.src[self.i + 1..];
                    let end_i = rest
                        .char_indices()
                        .find_map(|(i, c)| if c.is_ascii_digit() { None } else { Some(i) })
                        .unwrap_or(rest.len())
                        + self.i
                        + 1;
                    let num_str = &self.src[self.i..end_i];
                    self.i = end_i;
                    Op::Int(num_str.parse().unwrap())
                }
            }
            c => {
                if let Some(&op) = ops.get(&c) {
                    self.next_char();
                    let w: Op = op.clone();
                    w
                } else if let Some(&op) = one_block_ops.get(&c) {
                    self.next_char();
                    let block = self.parse_last_block()?;
                    op(block)
                } else if let Some(&op) = two_block_ops.get(&c) {
                    self.next_char();
                    let block1 = self.parse_last_block()?;
                    let block2 = self.parse_last_block()?;
                    op(block1, block2)
                } else {
                    return Err(ParseError {
                        kind: ParseErrorKind::UnknownToken(c),
                        span: self.i..self.i + c.len_utf8(),
                    });
                }
            }
        };
        Ok(Some(op))
    }

    fn parse_block(&mut self) -> ParseResult<Block> {
        let mut ops = vec![];
        let mut spans = vec![];
        loop {
            self.trim();
            let old_i = self.i;
            let Some(op) = self.parse_op()? else {
                if self.consume_if('`') {
                    return Err(ParseError {
                        kind: ParseErrorKind::UnexpectedBacktick,
                        span: self.i - 1..self.i,
                    });
                }
                return Ok(Block { ops, spans });
            };
            ops.push(op);
            spans.push(old_i..self.i);
        }
    }

    fn parse_last_block(&mut self) -> ParseResult<Block> {
        let mut ops = vec![];
        let mut spans = vec![];
        loop {
            self.trim();
            let old_i = self.i;
            let Some(op) = self.parse_op()? else {
                self.consume_if('`');
                return Ok(Block { ops, spans });
            };
            ops.push(op);
            spans.push(old_i..self.i);
        }
    }
}

fn parse(src: &str) -> ParseResult<Block> {
    let mut parser = Parser { src: src.trim_end(), i: 0 };
    parser.parse_block()
}

#[derive(Clone, Debug)]
struct RuntimeError {
    kind: RuntimeErrorKind,
    span: Span,
    masks: usize,
}

impl RuntimeError {
    pub const fn mask(mut self) -> Self {
        self.masks += 1;
        self
    }

    pub const fn unmask(mut self) -> Result<(), Self> {
        if self.masks == 0 {
            Ok(())
        } else {
            self.masks -= 1;
            Err(self)
        }
    }
}

#[derive(Clone, Debug)]
enum RuntimeErrorKind {
    StackUnderflow,
    TypeMismatch,
    DivisionByZero,
    NonInteger,
    Assertion,
    ExplicitRaise,
    DidNotRaise,
}

use RuntimeErrorKind::*;

impl std::fmt::Display for RuntimeErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StackUnderflow => write!(f, "stack underflow"),
            Self::TypeMismatch => write!(f, "type mismatch"),
            Self::DivisionByZero => write!(f, "division by zero"),
            Self::NonInteger => write!(f, "not an integer"),
            Self::Assertion => write!(f, "assertion failure"),
            Self::ExplicitRaise => write!(f, "explicit raise"),
            Self::DidNotRaise => write!(f, "block didn't raise"),
        }
    }
}

type RuntimeResult<T> = Result<T, RuntimeError>;

#[derive(Clone, Debug)]
struct State<'a> {
    stack: Vec<Vec<Value>>,
    ops: &'a [Op],
    spans: &'a [Span],
    ip: usize,
}

impl State<'_> {
    fn display_stack(&self) {
        for (group_i, group) in self.stack.iter().enumerate() {
            if group_i != 0 {
                print!(" ");
            }
            for (value_i, value) in group.iter().enumerate() {
                if value_i != 0 {
                    print!("&");
                }
                print!("{value}");
            }
        }
        println!();
    }

    fn error(&self, kind: RuntimeErrorKind) -> RuntimeError {
        RuntimeError { kind, span: self.spans[self.ip].clone(), masks: 0 }
    }

    fn push_group(&mut self, group: Vec<Value>) {
        self.stack.push(group);
    }

    fn push_value(&mut self, value: Value) {
        self.push_group(vec![value]);
    }

    fn pop_group(&mut self) -> RuntimeResult<Vec<Value>> {
        self.stack.pop().ok_or_else(|| self.error(StackUnderflow))
    }

    fn pop_value(&mut self) -> RuntimeResult<Value> {
        let Some(group) = self.stack.last_mut() else {
            return Err(self.error(StackUnderflow));
        };
        let value = group.pop().unwrap();
        if group.is_empty() {
            self.stack.pop().unwrap();
        }
        Ok(value)
    }

    fn execute_all(&mut self) -> RuntimeResult<()> {
        while self.ip < self.ops.len() {
            self.execute_op()?;
            self.ip += 1;
        }
        Ok(())
    }

    fn execute_op(&mut self) -> RuntimeResult<()> {
        macro_rules! op {
            (|$($arg:ident),*| $body:expr) => {{
               #[allow(unused_variables)]{
                let mut inputs = {#[allow(unused_variables)] [$({
                    let $arg = ();
                    self.pop_value()?
                } ),*]};
                inputs.reverse();
                let [$($arg),*] = inputs;
                let result = $body;
                self.push_value(result);
            }}}
        }
        macro_rules! math_op {
            (|$($arg:ident),*| $body:expr) => {{
               #[allow(unused_variables)]{
                let mut inputs = {#[allow(unused_variables)] [$({
                    let $arg = ();
                    match self.pop_value()? {
                        Value::Num(n) => n,
                        _ => return Err(self.error(TypeMismatch)),
                    }
                } ),*]};
                inputs.reverse();
                let [$($arg),*] = inputs;
                let result = $body;
                self.push_value(Value::Num(Rat::from(result)));
            }}}
        }
        macro_rules! comparison {
            (|$($arg:ident),*| $body:expr) => {{
               #[allow(unused_variables)]{
                let mut inputs = {#[allow(unused_variables)] [$({
                    let $arg = ();
                    match self.pop_value()? {
                        Value::Num(n) => n,
                        _ => return Err(self.error(TypeMismatch)),
                    }
                } ),*]};
                inputs.reverse();
                let [$($arg),*] = inputs;
                if !$body {
                    return Err(self.error(Assertion));
                }
            }}}
        }
        macro_rules! swizzle_groups {
            ($($input:ident)* -- $($output:ident)*) => {{
                let mut inputs = {#[allow(unused_variables)] [$({ let $input = (); self.pop_group()?}),*]};
                inputs.reverse();
                let [$($input),*] = inputs;
                $(self.push_group($output.clone());)*
            }}
        }
        let op = self.ops[self.ip].clone();
        match op {
            Op::Int(i) => self.push_value(Value::Num(i.into())),
            Op::Add => math_op!(|a, b| a + b),
            Op::Sub => math_op!(|a, b| a - b),
            Op::Mul => math_op!(|a, b| a * b),
            Op::Quotient => math_op!(|a, b| {
                if !a.is_integer() || !b.is_integer() {
                    return Err(self.error(NonInteger));
                }
                a.to_integer()
                    .checked_div_euclid(&b.to_integer())
                    .ok_or_else(|| self.error(DivisionByZero))?
            }),
            Op::Remainder => math_op!(|a, b| {
                if !a.is_integer() || !b.is_integer() {
                    return Err(self.error(NonInteger));
                }
                a.to_integer()
                    .checked_rem_euclid(&b.to_integer())
                    .ok_or_else(|| self.error(DivisionByZero))?
            }),
            Op::Div => {
                math_op!(|a, b| a.checked_div(&b).ok_or_else(|| self.error(DivisionByZero))?);
            }
            Op::Neg => math_op!(|a| -a),
            Op::Floor => math_op!(|a| a.floor()),
            Op::Ceil => math_op!(|a| a.ceil()),
            Op::CompareLt => comparison!(|a, b| a < b),
            Op::CompareGe => comparison!(|a, b| a >= b),
            Op::CompareEq => comparison!(|a, b| a == b),
            Op::CompareNe => comparison!(|a, b| a != b),
            Op::CompareGt => comparison!(|a, b| a > b),
            Op::CompareLe => comparison!(|a, b| a <= b),
            Op::Box => op!(|v| Value::Box(Box::new(v))),
            Op::Unbox => op!(|v| match v {
                Value::Box(b) => *b,
                _ => return Err(self.error(TypeMismatch)),
            }),
            Op::Group => {
                let mut rhs = self.pop_group()?;
                let mut lhs = self.pop_group()?;
                lhs.append(&mut rhs);
                self.push_group(lhs);
            }
            Op::Dup => swizzle_groups!(a -- a a),
            Op::Pop => {
                self.pop_value()?;
            }
            Op::Flip => swizzle_groups!(a b -- b a),
            Op::Yank => swizzle_groups!(a b -- a b a),
            Op::Raise => return Err(self.error(ExplicitRaise)),
            Op::Except(try_block, catch_block) => match self.execute_block(&try_block) {
                Ok(()) => {}
                Err(e) => {
                    e.unmask()?;
                    self.execute_block_no_rewind(&catch_block)?;
                }
            },
            Op::Suppress(b) => self.execute_block_unmask(&b)?,
            Op::Invert(b) => match self.execute_block_no_rewind(&b) {
                Ok(()) => return Err(self.error(DidNotRaise)),
                Err(e) => e.unmask()?,
            },
            Op::Mask(b) => self.execute_block(&b).map_err(RuntimeError::mask)?,
            Op::Trace => self.display_stack(),
        }
        Ok(())
    }

    fn execute_block_no_rewind(&mut self, Block { ops, spans }: &Block) -> RuntimeResult<()> {
        let stack = std::mem::take(&mut self.stack);
        let mut inner_state = State { stack, ops, spans, ip: 0 };
        let result = inner_state.execute_all();
        self.stack = inner_state.stack;
        result
    }

    fn execute_block(&mut self, block: &Block) -> RuntimeResult<()> {
        let old_stack = self.stack.clone();
        let result = self.execute_block_no_rewind(block);
        if result.is_err() {
            self.stack = old_stack;
        }
        result
    }

    fn execute_block_unmask(&mut self, block: &Block) -> RuntimeResult<()> {
        self.execute_block(block).or_else(RuntimeError::unmask)
    }
}

#[derive(Clone, Debug)]
enum Value {
    Num(Rat),
    Box(Box<Self>),
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Num(r) => write!(f, "{r}"),
            Self::Box(b) => write!(f, "#{b}"),
        }
    }
}

fn execute(Block { ops, spans }: &Block) -> RuntimeResult<()> {
    let mut state = State { stack: vec![], ops, spans, ip: 0 };
    state.execute_all()
}
