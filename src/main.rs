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
        eprintln!("usage: {} <file>", args.get(0).map(String::as_ref).unwrap_or("rx7"));
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
        Err(RuntimeError { kind, span }) => exit_with_error(Diagnostic {
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
];

type Block = (Vec<Op>, Vec<Span>);

struct ParseError {
    kind: ParseErrorKind,
    span: Span,
}

enum ParseErrorKind {
    UnknownToken(char),
}

impl ParseErrorKind {
    pub const fn label(&self) -> &'static str {
        match self {
            Self::UnknownToken(_) => "unknown token",
        }
    }
}

impl std::fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.label())?;
        match self {
            Self::UnknownToken(c) => write!(f, " {c:?}"),
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

    fn parse_op(&mut self) -> ParseResult<Option<Op>> {
        let ops: HashMap<char, &Op> = OP_CHARS.iter().map(|(c, op)| (*c, op)).collect();
        let Some(c) = self.get_char() else { return Ok(None) };
        let op = match c {
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
            c => match ops.get(&c) {
                Some(&op) => {
                    self.next_char();
                    let w: Op = op.clone();
                    w
                }
                None => {
                    return Err(ParseError {
                        kind: ParseErrorKind::UnknownToken(c),
                        span: self.i..self.i + c.len_utf8(),
                    });
                }
            },
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
                return Ok((ops, spans));
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
}

#[derive(Clone, Debug)]
enum RuntimeErrorKind {
    StackUnderflow,
    TypeMismatch,
    DivisionByZero,
    NonInteger,
    Assertion,
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
        }
    }
}

type RuntimeResult<T> = Result<T, RuntimeError>;

type RawResult<T> = Result<T, RuntimeErrorKind>;

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

    fn push_group(&mut self, group: Vec<Value>) {
        self.stack.push(group);
    }

    fn push_value(&mut self, value: Value) {
        self.push_group(vec![value]);
    }

    fn pop_group(&mut self) -> RawResult<Vec<Value>> {
        self.stack.pop().ok_or(StackUnderflow)
    }

    fn pop_value(&mut self) -> RawResult<Value> {
        let group = self.stack.last_mut().ok_or(StackUnderflow)?;
        let value = group.pop().unwrap();
        if group.is_empty() {
            self.stack.pop().unwrap();
        }
        Ok(value)
    }

    fn execute_all(&mut self) -> RuntimeResult<()> {
        while self.ip < self.ops.len() {
            self.execute_op()
                .map_err(|kind| RuntimeError { kind, span: self.spans[self.ip].clone() })?;
            print!("{:?}\n> ", self.ops[self.ip]);
            self.display_stack();
            self.ip += 1;
        }
        Ok(())
    }

    fn execute_op(&mut self) -> RawResult<()> {
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
                        _ => return Err(TypeMismatch),
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
                        _ => return Err(TypeMismatch),
                    }
                } ),*]};
                inputs.reverse();
                let [$($arg),*] = inputs;
                if !$body {
                    return Err(Assertion);
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
                    return Err(NonInteger);
                }
                a.to_integer().checked_div_euclid(&b.to_integer()).ok_or(DivisionByZero)?
            }),
            Op::Remainder => math_op!(|a, b| {
                if !a.is_integer() || !b.is_integer() {
                    return Err(NonInteger);
                }
                a.to_integer().checked_rem_euclid(&b.to_integer()).ok_or(DivisionByZero)?
            }),
            Op::Div => {
                math_op!(|a, b| a.checked_div(&b).ok_or(DivisionByZero)?);
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
                _ => return Err(TypeMismatch),
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
        }
        Ok(())
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

fn execute((ops, spans): &Block) -> RuntimeResult<()> {
    let mut state = State { stack: vec![], ops, spans, ip: 0 };
    state.execute_all()
}
