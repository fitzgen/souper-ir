//! Abstract syntax tree type definitions.

pub use id_arena::{Arena, Id};

/// An identifier for a value defined by an assignment.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ValueId(
    /// Always points to a `Statement::Assignment`, and references the value
    /// defined by the assignment.
    pub(crate) Id<Statement>,
);

impl From<ValueId> for Id<Statement> {
    #[inline]
    fn from(id: ValueId) -> Self {
        id.0
    }
}

/// An identifier for a defined block.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct BlockId(
    /// Always points to an assignment where the RHS is `AssignmentRhs::Block`.
    pub(crate) ValueId,
);

impl From<BlockId> for ValueId {
    #[inline]
    fn from(id: BlockId) -> Self {
        id.0
    }
}

impl From<BlockId> for Id<Statement> {
    #[inline]
    fn from(id: BlockId) -> Self {
        (id.0).0
    }
}

/// A complete optimization that replaces a left-hand side with a right-hand
/// side.
#[derive(Clone, Debug)]
pub enum Replacement {
    /// A replacement in the form of a left-hand side followed by a right-hand
    /// side.
    LhsRhs {
        /// Statements that make up the expression DAGs for the left- and
        /// right-hand sides.
        statements: Arena<Statement>,
        /// The left-hand side that is matched by the optimization.
        lhs: Infer,
        /// The right-hand side that replaces the left-hand side after applying
        /// the optimization.
        rhs: Operand,
    },

    /// A replacement in the form of an expression DAG followed by a `cand x y`
    /// statement that declares that `y` is a candidate for replacing `x`.
    Cand {
        /// Statements that make up the expression DAG for both the
        /// replacement's left- and right-hand sides.
        statements: Arena<Statement>,
        /// The candidate rewrite connecting the left- and right-hand sides of
        /// this replacement within `statements`.
        cand: Cand,
    },
}

impl Replacement {
    /// Get the assignment that defined the given value.
    ///
    /// # Panics
    ///
    /// May panic or produce incorrect results if given a `ValueId` from another
    /// `Replacement`, `LeftHandSide`, or `RightHandSide`'s arena.
    pub fn assignment(&self, id: ValueId) -> &Assignment {
        match self {
            Replacement::LhsRhs { statements, .. } | Replacement::Cand { statements, .. } => {
                match &statements[id.into()] {
                    Statement::Assignment(a) => a,
                    _ => panic!("use of an `id` that is not from this `Replacement`'s arena"),
                }
            }
        }
    }
}

/// A builder for a [`Replacement`][crate::ast::Replacement].
#[derive(Clone, Debug, Default)]
pub struct ReplacementBuilder {
    statements: Arena<Statement>,
}

impl ReplacementBuilder {
    /// Create a new assignment statement.
    ///
    /// Returns the value defined by the assignment.
    ///
    /// # Panics
    ///
    /// Panics if `name` (when given) does not start with '%'.
    pub fn assignment(
        &mut self,
        name: Option<String>,
        r#type: Option<Type>,
        value: impl Into<AssignmentRhs>,
        attributes: Vec<Attribute>,
    ) -> ValueId {
        let name = name.unwrap_or_else(|| format!("%{}", self.statements.len()));
        assert!(name.starts_with('%'));
        ValueId(
            self.statements.alloc(
                Assignment {
                    name,
                    r#type,
                    value: value.into(),
                    attributes,
                }
                .into(),
            ),
        )
    }

    /// Create a new [basic block][crate::ast::Block].
    ///
    /// Declare that the block has `predecessors` number of incoming edges in
    /// the control-flow graph.
    ///
    /// # Panics
    ///
    /// Panics if `name` (when given) does not start with '%'.
    pub fn block(&mut self, name: Option<String>, predecessors: u32) -> BlockId {
        BlockId(self.assignment(name, None, Block { predecessors }, vec![]))
    }

    /// Create a [path condition][crate::ast::Pc].
    ///
    /// Expresses the fact that `x` must equal `y` for the replacement to be
    /// valid.
    pub fn pc(&mut self, x: impl Into<Operand>, y: impl Into<Operand>) {
        let x = x.into();
        let y = y.into();
        self.statements.alloc(Pc { x, y }.into());
    }

    /// Create a [block path condition][crate::ast::BlockPc].
    ///
    /// Expresses that `x` is equal to `y` on an incoming edge to `block` in the
    /// control-flow graph.
    ///
    /// # Panics
    ///
    /// Panics if `predecessor` is greater than or equal to `block`'s number of
    /// predecessors.
    pub fn block_pc(
        &mut self,
        block: BlockId,
        predecessor: u32,
        x: impl Into<Operand>,
        y: impl Into<Operand>,
    ) {
        let x = x.into();
        let y = y.into();
        self.statements.alloc(
            BlockPc {
                block,
                predecessor,
                x,
                y,
            }
            .into(),
        );
    }

    /// Finish building this replacement by providing the left- and right-hand
    /// sides.
    pub fn finish(
        self,
        lhs: ValueId,
        rhs: impl Into<Operand>,
        attributes: impl IntoIterator<Item = RootAttribute>,
    ) -> Replacement {
        Replacement::LhsRhs {
            statements: self.statements,
            lhs: Infer {
                value: lhs,
                attributes: attributes.into_iter().collect(),
            },
            rhs: rhs.into(),
        }
    }
}

/// A candidate rewrite.
#[derive(Clone, Debug)]
pub struct Cand {
    /// The left-hand side expression that can be replaced by the right-hand
    /// side.
    pub lhs: Operand,

    /// The right-hand side expression that can replace the left-hand side.
    pub rhs: Operand,

    /// Attributes for this rewrite.
    pub attributes: Vec<RootAttribute>,
}

/// The left-hand side of a replacement.
#[derive(Clone, Debug)]
pub struct LeftHandSide {
    /// Statements making up this LHS's expression DAG.
    pub statements: Arena<Statement>,

    /// The root of this LHS's expression DAG.
    pub infer: Infer,
}

/// A builder for a [`LeftHandSide`][crate::ast::LeftHandSide].
#[derive(Clone, Debug, Default)]
pub struct LeftHandSideBuilder {
    statements: Arena<Statement>,
}

impl LeftHandSideBuilder {
    /// Create a new assignment statement.
    ///
    /// Returns the value defined by the assignment.
    ///
    /// # Panics
    ///
    /// Panics if `name` (when given) does not start with '%'.
    pub fn assignment(
        &mut self,
        name: Option<String>,
        r#type: Option<Type>,
        value: impl Into<AssignmentRhs>,
        attributes: Vec<Attribute>,
    ) -> ValueId {
        let name = name.unwrap_or_else(|| format!("%{}", self.statements.len()));
        assert!(name.starts_with('%'));
        ValueId(
            self.statements.alloc(
                Assignment {
                    name,
                    r#type,
                    value: value.into(),
                    attributes,
                }
                .into(),
            ),
        )
    }

    /// Create a new [basic block][crate::ast::Block].
    ///
    /// Declare that the block has `predecessors` number of incoming edges in
    /// the control-flow graph.
    ///
    /// # Panics
    ///
    /// Panics if `name` (when given) does not start with '%'.
    pub fn block(&mut self, name: Option<String>, predecessors: u32) -> BlockId {
        BlockId(self.assignment(name, None, Block { predecessors }, vec![]))
    }

    /// Create a [path condition][crate::ast::Pc].
    ///
    /// Expresses the fact that `x` must equal `y` for the replacement to be
    /// valid.
    pub fn pc(&mut self, x: impl Into<Operand>, y: impl Into<Operand>) {
        let x = x.into();
        let y = y.into();
        self.statements.alloc(Pc { x, y }.into());
    }

    /// Create a [block path condition][crate::ast::BlockPc].
    ///
    /// Expresses that `x` is equal to `y` on an incoming edge to `block` in the
    /// control-flow graph.
    ///
    /// # Panics
    ///
    /// Panics if `predecessor` is greater than or equal to `block`'s number of
    /// predecessors.
    pub fn block_pc(
        &mut self,
        block: BlockId,
        predecessor: u32,
        x: impl Into<Operand>,
        y: impl Into<Operand>,
    ) {
        let x = x.into();
        let y = y.into();
        self.statements.alloc(
            BlockPc {
                block,
                predecessor,
                x,
                y,
            }
            .into(),
        );
    }

    /// Finish building this `LeftHandSide`.
    pub fn finish(
        self,
        lhs: ValueId,
        attributes: impl IntoIterator<Item = RootAttribute>,
    ) -> LeftHandSide {
        LeftHandSide {
            statements: self.statements,
            infer: Infer {
                value: lhs,
                attributes: attributes.into_iter().collect(),
            },
        }
    }

    /// Get the assignment that created the given value.
    ///
    /// # Panics
    ///
    /// May panic when given a `ValudId` from a different LHS, RHS, or
    /// replacement.
    pub fn get_value(&self, id: ValueId) -> &Assignment {
        match &self.statements[id.into()] {
            Statement::Assignment(a) => a,
            _ => panic!(),
        }
    }
}

/// The root of a left-hand side.
#[derive(Clone, Debug)]
pub struct Infer {
    /// The value to be replaced by the right-hand side.
    pub value: ValueId,

    /// Attributes for this left-hand side.
    pub attributes: Vec<RootAttribute>,
}

/// The right-hand side of a replacement.
#[derive(Clone, Debug)]
pub struct RightHandSide {
    /// Statements making up this RHS's expression DAG.
    pub statements: Arena<Statement>,

    /// The root of this RHS's expression DAG.
    pub result: Operand,
}

/// A statement in a LHS or RHS.
#[derive(Clone, Debug)]
pub enum Statement {
    /// An assignment statement.
    Assignment(Assignment),

    /// A path condition statement.
    Pc(Pc),

    /// A block path condition statement.
    BlockPc(BlockPc),
}

impl From<Assignment> for Statement {
    fn from(a: Assignment) -> Self {
        Statement::Assignment(a)
    }
}

impl From<Pc> for Statement {
    fn from(pc: Pc) -> Self {
        Statement::Pc(pc)
    }
}

impl From<BlockPc> for Statement {
    fn from(bpc: BlockPc) -> Self {
        Statement::BlockPc(bpc)
    }
}

/// An assignment, defining a value.
#[derive(Clone, Debug)]
pub struct Assignment {
    /// The name of the value being defined by this assignment.
    pub name: String,

    /// The ascribed type, if any.
    pub r#type: Option<Type>,

    /// The value being bound in this assignment.
    pub value: AssignmentRhs,

    /// Attributes describing data-flow facts known about this value.
    pub attributes: Vec<Attribute>,
}

/// Any value that can be assigned to a name.
#[derive(Clone, Debug)]
pub enum AssignmentRhs {
    /// An input variable.
    Var,

    /// A basic block.
    Block(Block),

    /// A phi node.
    Phi(Phi),

    /// A hole reserved for an as-of-yet-unknown instruction.
    ReservedInst,

    /// A hole reserved for an as-of-yet-unknown constant.
    ReservedConst,

    /// An instruction and its operands.
    Instruction(Instruction),
}

impl From<Block> for AssignmentRhs {
    fn from(b: Block) -> Self {
        AssignmentRhs::Block(b)
    }
}

impl From<Phi> for AssignmentRhs {
    fn from(p: Phi) -> Self {
        AssignmentRhs::Phi(p)
    }
}

impl From<Instruction> for AssignmentRhs {
    fn from(i: Instruction) -> Self {
        AssignmentRhs::Instruction(i)
    }
}

/// An input variable.
#[derive(Clone, Debug)]
pub struct Var {
    /// Attributes describing dataflow facts known about this input variable.
    pub attributes: Vec<Attribute>,
}

/// A basic block.
#[derive(Clone, Debug)]
pub struct Block {
    /// The number of incoming predecessors that this basic block has in the
    /// control-flow graph.
    pub predecessors: u32,
}

/// A phi node.
///
/// If a phi's `block` has `n` predecessors, then the length of `values` must be
/// `n`.
///
/// All phi nodes associated with a particular `block` will have their `i`th
/// value selected when control flow comes from `block`'s `i`th predecessor. For
/// example, given:
///
/// ```text
/// %bb = block 3
/// %a = phi %bb, 1, 2, 3
/// %b = phi %bb, 4, 5, 6
/// %c = phi %bb, 7, 8, 9
/// ```
///
/// If the basic block `%bb` has three control-flow predecessors. If it is
/// entered via its first predecessor, then `%a == 1`, `%b == 4`, and `%c ==
/// 7`. If it is entered via its second predecessor, then `%a == 2`, `%b == 5`,
/// and `%c == 8`. Finally, if it is entered via its third predecessor, then `%a
/// == 3`, `%b == 6`, and `%c == 9`.
#[derive(Clone, Debug)]
pub struct Phi {
    /// The basic block that this phi node is contained within.
    pub block: BlockId,

    /// The potential values for this phi node.
    pub values: Vec<Operand>,
}

macro_rules! define_instructions {
    (
        $(
            $( #[$attr:meta] )*
            $token:literal => $inst:ident $( ( $($operand:ident),* ) )? ;
        )*
    ) => {
        /// A Souper instruction.
        #[derive(Copy, Clone, Debug)]
        pub enum Instruction {
            $(
                $( #[$attr] )*
                $inst $( { $(
                    #[allow(missing_docs)]
                    $operand: Operand
                ),* } )? ,
            )*
        }

        #[cfg(feature = "parse")]
        impl crate::parse::Peek for Instruction {
            fn peek<'a>(parser: &mut crate::parse::Parser<'a>) -> crate::parse::Result<bool> {
                match parser.lookahead()? {
                    Some(crate::parse::Token::Ident(ident)) => Ok( false $( || ident == $token )* ),
                    _ => Ok(false),
                }
            }
        }

        #[cfg(feature = "parse")]
        impl crate::parse::Parse for Instruction {
            fn parse<'a>(parser: &mut crate::parse::Parser<'a>) -> crate::parse::Result<Self> {
                let ident = parser.token()?;
                match ident {
                    $(
                        #[allow(unused_assignments)]
                        crate::parse::Token::Ident($token) => {
                            $(
                                let mut first = true;
                                $(
                                    if !first {
                                        parser.comma()?;
                                    }
                                    let $operand = Operand::parse(parser)?;
                                    first = false;
                                )*
                            )?
                            Ok(Instruction::$inst $( { $( $operand ),* } )? )
                        }
                    )*
                    _ => parser.error("expected instruction"),
                }
            }
        }

        #[cfg(feature = "stringify")]
        impl Instruction {
            pub(crate) fn value_ids(&self, mut f: impl FnMut(ValueId)) {
                match self {
                    $(
                        Instruction::$inst $( { $( $operand ),* } )? => {
                            $(
                                $(
                                    if let Operand::Value(v) = $operand {
                                        f(*v);
                                    }
                                )*
                            )?
                        }
                    )*
                }
            }

            pub(crate) fn operands(&self, mut f: impl FnMut(Operand)) {
                match self {
                    $(
                        Instruction::$inst $( { $( $operand ),* } )? => {
                            $(
                                $(
                                    f(*$operand);
                                )*
                            )?
                        }
                    )*
                }
            }

            pub(crate) fn instruction_name(&self) -> &'static str {
                match self {
                    $(
                        Instruction::$inst $( { $( $operand: _),* } )? => $token,
                    )*
                }
            }
        }
    };
}

define_instructions! {
    /// Wrapping integer addition.
    "add" => Add(a, b);

    /// Integer addition where signed overflow is undefined behavior.
    "addnsw" => AddNsw(a, b);

    /// Integer addition where unsigned overflow is undefined behavior.
    "addnuw" => AddNuw(a, b);

    /// Integer addition where any kind of overflow is undefined behavior.
    "addnw" => AddNw(a, b);

    /// Wrapping integer subtraction.
    "sub" => Sub(a, b);

    /// Integer subtraction where signed overflow is undefined behavior.
    "subnsw" => SubNsw(a, b);

    /// Integer subtraction where unsigned overflow is undefined behavior.
    "subnuw" => SubNuw(a, b);

    /// Integer subtraction where any kind of overflow is undefined behavior.
    "subnw" => SubNw(a, b);

    /// Wrapping integer multiplication.
    "mul" => Mul(a, b);

    /// Integer multiplication where signed overflow is undefined behavior.
    "mulnsw" => MulNsw(a, b);

    /// Integer multiplication where unsigned overflow is undefined behavior.
    "mulnuw" => MulNuw(a, b);

    /// Integer multiplication where any kind of overflow is undefined behavior.
    "mulnw" => MulNw(a, b);

    /// Unsigned integer division.
    "udiv" => Udiv(a, b);

    /// Signed integer division.
    "sdiv" => Sdiv(a, b);

    /// Unsigned division where `a` must be exactly divisible by `b`. If `a` is
    /// not exactly divisible by `b`, then the result is undefined behavior.
    "udivexact" => UdivExact(a, b);

    /// Signed division where `a` must be exactly divisible by `b`. If `a` is
    /// not exactly divisible by `b`, then the result is undefined behavior.
    "sdivexact" => SdivExact(a, b);

    /// Unsigned integer remainder.
    "urem" => Urem(a, b);

    /// Signed integer remainder.
    "srem" => Srem(a, b);

    /// Bit-wise and.
    "and" => And(a, b);

    /// Bit-wise or.
    "or" => Or(a, b);

    /// Bit-wise xor.
    "xor" => Xor(a, b);

    /// Bit shift left. Undefined behavior if `b` is greater than or equal to `bitwidth(a)`.
    "shl" => Shl(a, b);

    /// Bit shift left where shifting out any non-sign bits is undefined
    /// behavior.
    "shlnsw" => ShlNsw(a, b);

    /// Bit shift left where shifting out any non-zero bits is undefined
    /// behavior.
    "shlnuw" => ShlNuw(a, b);

    /// Bit shift left where shifting out any non-zero or non-sign bits is
    /// undefined behavior.
    "shlnw" => ShlNw(a, b);

    /// Logical bit shift right (fills left `b` bits with zero).  Undefined
    /// behavior if `b` is greater than or equal to `bitwidth(a)`.
    "lshr" => Lshr(a, b);

    /// Logical bit shift right (fills left `b` bits with zero) where it is
    /// undefined behavior if any bits shifted out are non-zero.
    "lshrexact" => LshrExact(a, b);

    /// Arithmetic bit shift right (sign extends the left `b` bits).
    "ashr" => Ashr(a, b);

    /// Arithmetic bit shift right (fills left `b` bits with zero) where it is
    /// undefined behavior if any bits shifted out are non-zero.
    "ashrexact" => AshrExact(a, b);

    /// If `a` is 1, then evaluates to `b`, otherwise evaluates to `c`.
    "select" => Select(a, b, c);

    /// Zero extend `a`.
    "zext" => Zext(a);

    /// Sign extend `a`.
    "sext" => Sext(a);

    /// Truncate `a`.
    "trunc" => Trunc(a);

    /// `a == b`.
    "eq" => Eq(a, b);

    /// `a != b`
    "ne" => Ne(a, b);

    /// Unsigned less than.
    "ult" => Ult(a, b);

    /// Signed less than.
    "slt" => Slt(a, b);

    /// Unsigned less than or equal.
    "ule" => Ule(a, b);

    /// Signed less than or equal.
    "sle" => Sle(a, b);

    /// Count the number of 1 bits in `a`.
    "ctpop" => Ctpop(a);

    /// Swap bytes in `a`, e.g. `0xaabbccdd` becomes `0xddccbbaa`.
    "bswap" => Bswap(a);

    /// Reverse the bits in `a`.
    "bitreverse" => BitReverse(a);

    /// Count trailing zero bits in `a`.
    "cttz" => Cttz(a);

    /// Count leading one bits in `a`.
    "ctlz" => Ctlz(a);

    /// Left funnel shift.
    "fshl" => Fshl(a, b, c);

    /// Right funnel shift.
    "fshr" => Fshr(a, b, c);

    /// Wrapping signed integer addition of `a` and `b` where the result is
    /// extended by one bit which indicates whether the addition overflowed.
    "sadd.with.overflow" => SaddWithOverflow(a, b);

    /// Wrapping unsigned integer addition of `a` and `b` where the result is
    /// extended by one bit which indicates whether the addition overflowed.
    "uadd.with.overflow" => UaddWithOverflow(a, b);

    /// Wrapping signed integer subtraction of `a` and `b` where the result is
    /// extended by one bit which indicates whether the subtraction overflowed.
    "ssub.with.overflow" => SsubWithOverflow(a, b);

    /// Wrapping unsigned integer subtraction of `a` and `b` where the result is
    /// extended by one bit which indicates whether the subtraction overflowed.
    "usub.with.overflow" => UsubWithOverflow(a, b);

    /// Wrapping signed integer multiplication of `a` and `b` where the result
    /// is extended by one bit which indicates whether the multiplication
    /// overflowed.
    "smul.with.overflow" => SmulWithOverflow(a, b);

    /// Wrapping unsigned integer multiplication of `a` and `b` where the result
    /// is extended by one bit which indicates whether the multiplication
    /// overflowed.
    "umul.with.overflow" => UmulWithOverflow(a, b);

    /// Signed saturating integer addition.
    "sadd.sat" => SaddSat(a, b);

    /// Unsigned saturating integer addition.
    "uadd.sat" => UaddSat(a, b);

    /// Signed saturating integer subtraction.
    "ssub.sat" => SsubSat(a, b);

    /// Unsigned saturating integer subtraction.
    "usub.sat" => UsubSat(a, b);

    /// Extract the `b`th value from `a`.
    "extractvalue" => ExtractValue(a, b);

    /// A hole reserved for an unknown instruction or value.
    "hole" => Hole;

    /// If `a` is a poison or undef value, returns an arbitrary but fixed
    /// value. Otherwise returns `a`.
    "freeze" => Freeze(a);
}

/// An operand for an instruction or some other kind of operation.
#[derive(Copy, Clone, Debug)]
pub enum Operand {
    /// The id of a value defined in an earlier statement.
    Value(ValueId),

    /// A literal constant value.
    Constant(Constant),
}

impl From<Constant> for Operand {
    fn from(c: Constant) -> Self {
        Operand::Constant(c)
    }
}

impl From<ValueId> for Operand {
    fn from(v: ValueId) -> Self {
        Operand::Value(v)
    }
}

/// Attributes describing data-flow facts known about the root of a left- or
/// right-hand side.
#[derive(Clone, Debug)]
pub enum RootAttribute {
    /// Which bits of the resulting value are actually used.
    ///
    /// The vector must have a boolean for each bit in the result type, e.g. if
    /// the result type is `i32`, then the vector's length must be 32.
    ///
    /// If the `n`th entry in the vector is `true`, then the `n`th bit of the
    /// result is used. If it is `false`, then that bit is not used.
    DemandedBits(Vec<bool>),

    /// TODO
    HarvestedFromUse,
}

/// Attributes describing data-flow facts known about a particular value or
/// result of an instruction.
#[derive(Clone, Debug)]
pub enum Attribute {
    /// Bits that are known to be set or unset.
    ///
    /// The vector must have an entry for each bit in the value, e.g. if the
    /// value's type is `i32`, then the vector's length must be 32.
    ///
    /// If the `i`th bit is known to be set, then the `i`th entry should be
    /// `Some(true)`. If the `i`th bit is known to be unset, then the `i`th
    /// entry should be `Some(false)`. If it is unknown whether the `i`th bit is
    /// set or unset, or it can sometimes be either, then the `i`th entry should
    /// be `None`.
    KnownBits(Vec<Option<bool>>),

    /// The value is known to be a power of two.
    PowerOfTwo,

    /// The value is known to be negative.
    Negative,

    /// The value is known to be non-negative.
    NonNegative,

    /// The value is known to be non-zero.
    NonZero,

    /// The value is used by other expressions, not just this replacement's
    /// expression DAG.
    HasExternalUses,

    /// It is known that there are `n` sign bits in this value.
    SignBits(u8),

    /// This value is within the range `.0` (inclusive) to `.1` (exclusive).
    Range(i128, i128),
}

/// A path condition.
///
/// Expresses the fact that `x` must equal `y` for the replacement to be valid.
#[derive(Clone, Debug)]
pub struct Pc {
    /// A value that must be equal to `y` for the replacement to be valid.
    pub x: Operand,

    /// A value that must be equal to `x` for the replacement to be valid.
    pub y: Operand,
}

/// A block path condition.
///
/// Expresses that `x` is equal to `y` on an incoming predecessor to `block` in
/// the control-flow graph.
#[derive(Clone, Debug)]
pub struct BlockPc {
    /// The basic block in question.
    pub block: BlockId,

    /// The `i`th control-flow predecessor of `block`.
    ///
    /// Zero-indexed: must be less than `block`'s total number of predecessors.
    pub predecessor: u32,

    /// Must be equal to `y` if control-flow entered `block` via `predecessor`.
    pub x: Operand,

    /// Must be equal to `x` if control-flow entered `block` via `predecessor`.
    pub y: Operand,
}

/// A constant value.
///
/// Optionally has an ascribed type.
#[derive(Copy, Clone, Debug)]
pub struct Constant {
    /// The constant value.
    pub value: i128,

    /// The ascribed type, if any.
    pub r#type: Option<Type>,
}

/// A type.
///
/// All Souper types are integers, they just have different bit widths.
#[derive(Copy, Clone, Debug)]
pub struct Type {
    /// The bit width of this integer type.
    pub width: u16,
}
