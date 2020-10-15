//! Emitting Souper IR's text format.

use crate::ast;
use id_arena::{Arena, Id};
use std::{
    collections::HashSet,
    fmt::{self, Display},
};

/// Like `std::fmt::Display`, but with an arena of `ast::Statement`s as context.
trait DisplayWithContext {
    fn display(&self, statements: &Arena<ast::Statement>, f: &mut fmt::Formatter) -> fmt::Result;
}

fn topo_sort_statements(
    stmts: &Arena<ast::Statement>,
    seen: &mut HashSet<Id<ast::Statement>>,
    root: Id<ast::Statement>,
) -> Vec<Id<ast::Statement>> {
    let mut seq = vec![];

    let mut stack = vec![Entry::Trace(root)];
    while let Some(entry) = stack.pop() {
        let id = match entry {
            Entry::Finished(id) => {
                seq.push(id);
                continue;
            }
            Entry::Trace(id) if seen.contains(&id) => continue,
            Entry::Trace(id) => {
                seen.insert(id);
                id
            }
        };

        stack.push(Entry::Finished(id));

        match &stmts[id] {
            ast::Statement::Pc(ast::Pc { x, y }) => {
                if let ast::Operand::Value(v) = *y {
                    stack.push(Entry::Trace(v.into()));
                }
                if let ast::Operand::Value(v) = *x {
                    stack.push(Entry::Trace(v.into()));
                }
            }
            ast::Statement::BlockPc(ast::BlockPc {
                block,
                predecessor: _,
                x,
                y,
            }) => {
                if let ast::Operand::Value(v) = *y {
                    stack.push(Entry::Trace(v.into()));
                }
                if let ast::Operand::Value(v) = *x {
                    stack.push(Entry::Trace(v.into()));
                }
                stack.push(Entry::Trace((*block).into()));
            }
            ast::Statement::Assignment(ast::Assignment { value, .. }) => match value {
                | ast::AssignmentRhs::Var
                | ast::AssignmentRhs::Block(_)
                | ast::AssignmentRhs::ReservedInst
                | ast::AssignmentRhs::ReservedConst => continue,
                ast::AssignmentRhs::Phi(ast::Phi { block, values }) => {
                    for v in values.iter().rev().copied() {
                        if let ast::Operand::Value(v) = v {
                            stack.push(Entry::Trace(v.into()));
                        }
                    }
                    stack.push(Entry::Trace((*block).into()));
                }
                ast::AssignmentRhs::Instruction(inst) => {
                    let n = stack.len();
                    inst.value_ids(|v| stack.push(Entry::Trace(v.into())));
                    stack[n..].reverse();
                }
            },
        }
    }

    return seq;

    enum Entry {
        Trace(Id<ast::Statement>),
        Finished(Id<ast::Statement>),
    }
}

impl Display for ast::Replacement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut seen = HashSet::new();
        match self {
            ast::Replacement::LhsRhs {
                statements,
                lhs,
                rhs,
            } => {
                for s in topo_sort_statements(statements, &mut seen, lhs.value.into()) {
                    statements[s].display(statements, f)?;
                }
                lhs.display(statements, f)?;
                match rhs {
                    ast::Operand::Value(v) => {
                        for s in topo_sort_statements(statements, &mut seen, (*v).into()) {
                            statements[s].display(statements, f)?;
                        }
                        writeln!(f, "result {}", self.assignment(*v).name)
                    }
                    ast::Operand::Constant(ast::Constant { value, r#type }) => {
                        write!(f, "result {}", value)?;
                        if let Some(ty) = r#type {
                            write!(f, ":{}", ty)?;
                        }
                        writeln!(f)
                    }
                }
            }
            ast::Replacement::Cand { statements, cand } => {
                if let ast::Operand::Value(v) = cand.lhs {
                    for s in topo_sort_statements(statements, &mut seen, v.into()) {
                        statements[s].display(statements, f)?;
                    }
                }
                if let ast::Operand::Value(v) = cand.rhs {
                    for s in topo_sort_statements(statements, &mut seen, v.into()) {
                        statements[s].display(statements, f)?;
                    }
                }
                cand.display(statements, f)
            }
        }
    }
}

impl Display for ast::LeftHandSide {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut seen = HashSet::new();
        for s in topo_sort_statements(&self.statements, &mut seen, self.infer.value.into()) {
            self.statements[s].display(&self.statements, f)?;
        }
        self.infer.display(&self.statements, f)
    }
}

impl Display for ast::RightHandSide {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut seen = HashSet::new();
        if let ast::Operand::Value(v) = self.result {
            for s in topo_sort_statements(&self.statements, &mut seen, v.into()) {
                self.statements[s].display(&self.statements, f)?;
            }
        }
        write!(f, "result ")?;
        self.result.display(&self.statements, f)
    }
}

fn assignment(statements: &Arena<ast::Statement>, id: ast::ValueId) -> &ast::Assignment {
    match &statements[id.into()] {
        ast::Statement::Assignment(a) => a,
        _ => panic!("use of an `id` that is not from this `Replacement`'s arena"),
    }
}

impl DisplayWithContext for ast::Infer {
    fn display(&self, statements: &Arena<ast::Statement>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "infer ")?;
        self.value.display(statements, f)?;
        for attr in &self.attributes {
            write!(f, " {}", attr)?;
        }
        writeln!(f)
    }
}

impl DisplayWithContext for ast::Cand {
    fn display(&self, statements: &Arena<ast::Statement>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "cand ")?;
        self.lhs.display(statements, f)?;
        write!(f, " ")?;
        self.rhs.display(statements, f)?;
        for attr in &self.attributes {
            write!(f, " {}", attr)?;
        }
        writeln!(f)
    }
}

impl DisplayWithContext for ast::Statement {
    fn display(&self, statements: &Arena<ast::Statement>, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ast::Statement::Assignment(a) => a.display(statements, f)?,
            ast::Statement::Pc(pc) => pc.display(statements, f)?,
            ast::Statement::BlockPc(bpc) => bpc.display(statements, f)?,
        }

        writeln!(f)
    }
}

impl DisplayWithContext for ast::Assignment {
    fn display(&self, statements: &Arena<ast::Statement>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)?;
        if let Some(ty) = self.r#type {
            write!(f, ":{}", ty)?;
        }
        write!(f, " = ")?;
        self.value.display(statements, f)?;
        for attr in &self.attributes {
            write!(f, " {}", attr)?;
        }
        Ok(())
    }
}

impl DisplayWithContext for ast::AssignmentRhs {
    fn display(&self, statements: &Arena<ast::Statement>, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ast::AssignmentRhs::Var => write!(f, "var"),
            ast::AssignmentRhs::Block(block) => <ast::Block as Display>::fmt(block, f),
            ast::AssignmentRhs::Phi(phi) => phi.display(statements, f),
            ast::AssignmentRhs::ReservedInst => write!(f, "reservedinst"),
            ast::AssignmentRhs::ReservedConst => write!(f, "reservedconst"),
            ast::AssignmentRhs::Instruction(inst) => inst.display(statements, f),
        }
    }
}

impl Display for ast::Block {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "block {}", self.predecessors)
    }
}

impl DisplayWithContext for ast::Phi {
    fn display(&self, statements: &Arena<ast::Statement>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "phi ")?;
        self.block.display(statements, f)?;
        for v in &self.values {
            write!(f, ", ")?;
            v.display(statements, f)?;
        }
        Ok(())
    }
}

impl DisplayWithContext for ast::Instruction {
    fn display(&self, statements: &Arena<ast::Statement>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.instruction_name())?;
        let mut first = true;
        let mut result = Ok(());
        self.operands(|x| {
            result = result.and_then(|_| {
                if first {
                    write!(f, " ")?;
                    first = false;
                } else {
                    write!(f, ", ")?;
                }
                x.display(statements, f)
            });
        });
        result
    }
}

impl DisplayWithContext for ast::Pc {
    fn display(&self, statements: &Arena<ast::Statement>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "pc ")?;
        self.x.display(statements, f)?;
        write!(f, " ")?;
        self.y.display(statements, f)
    }
}

impl DisplayWithContext for ast::BlockPc {
    fn display(&self, statements: &Arena<ast::Statement>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "blockpc ")?;
        self.block.display(statements, f)?;
        write!(f, " {}", self.predecessor)?;
        self.x.display(statements, f)?;
        write!(f, " ")?;
        self.y.display(statements, f)
    }
}

impl Display for ast::RootAttribute {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(")?;
        match self {
            ast::RootAttribute::DemandedBits(db) => {
                write!(f, "demandedBits=")?;
                for b in db {
                    if *b {
                        write!(f, "1")?;
                    } else {
                        write!(f, "0")?;
                    }
                }
            }
            ast::RootAttribute::HarvestedFromUse => write!(f, "harvestedFromUse")?,
        }
        write!(f, ")")
    }
}

impl Display for ast::Attribute {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(")?;
        match self {
            ast::Attribute::KnownBits(bits) => {
                write!(f, "knownBits=")?;
                for b in bits {
                    match b {
                        None => write!(f, "x")?,
                        Some(true) => write!(f, "1")?,
                        Some(false) => write!(f, "0")?,
                    }
                }
            }
            ast::Attribute::PowerOfTwo => write!(f, "powerOfTwo")?,
            ast::Attribute::Negative => write!(f, "negative")?,
            ast::Attribute::NonNegative => write!(f, "nonNegative")?,
            ast::Attribute::NonZero => write!(f, "nonZero")?,
            ast::Attribute::HasExternalUses => write!(f, "hasExternalUses")?,
            ast::Attribute::SignBits(n) => write!(f, "signBits={}", n)?,
            ast::Attribute::Range(min, max) => write!(f, "range=[{},{})", min, max)?,
        }
        write!(f, ")")
    }
}

impl DisplayWithContext for ast::Operand {
    fn display(&self, statements: &Arena<ast::Statement>, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ast::Operand::Value(id) => id.display(statements, f),
            ast::Operand::Constant(c) => <ast::Constant as Display>::fmt(c, f),
        }
    }
}

impl Display for ast::Constant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)?;
        if let Some(ty) = self.r#type {
            write!(f, ":{}", ty)?;
        }
        Ok(())
    }
}

impl DisplayWithContext for ast::ValueId {
    fn display(&self, statements: &Arena<ast::Statement>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", assignment(statements, *self).name)
    }
}

impl DisplayWithContext for ast::BlockId {
    fn display(&self, statements: &Arena<ast::Statement>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", assignment(statements, self.0).name)
    }
}

impl Display for ast::Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "i{}", self.width)
    }
}
