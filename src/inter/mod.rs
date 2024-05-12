#![allow(dead_code)]
//! IR

use std::{collections::HashMap, rc::Rc};

use num_traits::ToPrimitive;

use crate::{
    inter::{ir::Inst, types::PrimitiveType},
    parse::ast::{
        self, BinOp, Block, Expr, FieldDecl, FieldDeclarator, Ident, Location, MethodCall,
        MethodCallArg, MethodDecl, RuntimeLiteral, Stmt, UnaryOp, UpdateOp,
    },
    scan::location::{Span, Spanned},
};

use self::{
    constant::{Const, INT_0, INT_MAX},
    error::SemanticError,
    ir::{Address, BlockRef, GlobalVar, InstRef, Method, StackSlotRef, Terminator},
    types::Type,
};

pub mod constant;
pub mod error;
pub mod ir;
pub mod types;

#[derive(Debug, Clone)]
struct Var {
    name: Ident,
    ty: Type,
    is_const: bool,
}

pub struct IrBuilder {
    errors: Vec<SemanticError>,

    methods: HashMap<String, Method>,
    imported_methods: HashMap<String, Ident>,
    global_vars: HashMap<String, Var>,
    global_inits: HashMap<String, Const>,
}

impl IrBuilder {
    pub fn new() -> Self {
        Self {
            errors: Vec::new(),
            methods: HashMap::new(),
            imported_methods: HashMap::new(),

            global_vars: HashMap::new(),
            global_inits: HashMap::new(),
        }
    }

    fn emit_error(&mut self, error: SemanticError) {
        self.errors.push(error);
    }

    fn lookup(&self, name: &str) -> Option<&Var> {
        self.global_vars.get(name)
    }

    fn add_global(&mut self, var: Var, init_value: Const) {
        self.global_inits
            .insert(var.name.inner.to_string(), init_value);
        self.global_vars.insert(var.name.inner.to_string(), var);
    }

    pub fn check_program(
        &mut self,
        program: &ast::Program,
    ) -> Result<ir::Program, Vec<SemanticError>> {
        // Add imported methods to the symbol table
        for import_decl in &program.import_decls {
            if let Some(prev_decl) = self.imported_methods.get(&*import_decl.0.inner) {
                self.emit_error(SemanticError::DuplicateDecls {
                    first: prev_decl.clone(),
                    second: import_decl.0.clone(),
                });
                continue;
            }
            self.imported_methods
                .insert(import_decl.0.inner.to_string(), import_decl.0.clone());
        }
        for field_decl in &program.field_decls {
            FieldDeclContext::Global(self).check_field_decl(field_decl);
        }
        for method_decl in &program.method_decls {
            self.check_method_decl(method_decl);
        }
        match self.methods.get("main") {
            Some(main) if main.return_ty == Type::Void && main.params.is_empty() => {}
            invalid => self.emit_error(SemanticError::InvalidMainMethod(
                invalid.map(|m| m.name.clone()),
            )),
        }
        if self.errors.is_empty() {
            Ok(ir::Program {
                imports: std::mem::take(&mut self.imported_methods),
                methods: std::mem::take(&mut self.methods),
                globals: std::mem::take(&mut self.global_vars)
                    .into_values()
                    .map(|v| {
                        (
                            v.name.inner.to_string(),
                            GlobalVar {
                                init: self.global_inits.remove(&*v.name.inner).unwrap(),
                                ty: v.ty,
                                name: v.name,
                                is_const: v.is_const,
                            },
                        )
                    })
                    .collect(),
            })
        } else {
            Err(self.errors.clone())
        }
    }

    fn check_method_decl(&mut self, method_decl: &MethodDecl) {
        let name = &method_decl.name;
        if let Some(prev_decl) = self
            .imported_methods
            .get(&*name.inner)
            .or_else(|| self.methods.get(&*name.inner).map(|method| &method.name))
            .or_else(|| self.global_vars.get(&*name.inner).map(|var| &var.name))
        {
            self.emit_error(SemanticError::DuplicateDecls {
                first: prev_decl.clone(),
                second: name.clone(),
            });
            return;
        }
        let method = MethodBuilder::new(self, method_decl).build();
        self.methods.insert(name.inner.to_string(), method);
    }
}

struct LocalVar {
    var: Var,
    stack_slot: StackSlotRef,
}

struct LoopLabels {
    break_: BlockRef,
    continue_: BlockRef,
}

struct MethodBuilder<'a> {
    builder: &'a mut IrBuilder,
    method: Method,
    method_decl: &'a MethodDecl,

    locals: Vec<HashMap<String, LocalVar>>,
    /// How many loops are we currently in?
    /// Used to determine if a `break` or `continue` statement is valid.
    loop_labels: Vec<LoopLabels>,
}

impl<'a> MethodBuilder<'a> {
    fn new(builder: &'a mut IrBuilder, method_decl: &'a MethodDecl) -> Self {
        let return_ty = match &method_decl.return_ty {
            Some(ty) => Type::Primitive(PrimitiveType::from(ty)),
            None => Type::Void,
        };
        let mut params = vec![];
        for param in &method_decl.params {
            let name = &param.name;
            let ty = Type::Primitive(PrimitiveType::from(&param.ty));
            params.push((name.clone(), ty));
        }
        let method = Method::new(
            method_decl.name.clone(),
            return_ty,
            params.clone(),
            method_decl.body.span.clone(),
        );
        let mut ret = Self {
            builder,
            method,
            method_decl,
            locals: vec![],
            loop_labels: vec![],
        };
        ret.add_params(params);
        ret
    }

    fn emit_error(&mut self, error: SemanticError) {
        self.builder.emit_error(error);
    }

    fn lookup(&self, name: &str) -> Option<(&Var, Address)> {
        for scope in self.locals.iter().rev() {
            if let Some(local) = scope.get(name) {
                return Some((&local.var, Address::Local(local.stack_slot)));
            }
        }
        self.builder
            .lookup(name)
            .map(|var| (var, Address::Global(var.name.inner.clone())))
    }

    fn lookup_local(&self, name: &str) -> Option<&Var> {
        self.locals
            .last()
            .and_then(|scope| scope.get(name).map(|local| &local.var))
    }

    fn add_params(&mut self, params: Vec<(Ident, Type)>) {
        let mut param_scope = HashMap::<String, LocalVar>::new();
        for (name, ty) in params {
            if let Some(prev_decl) = param_scope.get(&*name.inner) {
                self.emit_error(SemanticError::DuplicateDecls {
                    first: prev_decl.var.name.clone(),
                    second: name.clone(),
                });
                continue;
            }
            let name_str = name.inner.to_string();
            let stack_slot = self.method.next_stack_slot(ty.clone(), name.clone());
            let local_var = LocalVar {
                var: Var {
                    name,
                    ty,
                    is_const: false,
                },
                stack_slot,
            };
            param_scope.insert(name_str, local_var);
        }
        self.locals.push(param_scope);
    }

    fn add_local(&mut self, var: Var, init_value: Const, block: BlockRef) {
        let name = var.name.inner.to_string();
        let stack_slot = self
            .method
            .next_stack_slot(var.ty.clone(), var.name.clone());
        self.method.next_inst(
            block,
            Inst::Initialize {
                stack_slot,
                value: init_value,
            },
        );
        let local_var = LocalVar { var, stack_slot };
        self.locals.last_mut().unwrap().insert(name, local_var);
    }

    fn build_block(&mut self, block: &Block, cur_block: BlockRef) -> BlockRef {
        self.locals.push(HashMap::new());
        let next_block = self.build_block_no_new_scope(block, cur_block);
        self.locals.pop();
        next_block
    }

    fn build_block_no_new_scope(&mut self, block: &Block, mut cur_block: BlockRef) -> BlockRef {
        for field_decl in &block.field_decls {
            FieldDeclContext::Local(self, cur_block).check_field_decl(field_decl);
        }
        for stmt in &block.stmts {
            cur_block = self.build_stmt(stmt, cur_block);
        }
        cur_block
    }

    fn build_stmt(&mut self, stmt: &Stmt, cur_block: BlockRef) -> BlockRef {
        match stmt {
            Stmt::Update { location, op } => self.build_update(location, op, cur_block),
            Stmt::Call(call) => self.build_call(call, cur_block).0,
            Stmt::If {
                condition,
                then_block,
                else_block,
            } => self.build_if(condition, then_block, else_block.as_ref(), cur_block),
            Stmt::For {
                loop_var_name,
                init,
                cond,
                update,
                block,
            } => self.build_for(loop_var_name, init, cond, update, block, cur_block),
            Stmt::While { condition, block } => self.build_while(condition, block, cur_block),
            Stmt::Return { span, expr } => self.build_return(span, expr, cur_block),
            Stmt::Break(span) => self.build_break(span, cur_block),
            Stmt::Continue(span) => self.build_continue(span, cur_block),
        }
    }

    fn build_update(
        &mut self,
        location: &Location,
        op: &UpdateOp,
        cur_block: BlockRef,
    ) -> BlockRef {
        match op {
            UpdateOp::Assign(value) => self.build_store(location, value, cur_block),
            _ => {
                let (next_block, lhs, lhs_ty) = self.build_load(location, cur_block);
                if lhs_ty != Type::Invalid && lhs_ty != Type::int() {
                    self.emit_error(SemanticError::NonNumericUpdate(Spanned {
                        inner: lhs_ty,
                        span: location.ident().span.clone(),
                    }));
                    return next_block;
                }
                if let Some((var, _)) = self.lookup(&location.ident().inner) {
                    if var.is_const {
                        self.emit_error(SemanticError::ReassigningConst {
                            decl_site: var.name.clone(),
                            assign_site: location.ident().clone(),
                        });
                    }
                }
                let (next_block, rhs) = match op {
                    UpdateOp::Increment | UpdateOp::Decrement => {
                        let one = self
                            .method
                            .next_inst(next_block, Inst::LoadConst(Const::Int(1)));
                        (next_block, one)
                    }
                    UpdateOp::AddAssign(value)
                    | UpdateOp::SubAssign(value)
                    | UpdateOp::MulAssign(value)
                    | UpdateOp::DivAssign(value)
                    | UpdateOp::ModAssign(value) => {
                        let (next_block, rhs, rhs_ty) = self.build_expr(value, next_block);
                        if rhs_ty != Type::Invalid && rhs_ty != Type::int() {
                            self.emit_error(SemanticError::NonNumericUpdate(Spanned {
                                inner: rhs_ty,
                                span: value.span.clone(),
                            }));
                            return next_block;
                        }
                        (next_block, rhs)
                    }
                    _ => unreachable!(),
                };
                let update_inst = match op {
                    UpdateOp::Increment => Inst::Add(lhs, rhs),
                    UpdateOp::Decrement => Inst::Sub(lhs, rhs),
                    UpdateOp::AddAssign(_) => Inst::Add(lhs, rhs),
                    UpdateOp::SubAssign(_) => Inst::Sub(lhs, rhs),
                    UpdateOp::MulAssign(_) => Inst::Mul(lhs, rhs),
                    UpdateOp::DivAssign(_) => Inst::Div(lhs, rhs),
                    UpdateOp::ModAssign(_) => Inst::Mod(lhs, rhs),
                    _ => unreachable!(),
                };
                let update_inst = self.method.next_inst(next_block, update_inst);
                let store_inst = match self.method.inst(lhs) {
                    Inst::Load(addr) => Inst::Store {
                        addr: addr.clone(),
                        value: update_inst,
                    },
                    Inst::LoadArray { addr, index } => Inst::StoreArray {
                        addr: addr.clone(),
                        index: *index,
                        value: update_inst,
                    },
                    _ => unreachable!(),
                };
                self.method.next_inst(next_block, store_inst);
                next_block
            }
        }
    }

    fn build_if(
        &mut self,
        condition: &Spanned<Expr>,
        then_block: &Block,
        else_block: Option<&Block>,
        cur_block: BlockRef,
    ) -> BlockRef {
        let true_block = self.method.next_block();
        let false_block = self.method.next_block();

        self.build_cond(condition, cur_block, true_block, false_block);

        let if_line_number = condition.span.start().line;
        self.method.annotate_block_mut(true_block).str =
            Some(format!("if-then block at line {}", if_line_number));

        let then_block = self.build_block(then_block, true_block);

        if let Some(else_block) = else_block {
            self.method.annotate_block_mut(false_block).str =
                Some(format!("if-else block at line {}", if_line_number));

            let else_block = self.build_block(else_block, false_block);
            let next_block = self.method.next_block();
            self.method.block_mut(then_block).term = Terminator::Jump(next_block);
            self.method.block_mut(else_block).term = Terminator::Jump(next_block);

            next_block
        } else {
            self.method.block_mut(then_block).term = Terminator::Jump(false_block);
            false_block
        }
    }

    fn build_while(
        &mut self,
        condition: &Spanned<Expr>,
        block: &Block,
        cur_block: BlockRef,
    ) -> BlockRef {
        let loop_block = self.method.next_block();
        let cond_block = self.method.next_block();
        let next_block = self.method.next_block();

        let loop_line_number = condition.span.start().line;
        self.method.annotate_block_mut(loop_block).str =
            Some(format!("while loop body at line {}", loop_line_number));
        self.method.annotate_block_mut(cond_block).str =
            Some(format!("while loop condition at line {}", loop_line_number));

        self.method.block_mut(cur_block).term = Terminator::Jump(cond_block);
        self.build_cond(condition, cond_block, loop_block, next_block);
        self.loop_labels.push(LoopLabels {
            break_: next_block,
            continue_: cond_block,
        });
        let loop_block = self.build_block(block, loop_block);
        self.loop_labels.pop();
        self.method.block_mut(loop_block).term = Terminator::Jump(cond_block);
        next_block
    }

    fn build_for(
        &mut self,
        loop_var_name: &Ident,
        init: &Spanned<Expr>,
        cond: &Spanned<Expr>,
        update: &Stmt,
        block: &Block,
        cur_block: BlockRef,
    ) -> BlockRef {
        if let Some((var, _)) = self.lookup(&loop_var_name.inner) {
            // Loop variable must be an integer.
            if var.ty != Type::Invalid && var.ty != Type::int() {
                self.emit_error(SemanticError::InvalidLoopVariable {
                    decl_site: var.name.clone(),
                    use_site: loop_var_name.clone(),
                    ty: var.ty.clone(),
                });
            }
        }
        let next_block = self.build_store(&Location::Ident(loop_var_name.clone()), init, cur_block);
        let loop_block = self.method.next_block();
        let cond_block = self.method.next_block();
        let update_block = self.method.next_block();

        let loop_line_number = loop_var_name.span.start().line;
        self.method.annotate_block_mut(loop_block).str =
            Some(format!("for loop body at line {}", loop_line_number));
        self.method.annotate_block_mut(update_block).str =
            Some(format!("for loop update at line {}", loop_line_number));
        self.method.annotate_block_mut(cond_block).str =
            Some(format!("for loop condition at line {}", loop_line_number));

        self.method.block_mut(next_block).term = Terminator::Jump(cond_block);
        let next_block = self.method.next_block();
        self.build_cond(cond, cond_block, loop_block, next_block);
        self.loop_labels.push(LoopLabels {
            break_: next_block,
            continue_: update_block,
        });
        let loop_block = self.build_block(block, loop_block);
        self.loop_labels.pop();
        self.method.block_mut(loop_block).term = Terminator::Jump(update_block);
        let update_block = self.build_stmt(update, update_block);
        self.method.block_mut(update_block).term = Terminator::Jump(cond_block);
        next_block
    }

    fn build_return(
        &mut self,
        span: &Span,
        expr: &Option<Spanned<Expr>>,
        cur_block: BlockRef,
    ) -> BlockRef {
        if let Some(expr) = expr {
            let (next_block, inst, ty) = self.build_expr(expr, cur_block);
            if ty != self.method.return_ty {
                self.emit_error(SemanticError::InvalidReturnType {
                    return_ty: self.method.return_ty.clone(),
                    expr_ty: Spanned {
                        inner: ty,
                        span: expr.span.clone(),
                    },
                    method: self.method.name.clone(),
                });
            }
            self.method.block_mut(next_block).term = Terminator::Return(Some(inst));
        } else {
            if Type::Void != self.method.return_ty {
                self.emit_error(SemanticError::InvalidReturnType {
                    return_ty: self.method.return_ty.clone(),
                    expr_ty: Spanned {
                        inner: Type::Void,
                        span: span.clone(),
                    },
                    method: self.method.name.clone(),
                });
            }
            self.method.block_mut(cur_block).term = Terminator::Return(None);
        }
        let unreachable_block = self.method.next_block();
        self.method.annotate_block_mut(unreachable_block).str =
            Some("unreachable (after return)".to_string());
        unreachable_block
    }

    fn build_break(&mut self, span: &Span, cur_block: BlockRef) -> BlockRef {
        match self.loop_labels.last() {
            Some(labels) => {
                self.method.block_mut(cur_block).term = Terminator::Jump(labels.break_);
                self.method.next_block()
            }
            None => {
                self.emit_error(SemanticError::InvalidBreak(span.clone()));
                cur_block
            }
        }
    }

    fn build_continue(&mut self, span: &Span, cur_block: BlockRef) -> BlockRef {
        match self.loop_labels.last() {
            Some(labels) => {
                self.method.block_mut(cur_block).term = Terminator::Jump(labels.continue_);
                self.method.next_block()
            }
            None => {
                self.emit_error(SemanticError::InvalidContinue(span.clone()));
                cur_block
            }
        }
    }

    fn build_expr(
        &mut self,
        expr: &Spanned<Expr>,
        cur_block: BlockRef,
    ) -> (BlockRef, InstRef, Type) {
        let (next_block, inst, ty) = self.build_expr_(expr, cur_block);
        if inst != InstRef::invalid() {
            // Annotate the instruction with the span of the expression.
            self.method.annotate_inst_mut(inst).span = Some(expr.span.clone());
        }
        (next_block, inst, ty)
    }

    fn build_expr_(
        &mut self,
        expr: &Spanned<Expr>,
        cur_block: BlockRef,
    ) -> (BlockRef, InstRef, Type) {
        match &expr.inner {
            Expr::Literal(lit) => self.build_literal(lit, cur_block),
            Expr::Location(loc) => self.build_load(loc, cur_block),
            Expr::Call(call) => self.build_call(call, cur_block),
            Expr::Len(ident) => self.build_len(ident, cur_block),
            Expr::BinOp { lhs, op, rhs } => {
                macro_rules! int_op {
                    ($ty:expr, $op:expr, $inst:expr) => {
                        self.build_int_op(lhs, rhs, cur_block, $ty, $op, $inst)
                    };
                }
                match op {
                    BinOp::Add => int_op!(Type::int(), BinOp::Add, Inst::Add),
                    BinOp::Sub => int_op!(Type::int(), BinOp::Sub, Inst::Sub),
                    BinOp::Mul => int_op!(Type::int(), BinOp::Mul, Inst::Mul),
                    BinOp::Div => int_op!(Type::int(), BinOp::Div, Inst::Div),
                    BinOp::Mod => int_op!(Type::int(), BinOp::Mod, Inst::Mod),
                    BinOp::Equal => int_op!(Type::bool(), BinOp::Equal, Inst::Eq),
                    BinOp::NotEqual => int_op!(Type::bool(), BinOp::NotEqual, Inst::Neq),
                    BinOp::Less => int_op!(Type::bool(), BinOp::Less, Inst::Less),
                    BinOp::LessEqual => int_op!(Type::bool(), BinOp::LessEqual, Inst::LessEq),
                    BinOp::Greater => {
                        let swap = |lhs, rhs| Inst::Less(rhs, lhs);
                        int_op!(Type::bool(), BinOp::Greater, swap)
                    }
                    BinOp::GreaterEqual => {
                        let swap = |lhs, rhs| Inst::LessEq(rhs, lhs);
                        int_op!(Type::bool(), BinOp::GreaterEqual, swap)
                    }
                    _ => {
                        let true_block = self.method.next_block();
                        let false_block = self.method.next_block();
                        let intermediate_stack_slot = self.method.next_stack_slot(
                            Type::Primitive(PrimitiveType::Bool),
                            Spanned {
                                inner: Rc::from(expr.span.source_str().as_ref()),
                                span: expr.span.clone(),
                            },
                        );
                        self.build_cond(expr, cur_block, true_block, false_block);
                        let true_inst = self
                            .method
                            .next_inst(true_block, Inst::LoadConst(Const::Bool(true)));
                        let _ = self.method.next_inst(
                            true_block,
                            Inst::Store {
                                addr: Address::Local(intermediate_stack_slot),
                                value: true_inst,
                            },
                        );
                        let false_inst = self
                            .method
                            .next_inst(false_block, Inst::LoadConst(Const::Bool(false)));
                        let next_block = self.method.next_block();
                        let _ = self.method.next_inst(
                            false_block,
                            Inst::Store {
                                addr: Address::Local(intermediate_stack_slot),
                                value: false_inst,
                            },
                        );
                        self.method.block_mut(true_block).term = Terminator::Jump(next_block);
                        self.method.block_mut(false_block).term = Terminator::Jump(next_block);
                        // let phi_inst = Inst::Phi(HashMap::from([
                        //     (true_block, true_inst),
                        //     (false_block, false_inst),
                        // ]));
                        // let phi_inst = self.method.next_inst(next_block, phi_inst);
                        let load_inst = self.method.next_inst(
                            next_block,
                            Inst::Load(Address::Local(intermediate_stack_slot)),
                        );
                        (next_block, load_inst, Type::bool())
                    }
                }
            }
            Expr::UnaryOp { op, expr } => {
                let (next_block, inst, ty) = self.build_expr(expr, cur_block);
                let (expect_ty, inst) = match op {
                    UnaryOp::Neg => (Type::int(), Inst::Neg(inst)),
                    UnaryOp::Not => (Type::bool(), Inst::Not(inst)),
                };
                if ty == expect_ty {
                    let neg_inst = self.method.next_inst(next_block, inst);
                    (next_block, neg_inst, ty)
                } else {
                    self.emit_error(SemanticError::InvalidUnaryOpType {
                        op: *op,
                        ty: Spanned {
                            inner: ty,
                            span: expr.span.clone(),
                        },
                    });
                    (next_block, InstRef::invalid(), Type::Invalid)
                }
            }
        }
    }

    fn build_int_op(
        &mut self,
        lhs: &Spanned<Expr>,
        rhs: &Spanned<Expr>,
        cur_block: BlockRef,
        ty: Type,
        op: BinOp,
        inst_builder: impl FnOnce(InstRef, InstRef) -> Inst,
    ) -> (BlockRef, InstRef, Type) {
        let (next_block, lhs_inst, lhs_ty) = self.build_expr(lhs, cur_block);
        let (next_block, rhs_inst, rhs_ty) = self.build_expr(rhs, next_block);
        let legal_ty = match op {
            BinOp::Equal | BinOp::NotEqual => {
                lhs_ty == rhs_ty && (lhs_ty == Type::int() || lhs_ty == Type::bool())
            }
            _ => lhs_ty == Type::int() && rhs_ty == Type::int(),
        };
        if legal_ty {
            let inst = self
                .method
                .next_inst(next_block, inst_builder(lhs_inst, rhs_inst));
            (next_block, inst, ty)
        } else {
            self.emit_error(SemanticError::InvalidBinOpTypes {
                op,
                lhs: Spanned {
                    inner: lhs_ty,
                    span: lhs.span.clone(),
                },
                rhs: Spanned {
                    inner: rhs_ty,
                    span: rhs.span.clone(),
                },
            });
            (next_block, InstRef::invalid(), Type::Invalid)
        }
    }

    fn build_cond(
        &mut self,
        expr: &Spanned<Expr>,
        cur_block: BlockRef,
        true_block: BlockRef,
        false_block: BlockRef,
    ) {
        match &expr.inner {
            #[rustfmt::skip]
            Expr::BinOp { lhs, op: BinOp::And, rhs } => {
                let new_true_block = self.method.next_block();
                self.build_cond(lhs, cur_block, new_true_block, false_block);
                self.build_cond(rhs, new_true_block, true_block, false_block);
            }
            #[rustfmt::skip]
            Expr::BinOp { lhs, op: BinOp::Or, rhs } => {
                let new_false_block = self.method.next_block();
                self.build_cond(lhs, cur_block, true_block, new_false_block);
                self.build_cond(rhs, new_false_block, true_block, false_block);
            }
            #[rustfmt::skip]
            Expr::UnaryOp { op: UnaryOp::Neg, expr } => {
                self.build_cond(expr, cur_block, false_block, true_block);
            }
            _ => {
                let (next_block, cond_inst, cond_ty) = self.build_expr(expr, cur_block);
                if cond_ty != Type::Invalid && cond_ty != Type::bool() {
                    self.emit_error(SemanticError::InvalidCondition(Spanned {
                        inner: cond_ty,
                        span: expr.span.clone(),
                    }));
                }
                self.method.block_mut(next_block).term = Terminator::CondJump {
                    cond: cond_inst,
                    true_: true_block,
                    false_: false_block,
                };
            }
        }
    }

    fn build_load(
        &mut self,
        location: &Location,
        cur_block: BlockRef,
    ) -> (BlockRef, InstRef, Type) {
        match location {
            Location::Ident(ident) => self.build_load_ident(ident, cur_block),
            Location::ArrayAccess {
                ident,
                index: index_expr,
            } => {
                let ident = match &**ident {
                    Location::Ident(ident) => ident,
                    _ => unreachable!("multi-dim array loading unsupported yet"),
                };
                self.build_load_array(ident, index_expr, cur_block)
            }
        }
    }

    fn build_load_ident(
        &mut self,
        ident: &Ident,
        cur_block: BlockRef,
    ) -> (BlockRef, InstRef, Type) {
        let (var, addr) = match self.lookup(&ident.inner) {
            Some(pair) => pair,
            None => {
                self.emit_error(SemanticError::UnknownVar(ident.clone()));
                return (cur_block, InstRef::invalid(), Type::Invalid);
            }
        };
        match var.ty.clone() {
            ty @ (Type::Primitive(_) | Type::Array { .. }) => {
                let load_inst = self.method.next_inst(cur_block, Inst::Load(addr));
                (cur_block, load_inst, ty)
            }
            Type::Invalid => (cur_block, InstRef::invalid(), Type::Invalid),
            Type::Void => unreachable!(),
        }
    }

    fn build_load_array(
        &mut self,
        ident: &Ident,
        index_expr: &Spanned<Expr>,
        cur_block: BlockRef,
    ) -> (BlockRef, InstRef, Type) {
        let (var, addr) = match self.lookup(&ident.inner) {
            Some(pair) => pair,
            None => {
                self.emit_error(SemanticError::UnknownVar(ident.clone()));
                return (cur_block, InstRef::invalid(), Type::Invalid);
            }
        };
        match var.ty.clone() {
            ty @ Type::Primitive(_) => {
                let ident = ident.clone();
                self.emit_error(SemanticError::IndexingScalar { ident, ty });
                (cur_block, InstRef::invalid(), Type::Invalid)
            }
            Type::Invalid => (cur_block, InstRef::invalid(), Type::Invalid),
            Type::Array { base, .. } => {
                let (next_block, index, index_ty) = self.build_expr(index_expr, cur_block);
                match index_ty {
                    Type::Primitive(PrimitiveType::Int) | Type::Invalid => {}
                    _ => {
                        self.emit_error(SemanticError::InvalidArrayIndex(Spanned {
                            inner: index_ty,
                            span: index_expr.span.clone(),
                        }));
                        return (cur_block, InstRef::invalid(), Type::Invalid);
                    }
                }
                let load_inst = self
                    .method
                    .next_inst(next_block, Inst::LoadArray { addr, index });
                (next_block, load_inst, *base.clone())
            }
            Type::Void => unreachable!(),
        }
    }

    fn build_store(
        &mut self,
        location: &Location,
        value_expr: &Spanned<Expr>,
        cur_block: BlockRef,
    ) -> BlockRef {
        match location {
            Location::Ident(ident) => self.build_store_ident(ident, value_expr, cur_block),
            Location::ArrayAccess {
                ident,
                index: index_expr,
            } => {
                let ident = match &**ident {
                    Location::Ident(ident) => ident,
                    _ => unreachable!("multi-dim array loading unsupported yet"),
                };
                self.build_store_array(ident, index_expr, value_expr, cur_block)
            }
        }
    }

    fn build_store_ident(
        &mut self,
        ident: &Ident,
        value_expr: &Spanned<Expr>,
        cur_block: BlockRef,
    ) -> BlockRef {
        let (var, addr) = match self.lookup(&ident.inner) {
            Some(pair) => pair,
            None => {
                self.emit_error(SemanticError::UnknownVar(ident.clone()));
                return cur_block;
            }
        };
        if var.is_const {
            self.emit_error(SemanticError::ReassigningConst {
                decl_site: var.name.clone(),
                assign_site: ident.clone(),
            });
            return cur_block;
        }
        match &var.ty {
            Type::Primitive(_) => {
                let var_ty = var.ty.clone(); // To make borrow checker happy
                let var_name = var.name.clone();
                let (next_block, value, value_ty) = self.build_expr(value_expr, cur_block);
                if value_ty != Type::Invalid && value_ty != var_ty {
                    self.emit_error(SemanticError::MismatchedAssignmentTypes {
                        rhs_ty: Spanned {
                            inner: value_ty,
                            span: value_expr.span.clone(),
                        },
                        lhs_ty: var_ty,
                        decl_site: var_name,
                    });
                }
                self.method
                    .next_inst(next_block, Inst::Store { addr, value });
                next_block
            }
            Type::Array { .. } => {
                self.emit_error(SemanticError::NonScalarAssignment {
                    decl_site: var.name.clone(),
                    update_site: ident.clone(),
                });
                cur_block
            }
            Type::Invalid => cur_block,
            Type::Void => unreachable!(),
        }
    }

    fn build_store_array(
        &mut self,
        ident: &Ident,
        index_expr: &Spanned<Expr>,
        value_expr: &Spanned<Expr>,
        cur_block: BlockRef,
    ) -> BlockRef {
        let (var, addr) = match self.lookup(&ident.inner) {
            Some(pair) => pair,
            None => {
                self.emit_error(SemanticError::UnknownVar(ident.clone()));
                return cur_block;
            }
        };
        if var.is_const {
            self.emit_error(SemanticError::ReassigningConst {
                decl_site: var.name.clone(),
                assign_site: ident.clone(),
            });
            return cur_block;
        }
        match &var.ty {
            Type::Primitive(_) => {
                let ident = ident.clone();
                self.emit_error(SemanticError::IndexingScalar {
                    ident,
                    ty: var.ty.clone(),
                });
                cur_block
            }
            Type::Array { base, .. } => {
                let base_ty = (**base).clone();
                let (next_block, index, index_ty) = self.build_expr(index_expr, cur_block);
                match index_ty {
                    Type::Primitive(PrimitiveType::Int) | Type::Invalid => {}
                    _ => {
                        self.emit_error(SemanticError::InvalidArrayIndex(Spanned {
                            inner: index_ty,
                            span: index_expr.span.clone(),
                        }));
                        return cur_block;
                    }
                }
                let (next_block, value, value_ty) = self.build_expr(value_expr, next_block);
                if value_ty != Type::Invalid && value_ty != base_ty {
                    self.emit_error(SemanticError::MismatchedAssignmentTypes {
                        rhs_ty: Spanned {
                            inner: value_ty,
                            span: value_expr.span.clone(),
                        },
                        lhs_ty: base_ty,
                        decl_site: ident.clone(),
                    });
                }
                self.method
                    .next_inst(next_block, Inst::StoreArray { addr, index, value });
                next_block
            }
            Type::Invalid => cur_block,
            Type::Void => unreachable!(),
        }
    }

    fn build_literal(
        &mut self,
        lit: &RuntimeLiteral,
        cur_block: BlockRef,
    ) -> (BlockRef, InstRef, Type) {
        let ty = Type::from_ast_literal(lit);
        let value = Const::from_ast_literal(lit).unwrap_or_else(|err| {
            self.emit_error(err);
            Const::default_for(&ty)
        });
        let load_inst = self.method.next_inst(cur_block, Inst::LoadConst(value));
        (cur_block, load_inst, ty)
    }

    fn build_call(
        &mut self,
        call: &MethodCall,
        mut cur_block: BlockRef,
    ) -> (BlockRef, InstRef, Type) {
        if let Some((var, _)) = self.lookup(&call.name.inner) {
            self.emit_error(SemanticError::InvalidCall {
                decl_site: var.name.clone(),
                use_site: call.name.clone(),
            });
            return (cur_block, InstRef::invalid(), Type::Invalid);
        }
        let method = match self.builder.methods.get(&*call.name.inner) {
            Some(method) => Some(method),
            None if call.name.inner == self.method.name.inner => Some(&self.method),
            None => None,
        };
        if let Some(method) = method {
            // Non-external method call
            let ty = method.return_ty.clone();
            if call.args.len() != method.params.len() {
                self.emit_error(SemanticError::MismatchedArgCount {
                    decl_site: method.name.clone(),
                    call_site: call.name.clone(),
                    expected: method.params.len(),
                    found: call.args.len(),
                });
                return (cur_block, InstRef::invalid(), ty);
            }
            for arg in &call.args {
                if let MethodCallArg::StringLiteral(lit) = arg {
                    self.emit_error(SemanticError::InvalidArgForNonImport {
                        decl_site: method.name.clone(),
                        call_site: call.name.clone(),
                        offending_arg: lit.span.clone(),
                    });
                    return (cur_block, InstRef::invalid(), ty);
                }
            }
            let mut arg_insts = Vec::with_capacity(call.args.len());
            let params = method.params.clone(); // To avoid borrow checker issue
            for (arg, (param, param_ty)) in call.args.iter().zip(params) {
                let arg = match arg {
                    MethodCallArg::Expr(arg) => arg,
                    MethodCallArg::StringLiteral(_) => unreachable!(),
                };
                let (next_block, arg_inst, arg_ty) = self.build_expr(arg, cur_block);
                if arg_ty != Type::Invalid && arg_ty != param_ty {
                    self.emit_error(SemanticError::MismatchedArgType {
                        param,
                        arg: arg.span.clone(),
                        param_ty,
                        arg_ty,
                    });
                }
                arg_insts.push(arg_inst);
                cur_block = next_block;
            }
            let call_inst = self.method.next_inst(
                cur_block,
                Inst::Call {
                    method: call.name.inner.clone(),
                    args: arg_insts,
                },
            );
            self.method.annotate_inst_mut(call_inst).str = Some(String::from("call"));
            self.method.annotate_inst_mut(call_inst).span = Some(call.name.span.clone());
            (cur_block, call_inst, ty)
        } else if self
            .builder
            .imported_methods
            .contains_key(&*call.name.inner)
        {
            let mut arg_insts = Vec::with_capacity(call.args.len());
            for arg in call.args.iter() {
                match arg {
                    MethodCallArg::Expr(arg) => {
                        let (next_block, arg_inst, _) = self.build_expr(arg, cur_block);
                        arg_insts.push(arg_inst);
                        cur_block = next_block;
                    }
                    MethodCallArg::StringLiteral(lit) => {
                        let load_inst = self
                            .method
                            .next_inst(cur_block, Inst::LoadStringLiteral(lit.inner.clone()));
                        arg_insts.push(load_inst);
                    }
                }
            }
            let call_inst = self.method.next_inst(
                cur_block,
                Inst::Call {
                    method: call.name.inner.clone(),
                    args: arg_insts,
                },
            );
            self.method.annotate_inst_mut(call_inst).str = Some(String::from("call"));
            self.method.annotate_inst_mut(call_inst).span = Some(call.name.span.clone());
            (cur_block, call_inst, Type::int())
        } else {
            self.emit_error(SemanticError::UnknownMethod(call.name.clone()));
            (cur_block, InstRef::invalid(), Type::Invalid)
        }
    }

    fn build_len(&mut self, ident: &Ident, cur_block: BlockRef) -> (BlockRef, InstRef, Type) {
        let var = match self.lookup(&ident.inner) {
            Some((var, _)) => var,
            None => {
                self.emit_error(SemanticError::UnknownVar(ident.clone()));
                return (cur_block, InstRef::invalid(), Type::Invalid);
            }
        };
        match var.ty.clone() {
            Type::Array { length, .. } => {
                let value = Const::Int(length as i64);
                let load_inst = self.method.next_inst(cur_block, Inst::LoadConst(value));
                (cur_block, load_inst, Type::int())
            }
            Type::Invalid => (cur_block, InstRef::invalid(), Type::Invalid),
            ty => {
                let ident = ident.clone();
                self.emit_error(SemanticError::InvalidLen { ident, ty });
                (cur_block, InstRef::invalid(), Type::Invalid)
            }
        }
    }

    pub fn build(mut self) -> Method {
        self.method.annotate_block_mut(self.method.entry).str = Some("entry".to_string());
        // Don't introduce a new scope for the method body, will just use the parameter scope.
        self.build_block_no_new_scope(&self.method_decl.body.inner, self.method.entry);
        self.method.remove_unreachable();
        self.method.merge_blocks();
        self.method
    }
}

enum FieldDeclContext<'a, 'b>
where
    'b: 'a,
{
    Global(&'a mut IrBuilder),
    Local(&'a mut MethodBuilder<'b>, BlockRef),
}

impl FieldDeclContext<'_, '_> {
    fn emit_error(&mut self, error: SemanticError) {
        match self {
            Self::Global(builder) => builder.emit_error(error),
            Self::Local(builder, _) => builder.emit_error(error),
        }
    }

    /// Look up an identifier in the current scope.
    fn lookup_local(&self, name: &str) -> Option<&Ident> {
        match self {
            Self::Global(builder) => builder
                .lookup(name)
                .map(|pair| &pair.name)
                .or_else(|| builder.imported_methods.get(name))
                .or_else(|| builder.methods.get(name).map(|m| &m.name)),
            Self::Local(builder, _) => builder.lookup_local(name).map(|ident| &ident.name),
        }
    }

    fn unwrap_type_and_emit_error(&mut self, ty: Result<Type, SemanticError>) -> Type {
        match ty {
            Ok(ty) => ty,
            Err(err) => {
                self.emit_error(err);
                Type::Invalid
            }
        }
    }

    fn add_var(&mut self, var: Var, init_value: Const) {
        match self {
            Self::Global(builder) => builder.add_global(var, init_value),
            Self::Local(builder, block) => builder.add_local(var, init_value, *block),
        }
    }

    fn check_field_decl(&mut self, field_decl: &FieldDecl) {
        let base_ty = PrimitiveType::from(&field_decl.ty);

        for decl in &field_decl.decls {
            let name = decl.declarator.ident();
            // Decaf forbids redeclaration of variables in the same scope.
            if let Some(prev_decl) = self.lookup_local(&name.inner) {
                self.emit_error(SemanticError::DuplicateDecls {
                    first: prev_decl.clone(),
                    second: name.clone(),
                });
                continue;
            }
            // Decaf forbids declaring a const variable without an initializer.
            if decl.initializer.is_none() && field_decl.is_const {
                self.emit_error(SemanticError::MissingConstInitializer(name.clone()));
                // Emit the error, but still insert the variable to suppress
                // further errors
            }
            // Infer initializer type if it exists
            let init_ty = decl
                .initializer
                .as_ref()
                .map(|init| self.unwrap_type_and_emit_error(Type::from_ast_initializer(init)));
            let var_ty = self.unwrap_type_and_emit_error(build_and_check_type(
                &base_ty,
                &decl.declarator,
                init_ty.as_ref(),
            ));
            let init_value = match &decl.initializer {
                Some(init) => match Const::from_ast_initializer(init) {
                    Ok(c) => c,
                    Err(e) => {
                        self.emit_error(e);
                        Const::default_for(&var_ty)
                    }
                },
                None => Const::default_for(&var_ty),
            };
            let var = Var {
                name: name.clone(),
                ty: var_ty,
                is_const: field_decl.is_const,
            };
            self.add_var(var, init_value);
        }

        // C-style languages are weird. Variables are declared by having a
        // primitive base type at the very front and a bunch of declarators
        // after it. Declarators are array (or pointer) notations that surround
        // **identifiers**. But arrays should really be a property of the type,
        // rather than the identifier, so we have a structural mismatch here.
        // Worse, the size in array declarators can be omitted, and
        // have to be inferred from the initializer.
        // This recursive function does the job of converting
        //   base type + array notation around identifier (as in the parse tree)
        // into
        //   identifier + array notation around base type (as in the type system).
        // and inferring the size of arrays from the initializer (if exists).
        fn build_and_check_type(
            base_ty: &PrimitiveType,
            declarator: &FieldDeclarator,
            init_ty: Option<&Type>,
        ) -> Result<Type, SemanticError> {
            match declarator {
                FieldDeclarator::Ident(_) => match init_ty {
                    // No initializer, just use the base type
                    None => Ok(Type::Primitive(*base_ty)),
                    // Initializer exists, check if it matches the base type
                    Some(Type::Primitive(init_base)) if base_ty == init_base => {
                        Ok(Type::Primitive(*base_ty))
                    }
                    // Otherwise, emit an error of mismatched types
                    Some(init_ty) => Err(SemanticError::MismatchedInitializerType {
                        ident: declarator.ident().clone(),
                        init_ty: init_ty.clone(),
                    }),
                },
                FieldDeclarator::Array { base, size } => match init_ty {
                    // No initializer, check if the size is specified
                    None => match size {
                        None => Err(SemanticError::MissingArrayLength(base.ident().clone())),
                        // Size is specified, check if it's valid
                        // Decaf spec requires positive integer size less than 2^63.
                        Some(size) if *INT_0 < size.inner && size.inner <= *INT_MAX => {
                            Ok(Type::Array {
                                base: Box::new(build_and_check_type(base_ty, base, None)?),
                                length: size.inner.to_usize().unwrap(),
                            })
                        }
                        // Size is specified, but it's invalid. Emit an error.
                        Some(size) => Err(SemanticError::InvalidArrayLength {
                            ident: base.ident().clone(),
                            length: size.clone(),
                        }),
                    },
                    // Initializer is also an array. Good!
                    // E.g. int a[] = {1, 2, 3};
                    Some(Type::Array {
                        base: init_base,
                        length,
                    }) => match size {
                        // ... and the array declarator is missing the size. Infer it from the initializer.
                        None => Ok(Type::Array {
                            base: Box::new(build_and_check_type(base_ty, base, Some(init_base))?),
                            length: *length,
                        }),
                        // ... and the array declarator has a size. Emit an error by Decaf spec.
                        Some(_) => Err(SemanticError::CoexistingArrayLengthAndInitializer(
                            base.ident().clone(),
                        )),
                    },
                    // Something wrong with initializer type checking. Emit an error.
                    Some(Type::Invalid) => Ok(Type::Invalid), // Suppress further errors
                    // Declared an array but given a non-array initializer. Emit an error.
                    // E.g. int a[] = 1;
                    Some(init_ty @ Type::Primitive(_)) => {
                        Err(SemanticError::MismatchedInitializerType {
                            ident: base.ident().clone(),
                            init_ty: init_ty.clone(),
                        })
                    }
                    _ => unreachable!(),
                },
            }
        }
    }
}
