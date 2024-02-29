#![allow(dead_code)]
//! IR

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use lazy_static::lazy_static;
use num_bigint::BigInt;

use crate::{
    inter::types::PrimitiveType,
    parse::ast::{Block, FieldDecl, FieldDeclarator, Ident, MethodDecl, Program},
};

use self::{error::SemanticError, types::Type};

mod error;
mod types;

struct VarDescriptor {
    name: Ident,
    ty: Type,
    is_const: bool,
}

struct MethodDescriptor {
    name: Ident,
    return_ty: Type,
    params: Vec<Rc<VarDescriptor>>,
}

struct ImportedMethodDescriptor(Ident);

struct SymbolTable {
    // Symbol table is mostly an immutable structure, so we use Rc to share it.
    // But do not use Rc<RefCell<...>> directly, as it makes everything too
    // cumbersome. The parent pointer of a symbol table is determined by the AST
    // structure and should never change once created, so make it immutable.
    /// The parent symbol table.
    parent: Option<Rc<SymbolTable>>,
    // The map mapping variable names to their descriptors, on the other hand,
    // can be updated by inserting new entries. So make it interior-mutable with
    // RefCell.
    // Need Rc to wrap VarDescriptor because otherwise a reference to the
    // VarDescriptor returned by a lookup will be invalidated when the RefCell
    // borrow of the map ends (and the end of the lookup), making the returned
    // reference unusable.
    // We could use Rc<RefCell<...>> here, but it's not necessary because
    // VarDescriptor need not be mutable -- at least for now.
    /// The map mapping variable names to their descriptors.
    vars: RefCell<HashMap<String, Rc<VarDescriptor>>>,
}

impl SymbolTable {
    fn add(&self, desc: Rc<VarDescriptor>) {
        self.vars.borrow_mut().insert(desc.name.inner.clone(), desc);
    }

    fn lookup_local(&self, name: &str) -> Option<Rc<VarDescriptor>> {
        self.vars.borrow().get(name).cloned()
    }

    fn lookup(&self, name: &str) -> Option<Rc<VarDescriptor>> {
        self.vars.borrow().get(name).cloned().or_else(|| {
            self.parent
                .as_ref()
                .and_then(|parent| parent.lookup(name).clone())
        })
    }
}

lazy_static! {
    static ref INT_0: BigInt = BigInt::from(0);
    static ref INT_MAX: BigInt = BigInt::from(i64::MAX);
}

pub struct SemanticChecker {
    errors: Vec<SemanticError>,

    methods: HashMap<String, MethodDescriptor>,
    imported_methods: HashMap<String, ImportedMethodDescriptor>,

    current_scope: Rc<SymbolTable>,
}

impl SemanticChecker {
    pub fn new() -> Self {
        Self {
            errors: Vec::new(),
            methods: HashMap::new(),
            imported_methods: HashMap::new(),
            current_scope: Rc::new(SymbolTable {
                parent: None,
                vars: Default::default(),
            }),
        }
    }

    fn emit_error(&mut self, error: SemanticError) {
        self.errors.push(error);
    }

    pub fn check_program(&mut self, program: &Program) -> Vec<SemanticError> {
        // Add imported methods to the symbol table
        for import_decl in &program.import_decls {
            self.imported_methods.insert(
                import_decl.0.inner.clone(),
                ImportedMethodDescriptor(import_decl.0.clone()),
            );
        }
        for field_decl in &program.field_decls {
            self.check_field_decl(field_decl);
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
        std::mem::take(&mut self.errors)
    }

    fn emit_and_invalid_type(&mut self) -> impl FnOnce(SemanticError) -> Type + '_ {
        |err| {
            self.emit_error(err);
            Type::Invalid
        }
    }

    fn check_field_decl(&mut self, field_decl: &FieldDecl) {
        let base_type = PrimitiveType::from(&field_decl.ty);

        for decl in &field_decl.decls {
            let name = decl.declarator.ident();
            // Decaf forbids redeclaration of variables in the same scope.
            if let Some(prev_decl) = self.current_scope.lookup_local(&name.inner) {
                self.emit_error(SemanticError::DuplicateDecls {
                    first: prev_decl.name.clone(),
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
            let init_type = decl.initializer.as_ref().map(|init| {
                Type::from_ast_initializer(init).unwrap_or_else(self.emit_and_invalid_type())
            });
            let var_type = build_and_check_type(&base_type, &decl.declarator, init_type.as_ref())
                .unwrap_or_else(self.emit_and_invalid_type());
            self.current_scope.add(Rc::new(VarDescriptor {
                name: name.clone(),
                ty: var_type,
                is_const: field_decl.is_const,
            }));
        }

        // C-style languages are weird. Variables are declared by having a
        // primitive base type at the very front and a bunch of declarators
        // after it. Declarators are array (or pointer) notations that surround
        // **identifiers**. But arrays should really be a property of the type,
        // rather than the identifier, so we have a structural mismatch here.
        // Worse, the size in array declarators can be omitted, and
        // have to be inferred from the initializer.
        // This recursive function does the job of converting
        //   base_type + array notation around identifier (as in the parse tree)
        // into
        //   identifier + array notation around base_type (as in the type system).
        // and inferring the size of arrays from the initializer (if exists).
        fn build_and_check_type(
            base_type: &PrimitiveType,
            declarator: &FieldDeclarator,
            init_type: Option<&Type>,
        ) -> Result<Type, SemanticError> {
            match declarator {
                FieldDeclarator::Ident(_) => match init_type {
                    // No initializer, just use the base type
                    None => Ok(Type::Primitive(*base_type)),
                    // Initializer exists, check if it matches the base type
                    Some(Type::Primitive(init_base)) if base_type == init_base => {
                        Ok(Type::Primitive(*base_type))
                    }
                    // Otherwise, emit an error of mismatched types
                    Some(init_type) => Err(SemanticError::MismatchedInitializerType {
                        ident: declarator.ident().clone(),
                        init_type: init_type.clone(),
                    }),
                },
                FieldDeclarator::Array { base, size } => match init_type {
                    // No initializer, check if the size is specified
                    None => match size {
                        None => Err(SemanticError::MissingArrayLength(base.ident().clone())),
                        // Size is specified, check if it's valid
                        // Decaf spec requires positive integer size less than 2^63.
                        Some(size) if *INT_0 < size.inner && size.inner <= *INT_MAX => {
                            Ok(Type::Array {
                                base: Box::new(build_and_check_type(base_type, base, None)?),
                                // to_u32_digits().1[0] is rather ugly. TODO: make it nicer?
                                length: size.inner.to_u64_digits().1[0] as usize,
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
                            base: Box::new(build_and_check_type(base_type, base, Some(init_base))?),
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
                    Some(init_type @ Type::Primitive(_)) => {
                        Err(SemanticError::MismatchedInitializerType {
                            ident: base.ident().clone(),
                            init_type: init_type.clone(),
                        })
                    }
                    _ => unreachable!(),
                },
            }
        }
    }

    fn push_scope(&mut self) {
        self.current_scope = Rc::new(SymbolTable {
            parent: Some(Rc::clone(&self.current_scope)),
            vars: Default::default(),
        });
    }

    fn pop_scope(&mut self) {
        self.current_scope = self
            .current_scope
            .parent
            .as_ref()
            .expect("popped the root scope")
            .clone();
    }

    fn check_method_decl(&mut self, method_decl: &MethodDecl) {
        let name = &method_decl.name;

        // Can't declare a method with the same name as an imported method
        if let Some(prev_decl) = self.imported_methods.get(&name.inner) {
            self.emit_error(SemanticError::DuplicateDecls {
                first: prev_decl.0.clone(),
                second: name.clone(),
            });
            return;
        }
        if let Some(prev_decl) = self.methods.get(&name.inner) {
            self.emit_error(SemanticError::DuplicateDecls {
                first: prev_decl.name.clone(),
                second: name.clone(),
            });
            return;
        }

        let return_type = match &method_decl.return_type {
            Some(ty) => Type::Primitive(PrimitiveType::from(ty)),
            None => Type::Void,
        };
        self.push_scope(); // For parameters
        let mut params = vec![];
        for param in &method_decl.params {
            let ty = Type::Primitive(PrimitiveType::from(&param.ty));
            let name = &param.name;
            let desc = Rc::new(VarDescriptor {
                name: name.clone(),
                ty,
                // TODO: Double check if Decaf allows mutable parameters
                is_const: false,
            });
            params.push(Rc::clone(&desc));
            self.current_scope.add(desc);
        }
        self.methods.insert(
            name.inner.clone(),
            MethodDescriptor {
                name: name.clone(),
                return_ty: return_type,
                params,
            },
        );

        self.pop_scope();
    }

    fn check_block(&mut self, block: &Block) {
        self.push_scope();
        self.check_block_(block);
        self.pop_scope();
    }

    fn check_block_(&mut self, block: &Block) {
        for field_decl in &block.field_decls {
            self.check_field_decl(field_decl);
        }
    }
}
