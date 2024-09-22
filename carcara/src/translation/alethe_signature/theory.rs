/// Definition of Alethe in Eunoia, following https://github.com/cvc5/aletheinalf/.
use std::string::String;

// TODO: import everything once
use crate::translation::eunoia_ast::*;
use crate::translation::eunoia_ast::EunoiaType::*;
use crate::translation::eunoia_ast::EunoiaTerm::*;
use crate::translation::eunoia_ast::EunoiaConsAttr::*;
use crate::translation::eunoia_ast::EunoiaKindParam::*;
use crate::translation::eunoia_ast::EunoiaTypeAttr::*;

// TODO: THIS IS ONLY DONE TO AVOID THE COMPLEXITIES OF DECLARING
// AND DEALING WITH GLOBALS IN RUST.
pub struct AletheTheory {
    // Built-in operators
    pub cl : EunoiaCommand,
    pub ite : EunoiaCommand, 
}

impl AletheTheory{
    pub fn new() -> Self {
        return AletheTheory{
            cl : EunoiaCommand::DeclareConst {
                name        : String::from("@cl"),
                eunoia_type : EunoiaTerm::Type(
                    Fun(Vec::new(), vec![Bool, Bool], Box::new(Bool))),
                attrs       : vec![RightAssocNil(False)]
            },

            ite : EunoiaCommand::DeclareConst {
                name        : String::from("ite"), 
                eunoia_type : EunoiaTerm::Type(
                    Fun(vec![KindParam(EunoiaType::Type, 
                                       vec![EunoiaTypeAttr::Var(String::from("A")),
                                            Implicit])],
                        vec![Bool, 
                             Name(String::from("A")), 
                             Name(String::from("A"))],
                        Box::new(Name(String::from("A"))))),
                attrs       : Vec::new(),
            },
        }
    }

    /// Accessors: simple API to query "Alethe in Eunoia"'s signature.
    pub fn get_cl_symbol(&self) -> Symbol {
        // TODO: some better type-error free way of accessing cl.name?
        match &self.cl {
            EunoiaCommand::DeclareConst {name, ..} => {
                name.clone()
            },
            
            _ => {
                // NOTE: it shouldn't be defined as something else...
                panic!()
            }
        }
    }
    
    
    
}