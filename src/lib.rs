pub mod ivl;
mod ivl_ext;
use itertools::fold;
use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, Quantifier, Type, Var};
use slang::Span;
use slang_ui::prelude::*;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::thread;
use crate::slang::ast::Type;

pub struct App;

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &mut slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // Get reference to Z3 solver
        let mut solver = cx.solver()?;

        // Iterate methods
        for m in file.methods() {
            // Get method's preconditions;
            let pres = m.requires();
            // Merge them into a single condition
            let pre = pres
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
            // Convert the expression into an SMT expression
            let spre = pre.smt()?;
            // Assert precondition
            solver.assert(spre.as_bool()?)?;

            // Get method's body
            let cmd = &m.body.clone().unwrap().cmd;
            // Encode it in IVL
            let ivl = cmd_to_ivlcmd(cmd)?;
            // Convert IVL to DSA
            let dsa = ivl_to_dsa(&ivl, &mut init_map())?;

            print!("dsa: ");
            print!("{}", dsa.to_string());
            // Calculate obligation and error message (if obligation is not
            // verified)
            let (oblig, msg) = wp(&dsa, &Expr::bool(true))?;
            // Convert obligation to SMT expression
            let soblig = oblig.smt()?;

            // Run the following solver-related statements in a closed scope.
            // That is, after exiting the scope, all assertions are forgotten
            // from subsequent executions of the solver
            solver.scope(|solver| {
                // Check validity of obligation
                solver.assert(!soblig.as_bool()?)?;
                // Run SMT solver on all current assertions
                match solver.check_sat()? {
                    // If the obligations result not valid, report the error (on
                    // the span in which the error happens)
                    smtlib::SatResult::Sat => {
                        cx.error(oblig.span, format!("{msg}"));
                    }
                    smtlib::SatResult::Unknown => {
                        cx.warning(oblig.span, "{msg}: unknown sat result");
                    }
                    smtlib::SatResult::Unsat => (),
                }
                Ok(())
            })?;
        }

        Ok(())
    }
}

// Encoding of (assert-only) statements into IVL (for programs comprised of only
// a single assertion)
fn cmd_to_ivlcmd(cmd: &Cmd) -> Result<IVLCmd> {
    match &cmd.kind {
        CmdKind::Assert { condition, .. } => Ok(IVLCmd::assert(condition, "Assert might fail!")),
        // Assume has not been documented in the report yet
        // Assume just takes the High level command Assume and passes the condition onto the assume IVL command
        // For the statement "assume true" the condition is "true" | for the statement "assume x == 2" the condition is "x == 2"
        CmdKind::Assume { condition, .. } => Ok(IVLCmd::assume(condition)),
        // Seq has not been documented in the report yet
        // Seq takes 2 commands in the higher level language (CmdKind) and passes them unto the IVLCmd seq
        // Note: the commands have to be processed as well, so that the IVL command seq does not pass on higer level commands
        CmdKind::Seq(command1, command2) => Ok(IVLCmd::seq(
            &cmd_to_ivlcmd(command1)?,
            &cmd_to_ivlcmd(command2)?,
        )),
        CmdKind::Assignment { name, expr } => Ok(IVLCmd::assign(name, expr)),

        CmdKind::VarDefinition { name, ty: (_span, ty), expr }=>{ 
            Ok(
                match expr {
                    Some(expr_value) => {
                        // ask the ta
                        //not sure if we should do the havoc before assign or assign is enough 
                        //if we should perform the havoc before then IVLCmd::seq(&hav, &cmdd) should be called
                        //but then the wp of assign is implemented twice so we should fix the implementation
                        //the logic is true implementation is false

                        // let hav=IVLCmd::havoc(name, ty);                             
                        let cmdd = IVLCmd::assign(name, expr_value);
                        cmdd 
                        // IVLCmd::seq(&hav, &cmdd)  
                    },
                    None => {
                        IVLCmd::havoc(name, ty)
                    }
                }
            )
    },

        _ => todo!("Not supported (yet)."),
    }
}

// Code to substitute variables in an expressions, to make the IVL commands into DSA
// fn sub_new_var(expr:Expr) -> Result<Expr>{
//     match &expr {
//         Expr::ExprKind::Infix::add{e1,e2} => Ok(Expr::error()),
//         _ => todo!("Not supported (yet)."),
//     }
// }

// Initializing an empty hashmap
fn init_map() -> HashMap<Ident, i32> {
    HashMap::new()
}



fn synchronize_cmd(com1:IVLCmd,map1:HashMap<Ident, i32>, map2: HashMap<Ident, i32> ) -> IVLCmd {
    for (key,value1) in map1 {
        if let Some(&value2) = map2.get(&key) {
            if value2 > value1 {
                let new_ident = Ident(format!("{}{}", key, value2));
                let old_ident = Ident(format!("{}{}", key, value1));
                let assign = IVLCmd::assign(&Name::ident(new_ident), &Expr::ident(&old_ident, &Type::Unknown { name: Name::ident(old_ident.clone()) }));
                IVLCmd::seq(&com1, &assign);
            }
        }
    }
    com1
}


// Maybe not sure
fn update_variable_map(variable_map: &mut HashMap<Ident, i32>, map1: &HashMap<Ident, i32>, map2: &HashMap<Ident, i32>) {
    // Iterate over map1 and update variable_map
    for (key, &value1) in map1.iter() {
        let entry = variable_map.entry(key.clone()).or_insert(value1);
        if value1 > *entry {
            *entry = value1;
        }
    }

    // Iterate over map2 and update variable_map
    for (key, &value2) in map2.iter() {
        let entry = variable_map.entry(key.clone()).or_insert(value2);
        if value2 > *entry {
            *entry = value2;
        }
    }
}


// Updates a variable to the newest version according to the map
fn update_variable_name(variable: &Ident, map: &mut HashMap<Ident, i32>) -> Ident {
    // Check if the variable exists in the map
    let counter = map.entry(variable.clone()).or_insert(0);
    // If it does increase its value by 1, otherwise add it to the map.
    *counter += 1;

    // Return the new variable name with the counter
    let new_variable_name = format!("{}{}", variable, counter);

    // Create an Ident instance
    Ident(new_variable_name)
}


// Code to make IVL commands to DSA form (Dynamic Single Assignment)
// This code works by creating a map variable_map, which keeps track of all the variables and maps them to the number of times they occur in the program.
// Using the variable_map, we can change the name of each of the variables, to the variablename concatenated with the number.
fn ivl_to_dsa(ivl: &IVLCmd, variable_map: &mut HashMap<Ident, i32>) -> Result<IVLCmd> {
    match &ivl.kind {
        // For each of the variables in the variable_map we check whether the variable occurs in the expression (rhs of the assignment)
        // If the variable occur, we change it with the value found in the map (ie. "x" becomes "x5" etc.) and we look for the next variable in the variable_map.
        // Then we look for the variable which gets assigned (the lhs of the assignment) and updates it in the variable_map (see definition of update_variable_name)
        // NB. We use fold, because we want to use the output of the substitution to be the input of the next call of the fold function
        IVLCmdKind::Assignment { name, expr } => {
            let expr = (variable_map.iter().fold(expr.clone(), |acc, (var, &val)| {
                let new_ident = Ident(format!("{}{}", var, val));
                let new_expr = Expr::ident(&new_ident, &acc.ty);
                acc.subst_ident(var, &new_expr)
            }));
            Ok(IVLCmd::assign(
                &Name::ident(update_variable_name(&name.ident, variable_map)),
                &expr,
            ))
        },
        // For the sequence we simply run the ivl_to_dsa for each of the commands
        // We assume that the rust program runs in sequential order, such that the variable_map gets updated by the first block before being used for the second one.
        IVLCmdKind::Seq(command1, command2) => Ok(IVLCmd::seq(
            &(ivl_to_dsa(command1, variable_map)?),
            &(ivl_to_dsa(command2, variable_map)?),
        )),
        // For assert we do the same as for assign except we only have an expression, not a new variable.
        // Iterate through the variable_map
        // For each variable look for and change the variable for the appropriate value
        // Continue with the rest of the map
        // NB. We use fold, because we want to use the output of the substitution to be the input of the next call of the fold function
        IVLCmdKind::Assert { condition, message } => Ok(IVLCmd::assert(&(variable_map
            .iter()
            .fold(condition.clone(), |acc, (var, &val)| {
                let new_ident = Ident(format!("{}{}", var, val));
                let new_expr = Expr::ident(&new_ident, &acc.ty);
                acc.subst_ident(var, &new_expr)
            })), &message.clone())
            
        ),
        // For assume we do the same as for assign except we only have an expression, not a new variable.
        // Iterate through the variable_map
        // For each variable look for and change the variable for the appropriate value
        // Continue with the rest of the map
        // NB. We use fold, because we want to use the output of the substitution to be the input of the next call of the fold function
        IVLCmdKind::Assume { condition } => Ok(IVLCmd::assume(&(variable_map
            .iter()
            .fold(condition.clone(), |acc, (var, &val)| {
                let new_ident = Ident(format!("{}{}", var, val));
                let new_expr = Expr::ident(&new_ident, &acc.ty);
                acc.subst_ident(var, &new_expr)
            })))),
        // For nondeterministic blocks we want to first compute the DSA of each individual command block
        // Then have a way of combining the resultant variable_maps, to make sure that we take the highest value for each variable
        // Finally we want to add assignments in the end of the blocks, to synchronize the variables.
        IVLCmdKind::NonDet(command1, command2) => {
            let map1 = &mut variable_map.clone();
            let map2 = &mut variable_map.clone();
            let com1 = ivl_to_dsa(command1,  map1)?;
            let com2 = ivl_to_dsa(command2,  map2)?;
            let done_com1 = synchronize_cmd(com1, map1.clone(), map2.clone());
            let done_com2 = synchronize_cmd(com2, map2.clone(), map1.clone());
            update_variable_map(variable_map, map1,  map2);
            Ok(IVLCmd::nondet(
                &(done_com1),
                &(done_com2),
            ))
        },
        
        _ => todo!("Not supported (yet)."),
    }
}



// Weakest precondition of (assert-only) IVL programs comprised of a single assertion
fn wp(ivl: &IVLCmd, postcon: &Expr) -> Result<(Expr, String)> {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => Ok((condition.clone().and(postcon), message.clone())),
        // Assume has not been documented in the report yet
        // Here the wp of assume with the condition, C, takes the postcondition, G, and returns the weakest precondition:
        // I.e. : wp[assume C](G) = C -> G
        IVLCmdKind::Assume { condition } => {
            Ok((condition.clone().imp(postcon), "HERE".to_string()))
        }
        // Seq has not been documented in the report yet
        // Here the wp of assume with the commands: command1 and command2 and the postcondition G returns the weakest precondition:
        // I.e. : wp[command1;command2](G) = wp[command1]( wp[command2](G) )
        IVLCmdKind::Seq(command1, command2) => {
            Ok((wp(command1, &wp(command2, postcon)?.0)?.0, "SEQ".to_string()))
        },
        //After the code is transformed to dsa
        //we compute wp by assuming the assigment, for example if we have x:=3 we assume x==3
        // (name==expr) ==> postcond
        IVLCmdKind::Assignment { name, expr } =>  {
        Ok(((Expr::ident(&name.ident, &expr.ty).op(slang::ast::Op::Eq, expr)).imp(postcon), "Assignment".to_string()))
        },
        //wp of havoc
        //the logic is true but we should make sure that span.Default() is true
        IVLCmdKind::Havoc { name, ty }=>{
            Ok((
                Expr::quantifier(
                    Quantifier::Forall, 
                    &[Var {
                        span: Span::default(),       
                        name: name.clone(),     
                        ty: (Span::default(), ty.clone()), 
                    }],
                    postcon
                ),
                "HERE".to_string()
            ))
        }
        ,
        _ => todo!("Not supported (yet)."),
    }
}
