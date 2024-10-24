pub mod ivl;
mod ivl_ext;
use std::sync::{Arc, Mutex};
use std::thread;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, Method, Quantifier, Type, Var};
use slang::Span;
use slang_ui::prelude::*;

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

                        // println!("in analyze");
                        // println!("{:?}", (m));
                        // println!("in analyze");


            // Encode it in IVL
            let ivl = cmd_to_ivlcmd(cmd, &m)?;
            // Calculate obligation and error message (if obligation is not
            // verified)
            let (oblig, msg) = wp(&ivl, &Expr::bool(true))?;
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



//related to core A
//in this method i am returning all ensures expressions as 1 expr and between each there is and
fn ensures_expressions(method: &Method) -> (Expr, bool) {
    let mut ens_exp = Expr::bool(true);

    let mut ensures_iter = method.ensures();
    let has_ensures = ensures_iter.next().is_some(); // true if there is at least one expression


    for ens in method.ensures() {
        let expr = ens.clone();
        ens_exp = Expr::and(&ens_exp, &expr);
       
    }

    (ens_exp, has_ensures)
}

//related to core B
//in this method i am returning all invariants expressions as 1 expr and between each there is and
fn invariants_expression(invariants: &Vec<Expr>) -> Expr {
    let mut in_exp = Expr::bool(true);

    for ens in invariants {
        let expr = ens.clone();
        in_exp = Expr::and(&in_exp, &expr);
    }

    in_exp
}



// Encoding of (assert-only) statements into IVL (for programs comprised of only
// a single assertion)
fn cmd_to_ivlcmd(cmd: &Cmd, method: &Method) -> Result<IVLCmd> {
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
            &cmd_to_ivlcmd(command1, &method)?,
            &cmd_to_ivlcmd(command2, &method)?,
        )),
        CmdKind::Assignment { name, expr } => Ok(IVLCmd::assign(name, expr)),
        CmdKind::Loop { invariants, variant, body }=>{
            let invariantExpr=invariants_expression(invariants);

            let cmd_case=body.cases.first().map(|case| &case.cmd);
            println!("in cmd to ivl");
                        println!("{:?}", cmd_case);
                        println!("in cmd to ivl");
            // assert i
            //ask ta what should we havoc here..
            // havoc x
            // assume i
            

            Ok(IVLCmd::nop())
        },
        CmdKind::Return { expr } => {
            //ask ta ..
            // should we assume that the programmer will return only at the end of the method?
            let re_ensure = ensures_expressions(&method);
            //first of all check  if the method is returning something
            //if no ignore the return cmdKind
            match expr {
                Some(expr_value) => {
                    //here i should find if there are ensures in the specifications
                    //if yes then i should assert it else i should nop()
                    if re_ensure.1 {
                        // println!("in cmd to ivl");
                        // println!("{:?}", &re_ensure.0.subst_result(expr_value));
                        // println!("in cmd to ivl");
                        //here re_ensure.0 is th expr that hold all ensures
                        //my aim is to change the appearance of result by expr_value
                        Ok(IVLCmd::assert(
                            &re_ensure.0.subst_result(expr_value),
                            "Ensures might fail!",
                        ))
                    } else {
                        Ok(IVLCmd::nop())
                    }
                }
                None => Ok(IVLCmd::nop()),
            }

            // Ok(IVLCmd::nop())
        }

        CmdKind::VarDefinition {
            name,
            ty: (_span, ty),
            expr,
        } => {
            Ok(match expr {
                Some(expr_value) => {
                    // ask ta
                    //not sure if we should do the havoc before assign or assign is enough
                    //if we should perform the havoc before then IVLCmd::seq(&hav, &cmdd) should be called
                    //but then the wp of assign is implemented twice so we should fix the implementation
                    //the logic is true implementation is false

                    // let hav=IVLCmd::havoc(name, ty);
                    let cmdd = IVLCmd::assign(name, expr_value);
                    cmdd
                    // IVLCmd::seq(&hav, &cmdd)
                }
                None => IVLCmd::havoc(name, ty),
            })
        }

        _ => todo!("Not supported (yet)."),
    }
}

// static GLOBAL_COUNTER: Mutex<u32> = Mutex::new(0);

// fn increment_counter() {
//     let mut counter = GLOBAL_COUNTER.lock().unwrap();
//     *counter += 1;
// }

// fn get_counter() -> u32 {
//     return *GLOBAL_COUNTER.lock().unwrap()
// }

// Code to substitute variables in an expressions, to make the IVL commands into DSA
// fn sub_new_var(expr:Expr) -> Result<Expr>{
//     match &expr {
//         Expr::ExprKind::Infix::add{e1,e2} => Ok(Expr::error()),
//         _ => todo!("Not supported (yet)."),
//     }
// }

// Code to make IVL commands to DSA form (Dynamic Single Assignment)
// MAYBE NOT IVLCmdKind but just IVLCmd
// fn ivl_to_dsa(ivl: &IVLCmd) -> Result<IVLCmdKind>{
//     match &ivl.kind {
//         IVLCmdKind::Assignment { name, expr } => Ok(IVLCmdKind::Assignment { name: (), expr: () }),
//         _ => todo!("Not supported (yet)."),
//     }

// }

// Weakest precondition of (assert-only) IVL programs comprised of a single assertion
fn wp(ivl: &IVLCmd, postcon: &Expr) -> Result<(Expr, String)> {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => {
            Ok((condition.clone().and(postcon), message.clone()))
        }
        // Assume has not been documented in the report yet
        // Here the wp of assume with the condition, C, takes the postcondition, G, and returns the weakest precondition:
        // I.e. : wp[assume C](G) = C -> G
        IVLCmdKind::Assume { condition } => {
            Ok((condition.clone().imp(postcon), "HERE".to_string()))
        }
        // Seq has not been documented in the report yet
        // Here the wp of assume with the commands: command1 and command2 and the postcondition G returns the weakest precondition:
        // I.e. : wp[command1;command2](G) = wp[command1]( wp[command2](G) )
        IVLCmdKind::Seq(command1, command2) => Ok((
            wp(command1, &wp(command2, postcon)?.0)?.0,
            "SEQ".to_string(),
        )),
        //After the code is transformed to dsa
        //we compute wp by assuming the assigment, for example if we have x:=3 we assume x==3
        // (name==expr) ==> postcond
        IVLCmdKind::Assignment { name, expr } => Ok((
            (Expr::ident(&name.ident, &expr.ty).op(slang::ast::Op::Eq, expr)).imp(postcon),
            "Assignment".to_string(),
        )),
        //wp of havoc
        //the logic is true but we should make sure that span.Default() is true
        IVLCmdKind::Havoc { name, ty } => Ok((
            Expr::quantifier(
                Quantifier::Forall,
                &[Var {
                    span: Span::default(),
                    name: name.clone(),
                    ty: (Span::default(), ty.clone()),
                }],
                postcon,
            ),
            "HERE".to_string(),
        )),
        _ => todo!("Not supported (yet)."),
    }
}
