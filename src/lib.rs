pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr};
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
            // Encode it in IVL
            let ivl = cmd_to_ivlcmd(cmd)?;
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
        _ => todo!("Not supported (yet)."),
    }
}

// Weakest precondition of (assert-only) IVL programs comprised of a single assertion
fn wp(ivl: &IVLCmd, postcon: &Expr) -> Result<(Expr, String)> {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => Ok((condition.clone(), message.clone())),
        // Assume has not been documented in the report yet
        // Here the wp of assume with the condition, C, takes the postcondition, G, and returns the weakest precondition:
        // I.e. : wp[assume C](G) = C -> G
        IVLCmdKind::Assume { condition } => Ok((condition.clone().imp(postcon), "HERE".to_string())),
        // Seq has not been documented in the report yet
        // Here the wp of assume with the commands: command1 and command2 and the postcondition G returns the weakest precondition:  
        // I.e. : wp[command1;command2](G) = wp[command1]( wp[command2](G) )
        IVLCmdKind::Seq(command1, command2) => {
            Ok((wp(command1, &wp(command2, postcon)?.0)?.0, "SEQ".to_string()))
        }
        _ => todo!("Not supported (yet)."),
    }
}
