pub mod ivl;
mod ivl_ext;
use crate::slang::ast::Case;
use itertools::fold;
use ivl::{IVLCmd, IVLCmdKind};
use regex::NoExpand;
use slang::ast::{
    Cases, Cmd, CmdKind, Expr, ExprKind, Ident, Method, Name, Op, Quantifier, Range, Type, Var,
};
use slang::Span;
use slang_ui::prelude::*;
use std::borrow::Borrow;
// use std::collections::btree_map::Range;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::Write;
use std::iter;
use std::ops::Not;

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
            let mut ivl = cmd_to_ivlcmd(cmd, &m)?;

            //Core A
            //checking if there is no return statement
            //if this is the case add the ensures as a post condition
            //if there is return then it will be encoded in the Return encoding.
            if !contains_return(&m) {
                let re_ensure = ensures_expressions2(&m);
                if re_ensure.1 {
                    //The ivl that i want to return at the end
                    let mut cmdd;

                    //if we have only one ensure we are returning ...
                    if re_ensure.0.len() == 1 {
                        cmdd = Cmd::assert(&re_ensure.0[0], "Ensures might fail!");
                    } else {
                        cmdd = Cmd::assert(&re_ensure.0[0], "Ensures might fail!");

                        for expr in &re_ensure.0[1..] {
                            let cmd = Cmd::assert(&expr, "Ensures might fail!");
                            cmdd = cmdd.seq(&cmd)
                        }
                    }

                    let c = Box::new(cmdd.clone());
                    let k = Box::new(cmd.seq(&c));
                    let h: &Box<Cmd> = &k;
                    ivl = cmd_to_ivlcmd(h, &m)?;
                }
            }

            // Convert IVL to DSA
            let dsa = ivl_to_dsa(&ivl, &mut init_map())?;

            println!("dsa: ");
            println!("{}", dsa.to_string());
            let mut initial_vector = vec![(Expr::bool(true), "".to_string())];
            // Calculate obligation and error message (if obligation is not
            // verified)
            for (oblig, msg) in swp(&dsa, initial_vector) {

    
                // println!("{:?}", initial_vector.clone());
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
        }

        Ok(())
    }
}

//Core A check if a method contains return
fn contains_return(method: &Method) -> bool {
    if let Some(block) = &method.body {
        return check_cmd_for_return(&block.cmd);
    }
    false
}

//Core A check a method contains return
fn check_cmd_for_return(cmd: &Cmd) -> bool {
    match &cmd.kind {
        // If the command is a return, we found a return
        CmdKind::Return { expr: _ } => true,

        // For sequential commands, check both subcommands
        CmdKind::Seq(command1, command2) => {
            check_cmd_for_return(command1) || check_cmd_for_return(command2)
        }

        // For match statements, check if all branches contain a return
        CmdKind::Match { body } => {
            let all_cases_return = body.cases.iter().all(|case| check_cmd_for_return(&case.cmd));
            let true_case = body.cases.iter().any(|case| has_true(&case.condition));
            all_cases_return && true_case
        }

        // For loop statements, check if the loop body contains a return
        CmdKind::Loop { body, .. } => body.cases.iter().any(|case| check_cmd_for_return(&case.cmd)),

        // For "for" loops, check if the body contains a return
        CmdKind::For { body, .. } => check_cmd_for_return(&body.cmd),

        // If a command kind is not expected to contain a return, we default to false
        _ => false,
    }
}


//related to core A
//in this method i am returning all ensures expressions as 1 expr and between each there is and
// fn ensures_expressions(method: &Method) -> (Expr, bool) {
//     let mut ens_exp = Expr::bool(true);

//     let mut ensures_iter = method.ensures();
//     let has_ensures = ensures_iter.next().is_some(); // true if there is at least one expression

//     for ens in method.ensures() {
//         let expr = ens.clone();
//         ens_exp = Expr::and(&ens_exp, &expr);
//     }

//     (ens_exp, has_ensures)
// }

//related to core A
//in this method i am returning all ensures expressions as 1 expr and between each there is and
fn ensures_expressions2(method: &Method) -> (Vec<Expr>, bool) {
    let mut exprs = Vec::new(); // Initialize an empty Vec<Expr>

    let mut ensures_iter = method.ensures();
    let has_ensures = ensures_iter.next().is_some(); // true if there is at least one expression

    for ens in method.ensures() {
        exprs.push(ens.clone()); // Push each Expr into the Vec
    }

    (exprs, has_ensures)
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




//Core B
//These are 2 related functions that iterate over the cases and find the modified variables
//the final result will be vec of Cmd::VarDef of thos modifies variables
//in this implementation u will see duplicated varDef of the same var because is modified in more than
//  one case, can be removed (I can do it if it helps u)
//The idea of it is that before loop we should havoc before the loop
//not sure how it will work with the dsa
fn collect_var_definitions_in_cmd(cmd: &Cmd, var_definitions: &mut Vec<Cmd>) {
    match &cmd.kind {
        // If the command is an assignment, push a Cmd::vardef into the vector
        CmdKind::Assignment { name, expr } => {
            var_definitions.push(Cmd::vardef(name, &expr.ty, &None));
        }
        // If the command is a sequence, recursively process both commands in the sequence
        CmdKind::Seq(cmd1, cmd2) => {
            collect_var_definitions_in_cmd(cmd1, var_definitions);
            collect_var_definitions_in_cmd(cmd2, var_definitions);
        }
        _ => todo!("Not supported (yet)."),
    }
}

fn collect_var_definitions(cases: &Cases) -> Vec<Cmd> {
    let mut var_definitions = Vec::new();

    // Iterate over all the cases
    for case in &cases.cases {
        // Recursively process the commands inside each case
        collect_var_definitions_in_cmd(&case.cmd, &mut var_definitions);
    }

    var_definitions
}

fn collect_variables_from_assignments_in_loop_body(com: Cmd) -> Vec<(Name, Type)> {
    let mut variables = Vec::new();
    match &com.kind {
        CmdKind::Assignment { name, expr } => {
            variables.push((name.clone(), expr.ty.clone()));
        }
        CmdKind::Seq(command1, command2) => {
            let mut variables1 = collect_variables_from_assignments_in_loop_body(*command1.clone());
            let mut variables2 = collect_variables_from_assignments_in_loop_body(*command2.clone());
            variables.append(&mut variables1);
            variables.append(&mut variables2);
        }
        CmdKind::Match { body } => {
            for case in &body.cases {
                let mut case_variables = collect_variables_from_assignments_in_loop_body(case.cmd.clone());
                variables.append(&mut case_variables);
            }
        }
        CmdKind::Loop { body, .. } => {
            for case in &body.cases {
                let mut case_variables = collect_variables_from_assignments_in_loop_body(case.cmd.clone());
                variables.append(&mut case_variables);
            }
        }
        CmdKind::For { body, .. } => {
            let mut body_variables = collect_variables_from_assignments_in_loop_body(*body.cmd.clone());
            variables.append(&mut body_variables);
        }
        _ => todo!("Not supported (yet)."),
    }
    variables
}

// Creates sequence of IVL commands from a vector of IVL commands
fn sequence_from_vec(vec: Vec<IVLCmd>) -> IVLCmd {
    vec.iter()
        .fold(IVLCmd::nop(), |acc, cmd| IVLCmd::seq(&acc, cmd))
}


fn eval_expr(expr: &Expr) -> i64 {
    match &expr.kind {
        ExprKind::Num(n) => *n,
        ExprKind::Infix(expr1, Op::Add, expr2) => eval_expr(expr1) + eval_expr(expr2),
        ExprKind::Infix(expr1, Op::Sub, expr2) => eval_expr(expr1) - eval_expr(expr2),
        ExprKind::Infix(expr1, Op::Mul, expr2) => eval_expr(expr1) * eval_expr(expr2),
        ExprKind::Infix(expr1, Op::Div, expr2) => eval_expr(expr1) / eval_expr(expr2),
        ExprKind::Infix(expr1, Op::Mod,expr2 ) => eval_expr(expr1) % eval_expr(expr2),
        _ => todo!("Cant evaluate this expression"),
    }
}

// Related to extension 1: bounded for-loops (*)
// Function that takes an expression and returns a bool if there is any ident in the expression
fn contains_ident(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Ident(_) => true,
        ExprKind::Infix(expr1, _, expr2) => contains_ident(expr1) || contains_ident(expr2),
        _ => false,
    }
}

// Related to encoding of match statements
fn has_return(cmd: &Cmd) -> bool {
    match &cmd.kind {
        CmdKind::Return { .. } => true,
        CmdKind::Seq(ref left, ref right) => has_return(left) || has_return(right),
        CmdKind::Match { ref body } => body.cases.iter().all(|case| has_return(&case.cmd)),
        CmdKind::Loop { body, .. } => {
            body.cases.iter().any(|case| has_return(&case.cmd)) // Check each case in loop body
        },

        CmdKind::For { body, .. } => {
            has_return(&body.cmd) // Check each command in the for loop's body block
        },
        _ => false,
    }
}

// Related to encoding of match statements
// Checks if one of the guards in the match statement is true
fn has_true(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Bool(true) => true,
        _ => false,
    }
}

// Encoding of (assert-only) statements into IVL (for programs comprised of only
// a single assertion)
fn cmd_to_ivlcmd(cmd: &Cmd, method_initial: &Method) -> Result<IVLCmd> {
    match &cmd.kind {
        CmdKind::Assert { condition, message } => {
            let assert_message = if message.len() < 2 {
                "Assert might fail!".to_string()
            } else {
                message.clone()
            };
            Ok(IVLCmd::assert(condition, &assert_message))
        }
        // Assume has not been documented in the report yet
        // Assume just takes the High level command Assume and passes the condition onto the assume IVL command
        // For the statement "assume true" the condition is "true" | for the statement "assume x == 2" the condition is "x == 2"
        CmdKind::Assume { condition, .. } => Ok(IVLCmd::assume(condition)),
        // Seq has not been documented in the report yet
        // Seq takes 2 commands in the higher level language (CmdKind) and passes them unto the IVLCmd seq
        // Note: the commands have to be processed as well, so that the IVL command seq does not pass on higer level commands
        CmdKind::Seq(command1, command2) => Ok(IVLCmd::seq(
            &cmd_to_ivlcmd(command1, &method_initial)?,
            &cmd_to_ivlcmd(command2, &method_initial)?,
        )),
        CmdKind::Assignment { name, expr } => Ok(IVLCmd::assign(name, expr)),
        CmdKind::Return { expr } => {
            let re_ensure = ensures_expressions2(&method_initial);
        
            // Check if the method has a return expression; if not, ignore `Return`
            match expr {
                Some(expr_value) => {
                    // Check if there are `ensures` specifications to validate
                    if re_ensure.1 {
                        // Start with an initial IVLCmd for the assertions
                        let mut ivlcmd;
        
                        // If there is only one `ensure`, handle it directly
                        if re_ensure.0.len() == 1 {
                            let x = &re_ensure.0[0].span;
                            ivlcmd = IVLCmd::assert(
                                &re_ensure.0[0].subst_result(expr_value).with_span(x.clone()),
                                "Ensures might fail!",
                            );
                        } else {
                            // If multiple `ensures`, sequence the assertions
                            let s = &re_ensure.0[0].span;
                            ivlcmd = IVLCmd::assert(
                                &re_ensure.0[0].subst_result(expr_value).with_span(s.clone()),
                                "Ensures might fail!",
                            );
        
                            // Chain additional ensures with `seq`
                            for expr in &re_ensure.0[1..] {
                                let x = &expr.span;
                                let ivl = IVLCmd::assert(
                                    &expr.subst_result(expr_value).with_span(x.clone()),
                                    "Ensures might fail!",
                                );
                                ivlcmd = ivlcmd.seq(&ivl);
                            }
                        }
        
                        // Add assume(false) to prevent any further execution
                        ivlcmd = ivlcmd.seq(&IVLCmd::assume(&Expr::bool(false)));
        
                        Ok(ivlcmd)
                    } else {
                        // No ensures to validate, just end with assume(false)
                        Ok(IVLCmd::assume(&Expr::bool(false)))
                    }
                }
                None => {
                    // If there is no return expression, end with assume(false)
                    Ok(IVLCmd::assume(&Expr::bool(false)))
                }
            }
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

                    let hav = IVLCmd::havoc(name, ty);
                    let cmdd = IVLCmd::assign(name, expr_value);
                    // cmdd
                    IVLCmd::seq(&hav, &cmdd)
                }
                None => IVLCmd::havoc(name, ty),
            })
        }

        CmdKind::Match { body } => {
            // Check if all cases contain a return
            let all_cases_return = body.cases.iter().all(|case| has_return(&case.cmd));

            let true_case = body.cases.iter().any(|case| has_true(&case.condition));
        
            // Initialize the "base case" as either `assume(false)` or `nop`
            let mut nested_command = if all_cases_return && true_case {
                IVLCmd::seq(&IVLCmd::assume(&Expr::bool(false)), &cmd_to_ivlcmd(&Cmd::new(CmdKind::Return { expr: Some(Expr::num(0)) }), method_initial)?)
                 // Terminate if all cases have return
            } else {
                IVLCmd::nop() // No termination if some cases do not return
            };
        
            // Build nested nondet structure from the last case to the first
            for case in body.cases.iter().rev() {
                let case_guard = case.condition.clone();
                let case_command = cmd_to_ivlcmd(&case.cmd, &method_initial).unwrap();
        
                // Wrap each case as a nondet with the guard
                let assume_guard = IVLCmd::assume(&case_guard);
                let guarded_case = IVLCmd::seq(&assume_guard, &case_command);

                // Weap each nested command with the negation of the guard
                let not_assume_guard = IVLCmd::assume(&Expr::not(case_guard));
                let not_guarded_case = IVLCmd::seq(&not_assume_guard, &nested_command);
        
                // Nest the guarded case with the previous nested command as the fallback
                nested_command = IVLCmd::nondet(&guarded_case, &not_guarded_case);
            }
        
            Ok(nested_command)
        },
        CmdKind::Loop {
            invariants,
            variant,
            body,
        } => {
            let mut invariants = invariants.clone();
            invariants.extend(iter::once(Expr::bool(true)));
            // Create a sequence of invariant assertions
            let sequence_of_invariant_assertions = invariants
                .iter()
                .map(|inv| {
                    Cmd::new(CmdKind::Assert {
                        condition: inv.clone(),
                        message: "Invariant might fail!".to_string(),
                    })
                })
                .reduce(|acc, cmd| Cmd::seq(&acc, &cmd))
                .unwrap_or_else(|| Cmd::nop());

            // initializing vector
            let mut vec_of_modified_variables = Vec::new();
            // Append modified variables from body to the vector vec_of_modified_variables
            for case in body.cases.iter() {
                let vars = collect_variables_from_assignments_in_loop_body(case.cmd.clone());
                // Add all elements from vars to vec_of_modified_variables
                vec_of_modified_variables.extend(vars);
            }

            // Create havoc commands for each variable in vec_of_modified_variables
            let sequence_of_havoc_commands = vec_of_modified_variables.iter().fold(
                Box::new(Cmd::nop()),
                |acc, (var_name, var_type)| {
                    Box::new(Cmd::seq(
                        &acc,
                        &Box::new(Cmd::vardef(var_name, var_type, &None)),
                    ))
                },
            );
            // Create a sequence of assumptions for each invariant
            let sequence_of_invariant_assumptions =
                invariants.iter().fold(Box::new(Cmd::nop()), |acc, inv| {
                    Box::new(Cmd::seq(&acc, &Box::new(Cmd::assume(inv))))
                });
            let mut list_of_conditions = Vec::new();

            // Create a match statement for each case in cases
            let mut sequence_of_cases =
                body.cases
                    .iter()
                    .fold(Vec::new(), |mut acc: Vec<Case>, case| {
                        let condition = case.condition.clone();
                        list_of_conditions.push(condition.clone());
                        if variant.is_some() {
                            let var_name = Ident(
                                "PREDEFINED_VARIABLE_DONT_USE".to_owned()
                                    + &variant.clone().unwrap().span.clone().start().to_string(),
                            );
                            let variant_type = variant.clone().unwrap().ty.clone();
                            let variant_initialization =
                                Cmd::vardef(&Name::ident(var_name.clone()), &variant_type, variant);
                            let assert_var_leq_zero = Cmd::new(CmdKind::Assert {
                                condition: Expr::op(
                                    &variant.clone().unwrap(),
                                    Op::Ge,
                                    &Expr::num(0),
                                ),
                                message: "Variant might not decrease!".to_string(),
                            });
                            let variant_seq =
                                Cmd::seq(&variant_initialization, &assert_var_leq_zero);
                            let command = case.cmd.clone();
                            let variant_seq_command = Cmd::seq(&variant_seq, &command);
                            let assert_variant_lt_start = Cmd::new(CmdKind::Assert {
                                condition: Expr::op(
                                    &variant.clone().unwrap(),
                                    Op::Lt,
                                    &Expr::ident(&var_name.clone(), &variant_type),
                                ),
                                message: "Variant might not decrease!".to_string(),
                            });
                            let assert_variant_lt_start_seq =
                                Cmd::seq(&variant_seq_command, &assert_variant_lt_start);
                            // let seq = Cmd::seq(
                            //     &assert_variant_lt_start_seq,
                            //     &sequence_of_invariant_assertions.clone(),
                            // );
                            // let seq2 = Cmd::seq(&seq, &Cmd::assume(&Expr::bool(false)));
                            acc.push(Case {
                                condition,
                                cmd: assert_variant_lt_start_seq,
                            });
                            acc
                        } else {
                            let command = case.cmd.clone();
                            // let seq = Cmd::seq(&command, &sequence_of_invariant_assertions.clone());
                            // let seq2 = Cmd::seq(&command, &Cmd::assume(&Expr::bool(false)));
                            acc.push(Case {
                                condition,
                                cmd: command,
                            });
                            acc
                        }
                    });

            let combined_conditions = list_of_conditions
                .iter()
                .fold(Expr::bool(false), |acc, cond| acc.or(cond));
            let exit_case = Case {
                condition: Expr::not(combined_conditions.clone()),
                cmd: Cmd::nop(),
            };
            // sequence_of_cases.push(exit_case);
            // print!("sequence_of_cases: {:#?}", sequence_of_cases );

            // Create a match statement for each case in cases
            let match_statement_in_loop = Cmd::new(CmdKind::Match {
                body: Cases {
                    cases: sequence_of_cases,
                    span: invariants[0].span,
                },
            });

            let inner_loop_with_invariants = Cmd::seq(
                &match_statement_in_loop,
                &sequence_of_invariant_assertions.clone(),
            );
            let inner_loop_with_invariants_seq = Cmd::new(CmdKind::Seq(
                Box::new(inner_loop_with_invariants),
                Box::new(Cmd::assume(&Expr::bool(false))),
            ));

            let enter_loop_case = Case {
                condition: combined_conditions,
                cmd: inner_loop_with_invariants_seq,
            };

            let outer_match = Cmd::new(CmdKind::Match {
                body: Cases {
                    cases: vec![enter_loop_case, exit_case],
                    span: invariants[0].span,
                },
            });

            let complete_encoding = Cmd::seq(
                &Cmd::seq(
                    &sequence_of_invariant_assertions, // Assert I
                    &sequence_of_havoc_commands,       // Havoc z̅
                ),
                &Cmd::seq(
                    &sequence_of_invariant_assumptions, // Assume I
                    &outer_match, // Outer match statement with the inner match statement
                ),
            );
            println!("Completed encoding: {:#?}", complete_encoding);

            Ok(cmd_to_ivlcmd(&complete_encoding, &method_initial)?)
        }
        CmdKind::For {
            name,
            range,
            invariants,
            variant,
            body,
        } => {
            let mut invariants = invariants.clone();
            let mut lower;
            let mut upper;
            match range {
                slang::ast::Range::FromTo(start, end) => {
                    lower = start.clone();
                    upper = end.clone();
                }
            };

            if !(contains_ident(&lower) || contains_ident(&upper)) {
                let lowerval = eval_expr(&lower);
                let upperval = eval_expr(&upper);
                let difference = upperval - lowerval;
                if difference <= 0 {
                    Ok(IVLCmd::nop())
                } else {
                    // Repeat the body of the for loop where the loop variable is incremented by 1 between lower and upper
                    let increment_variable = Cmd::new(CmdKind::Assignment {
                        name: name.clone(),
                        expr: Expr::op(
                            &Expr::ident(&name.ident, &range.elem_ty()),
                            Op::Add,
                            &Expr::num(1),
                        ),
                    });
                    let mut initial_point = Cmd::assign(name, &Expr::num(lowerval));
                    for i in 0..difference {
                        let command = *body.cmd.clone();
                        let intermediate_seq = Cmd::seq(&command, &increment_variable);
                        initial_point = Cmd::seq(&initial_point, &intermediate_seq);
                    }
                    Ok(cmd_to_ivlcmd(&initial_point, &method_initial)?)

                    // create a list of values between lowerval and upperval
                    // let values: Vec<(Expr)> = (lowerval..upperval)
                    //     .map(|i| (Expr::num(i)))
                    //     .collect();



                    // values.iter()
                    // .fold(IVLCmd::nop(), |acc, i| {
                    //     let command = *body.clone().cmd;
                    //     let new_body = command.subst_ident(&name.ident, i);
                    //     IVLCmd::seq(&acc, &cmd_to_ivlcmd(&new_body, &method_initial).unwrap())
                    // });
                    // Ok(IVLCmd::nop())

                }   

            } else {
                let lower_invariant =
                    Expr::op(&Expr::ident(&name.ident, &range.elem_ty()), Op::Ge, &lower);
                let upper_invariant =
                    Expr::op(&Expr::ident(&name.ident, &range.elem_ty()), Op::Le, &upper);
                let added_invariants: Vec<Expr> = vec![lower_invariant, upper_invariant];
                invariants.extend(added_invariants);

                let introduce_iterator: Cmd =
                    Cmd::vardef(name, &range.elem_ty(), &Some(lower.clone()));

                let increment_command = Cmd::new(CmdKind::Assignment {
                    name: name.clone(),
                    expr: Expr::op(
                        &Expr::ident(&name.ident, &range.elem_ty()),
                        Op::Add,
                        &Expr::num(1),
                    ),
                });

                let new_body = Cmd::new(CmdKind::Seq(
                    Box::new(*body.clone().cmd),
                    Box::new(increment_command),
                ));

                let loop_case = Case {
                    condition: Expr::op(
                        &Expr::ident(&name.ident, &range.elem_ty()),
                        Op::Lt,
                        &upper,
                    ),
                    cmd: new_body,
                };
                let inner_loop = Cmd::new(CmdKind::Loop {
                    invariants: invariants.clone(),
                    variant: variant.clone(),
                    body: Cases {
                        cases: vec![loop_case.clone()],
                        span: loop_case.condition.span,
                    },
                });

                let seq_with_loop = Cmd::seq(&introduce_iterator, &inner_loop);

                let outer_loop_case = Case {
                    condition: Expr::op(&lower, Op::Lt, &upper),
                    cmd: seq_with_loop,
                };
                let non_loop_case = Case {
                    condition: Expr::op(&lower, Op::Ge, &upper),
                    cmd: Cmd::nop(),
                };

                let outer_match = Cmd::new(CmdKind::Match {
                    body: Cases {
                        cases: vec![outer_loop_case, non_loop_case],
                        span: loop_case.condition.span,
                    },
                });

                // Print invariants
                println!("Invariants: {:#?}", invariants);
                // Print range
                println!("Range: {:#?}", range);
                // Print name
                println!("Name: {:#?}", name);

                // let case_dont_loop = Case {
                //     condition: Expr::op(&Expr::ident(name, &range.ty), Op::Ge, &range.end),
                //     cmd: Cmd::assume(&Expr::bool(false)),
                // };
                // let ensure_correct_range = Cmd::new(CmdKind::Match { body:  });
                Ok(cmd_to_ivlcmd(&outer_match, &method_initial)?)
            }
        },
        CmdKind::MethodCall { name, fun_name, args, method } => {
            let method_ref = method.get().unwrap();
            let method_vars: Vec<Var> = method_ref.args.clone();
            let requires: Vec<Expr> = method_ref.requires().cloned().collect();
            let ensures: Vec<Expr> = method_ref.ensures().cloned().collect();
            
            // Create temporary variables for the arguments with names from their span Expr.span
            
            let mut arg_idents = Vec::new();
            let temp_args_seq: Cmd = args
                .iter()
                .map(|arg| {
                    let ident = Ident(format!("arg_{}_{}", arg.span.start(), arg.span.start()));
                    arg_idents.push(ident.clone());
                    Cmd::vardef(&Name::ident(ident), &arg.ty, &Some(arg.clone()))
                })
                .fold(Cmd::nop(), |acc, cmd| Cmd::seq(&acc, &cmd));

            // Substitute the argument idents in the requires expressions from the one in method_vars with arg_idents, there are equally many in the two list
            let mut new_requires = Vec::new();
            new_requires.push(Expr::bool(true));
            for (i, vars) in method_vars.iter().enumerate() {
                for expr in requires.iter() {
                    new_requires.push(expr.subst_ident(&vars.name.ident, &Expr::ident(&arg_idents[i], &vars.ty.1).with_span(expr.span.clone())));
            }
}

            // Create a sequence of the requires expressions as asserts
            let requires_asserts_seq = new_requires
                .iter()
                .map(|expr| Cmd::new(CmdKind::Assert {
                    condition: expr.clone(),
                    message: "Requires might fail!".to_string(),
                }))
                .fold(Cmd::nop(), |acc, cmd| Cmd::seq(&acc, &cmd));
            
            if name.is_some() {
                let return_var_def = Cmd::vardef(&Name::ident(name.clone().unwrap().ident), &method_ref.return_ty.as_ref().unwrap().1, &None);
                // I would also like to substitute the return value in ensure that is always an ident named 'return' with return_var
                let mut new_ensures_with_return_changed = Vec::new();
                for expr in ensures.iter() {
                    new_ensures_with_return_changed.push(expr.subst_result(&Expr::ident(&name.as_ref().unwrap().ident, &method_ref.return_ty.as_ref().unwrap().1)).with_span(expr.span.clone()));                
                }    
                let mut new_ensures = Vec::new();
                new_ensures.push(Expr::bool(true));
                for (i, vars) in method_vars.iter().enumerate() {
                    for expr in new_ensures_with_return_changed.iter() {
                         new_ensures.push(expr.subst_ident(&vars.name.ident, &Expr::ident(&arg_idents[i], &vars.ty.1)).with_span(expr.span.clone()));
                    }
                }


                // Create a sequence of the ensures expressions as assumes
                let ensures_assumes_seq = new_ensures
                    .iter()
                    .map(|expr| Cmd::new(CmdKind::Assume {
                     condition: expr.clone(),
                    }))
                    .fold(Cmd::nop(), |acc, cmd| Cmd::seq(&acc, &cmd));


                // Create the sequence of first the var declarations, next the requires assert, then havoc and lastly ensure_asumes
                let seq = Cmd::seq(&temp_args_seq, &requires_asserts_seq);
                let seq2 = Cmd::seq(&seq, &return_var_def);
                let seq3 = Cmd::seq(&seq2, &ensures_assumes_seq);
                Ok(cmd_to_ivlcmd(&seq3, method_initial)?)
                
            } else {
                let mut new_ensures = Vec::new();
                new_ensures.push(Expr::bool(true));
                for (i, vars) in method_vars.iter().enumerate() {
                    for expr in ensures.iter() {
                        new_ensures.push(expr.subst_ident(&vars.name.ident, &Expr::ident(&arg_idents[i], &vars.ty.1)));
                    }
                }
                    // Create a sequence of the ensures expressions as assumes
                let ensures_assumes_seq = new_ensures
                    .iter()
                    .map(|expr| Cmd::new(CmdKind::Assume {
                        condition: expr.clone(),
                    }))
                    .fold(Cmd::nop(), |acc, cmd| Cmd::seq(&acc, &cmd));
                let seq = Cmd::seq(&temp_args_seq, &requires_asserts_seq);
                let seq2 = Cmd::seq(&seq, &ensures_assumes_seq);
                Ok(cmd_to_ivlcmd(&seq2, method_initial)?)
            }
        }

        _ => todo!("Not supported (yet)."),
    }
}

fn init_map() -> HashMap<Ident, (i32, Type)> {
    HashMap::new()
}


fn synchronize_cmd(
    com1: IVLCmd,
    map1: HashMap<Ident, (i32, Type)>,
    map2: HashMap<Ident, (i32, Type)>,
) -> IVLCmd {
    let mut synchronized_command = com1;
    for (key, (value1, type1)) in map1 {
        if let Some(&(value2, ref type2)) = map2.get(&key) {
            if value2 > value1 {
                let new_ident = Ident(format!("{}{}", key, value2));
                let old_ident = Ident(format!("{}{}", key, value1));
                let equality_expr = Expr::op(
                    &Expr::ident(&new_ident, type2),
                    Op::Eq,
                    &Expr::ident(&old_ident, &type1),
                );
                let assume = IVLCmd::assume(&equality_expr);
                synchronized_command = IVLCmd::seq(&synchronized_command, &assume);
            }
        }
    }
    synchronized_command
}

// Maybe not sure
fn update_variable_map(
    variable_map: &mut HashMap<Ident, (i32, Type)>,
    map1: &HashMap<Ident, (i32, Type)>,
    map2: &HashMap<Ident, (i32, Type)>,
) {
    // Iterate over map1 and update variable_map
    for (key, &(value1, ref type1)) in map1.iter() {
        let entry = variable_map
            .entry(key.clone())
            .or_insert((value1, type1.clone()));
        if value1 > entry.0 {
            entry.0 = value1;
            entry.1 = type1.clone();
        }
    }

    // Iterate over map2 and update variable_map
    for (key, &(value2, ref type2)) in map2.iter() {
        let entry = variable_map
            .entry(key.clone())
            .or_insert((value2, type2.clone()));
        if value2 > entry.0 {
            entry.0 = value2;
            entry.1 = type2.clone();
        }
    }
}

// Updates a variable to the newest version according to the map
fn update_variable_name(
    variable: &Ident,
    map: &mut HashMap<Ident, (i32, Type)>,
    var_type: Type,
) -> Ident {
    // Check if the variable exists in the map
    let entry = map.entry(variable.clone()).or_insert((0, var_type.clone()));
    // If it does, increase its value by 1
    entry.0 += 1;

    // Return the new variable name with the counter
    let new_variable_name = format!("{}{}", variable.0, entry.0);

    // Create an Ident instance
    Ident(new_variable_name)
}

// Code to make IVL commands to DSA form (Dynamic Single Assignment)
// This code works by creating a map variable_map, which keeps track of all the variables and maps them to the number of times they occur in the program.
// Using the variable_map, we can change the name of each of the variables, to the variablename concatenated with the number.
fn ivl_to_dsa(ivl: &IVLCmd, variable_map: &mut HashMap<Ident, (i32, Type)>) -> Result<IVLCmd> {
    match &ivl.kind {
        // For each of the variables in the variable_map we check whether the variable occurs in the expression (rhs of the assignment)
        // If the variable occur, we change it with the value found in the map (ie. "x" becomes "x5" etc.) and we look for the next variable in the variable_map.
        // Then we look for the variable which gets assigned (the lhs of the assignment) and updates it in the variable_map (see definition of update_variable_name)
        // NB. We use fold, because we want to use the output of the substitution to be the input of the next call of the fold function
        IVLCmdKind::Assignment { name, expr } => {
            let original_span = expr.span.clone();

            let mut expr =
                (variable_map
                    .iter()
                    .fold(expr.clone(), |acc, (var, &(val, ref ty))| {
                        let new_ident = Ident(format!("{}{}", var, val));
                        let new_expr = Expr::ident(&new_ident, &ty.clone());
                        acc.subst_ident(var, &new_expr)
                    }));

            expr.span = original_span;

            let new_name = &Name::ident(update_variable_name(
                &name.ident,
                variable_map,
                expr.ty.clone(),
            ));
            let command = IVLCmd::assume(
                &Expr::ident(&new_name.ident, &expr.ty).op(slang::ast::Op::Eq, &expr),
            );
            Ok(command)
        }
        // For assert we do the same as for assign except we only have an expression, not a new variable.
        // Iterate through the variable_map
        // For each variable look for and change the variable for the appropriate value
        // Continue with the rest of the map
        // NB. We use fold, because we want to use the output of the substitution to be the input of the next call of the fold function
        IVLCmdKind::Assert { condition, message } => {
            let original_span = condition.span.clone();

            let mut new_condition =
                variable_map
                    .iter()
                    .fold(condition.clone(), |acc, (var, &(val, ref ty))| {
                        let new_ident = Ident(format!("{}{}", var, val));
                        let new_expr = Expr::ident(&new_ident, &ty.clone());
                        acc.subst_ident(var, &new_expr)
                    });

            new_condition.span = original_span;

            Ok(IVLCmd::assert(&new_condition, &message.clone()))
        }
        // For assume we do the same as for assign except we only have an expression, not a new variable.
        // Iterate through the variable_map
        // For each variable look for and change the variable for the appropriate value
        // Continue with the rest of the map
        // NB. We use fold, because we want to use the output of the substitution to be the input of the next call of the fold function
        IVLCmdKind::Assume { condition } => Ok(IVLCmd::assume(
            &(variable_map
                .iter()
                .fold(condition.clone(), |acc, (var, &(val, ref ty))| {
                    let new_ident = Ident(format!("{}{}", var, val));
                    let new_expr = Expr::ident(&new_ident, &ty.clone());
                    acc.subst_ident(var, &new_expr)
                })),
        )),
        // For the sequence we simply run the ivl_to_dsa for each of the commands
        // We assume that the rust program runs in sequential order, such that the variable_map gets updated by the first block before being used for the second one.
        IVLCmdKind::Seq(command1, command2) => Ok(IVLCmd::seq(
            &(ivl_to_dsa(command1, variable_map)?),
            &(ivl_to_dsa(command2, variable_map)?),
        )),
        // For nondeterministic blocks we want to first compute the DSA of each individual command block
        // Then have a way of combining the resultant variable_maps, to make sure that we take the highest value for each variable
        // Finally we want to add assignments in the end of the blocks, to synchronize the variables.
        IVLCmdKind::NonDet(command1, command2) => {
            let map1 = &mut variable_map.clone();
            let map2 = &mut variable_map.clone();
            let com1 = ivl_to_dsa(command1, map1)?;
            let com2 = ivl_to_dsa(command2, map2)?;
            let done_com1 = synchronize_cmd(com1, map1.clone(), map2.clone());
            let done_com2 = synchronize_cmd(com2, map2.clone(), map1.clone());
            update_variable_map(variable_map, map1, map2);
            Ok(IVLCmd::nondet(&(done_com1), &(done_com2)))
        }
        IVLCmdKind::Havoc { name, ty } => {
            // println!("name sent to IVLCmd::havoc: {:?}", name);
            // println!("type sent to IVLCmd::havoc: {:?}", &ty.clone());
            // println!("newname sent to IVLCmd::havoc: {:?}", &Name::ident(update_variable_name(&name.ident, variable_map)));
            update_variable_name(&name.ident, variable_map, ty.clone());
            Ok(IVLCmd::nop())
        }
        _ => todo!("Not supported (yet)."),
    }
}

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
        IVLCmdKind::Havoc { name, ty } => unreachable!("Havoc should not be in the IVL command"),
        _ => todo!("Not supported (yet)."),
    }
}

// Weakest precondition of (assert-only) IVL programs comprised of a single assertion
fn swp(ivl: &IVLCmd, mut pc_msg_list: Vec<(Expr, String)>) -> Vec<(Expr, String)> {
    match &ivl.kind {

        IVLCmdKind::Assert { condition, message } => {
            // handled masked errors by first assuming the assert for all existing pc_msg_list
            // Create assume condition:
            let assume_condition = IVLCmd::assume(&condition);
            // Apply the assume condition to all existing pc_msg_list
            let mut new_pc_msg_list = swp(&assume_condition, pc_msg_list.clone());
            new_pc_msg_list.push((condition.clone(), message.clone()));

            new_pc_msg_list
        }
        // Assume has not been documented in the report yet
        // Here the wp of assume with the condition, C, takes the postcondition, G, and returns the weakest precondition:
        // I.e. : wp[assume C](G) = C -> G
        IVLCmdKind::Assume { condition } => {
            for (pc, _msg) in pc_msg_list.iter_mut() {
                // Apply the implication
                let updated_pc = condition.clone().imp(pc);
                *pc = updated_pc.with_span(pc.span); // Ensure the span of `pc` is preserved
            }
            pc_msg_list
        }
        // Seq has not been documented in the report yet
        // Here the wp of assume with the commands: command1 and command2 and the postcondition G returns the weakest precondition:
        // I.e. : wp[command1;command2](G) = wp[command1]( wp[command2](G) )
        IVLCmdKind::Seq(command1, command2) => {
            // The order is important as we need it to be bottom up for swp in order to apply the assumptions correctly.
            let pc_msg_list = swp(command2, pc_msg_list);
            let pc_msg_list = swp(command1, pc_msg_list);
            pc_msg_list
        }
        //After the code is transformed to dsa
        //we compute wp by assuming the assigment, for example if we have x:=3 we assume x==3
        // (name==expr) ==> postcond
        IVLCmdKind::Assignment { name, expr } => unreachable!("Assignment should not be here"),
        //wp of havoc
        //the logic is true but we should make sure that span.Default() is true
        IVLCmdKind::Havoc { name, ty } => unreachable!("Havoc should not be here"),
        IVLCmdKind::NonDet(command1, command2) => {
            // Clone the current pc_msg_list to apply swp to each command independently
            let pc_msg_list1 = swp(command1, pc_msg_list.clone());
            let pc_msg_list2 = swp(command2, pc_msg_list);

            // Combine both lists into a single list to represent non-deterministic choice
            let mut combined_pc_msg_list = pc_msg_list1;
            combined_pc_msg_list.extend(pc_msg_list2);

            combined_pc_msg_list
        }
        _ => todo!("Not supported (yet)."),
    }
}
