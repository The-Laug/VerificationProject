pub mod ivl;
mod ivl_ext;
use crate::slang::ast::Case;
use itertools::fold;
use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cases, Cmd, CmdKind, Expr, ExprKind, Ident, Method, Name, Quantifier, Type, Var};
use slang::Span;
use slang_ui::prelude::*;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::Write;

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
                let ensure = ensures_expressions(&m);
                if ensure.1 {
                    //it looks  a lot of statements to do simple thing but it worked
                    let new_cmd = Cmd::assert(&ensure.0, "ensure may fail");
                    let c = Box::new(new_cmd.clone());
                    let k = Box::new(cmd.seq(&c));
                    let h: &Box<Cmd> = &k;
                    ivl = cmd_to_ivlcmd(h, &m)?;
                }
            }

            // Convert IVL to DSA
            let dsa = ivl_to_dsa(&ivl, &mut init_map())?;

            print!("dsa: ");
            print!("{}", dsa.to_string());
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
        CmdKind::Return { expr: _ } => true,
        CmdKind::Seq(command1, command2) => {
            check_cmd_for_return(command1) || check_cmd_for_return(command2)
        }
        _ => false,
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


fn collect_variables_from_assignments_in_loop_body(com:Cmd) ->Vec<(Name,Type)> {
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
        _ => todo!("Not supported (yet)."),
    }
    variables
}  

// Creates sequence of IVL commands from a vector of IVL commands
fn sequence_from_vec(vec: Vec<IVLCmd>) -> IVLCmd {
    vec.iter().fold(IVLCmd::nop(), |acc, cmd| IVLCmd::seq(&acc, cmd))
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
        CmdKind::Loop {
            invariants,
            variant,
            body,
        } => {
            //first we need to do 
            // assert I ;
            //  havoc x;
            //  assume I
            let invariant_expr = invariants_expression(invariants);
            //I do not know how to make this flow in the cmds below
            let assert_invariant = IVLCmd::assert(&invariant_expr, "invariant");
            //assume invariant
            let assume_invariant = IVLCmd::assume(&invariant_expr);

            let modified_variables = collect_var_definitions(&body);
            //The above variables should be connected in some way


            // the cases of the loop should be handled as match

            Ok(IVLCmd::nop())
        }
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

                    let hav = IVLCmd::havoc(name, ty);
                    let cmdd = IVLCmd::assign(name, expr_value);
                    // cmdd
                    IVLCmd::seq(&hav, &cmdd)
                }
                None => IVLCmd::havoc(name, ty),
            })
        }

        CmdKind::Match { body } => {
            // Here, we create a start for the match, which we can use as an initial point for the fold function
            // The initial case is "Assume false;assert True"
            let start = IVLCmd::seq(
                &IVLCmd::assume(&Expr::bool(false)),
                &IVLCmd::assert(&Expr::bool(true), "message"),
            );
            // Here we call the fold function, which takes the start and the cases from the match.
            // The fold function will iterate over the cases and create a command for each case, which is then combined with the previous command.
            // The fold collects new cases with a NonDet command.
            // With the initial command the fold output looks like this:
            // Assume false ; assert true [] assume b1; c1 [] assume b2; c2 [] assume b3; c3
            let command = body.cases.iter().fold(start, |acc: IVLCmd, case: &Case| {
                let con = case.condition.clone();
                let case_command = case.cmd.clone();
                let assume = IVLCmd::assume(&con);
                let cmd = cmd_to_ivlcmd(&case_command, &method).unwrap();
                IVLCmd::nondet(&acc, &IVLCmd::seq(&assume, &cmd))
                // Use reduce (Fold som ikke tager initial element)
            });
            Ok(command)
        }
        CmdKind::Loop { invariants, variant, body } => {
            let sequence_of_invariant_assertions = invariants.iter().fold(IVLCmd::nop(), |acc, inv| {
                IVLCmd::seq(&acc, &IVLCmd::assert(inv, "Invariant might fail!"))
            });
            // initializing vector
            let mut vec_of_modified_variables = Vec::new();
            // Append modified variables from body to the vector vec_of_modified_variables
            for case in body.cases.iter() {
                let vars =collect_variables_from_assignments_in_loop_body(case.cmd.clone());
                // Add all elements from vars to vec_of_modified_variables
                vec_of_modified_variables.extend(vars);
            }


            // Create havoc commands for each variable in vec_of_modified_variables
            let sequence_of_havoc_commands = vec_of_modified_variables.iter().fold(IVLCmd::nop(), |acc, (var_name,var_type)| {
                IVLCmd::seq(&acc, &IVLCmd::havoc(&var_name, &var_type))
            });
            // Create a sequence of assumptions for each invariant
            let sequence_of_invariant_assumptions = invariants.iter().fold(IVLCmd::nop(), |acc, inv| {
                IVLCmd::seq(&acc, &IVLCmd::assume(inv))
            });

            // Create a match statement for each case in cases
            let sequence_of_cases = body.cases.iter().fold(IVLCmd::nop(), |acc, case| {
                let condition = case.condition.clone();
                let command = case.cmd.clone();
                let assume = IVLCmd::assume(&condition);
                let cmd = cmd_to_ivlcmd(&command, &method).unwrap();
                let seq = IVLCmd::seq(&assume, &cmd);
                let first_seq = IVLCmd::seq(&seq, &sequence_of_invariant_assertions);
                let assume_false = IVLCmd::assume(&Expr::bool(false));
                let sequence = IVLCmd::seq( &first_seq,&assume_false);
                IVLCmd::nondet(&acc, &sequence)
            });

            
            // Creating vector of all the commands
            let mut all_commands = vec![
                sequence_of_invariant_assertions,
                sequence_of_havoc_commands,
                sequence_of_invariant_assumptions,
                sequence_of_cases,
                ];
                
            // Combine all the commands into a single command with sequences
            let final_command = sequence_from_vec(all_commands);
            
            Ok(final_command)

        }

        _ => todo!("Not supported (yet)."),
    }
}

// assert I; 
// havoc z̅; 
// assume I; // (1) re-declarations gone, assumption changed
// if (b) {
//   enc(C); // encoding of C 
//   assert I; // fails if I is not an invariant
//   assume false // (2) discard remaining execution steps 
// } else {
//   skip
// }

// Code to substitute variables in an expressions, to make the IVL commands into DSA
// fn sub_new_var(expr:Expr) -> Result<Expr>{
//     match &expr {
//         Expr::ExprKind::Infix::add{e1,e2} => Ok(Expr::error()),
//         _ => todo!("Not supported (yet)."),
//     }
// }

// Initializing an empty hashmap
fn init_map() -> HashMap<Ident, (i32, Type)> {
    HashMap::new()
}

fn synchronize_cmd(
    com1: IVLCmd,
    map1: HashMap<Ident, (i32, Type)>,
    map2: HashMap<Ident, (i32, Type)>,
) -> IVLCmd {
    for (key, (value1, _)) in map1 {
        if let Some(&(value2, _)) = map2.get(&key) {
            if value2 > value1 {
                let new_ident = Ident(format!("{}{}", key, value2));
                let old_ident = Ident(format!("{}{}", key, value1));
                let assign = IVLCmd::assign(
                    &Name::ident(new_ident),
                    &Expr::ident(
                        &old_ident,
                        &Type::Unknown {
                            name: Name::ident(old_ident.clone()),
                        },
                    ),
                );
                IVLCmd::seq(&com1, &assign);
            }
        }
    }
    com1
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
            println!("Assignment before substitution, span: {}-{}", expr.span.start(), expr.span.end());

            let original_span = expr.span.clone();

            let mut expr = (variable_map
                .iter()
                .fold(expr.clone(), |acc, (var, &(val, ref ty))| {
                    let new_ident = Ident(format!("{}{}", var, val));
                    let new_expr = Expr::ident(&new_ident, &ty.clone());
                    acc.subst_ident(var, &new_expr)
                }));
            
            expr.span = original_span;
            println!("Assignment after substitution, span: {}-{}", expr.span.start(), expr.span.end());


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
            println!("Assert before substitution, span: {}-{}", condition.span.start(), condition.span.end());

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
            println!("Assert after substitution, span: {}-{}", new_condition.span.start(), new_condition.span.end());

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
            Ok(IVLCmd::assume(&Expr::bool(true)))
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
    
         

            // Push the condition and message into pc_msg_list
            pc_msg_list.push((condition.clone(), message.clone()));

            // Print the updated pc_msg_list to verify it has been added correctly
            println!("Updated pc_msg_list:");
            for (i, (pc, msg)) in pc_msg_list.iter().enumerate() {
                println!("  Entry {}: Condition: {}, Message: {}", i + 1, pc.to_string(), msg);
            }

            pc_msg_list
        }
        // Assume has not been documented in the report yet
        // Here the wp of assume with the condition, C, takes the postcondition, G, and returns the weakest precondition:
        // I.e. : wp[assume C](G) = C -> G
        IVLCmdKind::Assume { condition } => {
            for (pc, msg) in pc_msg_list.iter_mut() {
        
                // Apply the implication
                let updated_pc = condition.clone().imp(pc);
                *pc = updated_pc.with_span(pc.span);  // Ensure the span of `pc` is preserved
                
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
