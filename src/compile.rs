#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(warnings)]



use crate::asm::instrs_to_string;
use crate::asm::{Arg32, Arg64, BinArgs, Instr, JmpArg, MemRef, MovArgs, Offset, Reg, Reg32};
use crate::syntax::{Exp, FunDecl, ImmExp, Prim1, Prim2, SeqExp, SeqProg, SurfFunDecl, SurfProg};
use core::panic;
use std::collections::HashSet;
use crate::span::Span1;
use std::convert::TryInto;
use std::collections::HashMap;




fn usize_to_i32(x: usize) -> i32 {
    x.try_into().unwrap()
}

#[derive(Debug, PartialEq, Eq)]
pub enum CompileErr<Span> {
    UnboundVariable {
        unbound: String,
        location: Span,
    },
    /*UndefinedFunction {
        undefined: String,
        location: Span,
    },*/
    // The Span here is the Span of the let-expression that has the two duplicated bindings
    DuplicateBinding {
        duplicated_name: String,
        location: Span,
    },

    Overflow {
        num: i64,
        location: Span,
    },

    DuplicateFunName {
        duplicated_name: String,
        location: Span, // the locativarson of the 2nd function
    },

    DuplicateArgName {
        duplicated_name: String,
        location: Span,
    },
}


// vars contains both all function dec and variables
fn check_prog_helper<'a, Span>(
    p: &'a SurfProg<Span>,
    mut vars: HashSet<String>,
    mut funs: HashSet<String>,
) -> (Result<(), CompileErr<Span>>, HashSet<String>)
where
    Span: Clone,
{
    let max = std::i64::MAX >> 1;
    let min = std::i64::MIN >> 1;
    match p {
        SurfProg::Num(n, ann) => {
            // check if n is greater than max_snake_int or less than min_snake_int

            if n > &max || n < &min {
                return (Err(CompileErr::Overflow { num: *n, location: ann.clone() }), funs);
              } else {
                return (Ok(()), funs);
              }
        }, 
        SurfProg::Var(s, ann) => {
            // if varible is not defined, return CompilErr UnboundVariable with useful args
            if vars.contains(s) {
                return (Ok(()), funs);
            } else if funs.contains(s) {
                return (Ok(()), funs);
            } else {
                /*if (funs.contains_key(s)){
                    return (Err(CompileErr::FunctionUsedAsValue { 
                        function_name: s.to_string(), 
                        location: ann.clone() 
                    }), funs);
                }*/
                return (Err(CompileErr::UnboundVariable {
                    unbound: s.to_string(),
                    location: ann.clone(),
                }), funs);
            }
        }
        SurfProg::Bool(_bool, _Ann) => {
            return (Ok(()), funs);
        }
        SurfProg::Prim1(_p, sub, _ann) => {


            check_prog_helper(sub, vars, funs) 
            // add1 and sub1 are okay if subexpression is okay
            // not ok if sub 
        }

        // concrete: add1(1) + sub1(2)
        // abstract: add(add1(1), sub1(2))
        SurfProg::Prim2(_p, sub1, sub2, _ann) => {
            // add, sub, and mul are okay if both subexpressions are okay
            let (a, funs) = check_prog_helper(sub1, vars.clone(), funs);
            let (b, funs) = check_prog_helper(sub2, vars.clone(), funs);
            if a.is_err() {
                return (a, funs);
            } else if b.is_err() {
                return (b, funs);
            } else {
                return (Ok(()), funs);
            }
        }
        // let x = 2, y = 3, z=4 in {
        //    let z = 2 in 5
        // }
        SurfProg::Let {
            bindings,
            body,
            ann,
        } => {
            //if > 1 binding per varible, return CompileErr DuplicateBinding(args)
            let mut new_vars: HashSet<&String> = HashSet::new(); // don't let inner varibles leak to outer scope
            for (s, sub) in bindings {
                // for each string s and expression sub in bindings
                let mut temp;
                (temp, funs) = check_prog_helper(sub, vars.clone(), funs.clone());
                if (temp.is_err()) {return (temp, funs);} // return error if subexpression is invalid
                if new_vars.contains(s) {
                    return (Err(CompileErr::DuplicateBinding {
                        duplicated_name: s.to_string(),
                        location: ann.clone(), // duplicate in scope
                    }), funs);
                } else {
                    new_vars.insert(s);
                    vars.insert(s.to_string());
                }
            }
            return check_prog_helper(body, vars, funs);
        }
        SurfProg::If {
            cond,
            thn,
            els,
            ann,
        } => {
            // okay if cond, then, and else expressions are okay

            /*
            let a = check_prog_helper(cond, vars);
            let b = check_prog_helper(thn, vars);
            let c = check_prog_helper(els, vars);
            if a.unwrap().0.is_err { return a; }
            else if b.unwrap().0.is_error { return b; }
            else if c.unwrap().0.is_error { return c; }
            else { return OK(()); } */

            let subs = vec![cond, thn, els];
            for x in subs {
                let a = check_prog_helper(x, vars.clone(), funs.clone());
                if a.0.is_err() {
                    return a;
                }
            }
            return (Ok(()), funs);
        }
        SurfProg::Call(fun, args, ann) => {
            // returns errors: FunctionCalledWrongArity, ValueUsedAsFunction, UndefinedFunction
            let cur_num_args = args.len();
            
            for cur_arg in args {
                let (temp, funs_temp) = check_prog_helper(cur_arg, vars.clone(), funs);
                funs = funs_temp;
                if temp.is_err() { return (temp, funs); }
            }
            return (Ok(()), funs);
        }

        SurfProg::FunDefs { decls, body, ann } => {
            
          //  println!("decls");
            for curr_dec in decls{
       /*         println!("current decl name: {}", curr_dec.name.to_string());

                print!("funs keys: ");
                for f in funs.clone(){
                    print!("{}, ", f.0);
                }
                println!("");

                println!("funs.contains_key(curr_decl) {}", funs.contains_key(&curr_dec.name));*/

                if funs.contains(&curr_dec.name) {
                    //println!("got true ");
                    return (Err(CompileErr::DuplicateFunName {
                        duplicated_name: curr_dec.name.to_string(),
                        location: ann.clone(),
                    }), funs);
                }
                else{
                    let mut para = curr_dec.parameters.clone();
                    // let mut para_clone = curr_dec.parameters.clone();
                    while para.len() > 0{//foo(a,b,a)
                        let temp = para.pop().unwrap();
                    // let temp = para_clone.pop().unwrap();
                        if para.contains(&temp) {
                            return (Err(CompileErr::DuplicateArgName { 
                                duplicated_name: temp, 
                                location: ann.clone(), 
                            }), funs);
                        } 
                        vars.insert(temp);
                        
                    }
                    funs.insert(curr_dec.name.to_string());
                    let (temp_error, temp_funs) = check_prog_helper(&curr_dec.body, vars.clone(), funs);
                    funs = temp_funs;
                    if (temp_error.is_err()) {
                        return (temp_error, funs);
                    }
                }   
            }
            return check_prog_helper(body, vars, funs);
        }

        SurfProg::Array(vec, ann) => {
            for curr_exp in vec{
                let result;
                (result, funs) = check_prog_helper(curr_exp, vars.clone(), funs.clone());
                if (result.is_err()) {return (result, funs);}
            }
            return (Ok(()), funs);
        }
        SurfProg::ArraySet{array, index, new_value, ann} => {
            let mut result;
            (result, funs) = check_prog_helper(array, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            (result, funs) = check_prog_helper(index, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            (result, funs) = check_prog_helper(new_value, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            return (Ok(()), funs);

        }
        SurfProg::Semicolon{e1, e2, ann} => {
            let mut result;
            (result, funs) = check_prog_helper(e1, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            (result, funs) = check_prog_helper(e2, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            return (Ok(()), funs);
        }
        SurfProg::Lambda{parameters, body, ann} => {
            //panic!("NYI::Lambda");
            let mut new_vars: HashSet<&String> = HashSet::new();
            for s in parameters {
                if new_vars.contains(s) {
                    return (Err(CompileErr::DuplicateBinding {
                        duplicated_name: s.to_string(),
                        location: ann.clone(),
                    }), funs);
                } else {
                    new_vars.insert(s);
                    vars.insert(s.to_string());
                }
            }
            return check_prog_helper(body, vars, funs);
        }
        SurfProg::MakeClosure{arity, label, env, ann} => {
            return check_prog_helper(env, vars, funs);
        }
    }
    
}

fn check_prog_helper_prints<'a, Span>(
    p: &'a SurfProg<Span>,
    mut vars: HashSet<String>,
    mut funs: HashSet<String>,
) -> (Result<(), CompileErr<Span>>, HashSet<String>)
where
    Span: Clone,
{
    let max = std::i64::MAX >> 1;
    let min = std::i64::MIN >> 1;
    match p {
        SurfProg::Num(n, ann) => {
            // check if n is greater than max_snake_int or less than min_snake_int
            print!("Num({})", n);
            if n > &max || n < &min {
                return (Err(CompileErr::Overflow { num: *n, location: ann.clone() }), funs);
              } else {
                return (Ok(()), funs);
              }
        }, 
        SurfProg::Var(s, ann) => {
            // if varible is not defined, return CompilErr UnboundVariable with useful args
            print!("Var({})", s);
            if vars.contains(s) {
                return (Ok(()), funs);
            } else if funs.contains(s) {
                return (Ok(()), funs);
            } else {
                /*if (funs.contains_key(s)){
                    return (Err(CompileErr::FunctionUsedAsValue { 
                        function_name: s.to_string(), 
                        location: ann.clone() 
                    }), funs);
                }*/
                return (Err(CompileErr::UnboundVariable {
                    unbound: s.to_string(),
                    location: ann.clone(),
                }), funs);
            }
        }
        SurfProg::Bool(b, _Ann) => {
            print!("Bool({})", b);
            return (Ok(()), funs);
        }
        SurfProg::Prim1(_p, sub, _ann) => {

            print!("Prim1(p, ");
            let out = check_prog_helper_prints(sub, vars, funs);
            print!(")");
            return out;
        }

        // concrete: add1(1) + sub1(2)
        // abstract: add(add1(1), sub1(2))
        SurfProg::Prim2(_p, sub1, sub2, _ann) => {
            // add, sub, and mul are okay if both subexpressions are okay
            print!("Prim2(");
            let (a, funs) = check_prog_helper_prints(sub1, vars.clone(), funs);
            print!(", ");
            let (b, funs) = check_prog_helper_prints(sub2, vars.clone(), funs);
            print!(")");
            if a.is_err() {
                return (a, funs);
            } else if b.is_err() {
                return (b, funs);
            } else {
                return (Ok(()), funs);
            }
        }
        // let x = 2, y = 3, z=4 in {
        //    let z = 2 in 5
        // }
        SurfProg::Let {
            bindings,
            body,
            ann,
        } => {
            //if > 1 binding per varible, return CompileErr DuplicateBinding(args)
            let mut new_vars: HashSet<&String> = HashSet::new(); // don't let inner varibles leak to outer scope
            
            print!("Let((Bindings(");
            for (s, sub) in bindings {
                // for each string s and expression sub in bindings
                let mut temp;
                print!("{} = ", s);
                (temp, funs) = check_prog_helper_prints(sub, vars.clone(), funs.clone());
                print!(", ");
                if (temp.is_err()) {return (temp, funs);} // return error if subexpression is invalid
                if new_vars.contains(s) {
                    return (Err(CompileErr::DuplicateBinding {
                        duplicated_name: s.to_string(),
                        location: ann.clone(), // duplicate in scope
                    }), funs);
                } else {
                    new_vars.insert(s);
                    vars.insert(s.to_string());
                }
            }
            print!("), Let_body(");
            let a = check_prog_helper_prints(body, vars, funs);
            print!("))");
            return a;
        }
        SurfProg::If {
            cond,
            thn,
            els,
            ann,
        } => {
            let subs = vec![cond, thn, els];
            print!("If(");
            for x in subs {
                let a = check_prog_helper_prints(x, vars.clone(), funs.clone());
                print!(", ");
                if a.0.is_err() {
                    return a;
                }
            }
            print!(")");
            return (Ok(()), funs);
        }
        SurfProg::Call(fun, args, ann) => {
            // returns errors: FunctionCalledWrongArity, ValueUsedAsFunction, UndefinedFunction
            let cur_num_args = args.len();
            print!("Call(");
            check_prog_helper_prints(fun, vars.clone(), funs.clone());
            print!(", args:[");
            
            for cur_arg in args {
                let (temp, funs_temp) = check_prog_helper_prints(cur_arg, vars.clone(), funs);
                print!(",");
                funs = funs_temp;
                if temp.is_err() { return (temp, funs); }
            }
            print!("])");
            return (Ok(()), funs);
        }

        SurfProg::FunDefs { decls, body, ann } => {
            print!("FunDefs(stuff, body(");
            for curr_dec in decls{

                if funs.contains(&curr_dec.name) {
                    //println!("got true ");
                    return (Err(CompileErr::DuplicateFunName {
                        duplicated_name: curr_dec.name.to_string(),
                        location: ann.clone(),
                    }), funs);
                }
                else{
                    let mut para = curr_dec.parameters.clone();
                    // let mut para_clone = curr_dec.parameters.clone();
                    while para.len() > 0{//foo(a,b,a)
                        let temp = para.pop().unwrap();
                    // let temp = para_clone.pop().unwrap();
                        if para.contains(&temp) {
                            return (Err(CompileErr::DuplicateArgName { 
                                duplicated_name: temp, 
                                location: ann.clone(), 
                            }), funs);
                        } 
                        vars.insert(temp);
                        
                    }
                    funs.insert(curr_dec.name.to_string());
                    let (temp_error, temp_funs) = check_prog_helper_prints(&curr_dec.body, vars.clone(), funs);
                    funs = temp_funs;
                    if (temp_error.is_err()) {
                        return (temp_error, funs);
                    }
                }   
            }
            let x = check_prog_helper_prints(body, vars, funs);
            print!(")");
            return x;
        }

        SurfProg::Array(vec, ann) => {
            print!("Array(stuff)");

            for curr_exp in vec{
                let result;
                (result, funs) = check_prog_helper_prints(curr_exp, vars.clone(), funs.clone());
                if (result.is_err()) {return (result, funs);}
            }
            return (Ok(()), funs);
        }
        SurfProg::ArraySet{array, index, new_value, ann} => {
            print!("Arrayset(stuff)");

            let mut result;
            (result, funs) = check_prog_helper_prints(array, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            (result, funs) = check_prog_helper_prints(index, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            (result, funs) = check_prog_helper_prints(new_value, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            return (Ok(()), funs);

        }
        SurfProg::Semicolon{e1, e2, ann} => {
            print!("Semicolon(stuff)");

            let mut result;
            (result, funs) = check_prog_helper_prints(e1, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            (result, funs) = check_prog_helper_prints(e2, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            return (Ok(()), funs);
        }
        SurfProg::Lambda{parameters, body, ann} => {
            //panic!("NYI::Lambda");
            print!("Lambda(stuff)");
            let mut new_vars: HashSet<&String> = HashSet::new();
            for s in parameters {
                if new_vars.contains(s) {
                    return (Err(CompileErr::DuplicateBinding {
                        duplicated_name: s.to_string(),
                        location: ann.clone(),
                    }), funs);
                } else {
                    new_vars.insert(s);
                    vars.insert(s.to_string());
                }
            }
            return check_prog_helper_prints(body, vars, funs);
        }
        SurfProg::MakeClosure{arity, label, env, ann} => {
            print!("MakeClosure(stuff)");

            return check_prog_helper_prints(env, vars, funs);
        }
    }
    
}

fn check_prog_helper2<'a, Span>(
    p: &'a SurfProg<Span>,
    mut vars: HashSet<String>,
    mut funs: HashSet<String>,
) -> (Result<(), CompileErr<Span>>, HashSet<String>)
where
    Span: Clone,
{
    let max = std::i64::MAX >> 1;
    let min = std::i64::MIN >> 1;
    match p {
        SurfProg::Num(n, ann) => {
            // check if n is greater than max_snake_int or less than min_snake_int

            if n > &max || n < &min {
                return (Err(CompileErr::Overflow { num: *n, location: ann.clone() }), funs);
              } else {
                return (Ok(()), funs);
              }
        }, 
        SurfProg::Var(s, ann) => {
            // if varible is not defined, return CompilErr UnboundVariable with useful args
            if vars.contains(s) {
                return (Ok(()), funs);
            } else if funs.contains(s){
                return (Ok(()), funs);
            } else {
                /*if (funs.contains_key(s)){
                    return (Err(CompileErr::FunctionUsedAsValue { 
                        function_name: s.to_string(), 
                        location: ann.clone() 
                    }), funs);
                }*/
                return (Err(CompileErr::UnboundVariable {
                    unbound: s.to_string(),
                    location: ann.clone(),
                }), funs);
            }
        }
        SurfProg::Bool(_bool, _Ann) => {
            return (Ok(()), funs);
        }
        SurfProg::Prim1(_p, sub, _ann) => {


            check_prog_helper2(sub, vars, funs) 
            // add1 and sub1 are okay if subexpression is okay
            // not ok if sub 
        }

        // concrete: add1(1) + sub1(2)
        // abstract: add(add1(1), sub1(2))
        SurfProg::Prim2(_p, sub1, sub2, _ann) => {
            // add, sub, and mul are okay if both subexpressions are okay
            let (a, funs) = check_prog_helper2(sub1, vars.clone(), funs);
            let (b, funs) = check_prog_helper2(sub2, vars.clone(), funs);
            if a.is_err() {
                return (a, funs);
            } else if b.is_err() {
                return (b, funs);
            } else {
                return (Ok(()), funs);
            }
        }
        // let x = 2, y = 3, z=4 in {
        //    let z = 2 in 5
        // }
        SurfProg::Let {
            bindings,
            body,
            ann,
        } => {
            //if > 1 binding per varible, return CompileErr DuplicateBinding(args)
            let mut new_vars: HashSet<&String> = HashSet::new(); // don't let inner varibles leak to outer scope
            for (s, sub) in bindings {
                // for each string s and expression sub in bindings
                let mut temp;
                (temp, funs) = check_prog_helper2(sub, vars.clone(), funs.clone());
                if (temp.is_err()) {return (temp, funs);} // return error if subexpression is invalid
                if new_vars.contains(s) {
                    return (Err(CompileErr::DuplicateBinding {
                        duplicated_name: s.to_string(),
                        location: ann.clone(), // duplicate in scope
                    }), funs);
                } else {
                    new_vars.insert(s);
                    vars.insert(s.to_string());
                }
            }
            return check_prog_helper2(body, vars, funs);
        }
        SurfProg::If {
            cond,
            thn,
            els,
            ann,
        } => {
            // okay if cond, then, and else expressions are okay

            /*
            let a = check_prog_helper(cond, vars);
            let b = check_prog_helper(thn, vars);
            let c = check_prog_helper(els, vars);
            if a.unwrap().0.is_err { return a; }
            else if b.unwrap().0.is_error { return b; }
            else if c.unwrap().0.is_error { return c; }
            else { return OK(()); } */

            let subs = vec![cond, thn, els];
            for x in subs {
                let a = check_prog_helper2(x, vars.clone(), funs.clone());
                if a.0.is_err() {
                    return a;
                }
            }
            return (Ok(()), funs);
        }
        SurfProg::Call(fun, args, ann) => {

            match *fun.clone(){
                SurfProg::Var(s, _) => {
                    if (!vars.contains(&s) && !funs.contains(&s)) {
                        return (Err(CompileErr::UnboundVariable {
                            unbound: s.to_string(),
                            location: ann.clone(),
                        }), funs);
                    }
                }
                SurfProg::Lambda { parameters, body, ann } => { panic!("NYI:Check_prog_2 call lambda")}
                _ => { panic!("Check_prog_2 call did not contain a var."); }
            }

            for cur_arg in args {
                let (temp, funs_temp) = check_prog_helper2(cur_arg, vars.clone(), funs);
                funs = funs_temp;
                if temp.is_err() { return (temp, funs); }
            }
            return (Ok(()), funs);
            
        }

        SurfProg::FunDefs { decls, body, ann } => {
            // returns error if DuplicateFunName , DuplicateArgName , 

            for curr_dec in decls{
                let mut para = curr_dec.parameters.clone();
            //    let mut para_clone = curr_dec.parameters.clone();
                while para.len() > 0{//foo(a,b,a)
                    let temp = para.pop().unwrap();
                   // let temp = para_clone.pop().unwrap();
                    if para.contains(&temp) {
                        return (Err(CompileErr::DuplicateArgName { 
                            duplicated_name: temp, 
                            location: ann.clone(), 
                        }), funs);
                    } 
                    vars.insert(temp);
                    
                }
                funs.insert(curr_dec.name.to_string());
                let (temp_error, temp_funs) = check_prog_helper2(&curr_dec.body, vars.clone(), funs);
                funs = temp_funs;
                if (temp_error.is_err()) {
                    return (temp_error, funs);
                }
            }
            return check_prog_helper2(body, vars, funs);
        }
        
        SurfProg::Array(vec, ann) => {
            for curr_exp in vec{
                let result;
                (result, funs) = check_prog_helper2(curr_exp, vars.clone(), funs.clone());
                if (result.is_err()) {return (result, funs);}
            }
            return (Ok(()), funs);
        }
        SurfProg::ArraySet{array, index, new_value, ann} => {
            let mut result;
            (result, funs) = check_prog_helper2(array, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            (result, funs) = check_prog_helper2(index, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            (result, funs) = check_prog_helper2(new_value, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            return (Ok(()), funs);

        }
        SurfProg::Semicolon{e1, e2, ann} => {
            let mut result;
            (result, funs) = check_prog_helper2(e1, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            (result, funs) = check_prog_helper2(e2, vars.clone(), funs.clone());
            if (result.is_err()) {return (result, funs);}
            return (Ok(()), funs);
        }
        SurfProg::Lambda{parameters, body, ann} => {
            //panic!("NYI::Lambda");
            let mut new_vars: HashSet<&String> = HashSet::new();
            for s in parameters {
                if new_vars.contains(s) {
                    return (Err(CompileErr::DuplicateBinding {
                        duplicated_name: s.to_string(),
                        location: ann.clone(),
                    }), funs);
                } else {
                    new_vars.insert(s);
                    vars.insert(s.to_string());
                }
            }
            return check_prog_helper2(body, vars, funs);
        }
        SurfProg::MakeClosure{arity, label, env, ann} => {
            return check_prog_helper2(env, vars, funs);
        }
    }
    
}




pub fn check_prog<Span>(p: &SurfProg<Span>) -> Result<(), CompileErr<Span>>
where
    Span: Clone,
{   
   // println!(); check_prog_helper_prints(p, HashSet::new(), HashSet::new()); println!();
    let (x, fun_list) = check_prog_helper(p, HashSet::new(), HashSet::new());
    if x.is_err() {return x;}
    return check_prog_helper2(p, HashSet::new(), fun_list).0;
}

fn uni_helper(e: &Exp<u32>, mut new_vars: HashMap<String,String>, 
    mut new_funs: HashMap<String,String>, mut count: (usize, usize) )
 -> (Exp<()>, HashMap<String,String>){
    /*
    let x = 2 in
        def asdf(a):
            1
        and wasd(a):
            2
        in wasd(1)+asdf(2)
    
    */
    match e {
        Exp::Num(value, _) => {return (Exp::Num(*value,()), new_funs);},
        Exp::Bool(x, _) => {return (Exp::Bool(*x, ()), new_funs);},
        Exp::Var(s, _) => {
            return (Exp::Var(new_vars.get(s).unwrap().to_string(), ()), new_funs);
        },
        Exp::Prim1(p, e, _) => {
            let mut exp;
            (exp, new_funs) = uni_helper(e, new_vars.clone(), new_funs, count);
            return (Exp::Prim1(*p, Box::new(exp), ()), new_funs);
        },
        Exp::Prim2(p, e1, e2, _) => {
            let mut exp1; let mut exp2;
            (exp1, new_funs) = uni_helper(e1, new_vars.clone(), new_funs, count);
            (exp2, new_funs) = uni_helper(e2, new_vars.clone(), new_funs, count);
            return (Exp::Prim2(*p, Box::new(exp1), Box::new(exp2), ()), new_funs);
        },
        Exp::Let { bindings, body, ann } => {
            let mut new_bindings:Vec<(String, Exp<()>)> = Vec::new();
            let old_vars = new_vars.clone();
            for binding in bindings {
                let mut temp;
                (temp, new_funs) = uni_helper(&binding.1, new_vars.clone(),new_funs, count);
                let new_name = format!("Var_{}", count.0);
                count.0 +=1;
                new_vars.insert(binding.0.to_string(), new_name.to_string());
                new_bindings.push((new_name.to_string(), temp));
            }
            let mut new_body;
            (new_body, new_funs) = uni_helper(body, new_vars.clone(), new_funs, count);
            return (Exp::Let { bindings: new_bindings, body: Box::new(new_body), ann: () }, new_funs);
        },
        Exp::If { cond, thn, els, ann } => {
            let mut c; let mut t; let mut e;
            (c, new_funs) = uni_helper(cond, new_vars.clone(), new_funs, count);
            (t, new_funs) = uni_helper(thn, new_vars.clone(), new_funs, count);
            (e, new_funs) = uni_helper(els, new_vars.clone(), new_funs, count);
            return (Exp::If{cond: Box::new(c), 
                            thn: Box::new(t), 
                            els: Box::new(e),
                            ann: (),}, new_funs);
        }
        
        Exp::FunDefs { decls, body, ann } => {
            let mut new_decls:Vec<FunDecl<Exp<()>, ()>> = Vec::new();
            let old_vars = new_vars.clone();
            for curr_decl in decls{
                // for each function declaration, give the funcion a new name
                let new_func_name = format!("Fun_{}", count.1);
                count.1 += 1;
                new_funs.insert(curr_decl.name.to_string(), new_func_name.to_string());

                // treat each argument like a let statement with no bindings, renaming the argument and adding to new_vars
                // save the new parameters for later Exp::FunDefs
                let mut new_parameters:Vec<String> = Vec::new();
                for curr_parameter in curr_decl.parameters.clone() {
                    let new_parameter_name = format!("Fun_{}_param_{}_previous_param_{}", curr_decl.name.to_string(),count.0, curr_parameter);
                    count.0 +=1;
                    new_vars.insert(curr_parameter, new_parameter_name.to_string());
                    new_parameters.push(new_parameter_name);
                }
                // rename all the varibles inside the body of current declaration
                let temp_exp;
                (temp_exp, new_funs) = uni_helper(&curr_decl.body, new_vars.clone(), new_funs, count);
                new_decls.push(FunDecl { name: new_func_name, parameters: new_parameters, body: temp_exp, ann: () });
            }

            let temp_exp;
            (temp_exp, new_funs) = uni_helper(body, old_vars.clone(), new_funs, count);
            return (Exp::FunDefs{decls: new_decls,
                body: Box::new(temp_exp),
                ann: ()}, new_funs);

        },
        Exp::Call(s, a, _) => {
            let fun_name;
            match *s.clone(){
                Exp::Var(x, _) => {fun_name = Exp::Var(x.to_string(), ());}
                _ => {panic!("uni_helper calling something not var");}
            }

            let mut new_parameters:Vec<Exp<()>> = Vec::new();
            for cur_p in a{
                let renamed_para;
                (renamed_para, new_funs) = uni_helper(cur_p, new_vars.clone(), new_funs, count);
                new_parameters.push(renamed_para);
            }
            return (Exp::Call(Box::new(fun_name), new_parameters, ()), new_funs);
        }
        Exp::Array(vec, ann) => {
            let mut new_vec: Vec<Exp<()>> = Vec::new();
            //let mut new_vars: HashSet<&String> = HashSet::new();

            for curr_exp in vec{
                let mut x;
                x = uni_helper(curr_exp, new_vars.clone(), new_funs, count);
                new_funs = x.1;
                new_vec.push(x.0);

            }
            return ((Exp::Array(new_vec, ())), new_funs);
        }
        Exp::ArraySet{array, index, new_value, ann} => {
            //panic!("nyi:uni_helper arrayset");
            let (new_array, new_index, new_value2);
            (new_array, new_funs) = uni_helper(array, new_vars.clone(), new_funs, count);
            (new_index, new_funs) = uni_helper(index, new_vars.clone(), new_funs, count);
            (new_value2, new_funs) = uni_helper(new_value, new_vars.clone(), new_funs, count);
            return (Exp::ArraySet{ 
                array: Box::new(new_array), 
                index: Box::new(new_index), 
                new_value: Box::new(new_value2), 
                ann: ()}, new_funs);
        }
        Exp::Semicolon{e1, e2, ann} => {
            let (new_e1, new_e2);
            (new_e1, new_funs) = uni_helper(e1, new_vars.clone(), new_funs, count);
            (new_e2, new_funs) = uni_helper(e2, new_vars.clone(), new_funs, count);
            return (Exp::Semicolon { e1: Box::new(new_e1), e2: Box::new(new_e2), ann: (),},new_funs)
        }
        Exp::Lambda{parameters, body, ann} => {
            let mut new_parameters:Vec<String> = Vec::new();
                for curr_parameter in parameters.clone() {
                    let new_parameter_name = format!("Lambda_{}_param_{}", ann, count.0);
                    count.0 +=1;
                    new_vars.insert(curr_parameter, new_parameter_name.to_string());
                    new_parameters.push(new_parameter_name);
                }
            // rename all the varibles inside the body
            let new_body;
            (new_body, new_funs) = uni_helper(&body, new_vars.clone(), new_funs, count);

            return (Exp::Lambda{parameters: new_parameters, body: Box::new(new_body), ann: ()}, new_funs);
        }
        Exp::MakeClosure{arity, label, env, ann} => {
            panic!("MakeClosure in unqi_helper");
        }
    }

}

fn uni_fix_calls(e: &Exp<()>, new_funs: HashMap<String,String>) -> Exp<()>{
    match e {
        Exp::Num(_, _) => return e.clone(),
        Exp::Bool(_, _) => return e.clone(),
        Exp::Var(_, _) => return e.clone(),
        Exp::Prim1(p, exp, _) => { 
            return Exp::Prim1(*p, Box::new(uni_fix_calls(exp, new_funs)), ());
        },
        Exp::Prim2(p, e1, e2, _) => return Exp::Prim2(*p,
                                                    Box::new(uni_fix_calls(e1, new_funs.clone())),
                                                    Box::new(uni_fix_calls(e2, new_funs.clone())), ()),
        Exp::Let { bindings, body, ann } => 
            {
                let mut new_bindings:Vec<(String, Exp<()>)> = Vec::new();
                for curr_binding in bindings{
                    new_bindings.push((curr_binding.0.to_string(), uni_fix_calls(&curr_binding.1, new_funs.clone())));
                }
                return Exp::Let { bindings: new_bindings, 
                                    body: Box::new(uni_fix_calls(body, new_funs)), 
                                    ann: () }
            },

        Exp::If { cond, thn, els, ann } => return Exp::If { 
            cond: Box::new(uni_fix_calls(cond, new_funs.clone())), 
            thn: Box::new(uni_fix_calls(thn, new_funs.clone())), 
            els: Box::new(uni_fix_calls(els, new_funs.clone())), 
            ann: () },

        Exp::FunDefs { decls, body, ann } => {
            let mut new_declarations:Vec<FunDecl<Exp<()>, ()>> = Vec::new();
                for curr_decl in decls{
                    let temp = uni_fix_calls(&curr_decl.body, new_funs.clone());
                    new_declarations.push(FunDecl { 
                        name: curr_decl.name.clone(), 
                        parameters: curr_decl.parameters.clone(), 
                        body: temp, 
                        ann: () });
                }
            return Exp::FunDefs { decls: new_declarations, body: Box::new(uni_fix_calls(body, new_funs.clone())), ann: () };
        },
        Exp::Call(fun, args, _) => {
            let fun_name;
            match *fun.clone(){
                Exp::Var(x, _) => {
                    fun_name = Exp::Var(new_funs.get(&x).unwrap().to_string(), ());
                }
                _ => {panic!("uni_helper_fix_calls calling something not var");}
            }
            let mut new_parameters:Vec<Exp<()>> = Vec::new();
            for cur_p in args{
                let renamed_para = uni_fix_calls(cur_p, new_funs.clone());
                new_parameters.push(renamed_para);
            }
            return Exp::Call(Box::new(fun_name), new_parameters, ());
        }

        Exp::Array(vec, ann) => {
            let mut new_vec: Vec<Exp<()>> = Vec::new();
            //let mut new_vars: HashSet<&String> = HashSet::new();

            for curr_exp in vec{
                let mut x;
                x = uni_fix_calls(curr_exp, new_funs.clone());
                
                new_vec.push(x);

            }
            return Exp::Array(new_vec, ());
        }
        Exp::ArraySet{array, index, new_value, ann} => {
            //panic!("nyi:uni_helper arrayset");
            let (new_array, new_index, new_value2);
            new_array = uni_fix_calls(array, new_funs.clone());
            new_index = uni_fix_calls(index, new_funs.clone());
            new_value2 = uni_fix_calls(new_value, new_funs.clone());
            return Exp::ArraySet{ 
                array: Box::new(new_array), 
                index: Box::new(new_index), 
                new_value: Box::new(new_value2), 
                ann: ()};
        }
        Exp::Semicolon{e1, e2, ann} => {
            let (new_e1, new_e2);
            new_e1 = uni_fix_calls(e1, new_funs.clone());
            new_e2 = uni_fix_calls(e2, new_funs.clone());
            return Exp::Semicolon { e1: Box::new(new_e1), e2: Box::new(new_e2), ann: (),};
        }
        Exp::Lambda{parameters, body, ann} => {
            
            let new_body = uni_fix_calls(&body, new_funs.clone());

            return Exp::Lambda{parameters: parameters.clone(), body: Box::new(new_body), ann: ()};
        }
        Exp::MakeClosure{arity, label, env, ann} => {
            panic!("MakeClosure in unqi_helper");
        }
    }
    
}

fn uniquify(e: &Exp<u32>) -> Exp<()> {
    /*
    let x = 2, y = x in
        let x = 4, z = x + 1 in
            let x = z, z = x in
                x
    turns into
    let var1 = 2, var2 = var1 in
        let var3 = 4, var4 = var3 + 1 in
            let var5 = var4, var6 = var5 in
                var5
    */
    let (a, funs) = uni_helper(e, HashMap::new(), HashMap::new(), (0,0));
    return uni_fix_calls(&a, funs);
}

// Old Tests
#[cfg(test)]
mod check_uniquify_test {
    use super::*;

    #[test]
    fn check_uniquify() {
        let e1 = Exp::<u32>::Let {
            bindings: vec![("x".to_string(), Exp::Num(5, 0))],
            body: Box::new(Exp::Var("x".to_string(), 0)),
            ann: 0,
        };
        let e2 = Exp::Let {
            bindings: vec![("Var_0".to_string(), Exp::Num(5, ()))],
            body: Box::new(Exp::Var("Var_0".to_string(), ())),
            ann: (),
        };
        assert_eq!(uniquify(&e1), e2);
    }
    #[test]
    fn check_uniquify_prim1() {
        let e1 = Exp::<u32>::Let {
            bindings: vec![("x".to_string(), Exp::Num(5, 0))],
            body: Box::new(Exp::Prim1(Prim1::Add1,Box::new(Exp::Var("x".to_string(), 0)),0)),
            ann: 0,
        };
        let e2 = Exp::Let {
            bindings: vec![("Var_0".to_string(), Exp::Num(5, ()))],
            body: Box::new(Exp::Prim1(Prim1::Add1,Box::new(Exp::Var("Var_0".to_string(), ())),())),
            ann: (),
        };
        assert_eq!(uniquify(&e1), e2);
    }

    /*fn check_prog_func_works() {

        let function1 = FunDec{name: "function1", parameters: vec![]};

        let e1 = Exp::<u32>::FunDefs {
            bindings: vec![("x".to_string(), Exp::Num(5, 0))],
            body: Box::new(Exp::Var("x".to_string(), 0)),
            ann: 0,
        };
        let e2 = Exp::Let {
            bindings: vec![("Var_0".to_string(), Exp::Num(5, ()))],
            body: Box::new(Exp::Var("Var_0".to_string(), ())),
            ann: (),
        };
        assert_eq!(uniquify(&e1), e2);
    }*/

    #[test]
    fn check_lambda_lift_sequentialize_works() {



        
        let stupid_span = Span1 {
            start_ix: 0,
            end_ix: 0,
        };
        let var_exp = Exp::Prim1(Prim1::Not, Box::new(Exp::Bool(true, 0)), 0);
        let var_exp2 = Exp::Prim1(Prim1::Not, Box::new(Exp::Bool(true, ())), ());
        let var_exp3 = SeqExp::Prim1(Prim1::Not, ImmExp::Bool(true), ());

        assert_eq!(sequentialize_program(&Vec::new(), &var_exp).main, var_exp3);
    }
}


//1 make hashtable of all variables in outer scope (excluding pre existing parameters)
fn lift_create_hashmap<ann>(p: Exp<ann>, mut env: Vec<String>, mut func_param: HashMap<String, (usize,Vec<String>)>) 
-> HashMap<String, (usize, Vec<String>)> {
    match p{
        Exp::Num(_, _) => return func_param,
        Exp::Bool(_, _) => return func_param,
        Exp::Var(s, _) =>  return func_param,
        Exp::Prim1(_, body, _) =>{
            return lift_create_hashmap(*body, env, func_param);
        },
        Exp::Prim2(_, b1, b2, _) => {
            func_param = lift_create_hashmap(*b1, env.clone(), func_param);
            func_param = lift_create_hashmap(*b2, env.clone(), func_param);
            return func_param;
        },
        Exp::Let { bindings, body, ann } => {
            // let x=2, y=x, z=x ...
            // let x = (def foo(a){a+2} in foo(3))
            for b in bindings{
                func_param = lift_create_hashmap(b.1, env.clone(), func_param);
                env.push(b.0);
            }
            return lift_create_hashmap(*body, env.clone(), func_param);
        },

        Exp::If { cond, thn, els, ann } => {
            func_param = lift_create_hashmap(*cond, env.clone(), func_param);
            func_param = lift_create_hashmap(*thn, env.clone(), func_param);
            return lift_create_hashmap(*els, env.clone(), func_param);
        },
        Exp::FunDefs { decls, body, ann } =>{
            for curr_decl in decls{
                func_param.insert(curr_decl.name, (curr_decl.parameters.len() ,env.clone()));

                let mut env_inner = env.clone();
                env_inner.append(&mut curr_decl.parameters.clone());

                func_param = lift_create_hashmap(curr_decl.body, env_inner.clone(), func_param.clone());
            }
            return lift_create_hashmap(*body, env, func_param);
        },
        Exp::Call(fun, para, _) => {
            for e in para{
                func_param = lift_create_hashmap(e,env.clone(), func_param.clone());
            }
            func_param = lift_create_hashmap(*fun,env.clone(), func_param.clone());
            return func_param;
        },
        Exp::Array(vec, ann) => {
            for v in vec {
                func_param = lift_create_hashmap(v, env.clone(), func_param);
            }
            return func_param;
        }
        Exp::ArraySet{array, index, new_value, ann} => {
            //HashMap<String, (usize, Vec<String>)>
            func_param = lift_create_hashmap(*array, env.clone(), func_param);
            func_param = lift_create_hashmap(*index, env.clone(), func_param);
            func_param = lift_create_hashmap(*new_value, env, func_param);
            return func_param;
        }
        Exp::Semicolon{e1, e2, ann} => {
            func_param = lift_create_hashmap(*e1, env.clone(), func_param);
            func_param = lift_create_hashmap(*e2, env, func_param);
            return func_param;
        }
        Exp::Lambda{parameters, body, ann} => {
            func_param = lift_create_hashmap(*body, env, func_param);
            return func_param;
        }
        Exp::MakeClosure{arity, label, env, ann} => {panic!("Lambda lift 1 found a MakeClosure");}
    } 
}

fn lift_optimize<ann>(p: Exp<ann>, mut func_param: HashMap<String, Vec<String>>) -> HashMap<String, Vec<String>> {
    // Once everything works, remove unused variables
    return func_param;
}

//2 use hashtable to add needed parameters to definitions and calls
/*
fn lift_replace_func_call_old<ann: Clone + std::marker::Copy + std::fmt::Display>(p: Exp<ann>, mut func_param: HashMap<String, Vec<String>>)-> Exp<ann>{
    match p {
        Exp::Num(_, _) => return p,
        Exp::Bool(_, _) => return p,
        Exp::Var(_, _) => return p,
        Exp::Prim1(op, exp1, ann) => {
            return Exp::Prim1(op, Box::new(lift_replace_func_call(*exp1, func_param)), ann);        
        },
        Exp::Prim2(op, exp1, exp2, ann) => {
            return Exp::Prim2(op,
            Box::new(lift_replace_func_call(*exp1, func_param.clone())),
            Box::new(lift_replace_func_call(*exp2, func_param)),
            ann
            );
        },
        Exp::Let { bindings, body, ann } => {
            let mut new_binds = Vec::new();            
            for binding in bindings{
                new_binds.push((binding.0, lift_replace_func_call(binding.1, func_param.clone())));            
            }

            return Exp::Let { 
                bindings: new_binds, 
                body: Box::new(lift_replace_func_call(*body, func_param.clone())), 
                ann: ann }
        },
        Exp::If { cond, thn, els, ann } => {
            let (c,t,e);
            c = Box::new(lift_replace_func_call(*cond, func_param.clone()));
            t = Box::new(lift_replace_func_call(*thn, func_param.clone()));
            e = Box::new(lift_replace_func_call(*els, func_param.clone()));
            return Exp::If { cond: c, thn: t, els: e, ann: ann };
        },
        Exp::FunDefs { decls, body, ann } => {
            let mut new_decls:Vec<FunDecl<Exp<ann>, ann>> =  Vec::new();
            
            for curr_decl in decls{
                
                let mut new_para = curr_decl.parameters.clone();
                
                new_para.append(&mut func_param.get(&curr_decl.name).unwrap().clone());
                let new_decl = FunDecl { 
                    name: curr_decl.name, 
                    parameters: new_para, 
                    body: lift_replace_func_call(curr_decl.body, func_param.clone()), 
                    ann: ann.clone(), 
                };
                
                new_decls.push(new_decl);
            }
            return Exp::FunDefs { 
                decls: new_decls, 
                body: Box::new(lift_replace_func_call(*body, func_param.clone())), 
                ann: ann, 
            }
        },
        Exp::Call(fun, parameters, ann) => {
            panic!("NYI:: Lift part 2 call");
            let mut new_para:Vec<Exp<ann>> = Vec::new();
            /*for p in parameters{
                new_para.push(lift_replace_func_call(p, func_param.clone()));
            }
            for p in func_param.get(&fun).unwrap().clone(){
                new_para.push(Exp::Var(p, ann.clone()));
            }
         //   let tmp = Exp::Var(&mut func_param.get(&fun).unwrap().clone(), ann);
          //  new_para.append();
            return Exp::Call(fun, new_para, ann);*/
            
        },
        Exp::Array(vec, ann) => {panic!("nyi:lift_replace_func_call array");}
        Exp::ArraySet{array, index, new_value, ann} => {panic!("nyi:lift_replace_func_call arrayset");}
        Exp::Semicolon{e1, e2, ann} => {panic!("nyi:lift_replace_func_call Semicolon");}
        Exp::Lambda{parameters, body, ann} => {panic!("NYI:lift_replace_func_call Lambda");}
        Exp::MakeClosure{arity, label, env, ann} => {panic!("NYI:lift_replace_func_call MakeClosure");}
    }
}*/

//3 lift definitions to the top level
fn lift_top_level<ann>(p: Exp<ann>, mut funs: Vec<FunDecl<Exp<()>, ()>>) -> (Vec<FunDecl<Exp<()>, ()>>, Exp<()>) {
    match p {
        Exp::Num(x,_)=> return (funs, Exp::Num(x, ())),
        Exp::Bool(x, _) => return (funs, Exp::Bool(x, ())),
        Exp::Var(x, _) => return (funs, Exp::Var(x, ())),
        Exp::Prim1(p, e, _) => {
            let recursed_e;
            (funs, recursed_e) = lift_top_level(*e, funs);
            return (funs, Exp::Prim1(p,Box::new(recursed_e),()));
        },
        Exp::Prim2(p, e1, e2, _) => {
            let (re1,re2);
            (funs, re1) = lift_top_level(*e1, funs);
            (funs, re2) = lift_top_level(*e2, funs);
            return (funs, Exp::Prim2(p,Box::new(re1),Box::new(re2),()));
        },
        Exp::Let { bindings, body, ann } => {
            let mut recursed_bindings:Vec<(String, Exp<()>)> = Vec::new();
            let recursed_body;
            for b in bindings{
                let tmp;
                (funs, tmp) = lift_top_level(b.1, funs);
                recursed_bindings.push((b.0,tmp));
            }
            (funs, recursed_body) = lift_top_level(*body, funs);
            return (funs, Exp::Let { bindings: recursed_bindings, body: Box::new(recursed_body), ann: () });
        },
        Exp::If { cond, thn, els, ann } => {
            let (c,t,e);
            (funs,c) = lift_top_level(*cond, funs);
            (funs,t) = lift_top_level(*thn, funs);
            (funs,e) = lift_top_level(*els, funs);
            return (funs, Exp::If { cond: Box::new(c), thn: Box::new(t), els: Box::new(e), ann: () });
        },
        Exp::FunDefs { decls, body, ann } => {
            for curr_decl in decls{
                let recursed_body;
                (funs, recursed_body) = lift_top_level(curr_decl.body, funs);
                funs.push(FunDecl { name: curr_decl.name, parameters: curr_decl.parameters, body: recursed_body, ann: () });
            }
            let (funs, tmp) = lift_top_level(*body, funs);
            return (funs, tmp);
            // foo1 and foo2 and foo3 in
                // foo3 and foo4 in
                    // 4
        },

        Exp::Call(fun, args, _) => { panic!("lift_top_level contains call"); },
        Exp::Array(vec, _) => {
            let mut new_vec = Vec::new();
            for v in vec {
                let x;
                (funs, x) = lift_top_level(v, funs);
                new_vec.push(x);
            }
            return (funs, Exp::Array(new_vec, ()));
        }
        Exp::ArraySet{array, index, new_value, ann} => {
            let (funs, recursed_array) = lift_top_level(*array, funs);
            let (funs, recursed_index) = lift_top_level(*index, funs);
            let (funs, recursed_new_value) = lift_top_level(*new_value, funs);
            return (funs, Exp::ArraySet { 
                array: Box::new(recursed_array), 
                index: Box::new(recursed_index), 
                new_value: Box::new(recursed_new_value), 
                ann: () })
        }
        Exp::Semicolon{e1, e2, ann} => {
            let (funs, recursed_e1) = lift_top_level(*e1, funs);
            let (funs, recursed_e2) = lift_top_level(*e2, funs);
            return (funs, Exp::Semicolon { e1: Box::new(recursed_e1), e2: Box::new(recursed_e2), ann: () })
        }
        Exp::Lambda{parameters, body, ann} => {
            let (funs, recursed_body) = lift_top_level(*body, funs);
            return (funs, Exp::Lambda { parameters: parameters, body: Box::new(recursed_body), ann: () })
        }
        Exp::MakeClosure{arity, label, env, ann} => {
            let (funs, recursed_env) = lift_top_level(*env, funs);
            return (funs, Exp::MakeClosure { arity: arity, label: label.to_string(), env: Box::new(recursed_env), ann: ()})
        }
    }
}

//1.1 convert let lambdas to def let lambda
fn lift_convert_lambdas<ann: std::fmt::Display + std::marker::Copy>(e: Exp<ann>) -> Exp<ann> {
    match e {
        Exp::Num(_, _) => return e,
        Exp::Bool(_, _) => return e,
        Exp::Var(_, _) => return e,
        Exp::Prim1(op, exp1, ann) => {
            return Exp::Prim1(op, Box::new(lift_convert_lambdas(*exp1)), ann);        
        },
        Exp::Prim2(op, exp1, exp2, ann) => {
            return Exp::Prim2(op,
            Box::new(lift_convert_lambdas(*exp1)),
            Box::new(lift_convert_lambdas(*exp2)),
            ann
            );
        },
        Exp::Let { bindings, body, ann } => {
            let mut new_binds = Vec::new();            
            for binding in bindings{
                new_binds.push((binding.0, lift_convert_lambdas(binding.1)));            
            }

            return Exp::Let { 
                bindings: new_binds, 
                body: Box::new(lift_convert_lambdas(*body)), 
                ann: ann }
        },
        Exp::If { cond, thn, els, ann } => {
            let (c,t,e);
            c = Box::new(lift_convert_lambdas(*cond));
            t = Box::new(lift_convert_lambdas(*thn));
            e = Box::new(lift_convert_lambdas(*els));
            return Exp::If { cond: c, thn: t, els: e, ann: ann };
        },
        Exp::FunDefs { decls, body, ann } => {
            let mut new_decls:Vec<FunDecl<Exp<ann>, ann>> = Vec::new();
            for d in decls {
                new_decls.push(FunDecl { 
                    name: d.name, 
                    parameters: d.parameters, 
                    body: lift_convert_lambdas(d.body), 
                    ann: d.ann });
            }
            return Exp::FunDefs { decls: new_decls, body: Box::new(lift_convert_lambdas(*body)), ann: ann };
        },
        Exp::Call(fun, parameters, ann) => {
            let new_fun = lift_convert_lambdas(*fun);
            let mut new_para:Vec<Exp<ann>> = Vec::new();
            for p in parameters{
                new_para.push(lift_convert_lambdas(p));
            }
            return Exp::Call(Box::new(new_fun), new_para, ann);
        },
        Exp::Array(vec, ann) => {
            let mut new_e:Vec<Exp<ann>> = Vec::new();
            for p in vec{
                new_e.push(lift_convert_lambdas(p));
            }
            return Exp::Array(new_e, ann);
        }
        Exp::ArraySet{array, index, new_value, ann} => {
            let (a, i, nv);
            a = Box::new(lift_convert_lambdas(*array));
            i = Box::new(lift_convert_lambdas(*index));
            nv = Box::new(lift_convert_lambdas(*new_value));
            return Exp::ArraySet { array: a, index: i, new_value: nv, ann: ann };
        }
        Exp::Semicolon{e1, e2, ann} => {
            let (r1, r2);
            r1 = Box::new(lift_convert_lambdas(*e1));
            r2 = Box::new(lift_convert_lambdas(*e2));
            return Exp::Semicolon { e1: r1, e2: r2, ann: ann };
        }
        //1.1 convert let lambdas to let def
        // (lambda x: x + 1 end) -> def lambda_1(x): x + 1 in lambda_1
        Exp::Lambda{parameters, body, ann} => {
            let name = format!("Lambda{}_({})", ann, parameters.join(", "));
            let new_decl = FunDecl { 
                name: name.to_string(), 
                parameters: parameters, 
                body: Exp::Var(name.clone(), ann), 
                ann: ann
            };
            return Exp::FunDefs { decls: vec![new_decl], body: Box::new(lift_convert_lambdas(*body)), ann: ann };
        }
        Exp::MakeClosure{arity, label, env, ann} => {
        return Exp::MakeClosure { arity: arity, label: label, env: Box::new(lift_convert_lambdas(*env)), ann: ann };
        }
    }
    panic!("lift 1.1 failed to return inside match");
    return e;
}

//1.2 replace def(params) {body} with def(env_array, params) {let env1=env_aray[1], env2 ... in body}
fn lift_replace_def_params<ann: std::marker::Copy>(e: Exp<ann>, func_param: HashMap<String, (usize, Vec<String>)> ) -> Exp<ann> {
    match e {
        Exp::Num(_, _) => return e,
        Exp::Bool(_, _) => return e,
        Exp::Var(_, _) => return e,
        Exp::Prim1(op, exp1, ann) => {
            return Exp::Prim1(op, Box::new(lift_replace_def_params(*exp1, func_param)), ann);        
        },
        Exp::Prim2(op, exp1, exp2, ann) => {
            return Exp::Prim2(op,
            Box::new(lift_replace_def_params(*exp1, func_param.clone())),
            Box::new(lift_replace_def_params(*exp2, func_param.clone())),
            ann
            );
        },
        Exp::Let { bindings, body, ann } => {
            let mut new_binds = Vec::new();            
            for binding in bindings{
                new_binds.push((binding.0, lift_replace_def_params(binding.1, func_param.clone())));            
            }

            return Exp::Let { 
                bindings: new_binds, 
                body: Box::new(lift_replace_def_params(*body, func_param)), 
                ann: ann }
        },
        Exp::If { cond, thn, els, ann } => {
            let (c,t,e);
            c = Box::new(lift_replace_def_params(*cond, func_param.clone()));
            t = Box::new(lift_replace_def_params(*thn, func_param.clone()));
            e = Box::new(lift_replace_def_params(*els, func_param.clone()));
            return Exp::If { cond: c, thn: t, els: e, ann: ann };
        },
        Exp::FunDefs { decls, body, ann } => {
            let mut new_decls:Vec<FunDecl<Exp<ann>, ann>> = Vec::new();
            for d in decls {
                let old_body = lift_replace_def_params(d.body, func_param.clone());
                let mut bindings = Vec::new();
                let env = &func_param.get(&d.name.to_string()).unwrap().1; // env = [x1,x2,x3,f,g]

                let array_name = "env".to_string();
                                
                let mut i = 0 as i64;
                for curr_param in env{

                    let new_binding = (curr_param.to_string(), Exp::Prim2(
                        Prim2::ArrayGet, 
                        Box::new(Exp::Var(array_name.to_string(), ann)), 
                        Box::new(Exp::Num(i, ann)), 
                        ann));
                    i +=1;
                    bindings.push(new_binding);
                }

                let new_body = Exp::Let { bindings: bindings, body: Box::new(old_body), ann: ann };

                let mut parameters = Vec::new(); // array_name + d.param
                parameters.push(array_name.to_string());
                parameters.append(&mut d.parameters.clone());

                new_decls.push(FunDecl { 
                    name: d.name, 
                    parameters: parameters, 
                    body: new_body, 
                    ann: d.ann });
            }
            return Exp::FunDefs { decls: new_decls, body: Box::new(lift_replace_def_params(*body, func_param)), ann: ann };
        },
        Exp::Call(fun, parameters, ann) => {
            let new_fun = lift_replace_def_params(*fun, func_param.clone());
            let mut new_para:Vec<Exp<ann>> = Vec::new();
            for p in parameters{
                new_para.push(lift_replace_def_params(p, func_param.clone()));
            }
            return Exp::Call(Box::new(new_fun), new_para, ann);
        },
        Exp::Array(vec, ann) => {
            let mut new_e:Vec<Exp<ann>> = Vec::new();
            for p in vec{
                new_e.push(lift_replace_def_params(p, func_param.clone()));
            }
            return Exp::Array(new_e, ann);
        }
        Exp::ArraySet{array, index, new_value, ann} => {
            let (a, i, nv);
            a = Box::new(lift_replace_def_params(*array, func_param.clone()));
            i = Box::new(lift_replace_def_params(*index, func_param.clone()));
            nv = Box::new(lift_replace_def_params(*new_value, func_param.clone()));
            return Exp::ArraySet { array: a, index: i, new_value: nv, ann: ann };
        }
        Exp::Semicolon{e1, e2, ann} => {
            let (r1, r2);
            r1 = Box::new(lift_replace_def_params(*e1, func_param.clone()));
            r2 = Box::new(lift_replace_def_params(*e2, func_param.clone()));
            return Exp::Semicolon { e1: r1, e2: r2, ann: ann };
        }
        //1.1 convert let lambdas to let def
        // (lambda x: x + 1 end) -> def lambda_1(x): x + 1 in lambda_1
        Exp::Lambda{parameters, body, ann} => {
            panic!("lambda_lift 1.2 found a lambda");
            return e;
        }
        Exp::MakeClosure{arity, label, env, ann} => {
            return Exp::MakeClosure { arity: arity, label: label, env: Box::new(lift_replace_def_params(*env, func_param)), ann: ann };
        }
    }
    panic!("lift 1.2 failed to return inside match");
    return e;
}

//2 use hashtable to create MakeClosures
fn lift_replace_func_call<ann: Clone + std::marker::Copy + std::fmt::Display>
(p: Exp<ann>, mut func_param: HashMap<String, (usize, Vec<String>)>) -> Exp<ann>{
    match p {
        Exp::Num(_, _) => return p,
        Exp::Bool(_, _) => return p,
        Exp::Var(_, _) => return p,
        Exp::Prim1(op, exp1, ann) => {
            return Exp::Prim1(op, Box::new(lift_replace_func_call(*exp1, func_param)), ann);        
        },
        Exp::Prim2(op, exp1, exp2, ann) => {
            return Exp::Prim2(op,
            Box::new(lift_replace_func_call(*exp1, func_param.clone())),
            Box::new(lift_replace_func_call(*exp2, func_param)),
            ann
            );
        },
        Exp::Let { bindings, body, ann } => {
            let mut new_binds = Vec::new();            
            for binding in bindings{
                new_binds.push((binding.0, lift_replace_func_call(binding.1, func_param.clone())));            
            }

            return Exp::Let { 
                bindings: new_binds, 
                body: Box::new(lift_replace_func_call(*body, func_param.clone())), 
                ann: ann }
        },
        Exp::If { cond, thn, els, ann } => {
            let (c,t,e);
            c = Box::new(lift_replace_func_call(*cond, func_param.clone()));
            t = Box::new(lift_replace_func_call(*thn, func_param.clone()));
            e = Box::new(lift_replace_func_call(*els, func_param.clone()));
            return Exp::If { cond: c, thn: t, els: e, ann: ann };
        },
        Exp::FunDefs { decls, body, ann } => {
            let mut new_decls:Vec<FunDecl<Exp<ann>, ann>> =  Vec::new();
            
            for curr_decl in decls{
                
                let mut new_para = curr_decl.parameters.clone();
                
                let new_decl = FunDecl { 
                    name: curr_decl.name, 
                    parameters: new_para, 
                    body: lift_replace_func_call(curr_decl.body, func_param.clone()), 
                    ann: ann.clone(), 
                };
                
                new_decls.push(new_decl);
            }
            return Exp::FunDefs { 
                decls: new_decls, 
                body: Box::new(lift_replace_func_call(*body, func_param.clone())), 
                ann: ann, 
            }
        },
            /*
            for each call, insert a let with env_arr array containing all vars (env) + empty space for functions
                                        each function name = make_closure(fun.parameters.len(), fun.name, env_arr)
                then mutate the empty array values to be the created closures
                then semicolon call

            */
        Exp::Call(fun, parameters, ann) => {
            let mut fun_name;
            
            match *fun.clone() {
                Exp::Var(s, _) => {fun_name = s;},
                _ => {panic!();}
            }
            let mut let_bindings:Vec<(String, Exp<ann>)> = Vec::new();
            
            let env = &func_param.get(&fun_name).unwrap().1; // env = [x1,x2,x3,f,g]
            // func_param = [ (f, [x1,x2,x3,f,g]), (g, [x1,x2,x3,f,g])]
            // want env (env.len() - func_param.len() , env.len() -1)
            // want env[]
            let funs_list = &env[(env.len() - func_param.len())..] ; //[f,g] 

            // length = (all the vars in env) + (number of total functions)
            // array = func_param.get(fun) + func_param.len()

            // 
            let mut array_stuff = Vec::new();
            for x in env.clone() {
                array_stuff.push(Exp::Var(x.to_string(), ann.clone()));
            }

            let array_name = format!("Array_{}", ann); // IDK if this should be unique, and idk how to make it unique
            
            // create array in let statement
            let array = Exp::Array(array_stuff, ann.clone());
            let_bindings.push((array_name.clone(), array.clone()));

            // for each function add a let binding (fun_name = make_closure)
            for f in funs_list.clone() {
                let arity = func_param.get(&f.to_string()).unwrap().0; 
                let_bindings.push((f.clone(), Exp::MakeClosure { 
                    arity: arity,
                    label: f.clone(), 
                    env: Box::new(array.clone()), 
                    ann: ann.clone() }));
            }

            // fix parameters to include array
            let old_call = Box::new(Exp::Call(fun, parameters, ann.clone()));
            let mut new_body = old_call;


            // env = [x1, x2, x3, 0, 0],
            // func_param = hashmap [ (f, [x1,x2,x3,f,g]), (g, [x1,x2,x3,f,g])]
            // want to replace f and g with closures
            // 

            // overwrite the empty spaces in array with created make_closures
            let mut i = (env.len() - funs_list.len()) as i64;
            for f in funs_list {
                new_body = Box::new(Exp::Semicolon { 
                    e1: Box::new(Exp::ArraySet { 
                        array: Box::new(Exp::Var(array_name.to_string(), ann.clone())), 
                        index: Box::new(Exp::Num(i, ann.clone())), 
                        new_value: Box::new(Exp::Var(f.to_string(), ann.clone())), 
                        ann: ann.clone() 
                    }), 
                    e2: new_body, 
                    ann: ann.clone() 
                });
                i += 1;
            }
            return Exp::Let { bindings: let_bindings, body: new_body, ann: ann };
        },
        Exp::Array(vec, ann) => {
            let mut new_e:Vec<Exp<ann>> = Vec::new();
            for p in vec{
                new_e.push(lift_replace_func_call(p, func_param.clone()));
            }
            return Exp::Array(new_e, ann);
        }
        Exp::ArraySet{array, index, new_value, ann} => {
            let (a, i, nv);
            a = Box::new(lift_replace_func_call(*array, func_param.clone()));
            i = Box::new(lift_replace_func_call(*index, func_param.clone()));
            nv = Box::new(lift_replace_func_call(*new_value, func_param.clone()));
            return Exp::ArraySet { array: a, index: i, new_value: nv, ann: ann };
        }
        Exp::Semicolon{e1, e2, ann} => {
            let (r1, r2);
            r1 = Box::new(lift_replace_func_call(*e1, func_param.clone()));
            r2 = Box::new(lift_replace_func_call(*e2, func_param.clone()));
            return Exp::Semicolon { e1: r1, e2: r2, ann: ann };
        }
        Exp::Lambda{parameters, body, ann} => {
            panic!("lift part 1 failed to remove all lambdas");
            let name = format!("Lambda_({})", parameters.join(", "));
            let new_decl = FunDecl { 
                name: name, 
                parameters: parameters, 
                body: Exp::Var(name, ann), 
                ann: ann 
            };
            return Exp::FunDefs { decls: vec![new_decl], body: body, ann: ann };
        }
        Exp::MakeClosure{arity, label, env, ann} => {
            return Exp::MakeClosure { 
                arity: arity, label: label, 
                env: Box::new(lift_convert_lambdas(*env)), 
                ann: ann };
            }
    }
}

// Precondition: all names are uniquified
fn lambda_lift<Ann: Clone + std::marker::Copy + std::fmt::Display>(p: &Exp<Ann>) -> (Vec<FunDecl<Exp<()>, ()>>, Exp<()>) {

    // calls don't change anymore 
    // turn all lambdas into defs
    
    // move all the defs to the top level

    //1 make hashmap linking each function with all variables in further out scope
    let mut fun_env = lift_create_hashmap(p.clone(), Vec::new(), HashMap::new());

    // 1.1 turn lambdas into functions
    // e.g. let x = (lambda x: x + 1 end) in 42 
    //   -> let x = def lambda_0(x): x+1 in lambda_0 in 42
    // also create a list of function names
    let mut e;
    e = lift_convert_lambdas(p.clone());
    // recreate function environment to include the functions converted from lambdas
    fun_env = lift_create_hashmap(e.clone(), Vec::new(), HashMap::new());

    // append ordered list of every function to each value in fun_Env
    let mut vector_of_functions = Vec::new();
    for fun in fun_env.clone(){
        vector_of_functions.push(fun.0);
    }
    let mut newmap = HashMap::new();
    for fun in fun_env{
        let mut tmp = fun.1.1;
        tmp.append(&mut vector_of_functions.clone());
        newmap.insert(fun.0, (fun.1.0, tmp));
    }
    let fun_env = newmap;

    // 1.2 replace def(params) {body} with def(env_array, params) {let env1=env_aray[1], env2 ... in body}
    e = lift_replace_def_params(e.clone(), fun_env.clone());

  /*  if (false) {
        println!("func_param contains:");
        for x in func_param.clone(){
            let mut args_vec_string = "".to_string();
            for a in x.1{
                args_vec_string = format!("{}, {}", a, args_vec_string);
            }        
            println!(function:{}, possible outer varibles:{}", x.0, args_vec_string);}
    }// */
    //1.5 optimize
   // fun_env = lift_optimize(e.clone(), fun_env);

    //2 DO NOT use hashtable to add needed parameters to definitions and calls
    //2 use hashtable to create MakeClosures
    /*
        for each call, insert a let with env_arr array containing all vars (env) + empty space for functions
                                    each function name = make_closure(fun.parameters.len(), fun.name, env_arr)
                        then mutate the empty array values to be the created closures
    */
    let x = lift_replace_func_call(p.clone(), fun_env);

    //3 lift definitions to the top level
    return lift_top_level(x, Vec::new());
}

#[cfg(test)]
mod check_lambda_lift_test {
    use super::*;

    /*
    #[test]
    fn check_simple_nest_works() {
        let stupid_span = Span1 {
            start_ix: 0,
            end_ix: 0,
        };
        
        let s = stupid_span;
        let foo3body = Exp::Prim2(Prim2::Add, Box::new(Exp::Var("c".to_string(), s)), Box::new(Exp::Var("b".to_string(), s)), s);
        let foo3 = FunDecl{name: "foo3".to_string(), parameters: vec!["c".to_string()], body: foo3body, ann: stupid_span } ;

        let foo1body = Exp::Prim2(Prim2::Add, Box::new(Exp::Var("a".to_string(), s)), Box::new(Exp::Var("x".to_string(), s)), s);
        let foo1 = FunDecl{name: "foo1".to_string(), parameters: vec!["a".to_string()], body: foo1body, ann: stupid_span } ;

        let callfoo3 = Exp::Call("foo3".to_string(), vec![Exp::Var("b".to_string(), stupid_span)], stupid_span);
        let foo2_body = Exp::FunDefs { decls: vec![foo3], body: Box::new(callfoo3), ann: s };

        let foo2 = FunDecl{name: "foo2".to_string(), parameters: vec!["b".to_string()], body: foo2_body, ann: stupid_span};

        let callfoo1 = Exp::Call("foo1".to_string(), vec![Exp::Var("x".to_string(), stupid_span)], stupid_span);
        let funs = Exp::FunDefs { decls: vec![foo1, foo2], body: Box::new(callfoo1), ann: s };
        

        let bindings = vec![("x".to_string(), Exp::Num(2, stupid_span))];
        
        let exp1 = Exp::Let { 
            bindings: bindings,
            body: Box::new(funs), 
            ann: stupid_span 
        };

        let s = ();
       // let stupid_span = ();
        
        //let x = 2 in foo1(x, x)
        //vec![foo1(a,x){a+x}, foo2(b,x){foo3(b,x,b)}, foo3(c,x,b){c+b}}]

        let bindings = vec![("x".to_string(), Exp::Num(2, s))];
        let callfoo1 = Exp::Call("foo1".to_string(), vec![Exp::Var("x".to_string(), s),Exp::Var("x".to_string(), s)], s);
        let exp = Exp::Let { bindings: bindings, body: Box::new(callfoo1), ann: s };
        //        Exp::Let { bindings: recursed_bindings, body: Box::new(recursed_body), ann: () }

        let new_foo1 = FunDecl{name: "foo1".to_string(), 
        parameters: vec!["a".to_string(), "x".to_string()], 
        body: Exp::Prim2(Prim2::Add, Box::new(Exp::Var("a".to_string(), s)), Box::new(Exp::Var("x".to_string(), s)), s), 
        ann: s 
        };

        //foo3(b,x,b)
        let new_foo2_body_call = Exp::Call(
            "foo3".to_string(), 
            vec![Exp::Var("b".to_string(),s),
            Exp::Var("x".to_string(),s),Exp::Var("b".to_string(),s)], 
            s);
        
        let new_foo2 = FunDecl{name: "foo2".to_string(), 
        parameters: vec!["b".to_string(), "x".to_string()], 
        body: new_foo2_body_call,
        ann: s 
        };

        let new_foo3 = FunDecl{name: "foo3".to_string(), 
        parameters: vec!["c".to_string(), "x".to_string(), "b".to_string()], 
        body: Exp::Prim2(Prim2::Add, Box::new(Exp::Var("c".to_string(), s)), Box::new(Exp::Var("b".to_string(), s)), s), 
        ann: s 
        };


        let defs_vector = vec![new_foo1, new_foo2, new_foo3];
        //assert_eq!(defs_vector, lambda_lift(&exp1).0);
        assert_eq!(defs_vector,lambda_lift(&exp1).0);
        //Vec<FunDecl<Exp<()>, ()>>, Exp<()>


        /* 
        let x = 2 in
            def foo1(a):
                a + x
            and
            def foo2(b):
                def foo3(c):
                    c + b
                in
                foo3(b)
        in foo1(x)

        let x = 2 in
            def foo1(a):
                a + x
            and
            def foo2(b):
                def foo3(c):
                    c + b
                in
                foo3(b)
        in foo1(x)
*/
    }*/
}

fn tag_exp<Ann>(p: &SurfProg<Ann>) -> SurfProg<u32> {
    let mut i = 0;
    p.map_ann(
        &mut (|_| {
            let cur = i;
            i += 1;
            cur
        }),
    )
}

fn tag_prog<Ann>(
    defs: &[FunDecl<Exp<Ann>, Ann>],
    main: &Exp<Ann>,
) -> (Vec<FunDecl<Exp<u32>, u32>>, Exp<u32>) {
    let mut i = 0;
    (
        defs.iter()
            .map(|decl| {
                decl.map_ann(
                    &mut (|_| {
                        let cur = i;
                        i += 1;
                        cur
                    }),
                )
            })
            .collect(),
        main.map_ann(
            &mut (|_| {
                let cur = i;
                i += 1;
                cur
            }),
        ),
    )
}

fn tag_sprog<Ann>(p: &SeqProg<Ann>) -> SeqProg<u32> {
    let mut i = 0;
    p.map_ann(
        &mut (|_| {
            let cur = i;
            i += 1;
            cur
        }),
    )
}


// if e is an immediate, return it as a immediate. Else, return none
fn return_seq_immediate(e: &Exp<u32>) -> Option<SeqExp<()>> {
    match e {
        Exp::Num(n, ann) => {
            return Some(SeqExp::Imm(ImmExp::Num(*n),()));
        },
        Exp::Var(s, ann) => {
            return Some(SeqExp::Imm(ImmExp::Var(s.to_string()),()));
        },
        Exp::Bool(b, ann) => {
            return Some(SeqExp::Imm(ImmExp::Bool(*b),()));
        },

        _ =>  None,

    }
}

fn return_immediate(e: &Exp<u32>) -> Option<ImmExp> {
    match e {
        Exp::Num(n, ann) => {
            return Some(ImmExp::Num(*n));
        },
        Exp::Var(s, ann) => {
            return Some(ImmExp::Var(s.to_string()));
        },
        Exp::Bool(b, ann) => {
            return Some(ImmExp::Bool(*b));
        }
        _ => None,
    }
}

fn generate_identifier(ann: &u32) -> String {
    return format!("bleh{}", ann);
}

fn sequentialize_helper(e: &Exp<u32>) -> SeqExp<()> {
    match e {
        Exp::Bool(_b, _ann) => {
            return return_seq_immediate(e).unwrap();
        }

        Exp::Num(_n, _ann) => {
            return return_seq_immediate(e).unwrap();
        }
        Exp::Var(_s, _ann) => {
            return return_seq_immediate(e).unwrap();
        }

        // sub1(5) -> sub1(5)
        // sub1(add1(5)) -> let x = add1(5) in sub1(x)
        Exp::Prim1(p, sub, ann) => {
            //if sub immediate
            let variable_or_number_bool = return_immediate(sub);
            if variable_or_number_bool != None {
                return SeqExp::Prim1(*p, variable_or_number_bool.unwrap(), ());
            } else {
                // add1(1+2) => let x = (1+2) in add1(x)
                //let "x1" = 2 in "1"

                let new_var = generate_identifier(&ann);
                return SeqExp::Let{
                    var: new_var.clone(),
                    bound_exp: Box::new(sequentialize_helper(&sub)),
                    body: Box::new(SeqExp::Prim1(*p, ImmExp::Var(new_var.clone()), ())),
                    ann: ()
                };
            }
        }

        // let x =2, y= 3 in exp -> let x=2 in let y =3 in seqexp
        // let x = 1 in exp - > let x = 1 in seqexp
        Exp::Let {
            bindings,
            body,
            ann,
        } => {
            //exp:let x=2 in 3 -> seq:let
            if bindings.len() < 2 {
                return SeqExp::Let{
                    var: bindings[0].0.clone(),//x
                    bound_exp: Box::new(sequentialize_helper(&bindings[0].1)),
                    body: Box::new(sequentialize_helper(body)),
                    ann: (),
                }
            }
            else{
            // exp:let x=2,y=3,z=4 in exp(2)
            // exp:let(<(x,2),(y=3),(z=4)>, exp(2), ann)
            
            // seq:let z=4 in (exp:let x=2, y=3 in exp(2))
            // seq:let(z,4,recurse(exp:let(<(x,2),(y=3)>, exp(2), ann)))


            // seq:let z=4 in seq:let y=3 in exp(exp:let x=2 in exp(2))
            // seq:let z=4 in seq:let y=3 in seq:let x=2 in exp(2)
            // seq:let z=4 in seq:let y=3 in seq:let x=2 in seqexp(2)
                let mut new_bindings = bindings.clone();
                let popped_var = new_bindings.remove(0);
                let body_clone = body.clone();
                let inner_body_converted = Exp::Let {
                    bindings: new_bindings, 
                    body: body_clone, 
                    ann: *ann 
                };

                return  SeqExp::Let{
                    var: popped_var.0,
                    bound_exp: Box::new(sequentialize_helper(&popped_var.1)),
                    body: Box::new(sequentialize_helper(&inner_body_converted)),
                    ann: ()
                };   
            }            
        }
        Exp::If {
            cond,
            thn,
            els,
            ann,
        } => {
            let imm_cond = return_immediate(cond);
            if imm_cond != None {
                return SeqExp::If{
                    cond: imm_cond.unwrap(),
                    thn: Box::new(sequentialize_helper(thn)),
                    els: Box::new(sequentialize_helper(els)),
                    ann: (),
                }
            } else {
                // if add(2,3) then 6 else 7
                // let bleh# = add(2,3) in if bleh# then thn else els
                let single_var = (generate_identifier(&ann));
                let singular_binding = vec![(single_var.clone(), cond)];
                
                let single_var_exp = Box::new(Exp::Var(single_var.clone(), *ann));
                let cond_clone = cond.clone();
                let thn_clone = thn.clone();
                let els_clone = els.clone();

                
                
                return sequentialize_helper(
                    &Exp::Let{
                         bindings: vec![(single_var, *cond_clone)], 
                         body: Box::new(Exp::If{ cond: single_var_exp, thn: thn_clone, els: els_clone, ann: *ann }),
                         ann: *ann });

            }

            
        }
        
        // 2 - 3

        // let x1 = 2 in let x2 = 3 in x1 - x2

        // (2-3) + (4 * 5)

        // plus(sub(2,3),mul(4,5))

        // let first = 2 - 3 in
        // let second = 4 * 5 in
        // first + second
        Exp::Prim2(p, sub1, sub2, ann) => {
            //create 2 new variable named count from sub1, sub2
            //return let var1=sequentialize_helper(sub1) in let var2=sequentialize_helper(sub2) in Prim2(p,var1,var2,ann)
            // (sub1) + (sub2) - >
            // 2 + 3  ->  let x=2 in let y=3 in add(x,y)
            /*let var1 = format!(count);
            count+=1;
            let var2 = format!(count);
            count+=1;

            return SeqExp::Let{var: var1, bound_exp: sequentialize_helper(sub1),
                body: SeqExp::Let{var: var2, bound_exp: sequentialize_helper(sub2),
                    body: SeqExp::Prim2(p, var1, var2, ann), ann},
                ann: };

            // add(1, sub1(x)) -> let bleh# = sub1(x) in add(1,bleh#)
            */

            let sub1_immediate_result1 = return_immediate(sub1);
            let sub2_immediate_result2 = return_immediate(sub2);

            if sub1_immediate_result1 != None && sub2_immediate_result2 != None {
                return SeqExp::Prim2(
                    *p,
                    sub1_immediate_result1.unwrap(),
                    sub2_immediate_result2.unwrap(),
                    (),
                );
            } else if sub1_immediate_result1 != None {
                let var2 = generate_identifier(ann);
                return SeqExp::Let{
                    var: var2.clone(),
                    bound_exp: Box::new(sequentialize_helper(sub2)),
                    body: Box::new(SeqExp::Prim2(*p, sub1_immediate_result1.unwrap(), ImmExp::Var(var2), ())),
                    ann:(),
                };
            } else if sub2_immediate_result2 != None {
                let var1 = generate_identifier(ann);
                return SeqExp::Let {
                    var: var1.clone(),
                    bound_exp: Box::new(sequentialize_helper(sub1)),
                    body: Box::new(SeqExp::Prim2(*p, ImmExp::Var(var1.clone()), sub2_immediate_result2.unwrap(), ())),
                    ann: (),
                };
            } else {
                // add(add1(x), sub1(x)) -> let bleh1 = add1(x) in let bleh2 = sub1(x) in add(bleh1,bleh2)

                let var1 = generate_identifier(ann);
                let var2 = format!("{}_prim2_second_var",generate_identifier(ann));

                return SeqExp::Let {
                    var: var1.clone(),
                    bound_exp: Box::new(sequentialize_helper(sub1)),
                    body: Box::new(SeqExp::Let{
                        var: var2.clone(),
                        bound_exp: Box::new(sequentialize_helper(sub2)),
                        body: Box::new(SeqExp::Prim2(*p, ImmExp::Var(var1.clone()), ImmExp::Var(var2.clone()), ())),
                        ann:(),
                    }),
                    ann: (),
                };
            }
        }
        Exp::FunDefs { decls, body, ann } => {panic!("Tried to sequentialize a function definition")},

        Exp::Call(s, parameters, ann) => {
          //  panic!("NYI: call sequentialize_helper");
            
            /* check if all parameters are  immediate
             if they are all immediate, return seq::call(s, )


            foo(1, true, x+2) -> let bleh_* = (x+2) in foo(1,true,bleh_*)
                              -> let bleh_1 = 1 in let bleh2 = true in let bleh3 = x+2 in foo(bleh1,bleh2,bleh3)

            foo2(2)     -> let bleh = 2 in foo2(bleh)
            */
            
            
            /*if parameters.len() == 0 {
                return SeqExp::CallClosure{fun: fun_to_call,args: Vec::new(),ann: ()};
            }*/

            let mut new_para:Vec<ImmExp> = Vec::new();
            let mut new_para_s:Vec<String> = Vec::new();

            for p in parameters{
                let tmp = generate_identifier(&p.ann());
                new_para.push(ImmExp::Var(tmp.to_string()));
                new_para_s.push(tmp.to_string());
            }
            
            //def a() 1 and def b() 2 in (if x a else b)()
            //                          let fun_name_replacement = if x a else b in fun_name_replacement()

            let fun_name = format!("fun_name_replacement_{}", ann);
            let mut out = SeqExp::Let{
                var: fun_name.to_string(),
                bound_exp: Box::new(sequentialize_helper(s)),
                body: Box::new(SeqExp::CallClosure{
                    fun: ImmExp::Var(fun_name),
                    args: new_para,
                    ann: ()}),
                ann: (),
            };
            
            // out = foo1(bleh1, bleh2, bleh3)
            // original parameters = a,b,c
            // bleh3 = c, bleh2 = b, bleh1=a

            let mut i = parameters.len();

            // foo(a,b,c) => let bleh1 = a in let bleh2 = b in let bleh3 = c in foo(bleh1,bleh2,bleh3)

            /*
            before the loop:
            new_para_s = <bleh1,bleh2,bleh3>
            parameters = <a, b, c>
            pass 0: out = foo(bleh1,bleh2,bleh3)

            loop:
            pass 1: out = let bleh3 = c in foo(bleh1,bleh2,bleh3)
            pass 2: out = let bleh2 = b in let bleh3 = c in foo(bleh1,bleh2,bleh3)
            pass 3: out = let bleh1 = a in let bleh2 = b in let bleh3 = c in foo(bleh1,bleh2,bleh3)
            */

            while i > 0{
                i = i - 1;
                out = SeqExp::Let { 
                    var: new_para_s.get(i).unwrap().to_string(), 
                    bound_exp: Box::new(sequentialize_helper((parameters.get(i).unwrap()))), 
                    body: Box::new(out), 
                    ann: () 
                };
            }

            return out;
        }
        Exp::Array(vec, ann) => {
            //let mut new_vec = Vec::new();
            let mut i = 0;
            let mut all_are_imm = true;
            let mut imm_exp_vec = Vec::new();
            let mut exp_let_vec = Vec::new();
            let mut imm_vec = Vec::new();
            for curr_exp in vec{
                let curr_exp_is_imm = return_immediate(curr_exp).is_some();
            
                // array[1,x,add1(2),3] => let potato = add1(2) in array[1,x,potato,3]
                // array[1,x] => let in array[1,x]
                // array[1,x,add1(2),3] => let a1 = 1, a2 = x, a3 = add1(2), a4 = 3 in array[a1,a2,a3,a4]
                
                if (!curr_exp_is_imm) {
                    all_are_imm = false;
                    let name = format!("CreateArray_{}_param_{}", ann, i);
                    exp_let_vec.push((name.to_string(), curr_exp.clone()));
                    imm_exp_vec.push(Exp::Var(name.clone(), *ann));
                } else {
                    imm_exp_vec.push(curr_exp.clone());
                    imm_vec.push(return_immediate(curr_exp).unwrap()); // only used if all values are immediates
                }
                i += 1;
            }
            if all_are_imm {
                return SeqExp::Array(imm_vec, ());
            } else {
                return sequentialize_helper(&Exp::Let{
                    bindings: exp_let_vec,
                    body: Box::new(Exp::Array(imm_exp_vec, *ann)),
                    ann: *ann,
                })
            }
        }
        Exp::ArraySet{array, index, new_value, ann} => {

            let index_is_imm = return_immediate(index).is_some();
            let new_value_is_imm = return_immediate(new_value).is_some();
            let array_is_imm = return_immediate(array).is_some();
            let (new_index, new_value2, new_array): (Exp<u32>, Exp<u32>, Exp<u32>);

            if (index_is_imm && new_value_is_imm && array_is_imm) {
                return SeqExp::ArraySet { 
                    array: return_immediate(array).unwrap(), 
                    index: return_immediate(index).unwrap(), 
                    new_value: return_immediate(new_value).unwrap(), 
                    ann: () 
                }  
            }
            let mut let_bindings = Vec::new();

            if (!index_is_imm) {
                let name = format!("SeqExp_Arrayset_index_{}", ann);
                let_bindings.push((name.to_string(), *index.clone()));
                new_index = Exp::Var(name, *ann);
            } else {
                new_index = *index.clone();
            }
            if (!new_value_is_imm) {
                let name = format!("SeqExp_Arrayset_newval_{}", ann);
                let_bindings.push((name.to_string(), *new_value.clone()));
                new_value2 = Exp::Var(name, *ann);
            } else {
                new_value2 = *new_value.clone();
            }
            if (!array_is_imm) {
                let name = format!("SeqExp_Arrayset_array_{}", ann);
                let_bindings.push((name.to_string(), *array.clone()));
                new_array = Exp::Var(name, *ann);
            } else {
                new_array = *array.clone();
            }
            return sequentialize_helper(&Exp::Let { 
                bindings: let_bindings, 
                body: Box::new(Exp::ArraySet { 
                    array: Box::new(new_array),
                    index: Box::new(new_index), 
                    new_value: Box::new(new_value2), 
                    ann: *ann }), 
                ann: *ann });
        }
        Exp::Semicolon{e1, e2, ann} => {
            return SeqExp::Let { 
                var: format!("disposable_{}", ann).to_string(),
                bound_exp: Box::new(sequentialize_helper(e1)), 
                body: Box::new(sequentialize_helper(e2)), 
                ann: () 
            };
        }
        Exp::Lambda{parameters, body, ann} => {panic!("Tried to sequentialize a  Lambda");}
        Exp::MakeClosure{arity, label, env, ann} => {
            return SeqExp::MakeClosure { 
                arity: *arity, 
                label: label.to_string(), 
                env: return_immediate(env).unwrap(), 
                ann: () };
        }
    }
}
#[cfg(test)]
mod seq_helper_Test {
    use super::*;
    /* 
    #[test]
    fn is_out_deleted() {
        //foo(a,b) -> let bleh1 = a in bleh2 = b in call(bleh1,bleh2)
        //foo(a,b) -> let bleh1 = a in call(bleh1, bleh2)
        let stupid_span = Span1 {
            start_ix: 0,
            end_ix: 0,
        };
        
        let exp = Exp::Call(
            "foo".to_string(), 
            vec![Exp::Var("a".to_string(), ()), Exp::Var("b".to_string(), ())], 
            ()
        );
        let inner_let = SeqExp::Imm(ImmExp::Var("2".to_string()), ());
        let (exp_tagged, trash);
        (trash, exp_tagged) = tag_prog(&[], &exp);
        assert_eq!(sequentialize_helper(&exp_tagged), inner_let);
    }*/
}

// Precondition: expressions do not include local function definitions or lambdas
fn sequentialize_program(decls: &[FunDecl<Exp<u32>, u32>], p: &Exp<u32>) -> SeqProg<()> {

    let mut funs : Vec<FunDecl<SeqExp<()>, ()>>= Vec::new();
    let mut i:u32 = 0;
    for d in decls{
        funs.push(FunDecl { 
            name: d.name.clone(),
            parameters: d.parameters.clone(), 
            body: sequentialize_helper(&d.body), 
            ann: () 
            });
    }

    return SeqProg{
        funs: funs,
        main: sequentialize_helper(p),
        ann: (),
    };
}


fn space_needed<Ann>(e: &SeqExp<Ann>) -> i32 {
    match e {
        SeqExp::Let{var: _variable, bound_exp: expression, body: inner_body, ann: _ann} => {
            return 1 + space_needed(expression) + space_needed(inner_body);
        },
        SeqExp::Imm(exp, _ann) =>{
            return 0;
        },
        SeqExp::Prim1(_prim, _immexp, _ann) => {
            return 0;
        },
        SeqExp::Prim2(_prim2, _imm1, _imm2, _ann) => 
        {
            return 0;
        },
        SeqExp::If{ cond: _con, thn: then, els: els, ann: _ann } => {
            return space_needed(then) + space_needed(els);
        },

        
        SeqExp::Array(vec, ann) => {return 1;}
        SeqExp::ArraySet{array, index, new_value, ann} => {return 0;}
        SeqExp::CallClosure { fun, args, ann } =>{panic!("nyi space needed callclosure");}
        SeqExp::MakeClosure{arity, label, env, ann} => {panic!("NYI:sequentialize_helper MakeClosure");}
    }
    //panic!("NYI: space_needed")
}


fn arith_number_err(reg_to_check: Reg) -> Vec<Instr> {
    // test RAX, 0x0000000000000001 ;; check only the tag bit of the value
    // jnz error_not_number         ;; if the bit is set, go to some centralized error handler
    let mut instructions = Vec::new();
    instructions.push(Instr::Test(BinArgs::ToReg(reg_to_check, Arg32::Unsigned(1))));
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(reg_to_check))));
    instructions.push(Instr::Jnz(JmpArg::Label("error_arith_number".to_string())));
    return instructions;
}

fn compare_number_err(reg_to_check: Reg) -> Vec<Instr> {
    // test RAX, 0x0000000000000001 ;; check only the tag bit of the value
    // jnz error_not_number         ;; if the bit is set, go to some centralized error handler
    let mut instructions = Vec::new();
    instructions.push(Instr::Test(BinArgs::ToReg(reg_to_check, Arg32::Unsigned(1))));
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(reg_to_check))));
    instructions.push(Instr::Jnz(JmpArg::Label("error_compare_number".to_string())));
    return instructions;
}



fn logic_bool_err(reg_to_check: Reg) -> Vec<Instr> {
    //let ufalse: u64 = 0x7F_FF_FF_FF_FF_FF_FF_FF;
    //let utrue: u64 = 0xFF_FF_FF_FF_FF_FF_FF_FF;
    let mut instructions = Vec::new();
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(reg_to_check))));

    instructions.push(Instr::And(BinArgs::ToReg(Reg::Rsi, Arg32::Unsigned(7))));
    instructions.push(Instr::Cmp(BinArgs::ToReg(Reg::Rsi, Arg32::Unsigned(7))));
    instructions.push(Instr::Jne(JmpArg::Label("error_logic_bool".to_string())));

    return instructions;
}


fn if_bool_err(reg_to_check: Reg) -> Vec<Instr> {
    // test RAX, 0x077777777777777 ;; check only the tag bit of the value
    // jnz error_not_number         ;; if the bit is set, go to some centralized error handler
    let mut instructions = Vec::new();

    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(reg_to_check))));
    instructions.push(Instr::And(BinArgs::ToReg(Reg::Rsi, Arg32::Unsigned(7))));
    instructions.push(Instr::Cmp(BinArgs::ToReg(Reg::Rsi, Arg32::Unsigned(7))));
    instructions.push(Instr::Jne(JmpArg::Label("error_if_bool".to_string())));
    return instructions;
}


fn is_array(reg_to_check: Reg) -> Vec<Instr> {
    // test RAX, 0x0000000000000001 ;; check only the tag bit of the value
    // jnz error_not_number         ;; if the bit is set, go to some centralized error handler
    let mut instructions = Vec::new();
    // 0x0000000002222001 valid array
    // 0x0007456481153001 valid array
    // 0x0000000000000000 not an array
    // 0x0000000000077777 not an array

    // mask to the last 3 bits
    // and with 0x000000007
    // all arrays will be 0x0000000000000001
    //instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Unsigned(7))));
    
    // story array pointer into rsi
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(reg_to_check))));

    instructions.push(Instr::And(BinArgs::ToReg(Reg::Rsi, Arg32::Unsigned(7))));
    
    // compare to 0x0000000000000001
    instructions.push(Instr::Cmp(BinArgs::ToReg(Reg::Rsi, Arg32::Unsigned(1))));
    
    

    // jump if not equal
    instructions.push(Instr::Jne(JmpArg::Label("error_is_array".to_string())));

    return instructions;
}

fn is_array_len(reg_to_check: Reg) -> Vec<Instr> {
    let mut instructions = Vec::new();
    // story array pointer into rsi
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(reg_to_check))));
    instructions.push(Instr::And(BinArgs::ToReg(Reg::Rsi, Arg32::Unsigned(7))));
    // compare to 0x0000000000000001
    instructions.push(Instr::Cmp(BinArgs::ToReg(Reg::Rsi, Arg32::Unsigned(1))));
    // jump if not equal
    instructions.push(Instr::Jne(JmpArg::Label("error_is_array_len".to_string())));
    return instructions;
}

fn index_number_err(reg_to_check: Reg) -> Vec<Instr> {
    // test RAX, 0x0000000000000001 ;; check only the tag bit of the value
    // jnz error_not_number         ;; if the bit is set, go to some centralized error handler
    let mut instructions = Vec::new();
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(reg_to_check))));
    instructions.push(Instr::Test(BinArgs::ToReg(Reg::Rsi, Arg32::Unsigned(1))));
    instructions.push(Instr::Jnz(JmpArg::Label("error_index_number".to_string())));
    return instructions;
}

fn index_bounds_err(reg_to_check: Reg, array_pointer: Reg) -> Vec<Instr> {
    let mut instructions = Vec::new();

    // untag array pointer
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(array_pointer))));
    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rsi, Arg32::Unsigned(1))));

    // move array length to rsi
    let mem = MemRef{reg:Reg::Rsi, offset:Offset::Constant(0)};
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Mem(mem))));

    // turn rsi into snake_val (x2)
 //   instructions.push(Instr::Shl(BinArgs::ToReg(Reg::Rsi, Arg32::Unsigned(1))));
    instructions.push(Instr::IMul(BinArgs::ToReg(Reg::Rsi, Arg32::Unsigned(2))));
    
    // cmp between rsi(length) and reg_to_check(index) which is Rbx
    instructions.push(Instr::Cmp(BinArgs::ToReg(Reg::Rsi, Arg32::Reg(reg_to_check))));    
    
    //jmp if less than or equal (jle)
    instructions.push(Instr::Jle(JmpArg::Label("error_index_bounds".to_string())));
    
    //jump if <0
    // cmp between rsi(length) and reg_to_check(index) which is Rbx
    instructions.push(Instr::Cmp(BinArgs::ToReg(reg_to_check, Arg32::Unsigned(0)))); 
    instructions.push(Instr::Jl(JmpArg::Label("error_index_bounds".to_string())));

    return instructions;
}


// List of currently used registers:
// RSP: Points to current instruction location on stackr14
// RBP: heap pointer?
// RDI, RSI, RDX, RCX, R8, and R9 are System V AMD64 ABI arguments (rust calls)
// Rax: everywhere, used to compute and return
// Rbx: overwritten by prim2, if, and prim1:not
// R10: overwritten in non-tail calls for debugging only // could be removed
// Rdi: error codes in rust calls
// Rsi: error faulty value in rust calls
// R15: heap pointer (space for arrays)
// R14: working register used in array set
fn compile_to_instrs_helper(e: &SeqExp<u32>,  mut env: Vec<String>, mut is_tail:bool) -> Vec<Instr> {
    let mut instructions = Vec::new();
    let ufalse: u64 = 0x7F_FF_FF_FF_FF_FF_FF_FF;
    let utrue: u64 = 0xFF_FF_FF_FF_FF_FF_FF_FF;

    match e {
        SeqExp::Imm(e2, _ann) => {
            match e2{
                ImmExp::Bool(b) => {
                    if *b {
                        instructions.push(Instr::Mov(
                            MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(0xFF_FF_FF_FF_FF_FF_FF_FF),
                        )));
                    } else {
                        instructions.push(Instr::Mov(
                            MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(0x7F_FF_FF_FF_FF_FF_FF_FF),
                        )));
                    }
                }
                ImmExp::Num(curr_num) => {
                    
                    instructions.push(Instr::Mov(
                        MovArgs::ToReg(Reg::Rax, Arg64::Signed(*curr_num << 1),
                    )));
                },
                // get variable index, move value from memory to rax
                ImmExp::Var(s) => {
                    
                    
                    //get offset from rsp (string index in array *8)
                    let mut count = env.len();
                    
                    loop {
                        if s == &env[count-1] {
                            break;
                        } else if count == 1 {
                            panic!("env does not contain variable {}", s);
                        }
                        count -= 1;
                    }
                    
                    let calculated_offset:i32 = -8 * usize_to_i32(count);
                    let address = MemRef{
                        reg: Reg::Rsp,
                        offset: Offset::Constant(calculated_offset),
                    };
                    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Mem(address))));                    
                }
            } 
        }

        SeqExp::Prim1(operation, sub_exp, ann) => {
            
            // Store sub_exp into rax
            instructions.append(&mut compile_to_instrs_helper(&Box::new(SeqExp::<u32>::Imm(sub_exp.clone(), *ann),), env.clone(), is_tail));
            let is_num = format!("is_num#{}", ann);
            let is_false = format!("is_false#{}", ann);
            let done_lab = format!("done#{}", ann);
            
            
            let xor_mask: u64 = 0x8000000000000000;


            match operation{
                Prim1::Add1 => {
                    // check if rax is a number or boolean
                    //instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Unsigned(0))));
                    instructions.append(&mut arith_number_err(Reg::Rax));

                    instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rax, Arg32::Signed(2))));
                    instructions.push(Instr::Jo(JmpArg::Label("overflow".to_string())));
                },

                Prim1::Sub1 => { 
                    //instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Unsigned(0))));
                    // if rax is a number, sub1 else call error function
                    // test RAX, 0x0000000000000001 ;; check only the tag bit of the value
                    // jnz error_not_number         ;; if the bit is set, go to some centralized error handler
                    instructions.append(&mut arith_number_err(Reg::Rax));
                    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rax, Arg32::Signed(2))));
                    instructions.push(Instr::Jo(JmpArg::Label("overflow".to_string())));
                }

                Prim1::IsBool =>{ // if rax is a bool, store true in rax, else store false
                    instructions.push(Instr::Test(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(1))));
                    instructions.push(Instr::Jz(JmpArg::Label(is_num.clone()))); // zero means rax is a number
                    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(utrue))));
                     //not a number
                    instructions.push(Instr::Jmp(JmpArg::Label(done_lab.clone())));

                    instructions.push(Instr::Label(is_num.clone()));
                    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(ufalse)))); // is a number

                    instructions.push(Instr::Label(done_lab.clone()));
                }

                Prim1::IsNum =>{ // if rax is a number, store true in rax else store false
                    // IsNum(RAX)
                    instructions.push(Instr::Test(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(1))));
                    instructions.push(Instr::Jz(JmpArg::Label(is_num.clone()))); // zero means rax is a number

                    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(ufalse))));
                    instructions.push(Instr::Jmp(JmpArg::Label(done_lab.clone())));

                    instructions.push(Instr::Label(is_num.clone()));
                    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(utrue))));

                    instructions.push(Instr::Label(done_lab.clone()));

                }

                Prim1::Not =>{
                    // let xor_mask: u64 = 0x8000000000000000;
                    //instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Unsigned(4))));
                    // test RAX, 0x0000000000000001 ;; check only the tag bit of the value
                    // jnz error_not_number         ;; if the bit is set, go to some centralized error handler
                    
                    instructions.append(&mut logic_bool_err(Reg::Rax));
                    
                    // store 0x8000000000000000 into Rbx
                    // xor rax, Rbx
                    //
                    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rbx, Arg64::Unsigned(xor_mask))));
                    instructions.push(Instr::Xor(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rbx))));

                }
                Prim1::Print =>{
                    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Reg(Reg::Rax))));
                    
                    let mut max_space_needed = env.clone().len() as u32;
                    
                    if max_space_needed % 2 == 0{
                        max_space_needed +=1;
                    }
                    max_space_needed = max_space_needed * 8;

                    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));
                    instructions.push(Instr::Call(JmpArg::Label("print_snake_val".to_string())));
                    instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));

                }
                Prim1::Length => {
                    // check if it is an array
                    instructions.append(&mut is_array_len(Reg::Rax));

                    // untag the array pointer
                    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(1))));

                    // mov the first element of the array (0th) to rax
                    let address = MemRef{
                        reg: Reg::Rax,
                        offset: Offset::Constant(0),
                    };
                    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Mem(address))));

                    // convert into a snake_Val number (x2)
                    instructions.push(Instr::IMul(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(2))));


                },
                Prim1::IsArray => {
                    let is_array = format!("is_array#{}", ann);
                    
                    // test RAX, 0x0000000000000001 ;; check only the tag bit of the value
                    // jnz error_not_number         ;; if the bit is set, go to some centralized error handler
                    let mut instructions = Vec::new();

                    // story array pointer into rbx
                    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rbx, Arg64::Reg(Reg::Rax))));

                    instructions.push(Instr::And(BinArgs::ToReg(Reg::Rbx, Arg32::Unsigned(7))));
                    
                    // compare to 0x0000000000000001
                    instructions.push(Instr::Cmp(BinArgs::ToReg(Reg::Rbx, Arg32::Unsigned(1))));
    
                    // jump if not equal
                    instructions.push(Instr::Jne(JmpArg::Label(is_array.clone())));
                    
                    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(utrue))));
                    instructions.push(Instr::Jmp(JmpArg::Label(done_lab.clone())));

                    instructions.push(Instr::Label(is_array.clone()));
                    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(ufalse))));
                    instructions.push(Instr::Label(done_lab.clone()));

                    return instructions;

                },
                Prim1::IsFun => todo!(),
                
            }
        }

        SeqExp::Prim2(op, imm1, imm2, ann) => {
            
            
            let is_true = format!("is_true#{}", ann);
            let done_lab = format!("done#{}", ann);
            
            // sub(2,3) -> store 3 into rax, rax into Rbx, store 2 in rax, then sub Rbx from rax

            // Store imm2 into rax
            instructions.append(&mut compile_to_instrs_helper(&Box::new(SeqExp::<u32>::Imm(imm2.clone(), *ann),), env.clone(), is_tail));
            // move rax to Rbx
            instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rbx, Arg64::Reg(Reg::Rax))));

            // Store imm1 into rax
            instructions.append(&mut compile_to_instrs_helper(&Box::new(SeqExp::<u32>::Imm(imm1.clone(), *ann),), env.clone(), is_tail));

            // evaluate operation

            // error checking for imm1 and imm2 to make sure they're numbers
            // check if rax is a number or boolean
            // test RAX, 0x0000000000000001 ;; check only the tag bit of the value
            // jnz error_not_number         ;; if the bit is set, go to some centralized error handler
        //    instructions.push(Instr::Test(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(1))));
        //    instructions.push(Instr::Jnz("error_not_number".to_string()));

            match op{
                
                Prim2::Add => {
                    instructions.append(&mut arith_number_err(Reg::Rax));
                    instructions.append(&mut arith_number_err(Reg::Rbx));
                    instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rbx))));
                    instructions.push(Instr::Jo(JmpArg::Label("overflow".to_string())));
                }
                Prim2::Sub => {
                    instructions.append(&mut arith_number_err(Reg::Rax));
                    instructions.append(&mut arith_number_err(Reg::Rbx));
                    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rbx))));
                    instructions.push(Instr::Jo(JmpArg::Label("overflow".to_string())));
                }
                Prim2::Mul => {
                    instructions.append(&mut arith_number_err(Reg::Rax));
                    instructions.append(&mut arith_number_err(Reg::Rbx));
                    instructions.push(Instr::IMul(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rbx))));
                    instructions.push(Instr::Jo(JmpArg::Label("overflow".to_string())));
                    instructions.push(Instr::Sar(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(1))));
                    
                }
                Prim2::And => {
                    instructions.append(&mut logic_bool_err(Reg::Rax));
                    instructions.append(&mut logic_bool_err(Reg::Rbx));
                    instructions.push(Instr::And(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rbx))));
                    
                }
                Prim2::Or => {
                    instructions.append(&mut logic_bool_err(Reg::Rax));
                    instructions.append(&mut logic_bool_err(Reg::Rbx));
                    instructions.push(Instr::Or(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rbx))));
                }
                Prim2::Lt => {
                    instructions.append(&mut compare_number_err(Reg::Rax));
                    instructions.append(&mut compare_number_err(Reg::Rbx));

                    instructions.push(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rbx))));
                    instructions.push(Instr::Jl(JmpArg::Label(is_true.clone())));

                    instructions.push(Instr::Mov(
                        MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(ufalse),
                    )));
                    instructions.push(Instr::Jmp(JmpArg::Label(done_lab.clone())));

                    instructions.push(Instr::Label(is_true.clone()));
                    instructions.push(Instr::Mov(
                        MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(utrue),
                    )));                    

                    instructions.push(Instr::Label(done_lab.clone()));
                    
                }
                Prim2::Gt => {
                    instructions.append(&mut compare_number_err(Reg::Rax));
                    instructions.append(&mut compare_number_err(Reg::Rbx));
                    
                    instructions.push(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rbx))));
                    instructions.push(Instr::Jg(JmpArg::Label(is_true.clone())));

                    instructions.push(Instr::Mov(
                        MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(ufalse),
                    )));
                    instructions.push(Instr::Jmp(JmpArg::Label(done_lab.clone())));

                    instructions.push(Instr::Label(is_true.clone()));
                    instructions.push(Instr::Mov(
                        MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(utrue),
                    )));                    

                    instructions.push(Instr::Label(done_lab.clone()));
                }
                Prim2::Le => {
                    instructions.append(&mut compare_number_err(Reg::Rax));
                    instructions.append(&mut compare_number_err(Reg::Rbx));

                    instructions.push(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rbx))));
                    instructions.push(Instr::Jle(JmpArg::Label(is_true.clone())));

                    instructions.push(Instr::Mov(
                        MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(ufalse),
                    )));
                    instructions.push(Instr::Jmp(JmpArg::Label(done_lab.clone())));

                    instructions.push(Instr::Label(is_true.clone()));
                    instructions.push(Instr::Mov(
                        MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(utrue),
                    )));                    

                    instructions.push(Instr::Label(done_lab.clone()));
                    
                }
                Prim2::Ge => {
                    
                    instructions.append(&mut compare_number_err(Reg::Rax));
                    instructions.append(&mut compare_number_err(Reg::Rbx));

                    instructions.push(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rbx))));
                    instructions.push(Instr::Jge(JmpArg::Label(is_true.clone())));

                    instructions.push(Instr::Mov(
                        MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(ufalse),
                    )));
                    instructions.push(Instr::Jmp(JmpArg::Label(done_lab.clone())));

                    instructions.push(Instr::Label(is_true.clone()));
                    instructions.push(Instr::Mov(
                        MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(utrue),
                    )));                    

                    instructions.push(Instr::Label(done_lab.clone()));
                    
                }
                Prim2::Eq => {
                    
                    instructions.push(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rbx))));
                    instructions.push(Instr::Je(JmpArg::Label(is_true.clone())));

                    instructions.push(Instr::Mov(
                        MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(ufalse),
                    )));
                    instructions.push(Instr::Jmp(JmpArg::Label(done_lab.clone())));

                    instructions.push(Instr::Label(is_true.clone()));
                    instructions.push(Instr::Mov(
                        MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(utrue),
                    )));                    

                    instructions.push(Instr::Label(done_lab.clone()));
                }
                Prim2::Neq => todo!(),
                Prim2::ArrayGet => {
                    // starts with arg1 in Rax, and arg2 in Rbx
                    // Rax is array, Rbx is index

                    // check rax is a array
                    instructions.append(&mut is_array(Reg::Rax));
                    
                    

                    // move index value into r14
             //       instructions.push(Instr::Mov(MovArgs::ToReg(Reg::R14, Reg::Rbx)));

                    // check that index is number
                    instructions.append(&mut index_number_err(Reg::Rbx));

                    // check that index is in bounds
                    instructions.append(&mut index_bounds_err(Reg::Rbx, Reg::Rax));

                    // untag Rax
                    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(1))));

                    // find where the value is (array + index *8 + 1)
                   // instructions.push(Instr::Mul(BinArgs::ToReg(Reg::Rbx, Arg32::Unsigned(8))));
                   // instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rbx))));
                   
                   // divide rbx by 2 
                   instructions.push(Instr::Sar(BinArgs::ToReg(Reg::Rbx, Arg32::Unsigned(1))));

                    // write the value from array[index] to rax
                    let mem = MemRef{ 
                        reg: Reg::Rax, 
                        offset: Offset::Computed { reg: Reg::Rbx, factor: 8, constant: 8 } // try setting const to 1 if broken
                    };
                    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Mem(mem))));


                },
            }
            
        } 

        SeqExp::Let {var: identifier, bound_exp: expression, body: inner_body, ann: _ann} => {
            
            //add instructions to evaluate expression and store into rax
            instructions.append(&mut compile_to_instrs_helper(expression, env.clone(), false));

            //add identifier to vector
            env.push(identifier.to_string());

            //mov rax to mem
            let address = MemRef{
                reg: Reg::Rsp,
                offset: Offset::Constant(-8 * usize_to_i32(env.len())),
            };

            instructions.push(Instr::Mov(MovArgs::ToMem(address ,Reg32::Reg(Reg::Rax))));
            
            //evaluate body and store into rax
            instructions.append(&mut compile_to_instrs_helper(inner_body, env.clone(), is_tail));
        }

        SeqExp::If { cond, thn, els, ann } => {
            //instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Unsigned(3))));
            instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rbx, Arg64::Unsigned(utrue))));

            // cond is ImmExp
            let else_lab = format!("else#{}", ann);
            let done_lab = format!("done#{}", ann);
            // store cond to rax
            instructions.append(&mut compile_to_instrs_helper(&Box::new(SeqExp::<u32>::Imm(cond.clone(), *ann)), env.clone(), is_tail));
            // check if cond is bool
            instructions.append(&mut if_bool_err(Reg::Rax));

            // sets flags used by condional jump instructions, comparing rax to 0
            instructions.push(Instr::Cmp(BinArgs::ToReg(Reg::Rax, Arg32::Reg(Reg::Rbx))));

            // if not equal jump to the else label
            instructions.push(Instr::Jne(JmpArg::Label(else_lab.clone())));

            // then instrutions
            instructions.append(&mut compile_to_instrs_helper(thn, env.clone(), is_tail));

            // jump to end (to avoid executing both then and else)
            instructions.push(Instr::Jmp(JmpArg::Label(done_lab.clone())));

            // set label for else condion
            instructions.push(Instr::Label(else_lab.clone()));
            
            // else instructions
            instructions.append(&mut compile_to_instrs_helper(els, env.clone(), is_tail));

            // set label for done 
            instructions.push(Instr::Label(done_lab.clone()));
        }
        SeqExp::CallClosure{fun, args, ann} => {
            panic!("NYI::call");
            /*
            // if it is a tail call:
            if (is_tail){
                // Store each parameter into rsp-8, rsp-16, ...
                // We don't/shouldn't have to worry about overwritting varibles that will be needed later due to uniquify and sequentialize
                let mut i = 0;
                for a in args{
                // Temporarly store in a register (rax) because you can't move directly from one part of memory to another
                instructions.append(&mut compile_to_instrs_helper(&SeqExp::Imm(a.clone(), 0), env.clone(), false));
                // Save rax to memory in the appropiate place
                i += 1;
                let address_to_write = MemRef{reg: Reg::Rsp, offset: -8 * i};
                instructions.push(Instr::Mov(MovArgs::ToMem(address_to_write, Reg32::Reg(Reg::Rax))));
                }
                // jump to function 
                instructions.push(Instr::Jmp(fun.to_string()));
            }

            else { //non-tail

                //temp to see where in assembly we start call
                instructions.push(Instr::Add(BinArgs::ToReg(Reg::R10, Arg32::Unsigned(888888888))));

                // find space_needed ( amount rsp will be incremented)
                let mut space_needed:u32 = env.len() as u32;
                if space_needed % 2 == 0{
                    space_needed +=1;
                }
                space_needed = space_needed * 8;
             /*   print!("env = ");
                for x in env.clone(){ print!("{}, ", x);}
                println!();
                println!("space needed = {}", space_needed);*/


                // store args into rsp-(1+space_needed), rsp-(2+spance_needed), ...
                let mut i:i32 = 0;
                for a in args{ 
                    let address_to_write = MemRef{reg: Reg::Rsp, offset: (-1* space_needed as i32) + -8 * (i + 2)};
                    i += 1;
                    // move a into rax
                    instructions.append(&mut compile_to_instrs_helper(&SeqExp::Imm(a.clone(), 666666), env.clone(), is_tail));
                    // move rax into rsp+i+space_needed
                    instructions.push(Instr::Mov(MovArgs::ToMem(address_to_write, Reg32::Reg(Reg::Rax))));
                }
                // increment rsp by space_needed
                instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(space_needed))));

                // call to label fun
                instructions.push(Instr::Call(fun.to_string()));

                // decrement rsp by space_needed
                instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(space_needed))));
            }*/
        }
        SeqExp::ArraySet { array, index, new_value, ann } => {
            
            // Store new_value into r14
            instructions.append(&mut compile_to_instrs_helper(&SeqExp::Imm(new_value.clone(), 0), env.clone(), is_tail));
            instructions.push(Instr::Mov(MovArgs::ToReg(Reg::R14, Arg64::Reg(Reg::Rax))));

            // Store index into Rbx
            instructions.append(&mut compile_to_instrs_helper(&Box::new(SeqExp::<u32>::Imm(index.clone(), *ann),), env.clone(), is_tail));
            instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rbx, Arg64::Reg(Reg::Rax))));

            // Store array into rax
            instructions.append(&mut compile_to_instrs_helper(&Box::new(SeqExp::<u32>::Imm(array.clone(), *ann),), env.clone(), is_tail));
            
            // check rax is a array
            instructions.append(&mut is_array(Reg::Rax));
            
            // untag Rax
            instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(1))));

            // check that index is number
            instructions.append(&mut index_number_err(Reg::Rbx));

            // check that index is in bounds
            instructions.append(&mut index_bounds_err(Reg::Rbx, Reg::Rax));

            // untag index (divide Rbx by 2)
            instructions.push(Instr::Shr(BinArgs::ToReg(Reg::Rbx, Arg32::Unsigned(1))));
            
            
            // write the r14 to array[index]
            let mem = MemRef{ 
                reg: Reg::Rax, 
                offset: Offset::Computed { reg: Reg::Rbx, factor: 8, constant: 8 } 
            };
            instructions.push(Instr::Mov(MovArgs::ToMem(mem, Reg32::Reg(Reg::R14))));

            // Retag Rax
            instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(1))));
        },
        SeqExp::Array(vec, ann) => {
            let size_of = vec.len() as u64;

            //instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Unsigned(size_of))));
            let memadr = MemRef{ reg: Reg::R15, offset: Offset::Constant(0) };
            instructions.push(Instr::Mov(MovArgs::ToMem(memadr, Reg32::Unsigned(size_of as u32))));
            
            
            let mut i = 1;
            for curr_element in vec{
                //store curr_element into rax
                instructions.append(&mut compile_to_instrs_helper(
                    &SeqExp::Imm(curr_element.clone(), *ann), env.clone(), is_tail)
                );
                // store rax onto heap
                let memadr = MemRef{ reg: Reg::R15, offset: Offset::Constant(8*i) };
                instructions.push(Instr::Mov(MovArgs::ToMem(memadr, Reg32::Reg(Reg::Rax))));
                // add 8 to r15
                i += 1;
            }

            // put array pointer into rax
            instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rax, Arg64::Reg(Reg::R15))));
            
            // tag rax as array
            instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(1))));

            // increase r15 by 8*length
            instructions.push(Instr::Add(BinArgs::ToReg(Reg::R15, Arg32::Unsigned(8*(size_of as u32 + 1)))));
        },
        SeqExp::MakeClosure { arity, label, env, ann } => todo!(),
    }
    return instructions;
}

fn compile_to_instr_functions(funcs:Vec<FunDecl<SeqExp<u32>, u32>>, e: &SeqExp<u32>) -> Vec<Instr> {
    
    let mut instructions = Vec::new();

    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::R15, Arg64::Label("HEAP".to_string()))));
    // add 7
    /*instructions.push(Instr::Add(BinArgs::ToReg(Reg::R15, Arg32::Unsigned(7))));
    // round down to nearest multiple of 8
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rbx, Arg64::Unsigned(0xFF_FF_FF_FF_FF_FF_FF_F7))));

    instructions.push(Instr::And(BinArgs::ToReg(Reg::R15, Arg32::Reg(Reg::Rbx))));*/


    
    instructions.append(&mut compile_to_instrs_helper(e, Vec::new(), true));
    
    let mut max_space_needed: u32 = space_needed(e) as u32; //wastes memory, but is safe
    if max_space_needed % 2 == 0{
        max_space_needed +=1;
    }
    max_space_needed = max_space_needed * 8;
  //  println!("Space needed is {}", max_space_needed);
  //  println!("instructions: {}", instrs_to_string(&instructions));
    // unconditional jump to end of program label
    instructions.push(Instr::Jmp(JmpArg::Label("End".to_string())));

    for f in funcs{

        /*
        foo(a,b)
        push a and b to env so env = [a,b]
        a is located in rsp + 8 *1 in mem
         */


        // create function label
        instructions.push(Instr::Label(f.name));
        // write the function body
        instructions.append(&mut compile_to_instrs_helper(&f.body, f.parameters, true));
        // jump to return address (rsp-1?)
        instructions.push(Instr::Ret);
    }



    // error handling labels
    // call rust print error thing and book
    instructions.push(Instr::Label("error_arith_number".to_string()));
    //todo: put any arguments needed into registers/memory
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Unsigned(0))));
    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));
    instructions.push(Instr::Call(JmpArg::Label("snake_error".to_string())));
    // should be inc
    instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));
    //instructions.push(Instr::Jmp("End".to_string()));

    instructions.push(Instr::Label("error_compare_number".to_string()));
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Unsigned(1))));
    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));
    instructions.push(Instr::Call(JmpArg::Label("snake_error".to_string())));
    instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));


    instructions.push(Instr::Label("error_if_bool".to_string()));
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Unsigned(3))));
    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));
    instructions.push(Instr::Call(JmpArg::Label("snake_error".to_string())));
    instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));


    instructions.push(Instr::Label("error_logic_bool".to_string()));
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Unsigned(4))));
    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));
    // call rust function
    instructions.push(Instr::Call(JmpArg::Label("snake_error".to_string())));
    // should be inc
    instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));



    instructions.push(Instr::Label("error_is_array".to_string()));
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Unsigned(7))));
    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));
    // call rust function
    instructions.push(Instr::Call(JmpArg::Label("snake_error".to_string())));
    // should be inc
    instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));

    instructions.push(Instr::Label("error_is_array_len".to_string()));
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Unsigned(10))));
    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));
    // call rust function
    instructions.push(Instr::Call(JmpArg::Label("snake_error".to_string())));
    // should be inc
    instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));

    instructions.push(Instr::Label("error_index_number".to_string()));
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Unsigned(8))));
    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));
    // call rust function
    instructions.push(Instr::Call(JmpArg::Label("snake_error".to_string())));
    // should be inc
    instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));

    instructions.push(Instr::Label("error_index_bounds".to_string()));
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Unsigned(9))));
    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));
    // call rust function
    instructions.push(Instr::Call(JmpArg::Label("snake_error".to_string())));
    // should be inc
    instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));
    

    

    instructions.push(Instr::Label("overflow".to_string()));
    instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rdi, Arg64::Unsigned(2))));
    //instructions.push(Instr::Mov(MovArgs::ToReg(Reg::Rsi, Arg64::Reg(Reg::Rax))));
    // should be dec
    instructions.push(Instr::Sub(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));
    // call rust function
    instructions.push(Instr::Call(JmpArg::Label("snake_error".to_string())));
    // should be inc
    instructions.push(Instr::Add(BinArgs::ToReg(Reg::Rsp, Arg32::Unsigned(max_space_needed))));


    // end of program label
    instructions.push(Instr::Label("End".to_string()));
    // shift right rax 1
  //  instructions.push(Instr::Shr(BinArgs::ToReg(Reg::Rax, Arg32::Unsigned(1))));
    // end of program
    instructions.push(Instr::Ret);
    return instructions;
}


fn compile_to_instrs(p: &SeqProg<u32>) -> Vec<Instr> {
  //  let mut output:Vec<Instr> = Vec::new();
    // write the main program
    //output.append(&mut compile_to_instrs_helper(&p.main, Vec::new()));
    // write all the functions from the vector Vec<FunDecl<SeqExp<Ann>, Ann>>
   // output = compile_to_instr_functions(p.funs, &p.main);


    return compile_to_instr_functions(p.funs.clone(), &p.main);
    
}

pub fn compile_to_string<Span>(p: &SurfProg<Span>) -> Result<String, CompileErr<Span>>
where
    Span: Clone,
{
    // first check for errors
    check_prog(p)?;
    // then give all the variables unique names
    let uniq_p = tag_exp(&uniquify(&tag_exp(p)));

    // lift definitions to the top level
    let (defs, main) = lambda_lift(&uniq_p);
    let (t_defs, t_main) = tag_prog(&defs, &main);
    // then sequentialize
    let seq_p = tag_sprog(&sequentialize_program(&t_defs, &t_main));
    // then codegen
    let is = compile_to_instrs(&seq_p);
    return Ok(format!(
        "\
section .data
HEAP:    times 1024 dq 0
section .text
global start_here
extern snake_error
extern print_snake_val

start_here:

{}       
",instrs_to_string(&is)));
}
