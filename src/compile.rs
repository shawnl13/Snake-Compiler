use crate::asm::instrs_to_string;
use crate::asm::{Arg32, Arg64, BinArgs, Instr, JmpArg, MemRef, MovArgs, Offset, Reg, Reg32};
use crate::syntax::{Exp, FunDecl, ImmExp, Prim1, Prim2, SeqExp, SeqProg, SurfFunDecl, SurfProg};

#[derive(Debug, PartialEq, Eq)]
pub enum CompileErr<Span> {
    UnboundVariable {
        unbound: String,
        location: Span,
    },
    UndefinedFunction {
        undefined: String,
        location: Span,
    },
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
        location: Span, // the location of the 2nd function
    },

    DuplicateArgName {
        duplicated_name: String,
        location: Span,
    },
}

pub fn check_prog<Span>(p: &SurfProg<Span>) -> Result<(), CompileErr<Span>>
where
    Span: Clone,
{
    panic!("NYI: check_prog")
}

fn uniquify(e: &Exp<u32>) -> Exp<()> {
    panic!("NYI: uniquify");
}

// Precondition: all names are uniquified
fn lambda_lift<Ann>(p: &Exp<Ann>) -> (Vec<FunDecl<Exp<()>, ()>>, Exp<()>) {
    panic!("NYI: lambda_lift")
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

// Precondition: expressions do not include local function definitions or lambdas
fn sequentialize_program(decls: &[FunDecl<Exp<u32>, u32>], p: &Exp<u32>) -> SeqProg<()> {
    panic!("NYI: sequentialize_program")
}

fn compile_to_instrs(p: &SeqProg<u32>) -> Vec<Instr> {
    panic!("NYI: compile_to_instrs")
}

pub fn compile_to_string<Span>(p: &SurfProg<Span>) -> Result<String, CompileErr<Span>>
where
    Span: Clone,
{
    // first check for errors
    check_prog(p)?;
    // then give all the variables unique names
    let uniq_p = uniquify(&tag_exp(p));

    // lift definitions to the top level
    let (defs, main) = lambda_lift(&uniq_p);
    let (t_defs, t_main) = tag_prog(&defs, &main);
    // then sequentialize
    let seq_p = tag_sprog(&sequentialize_program(&t_defs, &t_main));
    // then codegen
    panic!("NYI: code generation")
}
