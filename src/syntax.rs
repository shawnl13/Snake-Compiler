pub type SurfProg<Ann> = Exp<Ann>;
pub type SurfFunDecl<Ann> = FunDecl<Exp<Ann>, Ann>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunDecl<E, Ann> {
    pub name: String,
    pub parameters: Vec<String>,
    pub body: E,
    pub ann: Ann,
}

/* Expressions */
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Exp<Ann> {
    Num(i64, Ann),
    Bool(bool, Ann),
    Var(String, Ann),
    Prim1(Prim1, Box<Exp<Ann>>, Ann),
    Prim2(Prim2, Box<Exp<Ann>>, Box<Exp<Ann>>, Ann),
    Let {
        bindings: Vec<(String, Exp<Ann>)>, // new binding declarations
        body: Box<Exp<Ann>>,               // the expression in which the new variables are bound
        ann: Ann,
    },
    If {
        cond: Box<Exp<Ann>>,
        thn: Box<Exp<Ann>>,
        els: Box<Exp<Ann>>,
        ann: Ann,
    },

    Array(Vec<Exp<Ann>>, Ann),
    ArraySet {
        array: Box<Exp<Ann>>,
        index: Box<Exp<Ann>>,
        new_value: Box<Exp<Ann>>,
        ann: Ann,
    },

    Semicolon {
        e1: Box<Exp<Ann>>,
        e2: Box<Exp<Ann>>,
        ann: Ann,
    },

    FunDefs {
        decls: Vec<FunDecl<Exp<Ann>, Ann>>,
        body: Box<Exp<Ann>>,
        ann: Ann,
    },
    Call(Box<Exp<Ann>>, Vec<Exp<Ann>>, Ann),
    Lambda {
        parameters: Vec<String>,
        body: Box<Exp<Ann>>,
        ann: Ann,
    },
    MakeClosure {
        arity: usize,
        label: String,
        env: Box<Exp<Ann>>,
        ann: Ann,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Prim1 {
    Add1,
    Sub1,
    Not,
    Print,
    IsBool,
    IsNum,
    Length,
    IsArray,
    IsFun,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Prim2 {
    Add,
    Sub,
    Mul,

    And,
    Or,

    Lt,
    Gt,
    Le,
    Ge,

    Eq,
    Neq,
    ArrayGet, // first arg is array, second is index
}

/* Sequential Expressions */
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeqProg<Ann> {
    pub funs: Vec<FunDecl<SeqExp<Ann>, Ann>>,
    pub main: SeqExp<Ann>,
    pub ann: Ann,
}

pub type SeqFunDecl<Ann> = FunDecl<SeqExp<Ann>, Ann>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImmExp {
    Num(i64),
    Bool(bool),
    Var(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SeqExp<Ann> {
    Imm(ImmExp, Ann),
    Prim1(Prim1, ImmExp, Ann),
    Prim2(Prim2, ImmExp, ImmExp, Ann),
    ArraySet {
        array: ImmExp,
        index: ImmExp,
        new_value: ImmExp,
        ann: Ann,
    },
    Array(Vec<ImmExp>, Ann),
    MakeClosure {
        arity: usize,
        label: String,
        env: ImmExp,
        ann: Ann,
    },
    CallClosure {
        fun: ImmExp,
        args: Vec<ImmExp>,
        ann: Ann,
    },

    Let {
        var: String,
        bound_exp: Box<SeqExp<Ann>>,
        body: Box<SeqExp<Ann>>,
        ann: Ann,
    },
    If {
        cond: ImmExp,
        thn: Box<SeqExp<Ann>>,
        els: Box<SeqExp<Ann>>,
        ann: Ann,
    },
}

/* Useful functions for Exps, BindExps, SeqExps */
impl<Ann> Exp<Ann> {
    pub fn ann(&self) -> Ann
    where
        Ann: Clone,
    {
        match self {
            Exp::Num(_, a)
            | Exp::Bool(_, a)
            | Exp::Var(_, a)
            | Exp::Prim1(_, _, a)
            | Exp::Prim2(_, _, _, a)
            | Exp::Let { ann: a, .. }
            | Exp::If { ann: a, .. }
            | Exp::Array(_, a)
            | Exp::ArraySet { ann: a, .. }
            | Exp::Semicolon { ann: a, .. }
            | Exp::Call(_, _, a)
            | Exp::FunDefs { ann: a, .. }
            | Exp::Lambda { ann: a, .. }
            | Exp::MakeClosure { ann: a, .. } => a.clone(),
        }
    }

    pub fn ann_mut(&mut self) -> &mut Ann {
        match self {
            Exp::Num(_, a)
            | Exp::Bool(_, a)
            | Exp::Var(_, a)
            | Exp::Prim1(_, _, a)
            | Exp::Prim2(_, _, _, a)
            | Exp::Let { ann: a, .. }
            | Exp::If { ann: a, .. }
            | Exp::Array(_, a)
            | Exp::ArraySet { ann: a, .. }
            | Exp::Semicolon { ann: a, .. }
            | Exp::Call(_, _, a)
            | Exp::FunDefs { ann: a, .. }
            | Exp::Lambda { ann: a, .. }
            | Exp::MakeClosure { ann: a, .. } => a,
        }
    }

    pub fn map_ann<Ann2, F>(&self, f: &mut F) -> Exp<Ann2>
    where
        F: FnMut(&Ann) -> Ann2,
    {
        match self {
            Exp::Num(n, a) => Exp::Num(*n, f(a)),
            Exp::Bool(b, a) => Exp::Bool(*b, f(a)),
            Exp::Var(s, a) => Exp::Var(s.clone(), f(a)),
            Exp::Prim1(op, e, a) => Exp::Prim1(*op, Box::new(e.map_ann(f)), f(a)),
            Exp::Prim2(op, e1, e2, a) => {
                Exp::Prim2(*op, Box::new(e1.map_ann(f)), Box::new(e2.map_ann(f)), f(a))
            }
            Exp::Let {
                bindings,
                body,
                ann,
            } => Exp::Let {
                bindings: bindings
                    .iter()
                    .map(|(x, e)| (x.clone(), e.map_ann(f)))
                    .collect(),
                body: Box::new(body.map_ann(f)),
                ann: f(ann),
            },
            Exp::If {
                cond,
                thn,
                els,
                ann,
            } => Exp::If {
                cond: Box::new(cond.map_ann(f)),
                thn: Box::new(thn.map_ann(f)),
                els: Box::new(els.map_ann(f)),
                ann: f(ann),
            },
            Exp::Array(es, a) => Exp::Array(es.iter().map(|e| e.map_ann(f)).collect(), f(a)),
            Exp::ArraySet {
                array,
                index,
                new_value,
                ann,
            } => Exp::ArraySet {
                array: Box::new(array.map_ann(f)),
                index: Box::new(index.map_ann(f)),
                new_value: Box::new(new_value.map_ann(f)),
                ann: f(ann),
            },
            Exp::Semicolon { e1, e2, ann } => Exp::Semicolon {
                e1: Box::new(e1.map_ann(f)),
                e2: Box::new(e2.map_ann(f)),
                ann: f(ann),
            },
            Exp::Call(fun, args, ann) => Exp::Call(
                Box::new(fun.map_ann(f)),
                args.iter().map(|e| e.map_ann(f)).collect(),
                f(ann),
            ),
            Exp::FunDefs { decls, body, ann } => Exp::FunDefs {
                decls: decls.iter().map(|d| d.map_ann(f)).collect(),
                body: Box::new(body.map_ann(f)),
                ann: f(ann),
            },
            Exp::Lambda {
                parameters,
                body,
                ann,
            } => Exp::Lambda {
                parameters: parameters.clone(),
                body: Box::new(body.map_ann(f)),
                ann: f(ann),
            },
            Exp::MakeClosure {
                arity,
                label,
                env,
                ann,
            } => Exp::MakeClosure {
                arity: *arity,
                label: label.clone(),
                env: Box::new(env.map_ann(f)),
                ann: f(ann),
            },
        }
    }
}

impl<Ann> SeqExp<Ann> {
    pub fn ann(&self) -> Ann
    where
        Ann: Clone,
    {
        match self {
            SeqExp::Imm(_, a)
            | SeqExp::Prim1(_, _, a)
            | SeqExp::Prim2(_, _, _, a)
            | SeqExp::ArraySet { ann: a, .. }
            | SeqExp::Array(_, a)
            | SeqExp::MakeClosure { ann: a, .. }
            | SeqExp::CallClosure { ann: a, .. }
            | SeqExp::Let { ann: a, .. }
            | SeqExp::If { ann: a, .. } => a.clone(),
        }
    }

    pub fn map_ann<Ann2, F>(&self, f: &mut F) -> SeqExp<Ann2>
    where
        F: FnMut(&Ann) -> Ann2,
    {
        match self {
            SeqExp::Imm(imm, a) => SeqExp::Imm(imm.clone(), f(a)),
            SeqExp::Prim1(op, imm, a) => SeqExp::Prim1(*op, imm.clone(), f(a)),
            SeqExp::Prim2(op, imm1, imm2, a) => {
                SeqExp::Prim2(*op, imm1.clone(), imm2.clone(), f(a))
            }
            SeqExp::ArraySet {
                array,
                index,
                new_value,
                ann,
            } => SeqExp::ArraySet {
                array: array.clone(),
                index: index.clone(),
                new_value: new_value.clone(),
                ann: f(ann),
            },
            SeqExp::Array(is, a) => SeqExp::Array(is.iter().map(|i| i.clone()).collect(), f(a)),
            SeqExp::MakeClosure {
                arity,
                label,
                env,
                ann,
            } => SeqExp::MakeClosure {
                arity: *arity,
                label: label.clone(),
                env: env.clone(),
                ann: f(ann),
            },
            SeqExp::CallClosure { fun, args, ann } => SeqExp::CallClosure {
                fun: fun.clone(),
                args: args.iter().map(|i| i.clone()).collect(),
                ann: f(ann),
            },
            SeqExp::Let {
                var,
                bound_exp,
                body,
                ann,
            } => SeqExp::Let {
                var: var.clone(),
                bound_exp: Box::new(bound_exp.map_ann(f)),
                body: Box::new(body.map_ann(f)),
                ann: f(ann),
            },
            SeqExp::If {
                cond,
                thn,
                els,
                ann,
            } => SeqExp::If {
                cond: cond.clone(),
                thn: Box::new(thn.map_ann(f)),
                els: Box::new(els.map_ann(f)),
                ann: f(ann),
            },
        }
    }
}

impl<Ann> FunDecl<Exp<Ann>, Ann> {
    pub fn map_ann<Ann2, F>(&self, f: &mut F) -> FunDecl<Exp<Ann2>, Ann2>
    where
        F: FnMut(&Ann) -> Ann2,
    {
        FunDecl {
            name: self.name.clone(),
            parameters: self.parameters.clone(),
            body: self.body.map_ann(f),
            ann: f(&self.ann),
        }
    }
}

impl<Ann> SeqProg<Ann> {
    pub fn map_ann<Ann2, F>(&self, f: &mut F) -> SeqProg<Ann2>
    where
        F: FnMut(&Ann) -> Ann2,
    {
        SeqProg {
            funs: self.funs.iter().map(|d| d.map_ann(f)).collect(),
            main: self.main.map_ann(f),
            ann: f(&self.ann),
        }
    }
}
impl<Ann> FunDecl<SeqExp<Ann>, Ann> {
    pub fn map_ann<Ann2, F>(&self, f: &mut F) -> FunDecl<SeqExp<Ann2>, Ann2>
    where
        F: FnMut(&Ann) -> Ann2,
    {
        FunDecl {
            name: self.name.clone(),
            parameters: self.parameters.clone(),
            body: self.body.map_ann(f),
            ann: f(&self.ann),
        }
    }
}
