#![allow(dead_code)]

use std::collections::HashMap;

type Sub = HashMap<LVar, Term>;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
struct LVar(usize);

impl LVar {
    fn new(id: usize) -> Self {
        Self(id)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum Term {
    Int(isize),
    Str(String),
    Var(LVar),
    List(Vec<Term>),
}

impl Term {
    fn list_from<const N: usize>(arr: [Term; N]) -> Term {
        Term::List(arr.into_iter().collect::<Vec<_>>())
    }
}

#[derive(Debug, Clone)]
enum Goal {
    Equal(Term, Term),
    Both(Box<Goal>, Box<Goal>),
    Either(Box<Goal>, Box<Goal>),
}

fn equal(t1: Term, t2: Term) -> Goal {
    Goal::Equal(t1, t2)
}

fn both(g1: Goal, g2: Goal) -> Goal {
    Goal::Both(Box::new(g1), Box::new(g2))
}

fn either(g1: Goal, g2: Goal) -> Goal {
    Goal::Either(Box::new(g1), Box::new(g2))
}

fn interpret(goal: Goal, sub: Sub) -> Vec<Sub> {
    match goal {
        Goal::Equal(t1, t2) => match unify(t1, t2, &mut sub.clone()) {
            Some(sub) => vec![sub.clone()],
            None => vec![],
        },
        Goal::Both(g1, g2) => interpret(*g1, sub)
            .into_iter()
            .flat_map(|s| interpret(*g2.clone(), s))
            .collect(),
        Goal::Either(g1, g2) => {
            let mut subs = interpret(*g1, sub.clone());
            let mut subs_other = interpret(*g2, sub.clone());
            subs.append(&mut subs_other);
            subs
        }
    }
}

fn extend(sub: &mut Sub, var: LVar, term: Term) {
    sub.insert(var, term);
}

fn walk(term: Term, sub: &Sub) -> Term {
    match term {
        Term::Var(var) => match sub.get(&var) {
            Some(t) => walk(t.clone(), sub),
            None => term,
        },
        _ => term,
    }
}

// TODO: Can this work for any type that implements equality (Eq, PartialEq??)?
// What about matching on vectors (see slice patterns)?
fn unify(term1: Term, term2: Term, sub: &mut Sub) -> Option<&mut Sub> {
    let wterm1 = walk(term1, sub);
    let wterm2 = walk(term2, sub);

    match (wterm1, wterm2) {
        (t1, t2) if t1 == t2 => Some(sub),
        (Term::Var(var), t) => {
            extend(sub, var, t.clone());
            Some(sub)
        }
        (t, Term::Var(var)) => {
            extend(sub, var, t.clone());
            Some(sub)
        }
        (Term::List(mut vec1), Term::List(mut vec2)) if !vec1.is_empty() && !vec2.is_empty() => {
            let h1 = vec1.pop().unwrap();
            let h2 = vec2.pop().unwrap();
            match unify(h1.clone(), h2.clone(), sub) {
                Some(s) => unify(Term::List(vec1.clone()), Term::List(vec2.clone()), s),
                None => None,
            }
        }
        _ => None,
    }
}

fn present<const N: usize>(goal: Goal, vars: [LVar; N]) -> Vec<Vec<Term>> {
    let sub = HashMap::new();
    interpret(goal, sub)
        .into_iter()
        .map(|s| present_sub(vars, &s))
        .collect()
}

fn present_sub<const N: usize>(vars: [LVar; N], sub: &Sub) -> Vec<Term> {
    vars.into_iter()
        .map(|v| {
            if sub.contains_key(&v) {
                simplify(Term::Var(v), &sub)
            } else {
                Term::Var(v)
            }
        })
        .collect()
}

fn simplify(term: Term, sub: &Sub) -> Term {
    match walk(term, sub) {
        Term::List(mut vec) if !vec.is_empty() => {
            let h = vec.pop().unwrap();
            if let Term::List(mut v) = simplify(Term::List(vec), sub) {
                v.push(simplify(h, sub));
                Term::List(v)
            } else {
                todo!("Shouldn't be able to get here!")
            }
        }
        t => t,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn terms_sub_and_walk() {
        let x = LVar::new(0);
        let y = LVar::new(1);
        let mut sub = Sub::new();
        extend(&mut sub, x, Term::Int(1));
        extend(&mut sub, y, Term::Var(x));
        assert_eq!(Term::Int(1), walk(Term::Var(x), &sub));
        assert_eq!(Term::Int(1), walk(Term::Var(y), &sub));
        assert_eq!(Term::Int(1), walk(Term::Int(1), &sub));
    }

    #[test]
    fn unify_vars() {
        let x = LVar::new(0);
        let y = LVar::new(1);
        let mut sub = Sub::new();
        unify(Term::Var(x), Term::Var(y), &mut sub);
        unify(Term::Var(x), Term::Int(1), &mut sub);
        let soln = simplify(Term::list_from([Term::Var(x), Term::Var(y)]), &sub);
        assert_eq!(Term::list_from([Term::Int(1), Term::Int(1)]), soln)
    }

    #[test]
    fn unify_lists() {
        let x = LVar::new(0);
        let y = LVar::new(1);
        let t1 = Term::list_from([Term::Var(x), Term::Int(2)]);
        let t2 = Term::list_from([Term::Int(1), Term::Var(y)]);
        let mut sub = Sub::new();
        let sub = unify(t1, t2, &mut sub).unwrap();
        let soln = simplify(Term::list_from([Term::Var(x), Term::Var(y)]), sub);
        assert_eq!(Term::list_from([Term::Int(1), Term::Int(2)]), soln);
    }

    #[test]
    fn interpret_equal() {
        let x = LVar::new(0);
        let sub = Sub::new();
        let goal = Goal::Equal(Term::Var(x), Term::Int(1));
        let subs = interpret(goal, sub);
        let solns: Vec<_> = subs.iter().map(|s| simplify(Term::Var(x), s)).collect();
        assert_eq!(vec![Term::Int(1)], solns);
    }

    #[test]
    fn present_both() {
        let x = LVar::new(0);
        let y = LVar::new(1);
        let goal1 = Goal::Equal(Term::Var(x), Term::Int(1));
        let goal2 = Goal::Equal(Term::Var(y), Term::Var(x));
        let both = Goal::Both(Box::new(goal1), Box::new(goal2));
        let pres = present(both, [x, y]);
        assert_eq!(vec![vec![Term::Int(1), Term::Int(1)]], pres);
    }

    #[test]
    fn inconsistent_assignment() {
        use Goal::*;
        let x = LVar::new(0);
        let goal = Both(
            Box::new(Equal(Term::Var(x), Term::Int(1))),
            Box::new(Equal(Term::Var(x), Term::Int(2))),
        );
        assert_eq!(Vec::<Vec<Term>>::new(), present(goal, [x]));
    }

    #[test]
    fn either_value() {
        use Goal::*;
        let x = LVar::new(0);
        let eq1 = Equal(Term::Var(x), Term::Int(1));
        let eq2 = Equal(Term::Var(x), Term::Int(2));
        let goal = Either(Box::new(eq1), Box::new(eq2));
        assert_eq!(
            vec![vec![Term::Int(1)], vec![Term::Int(2)]],
            present(goal, [x])
        );
    }

    #[test]
    fn goal_shorthand_funcs() {
        use Term::*;
        let x = LVar::new(0);
        let y = LVar::new(1);
        let goal = either(
            equal(
                Term::list_from([Var(x), Var(y)]),
                Term::list_from([Int(1), Int(2)]),
            ),
            equal(
                Term::list_from([Var(y), Var(x)]),
                Term::list_from([Int(3), Int(4)]),
            ),
        );
        assert_eq!(
            vec![vec![Int(1), Int(2)], vec![Int(4), Int(3)]],
            present(goal, [x, y])
        );
    }
}
