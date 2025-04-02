#![allow(unused)]

// https://okmij.org/ftp/ML/generalization/sound_eager.ml

use std::{
    cell::{Cell, RefCell},
    rc::Rc,
};

use Exp::*;
use Tv::*;
use Typ::*;

type Varname = String;

enum Exp {
    Var(Varname),
    App(Box<Exp>, Box<Exp>),
    Lam(String, Box<Exp>),
    Let(String, Box<Exp>, Box<Exp>),
}

type QName = String;

enum Typ {
    TVar(Rc<RefCell<Tv>>),
    QVar(QName),
    TArrow(Rc<Typ>, Rc<Typ>),
}

enum Tv {
    Unbound(String, i32),
    Link(Rc<Typ>),
}

impl std::fmt::Debug for Typ {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TVar(tvr) => {
                write!(f, "{:?}", tvr.borrow())
            }
            QVar(name) => write!(f, "QVar({:?})", name),
            TArrow(ty1, ty2) => write!(f, "({:?} -> {:?})", ty1, ty2),
        }
    }
}

impl std::fmt::Debug for Tv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Unbound(name, level) => write!(f, "{}^{}", name, level),
            Link(ty) => write!(f, "{:?}", ty),
        }
    }
}

fn occurs(tvr: &Rc<RefCell<Tv>>, typ: &Typ) {
    match typ {
        TVar(tvr2) => {
            if Rc::ptr_eq(tvr, tvr2) {
                panic!("occurs check")
            }
            if is_bound(tvr2) {
                let (name, min_level) = match &*tvr2.borrow() {
                    Unbound(name, l2) => {
                        let min_level = match &*tvr.borrow() {
                            Unbound(_, l) => (*l).min(*l2),
                            _ => *l2,
                        };
                        (name.clone(), min_level)
                    }
                    Link(_) => unreachable!(),
                };
                *tvr2.borrow_mut() = Unbound(name, min_level);
            } else {
                match &*tvr2.borrow() {
                    Link(ty) => occurs(tvr, ty),
                    _ => unreachable!(),
                }
            }
        }
        TArrow(t1, t2) => {
            occurs(tvr, t1);
            occurs(tvr, t2);
        }
        _ => (),
    }
}

fn is_link(tvr: &Rc<RefCell<Tv>>) -> bool {
    match &*tvr.borrow() {
        Unbound(..) => false,
        Link(_) => true,
    }
}

fn is_bound(tvr: &Rc<RefCell<Tv>>) -> bool {
    !is_link(tvr)
}

fn unify(t1: &Rc<Typ>, t2: &Rc<Typ>) {
    if Rc::ptr_eq(t1, t2) {
        return;
    }

    match (&**t1, &**t2) {
        (TVar(tvr), _) if is_link(tvr) => {
            let linked_ty = {
                match &*tvr.borrow() {
                    Link(t) => t.clone(),
                    _ => unreachable!(),
                }
            };
            unify(&linked_ty, t2);
        }
        (_, TVar(tvr)) if is_link(tvr) => {
            let linked_ty = {
                match &*tvr.borrow() {
                    Link(t) => t.clone(),
                    _ => unreachable!(),
                }
            };
            unify(&linked_ty, t1);
        }
        (TVar(tvr), _) if is_bound(tvr) => {
            occurs(tvr, t2);
            *tvr.borrow_mut() = Link(t2.clone());
        }
        (_, TVar(tvr)) if is_bound(tvr) => {
            occurs(tvr, t1);
            *tvr.borrow_mut() = Link(t1.clone());
        }
        (TArrow(tyl1, tyl2), TArrow(tyr1, tyr2)) => {
            unify(tyl1, tyr1);
            unify(tyl2, tyr2);
        }
        _ => {
            panic!("unification failed: {:?} and {:?}", t1, t2);
        }
    }
}

struct Typer {
    counter: Cell<i32>,
    level: Cell<i32>,
}

impl Typer {
    pub fn new() -> Self {
        Typer {
            counter: Cell::new(0),
            level: Cell::new(1),
        }
    }
    fn gensym(&self) -> String {
        let id = self.counter.get();
        self.counter.set(id + 1);

        if id < 26 {
            ((b'a' + id as u8) as char).to_string()
        } else {
            format!("t{}", id)
        }
    }

    fn reset(&self) {
        self.reset_counter();
        self.reset_level();
    }

    fn reset_counter(&self) {
        self.counter.set(0);
    }

    fn reset_level(&self) {
        self.level.set(1);
    }

    fn enter_level(&self) {
        self.level.set(self.level.get() + 1);
    }

    fn leave_level(&self) {
        self.level.set(self.level.get() - 1);
    }

    fn current_level(&self) -> i32 {
        self.level.get()
    }
}

impl Typer {
    fn newvar(&self) -> Rc<Typ> {
        Rc::new(TVar(Rc::new(RefCell::new(Unbound(
            self.gensym(),
            self.current_level(),
        )))))
    }

    fn gen(&self, t: &Rc<Typ>) -> Rc<Typ> {
        match &**t {
            TVar(tvr) => match &*tvr.borrow() {
                Unbound(name, l) if *l > self.current_level() => Rc::new(QVar(name.into())),
                Unbound(..) => t.clone(),
                Link(ty) => self.gen(ty),
            },
            TArrow(ty1, ty2) => Rc::new(TArrow(self.gen(ty1), self.gen(ty2))),
            _ => t.clone(),
        }
    }

    fn inst(&self, t: &Rc<Typ>) -> Rc<Typ> {
        fn go(typer: &Typer, t: &Rc<Typ>, subst: &mut im::HashMap<QName, Rc<Typ>>) -> Rc<Typ> {
            match &**t {
                QVar(name) => {
                    if let Some(ty) = subst.get(name) {
                        ty.clone()
                    } else {
                        let tv = typer.newvar();
                        subst.insert(name.clone(), tv.clone());
                        tv
                    }
                }
                TVar(tvr) => match &*tvr.borrow() {
                    Unbound(..) => t.clone(),
                    Link(ty) => go(typer, ty, subst),
                },
                TArrow(ty1, ty2) => {
                    let ty1_inst = go(typer, ty1, subst);
                    let ty2_inst = go(typer, ty2, subst);
                    Rc::new(Typ::TArrow(ty1_inst, ty2_inst))
                }
            }
        }
        let mut subst = im::HashMap::new();
        go(self, t, &mut subst)
    }

    fn typof(&self, env: im::HashMap<Varname, Rc<Typ>>, e: &Exp) -> Rc<Typ> {
        match e {
            Var(x) => {
                let ty = env.get(x).unwrap();
                self.inst(ty)
            }
            Lam(x, e) => {
                let ty_x = self.newvar();
                let ty_e = self.typof(env.update(x.clone(), ty_x.clone()), e);
                Rc::new(TArrow(ty_x, ty_e))
            }
            App(e1, e2) => {
                let ty_fun = self.typof(env.clone(), e1);
                let ty_arg = self.typof(env, e2);
                let ty_res = self.newvar();
                let ty_arrow = Rc::new(TArrow(ty_arg, ty_res.clone()));
                unify(&ty_fun, &ty_arrow);
                ty_res
            }
            Let(x, e, e2) => {
                self.enter_level();
                let ty_e = self.typof(env.clone(), e);
                self.leave_level();
                self.typof(env.update(x.clone(), self.gen(&ty_e)), e2)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use expect_test::{expect, Expect};

    use super::*;

    fn var(x: &str) -> Exp {
        Exp::Var(x.into())
    }

    fn lam(x: &str, e: Exp) -> Exp {
        Exp::Lam(x.into(), Box::new(e))
    }

    fn app(e1: Exp, e2: Exp) -> Exp {
        Exp::App(Box::new(e1), Box::new(e2))
    }

    fn let_(x: &str, e1: Exp, e2: Exp) -> Exp {
        Exp::Let(x.into(), Box::new(e1), Box::new(e2))
    }

    fn check(e: &Exp, expect: Expect) {
        let typer = Typer::new();
        let env = im::HashMap::new();
        let t = typer.typof(env, e);
        expect.assert_debug_eq(&t);
    }

    #[test]
    fn test_001() {
        // (* # fun x -> x;;
        //     - : 'a -> 'a = <fun> *)
        let id = lam("x", var("x"));
        check(
            &id,
            expect![[r#"
                (a^1 -> a^1)
            "#]],
        );
    }

    #[test]
    fn test_002() {
        // (* # fun x -> fun y -> x y;;
        //     - : ('a -> 'b) -> 'a -> 'b = <fun> *)
        let c = lam("x", lam("y", app(var("x"), var("y"))));
        check(
            &c,
            expect![[r#"
                ((b^1 -> c^1) -> (b^1 -> c^1))
            "#]],
        );
    }

    #[test]
    fn test_003() {
        // # let x = fun x -> fun y -> x y in x;;
        //   - : ('a -> 'b) -> 'a -> 'b = <fun>
        let e = let_("x", lam("x", lam("y", app(var("x"), var("y")))), var("x"));
        check(
            &e,
            expect![[r#"
                ((d^1 -> e^1) -> (d^1 -> e^1))
            "#]],
        );
    }

    #[test]
    fn test_004() {
        // (* # let y = fun z -> z in y;;
        //     - : 'a -> 'a = <fun> *)
        let e = let_("y", lam("z", var("z")), var("y"));
        check(
            &e,
            expect![[r#"
                (b^1 -> b^1)
            "#]],
        );
    }

    #[test]
    fn test_005() {
        // (* # fun x -> let y = fun z -> z in y;;
        //     - : 'a -> 'b -> 'b = <fun> *)
        let e = lam("x", let_("y", lam("z", var("z")), var("y")));
        check(
            &e,
            expect![[r#"
                (a^1 -> (c^1 -> c^1))
            "#]],
        );
    }

    #[test]
    fn test_006() {
        // (* # fun x -> let y = fun z -> z in y x;;
        //     - : 'a -> 'a = <fun> *)
        let e = lam("x", let_("y", lam("z", var("z")), app(var("y"), var("x"))));
        check(
            &e,
            expect![[r#"
                (d^1 -> d^1)
            "#]],
        );
    }

    #[test]
    #[should_panic]
    fn test_007() {
        // fun x -> x x;;
        // error
        let e = lam("x", app(var("x"), var("x")));
        check(&e, expect![]);
    }

    #[test]
    #[should_panic]
    fn test_008() {
        // let x = x in x
        // Error: Unbound value x
        let e = let_("x", var("x"), var("x"));
        check(&e, expect![]);
    }

    #[test]
    #[should_panic]
    fn test_009() {
        // (* Max Heiber's example *)
        // (* # fun y -> y (fun z -> y z);;
        //                             ˉ
        //    Error: This expression has type 'a but an expression was expected of type
        //             'a -> 'b
        //           The type variable 'a occurs inside 'a -> 'b *)
        let e = lam("y", app(var("y"), lam("z", app(var("y"), var("z")))));
        check(&e, expect![]);
    }

    #[test]
    fn test_010() {
        //    Example illustrating the problem pointed out by kirang
        //     spurious occurs-check
        //     # fun x -> fun y -> fun k -> k (k x y) (k y x);;
        //     - : 'a -> 'a -> ('a -> 'a -> 'a) -> 'a = <fun>
        let e = lam(
            "x",
            lam(
                "y",
                lam(
                    "k",
                    app(
                        app(var("k"), app(app(var("k"), var("x")), var("y"))),
                        app(app(var("k"), var("y")), var("x")),
                    ),
                ),
            ),
        );
        check(
            &e,
            expect![[r#"
                (i^1 -> (i^1 -> ((i^1 -> (i^1 -> i^1)) -> i^1)))
            "#]],
        );
    }

    #[test]
    fn test_011() {
        // (* id can be `self-applied', on the surface of it *)
        // (* # let id = fun x -> x in id id;;
        //    - : '_weak1 -> '_weak1 = <fun> *)
        let e = let_("id", lam("x", var("x")), app(var("id"), var("id")));
        check(
            &e,
            expect![[r#"
                (c^1 -> c^1)
            "#]],
        );
    }

    #[test]
    // (* # let x = c1 in let y = let z = x id in z in y;;
    //     - : '_weak2 -> '_weak2 = <fun> *)
    fn test_012() {
        let id = lam("x", var("x"));
        let c1 = lam("x", lam("y", app(var("x"), var("y"))));
        let e = let_(
            "x",
            c1,
            let_("y", let_("z", app(var("x"), id), var("z")), var("y")),
        );
        check(
            &e,
            expect![[r#"
                (i^1 -> i^1)
            "#]],
        );
    }

    #[test]
    // (* fun x -> fun y -> let x = x y in fun x -> y x;;
    //     - : (('a -> 'b) -> 'c) -> ('a -> 'b) -> 'a -> 'b = <fun>
    //  *)
    fn test_013() {
        let e = lam(
            "x",
            lam(
                "y",
                let_(
                    "x",
                    app(var("x"), var("y")),
                    lam("x", app(var("y"), var("x"))),
                ),
            ),
        );
        check(
            &e,
            expect![[r#"
                (((d^1 -> e^1) -> c^1) -> ((d^1 -> e^1) -> (d^1 -> e^1)))
            "#]],
        );
    }

    #[test]
    // (* # fun x -> let y = x in y;;
    //     - : 'a -> 'a = <fun> *)
    fn test_014() {
        let e = lam("x", let_("y", var("x"), var("y")));
        check(
            &e,
            expect![[r#"
                (a^1 -> a^1)
            "#]],
        );
    }

    #[test]
    // (* # fun x -> let y = fun z -> x in y;;
    //     - : 'a -> 'b -> 'a = <fun> *)
    fn test_015() {
        let e = lam("x", let_("y", lam("z", var("x")), var("y")));
        check(
            &e,
            expect![[r#"
                (a^1 -> (c^1 -> a^1))
            "#]],
        );
    }

    #[test]
    // (* # fun x -> let y = fun z -> x z in y;;
    //     - : ('a -> 'b) -> 'a -> 'b = <fun> *)
    fn test_016() {
        let e = lam("x", let_("y", lam("z", app(var("x"), var("z"))), var("y")));
        check(
            &e,
            expect![[r#"
                ((b^1 -> c^1) -> (b^1 -> c^1))
            "#]],
        );
    }

    #[test]
    // (* # fun x -> fun y -> let x = x y in x y;;
    //     - : ('a -> 'a -> 'b) -> 'a -> 'b = <fun> *)
    fn test_017() {
        let e = lam(
            "x",
            lam(
                "y",
                let_("x", app(var("x"), var("y")), app(var("x"), var("y"))),
            ),
        );
        check(
            &e,
            expect![[r#"
                ((b^1 -> (b^1 -> d^1)) -> (b^1 -> d^1))
            "#]],
        );
    }

    #[test]
    #[should_panic]
    // (* # fun x -> let y = x in y y;;
    //     ~
    // Error: This expression has type 'a -> 'b but an expression was expected of type
    // 'a
    // The type variable 'a occurs inside 'a -> 'b *)
    fn test_018() {
        let e = lam("x", let_("y", var("x"), app(var("y"), var("y"))));
        check(&e, expect![]);
    }

    #[test]
    // (* fun x -> let y = let z = x (fun x -> x) in z in y;;
    // - : (('a -> 'a) -> 'b) -> 'b = <fun>
    // *)
    fn test_019() {
        let e = lam(
            "x",
            let_(
                "y",
                let_("z", app(var("x"), lam("x", var("x"))), var("z")),
                var("y"),
            ),
        );
        check(
            &e,
            expect![[r#"
                (((b^1 -> b^1) -> c^1) -> c^1)
            "#]],
        );
    }
}
