-- Solutions to the exercises of Chapter 10.
import Pond
open Critter

inductive Ty where
  | nat | bool

abbrev Ty.denote : Ty → Type
  | .nat  => Nat
  | .bool => Bool

inductive Expr : Ty → Type where
  | lit  : Nat → Expr .nat
  | tt   : Expr .bool
  | ff   : Expr .bool
  | plus : Expr .nat → Expr .nat → Expr .nat
  | le   : Expr .nat → Expr .nat →
           Expr .bool
  | ite  : Expr .bool → Expr t → Expr t →
           Expr t

def eval : Expr t → t.denote
  | .lit n      => n
  | .tt         => true
  | .ff         => false
  | .plus a b   => eval a + eval b
  | .le a b     => decide (eval a ≤ eval b)
  | .ite c a b  =>
    if eval c then eval a else eval b

inductive Stack : List Ty → Type where
  | nil  : Stack []
  | push : t.denote → Stack s →
           Stack (t :: s)

inductive Instr :
    List Ty → List Ty → Type where
  | push : t.denote → Instr s (t :: s)
  | add  : Instr (.nat :: .nat :: s) (.nat :: s)
  | le   : Instr (.nat :: .nat :: s) (.bool :: s)
  | pick : Instr (t :: t :: .bool :: s) (t :: s)

inductive Prog :
    List Ty → List Ty → Type where
  | nil  : Prog s s
  | cons : Instr s m → Prog m r → Prog s r

def step : Instr s r → Stack s → Stack r
  | .push v, st => .push v st
  | .add, .push x (.push y st) =>
    .push (y + x) st
  | .le, .push x (.push y st) =>
    .push (decide (y ≤ x)) st
  | .pick, .push x (.push y (.push c st)) =>
    .push (if c then y else x) st

def run : Prog s r → Stack s → Stack r
  | .nil, st => st
  | .cons i p, st => run p (step i st)

def Stack.top : Stack (t :: s) → t.denote
  | .push v _ => v

open Stack

def join : Prog s m → Prog m r → Prog s r
  | .nil, q      => q
  | .cons i p, q => .cons i (join p q)

def one (i : Instr s r) : Prog s r :=
  .cons i .nil


def compile : Expr t → Prog s (t :: s)
  | .lit n => one (.push n)
  | .tt    => one (.push true)
  | .ff    => one (.push false)
  | .plus a b =>
    join (compile a)
      (join (compile b) (one .add))
  | .le a b =>
    join (compile a)
      (join (compile b) (one .le))
  | .ite c a b =>
    join (compile c)
      (join (compile a)
        (join (compile b) (one .pick)))

theorem run_join (p : Prog s m)
    (q : Prog m r) (st : Stack s) :
    run (join p q) st
      = run q (run p st) := by
  induction p with
  | nil => rfl
  | cons i p ih => exact ih q (step i st)

theorem compile_correct (e : Expr t)
    (st : Stack s) :
    run (compile e) st
      = push (eval e) st := by
  induction e generalizing s with
  | lit n => rfl
  | tt => rfl
  | ff => rfl
  | plus a b iha ihb =>
    rw [compile, run_join, run_join, iha, ihb]
    rfl
  | le a b iha ihb =>
    rw [compile, run_join, run_join, iha, ihb]
    rfl
  | ite c a b ihc iha ihb =>
    rw [compile, run_join, run_join, run_join]
    rw [ihc, iha, ihb]
    rfl

-- ANCHOR: ex1
def few : Expr .bool :=
  .le (.plus (.lit 2) (.lit 2)) (.lit 3)

#eval eval few
#eval (run (compile few) .nil).top
-- Both say false: 2 + 2 = 4 is not at most 3.
-- `.le .tt (.lit 3)` is refused by `#check`,
-- before anything runs: `le` wants an
-- `Expr .nat`, and `.tt` is an `Expr .bool`.
-- ANCHOR_END: ex1

-- ANCHOR: ex2
-- Rewrite with the big theorem, then compute
-- `top` of a `push`. Two tactics: `rw`, `rfl`.
-- What was in `st` does not matter: the value
-- of `e` lands on top of it either way.
theorem top_correct (e : Expr t)
    (st : Stack s) :
    (run (compile e) st).top = eval e := by
  rw [compile_correct]
  rfl
-- ANCHOR_END: ex2

-- ANCHOR: ex3
namespace Ex3

inductive Expr : Ty → Type where
  | lit  : Nat → Expr .nat
  | tt   : Expr .bool
  | ff   : Expr .bool
  | plus : Expr .nat → Expr .nat → Expr .nat
  | le   : Expr .nat → Expr .nat →
           Expr .bool
  | ite  : Expr .bool → Expr t → Expr t →
           Expr t
  | not  : Expr .bool → Expr .bool

def eval : Expr t → t.denote
  | .lit n      => n
  | .tt         => true
  | .ff         => false
  | .plus a b   => eval a + eval b
  | .le a b     => decide (eval a ≤ eval b)
  | .ite c a b  =>
    if eval c then eval a else eval b
  | .not a      =>
    if eval a then false else true

-- No new instruction: push false, push true,
-- and let `pick` choose with `a` on the stack.
def compile : Expr t → Prog s (t :: s)
  | .lit n => one (.push n)
  | .tt    => one (.push true)
  | .ff    => one (.push false)
  | .plus a b =>
    join (compile a)
      (join (compile b) (one .add))
  | .le a b =>
    join (compile a)
      (join (compile b) (one .le))
  | .ite c a b =>
    join (compile c)
      (join (compile a)
        (join (compile b) (one .pick)))
  | .not a =>
    join (compile a)
      (join (one (.push false))
        (join (one (.push true)) (one .pick)))

theorem compile_correct (e : Expr t)
    (st : Stack s) :
    run (compile e) st
      = push (eval e) st := by
  induction e generalizing s with
  | lit n => rfl
  | tt => rfl
  | ff => rfl
  | plus a b iha ihb =>
    rw [compile, run_join, run_join, iha, ihb]
    rfl
  | le a b iha ihb =>
    rw [compile, run_join, run_join, iha, ihb]
    rfl
  | ite c a b ihc iha ihb =>
    rw [compile, run_join, run_join, run_join]
    rw [ihc, iha, ihb]
    rfl
  | not a iha =>
    rw [compile, run_join, iha]
    rfl

#eval eval (.not (.le (.lit 4) (.lit 3)))

end Ex3
-- ANCHOR_END: ex3

-- ANCHOR: ex4
-- Add two expressions, folding two literals.
def add' : Expr .nat → Expr .nat → Expr .nat
  | .lit x, .lit y => .lit (x + y)
  | a, b           => .plus a b

def fold : Expr t → Expr t
  | .lit n     => .lit n
  | .tt        => .tt
  | .ff        => .ff
  | .plus a b  => add' (fold a) (fold b)
  | .le a b    => .le (fold a) (fold b)
  | .ite c a b =>
    .ite (fold c) (fold a) (fold b)

example : fold (.ite .tt
    (.plus (.lit 2) (.lit 3)) (.lit 0))
    = .ite .tt (.lit 5) (.lit 0) := rfl

-- `add'` keeps the meaning. Take `a` and `b`
-- apart (`cases`); in every case both sides
-- compute to the same number.
theorem add'_ok (a b : Expr .nat) :
    eval (add' a b) = eval a + eval b := by
  cases a <;> cases b <;> rfl

theorem fold_ok (e : Expr t) :
    eval (fold e) = eval e := by
  induction e with
  | lit n => rfl
  | tt => rfl
  | ff => rfl
  | plus a b iha ihb =>
    rw [fold, add'_ok, iha, ihb]
    rfl
  | le a b iha ihb =>
    rw [fold, eval, eval, iha, ihb]
  | ite c a b ihc iha ihb =>
    rw [fold, eval, eval, ihc, iha, ihb]

-- And the compiled code of `fold e` pushes the
-- same value as the code of `e`.
theorem fold_compile (e : Expr t)
    (st : Stack s) :
    run (compile (fold e)) st
      = run (compile e) st := by
  rw [compile_correct, compile_correct, fold_ok]
-- ANCHOR_END: ex4
