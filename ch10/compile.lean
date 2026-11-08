-- Chapter 10: a compiler, and its proof.
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

def caught : Expr .nat :=
  .plus (.lit 2) (.lit 3)

def enough : Expr .bool :=
  .le (.lit 4) caught

def snack : Expr .nat :=
  .ite enough caught (.lit 0)

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

-- ANCHOR: join
def join : Prog s m → Prog m r → Prog s r
  | .nil, q      => q
  | .cons i p, q => .cons i (join p q)
-- ANCHOR_END: join

-- ANCHOR: one
def one (i : Instr s r) : Prog s r :=
  .cons i .nil
-- ANCHOR_END: one

-- ANCHOR: run_join
theorem run_join (p : Prog s m)
    (q : Prog m r) (st : Stack s) :
    run (join p q) st
      = run q (run p st) := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    exact ih q (step i st)
-- ANCHOR_END: run_join

-- ANCHOR: compile
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
-- ANCHOR_END: compile

-- ANCHOR: snack
#eval (run (compile snack) .nil).top
-- ANCHOR_END: snack

-- ANCHOR: snack_rfl
example : run (compile snack) .nil
    = push (eval snack) .nil := rfl
-- ANCHOR_END: snack_rfl

-- ANCHOR: correct
-- ANCHOR: statement
theorem compile_correct (e : Expr t)
    (st : Stack s) :
    run (compile e) st
      = push (eval e) st := by
-- ANCHOR_END: statement
  induction e generalizing s with
  -- ANCHOR: lit_case
  | lit n =>
    -- ANCHOR: lit_goal
    trace_state
    -- ANCHOR_END: lit_goal
    rfl
  -- ANCHOR_END: lit_case
  | tt => rfl
  | ff => rfl
  -- ANCHOR: plus_case
  | plus a b iha ihb =>
    -- ANCHOR: plus_goal
    trace_state
    -- ANCHOR_END: plus_goal
    -- ANCHOR: plus_rw1
    rw [compile, run_join, run_join]
    -- ANCHOR_END: plus_rw1
    -- ANCHOR: plus_join
    trace_state
    -- ANCHOR_END: plus_join
    -- ANCHOR: plus_rw2
    rw [iha, ihb]
    -- ANCHOR_END: plus_rw2
    -- ANCHOR: plus_ih
    trace_state
    -- ANCHOR_END: plus_ih
    rfl
  -- ANCHOR_END: plus_case
  | le a b iha ihb =>
    rw [compile, run_join, run_join]
    rw [iha, ihb]
    rfl
  -- ANCHOR: ite_case
  | ite c a b ihc iha ihb =>
    rw [compile, run_join, run_join]
    rw [run_join, ihc, iha, ihb]
    -- ANCHOR: ite_goal
    trace_state
    -- ANCHOR_END: ite_goal
    rfl
  -- ANCHOR_END: ite_case
-- ANCHOR_END: correct
