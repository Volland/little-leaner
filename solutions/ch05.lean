-- Solutions to the exercises of Chapter 5.
import Pond
open Critter
set_option pp.fieldNotation false

inductive N where
  | zero
  | succ (n : N)

open N

def N.add : N → N → N
  | m, zero   => m
  | m, succ n => succ (add m n)

inductive Chain :
    Nat → Critter → Critter → Prop where
  | step : Eats x y → Chain 1 x y
  | trans : Eats x y → Chain n y z →
      Chain (n + 1) x z

-- ANCHOR: ex1
-- The otter eats fish; the fish eats snails.
example : Chain 2 otter snail := by
  apply Chain.trans Eats.otter_fish
  trace_state
  exact Chain.step Eats.fish_snail
-- The goal after the first apply is
-- Chain 1 fish snail: Lean worked out
-- that n + 1 = 2 means n = 1.
-- ANCHOR_END: ex1

-- ANCHOR: ex2
def N.mul : N → N → N
  | _, zero   => zero
  | m, succ n => add (mul m n) m

-- mul looks at its second argument,
-- so this one holds by computing.
example (n : N) : mul n zero = zero := by
  rfl

-- Here the second argument is n, which is
-- stuck, so we need induction on n.
example (n : N) : mul zero n = zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    trace_state
    -- add (mul zero n) zero computes to
    -- mul zero n, which ih says is zero.
    exact ih
-- ANCHOR_END: ex2

-- ANCHOR: ex3
-- Induction on c: add recurses on its
-- second argument, and c is the second
-- argument of the outer add on both sides.
theorem N.add_assoc (a b c : N) :
    add (add a b) c = add a (add b c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    trace_state
    exact congrArg succ ih
-- ANCHOR_END: ex3

-- ANCHOR: ex4
-- Induction on the first chain. Its length
-- m is the second argument of n + m, so
-- n + (k + 1) computes to (n + k) + 1,
-- which is what Chain.trans gives.
-- With m + n the lengths would not match
-- by computing alone.
theorem Chain.join (h1 : Chain m x y) :
    Chain n y z → Chain (n + m) x z := by
  induction h1 with
  | step e =>
    intro h2
    exact Chain.trans e h2
  | trans e c ih =>
    intro h2
    exact Chain.trans e (ih h2)
-- ANCHOR_END: ex4
