-- Chapter 10: a stack machine with a typed stack.
import Pond
open Critter

inductive Ty where
  | nat | bool

abbrev Ty.denote : Ty → Type
  | .nat  => Nat
  | .bool => Bool

-- ANCHOR: stack
inductive Stack : List Ty → Type where
  | nil  : Stack []
  | push : t.denote → Stack s →
           Stack (t :: s)
-- ANCHOR_END: stack

-- ANCHOR: stackex
#check (Stack.push 5 (.push true .nil) :
  Stack [.nat, .bool])
-- ANCHOR_END: stackex

-- ANCHOR: instr
inductive Instr :
    List Ty → List Ty → Type where
  | push : t.denote → Instr s (t :: s)
  | add  : Instr (.nat :: .nat :: s) (.nat :: s)
  | le   : Instr (.nat :: .nat :: s) (.bool :: s)
  | pick : Instr (t :: t :: .bool :: s) (t :: s)
-- ANCHOR_END: instr

-- ANCHOR: prog
inductive Prog :
    List Ty → List Ty → Type where
  | nil  : Prog s s
  | cons : Instr s m → Prog m r → Prog s r
-- ANCHOR_END: prog

-- ANCHOR: step
def step : Instr s r → Stack s → Stack r
  | .push v, st => .push v st
  | .add, .push x (.push y st) =>
    .push (y + x) st
  | .le, .push x (.push y st) =>
    .push (decide (y ≤ x)) st
  | .pick, .push x (.push y (.push c st)) =>
    .push (if c then y else x) st
-- ANCHOR_END: step

-- ANCHOR: run
def run : Prog s r → Stack s → Stack r
  | .nil, st => st
  | .cons i p, st => run p (step i st)
-- ANCHOR_END: run

-- ANCHOR: top
def Stack.top : Stack (t :: s) → t.denote
  | .push v _ => v
-- ANCHOR_END: top

-- ANCHOR: five
def five : Prog [] [.nat] :=
  .cons (.push 2)
    (.cons (.push 3)
      (.cons .add .nil))

#eval (run five .nil).top
-- ANCHOR_END: five
