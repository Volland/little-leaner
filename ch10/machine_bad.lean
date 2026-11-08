-- expect: error
-- Chapter 10: instructions that do not fit.
import Pond
open Critter

inductive Ty where
  | nat | bool

abbrev Ty.denote : Ty → Type
  | .nat  => Nat
  | .bool => Bool

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

-- ANCHOR: empty
def oops : Prog [] [.nat] :=
  .cons .add .nil
-- ANCHOR_END: empty

-- ANCHOR: mixed
def mixed : Prog [] [.nat] :=
  .cons (.push 2)
    (.cons (.push true)
      (.cons .add .nil))
-- ANCHOR_END: mixed
