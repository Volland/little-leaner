-- Chapter 8: types that depend on arguments.
import Pond
open Critter

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

open Vec

def toList : Vec α n → List α
  | nil       => []
  | cons x xs => x :: toList xs

-- ANCHOR: replicate
def replicate : (n : Nat) → α → Vec α n
  | 0,     _ => nil
  | n + 1, x => cons x (replicate n x)
-- ANCHOR_END: replicate

-- ANCHOR: evalRep
#eval toList (replicate 3 snail)
-- ANCHOR_END: evalRep

-- ANCHOR: checkRep
#check replicate 3 snail
#check replicate 5 snail
-- ANCHOR_END: checkRep

-- ANCHOR: checkAt
#check @replicate
-- ANCHOR_END: checkAt

-- ANCHOR: snails
def snails : (n : Nat) → Vec Critter n :=
  fun n => replicate n snail
-- ANCHOR_END: snails

-- ANCHOR: piType
#check (n : Nat) → Vec Critter n
-- ANCHOR_END: piType

-- ANCHOR: arrow
#check Nat → Vec Critter 3
-- ANCHOR_END: arrow

-- ANCHOR: forall
#check (n : Nat) → n + 0 = n
-- ANCHOR_END: forall

-- ANCHOR: addZero
theorem add_zero' :
    (n : Nat) → n + 0 = n := by
  intro n
  rfl

#check add_zero' 5
-- ANCHOR_END: addZero

-- ANCHOR: noHeron
#check (c : Critter) → ¬ Eats c heron
-- ANCHOR_END: noHeron
