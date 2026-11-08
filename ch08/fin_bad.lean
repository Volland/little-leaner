-- expect: error
-- Chapter 8: positions out of range, lengths that differ.
import Pond
open Critter

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

open Vec

def replicate : (n : Nat) → α → Vec α n
  | 0,     _ => nil
  | n + 1, x => cons x (replicate n x)

def zip : Vec α n → Vec β n → Vec (α × β) n
  | nil,       nil       => nil
  | cons x xs, cons y ys =>
    cons (x, y) (zip xs ys)

def chain : Vec Critter 3 :=
  cons heron (cons frog (cons fly nil))

-- ANCHOR: five
def five : Fin 3 := ⟨5, by decide⟩
-- ANCHOR_END: five

-- ANCHOR: zipBad
#check zip chain (replicate 2 snail)
-- ANCHOR_END: zipBad
