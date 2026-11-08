-- expect: error
-- Chapter 8: wrong lengths are type errors.
import Pond
open Critter

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

open Vec

def head : Vec α (n + 1) → α
  | cons x _ => x

-- ANCHOR: short
def chain : Vec Critter 2 :=
  cons heron (cons frog (cons fly nil))
-- ANCHOR_END: short

-- ANCHOR: headNil
#eval head (nil : Vec Critter 0)
-- ANCHOR_END: headNil

-- ANCHOR: nilCase
def head' : Vec Critter (n + 1) → Critter
  | nil      => fly
  | cons x _ => x
-- ANCHOR_END: nilCase
