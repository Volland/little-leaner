-- Chapter 8: a list that knows its length.
import Pond
open Critter

-- ANCHOR: listHead
#eval [heron, frog].head?
#eval ([] : List Critter).head?
-- ANCHOR_END: listHead

-- ANCHOR: vec
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
-- ANCHOR_END: vec

open Vec

-- ANCHOR: checkVec
#check Vec
-- ANCHOR_END: checkVec

-- ANCHOR: three
#check Vec Critter 3
-- ANCHOR_END: three

-- ANCHOR: checkNil
#check (nil : Vec Critter 0)
-- ANCHOR_END: checkNil

-- ANCHOR: checkCons
#check @cons
-- ANCHOR_END: checkCons

-- ANCHOR: one
#check cons fly nil
-- ANCHOR_END: one

-- ANCHOR: two
def pair := cons frog (cons fly nil)

#check pair
-- ANCHOR_END: two

-- ANCHOR: chain
def chain : Vec Critter 3 :=
  cons heron (cons frog (cons fly nil))
-- ANCHOR_END: chain

-- ANCHOR: toList
def toList : Vec α n → List α
  | nil       => []
  | cons x xs => x :: toList xs
-- ANCHOR_END: toList

-- ANCHOR: evalChain
#eval toList chain
-- ANCHOR_END: evalChain

-- ANCHOR: len
def len (_ : Vec α n) : Nat := n

#eval len chain
-- ANCHOR_END: len

-- ANCHOR: head
def head : Vec α (n + 1) → α
  | cons x _ => x
-- ANCHOR_END: head

-- ANCHOR: evalHead
#eval head chain
-- ANCHOR_END: evalHead

-- ANCHOR: tail
def tail : Vec α (n + 1) → Vec α n
  | cons _ xs => xs

#check tail chain
#eval head (tail chain)
-- ANCHOR_END: tail

-- ANCHOR: casesZero
example (v : Vec Critter 0) : v = nil := by
  cases v
-- ANCHOR: goalZero
  trace_state
-- ANCHOR_END: goalZero
  rfl
-- ANCHOR_END: casesZero

-- ANCHOR: casesSucc
example (v : Vec Critter (n + 1)) :
    v = cons (head v) (tail v) := by
  cases v with
  | cons x xs =>
-- ANCHOR: goalSucc
    trace_state
-- ANCHOR_END: goalSucc
    rfl
-- ANCHOR_END: casesSucc
