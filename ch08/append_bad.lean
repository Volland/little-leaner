-- expect: error
-- Chapter 8: append with the lengths in the wrong order.
import Pond
open Critter

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

open Vec

def toList : Vec α n → List α
  | nil       => []
  | cons x xs => x :: toList xs

-- ANCHOR: wrong
def app : Vec α n → Vec α m → Vec α (n + m)
-- ANCHOR: wrongNil
  | nil,       ys => ys
-- ANCHOR_END: wrongNil
-- ANCHOR: wrongCons
  | cons x xs, ys => cons x (app xs ys)
-- ANCHOR_END: wrongCons
-- ANCHOR_END: wrong

def append :
    Vec α n → Vec α m → Vec α (m + n)
  | nil,       ys => ys
  | cons x xs, ys => cons x (append xs ys)

theorem toList_append
    (xs : Vec α n) (ys : Vec α m) :
    toList (append xs ys)
      = toList xs ++ toList ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [append, toList, ih]

def append' (xs : Vec α n) (ys : Vec α m) :
    Vec α (n + m) :=
  Nat.add_comm m n ▸ append xs ys

-- ANCHOR: stuck
example (xs : Vec α n) (ys : Vec α m) :
    toList (append' xs ys)
      = toList xs ++ toList ys := by
  unfold append'
-- ANCHOR: stuckRw
  rw [toList_append]
-- ANCHOR_END: stuckRw
-- ANCHOR_END: stuck
