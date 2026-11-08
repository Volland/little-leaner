-- Chapter 8: appending adds the lengths.
import Pond
open Critter

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

open Vec

def toList : Vec α n → List α
  | nil       => []
  | cons x xs => x :: toList xs

def replicate : (n : Nat) → α → Vec α n
  | 0,     _ => nil
  | n + 1, x => cons x (replicate n x)

def chain : Vec Critter 3 :=
  cons heron (cons frog (cons fly nil))

-- ANCHOR: append
def append :
    Vec α n → Vec α m → Vec α (m + n)
  | nil,       ys => ys
  | cons x xs, ys => cons x (append xs ys)
-- ANCHOR_END: append

-- ANCHOR: evalApp
def five :=
  append chain (replicate 2 snail)

#eval toList five
-- ANCHOR_END: evalApp

-- ANCHOR: checkApp
#check five
-- ANCHOR_END: checkApp

-- ANCHOR: rfl5
example : 2 + 3 = 5 := rfl
-- ANCHOR_END: rfl5

-- ANCHOR: five
example : Vec Critter 5 := five
-- ANCHOR_END: five

-- ANCHOR: toListApp
theorem toList_append
    (xs : Vec α n) (ys : Vec α m) :
    toList (append xs ys)
      = toList xs ++ toList ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [append, toList, ih]
-- ANCHOR_END: toListApp

-- ANCHOR: cast
def append' (xs : Vec α n) (ys : Vec α m) :
    Vec α (n + m) :=
  Nat.add_comm m n ▸ append xs ys
-- ANCHOR_END: cast

-- ANCHOR: evalCast
#eval toList (append' chain chain)
-- ANCHOR_END: evalCast

-- ANCHOR: grind
example (xs : Vec α n) (ys : Vec α m) :
    toList (append' xs ys)
      = toList xs ++ toList ys := by
  grind [append', toList_append]
-- ANCHOR_END: grind
