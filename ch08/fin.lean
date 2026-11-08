-- Chapter 8: positions that cannot miss.
import Pond
open Critter

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

open Vec

def toList : Vec α n → List α
  | nil       => []
  | cons x xs => x :: toList xs

def chain : Vec Critter 3 :=
  cons heron (cons frog (cons fly nil))

-- ANCHOR: listGet
#eval [heron, frog, fly][5]?
-- ANCHOR_END: listGet

-- ANCHOR: checkFin
#check Fin
#check @Fin.mk
-- ANCHOR_END: checkFin

-- ANCHOR: two
def two : Fin 3 := ⟨2, by decide⟩
-- ANCHOR_END: two

-- ANCHOR: nth
def nth : Vec α n → Fin n → α
  | cons x _,  ⟨0, _⟩     => x
  | cons _ xs, ⟨i + 1, h⟩ =>
    nth xs ⟨i, by omega⟩
-- ANCHOR_END: nth

-- ANCHOR: evalNth
#eval nth chain two
#eval nth chain 0
-- ANCHOR_END: evalNth

-- ANCHOR: wrap
#eval (5 : Fin 3)
#eval nth chain 5
-- ANCHOR_END: wrap

-- ANCHOR: swims
def swims : Critter → Bool
  | frog  => true
  | fish  => true
  | duck  => true
  | otter => true
  | _     => false
-- ANCHOR_END: swims

-- ANCHOR: map
def map (f : α → β) : Vec α n → Vec β n
  | nil       => nil
  | cons x xs => cons (f x) (map f xs)
-- ANCHOR_END: map

-- ANCHOR: evalMap
#check map swims chain
#eval toList (map swims chain)
-- ANCHOR_END: evalMap

-- ANCHOR: zip
def zip : Vec α n → Vec β n → Vec (α × β) n
  | nil,       nil       => nil
  | cons x xs, cons y ys =>
    cons (x, y) (zip xs ys)
-- ANCHOR_END: zip

-- ANCHOR: evalZip
#eval toList (zip chain (map swims chain))
-- ANCHOR_END: evalZip
