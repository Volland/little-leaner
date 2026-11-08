-- Solutions to the exercises of Chapter 8.
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

def map (f : α → β) : Vec α n → Vec β n
  | nil       => nil
  | cons x xs => cons (f x) (map f xs)

def nth : Vec α n → Fin n → α
  | cons x _,  ⟨0, _⟩     => x
  | cons _ xs, ⟨i + 1, h⟩ =>
    nth xs ⟨i, by omega⟩

def chain : Vec Critter 3 :=
  cons heron (cons frog (cons fly nil))

-- ANCHOR: ex1
-- One case is enough: a vector of length
-- n + 2 is two conses on top of something.
def second : Vec α (n + 2) → α
  | cons _ (cons y _) => y

#eval second chain
-- `second (replicate 1 snail)` is turned
-- away: 1 is not of the form n + 2.
-- ANCHOR_END: ex1

-- ANCHOR: ex2
def snoc : Vec α n → α → Vec α (n + 1)
  | nil,       x => cons x nil
  | cons y ys, x => cons y (snoc ys x)

#eval toList (snoc chain algae)
-- No ▸ is needed. The nil case wants
-- Vec α (0 + 1), and cons x nil has it.
-- The cons case wants Vec α (n + 1 + 1),
-- and cons y (snoc ys x) has exactly that.
-- ANCHOR_END: ex2

-- ANCHOR: ex3
theorem map_replicate (f : α → β)
    (x : α) (n : Nat) :
    map f (replicate n x)
      = replicate n (f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    trace_state
    simp [replicate, map, ih]
-- ANCHOR_END: ex3

-- ANCHOR: ex4
theorem nth_replicate (x : α) (n : Nat)
    (i : Fin n) :
    nth (replicate n x) i = x := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨k + 1, h⟩ =>
      exact ih ⟨k, by omega⟩
-- There is no position in an empty vector,
-- so the zero case has nothing to prove.
-- ANCHOR_END: ex4
