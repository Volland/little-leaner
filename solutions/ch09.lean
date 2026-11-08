-- Solutions to the exercises of Chapter 9.
import Pond
open Critter

inductive Even : Nat → Prop where
  | zero : Even 0
  | add_two : Even n → Even (n + 2)

theorem back : Even (n + 2) → Even n := by
  intro h
  cases h with
  | add_two h1 => exact h1

def decEven : (n : Nat) → Decidable (Even n)
  | 0 => isTrue Even.zero
  | 1 => isFalse nofun
  | n + 2 =>
    match decEven n with
    | isTrue h  => isTrue (Even.add_two h)
    | isFalse h =>
      isFalse (fun h2 => h (back h2))

instance (n : Nat) : Decidable (Even n) :=
  decEven n

-- ANCHOR: ex1
-- Three steps of add_two: 6, 4, 2, then 0.
theorem six : Even 6 := by
  apply Even.add_two
  apply Even.add_two
  apply Even.add_two
  exact Even.zero

example : Even 6 := by
  decide
-- ANCHOR_END: ex1

-- ANCHOR: ex2
-- Three uses of cases: from 5 to 3, from 3
-- to 1, and then no constructor ends in 1.
theorem not5 : ¬ Even 5 := by
  intro h
  cases h with
  | add_two h =>
    cases h with
    | add_two h => cases h

example : ¬ Even 5 := by
  decide
-- ANCHOR_END: ex2

-- ANCHOR: ex3
def EvenNat := {n : Nat // Even n}

def next (e : EvenNat) : EvenNat :=
  ⟨e.val + 2, Even.add_two e.property⟩

#eval (next ⟨4, by decide⟩).val
-- `⟨3, _⟩ : EvenNat` cannot be written:
-- the second part would be a proof of
-- `Even 3`, and there is none.
-- ANCHOR_END: ex3

-- ANCHOR: ex4
def swims : Critter → Bool
  | frog  => true
  | fish  => true
  | duck  => true
  | otter => true
  | _     => false

theorem swims_iff :
    swims c = true ↔ Swims c := by
  constructor
  · intro h
    cases c <;>
      first | constructor | contradiction
  · intro h
    cases h <;> rfl

instance (c : Critter) :
    Decidable (Swims c) :=
  decidable_of_iff _ swims_iff

#eval Critter.all.filter
  (fun c => decide (Swims c))
-- The same four as `filter swims` in
-- Chapter 1: frog, fish, duck, otter.
-- ANCHOR_END: ex4
