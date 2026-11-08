-- Chapter 9: teaching Lean to decide Even.
import Pond
open Critter

inductive Even : Nat → Prop where
  | zero : Even 0
  | add_two : Even n → Even (n + 2)

theorem back : Even (n + 2) → Even n := by
  intro h
  cases h with
  | add_two h1 => exact h1

-- ANCHOR: yes
#check isTrue Even.zero
-- ANCHOR_END: yes

-- ANCHOR: no
#check (isFalse nofun : Decidable (Even 1))
-- ANCHOR_END: no

-- ANCHOR: decEven
def decEven : (n : Nat) → Decidable (Even n)
  | 0 => isTrue Even.zero
  | 1 => isFalse nofun
  | n + 2 =>
    match decEven n with
    | isTrue h  => isTrue (Even.add_two h)
    | isFalse h =>
      isFalse (fun h2 => h (back h2))
-- ANCHOR_END: decEven

-- ANCHOR: instance
instance (n : Nat) : Decidable (Even n) :=
  decEven n
-- ANCHOR_END: instance

-- ANCHOR: ten
example : Even 10 := by
  decide
-- ANCHOR_END: ten

-- ANCHOR: seven
example : ¬ Even 7 := by
  decide
-- ANCHOR_END: seven

-- ANCHOR: bool
#check decide (Even 7)
#eval decide (Even 7)
-- ANCHOR_END: bool

-- ANCHOR: filter
#eval (List.range 12).filter
  (fun n => decide (Even n))
-- ANCHOR_END: filter

-- ANCHOR: bounded
example : ∀ n, n < 10 → Even (n + n) := by
  decide
-- ANCHOR_END: bounded
