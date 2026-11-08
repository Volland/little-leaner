-- expect: error
-- Chapter 9: what decide refuses.
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

-- ANCHOR: seven
example : Even 7 := by
  decide
-- ANCHOR_END: seven

-- ANCHOR: forall
example : ∀ n, Even (n + n) := by
  decide
-- ANCHOR_END: forall
