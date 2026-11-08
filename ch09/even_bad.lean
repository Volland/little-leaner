-- expect: error
-- Chapter 9: no evidence for three.
import Pond
open Critter

inductive Even : Nat → Prop where
  | zero : Even 0
  | add_two : Even n → Even (n + 2)

-- ANCHOR: three
example : Even 3 := by
  apply Even.add_two
  -- ANCHOR: three1
  trace_state
  -- ANCHOR_END: three1
  apply Even.add_two
-- ANCHOR_END: three

-- ANCHOR: decide
example : Even 4 := by
  decide
-- ANCHOR_END: decide

-- ANCHOR: eats
example : Eats frog fly := by
  decide
-- ANCHOR_END: eats
