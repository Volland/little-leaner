-- Chapter 9: even numbers, by evidence.
import Pond
open Critter

-- ANCHOR: Even
inductive Even : Nat → Prop where
  | zero : Even 0
  | add_two : Even n → Even (n + 2)
-- ANCHOR_END: Even

-- ANCHOR: check
#check Even
#check Even 4
-- ANCHOR_END: check

-- ANCHOR: addtwo
#check Even.add_two
-- ANCHOR_END: addtwo

-- ANCHOR: zero
theorem even0 : Even 0 := by
  exact Even.zero
-- ANCHOR_END: zero

-- ANCHOR: four
theorem even4 : Even 4 := by
  apply Even.add_two
  -- ANCHOR: four1
  trace_state
  -- ANCHOR_END: four1
  apply Even.add_two
  -- ANCHOR: four2
  trace_state
  -- ANCHOR_END: four2
  exact Even.zero
-- ANCHOR_END: four

-- ANCHOR: term
theorem even6 : Even 6 :=
  .add_two (.add_two (.add_two .zero))
-- ANCHOR_END: term

-- ANCHOR: three
theorem not3 : ¬ Even 3 := by
  intro h
  -- ANCHOR: three1
  trace_state
  -- ANCHOR_END: three1
  cases h with
  | add_two h1 =>
    -- ANCHOR: three2
    trace_state
    -- ANCHOR_END: three2
    cases h1
-- ANCHOR_END: three

-- ANCHOR: one
theorem not1 : ¬ Even 1 := nofun
-- ANCHOR_END: one

-- ANCHOR: back
theorem back : Even (n + 2) → Even n := by
  intro h
  cases h with
  | add_two h1 => exact h1
-- ANCHOR_END: back
