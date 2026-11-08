-- Chapter 4: from False, anything follows.
import Pond
open Critter

-- ANCHOR: false_elim
example (h : False) : Swims snail := by
  cases h
-- ANCHOR_END: false_elim

-- ANCHOR: exfalso
example (h : Eats fly frog) :
    Swims snail := by
  exfalso
  -- ANCHOR: exfalso_1
  trace_state
  -- ANCHOR_END: exfalso_1
  cases h
-- ANCHOR_END: exfalso

-- ANCHOR: direct
example (h : Eats fly frog) :
    Swims snail := by
  cases h
-- ANCHOR_END: direct

-- ANCHOR: apply_not
example (n : ¬ Eats frog fly) :
    Swims snail := by
  exfalso
  apply n
  -- ANCHOR: apply_not_1
  trace_state
  -- ANCHOR_END: apply_not_1
  exact Eats.frog_fly
-- ANCHOR_END: apply_not

-- ANCHOR: contradiction
example (h : Eats frog fly)
    (n : ¬ Eats frog fly) :
    Swims snail := by
  contradiction
-- ANCHOR_END: contradiction

-- ANCHOR: contradiction2
example (h : Eats fly frog) :
    Swims snail := by
  contradiction
-- ANCHOR_END: contradiction2

-- ANCHOR: absurd
example (h : Eats frog fly)
    (n : ¬ Eats frog fly) :
    Swims snail :=
  absurd h n
-- ANCHOR_END: absurd

-- ANCHOR: snail
theorem snail_stays :
    ¬ (Swims snail ∨ Flies snail) := by
  intro h
  cases h
  -- ANCHOR: snail_1
  trace_state
  -- ANCHOR_END: snail_1
  · contradiction
  · contradiction
-- ANCHOR_END: snail
