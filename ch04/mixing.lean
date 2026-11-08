-- Chapter 4: "not", "for every", "there is".
import Pond
open Critter

-- ANCHOR: all_not
theorem no_cannibals :
    ∀ c, ¬ Eats c c := by
  intro c h
  -- ANCHOR: all_not_1
  trace_state
  -- ANCHOR_END: all_not_1
  cases h
-- ANCHOR_END: all_not

-- ANCHOR: not_ex
example : ¬ ∃ c, Eats c c := by
  intro h
  -- ANCHOR: not_ex_1
  trace_state
  -- ANCHOR_END: not_ex_1
  obtain ⟨c, e⟩ := h
  -- ANCHOR: not_ex_2
  trace_state
  -- ANCHOR_END: not_ex_2
  cases e
-- ANCHOR_END: not_ex

-- ANCHOR: bridge
theorem not_ex (x : Critter)
    (h : ∀ c, ¬ Eats c x) :
    ¬ ∃ c, Eats c x := by
  intro hx
  obtain ⟨c, e⟩ := hx
  exact h c e
-- ANCHOR_END: bridge

theorem heron_safe :
    ∀ c, ¬ Eats c heron := by
  intro c h
  cases h

-- ANCHOR: heron
#check not_ex heron heron_safe
-- ANCHOR_END: heron

-- ANCHOR: snail
example : ∃ c, ¬ Swims c := by
  exists snail
  -- ANCHOR: snail_1
  trace_state
  -- ANCHOR_END: snail_1
  intro h
  cases h
-- ANCHOR_END: snail

-- ANCHOR: axioms
#print axioms no_cannibals
-- ANCHOR_END: axioms
