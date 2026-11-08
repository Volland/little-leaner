-- Chapter 4: "for every" is a function.
import Pond
open Critter

-- ANCHOR: check
#check ∀ c, ¬ Eats c heron
-- ANCHOR_END: check

-- ANCHOR: heron_safe
theorem heron_safe :
    ∀ c, ¬ Eats c heron := by
  intro c
  -- ANCHOR: heron_safe_1
  trace_state
  -- ANCHOR_END: heron_safe_1
  intro h
  -- ANCHOR: heron_safe_2
  trace_state
  -- ANCHOR_END: heron_safe_2
  cases h
-- ANCHOR_END: heron_safe

-- ANCHOR: type
#check heron_safe
-- ANCHOR_END: type

-- ANCHOR: use
#check heron_safe otter
-- ANCHOR_END: use

-- ANCHOR: otter
example : ¬ Eats otter heron :=
  heron_safe otter
-- ANCHOR_END: otter

-- ANCHOR: short
example : ∀ c, ¬ Eats c heron := by
  intro c h
  cases h
-- ANCHOR_END: short

-- ANCHOR: nofun
example : ∀ c, ¬ Eats c heron := nofun
-- ANCHOR_END: nofun

-- ANCHOR: not_all
example : ¬ ∀ c, Swims c := by
  intro h
  -- ANCHOR: not_all_1
  trace_state
  -- ANCHOR_END: not_all_1
  cases h snail
-- ANCHOR_END: not_all
