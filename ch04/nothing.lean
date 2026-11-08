-- Chapter 4: False, and what "not" means.
import Pond
open Critter

-- ANCHOR: false
#print False
-- ANCHOR_END: false

-- ANCHOR: not
#print Not
-- ANCHOR_END: not

-- ANCHOR: check
#check ¬ Eats fly frog
-- ANCHOR_END: check

-- ANCHOR: fly_frog
theorem fly_not_frog :
    ¬ Eats fly frog := by
  -- ANCHOR: fly_frog_0
  trace_state
  -- ANCHOR_END: fly_frog_0
  intro h
  -- ANCHOR: fly_frog_1
  trace_state
  -- ANCHOR_END: fly_frog_1
  cases h
-- ANCHOR_END: fly_frog

-- ANCHOR: frog_heron
example : ¬ Eats frog heron := by
  intro h
  cases h
-- ANCHOR_END: frog_heron

-- ANCHOR: nofun
example : ¬ Eats fly frog := nofun
-- ANCHOR_END: nofun
