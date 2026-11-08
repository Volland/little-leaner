-- expect: error
-- Chapter 4: the wrong witness.
import Pond
open Critter

-- ANCHOR: frog
example : ∃ c, Eats c fish := by
  exists frog
  -- ANCHOR: frog_1
  trace_state
  -- ANCHOR_END: frog_1
  exact Eats.heron_fish
-- ANCHOR_END: frog
