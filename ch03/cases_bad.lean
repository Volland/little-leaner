-- expect: error
-- Chapter 3: not every fish eater flies.
import Pond
open Critter

-- ANCHOR: otter
example (c : Critter) :
    Eats c fish → Flies c := by
  intro h
  cases h with
  | heron_fish => exact Flies.heron
  | otter_fish => constructor
-- ANCHOR_END: otter
