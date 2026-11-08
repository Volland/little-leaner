-- Chapter 2: the first theorem.
import Pond
open Critter

-- ANCHOR: first
theorem frog_eats_fly : Eats frog fly := by
-- ANCHOR: before
  trace_state
-- ANCHOR_END: before
  exact Eats.frog_fly
-- ANCHOR_END: first

-- ANCHOR: check
#check frog_eats_fly
-- ANCHOR_END: check

-- ANCHOR: use
example : Eats frog fly := by
  exact frog_eats_fly
-- ANCHOR_END: use

-- ANCHOR: dot
example : Eats heron fish := by
  exact .heron_fish
-- ANCHOR_END: dot

-- ANCHOR: ctor
theorem heron_eats_fish :
    Eats heron fish := by
-- ANCHOR: ctor_before
  trace_state
-- ANCHOR_END: ctor_before
  constructor
-- ANCHOR_END: ctor
