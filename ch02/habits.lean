-- Chapter 2: claims about one critter.
import Pond
open Critter

-- ANCHOR: Swims
#check Swims
-- ANCHOR_END: Swims

-- ANCHOR: frog
#check Swims.frog
-- ANCHOR_END: frog

-- ANCHOR: duck
theorem duck_swims : Swims duck := by
  constructor

theorem duck_flies : Flies duck := by
  constructor
-- ANCHOR_END: duck

-- ANCHOR: print
#print duck_flies
-- ANCHOR_END: print

-- ANCHOR: fly
#check Swims fly
-- ANCHOR_END: fly

-- ANCHOR: plant
#print Plant
-- ANCHOR_END: plant
