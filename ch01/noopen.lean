-- expect: error
-- Chapter 1: without `open Critter`, `frog` has no short name.
import Pond

-- ANCHOR: short
#check frog
-- ANCHOR_END: short

-- ANCHOR: long
#check Critter.frog
-- ANCHOR_END: long
