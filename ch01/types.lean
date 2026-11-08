-- Chapter 1: asking Lean for the type of a thing.
import Pond
open Critter

-- ANCHOR: frog
#check frog
-- ANCHOR_END: frog

-- ANCHOR: critter
#check Critter
-- ANCHOR_END: critter

-- ANCHOR: others
#check 3
#check "frog"
#check true
-- ANCHOR_END: others

-- ANCHOR: all
#check Critter.all
#eval Critter.all.length
-- ANCHOR_END: all

-- ANCHOR: type
#check Type
-- ANCHOR_END: type
