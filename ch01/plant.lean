-- Chapter 1: first functions, by cases.
import Pond
open Critter

-- ANCHOR: isPlant
def isPlant : Critter → Bool
  | algae => true
  | _     => false
-- ANCHOR_END: isPlant

-- ANCHOR: check
#check isPlant
-- ANCHOR_END: check

-- ANCHOR: evals
#eval isPlant algae
#eval isPlant frog
-- ANCHOR_END: evals

-- ANCHOR: swims
def swims : Critter → Bool
  | frog  => true
  | fish  => true
  | duck  => true
  | otter => true
  | _     => false
-- ANCHOR_END: swims

-- ANCHOR: who
#eval Critter.all.filter swims
-- ANCHOR_END: who
