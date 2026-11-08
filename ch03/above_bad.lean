-- expect: error
-- Chapter 3: rules that do not fit.
import Pond
open Critter

inductive Above :
    Critter → Critter → Prop where
  | step  : Eats x y → Above x y
  | trans : Eats x y → Above y z → Above x z

-- ANCHOR: step
example : Above heron algae := by
  apply Above.step
  constructor
-- ANCHOR_END: step

-- ANCHOR: duck
example : Above heron algae := by
  apply Above.trans (y := duck)
  · constructor
  · exact Above.step Eats.duck_algae
-- ANCHOR_END: duck

-- ANCHOR: eats
example : Above heron frog :=
  Eats.heron_frog
-- ANCHOR_END: eats
