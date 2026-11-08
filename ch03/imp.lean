-- Chapter 3: "if, then" is a function.
import Pond
open Critter

inductive Above :
    Critter → Critter → Prop where
  | step  : Eats x y → Above x y
  | trans : Eats x y → Above y z → Above x z

-- ANCHOR: flyEater
theorem flyEater (c : Critter) :
    Eats c fly → Above c algae := by
  -- ANCHOR: fe0
  trace_state
  -- ANCHOR_END: fe0
  intro h
  -- ANCHOR: fe1
  trace_state
  -- ANCHOR_END: fe1
  apply Above.trans h
  -- ANCHOR: fe2
  trace_state
  -- ANCHOR_END: fe2
  exact Above.step Eats.fly_algae
-- ANCHOR_END: flyEater

-- ANCHOR: check
#check flyEater
-- ANCHOR_END: check

-- ANCHOR: use
#check flyEater frog Eats.frog_fly
-- ANCHOR_END: use

-- ANCHOR: fish
example : Above fish algae :=
  flyEater fish Eats.fish_fly
-- ANCHOR_END: fish

-- ANCHOR: term
example (c : Critter) :
    Eats c fly → Above c algae :=
  fun h => Above.trans h
    (Above.step Eats.fly_algae)
-- ANCHOR_END: term
