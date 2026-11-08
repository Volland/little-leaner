-- expect: error
-- Chapter 5: a chain that is too short.
import Pond
open Critter

inductive Chain :
    Nat → Critter → Critter → Prop where
  | step : Eats x y → Chain 1 x y
  | trans : Eats x y → Chain n y z →
      Chain (n + 1) x z

-- ANCHOR: short
example : Chain 2 heron algae := by
  apply Chain.trans Eats.heron_frog
  apply Chain.trans Eats.frog_fly
  exact Chain.step Eats.fly_algae
-- ANCHOR_END: short
