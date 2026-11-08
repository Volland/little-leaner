-- Chapter 5: a food chain with a length.
import Pond
open Critter

-- ANCHOR: Chain
inductive Chain :
    Nat → Critter → Critter → Prop where
  | step : Eats x y → Chain 1 x y
  | trans : Eats x y → Chain n y z →
      Chain (n + 1) x z
-- ANCHOR_END: Chain

-- ANCHOR: check
#check Chain 3 heron algae
-- ANCHOR_END: check

-- ANCHOR: heron
theorem heron_algae :
    Chain 3 heron algae := by
  apply Chain.trans Eats.heron_frog
  -- ANCHOR: h1
  trace_state
  -- ANCHOR_END: h1
  apply Chain.trans Eats.frog_fly
  -- ANCHOR: h2
  trace_state
  -- ANCHOR_END: h2
  exact Chain.step Eats.fly_algae
-- ANCHOR_END: heron
