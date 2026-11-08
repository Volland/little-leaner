-- Chapter 3: a rule with two constructors.
import Pond
open Critter

-- ANCHOR: Above
inductive Above :
    Critter → Critter → Prop where
  | step  : Eats x y → Above x y
  | trans : Eats x y → Above y z → Above x z
-- ANCHOR_END: Above

-- ANCHOR: checks
#check Above.step
#check Above.trans
-- ANCHOR_END: checks

-- ANCHOR: fly
theorem fly_above_algae :
    Above fly algae := by
  -- ANCHOR: fly0
  trace_state
  -- ANCHOR_END: fly0
  apply Above.step
  -- ANCHOR: fly1
  trace_state
  -- ANCHOR_END: fly1
  exact Eats.fly_algae
-- ANCHOR_END: fly

-- ANCHOR: heron1
theorem heron_above_algae :
    Above heron algae := by
  apply Above.trans
  -- ANCHOR: heron1a
  trace_state
  -- ANCHOR_END: heron1a
  exact Eats.heron_frog
  -- ANCHOR: heron1b
  trace_state
  -- ANCHOR_END: heron1b
  apply Above.trans (y := fly)
  -- ANCHOR: heron1c
  trace_state
  -- ANCHOR_END: heron1c
  exact Eats.frog_fly
  exact fly_above_algae
-- ANCHOR_END: heron1

-- ANCHOR: heron2
example : Above heron algae := by
  apply Above.trans (y := fish)
  · exact Eats.heron_fish
  · apply Above.trans (y := snail)
    · exact Eats.fish_snail
    · apply Above.step
      exact Eats.snail_algae
-- ANCHOR_END: heron2

-- ANCHOR: heron3
example : Above heron algae :=
  Above.trans Eats.heron_frog
    (Above.trans Eats.frog_fly
      (Above.step Eats.fly_algae))
-- ANCHOR_END: heron3

-- ANCHOR: print
#print heron_above_algae
-- ANCHOR_END: print
