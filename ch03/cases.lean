-- Chapter 3: taking evidence apart.
import Pond
open Critter

inductive Above :
    Critter → Critter → Prop where
  | step  : Eats x y → Above x y
  | trans : Eats x y → Above y z → Above x z

-- ANCHOR: snail
example (c : Critter) :
    Eats c snail → Swims c := by
  intro h
  cases h
  -- ANCHOR: snail1
  trace_state
  -- ANCHOR_END: snail1
  · exact Swims.frog
  · exact Swims.fish
  · exact Swims.duck
-- ANCHOR_END: snail

-- ANCHOR: snailWith
example (c : Critter) :
    Eats c snail → Swims c := by
  intro h
  cases h with
  | frog_snail => exact Swims.frog
  | fish_snail => exact Swims.fish
  | duck_snail => exact Swims.duck
-- ANCHOR_END: snailWith

-- ANCHOR: above
example (x : Critter) :
    Above fly x → Above frog x := by
  intro h
  cases h with
  | step e =>
    -- ANCHOR: above1
    trace_state
    -- ANCHOR_END: above1
    exact Above.trans Eats.frog_fly
      (Above.step e)
  | trans e r =>
    -- ANCHOR: above2
    trace_state
    -- ANCHOR_END: above2
    cases e
    -- ANCHOR: above3
    trace_state
    -- ANCHOR_END: above3
    exact Above.trans Eats.frog_fly
      (Above.trans Eats.fly_algae r)
-- ANCHOR_END: above
