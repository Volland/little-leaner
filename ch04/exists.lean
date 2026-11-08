-- Chapter 4: "there is" shows one.
import Pond
open Critter

-- ANCHOR: check
#check ∃ c, Eats c fish
-- ANCHOR_END: check

-- ANCHOR: fish_eaten
theorem fish_eaten :
    ∃ c, Eats c fish := by
  exists heron
  -- ANCHOR: fish_eaten_1
  trace_state
  -- ANCHOR_END: fish_eaten_1
  exact Eats.heron_fish
-- ANCHOR_END: fish_eaten

-- ANCHOR: otter
example : ∃ c, Eats c fish := by
  exists otter
  exact Eats.otter_fish
-- ANCHOR_END: otter

-- ANCHOR: pair
example : ∃ c, Eats c fish :=
  ⟨heron, Eats.heron_fish⟩
-- ANCHOR_END: pair

-- ANCHOR: print
#print fish_eaten
-- ANCHOR_END: print

-- ANCHOR: duck
example : ∃ c, Swims c ∧ Flies c := by
  exists duck
  -- ANCHOR: duck_1
  trace_state
  -- ANCHOR_END: duck_1
  exact ⟨Swims.duck, Flies.duck⟩
-- ANCHOR_END: duck

-- ANCHOR: above
inductive Above :
    Critter → Critter → Prop where
  | step : Eats x y → Above x y
  | trans : Eats x y → Above y z →
      Above x z
-- ANCHOR_END: above

-- ANCHOR: use
example (h : ∃ c, Eats c snail) :
    ∃ c, Above c algae := by
  obtain ⟨c, e⟩ := h
  -- ANCHOR: use_1
  trace_state
  -- ANCHOR_END: use_1
  exists c
  -- ANCHOR: use_2
  trace_state
  -- ANCHOR_END: use_2
  apply Above.trans e
  exact Above.step Eats.snail_algae
-- ANCHOR_END: use
