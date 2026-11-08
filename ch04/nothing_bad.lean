-- expect: error
-- Chapter 4: "not" fails when it is true.
import Pond
open Critter

-- ANCHOR: frog_fly
example : ¬ Eats frog fly := by
  intro h
  cases h
-- ANCHOR_END: frog_fly

-- ANCHOR: nofun
example : ¬ Eats frog fly := nofun
-- ANCHOR_END: nofun

-- ANCHOR: fish
example : ∀ c, ¬ Eats c fish := by
  intro c h
  cases h
-- ANCHOR_END: fish
