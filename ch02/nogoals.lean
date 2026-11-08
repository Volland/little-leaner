-- expect: error
-- Chapter 2: when the goal is gone, we are done.
import Pond
open Critter

-- ANCHOR: extra
example : Eats frog fly := by
  exact Eats.frog_fly
  exact Eats.frog_fly
-- ANCHOR_END: extra
