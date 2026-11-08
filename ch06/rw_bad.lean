-- expect: error
-- Chapter 6: when exact and rw say no.
import Pond
open Critter

-- ANCHOR: exact
example (c : Critter) (h : c = frog) :
    Eats c fly := by
  exact Eats.frog_fly
-- ANCHOR_END: exact

-- ANCHOR: wrong_way
example (c : Critter) (h : frog = c) :
    Eats c fly := by
  rw [h]
-- ANCHOR_END: wrong_way
