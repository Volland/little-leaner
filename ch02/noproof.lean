-- expect: error
-- Chapter 2: a claim with no proof.
import Pond
open Critter

-- ANCHOR: ctor
example : Eats fly frog := by
  constructor
-- ANCHOR_END: ctor

-- ANCHOR: exact
example : Eats fly frog := by
  exact Eats.frog_fly
-- ANCHOR_END: exact

-- ANCHOR: false
example : False := by
  constructor
-- ANCHOR_END: false

-- ANCHOR: critter
example : Eats frog fly := by
  exact frog
-- ANCHOR_END: critter
