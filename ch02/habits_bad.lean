-- expect: error
-- Chapter 2: the fly does not swim (as far as we can prove).
import Pond
open Critter

-- ANCHOR: fly
example : Swims fly := by
  constructor
-- ANCHOR_END: fly
