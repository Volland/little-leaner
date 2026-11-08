-- expect: error
-- Chapter 3: the snail neither swims nor flies.
import Pond
open Critter

-- ANCHOR: snail
example : Swims snail ∨ Flies snail := by
  left
  constructor
-- ANCHOR_END: snail
