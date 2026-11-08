-- expect: error
-- Chapter 1: a match must cover every critter.
import Pond
open Critter

-- ANCHOR: missing
def swims : Critter → Bool
  | frog  => true
  | fish  => true
  | duck  => true
  | otter => true
-- ANCHOR_END: missing
