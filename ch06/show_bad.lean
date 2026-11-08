-- expect: error
-- Chapter 6: show only accepts what computes.
import Pond
open Critter

-- ANCHOR: show_bad
example (n : Nat) :
    0 + (n + 1) = n + 1 := by
  show 1 + n = n + 1
-- ANCHOR_END: show_bad
