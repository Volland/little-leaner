-- expect: error
-- Chapter 5: where simp and omega stop.
import Pond
open Critter

-- ANCHOR: simp_stuck
example (m n : Nat) :
    (m + 1) + n = (m + n) + 1 := by
  simp
-- ANCHOR_END: simp_stuck

-- ANCHOR: times
example (m n : Nat) : m * n = n * m := by
  omega
-- ANCHOR_END: times
