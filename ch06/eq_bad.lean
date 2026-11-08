-- expect: error
-- Chapter 6: what rfl cannot prove.
import Pond
open Critter

-- ANCHOR: frog_fly
example : frog = fly := by
  rfl
-- ANCHOR_END: frog_fly

-- ANCHOR: zero_add
example (n : Nat) : 0 + n = n := by
  rfl
-- ANCHOR_END: zero_add

-- ANCHOR: comm
example (a b : Nat) : a + b = b + a := by
  rfl
-- ANCHOR_END: comm
