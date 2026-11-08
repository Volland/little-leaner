-- expect: error
-- Chapter 6: a calc step that does not hold.
import Pond
open Critter

-- ANCHOR: calc_bad
example (a b : Nat) (h : a = b + 1) :
    a = b + 2 :=
  calc a = b + 1 := h
    _ = b + 2 := by rfl
-- ANCHOR_END: calc_bad
