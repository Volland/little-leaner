-- Chapter 5: Lean's numbers, by hand and not.
import Pond
open Critter

-- ANCHOR: by_hand
theorem my_zero_add (n : Nat) :
    0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    -- ANCHOR: nat_succ
    trace_state
    -- ANCHOR_END: nat_succ
    exact congrArg Nat.succ ih
-- ANCHOR_END: by_hand

-- ANCHOR: simp
example (n : Nat) : 0 + n = n := by
  -- ANCHOR: simp_before
  trace_state
  -- ANCHOR_END: simp_before
  simp
-- ANCHOR_END: simp

-- ANCHOR: omega
example (m n : Nat) :
    (m + 1) + n = (m + n) + 1 := by
  omega
-- ANCHOR_END: omega

-- ANCHOR: omega_more
example (m n : Nat) : m + n = n + m := by
  omega

example (n : Nat) (h : n < 3) :
    n + n < 6 := by
  omega
-- ANCHOR_END: omega_more
