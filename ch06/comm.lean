-- Chapter 6: a + b = b + a, by rewriting.
import Pond
open Critter

-- ANCHOR: zero_add
theorem my_zero_add (n : Nat) :
    0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    -- ANCHOR: za_before
    trace_state
    -- ANCHOR_END: za_before
    show 0 + n + 1 = n + 1
    -- ANCHOR: za_show
    trace_state
    -- ANCHOR_END: za_show
    rw [ih]
-- ANCHOR_END: zero_add

-- ANCHOR: succ_add
theorem my_succ_add (n m : Nat) :
    (n + 1) + m = (n + m) + 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show (n + 1 + m) + 1
       = (n + m + 1) + 1
    rw [ih]
-- ANCHOR_END: succ_add

-- ANCHOR: add_comm
theorem my_add_comm (n m : Nat) :
    n + m = m + n := by
  induction m with
  | zero =>
    -- ANCHOR: zero_before
    trace_state
    -- ANCHOR_END: zero_before
    rw [my_zero_add]
    -- ANCHOR: zero_after
    trace_state
    -- ANCHOR_END: zero_after
    rfl
  | succ m ih =>
    -- ANCHOR: succ_before
    trace_state
    -- ANCHOR_END: succ_before
    rw [my_succ_add]
    -- ANCHOR: succ_after
    trace_state
    -- ANCHOR_END: succ_after
    show n + m + 1 = m + n + 1
    rw [ih]
-- ANCHOR_END: add_comm

-- ANCHOR: lean_comm
#check Nat.add_comm
-- ANCHOR_END: lean_comm
