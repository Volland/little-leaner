-- expect: error
-- Chapter 7: where list proofs get stuck.
import Pond
open Critter

def app : List Critter → List Critter →
    List Critter
  | [],      ys => ys
  | x :: xs, ys => x :: app xs ys

def len : List Critter → Nat
  | []      => 0
  | _ :: xs => len xs + 1

def rev : List Critter → List Critter
  | []      => []
  | x :: xs => app (rev xs) [x]

-- ANCHOR: app_nil_right
example (xs : List Critter) :
    app xs [] = xs := by
  rfl
-- ANCHOR_END: app_nil_right

-- ANCHOR: on_ys
theorem len_app (xs ys : List Critter) :
    len (app xs ys) = len xs + len ys := by
  induction ys with
  | nil =>
    -- ANCHOR: on_ys_nil
    trace_state
    -- ANCHOR_END: on_ys_nil
    rfl
  | cons y ys ih =>
    -- ANCHOR: on_ys_cons
    trace_state
    -- ANCHOR_END: on_ys_cons
    rfl
-- ANCHOR_END: on_ys

-- ANCHOR: rr_stuck
theorem rev_rev (xs : List Critter) :
    rev (rev xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    -- ANCHOR: rr_start
    trace_state
    -- ANCHOR_END: rr_start
    rw [rev]
    -- ANCHOR: rr_unfold
    trace_state
    -- ANCHOR_END: rr_unfold
    rw [ih]
-- ANCHOR_END: rr_stuck
