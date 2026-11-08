-- Chapter 5: proofs by induction.
import Pond
open Critter
set_option pp.fieldNotation false

inductive N where
  | zero
  | succ (n : N)

open N

def N.add : N → N → N
  | m, zero   => m
  | m, succ n => succ (add m n)

-- ANCHOR: add_zero
theorem N.add_zero (n : N) :
    add n zero = n := by
  rfl
-- ANCHOR_END: add_zero

-- ANCHOR: zero_add
theorem N.zero_add (n : N) :
    add zero n = n := by
  -- ANCHOR: za_start
  trace_state
  -- ANCHOR_END: za_start
  induction n with
  | zero =>
    -- ANCHOR: za_zero
    trace_state
    -- ANCHOR_END: za_zero
    rfl
  | succ n ih =>
    -- ANCHOR: za_succ
    trace_state
    -- ANCHOR_END: za_succ
    exact congrArg succ ih
-- ANCHOR_END: zero_add

-- ANCHOR: one_step
example (m n : N) :
    add m (succ n) = succ (add m n) := by
  rfl
-- ANCHOR_END: one_step

-- ANCHOR: congr_succ
example (a b : N) (h : a = b) :
    succ a = succ b := by
  exact congrArg succ h
-- ANCHOR_END: congr_succ

-- ANCHOR: succ_add
theorem N.succ_add (m n : N) :
    add (succ m) n = succ (add m n) := by
  induction n with
  | zero =>
    -- ANCHOR: sa_zero
    trace_state
    -- ANCHOR_END: sa_zero
    rfl
  | succ n ih =>
    -- ANCHOR: sa_succ
    trace_state
    -- ANCHOR_END: sa_succ
    exact congrArg succ ih
-- ANCHOR_END: succ_add
