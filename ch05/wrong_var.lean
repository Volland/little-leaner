-- expect: error
-- Chapter 5: induction on the wrong number.
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

-- ANCHOR: on_m
-- ANCHOR: on_m_start
example (m n : N) :
    add (succ m) n = succ (add m n) := by
  induction m with
  | zero =>
    -- ANCHOR: m_zero
    trace_state
    -- ANCHOR_END: m_zero
-- ANCHOR_END: on_m_start
    rfl
  | succ m ih =>
    sorry
-- ANCHOR_END: on_m
