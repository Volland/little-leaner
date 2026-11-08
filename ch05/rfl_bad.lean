-- expect: error
-- Chapter 5: where computing is not enough.
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

-- ANCHOR: four
example : 2 + 2 = 5 := by
  rfl
-- ANCHOR_END: four

-- ANCHOR: N_zero_add
example (n : N) : add zero n = n := by
  rfl
-- ANCHOR_END: N_zero_add

-- ANCHOR: nat_zero_add
example (n : Nat) : 0 + n = n := by
  rfl
-- ANCHOR_END: nat_zero_add
