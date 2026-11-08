-- expect: error
-- Chapter 6: what decide, omega and simp see.
import Pond
open Critter

-- ANCHOR: decide_ok
example : 2 + 3 = 5 := by
  decide
-- ANCHOR_END: decide_ok

-- ANCHOR: decide_vars
example (a b : Nat) :
    a + b = b + a := by
  decide
-- ANCHOR_END: decide_vars

-- ANCHOR: omega_ok
example (a b : Nat) :
    a + b = b + a := by
  omega
-- ANCHOR_END: omega_ok

-- ANCHOR: omega_mul
example (a b : Nat) :
    a * b = b * a := by
  omega
-- ANCHOR_END: omega_mul

-- ANCHOR: simp_mul
example (a b : Nat) :
    a * b = b * a := by
  simp
-- ANCHOR_END: simp_mul

-- ANCHOR: simp_lemma
example (a b : Nat) :
    a * b = b * a := by
  simp [Nat.mul_comm]
-- ANCHOR_END: simp_lemma
