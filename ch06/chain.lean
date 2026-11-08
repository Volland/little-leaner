-- Chapter 6: turning and chaining equations.
import Pond
open Critter

def legs : Critter → Nat
  | fly           => 6
  | frog | otter  => 4
  | heron | duck  => 2
  | _             => 0

-- ANCHOR: symm
example (a b : Nat) (h : a = b) :
    b = a := by
  -- ANCHOR: symm_before
  trace_state
  -- ANCHOR_END: symm_before
  symm
  -- ANCHOR: symm_after
  trace_state
  -- ANCHOR_END: symm_after
  exact h
-- ANCHOR_END: symm

-- ANCHOR: symm_check
#check @Eq.symm
-- ANCHOR_END: symm_check

-- ANCHOR: symm_term
example (a b : Nat) (h : a = b) :
    b = a :=
  Eq.symm h
-- ANCHOR_END: symm_term

-- ANCHOR: trans_check
#check @Eq.trans
-- ANCHOR_END: trans_check

-- ANCHOR: trans
example (a b c : Nat) (h1 : a = b)
    (h2 : b = c) : a = c :=
  Eq.trans h1 h2
-- ANCHOR_END: trans

-- ANCHOR: congr_check
#check @congrArg
-- ANCHOR_END: congr_check

-- ANCHOR: congr
example (c d : Critter) (h : c = d) :
    legs c = legs d :=
  congrArg legs h
-- ANCHOR_END: congr

-- ANCHOR: congr_rw
example (c d : Critter) (h : c = d) :
    legs c = legs d := by
  rw [h]
-- ANCHOR_END: congr_rw

-- ANCHOR: calc
example (c : Critter) (h : c = frog) :
    legs c + legs c = 8 :=
  calc legs c + legs c
      = legs frog + legs frog := by
        rw [h]
    _ = 4 + 4 := rfl
    _ = 8     := rfl
-- ANCHOR_END: calc

-- ANCHOR: by_rw
theorem c_fly (c : Critter) (h : c = frog) :
    Eats c fly := by
  rw [h]
  exact Eats.frog_fly
-- ANCHOR_END: by_rw

-- ANCHOR: print_rw
#print c_fly
-- ANCHOR_END: print_rw
