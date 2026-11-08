-- Chapter 6: what equality is.
import Pond
open Critter

-- ANCHOR: prop
#check frog = frog
-- ANCHOR_END: prop

-- ANCHOR: print
#print Eq
-- ANCHOR_END: print

-- ANCHOR: refl
#check Eq.refl frog
-- ANCHOR_END: refl

-- ANCHOR: by_refl
example : frog = frog :=
  Eq.refl frog
-- ANCHOR_END: by_refl

-- ANCHOR: rfl
#check @rfl
-- ANCHOR_END: rfl

-- ANCHOR: by_rfl
example : frog = frog := rfl
-- ANCHOR_END: by_rfl

-- ANCHOR: tactic
example : frog = frog := by
  rfl
-- ANCHOR_END: tactic

-- ANCHOR: compute
example : 2 + 3 = 5 := rfl
-- ANCHOR_END: compute

-- ANCHOR: add_zero
example (n : Nat) : n + 0 = n := rfl
-- ANCHOR_END: add_zero
