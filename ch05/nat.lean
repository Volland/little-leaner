-- Chapter 5: Lean's own numbers.
import Pond
open Critter

-- ANCHOR: print
#print Nat
-- ANCHOR_END: print

-- ANCHOR: three
#eval Nat.succ (Nat.succ (Nat.succ Nat.zero))
-- ANCHOR_END: three

-- ANCHOR: big
#eval 2 + 3
#eval 123456789 + 987654321
-- ANCHOR_END: big

-- ANCHOR: five
example : 2 + 3 = 5 := by
  -- ANCHOR: five_goal
  trace_state
  -- ANCHOR_END: five_goal
  rfl
-- ANCHOR_END: five

-- ANCHOR: add_zero
theorem my_add_zero (n : Nat) :
    n + 0 = n := by
  rfl
-- ANCHOR_END: add_zero
