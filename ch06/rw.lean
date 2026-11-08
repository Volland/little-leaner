-- Chapter 6: rewriting with an equation.
import Pond
open Critter

-- ANCHOR: frog
example (c : Critter) (h : c = frog) :
    Eats c fly := by
  -- ANCHOR: frog_before
  trace_state
  -- ANCHOR_END: frog_before
  rw [h]
  -- ANCHOR: frog_after
  trace_state
  -- ANCHOR_END: frog_after
  exact Eats.frog_fly
-- ANCHOR_END: frog

-- ANCHOR: back
example (c : Critter) (h : frog = c) :
    Eats c fly := by
  rw [← h]
  -- ANCHOR: back_after
  trace_state
  -- ANCHOR_END: back_after
  exact Eats.frog_fly
-- ANCHOR_END: back

-- ANCHOR: nums
example (a b c : Nat) (h1 : a = b)
    (h2 : b = c) : a = c := by
  rw [h1]
  -- ANCHOR: nums_mid
  trace_state
  -- ANCHOR_END: nums_mid
  rw [h2]
-- ANCHOR_END: nums

-- ANCHOR: two
example (a b c : Nat) (h1 : a = b)
    (h2 : b = c) : a = c := by
  rw [h1, h2]
-- ANCHOR_END: two

-- ANCHOR: legs
def legs : Critter → Nat
  | fly           => 6
  | frog | otter  => 4
  | heron | duck  => 2
  | _             => 0
-- ANCHOR_END: legs

-- ANCHOR: legs_frog
example (c : Critter) (h : c = frog) :
    legs c = 4 := by
  rw [h]
  -- ANCHOR: legs_after
  trace_state
  -- ANCHOR_END: legs_after
  rfl
-- ANCHOR_END: legs_frog

-- ANCHOR: at
example (c : Critter) (h1 : c = heron)
    (h2 : Eats c frog) :
    Eats heron frog := by
  rw [h1] at h2
  -- ANCHOR: at_after
  trace_state
  -- ANCHOR_END: at_after
  exact h2
-- ANCHOR_END: at
