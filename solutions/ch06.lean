-- Solutions to the exercises of Chapter 6.
import Pond
open Critter

theorem my_zero_add (n : Nat) :
    0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show 0 + n + 1 = n + 1
    rw [ih]

theorem my_succ_add (n m : Nat) :
    (n + 1) + m = (n + m) + 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show (n + 1 + m) + 1
       = (n + m + 1) + 1
    rw [ih]

theorem my_add_comm (n m : Nat) :
    n + m = m + n := by
  induction m with
  | zero =>
    rw [my_zero_add]
    rfl
  | succ m ih =>
    rw [my_succ_add]
    show n + m + 1 = m + n + 1
    rw [ih]

-- ANCHOR: ex1
example (a b c : Nat) (h1 : a = b)
    (h2 : c = b) : a + 1 = c + 1 := by
  rw [h1]
  trace_state
  rw [← h2]
-- After rw [h1] the goal is b + 1 = c + 1.
-- h2 reads c = b, so rewrite it backward
-- (b becomes c); rw then closes c + 1 = c + 1.
-- ANCHOR_END: ex1

-- ANCHOR: ex2
-- Rewrite the goal: d becomes c, left to right.
example (c d : Critter) (h1 : d = c)
    (h2 : Eats heron c) :
    Eats heron d := by
  rw [h1]
  exact h2

-- Rewrite h2: c becomes d, so right to left.
example (c d : Critter) (h1 : d = c)
    (h2 : Eats heron c) :
    Eats heron d := by
  rw [← h1] at h2
  exact h2
-- ANCHOR_END: ex2

-- ANCHOR: ex3
-- Induction on k: + recurses on its
-- second argument, and k is the last one.
theorem my_add_assoc (n m k : Nat) :
    n + m + k = n + (m + k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    trace_state
    show n + m + k + 1
       = n + (m + k) + 1
    rw [ih]
-- ANCHOR_END: ex3

-- ANCHOR: ex4
example (n m k : Nat) :
    n + m + k = n + k + m := by
  rw [my_add_assoc, my_add_comm m k,
      ← my_add_assoc]
-- With no arguments, rw [my_add_comm]
-- rewrites the first sum it meets, the
-- whole left side n + m + k, and the goal
-- becomes k + (n + m) = n + k + m. Giving
-- the arguments m k picks the sum to swap.
-- ANCHOR_END: ex4
