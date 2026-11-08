-- Solutions to the exercises of Chapter 2.
import Pond
open Critter

-- ANCHOR: ex1
theorem otter_eats_fish : Eats otter fish := by
  trace_state
  exact Eats.otter_fish

example : Eats otter fish := by
  trace_state
  constructor
-- The goal before each tactic is the claim.
-- After it, no goals are left.
-- ANCHOR_END: ex1

-- ANCHOR: ex2
theorem heron_flies : Flies heron := by
  constructor

#print heron_flies
-- `constructor` chose `Flies.heron`, the only
-- constructor whose type is `Flies heron`.
-- `Flies.duck` has type `Flies duck`, and
-- `duck` is not `heron`.
-- ANCHOR_END: ex2

-- ANCHOR: ex3
inductive Grazes : Critter → Prop where
  | fly   : Grazes fly
  | snail : Grazes snail
  | duck  : Grazes duck

theorem duck_grazes : Grazes duck := by
  constructor

#print Grazes
-- On `Grazes frog`, `constructor` fails with
-- "no applicable constructor found". That only
-- says no constructor fits. It is not a proof
-- that the frog does not graze (Chapter 4).
-- ANCHOR_END: ex3

-- ANCHOR: ex4
example : Eats duck snail := by
  constructor

example : True := by
  constructor

example : Plant algae := by
  constructor
-- `Eats snail duck`, `False`, and `Swims heron`
-- have no constructor that fits, so
-- `constructor` fails on each with "no
-- applicable constructor found". Lean has not
-- shown them false. It has only failed to
-- prove them. Saying "not" is Chapter 4.
-- ANCHOR_END: ex4
