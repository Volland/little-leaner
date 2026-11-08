-- Solutions to the exercises of Chapter 4.
import Pond
open Critter

inductive Above : Critter → Critter → Prop where
  | step : Eats x y → Above x y
  | trans : Eats x y → Above y z → Above x z

-- ANCHOR: ex1
example : ∃ c, Flies c ∧ Eats c algae := by
  exists fly
  trace_state
  exact ⟨Flies.fly, Eats.fly_algae⟩
-- The goal after `exists fly` is
-- `Flies fly ∧ Eats fly algae`.
-- The duck also flies and eats algae,
-- so `exists duck` works too.
-- ANCHOR_END: ex1

-- ANCHOR: ex2
theorem duck_safe : ∀ c, ¬ Eats c duck := by
  intro c h
  cases h

theorem otter_safe : ∀ c, ¬ Eats c otter := by
  intro c h
  cases h
-- Chapter 1's `onTop` computed `true` for
-- these critters: an answer. These theorems
-- are reasons, checked for every critter.
-- ANCHOR_END: ex2

-- ANCHOR: ex3
example : ∃ c, ¬ Swims c ∧ ¬ Flies c := by
  exists snail
  constructor
  · intro h
    cases h
  · intro h
    cases h
-- The algae work too: `exists algae`.
-- The fly does not swim, but it fails at
-- the second goal, `¬ Flies fly`: after
-- `intro h`, `cases h` leaves one case.
-- ANCHOR_END: ex3

-- ANCHOR: ex4
theorem algae_above_nothing :
    ¬ ∃ c, Above algae c := by
  intro h
  obtain ⟨c, a⟩ := h
  cases a with
  | step e => cases e
  | trans e _ => cases e
-- Both rules of `Above` start with an
-- `Eats algae y`, and no constructor of
-- `Eats` has the algae as the eater.
-- ANCHOR_END: ex4
