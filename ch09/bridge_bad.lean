-- expect: error
-- Chapter 9: decide turns a false claim away.
import Pond
open Critter

def eats : Critter → Critter → Bool
  | snail, algae => true
  | fly,   algae => true
  | frog,  fly   => true
  | frog,  snail => true
  | fish,  fly   => true
  | fish,  snail => true
  | duck,  snail => true
  | duck,  algae => true
  | heron, frog  => true
  | heron, fish  => true
  | otter, fish  => true
  | _,     _     => false

theorem eats_iff :
    eats c d = true ↔ Eats c d := by
  constructor
  · intro h
    cases c <;> cases d <;>
      first | constructor | contradiction
  · intro h
    cases h <;> rfl

instance (c d : Critter) :
    Decidable (Eats c d) :=
  decidable_of_iff _ eats_iff

-- ANCHOR: lie
example : Eats fly frog := by
  decide
-- ANCHOR_END: lie

-- ANCHOR: heron
example : ∃ c, Eats c heron := by
  decide
-- ANCHOR_END: heron
