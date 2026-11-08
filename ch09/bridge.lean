-- Chapter 9: a bridge from Bool to Prop.
import Pond
open Critter

-- ANCHOR: eats
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
-- ANCHOR_END: eats

-- ANCHOR: iff
#check Iff
#check @Iff.intro
-- ANCHOR_END: iff

-- ANCHOR: up
theorem up :
    Eats c d → eats c d = true := by
  intro h
  cases h <;> rfl
-- ANCHOR_END: up

-- ANCHOR: down_yes
example : eats frog fly = true →
    Eats frog fly := by
  intro h
  -- ANCHOR: down_yes1
  trace_state
  -- ANCHOR_END: down_yes1
  constructor
-- ANCHOR_END: down_yes

-- ANCHOR: down_no
example : eats fly frog = true →
    Eats fly frog := by
  intro h
  -- ANCHOR: down_no1
  trace_state
  -- ANCHOR_END: down_no1
  contradiction
-- ANCHOR_END: down_no

-- ANCHOR: eats_iff
theorem eats_iff :
    eats c d = true ↔ Eats c d := by
  constructor
  -- ANCHOR: eats_iff1
  trace_state
  -- ANCHOR_END: eats_iff1
  · intro h
    cases c <;> cases d <;>
      first | constructor | contradiction
  · exact up
-- ANCHOR_END: eats_iff

-- ANCHOR: use
#check eats_iff.mpr Eats.frog_fly
-- ANCHOR_END: use

-- ANCHOR: instance
instance (c d : Critter) :
    Decidable (Eats c d) :=
  decidable_of_iff _ eats_iff
-- ANCHOR_END: instance

-- ANCHOR: of_iff
#check @decidable_of_iff
-- ANCHOR_END: of_iff

-- ANCHOR: yes
example : Eats frog fly := by
  decide
-- ANCHOR_END: yes

-- ANCHOR: no
example : ¬ Eats fly frog := by
  decide
-- ANCHOR_END: no

-- ANCHOR: filter
#eval Critter.all.filter
  (fun c => decide (Eats c fish))
-- ANCHOR_END: filter
