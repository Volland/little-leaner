-- Chapter 2: the term a tactic built.
import Pond
open Critter

theorem frog_eats_fly : Eats frog fly := by
  exact Eats.frog_fly

theorem heron_eats_fish :
    Eats heron fish := by
  constructor

-- ANCHOR: print
#print frog_eats_fly
-- ANCHOR_END: print

-- ANCHOR: print2
#print heron_eats_fish
-- ANCHOR_END: print2

-- ANCHOR: term
theorem otter_eats_fish :
    Eats otter fish :=
  Eats.otter_fish
-- ANCHOR_END: term

-- ANCHOR: true
#print True
-- ANCHOR_END: true

-- ANCHOR: truth
example : True := by
  constructor
-- ANCHOR_END: truth

-- ANCHOR: false
#print False
-- ANCHOR_END: false
