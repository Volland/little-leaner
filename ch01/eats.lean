-- Chapter 1: a function of two critters.
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

-- ANCHOR: check
#check eats
-- ANCHOR_END: check

-- ANCHOR: yes
#eval eats frog fly
-- ANCHOR_END: yes

-- ANCHOR: no
#eval eats fly frog
-- ANCHOR_END: no

-- ANCHOR: partial
#check eats frog
-- ANCHOR_END: partial

-- ANCHOR: menu
#eval Critter.all.filter (eats frog)
-- ANCHOR_END: menu

-- ANCHOR: fun
#check fun c => eats c fish
-- ANCHOR_END: fun

-- ANCHOR: eaters
#eval Critter.all.filter (fun c => eats c fish)
-- ANCHOR_END: eaters

-- ANCHOR: grazer
def grazer (c : Critter) : Bool :=
  eats c algae

#eval Critter.all.filter grazer
-- ANCHOR_END: grazer

-- ANCHOR: self
#eval Critter.all.filter (fun c => eats c c)
-- ANCHOR_END: self

-- ANCHOR: promise
example : eats frog fly = true := by
  decide
-- ANCHOR_END: promise
