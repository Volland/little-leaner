-- Chapter 2: a claim is a type.
import Pond
open Critter

-- Chapter 1's Boolean `eats`, for comparison.
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

-- ANCHOR: two
#check eats frog fly
#check Eats frog fly
-- ANCHOR_END: two

-- ANCHOR: Eats
#check Eats
-- ANCHOR_END: Eats

-- ANCHOR: liar
#check Eats fly frog
-- ANCHOR_END: liar

-- ANCHOR: prop
#check Prop
-- ANCHOR_END: prop

-- ANCHOR: proof
#check Eats.frog_fly
-- ANCHOR_END: proof

-- ANCHOR: family
#check Eats frog
-- ANCHOR_END: family

-- ANCHOR: promise
#check eats frog fly = true
-- ANCHOR_END: promise
