-- Solutions to the exercises of Chapter 1.
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

-- ANCHOR: ex1
def flies : Critter → Bool
  | fly   => true
  | heron => true
  | duck  => true
  | _     => false

#eval Critter.all.filter flies
-- ANCHOR_END: ex1

-- ANCHOR: ex2
-- Swap the arguments. No new pairs needed.
def eatenBy (food eater : Critter) : Bool :=
  eats eater food

#eval eatenBy fly frog
#check eatenBy fly
#eval Critter.all.filter (eatenBy fly)
-- ANCHOR_END: ex2

-- ANCHOR: ex3
-- On top: no critter in the pond eats it.
def onTop (c : Critter) : Bool :=
  !(Critter.all.any (fun e => eats e c))

#eval Critter.all.filter onTop
-- The duck is on top too: nothing eats it,
-- though it is no hunter.
-- ANCHOR_END: ex3
