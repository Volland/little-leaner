-- Chapter 7: lists of critters, by hand.
import Pond
open Critter

-- ANCHOR: chain
#check [heron, frog, fly, algae]
-- ANCHOR_END: chain

-- ANCHOR: cons
#check heron :: frog :: fly :: algae :: []
-- ANCHOR_END: cons

-- ANCHOR: nil
#check ([] : List Critter)
-- ANCHOR_END: nil

-- ANCHOR: app
def app : List Critter → List Critter →
    List Critter
  | [],      ys => ys
  | x :: xs, ys => x :: app xs ys
-- ANCHOR_END: app

-- ANCHOR: app_eval
#eval app [heron, frog] [fly, algae]
-- ANCHOR_END: app_eval

-- ANCHOR: len
def len : List Critter → Nat
  | []      => 0
  | _ :: xs => len xs + 1
-- ANCHOR_END: len

-- ANCHOR: len_eval
#eval len [heron, frog, fly, algae]
-- ANCHOR_END: len_eval

-- ANCHOR: rev
def rev : List Critter → List Critter
  | []      => []
  | x :: xs => app (rev xs) [x]
-- ANCHOR_END: rev

-- ANCHOR: rev_eval
#eval rev [heron, frog, fly, algae]
-- ANCHOR_END: rev_eval

-- ANCHOR: prey
def prey : Critter → Critter
  | heron => frog
  | otter => fish
  | frog  => fly
  | fish  => snail
  | duck  => snail
  | _     => algae
-- ANCHOR_END: prey

-- ANCHOR: mapL
def mapL (f : Critter → Critter) :
    List Critter → List Critter
  | []      => []
  | x :: xs => f x :: mapL f xs
-- ANCHOR_END: mapL

-- ANCHOR: map_eval
#eval mapL prey [heron, frog, fly]
-- ANCHOR_END: map_eval

-- ANCHOR: app_nil_left
example (ys : List Critter) :
    app [] ys = ys := by
  rfl
-- ANCHOR_END: app_nil_left
