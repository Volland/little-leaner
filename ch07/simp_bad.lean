-- expect: error
-- Chapter 7: simp does not invent a lemma.
import Pond
open Critter

def app : List Critter → List Critter →
    List Critter
  | [],      ys => ys
  | x :: xs, ys => x :: app xs ys

def rev : List Critter → List Critter
  | []      => []
  | x :: xs => app (rev xs) [x]

-- ANCHOR: no_helper
theorem rev_rev (xs : List Critter) :
    rev (rev xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rev]
-- ANCHOR_END: no_helper
