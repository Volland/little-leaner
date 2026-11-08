-- Chapter 7: a food chain as a list.
import Pond
open Critter

def app : List Critter → List Critter →
    List Critter
  | [],      ys => ys
  | x :: xs, ys => x :: app xs ys

def len : List Critter → Nat
  | []      => 0
  | _ :: xs => len xs + 1

def rev : List Critter → List Critter
  | []      => []
  | x :: xs => app (rev xs) [x]

-- ANCHOR: Path
inductive Path : List Critter → Prop where
  | one (c : Critter) : Path [c]
  | link : Eats x y → Path (y :: ys) →
      Path (x :: y :: ys)
-- ANCHOR_END: Path

-- ANCHOR: down
theorem down :
    Path [heron, frog, fly, algae] := by
  apply Path.link Eats.heron_frog
  -- ANCHOR: down_goal
  trace_state
  -- ANCHOR_END: down_goal
  apply Path.link Eats.frog_fly
  apply Path.link Eats.fly_algae
  exact Path.one algae
-- ANCHOR_END: down

-- ANCHOR: down_len
example :
    len [heron, frog, fly, algae] = 4 := by
  rfl
-- ANCHOR_END: down_len

-- ANCHOR: up_eval
#eval rev [heron, frog]
-- ANCHOR_END: up_eval

-- ANCHOR: up
theorem up :
    ¬ Path (rev [heron, frog]) := by
  intro h
  cases h with
  | link e p =>
    -- ANCHOR: up_goal
    trace_state
    -- ANCHOR_END: up_goal
    cases e
-- ANCHOR_END: up
