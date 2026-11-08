-- expect: error
-- Chapter 1: Lean reads the question before it runs it.
import Pond
open Critter

def eats : Critter → Critter → Bool
  | frog, fly => true
  | _,    _   => false

-- ANCHOR: string
#eval eats frog "fly"
-- ANCHOR_END: string

-- ANCHOR: half
#eval eats frog
-- ANCHOR_END: half

-- ANCHOR: lie
example : eats fly frog = true := by
  decide
-- ANCHOR_END: lie
