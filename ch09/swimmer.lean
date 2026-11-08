-- Chapter 9: a critter with its evidence.
import Pond
open Critter

-- ANCHOR: type
#check {c : Critter // Swims c}
-- ANCHOR_END: type

-- ANCHOR: Swimmer
def Swimmer := {c : Critter // Swims c}
-- ANCHOR_END: Swimmer

-- ANCHOR: duck
def ducky : Swimmer := ⟨duck, Swims.duck⟩
-- ANCHOR_END: duck

-- ANCHOR: parts
#check ducky.val
#check ducky.property
-- ANCHOR_END: parts

-- ANCHOR: show
#eval ducky
-- ANCHOR_END: show

-- ANCHOR: dive
def dive (s : Swimmer) : Critter :=
  s.val

#eval dive ⟨frog, .frog⟩
-- ANCHOR_END: dive

-- ANCHOR: wet
theorem wet (s : Swimmer) :
    Swims (dive s) :=
  s.property
-- ANCHOR_END: wet

-- ANCHOR: team
def team : List Swimmer :=
  [⟨frog, .frog⟩, ⟨otter, .otter⟩]

#eval team.map dive
-- ANCHOR_END: team
