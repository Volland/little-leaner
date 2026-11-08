-- expect: error
-- Chapter 9: a heron is not a swimmer.
import Pond
open Critter

def Swimmer := {c : Critter // Swims c}

def dive (s : Swimmer) : Critter :=
  s.val

-- ANCHOR: heron
#eval dive ⟨heron, by constructor⟩
-- ANCHOR_END: heron

-- ANCHOR: bare
#eval dive frog
-- ANCHOR_END: bare

-- ANCHOR: pick
def pick (h : ∃ c, Swims c) :
    Critter := by
  obtain ⟨c, _⟩ := h
  exact c
-- ANCHOR_END: pick
