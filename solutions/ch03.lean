-- Solutions to the exercises of Chapter 3.
import Pond
open Critter

inductive Above :
    Critter → Critter → Prop where
  | step  : Eats x y → Above x y
  | trans : Eats x y → Above y z → Above x z

-- ANCHOR: ex1
-- Two routes: through the fish and the fly,
-- or through the fish and the snail.
example : Above otter algae := by
  apply Above.trans (y := fish)
  · exact Eats.otter_fish
  · apply Above.trans (y := fly)
    · exact Eats.fish_fly
    · exact Above.step Eats.fly_algae

example : Above otter algae :=
  Above.trans Eats.otter_fish
    (Above.trans Eats.fish_snail
      (Above.step Eats.snail_algae))
-- ANCHOR_END: ex1

-- ANCHOR: ex2
-- Two goals after cases; each one picks
-- the other side.
example (c : Critter) :
    Swims c ∨ Flies c →
    Flies c ∨ Swims c := by
  intro h
  cases h with
  | inl hs =>
    right
    exact hs
  | inr hf =>
    left
    exact hf
-- ANCHOR_END: ex2

-- ANCHOR: ex3
-- cases first: two critters eat flies, and
-- each gets a pair. (constructor first also
-- works, but then we take h apart twice.)
example (c : Critter) :
    Eats c fly →
    Swims c ∧ Above c algae := by
  intro h
  cases h with
  | frog_fly =>
    exact ⟨Swims.frog,
      Above.trans Eats.frog_fly
        (Above.step Eats.fly_algae)⟩
  | fish_fly =>
    exact ⟨Swims.fish,
      Above.trans Eats.fish_fly
        (Above.step Eats.fly_algae)⟩
-- ANCHOR_END: ex3

-- ANCHOR: ex4
-- Five goals in all: frog, fish and duck
-- eat snails; frog and fish eat flies.
example (c : Critter) :
    Eats c snail ∨ Eats c fly →
    Swims c := by
  intro h
  cases h with
  | inl hs =>
    cases hs
    · exact Swims.frog
    · exact Swims.fish
    · exact Swims.duck
  | inr hf =>
    cases hf
    · exact Swims.frog
    · exact Swims.fish
-- ANCHOR_END: ex4
