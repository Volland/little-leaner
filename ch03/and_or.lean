-- Chapter 3: "and" and "or" are rules too.
import Pond
open Critter

inductive Above :
    Critter → Critter → Prop where
  | step  : Eats x y → Above x y
  | trans : Eats x y → Above y z → Above x z

theorem flyEater (c : Critter) :
    Eats c fly → Above c algae := by
  intro h
  exact Above.trans h (Above.step Eats.fly_algae)

-- ANCHOR: and
example : Swims frog ∧ Eats frog fly := by
  constructor
  -- ANCHOR: and1
  trace_state
  -- ANCHOR_END: and1
  · exact Swims.frog
  · exact Eats.frog_fly
-- ANCHOR_END: and

-- ANCHOR: pair
example : Swims frog ∧ Eats frog fly :=
  ⟨Swims.frog, Eats.frog_fly⟩
-- ANCHOR_END: pair

-- ANCHOR: andIntro
#check And.intro
-- ANCHOR_END: andIntro

-- ANCHOR: obtain
example (c : Critter) :
    Swims c ∧ Eats c fly →
    Above c algae := by
  intro h
  obtain ⟨hs, hf⟩ := h
  -- ANCHOR: obtain1
  trace_state
  -- ANCHOR_END: obtain1
  exact flyEater c hf
-- ANCHOR_END: obtain

-- ANCHOR: left
example : Swims duck ∨ Flies duck := by
  left
  -- ANCHOR: left1
  trace_state
  -- ANCHOR_END: left1
  exact Swims.duck
-- ANCHOR_END: left

-- ANCHOR: right
example : Swims duck ∨ Flies duck := by
  right
  exact Flies.duck
-- ANCHOR_END: right

-- ANCHOR: orIntro
#check Or.inl
#check Or.inr
-- ANCHOR_END: orIntro

-- ANCHOR: cases
example (c : Critter) :
    Eats c fly ∨ Eats c snail →
    Above c algae := by
  intro h
  cases h with
  | inl hf =>
    -- ANCHOR: cases1
    trace_state
    -- ANCHOR_END: cases1
    exact flyEater c hf
  | inr hs =>
    -- ANCHOR: cases2
    trace_state
    -- ANCHOR_END: cases2
    apply Above.trans hs
    exact Above.step Eats.snail_algae
-- ANCHOR_END: cases
