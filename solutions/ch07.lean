-- Solutions to the exercises of Chapter 7.
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

def mapL (f : Critter → Critter) :
    List Critter → List Critter
  | []      => []
  | x :: xs => f x :: mapL f xs

theorem len_app (xs ys : List Critter) :
    len (app xs ys) = len xs + len ys := by
  induction xs with
  | nil => simp [app, len]
  | cons x xs ih =>
    simp [app, len, ih]
    omega

-- ANCHOR: ex1
-- Induction on xs, because mapL recurses
-- on its list. In the cons case the goal is
-- len (mapL f (x :: xs)) = len (x :: xs).
theorem len_map (f : Critter → Critter)
    (xs : List Critter) :
    len (mapL f xs) = len xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    trace_state
    rw [mapL, len, len, ih]
-- ANCHOR_END: ex1

-- ANCHOR: ex2
-- Induction on xs: both app and mapL take
-- xs apart, and ys is never looked at.
theorem map_app (f : Critter → Critter)
    (xs ys : List Critter) :
    mapL f (app xs ys)
      = app (mapL f xs) (mapL f ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [app, mapL, mapL, ih]
    rfl
-- ANCHOR_END: ex2

-- ANCHOR: ex3
-- After rw [rev, len_app] the goal is
-- len (rev xs) + len [x] = len (x :: xs).
theorem len_rev (xs : List Critter) :
    len (rev xs) = len xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [rev, len_app]
    trace_state
    rw [ih]
    rfl
-- ANCHOR_END: ex3

-- ANCHOR: ex4
-- The cons case needs map_app from
-- Exercise 7.2, the way rev_rev needed
-- rev_app.
theorem rev_map (f : Critter → Critter)
    (xs : List Critter) :
    rev (mapL f xs) = mapL f (rev xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [mapL, rev, rev, map_app, ih]
    rfl
-- ANCHOR_END: ex4
