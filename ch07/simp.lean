-- Chapter 7: letting simp do the computing.
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

-- ANCHOR: len_app
theorem len_app (xs ys : List Critter) :
    len (app xs ys) = len xs + len ys := by
  induction xs with
  | nil => simp [app, len]
  | cons x xs ih =>
    simp [app, len, ih]
    -- ANCHOR: len_app_simp
    trace_state
    -- ANCHOR_END: len_app_simp
    omega
-- ANCHOR_END: len_app

-- ANCHOR: app_nil
@[simp]
theorem app_nil (xs : List Critter) :
    app xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [app, ih]
-- ANCHOR_END: app_nil

-- ANCHOR: app_assoc
@[simp]
theorem app_assoc
    (xs ys zs : List Critter) :
    app (app xs ys) zs
      = app xs (app ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [app, ih]
-- ANCHOR_END: app_assoc

-- ANCHOR: rev_app
@[simp]
theorem rev_app (xs ys : List Critter) :
    rev (app xs ys)
      = app (rev ys) (rev xs) := by
  induction xs with
  | nil => simp [app, rev]
  | cons x xs ih => simp [app, rev, ih]
-- ANCHOR_END: rev_app

-- ANCHOR: rev_rev
@[simp]
theorem rev_rev (xs : List Critter) :
    rev (rev xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rev, app, ih]
-- ANCHOR_END: rev_rev

-- ANCHOR: plain
example (xs ys : List Critter) :
    rev (rev (app xs ys)) = app xs ys := by
  simp
-- ANCHOR_END: plain

-- ANCHOR: why
example (xs ys : List Critter) :
    rev (rev (app xs ys)) = app xs ys := by
  simp?
-- ANCHOR_END: why
