-- Chapter 7: laws of lists, by induction.
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
-- ANCHOR: len_app_top
theorem len_app (xs ys : List Critter) :
    len (app xs ys) = len xs + len ys := by
  induction xs with
-- ANCHOR_END: len_app_top
  | nil =>
    -- ANCHOR: len_nil
    trace_state
    -- ANCHOR_END: len_nil
    rw [app, len]
    -- ANCHOR: len_nil2
    trace_state
    -- ANCHOR_END: len_nil2
    rw [Nat.zero_add]
  | cons x xs ih =>
    -- ANCHOR: len_cons
    trace_state
    -- ANCHOR_END: len_cons
    rw [app, len, len]
    -- ANCHOR: len_cons2
    trace_state
    -- ANCHOR_END: len_cons2
    rw [ih]
    -- ANCHOR: len_cons3
    trace_state
    -- ANCHOR_END: len_cons3
    omega
-- ANCHOR_END: len_app

-- ANCHOR: guess
#eval rev (app [heron, frog] [fly])
#eval app (rev [fly]) (rev [heron, frog])
-- ANCHOR_END: guess

-- ANCHOR: app_nil
theorem app_nil (xs : List Critter) :
    app xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    -- ANCHOR: app_nil_cons
    trace_state
    -- ANCHOR_END: app_nil_cons
    rw [app, ih]
-- ANCHOR_END: app_nil

-- ANCHOR: app_assoc
theorem app_assoc
    (xs ys zs : List Critter) :
    app (app xs ys) zs
      = app xs (app ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [app, app, app]
    -- ANCHOR: assoc_cons
    trace_state
    -- ANCHOR_END: assoc_cons
    rw [ih]
-- ANCHOR_END: app_assoc

-- ANCHOR: rev_app
theorem rev_app (xs ys : List Critter) :
    rev (app xs ys)
      = app (rev ys) (rev xs) := by
  induction xs with
  | nil =>
    rw [app, rev]
    -- ANCHOR: rev_app_nil
    trace_state
    -- ANCHOR_END: rev_app_nil
    rw [app_nil]
  | cons x xs ih =>
    rw [app, rev, rev, ih]
    -- ANCHOR: rev_app_cons
    trace_state
    -- ANCHOR_END: rev_app_cons
    rw [app_assoc]
-- ANCHOR_END: rev_app

-- ANCHOR: rev_rev
theorem rev_rev (xs : List Critter) :
    rev (rev xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [rev, rev_app, ih]
    -- ANCHOR: rev_rev_cons
    trace_state
    -- ANCHOR_END: rev_rev_cons
    rfl
-- ANCHOR_END: rev_rev
