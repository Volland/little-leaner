-- Chapter 5: numbers built by hand.
import Pond
open Critter

-- ANCHOR: N
inductive N where
  | zero
  | succ (n : N)
  deriving Repr

open N
-- ANCHOR_END: N

-- ANCHOR: two
#check succ (succ zero)
-- ANCHOR_END: two

-- ANCHOR: plain
set_option pp.fieldNotation false
#check succ (succ zero)
-- ANCHOR_END: plain

-- ANCHOR: types
#check zero
#check succ
-- ANCHOR_END: types

-- ANCHOR: eval
#eval succ (succ zero)
-- ANCHOR_END: eval

-- ANCHOR: add
def N.add : N → N → N
  | m, zero   => m
  | m, succ n => succ (add m n)
-- ANCHOR_END: add

-- ANCHOR: names
def one : N := succ zero
def two : N := succ one
-- ANCHOR_END: names

-- ANCHOR: sum
#eval add one two
-- ANCHOR_END: sum

-- ANCHOR: sumcheck
#check add one two
-- ANCHOR_END: sumcheck
