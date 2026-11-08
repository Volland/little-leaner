-- Chapter 10: a language with no types.
import Pond
open Critter

-- ANCHOR: raw
inductive Raw where
  | lit  : Nat → Raw
  | tt   : Raw
  | ff   : Raw
  | plus : Raw → Raw → Raw
  | le   : Raw → Raw → Raw
  | ite  : Raw → Raw → Raw → Raw
-- ANCHOR_END: raw

-- ANCHOR: val
inductive Val where
  | nat  : Nat → Val
  | bool : Bool → Val
  deriving Repr
-- ANCHOR_END: val

-- ANCHOR: eval
def eval : Raw → Option Val
  | .lit n => some (.nat n)
  | .tt    => some (.bool true)
  | .ff    => some (.bool false)
  | .plus a b =>
    match eval a, eval b with
    | some (.nat x), some (.nat y) =>
      some (.nat (x + y))
    | _, _ => none
  | .le a b =>
    match eval a, eval b with
    | some (.nat x), some (.nat y) =>
      some (.bool (decide (x ≤ y)))
    | _, _ => none
  | .ite c a b =>
    match eval c with
    | some (.bool true)  => eval a
    | some (.bool false) => eval b
    | _ => none
-- ANCHOR_END: eval

-- ANCHOR: good
#eval eval (.plus (.lit 2) (.lit 3))
-- ANCHOR_END: good

-- ANCHOR: bad
#eval eval (.plus .tt (.lit 1))
-- ANCHOR_END: bad

-- ANCHOR: badif
#eval eval (.ite (.lit 0) (.lit 1) (.lit 2))
-- ANCHOR_END: badif

-- ANCHOR: lucky
#eval eval (.ite .tt (.lit 1) .ff)
-- ANCHOR_END: lucky

-- ANCHOR: unlucky
#eval eval (.ite .ff (.lit 1) .ff)
-- ANCHOR_END: unlucky
