-- expect: error
-- Chapter 10: ill-typed expressions.
import Pond
open Critter

inductive Ty where
  | nat | bool

abbrev Ty.denote : Ty → Type
  | .nat  => Nat
  | .bool => Bool

inductive Expr : Ty → Type where
  | lit  : Nat → Expr .nat
  | tt   : Expr .bool
  | ff   : Expr .bool
  | plus : Expr .nat → Expr .nat → Expr .nat
  | le   : Expr .nat → Expr .nat →
           Expr .bool
  | ite  : Expr .bool → Expr t → Expr t →
           Expr t

-- ANCHOR: plus
def bad : Expr .nat :=
  .plus .tt (.lit 1)
-- ANCHOR_END: plus

-- ANCHOR: ite
def odd : Expr .nat :=
  .ite .tt (.lit 1) .ff
-- ANCHOR_END: ite
