-- Chapter 10: expressions that carry types.
import Pond
open Critter

-- ANCHOR: ty
inductive Ty where
  | nat | bool
-- ANCHOR_END: ty

-- ANCHOR: denote
abbrev Ty.denote : Ty → Type
  | .nat  => Nat
  | .bool => Bool
-- ANCHOR_END: denote

-- ANCHOR: denote_rfl
example : Ty.denote .nat = Nat := rfl
example : Ty.nat.denote = Nat := rfl
-- ANCHOR_END: denote_rfl

-- ANCHOR: expr
inductive Expr : Ty → Type where
  | lit  : Nat → Expr .nat
  | tt   : Expr .bool
  | ff   : Expr .bool
  | plus : Expr .nat → Expr .nat → Expr .nat
  | le   : Expr .nat → Expr .nat →
           Expr .bool
  | ite  : Expr .bool → Expr t → Expr t →
           Expr t
-- ANCHOR_END: expr

-- ANCHOR: checks
#check Expr.lit 2
#check Expr.tt
-- ANCHOR_END: checks

-- ANCHOR: checkplus
#check Expr.plus
-- ANCHOR_END: checkplus

-- ANCHOR: checkite
#check Expr.ite
-- ANCHOR_END: checkite

-- ANCHOR: flies
def caught : Expr .nat :=
  .plus (.lit 2) (.lit 3)

def enough : Expr .bool :=
  .le (.lit 4) caught

def snack : Expr .nat :=
  .ite enough caught (.lit 0)
-- ANCHOR_END: flies

-- ANCHOR: eval
def eval : Expr t → t.denote
  | .lit n      => n
  | .tt         => true
  | .ff         => false
  | .plus a b   => eval a + eval b
  | .le a b     => decide (eval a ≤ eval b)
  | .ite c a b  =>
    if eval c then eval a else eval b
-- ANCHOR_END: eval

-- ANCHOR: checkeval
#check eval
-- ANCHOR_END: checkeval

-- ANCHOR: evals
#eval eval caught
#eval eval enough
#eval eval snack
-- ANCHOR_END: evals
