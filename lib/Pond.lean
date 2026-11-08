/-! The Little Leaner: the pond. Who lives here, and who eats whom.
Every chapter file starts with `import Pond` and `open Critter`.
Chapter 1 explains `Critter`; Chapter 2 explains `Eats`. -/

-- ANCHOR: critter
inductive Critter where
  | algae | fly | snail | frog
  | fish | heron | duck | otter
  deriving Repr, DecidableEq
-- ANCHOR_END: critter

namespace Critter

-- ANCHOR: all
def all : List Critter :=
  [algae, fly, snail, frog,
   fish, heron, duck, otter]
-- ANCHOR_END: all

end Critter

open Critter

-- ANCHOR: Eats
inductive Eats : Critter → Critter → Prop where
  | snail_algae : Eats snail algae
  | fly_algae   : Eats fly   algae
  | frog_fly    : Eats frog  fly
  | frog_snail  : Eats frog  snail
  | fish_fly    : Eats fish  fly
  | fish_snail  : Eats fish  snail
  | duck_snail  : Eats duck  snail
  | duck_algae  : Eats duck  algae
  | heron_frog  : Eats heron frog
  | heron_fish  : Eats heron fish
  | otter_fish  : Eats otter fish
-- ANCHOR_END: Eats

-- ANCHOR: habits
inductive Swims : Critter → Prop where
  | frog : Swims frog
  | fish : Swims fish
  | duck : Swims duck
  | otter : Swims otter

inductive Flies : Critter → Prop where
  | fly : Flies fly
  | heron : Flies heron
  | duck : Flies duck

inductive Plant : Critter → Prop where
  | algae : Plant algae
-- ANCHOR_END: habits
