-- expect: error
-- Chapter 1: a string is not a critter.
import Pond
open Critter

-- ANCHOR: string
#check ("frog" : Critter)
-- ANCHOR_END: string
