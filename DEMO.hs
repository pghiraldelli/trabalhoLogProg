module DEMO
    (
     module Data.List,
     module Data.Char, 
     module Models,
     module Display,
     module MinBis,
     module ActEpist,
     module MinAE,
     module DPLL,
     module Semantics
    )
    where

import Data.List
import Data.Char
import Models
import Display
import MinBis
import ActEpist
import MinAE
import DPLL 
import Semantics

version :: String
version = "DEMO 1.03, Summer 2005"

initM = initE [P 1, P 2, P 3, P 4]
upM   = upd initM (groupM [a,b] p1)

measure :: (Eq a,Ord a) => (Model a b,a) -> Maybe [Int]
measure (m,w) = 
  let 
    f           = filter (\ (us,vs) -> elem w us || elem w vs) 
    g [(xs,ys)] = length ys - 1
  in 
    case kd45 (domain m) (access m) of 
      Just a_balloons -> Just 
         ( [ g (f balloons) | (a,balloons) <- a_balloons  ])
      Nothing         -> Nothing 

