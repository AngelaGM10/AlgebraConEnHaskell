\begin{code}
module TAHCoherent
  ( Coherent(solve),
isSolution

  ) where

import Test.QuickCheck

import TAHIntegralDomain
import TAHStronglyDiscrete
import TAHIdeal


import qualified Data.Vector as V
import qualified Data.Matrix as M

class IntegralDomain a => Coherent a where
solve :: V.Vector a -> M.Matrix a
solve = undefined
\end{code}

\begin{code}
-- | Test para comprobar que la segunda matriz es una solución de la primera.
isSolution :: (CommutRing a, Eq a) => [[a]] ->  [[a]] -> Bool
isSolution m sol = all (==zero) (M.toList (M.fromLists(m) * M.fromLists(sol)))

propCoherent :: (Coherent a, Eq a) => V.Vector a -> Bool
propCoherent m = isSolution (M.fromLists(m)) (solve m)

\end{code}

