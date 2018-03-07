\begin{code}
module TAHCoherent
  ( Coherent(solve)

  ) where

import Test.QuickCheck

import TAHIntegralDomain
import TAHStronglyDiscrete
import TAHIdeal


import qualified Data.Vector as V
import qualified Data.Matrix as M

class IntegralDomain a => Coherent a where
solve :: V.Vector a -> M.Matrix a
\end{code}


