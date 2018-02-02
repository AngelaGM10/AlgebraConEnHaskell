\begin{code}
module TAHStronglyDiscrete 
  ( StronglyDiscrete(member)
  , propStronglyDiscrete
  ) where

import TAHCommutative
import TAHIdeal
\end{code}

\begin{defi}
Un anillo se llama discreto si la igualdad es decidible.
\end{defi}

\begin{defi}
Un anillo es fuertemente discreto si podemos decidir que un elemento de un ideal es decidible, es decir, podemos decidir si un sistema $a_1x_1+..+a_nx_n = b$ tiene solución o no.
\end{defi}

\begin{code}
class Ring a => StronglyDiscrete a where
  member :: a -> Ideal a -> Maybe [a]
\end{code}

Damos a continuación la función para comprobar si un elemento está en el ideal o no.
\begin{code}
propStronglyDiscrete :: (CommutRing a, StronglyDiscrete a, Eq a)
                     => a -> Ideal a -> Bool                  
propStronglyDiscrete x id@(Id xs) = case member x id of
  Just as -> x == sumRing (zipWith (<**>) xs as) && length xs == length as
  Nothing -> True
\end{code}
