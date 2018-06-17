\begin{code}
module TAHStronglyDiscrete 
  ( StronglyDiscrete(member)
  , propStronglyDiscrete
  ) where

import TAHCommutative
import TAHIdeal
\end{code}

Para desarrollar esta sección, importamos los módulos \texttt{TAHConmutative} y \texttt{TAHIdeal}. Veamos antes unas definiciones teóricas.\\

\begin{defi}
Un anillo se llama discreto si la igualdad es decidible.
\end{defi}\\

Todos los anillos que consideremos serán discretos. Pero hay muchos ejemplos de anillos que no son discretos. Por ejemplo, $\mathbb{R}$ no es discreto ya que no es posible decidir si dos números irracionales son iguales en tiempo finito.\\

\begin{defi}
Un anillo es fuertemente discreto si la pertenencia a un ideal es decidible.
\end{defi}

Para introducir este concepto definimos una clase restringida a la clase de tipo $Ring$:

\begin{code}
class Ring a => StronglyDiscrete a where
  member :: a -> Ideal a -> Maybe [a]
\end{code}

El objetivo de este método es decidir si un elemento del anillo pertene al ideal, por ello hacemos uso del constructor \texttt{(Maybe\,\,[a])}. En el caso de que no pertenezca al ideal, \texttt{member} devolverá \texttt{Nothing}. Por otro lado, si un elemento pertenece a un ideal, significa que podemos escribir dicho elemento mediante una combinación lineal de los generadores del ideal. Por ello, si el elemento pertenece al ideal, \texttt{member} nos devolverá la lista con los coeficientes de los generadores del ideal al que el elemento pertenece.\\

Para verificar que una especificación concreta de \texttt{member} es correcta definimos una función que denotaremos \texttt{(propStronglyDiscrete\,\,x\,\,id@(Id xs))}, esta devolverá un booleano, \texttt{True} cuando \texttt{member} haya funcionado bien y \texttt{False} cuando no haya devuelto lo esperado. En caso de que no pertenezca al ideal y devuelva \texttt{Nothing} significa que funciona correctamente luego obtendremos \texttt{True}. Si \texttt{x} pertenece al ideal generado por \texttt{xs} entonces comprobará que la lista de coeficientes que \texttt{member} ha devuelto al multiplicarla por la lista de generadores del ideal, \texttt{xs}, la suma resultante es \texttt{x} y entonces devolverá  \texttt{True}.

\index{\texttt{propStronglyDiscrete}}
\begin{code}
propStronglyDiscrete :: (CommutRing a, StronglyDiscrete a, Eq a)
                     => a -> Ideal a -> Bool                  
propStronglyDiscrete x id@(Id xs) = case member x id of
  Just as -> x == sumRing (zipWith (<**>) xs as) && length xs == length as
  Nothing -> True
\end{code}


