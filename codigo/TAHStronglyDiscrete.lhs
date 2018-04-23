\begin{code}
module TAHStronglyDiscrete 
  ( StronglyDiscrete(member)
  , propStronglyDiscrete
  ) where

import TAHCommutative
import TAHIdeal
\end{code}

Para desarrollar esta pequeña sección, importamos los módulos TAHConmutative y TAHIdeal. Veamos antes unas definiciones teóricas.

\begin{defi}
Un anillo se llama discreto si la igualdad es decidible.
\end{defi}\\

Todos los anillos que consideremos serán discretos. Pero hay muchos ejemplos de anillos que no son discretos. Por ejemplo, $\mathbb{R}$ no es discreto ya que es no es posible decidir si dos números irracionales son iguales en tiempo finito.

\begin{defi}
Un anillo es fuertemente discreto si podemos decidir que un elemento de un ideal es decidible.
\end{defi}

Para introducir este concepto crearemos una clase restringida a la clase de tipo $Ring$:

\begin{code}
class Ring a => StronglyDiscrete a where
  member :: a -> Ideal a -> Maybe [a]
\end{code}

Hemos creado la función $member$ con la cual, mediante el constructor $Maybe$ podemos decidir si el parámetro $a$ es de tipo $Ideal$ o no.\\

Damos a continuación la función para comprobar si un anillo conmutativo es fuertemente discreto.
\begin{code}
propStronglyDiscrete :: (CommutRing a, StronglyDiscrete a, Eq a)
                     => a -> Ideal a -> Bool                  
propStronglyDiscrete x id@(Id xs) = case member x id of
  Just as -> x == sumRing (zipWith (<**>) xs as) && length xs == length as
  Nothing -> True
\end{code}

Explicamos brevemente como funciona $propStronglyDiscrete$. Esta recibe como argumentos un elemento $x$ y $id@(Id \,\,xs)$ con $@$ lo que hacemos es crear una función o guardar un valor en $id$ de forma de que cuando llamemos a $id$ nos estamos refiriendo a $(Id\,\, xs)$. En primer lugar con $case .. of$ nos preguntamos si $x$ pertenece al ideal generado por $xs$, es decir si $x$ es un elemento del ideal.En particular, si pertenece, devuelve $(Just\,\, as)$ donde $as$ es la lista de coeficientes de la expresión de $x$ como combinación lineal de los generadores del ideal y, en caso contrario, $Nothing$. Si esto se verifica devuelve $True$ y nuestro anillo es fuertemente discreto.

