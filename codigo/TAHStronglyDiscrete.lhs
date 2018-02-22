\begin{code}
module TAHStronglyDiscrete 
  ( StronglyDiscrete(member)
  , propStronglyDiscrete
  ) where

import TAHCommutative
import TAHIdeal
\end{code}

Para desarrolla esta pequeña sección, importamos los módulos TAHConmutative y TAHIdeal. Veamos antes unas definiciones teóricas.

\begin{defi}
Un anillo se llama discreto si la igualdad es decidible.
\end{defi}\\

Todos los anillos consideremos serán discretos. Pero hay muchos ejemplos de anillos que no son discretos. Por ejemplo, R no es discreto ya que es no es posible decidir si dos números irracionales son iguales en tiempo finito.

\begin{defi}
Un anillo es fuertemente discreto si podemos decidir que un elemento de un ideal es decidible.
\end{defi}

Esta propiedad es muy fuerte. Muchos de los anillos que hemos visto hasta ahora son muy discreto, esto de hecho está estrechamente relacionado con si la división es decidible en el anillo.\\

Para introducir este concepto crearemos una clase restringida a la clase de tipo $Ring$.

\begin{code}
class Ring a => StronglyDiscrete a where
  member :: a -> Ideal a -> Maybe [a]
\end{code}

Para definir la función $member$ hemos utilizado $Maybe$, un constructor de tipo. La $a$ es un parámetro de tipo. Ningún valor puede tener un tipo que sea simplemente $Maybe$, ya que eso no es un tipo por si mismo, es un constructor de tipos. Para que sea un tipo real que algún valor pueda tener, tiene que tener todos los parámetros de tipo definidos. De esta forma, con $Maybe$ lo que estamos haciendo es decidir si el parámetro $a$ es de tipo $Ideal$ o no.\\

Damos a continuación la función para comprobar si un anillo conmutativo es fuertemente discreto.
\begin{code}
propStronglyDiscrete :: (CommutRing a, StronglyDiscrete a, Eq a)
                     => a -> Ideal a -> Bool                  
propStronglyDiscrete x id@(Id xs) = case member x id of
  Just as -> x == sumRing (zipWith (<**>) xs as) && length xs == length as
  Nothing -> True
\end{code}

Explicamos brevemente como funciona $propStronglyDiscrete$. Esta recibe como argumentos un elemento $x$ y $id@(Id \,\,xs)$ con $@$ lo que hacemos es como crear una función o guardar un valor en $id$ de forma de que cuando llamemos a $id$ nos estamos refiriendo a $Id\,\, xs$. En primer lugar con $case .. of$ nos preguntamos si $x$ pertenece al ideal generado por $xs$, es decir si $x$ es un elemento del ideal. En caso de que sí pertenezca, debe de existir una lista $as$ tal que el elemento $x$ sea igual a la suma del anillo generado por la multiplicación de elementos a pares de $xs$ y $as$, así como que ambas listas deben tener la misma longitud. Si esto se verifica devuelve $True$ y nuestro anillo es fuertemente discreto.
