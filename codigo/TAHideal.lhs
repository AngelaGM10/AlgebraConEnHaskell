\begin{code}
-- |Ideales finitamente generados en anillos conmutativos.

module TAHideal
  ( Ideal(Id)
  , zeroIdeal, isPrincipal, fromId
  , eval, addId, mulId
  , isSameIdeal, zeroIdealWitnesses
  ) where

import Data.List (intersperse,nub)
import Test.QuickCheck

import TAHCommutative
\end{code}
\begin{defi}
Sea $(R,+,*)$ un anillo. Un ideal de $R$ es un subconjunto $I \subset\, R$ tal que
1. $(I, +)$ es un subgrupo de $(R, +)$.
2. $RI \subset\, I$.
Es decir, $\forall\,\, a \in\, A \forall\, b \in\, I, ab \in\, I$.
\end{defi}

\begin{defi}
Sea R un anillo, y E un subconjunto de R. Se define el ideal generado por E, y
se denota $<E>$, como la intersección de todos los ideales que contienen a E (que es una familia no 
vacía puesto que R es un ideal que contiene a E).
\end{defi}

\begin{code}
-- |Ideales caracterizados por una lista de generadores.
data CommutRing a => Ideal a = Id [a]

instance (CommutRing a, Show a) => Show (Ideal a) where
  show (Id xs) = "<" ++ concat (intersperse "," (map show xs)) ++ ">"

instance (CommutRing a, Arbitrary a, Eq a) => Arbitrary (Ideal a) where
  arbitrary = do xs' <- arbitrary
                 let xs = filter (/= zero) xs'
                 if xs == [] then return (Id [one]) else return (Id (nub xs))

-- | El ideal cero.
zeroIdeal :: CommutRing a => Ideal a
zeroIdeal = Id [zero]
\end{code}

\begin{defi}
Un ideal $I \subset R$ se llama principal si se puede generar por un sólo elemento. Es
decir, si $I = <a>$, para un cierto $a \in\,\,R$.
\end{defi}

\begin{code}
isPrincipal :: CommutRing a => Ideal a -> Bool
isPrincipal (Id xs) = length xs == 1

fromId :: CommutRing a => Ideal a -> [a]
fromId (Id xs) = xs
\end{code}

\begin{code}
-- |Evaluar un ideal en un cierto punto.
eval :: CommutRing a => a -> Ideal a -> a
eval x (Id xs) = foldr (<+>) zero (map (<**> x) xs)
\end{code}

La propiedad más importante de los ideales es que sirven para definir los anillos cocientes. Dado
un ideal $I \subset\, R$, sabemos que $(I, +)$ es un subgrupo (abeliano) de $(R, +)$, y por tanto podemos
considerar el grupo cociente $A/I$. Lo interesante es que en este grupo cociente, además de la
suma: $(a + I) + (b + I) = (a + b) + I$,
\begin{code}
-- | Addition of ideals.
addId :: (CommutRing a, Eq a) => Ideal a -> Ideal a -> Ideal a
addId (Id xs) (Id ys) = Id (nub (xs ++ ys))
\end{code}
se puede definir un producto, de forma natural: $(a + I)(b + I) = ab + I$.

\begin{code}
-- |  Multiplication of ideals.
mulId :: (CommutRing a, Eq a) => Ideal a -> Ideal a -> Ideal a
mulId (Id xs) (Id ys) = if zs == [] then zeroIdeal else Id zs
  where zs = nub [ f <**> g | f <- xs, g <- ys, f <**> g /= zero ]
\end{code}
Este producto está bien definido porque $I$ es un ideal. Además, la suma y el producto de clases de
equivalencia que acabamos de definir, cumplen las propiedades necesarias que hacen de $R/I$ un
anillo: El anillo cociente de $R$ sobre $I$.

Para saber si dos ideales son el mismo usaremos la siguiente función:
\begin{code}
isSameIdeal :: (CommutRing a, Eq a) 
            => (Ideal a -> Ideal a -> (Ideal a, [[a]], [[a]]))
            -> Ideal a 
            -> Ideal a 
            -> Bool
isSameIdeal op (Id xs) (Id ys) = 
  let (Id zs, as, bs) = (Id xs) `op` (Id ys)
  in length as == length zs && length bs == length zs
     &&
     and [ z_k == sumRing (zipWith (<**>) a_k xs) && length a_k == length xs
         | (z_k,a_k) <- zip zs as ]
     &&
     and [ z_k == sumRing (zipWith (<**>) b_k ys) && length b_k == length ys
         | (z_k,b_k) <- zip zs bs ]
\end{code}

Daremos la función que genera dos listas de ideales que se completan con cero para calcular las intersecciones entre ideales.
\begin{code}
zeroIdealWitnesses :: (CommutRing a) => [a] -> [a] -> (Ideal a, [[a]], [[a]])
zeroIdealWitnesses xs ys = ( zeroIdeal
                           , [replicate (length xs) zero]
                           , [replicate (length ys) zero])
\end{code}



