\begin{code}
-- |Ideal finitamente generado en un anillo conmutativo.

module TAHIdeal
  ( Ideal(Id)
  , zeroIdeal, isPrincipal, fromId
  , addId, mulId
  , isSameIdeal, zeroIdealWitnesses
  ) where

import Data.List (intersperse,nub)
import Test.QuickCheck

import TAHCommutative
\end{code}

Para desarrollar está sección importamos el módulo $TAHConmutative$.\\

\begin{defi}
Sea $(R,+,*)$ un anillo. Un ideal de $R$ es un subconjunto $I \subset\, R$ tal que
1. $(I, +)$ es un subgrupo de $(R, +)$.
2. $RI \subset\, I$.
Es decir, $\forall\,\, a \in\, A \forall\, b \in\, I, ab \in\, I$.
\end{defi}

Podemos decir que los ideales se pueden describir como los subgrupos aditivos de un anillo $(R,+,*)$, en nuestro caso conmutativo, que es
cerrado bajo la multiplicación por cualquier elemento de R. Los dos ideales canónicos son el cero ideal $<0>$ y todo el anillo R.\\

La definición anterior da ideales arbitrarios de anillos y no es factible para el algebra constructiva. Enunciaremos otra definión de los ideales que nos proporcionará ideales finitamente generados, estos se pueden implementar en Haskell.\\

\begin{defi}
Sea $(R,+,*)$ un anillo, y $E$ un subconjunto de $R$. Se define el ideal generado por $E$, y
se denota $<E>$, como la intersección de todos los ideales que contienen a $E$ (que es una familia no 
vacía puesto que $R$ es un ideal que contiene a $E$).
\end{defi}

Para el tipo de dato de los Ideales, en anteriores versiones de Haskell podiamos introducir una restricción al tipo que ibamos a definir mediante el constructor $data$, pero actualmente no se puede. El constructor $data$ significa que vamos a definir un nuevo tipo de dato. La parte de la izquierda del $=$ denota el tipo y la parte de la derecha son los constructores de datos. Estos especifican los diferentes valores que puede tener un tipo.\\

Sin embargo los ideales con los que trabajaremos están restringidos a anillos conmutativos. Para aplicar dicha restricción, lo haremos en cada definición de instancia o función, quedando explicito que usaremos los anillos conmutativos con la clase definida anteriormente como $CommutRing$.

\begin{code}
-- |Ideales caracterizados por una lista de generadores.
data Ideal a = Id [a]

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

Explicamos varios conceptos de Haskell utilizados en las anteriores líneas de código. Comenzamos por explicar las funciones utilizadas para declarar mediante una instancia a un ideal. La clase $Show$ convierte el elemento que recibe en una cadena legible, y la función $intersperse$toma un elemento y una lista, e intercala el elemento entre cada uno de los elementos de la lista. Por ejemplo: $intersperse\,\, ','\,\, "abcde" == "a,b,c,d,e"$. Con ambas funciones damos la forma de presentación del ideal, tal y como se representa de forma teórica.\\

Para la segunda instancia hemos utilizado la clase $Arbitrary$, esta proviene de la líbrería $QuickCheck$, proporciona una generación aleatoria y proporciona valores reducidos. Gracias a esta clase, con la segunda instancia podemos generar ideales de forma aleatoria. Esto nos ayudará a testear las funciones a verificar para ser un ideal. En esta misma instancia se hace uso de la función $filter$, es una función que toma un predicado (un predicado es una función que dice si algo es cierto o falso, o en nuestro caso, una función que devuelve un valor booleano) y una lista y devuelve una lista con los elementos que satisfacen el predicado. La función $filter$ la utilizamos para eliminar los elementos nulos, si los hubiese, de la lista que toma.\\

Tanto la función $filter$ como $foldr$ son funciones de orden superior. Las funciones de Haskell pueden tomar funciones como parámetros y devolver funciones como resultado. Una función que hace ambas cosas o alguna de ellas se llama función de orden superior.
Generación aleatoria y reducción de valores.\\

Finalmente hemos implementado uno de los ideales canónicos, el ideal cero, $<0>$. A continuación, damos la definición teórica de ideal principal.\\

\begin{defi}
Un ideal $I \subset R$ se llama principal si se puede generar por un sólo elemento. Es
decir, si $I = <a>$, para un cierto $a \in\,\,R$.
\end{defi}
\\
Los anillos como $Z$ en los cuales todos los ideales son principales se llaman clásicamente 
dominios de ideales principales. Pero constructivamente esta definición no es adecuada. Sin embargo, estamos considerando anillos conmutativos en los cuales todos los ideales son finitamente generados. Por tanto, estos son representados por un conjunto finito, y esto si podemos implementarlo a nivel computacional.

\begin{code}
isPrincipal :: CommutRing a => Ideal a -> Bool
isPrincipal (Id xs) = length xs == 1
\end{code}

Mediante la función $fromId$, definida a continuación, mostramos el ideal en forma de lista. 

\begin{code}
fromId :: CommutRing a => Ideal a -> [a]
fromId (Id xs) = xs
\end{code}

Ahora veamos algunas operaciones sobre ideales y propiedades fundamentales de ideales. Como pueden ser la suma y multiplicación. En ellas haremos uso de la función $nub$, esta elimina los elementos repetidos de una lista. Por último daremos una función para identificar si dos ideales son el mismo ideal.\\

La intersección de dos ideales es también un ideal. Pero no hay un método general para calcular el conjunto de generadores para la intersección de dos ideales en anillos arbitrarios. Por ello, daremos una función que nos indique si se puede realizar dicha operación o no.

\begin{code}
-- | Suma de ideales.
addId :: (CommutRing a, Eq a) => Ideal a -> Ideal a -> Ideal a
addId (Id xs) (Id ys) = Id (nub (xs ++ ys))

-- | Multiplicación de ideales.
mulId :: (CommutRing a, Eq a) => Ideal a -> Ideal a -> Ideal a
mulId (Id xs) (Id ys) = if zs == [] then zeroIdeal else Id zs
  where zs = nub [ f <**> g | f <- xs, g <- ys, f <**> g /= zero ]

-- | Comprueba si se puede realizar la intersección de dos ideales.

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

Explicamos con más detenimiento como funciona $isSameIdeal$, recibe como argumento una operación $op$ que representa la intersección y dos ideales. Devuelve un booleano, si devuelve $True$ nos indica que se puede realizar la intersección entre ambos ideales. Para ello, toma una terna formada por: (un ideal, lista de anillos conmutativos, lista de anillos conmutativos), seguido de un booleano sobre dos ideales. Realiza 3 comprobaciones, la primera comprueba que la longitud de las dos listas de la terna sean la misma que la del ideal de la terna. La segunda comprueba, mediante elementos de ambas listas tomadas a pares $zs$ con $as$, que cada elemento del ideal $zs$ sea el mismo que el elemento resultante al aplicar $sumRing$ sobre el anillo generado con la función $zipWith$ y además que la longitud de ambos coincida. La tercera es análoga a la anterior cambiando $as$ por $bs$.\\

La función $zipWith$ generaliza a la función $zip$ comprimiendo con la función dada como primer argumento, en lugar de una función de tuplas. Por ejemplo, $zipWith (+)$ se aplica a dos listas para producir la lista de sumas correspondientes.\\


Para finalizar esta sección, implementamos una función que recibe como argumentos dos listas, por ejemplo $xs$ e $ys$, y devuelve una terna de la forma: (el ideal canónico cero, una lista de ceros de la misma lontitud que, para nuestro ejemplo, $xs$,  una lista de ceros de la misma lontitud que $ys$)

\begin{code}
zeroIdealWitnesses :: (CommutRing a) => [a] -> [a] -> (Ideal a, [[a]], [[a]])
zeroIdealWitnesses xs ys = ( zeroIdeal
                           , [replicate (length xs) zero]
                           , [replicate (length ys) zero])
\end{code}
