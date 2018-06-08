
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
Sea $(R,+,*)$ un anillo. Un ideal de $R$ es un subconjunto $I \subset\, R$ tal que\\

1. $(I, +)$ es un subgrupo de $(R, +)$.\\

2. $RI \subset\, I$.\\

Es decir, $\forall\,\, a \in\, A \forall\, b \in\, I, ab \in\, I$.
\end{defi}

La definición anterior para ideales arbitrarios no es adecuada para definirla de forma constructiva. En la implementación en Haskell, nos reduciremos a los ideales finitamente generados.\\

\begin{defi}
Sea $(R,+,*)$ un anillo, y $E$ un subconjunto de $R$. Se define el ideal generado por $E$, y
se denota $<E>$, como la intersección de todos los ideales que contienen a $E$ (que es una familia no 
vacía puesto que $R$ es un ideal que contiene a $E$).
\end{defi}

Se llama ideal generado por los elementos $e_1,..,e_r$ de un anillo $(A,+,*)$ al conjunto $E = <e_1,..,e_r> := \{a_1e_1 + .. + a_re_r \,\,|\,\, a_1,..a_r \in\,\, A\}$. Este conjunto es el ideal de $A$ más pequeño que contiene a los elementos $e_1,..,e_r$. Cualquier elemento x del ideal generado por $E$, es una combinación lineal de los generadores. Es decir, si $x \in\,\, E$, existen coeficientes $\alpha_1,..,\alpha_r$ tales que $x=\alpha_1x_1+..+\alpha_rx_r$.\\

Para el tipo de dato de los Ideales, en anteriores versiones de Haskell podiamos introducir una restricción al tipo que ibamos a definir mediante el constructor $data$, pero actualmente no se puede. Mediante $data$ se define el tipo $Ideal\,\,a$, donde $a$ es un tipo cualquiera que representa los elementos del ideal. El constructor es $Id$ cuyo conjunto es una lista de elementos de $a$ (los generados del ideal).\\

Para especificar en Haskell el ideal generado por un conjunto finito $E$, con $data$ crearemos el tipo de dato mediante el constructor $Id$ y el conjunto $E$ se representará por una lista de elementos del anillo. Por ejemplo, en el anillo de los enteros $\mathbb{Z}$, el ideal generado por $<2,5>$ se representará por $(Id\, [2,5])$. Y el ideal canónico cero $<0>$ en cualquier anillo se representará
por $(Id\, [zero])$, hay dos ideales canónico el cero ideal y todo el anillo R, este último se representará por $(Id\, [one])$.\\

Los ideales con los que trabajaremos están restringidos a anillos conmutativos. Para aplicar dicha restricción, lo haremos en cada definición de instancia o función, quedando explicito que usaremos los anillos conmutativos con la clase definida anteriormente como $CommutRing$.
\index{\texttt{zeroIdeal}}
\begin{code}
-- |Ideales caracterizados por una lista de generadores.
data Ideal a = Id [a]

instance Show a => Show (Ideal a) where
  show (Id xs) = "<" ++ concat (intersperse "," (map show xs)) ++ ">"

instance (CommutRing a, Arbitrary a, Eq a) => Arbitrary (Ideal a) where
  arbitrary = do xs' <- arbitrary
                 let xs = filter (/= zero) xs'
                 if xs == [] then return (Id [one]) else return (Id (nub xs))

-- | El ideal cero.
zeroIdeal :: CommutRing a => Ideal a
zeroIdeal = Id [zero]
\end{code}

Al añadir $deriving (Show)$ al final de una declaración de tipo, automáticamente Haskell hace que ese tipo forme parte de la clase de tipos $Show$, y lo muestra como lo tenga por defecto. Mediante esta instancia modificamos esta presentación especificando como queremos que lo muestre. Por ejemplo, el ideal $(Id\, [2,5])$ se va a mostrar como $<2,5>$.\\  

Para la segunda instancia hemos utilizado la clase $Arbitrary$. Esta proviene de la líbrería $QuickCheck$, proporciona una generación aleatoria y proporciona valores reducidos. Gracias a esta clase, con la segunda instancia podemos generar ideales de forma aleatoria. Esto nos ayudará a comprobar las funciones a verificar para ser un ideal.\\

Vamos a explicar brevemente como funciona la segunda instancia. Comienza generando una lista $xs'$ de elementos cualesquiera del anillo, con $filter$ se filtra y se eliminan los ceros obteniendo la nueva lista $xs$. Si $\,xs\, = \,[]$, se genera el ideal $(Id\, [one])$, todo el anillo; en caso contrario, el ideal generado por los elementos de $xs$, sin repeticiones (eliminadas con la función $nub$).\\

Finalmente hemos implementado uno de los ideales canónicos, el ideal cero, $<0>$. A continuación, damos la definición de ideal principal.\\

\begin{defi}
Un ideal $I \subset R$ se llama principal si se puede generar por un sólo elemento. Es decir, si $I = <a>$, para un cierto $a \in\,\,R$.
\end{defi}
\\
Los anillos como $\mathbb{Z}$ en los cuales todos los ideales son principales se llaman clásicamente 
dominios de ideales principales. Pero constructivamente esta definición no es adecuada. Sin embargo, nosotros solo queremos considerar anillos en los cuales todos los ideales finitamente generados son principales. Al ser representados por un conjunto finito, podemos implementarlo a nivel computacional. Estos anillos se llaman dominios de Bézout y se considerarán en el siguiente capítulo. Siempre que se pueda añadiremos ejemplos sobre los enteros, haciendo uso de la instancia sobre los enteros especificada en los anteriores módulos.
\index{\texttt{isPrincipal}}
\begin{code}
isPrincipal :: CommutRing a => Ideal a -> Bool
isPrincipal (Id xs) = length xs == 1

--Ejemplos:
--λ> isPrincipal (Id [2,3])
--False
--λ> isPrincipal (Id [4])
--True
\end{code}

Mediante la función $from\,\,Id$, definida a continuación, mostramos la lista de los generadores de $(Id\,\,xs)$. 
\index{\texttt{fromId}}
\begin{code}
fromId :: CommutRing a => Ideal a -> [a]
fromId (Id xs) = xs

--Ejemplos:
--λ> fromId (Id [3,4])
--[3,4]
--λ> fromId (Id [4,5,8,9,2])
--[4,5,8,9,2]
\end{code}

Ahora veamos algunas operaciones sobre ideales y propiedades fundamentales de ideales, como pueden ser la suma y multiplicación. Por último daremos una función para identificar si dos ideales son el mismo ideal. Para realizar la implementación de estas operaciones, lo haremos solo para ideales finitamente generados.\\

\begin{defi}
Si $I$ y $J$ son ideales de un anillo $(R,+,*)$, se llama suma de ideales al conjunto $I\,\, +\,\, J = \{a+b\,\, |\,\, a\,\, \in\,\, I, b\in\,\, J\}$.La suma de ideales también es un ideal.
\end{defi}

Está definición es para cualquier ideal, nosotros nos centramos en los ideales finitamente generados. La suma de ideales finitamente generados es también un ideal finitamente generado y esta puede obtenerse a partir de los generadores de ambos ideales, es decir, $I\,+\,J\,\,=\,<I\,\cup\,J>.
\index{\texttt{addId}}

\begin{code}
addId :: (CommutRing a, Eq a) => Ideal a -> Ideal a -> Ideal a
addId (Id xs) (Id ys) = Id (nub (xs ++ ys))

--Ejemplos:
--λ> addId (Id [2,3]) (Id [4,5])
-- <2,3,4,5>
--λ> addId (Id [2,3,4]) (Id [3,4,6,7])
-- <2,3,4,6,7>
\end{code}

\begin{defi}
Si $I$ y $J$ son ideales de un anillo $(R,+,*)$, se llama producto al conjunto $I\,$·$ \,J = \{a\,$·$ \,b | a \in\, I, b\in\, J\}$. El producto de ideales también es un ideal.
\end{defi}

De igual forma que en la suma, está es la definición general para cualquier ideal. Centrándonos en los ideales finitamente generados, el producto de ideales finitamente generados es también un ideal finitamente generado y este se obtiene de igual forma que para cualquier ideal, solo que el producto es entre ideales finitamente generados.
\index{\texttt{mulId}}

\begin{code}
-- | Multiplicación de ideales.
mulId :: (CommutRing a, Eq a) => Ideal a -> Ideal a -> Ideal a
mulId (Id xs) (Id ys) = if zs == [] then zeroIdeal else Id zs
  where zs = nub [ f <**> g | f <- xs, g <- ys, f <**> g /= zero ]

--Ejemplos:
--λ> mulId (Id [2,3]) (Id [4,5])
-- <8,10,12,15>
--λ> mulId (Id [2,3,4]) (Id [3,4,6,7])
-- <6,8,12,14,9,18,21,16,24,28> 
\end{code}
 
A continuación veremos una función cuyo objetivo es comprobar que el resultado de una operación $op$ sobre dos ideales calcula el ideal correcto. Para ello, la operación debería proporcionar un “testigo” de forma que el ideal calculado tenga los mismos elementos. Es decir, si $z_k$ es un elemento del conjunto de generadores de $(Id\, zs)$, $z_k$ tiene una expresión como combinación lineal de $xs$ e $ys$, cuyos coeficientes vienen dados por $as$ y $bs$, respectivamente. 
\index{\texttt{isSameIdeal}}

\begin{code}
-- | Verificar si es correcta la operación entre ideales.

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

Explicamos con más detalle como funciona $isSameIdeal$. Recibe como argumento una operación $op$ que representa una operación entre los dos ideales que recibe. Es decir, la función $op$ debería devolver una terna $(Id\, zs, as, bs)$, donde $as$ y $bs$ son listas de listas de coeficientes (justamente, los coeficientes de cada generador de $zs$ en función de $xs$ y de $ys$,respectivamente). La función $isSameIdeal$ devuelve un booleano, si devuelve $True$ nos indica que la operación que se ha realizado entre ambos ideales es correcta. Cada elemento de $zs$ se puede expresar como combinación lineal de $xs$ con los coeficientes proporcionados por el correspondiente elemento de $as$ (análogamente, como combinación lineal de $ys$ con los coeficientes proporcionados por $bs$).

Para finalizar esta sección, implementamos la función zeroIdealWitnesses proporciona la función “testigo” para una operación sobre ideales cuyo resultado sea el ideal cero.

\begin{code}
zeroIdealWitnesses :: (CommutRing a) => [a] -> [a] -> (Ideal a, [[a]], [[a]])
zeroIdealWitnesses xs ys = ( zeroIdeal
                           , [replicate (length xs) zero]
                           , [replicate (length ys) zero])

--Ejemplo:
--λ> zeroIdealWitnesses [2,3] [4,5]
--(<0>,[[0,0]],[[0,0]])

\end{code}
