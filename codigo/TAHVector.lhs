
\begin{code}
module TAHVector
  ( Vector(Vec)
  , unVec, lengthVec
  , sumVec, mulVec
  ) where

import Control.Monad (liftM)

import Test.QuickCheck
import TAHField

\end{code}
Para comenzar este módulo, necesitaremos hacer uso de librerías de Haskell como $Control.Monad$ para utilizar ciertas funciones que nos ayuden a construir nuestros vectores, daremos más detalle cuando la utilicemos.

Comenzamos por implementar las nocines básicas de los vectores. Creamos un nuevo tipo para definir un vector, usaremos las listas para trabajr con los vectores en Haskell. Daremos también una función para generar vectores de forma aleatoria, para poder comprobar resultados mediante $QuickCheck$.
\begin{code}
-- | Vectores.

newtype Vector r = Vec [r] deriving (Eq)

instance Show r => Show (Vector r) where
  show (Vec vs) = show vs

-- Generar un vector de longitud 1-10.
instance Arbitrary r => Arbitrary (Vector r) where
  arbitrary = do n <- choose (1,10) :: Gen Int
                 liftM Vec $ gen n
    where
    gen 0 = return []
    gen n = do x <- arbitrary
               xs <- gen (n-1)
               return (x:xs)

\end{code}

Explicamos brevemente algunas de las funciones utilizadas en el generador de vectores, con $choose$ se elige de forma aleatoria un número, en nuestro caso, entre 1 y 10. La función $liftM$ nos permite transformar una función en una función correspondiente dentro de otra configuración en nuestro caso en forma de vector y junto con $gen$ que es una función que genera un tipo dado de forma aleatoria en nuestro caso un vector gracias a $liftM$. \\

Para trabajar con vectores, haremos uso de la clase de tipos $Functor$ de Haskell. Esta clase de tipos está implementada de la siguiente forma:
\begin{code}
-- class Functor f where
--     fmap :: (a -> b) -> f a -> f b
\end{code}

Define una función, $fmap$, y no proporciona ninguna implementación por defecto. El tipo de $fmap$ es similar al tipo de $map$. Aquí, $f$ no es un tipo concreto, sino un constructor de tipos que toma un tipo como parámetro. Vemos que $fmap$ toma una función de un tipo a otro, un funtor aplicado a un tipo y devuelve otro funtor aplicado con el otro tipo.\\

En nuestro caso crearemos una instancia con la clase de tipos $Functor$ sobre el constructor $Vector$ con el objetivo de establecer los vectores en forma de lista. Definiremos la función $(fmap\,\,f)$ como tipo vector mediante $Vec$ y aplicaremos $unVec$ (una función que definiremos más adelante) a la lista obtenida tras aplicar la función $(map\,\,f)$.

\begin{code}
instance Functor Vector where 
  fmap f = Vec . map f . unVec
\end{code}

Veamos las operaciones de suma y multiplicación de vectores sobre anillos, para ello restringimos a los anillos conmutativos de forma general. La multiplicación de vectores es el producto escalar de ambos. Añadimos unos ejemplos sobre los números enteros.
\begin{code}
sumVec:: Ring a => Vector a -> Vector a -> Vector a
sumVec (Vec xs) (Vec ys) | length xs == length ys = Vec (zipWith (<+>) xs ys)
             | otherwise = error "Los vectores tienen dimensiones diferentes"

mulVec:: Ring a => Vector a -> Vector a -> a
mulVec (Vec xs) (Vec ys) | length xs == length ys = foldr (<+>) zero $
                           zipWith (<**>) xs ys
             | otherwise = error "Los vectores tienen dimensiones diferentes"

-- | Ejemplos:
--λ> sumVec (Vec [2,3]) (Vec [4,5])
--   [6,8]
--λ> mulVec (Vec [2,3]) (Vec [4,5])
--   23
\end{code}


Para definir la suma y multiplicación de vectores sobre un anillo en concreto, estas operaciones no son sufientes, pues hay que añadir el resto de axiomas del anillo. Así como el elemento neutro para suma y producto, y la función inversa $neg$. Tenemos que dejarlas comentadas pues para que funcionen tenemos que asignar el elemento neutro para la suma y producto, pues estamos definiéndolo como una instancia de la clase $Ring$. Recordamos que para realizar operaciones con vectores estos tienen que tener la misma dimensión.
\begin{code}
{-
instance Ring r => Ring (Vector r) where
  (Vec xs) <+> (Vec ys) = sumVec (Vec xs) (Vec ys)
  (Vec xs) <**> (Vec ys) = mulVec (Vec xs) (Vec ys)
  one  = ?
  zero = ?
  neg = ?
-}
\end{code}

Para finalizar, damos la función que muestra el vector en forma de lista y la que mide la longitud de un vector en ese formato. Acompañamos de ejemplos para mostrar los resultados que se obtienen.

\begin{code}
unVec :: Vector r -> [r]
unVec (Vec vs) = vs

lengthVec :: Vector r -> Int
lengthVec = length . unVec

-- | Ejemplos:
--λ> unVec (Vec [2,3])
--   [2,3]
--λ> lengthVec (Vec [3,4,5])
--   3
\end{code}
