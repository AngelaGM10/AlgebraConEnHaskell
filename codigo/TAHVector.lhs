
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
Para comenzar este módulo, necesitaremos hacer uso de librerías de Haskell como \texttt{Control.Monad} para utilizar ciertas funciones que nos ayuden a construir nuestros vectores. Daremos más detalle cuando la utilicemos.

Comenzamos por implementar las nociones básicas de los vectores. Creamos un nuevo tipo para definir un vector, usaremos las listas para trabajr con los vectores en Haskell. Daremos también una función para generar vectores de forma aleatoria, para poder comprobar resultados mediante \texttt{QuickCheck}.

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

Explicamos brevemente algunas de las funciones utilizadas en el generador de vectores. Con \texttt{choose} se elige de forma aleatoria un número (en nuestro caso, entre 1 y 10) para establecer la longitud del vector. Con \texttt{gen} generamos elementos aleatorios del tipo \texttt{Int} y la lista obtenida la transformamos en tipo \texttt{Vector} con la función \texttt{liftM}.\\

Damos la función que muestra el vector en forma de lista y la que mide la longitud de un vector en ese formato. Acompañamos de ejemplos para mostrar los resultados que se obtienen.
\index{\texttt{unVec}}
\index{\texttt{lengthVec}}
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

Para trabajar con vectores, haremos uso de la clase de tipos \texttt{Functor} de Haskell. Esta clase de tipos está implementada de la siguiente forma:
\begin{code}
-- class Functor f where
--     fmap :: (a -> b) -> f a -> f b
\end{code}

Define una función, \texttt{fmap}, y no proporciona ninguna implementación por defecto. El tipo de \texttt{fmap} es similar al tipo de \texttt{map}. Aquí, \texttt{f} no es un tipo concreto, sino un constructor de tipos que toma un tipo como parámetro. Vemos que \texttt{fmap} toma una función de un tipo a otro, un funtor aplicado a un tipo y devuelve otro funtor aplicado con el otro tipo.\\

En nuestro caso crearemos una instancia con la clase de tipos \texttt{Functor} sobre el constructor \texttt{Vector} con el objetivo de aplicar una función \texttt{f} sobre un vector. Definiremos la función \texttt{(fmap f)} de forma que devuelva un vector con la función \texttt{f} aplicada a cada componente del vector.

\begin{code}
instance Functor Vector where 
  fmap f = Vec . map f . unVec
\end{code}

Veamos las operaciones de suma y multiplicación de vectores sobre anillos, para ello restringimos a los anillos conmutativos de forma general. La multiplicación de vectores es el producto escalar de ambos. Añadimos unos ejemplos sobre los números enteros.
\index{\texttt{sumVec}}
\index{\texttt{mulVec}}
\begin{code}
sumVec:: Ring a => Vector a -> Vector a -> Vector a
sumVec (Vec xs) (Vec ys)
  | length xs == length ys = Vec (zipWith (<+>) xs ys)
  | otherwise = error "Los vectores tienen dimensiones diferentes"

mulVec:: Ring a => Vector a -> Vector a -> a
mulVec (Vec xs) (Vec ys)
  | length xs == length ys = foldr (<+>) zero $ zipWith (<**>) xs ys
  | otherwise = error "Los vectores tienen dimensiones diferentes"

-- | Ejemplos:
--λ> sumVec (Vec [2,3]) (Vec [4,5])
--   [6,8]
--λ> mulVec (Vec [2,3]) (Vec [4,5])
--   23
\end{code}

