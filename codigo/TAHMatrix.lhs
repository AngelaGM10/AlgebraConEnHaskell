\begin{code}
module TAHMatrix
  ( Matrix(M), matrix
  , matrixToVector, vectorToMatrix, unMVec, unM, (!!!)
  , identity, propLeftIdentity, propRightIdentity
  , mulM, addM, transpose, isSquareMatrix, dimension
  , scale, swap, pivot
  , addRow, subRow, addCol, subCol
  , findPivot, forwardElim, gaussElim, gaussElimCorrect
  ) where

import qualified Data.List as L


import Control.Monad (liftM)
import Control.Arrow hiding ((<+>))
import Test.QuickCheck

import TAHField
import TAHVector

\end{code}
Antes de comenzar, hemos importado algunas librerías necesarias para construir las matrices. Entre ellas utilizaremos $Control.Arrow$, de ella tenemos que excluir la suma $(<+>)$ pues nosotros utilizamos la definida en anillos.

Declaramos el nuevo tipo de matrices, la representación de la matriz viene dada en forma de lista de vectores, donde cada vector de la lista representa una fila de la matriz. Daremos también una instancia para que se puedan mostrar. Así como un generador de matrices aleatorio, similar al utilizado en vectores, con el fin de poder comprobar resultados mediante $QuickCheck$.

\begin{code}
newtype Matrix r = M [Vector r]
  deriving (Eq) 

instance Show r => Show (Matrix r) where
  show xs = case unlines (map show (unMVec xs)) of
    [] -> "[]" 
    xs -> init xs ++ "\n"

-- Generar matrices con a lo sumo 10 filas.
instance Arbitrary r => Arbitrary (Matrix r) where
  arbitrary = do n <- choose (1,10) :: Gen Int
                 m <- choose (1,10) :: Gen Int
                 xs <- sequence [ liftM Vec (gen n) | _ <- [1..m]]
                 return (M xs)
    where
    gen 0 = return []
    gen n = do x <- arbitrary
               xs <- gen (n-1)
               return (x:xs)
\end{code}


Una vez implementado el tipo de las matrices vamos a definir la función para construir una matriz de dimensión $mxn$ a partir de una lista de listas, de forma que cada lista es una fila de la matriz (todas de la misma longitud) y la longitud de una lista es el número de columnas. Vamos a dar una función para que devuelva la matriz de la forma en que visualmente la vemos, es decir una fila debajo de la otra.
\index{\texttt{matrix}}
\begin{code}
-- | Matriz mxn.
matrix :: [[r]] -> Matrix r
matrix xs = 
  let m = fromIntegral $ length xs
      n = fromIntegral $ length (head xs)
  in if length (filter (\x -> fromIntegral (length x) == n) xs) == length xs 
        then M (map Vec xs)
        else error "La dimensión del vector no puede ser distinta al resto"
\end{code}

Las siguientes funciones son para mostrar una matriz como lista de vectores, y aplicar funciones con este formato sobre ella. Pasar de matrices a vectores y viceversa, así como una función para obtener el elemento en la posición $(i,j)$.
\index{\texttt{unM}}
\index{\texttt{unMVec}}
\index{\texttt{vectorToMatrix }}
\index{\texttt{matrixToVector}}
\index{\texttt{Posición (i+1,j+1)}}
\begin{code}
-- | Mostrar la matriz como lista de vectores.
unM :: Matrix r -> [Vector r]
unM (M xs) = xs

-- Ejemplo:
-- λ> unM (M [Vec [2,3], Vec [3,4]])
--    [[2,3],[3,4]]
-- | Aplicamos la función 'unM' a cada vector de la lista.
unMVec :: Matrix r -> [[r]]
unMVec = map unVec . unM
-- Ejemplo:
-- λ> unMVec (M [Vec [2,3], Vec [3,4]])
--    [[2,3],[3,4]]

-- | De vector a matriz.
vectorToMatrix :: Vector r -> Matrix r
vectorToMatrix = matrix . (:[]) . unVec

-- Ejemplo:
-- λ> vectorToMatrix (Vec [2,3,4]) 
--    [2,3,4]

-- | De matriz a vector.
matrixToVector :: Matrix r -> Vector r
matrixToVector m | fst (dimension m) == 1 = head (unM m)
                 | otherwise = error "No pueden tener dimensiones distintas"
-- Ejemplos:
-- λ> matrixToVector (M [Vec [2,3], Vec [4,5]])
--    *** Exception: No pueden tener dimensiones distintas
-- λ> matrixToVector (M [Vec [2,3]])
--    [2,3]

-- | Obtener el elemento de la posición (i+1,j+1).
(!!!) :: Matrix a -> (Int,Int) -> a
m !!! (i,j) | i >= 0 && i < rows && j >= 0 && j < cols = unMVec m !! i !! j
            | otherwise = error "!!!: Fuera de los límetes"
  where
  (rows,cols) = dimension m

-- Ejemplos:
-- λ> (M [Vec [2,3,4], Vec [4,5,6], Vec [7,8,9]]) !!! (2,3)
--    *** Exception: !!!: Fuera de los límetes
-- λ> (M [Vec [2,3,4], Vec [4,5,6], Vec [7,8,9]]) !!! (1,2)
--    6
-- λ> (M [Vec [2,3,4], Vec [4,5,6], Vec [7,8,9]]) !!! (0,1)
--    3
\end{code}

Utilizando las funciones anteriores podemos implementar propiedades y operaciones con las matrices. Daremos la dimensión de la matriz, una función que compruebe si la matriz es cuadrada, es decir, que el número de filas coincide con el número de columnas. Y la función para transponer una matriz, es decir, pasar las filas a columnas. Para esta última, utilizaremos la función $transpose$ de la librería $Data.List$ que se aplica sobre listas de forma que agrupa los elementos para que las listas que son filas estén en la posición de la columna correspondiente.
\index{\texttt{dimension}}
\index{\texttt{isSquareMatrix}}
\index{\texttt{transpose}}
\begin{code}
-- | Dimensión de la matriz.
dimension :: Matrix r -> (Int, Int)
dimension (M xs) | null xs   = (0,0)
                 | otherwise = (length xs, length (unVec (head xs)))
-- Ejemplo:
-- λ> dimension (M [Vec [2,3,4], Vec [4,5,6], Vec [7,8,9]])
--    (3,3)

-- | Comprobar si una matriz es cuadrada.
isSquareMatrix :: Matrix r -> Bool
isSquareMatrix (M xs) = all (== l) (map lengthVec xs)
                        where l = length xs
-- Ejemplo:
-- λ> isSquareMatrix (M [Vec [2,3,4], Vec [4,5,6], Vec [7,8,9]])
--    True
-- λ> isSquareMatrix (M [Vec [2,3,4], Vec [4,5,6]])
--    False

-- | Transponer la matriz.
transpose :: Matrix r -> Matrix r
transpose (M xs) = matrix (L.transpose (map unVec xs))

-- Ejemplo:
-- λ> transpose (M [Vec [2,3,4], Vec [4,5,6]])
--    [2,4]
--    [3,5]
--    [4,6]
\end{code}
 
Recordamos que la suma de matrices da una matriz cuyas entradas son la suma de las entradas correspondientes de las matrices a sumar. Para esta suma lo haremos mediante suma de listas ya que utilizaremos la función $\,matrix\,$ para mostrar la matriz correspondiente y esta recibe como argumento de entrada una lista de listas.\\

Por otro lado la multiplicación de matrices recordamos que consiste en multiplicar cada fila de la primera matriz por cada columna de la segunda matriz, obteniendo así un elemento en la entrada correspondiente a la fila y columna. Aquí si podemos utilizar la operación $\,mulVec\,$ entre vectores pues devuelve un valor que no es un vector, por tanto obtenemos una lista de vectores. Recordamos que para poder realizar multiplicaciones entre matrices el número de columnas de la primera matriz tiene que ser igual al número de filas de la segunda matriz.
\index{\texttt{addM}}
\index{\texttt{mulM}}
\begin{code}
-- | Suma de matrices.
addM :: Ring r => Matrix r -> Matrix r -> Matrix r
addM (M xs) (M ys)
  | dimension (M xs) == dimension (M ys) = m
  | otherwise = error "Las dimensiones de las matrices son distintas"
  where
    m = matrix (zipWith (zipWith (<+>)) (map unVec xs) (map unVec ys))

-- Ejemplo:
-- λ> addM (M [Vec [2,3,4], Vec [4,5,6]]) (M [Vec [1,0,2], Vec [1,2,3]])
--    [3,3,6]
--    [5,7,9]
-- λ> addM (M [Vec [2,3,4], Vec [4,5,6]]) (M [Vec [1,0,2]])
--    *** Exception: Las dimensiones de las matrices son distintas

-- | Multiplicación de matrices.
mulM :: Ring r => Matrix r -> Matrix r -> Matrix r
mulM (M xs) (M ys)
  | snd (dimension (M xs)) == fst (dimension (M ys)) = m
  | otherwise = error "La dimensión de colunmas y filas es distinta"
    where
    m = matrix [ [mulVec x y | y <- unM (transpose (M ys)) ]
               | x <- unM (M xs) ]

-- Ejemplo:
-- λ>  mulM (M [Vec [2,3], Vec [4,5]]) (M [Vec [1,0,2], Vec [1,2,3]])
--     [5,6,13]
--     [9,10,23]
-- λ> mulM (M [Vec [2,3,4], Vec [4,5,6]]) (M [Vec [1,0,2], Vec [1,2,3]])
--    *** Exception: La dimensión de colunmas y filas es distinta

\end{code}

Del mismo modo que para vectores, para matrices volveremos a utilizar la clase de tipos $Functor$ para establecer matrices en forma de listas.
\begin{code}
instance Functor Matrix where
  fmap f = M . map (fmap f) . unM
\end{code}

Veamos un ejemplo sobre los números enteros de $(fmap\,\,f)$, sumar 2 a una matriz:
\begin{code}
-- λ> fmap (<+> 2) (M [Vec [2,3], Vec [4,5]])
--    [4,5]
--    [6,7]
\end{code}
Introducimos las propiedades básicas de la matriz identidad. Estas estarán restringidas a la clase de dominio de integridad, $IntegralDomain$.
\index{\texttt{identity}}
\index{\texttt{propLeftIdentity}}
\index{\texttt{propRightIdentity}}
\begin{code}
-- | Construcción de la matriz identidad nxn.
identity :: IntegralDomain r => Int -> Matrix r
identity n = matrix (xs 0)
  where
  xs x | x == n    = []
       | otherwise = (replicate x zero ++ [one] ++
                      replicate (n-x-1) zero) : xs (x+1)

-- Ejemplo:
-- λ> identity 3
--    [1,0,0]
--    [0,1,0]
--    [0,0,1]

-- Propiedades de la multiplicación a izquierda y derecha de la
-- matriz identidad.
propLeftIdentity :: (IntegralDomain r, Eq r) => Matrix r -> Bool
propLeftIdentity a = a == identity n `mulM` a
  where n = fst (dimension a)

propRightIdentity :: (IntegralDomain r, Eq r) => Matrix r -> Bool
propRightIdentity a = a == a `mulM` identity m
  where m = snd (dimension a)
\end{code}

A continuación  vamos a trabajar con matrices sobre anillos conmutativos, al igual que hicimos con los vectores. Realizaremos operaciones entre filas y columnas, y veremos que estas operaciones no afectan a la dimensión de la matriz. Hacemos esta restricción debido a en el siguiente capítulo necesitaremos estas operaciones con matrices y estaremos restringidos a anillos conmutativos. \\

 Damos una breve descripción de la primera operación. El objetivo es multiplicar una fila por un escalar, de forma que la matriz obtenida tenga la fila que queramos modificar como el resultado de multiplicar esta fila por un número o escalar, quedando el resto de filas sin modificar. Los argumentos de entrada serán la matriz, el número de la fila que queremos modificar menos 1 (pues la función $(!!\,\,r)$ de la librería Data.List selecciona el elemento $r+1$ de la lista, pues es un índice y comienza en 0). Comprobaremos que esta operación no afecta a la dimensión, pues la dimensión de la matriz resultante es la misma que la primera matriz.
\index{\texttt{scaleMatrix}}
\index{\texttt{propScaleDimension}}
\begin{code}
-- | Multiplicar una fila por un escalar en la matriz.
scaleMatrix :: CommutRing a => Matrix a -> Int -> a -> Matrix a
scaleMatrix m r s
  | 0 <= r && r < rows = matrix $ take r m' ++
                         map (s <**>) (m' !! r) : drop (r+1) m'
  | otherwise = error "La fila escogida es mayor que la dimensión"
  where
  (rows,_) = dimension m
  m'       = unMVec m

-- Ejemplo:
-- λ> scaleMatrix (M [Vec [2,3], Vec [4,5]]) 1 5
--    [2,3]
--    [20,25]

-- La dimensión no varía.
propScaleDimension :: (Arbitrary r, CommutRing r) =>
                       Matrix r -> Int -> r -> Bool
propScaleDimension m r s = d == dimension (scaleMatrix m (mod r rows) s)
  where d@(rows,_) = dimension m
\end{code}

La siguiente operación consiste en intercambiar filas, el objetivo de $(swap \,\,m\,\,i\,\,j)$ es dada una matriz $m$ intercambiar las filas $i$ y $j$, de forma que la fila $i$ acabe en la posición de la fila $j$ y viceversa. Comprobamos que no varía de dimensión. Comprobaremos también que si realizamos el mismo intercambio dos veces obtenemos la matriz inicial.
\index{\texttt{swap}}
\index{\texttt{propSwapDimension}}
\index{\texttt{propSwapIdentity}}
\begin{code}
-- | Intercambiar dos filas de una matriz.
swap :: Matrix a -> Int -> Int -> Matrix a
swap m i j
  | 0 <= i && i <= r && 0 <= j && j <= r = matrix $ swap' m' i j
  | otherwise = error "Intercambio: índice fuera de los límites"
  where
  (r,_) = dimension m
  m'    = unMVec m

  swap' xs 0 0     = xs
  swap' (x:xs) 0 j = (x:xs) !! j : take (j-1) xs ++ x : drop j xs
  swap' xs i 0     = swap' xs 0 i
  swap' (x:xs) i j = x : swap' xs (i-1) (j-1)

-- Ejemplo:
-- λ> swap (M [Vec [2,3], Vec [4,5], Vec [6,7]]) 0 1
--    [4,5]
--    [2,3]
--    [6,7]

-- Al intercambiar filas de una matriz no varía la dimensión.
propSwapDimension :: Matrix () -> Int -> Int -> Bool
propSwapDimension m i j = d == dimension (swap m (mod i r) (mod j r))
  where d@(r,_) = dimension m

-- | Al realizar dos veces un mismo intercambio volvemos a la matriz
--   de inicio.
propSwapIdentity :: Matrix () -> Int -> Int -> Bool
propSwapIdentity m i j = m == swap (swap m i' j') i' j'
  where
  d@(r,_) = dimension m
  i'      = mod i r
  j'      = mod j r
\end{code}

Mediante la función $(addRow\,\, m\,\, row@(Vec xs)\,\, x)$ realizamos la operación de sumar un vector ($row@(Vec xs)$)  a la fila $x+1$ de una matriz $m$ dada. Recordamos que es importante que el vector tenga la misma dimensión que el número de colunmas de la matriz. Verificamos que la dimensión no varía. Seguidamente realizamos la misma operación sobre las columnas. Para ello basta transponer la matriz y aplicar la función sobre las filas.
\index{\texttt{addRow}}
\index{\texttt{propAddRowDimension}}
\index{\texttt{addCol}}
\index{\texttt{subRow}}
\index{\texttt{subCol}}
\begin{code}
-- | Sumar un vector a una fila de la matriz .
addRow :: CommutRing a => Matrix a -> Vector a -> Int -> Matrix a
addRow m row@(Vec xs) x
  | 0 <= x && x < r =
    matrix $ take x m' ++ zipWith (<+>) (m' !! x) xs : drop (x+1) m'
  | c /= lengthVec row =
    error "SumaFila: La longitud de la fila es distinta."
  | otherwise =
    error "SumaFila: Error al seleccionar la fila."

    where
    (r,c) = dimension m
    m'    = unMVec m

-- Ejemplo:
-- λ> addRow (M [Vec [2,3], Vec [4,5], Vec [6,7]]) (Vec [10,15]) 1
--    [2,3]
--    [14,20]
--    [6,7]

-- La operación no afectan a la dimensión.
propAddRowDimension :: (CommutRing a, Arbitrary a)
                    => Matrix a -> Vector a -> Int -> Property
propAddRowDimension m row@(Vec xs) r =
  length xs == c ==> d == dimension (addRow m row (mod r r'))
  where d@(r',c) = dimension m

-- | Sumar un vector columna a una columna de la matriz.
addCol :: CommutRing a => Matrix a -> Vector a -> Int -> Matrix a
addCol m c x = transpose $ addRow (transpose m) c x

-- Ejemplo:
-- λ> addCol (M [Vec [2,3], Vec [4,5], Vec [6,7]]) (Vec [10,15,10]) 1
--    [2,13]
--    [4,20]
--    [6,17]
\end{code}

Finalmente, realizaremos la operación anterior  de sumar un vector a una fila o columna pero esta vez restando un vector, es decir, la matriz resultante mantiene todas las filas menos la fila seleccionada, a la cuál se le resta un vector dado. 
\begin{code}
-- Restar un vector fila o columna a una fila o colunma, respectivamente,
-- de una matriz.
subRow, subCol :: CommutRing a => Matrix a -> Vector a -> Int -> Matrix a
subRow m (Vec xs) x = addRow m (Vec (map neg xs)) x
subCol m (Vec xs) x = addCol m (Vec (map neg xs)) x

-- Ejemplo:
-- λ> subRow (M [Vec [2,3], Vec [4,5], Vec [6,7]]) (Vec [10,15,10]) 1
--    [2,3]
--    [-6,-10]
--    [6,7]
-- λ> subCol (M [Vec [2,3], Vec [4,5], Vec [6,7]]) (Vec [10,15,10]) 1
--    [2,-7]
--    [4,-10]
--    [6,-3]

\end{code}

Gracias a todo lo anterior ahora podemos implementar el método de Gauss-Jordan para poder resolver sistemas $A\vec{x}=\vec{b}$ donde $A$ es una matriz $mxn$ y $\vec{b}$ es un vector columna de $n$ filas.\\

Comenzaremos por obtener los pivotes en cada fila, escalonar la matriz y finalmente hacer el paso de Jordan para finalmente conseguir la solución del sistema. El paso de Jordan consiste en hacer ceros por encima de la diagonal de la matriz cuando previamente se ha obtenido ceros debajo de la diagonal de la matriz, esta primera parte se conoce como aplicar Gauss o aplicar el método de Gauss o escalonar una matriz.\\

Para empezar damos las funciones para obtener un 0 en las posiciones de debajo del pivote y la segunda función consiste en localizar el siguiente pivote, comenzando la búsqueda desde una entrada fijada de la matriz. Por ejemplo, dada una matriz $3x3$ $findPivot\,\,m\,\,(0,1)$, nos devolverá el primer cero que aparezca en la columna 2 comenzando desde la fila 2, es decir, mirará las posiciones (2,2) y (2,3). Recordemos que en el algoritmo el índice empieza en 0, por lo que miraría las posiciones (1,1) y (1,2).
\index{\texttt{pivot}}
\index{\texttt{findPivot}}
\begin{code}
-- | Multiplicar por el escalar s la fila  donde está
-- el pivote y sumarle la fila en la que queremos hacer un 0.
-- El escalar se elige de forma que al sumar la fila consigamos un 0
-- en la posición del pivote.
pivot :: CommutRing a => Matrix a -> a -> Int -> Int -> Matrix a
pivot m s p t = addRow m (fmap (s <**>) (unM m !! p)) t

-- Ejemplo:
-- λ> pivot (M [Vec [2,3,4], Vec [4,5,6], Vec [4,8,9]]) (-2) 0 1
--    [2,3,4]
--    [0,-1,-2]
--    [4,8,9]

-- | Encontrar el primer cero que aparezca la columna c empezando
--   desde la fila r y devolve el valor del pivote y el número de
--   la fila en la que está.
findPivot :: (CommutRing a, Eq a) => Matrix a -> (Int,Int) -> Maybe (a,Int)
findPivot m (r,c) = safeHead $ filter ((/= zero) . fst) $ drop (r+1) $
                    zip (head $ drop c $ unMVec $ transpose m) [0..]
  where
  m' = unMVec m

  safeHead []     = Nothing
  safeHead (x:xs) = Just x

-- Ejemplos:
-- λ> findPivot (M [Vec [1,3,4], Vec [0,5,6], Vec [0,8,9]]) (0,0)
--    Nothing
-- Devuelve Nothing porque en la primera columna y la primera fila no hay 0
-- λ> findPivot (M [Vec [1,3,4], Vec [0,5,6], Vec [0,8,9]]) (0,1)
--    Just (5,1)
-- Devuelve (5,1) porque 5 es el primer valor distinto de cero comenzando
-- desde la fila 1  (sin contar la propia fila 1) hacia abajo siguiendo
-- la columna 2.
-- λ> findPivot (M [Vec [1,3,4], Vec [0,0,6], Vec [0,8,9]]) (0,1)
--    Just (8,2)
-- Al colocar un 0 en la posición donde antes teníamos un 5 vemos como ahora
-- nos devuelve el primer valor distinto de cero que aparezca en la columna
-- 2 empezando desde la fila 1 (sin contar la propia fila 1)
\end{code}

Con la siguiente función buscamos escalonar la matriz de forma que todo lo que quede debajo de la diagonal sean ceros. Para ello necesitamos que sea un cuerpo pues necesitamos que exista inverso, ya que el valor del escalar al multiplicarse por la fila en la posición del pivote se corresponde con el inverso del pivote para que al sumarlo obtengamos un cero.
\index{\texttt{fE}}
\begin{code}
-- | Escalonar la matriz.
fE :: (Field a, Eq a) => Matrix a -> Matrix a
fE (M [])         = M []
fE (M (Vec []:_)) = M []
fE m     = case L.findIndices (/= zero) (map head xs) of
  (i:is) -> case fE (cancelOut
     m [ (i,map head xs !! i) | i <- is ] (i,map head xs !! i)) of
    ys -> matrix (xs !! i : map (zero :) (unMVec ys))
  []     -> case fE (matrix (map tail xs)) of
    ys -> matrix (map (zero:) (unMVec ys))
  where
  cancelOut :: (Field a, Eq a) => Matrix a -> [(Int,a)] -> (Int,a) -> Matrix a
  cancelOut m [] (i,_)    = let xs = unMVec m in matrix $
                                     map tail (L.delete (xs !! i) xs)
  cancelOut m ((t,x):xs) (i,p) =
                  cancelOut (pivot m (neg (x </> p)) i t) xs (i,p)
  -- Con cancelOut hacemos cero en las posiciones de debajo del pivote.
  xs = unMVec m

--Ejemplos:
--λ>  fE (M [Vec [2,3,4], Vec [4,5,6], Vec [7,8,9]])
--[2.0,3.0,4.0]
--[0.0,6.5,8.0]
--[0.0,0.0,16.013824884792626]

--λ> fE (M [Vec [1,3,4], Vec [0,0,6], Vec [0,8,9]])
--[1.0,3.0,4.0]
--[0.0,8.0,9.0]
--[0.0,0.0,6.0]

--λ> fE (M [Vec [1,0,2], Vec [2,-1,3], Vec [4,1,8]])
--[1.0,0.0,2.0]
--[0.0,-1.0,4.0]
--[0.0,0.0,4.5]
\end{code}

Para calcular la forma escalonada para resolver un sistema $\,A\vec{x} = \vec{b}\,$, seguimos necesitando que los elementos de las matrices pertenezca a un cuerpo. Primero aplicamos Gauss, es decir, obtenemos ceros por debajo de la diagonal. Aplicando las operaciones al vector $\vec{b}$ también. De esta forma se queda el sistema preparado para resolver de abajo a arriba cada incógnita. Además, con esta función dejamos los pivotes con unos, para facilitar la solución del sistema.
\index{\texttt{forwardElim}}
\begin{code}
-- | Calcular la forma escalonada de un sistema Ax = b.
forwardElim :: (Field a, Eq a) => (Matrix a,Vector a) -> (Matrix a,Vector a)
forwardElim (m,v) = fE m' (0,0)
  where
  -- fE toma como argumento de entrada la matriz a escalonar y
  --la posición del pivote.
  fE :: (Field a, Eq a) => Matrix a -> (Int,Int) -> (Matrix a,Vector a)
  fE (M []) _  = error "forwardElim: La matriz dada es vacía."
  fE m rc@(r,c)
      -- Si estamos en la última fila o columna de la matriz
    | c == mc || r == mr =
      -- Descompone la matriz en A y b de nuevo.
      (matrix *** Vec) $ unzip $ map (init &&& last) $ unMVec m

      -- Si hay un cero en la posición (r,c) entonces intercambiamos la
      -- fila por la primera fila con elemento no nulo en la columna
      -- del pivote.
    | m !!! rc == zero   = case findPivot m rc of
      Just (_,r') -> fE (swap m r r') rc
      
      -- Si todos los elementos de la columna pivote son cero entonces nos
      -- movemos a la siguiente columna por la derecha.
      Nothing     -> fE m (r,c+1)

    | m !!! rc /= one    =
      -- Convertir el pivot en 1.
      fE (scaleMatrix m r (inv (m !!! rc))) rc

    | otherwise          = case findPivot m rc of
      -- Hacer 0 el primer elemento distinto de cero en la fila pivote.
      Just (v,r') -> fE (pivot m (neg v) r r') (r,c)
      -- Si todos los elementos en la columna pivote son 0 entonces nos
      -- vemos a la fila de abajo y hacia la columna de la derecha.
      Nothing     -> fE m (r+1,c+1)

  (mr,mc) = dimension m

  -- Forma la matriz A añadiendole la columna b.
  m' = matrix $ [ r ++ [x] | (r,x) <- zip (unMVec m) (unVec v) ]

--Ejemplos:
--λ> forwardElim (M [Vec [1,3,4], Vec [0,0,6], Vec [0,8,9]],Vec [4,5,6])
-- ([1.0,3.0,4.0]
-- [0.0,1.0,1.125]
-- [0.0,0.0,1.0]
-- ,[4.0,0.75,0.8333333333333333])


\end{code}

En segundo lugar aplicamos el paso de Jordan que consiste en obtener ceros por encima de la diagonal. Para aplicar el método de Gauss-Jordan es necesario aplicar antes el paso de Gauss y después el de Jordan.
\index{\texttt{jordan}}
\begin{code}
-- | Realizar el paso "Jordan" en la eliminación de Gauss-Jordan. Esto
--   es hacer que cada elemento encima de la diagonal sea cero.

jordan :: (Field a, Eq a) => (Matrix a, Vector a) -> (Matrix a, Vector a)
jordan (m, Vec ys) = case L.unzip (jordan' (zip (unMVec m) ys) (r-1)) of
  (a,b) -> (matrix a, Vec b)
  where
  (r,_) = dimension m

  jordan' [] _ = []
  jordan' xs c =
    jordan' [ (take c x ++ zero : drop (c+1) x,
            v <-> x !! c <**> snd (last xs))
            | (x,v) <- init xs ] (c-1) ++ [last xs]
--Ejemplos:
--λ> jordan (M [Vec [1,3,4], Vec [0,1,1.125], Vec [0,0,1]],Vec [4,0.75,0.84])
-- ([1.0,0.0,0.0]
-- [0.0,1.0,0.0]
-- [0.0,0.0,1.0]
-- ,[4.481964329257672,1.8082010582010584,0.84])
--
--λ> jordan (M [Vec [1,3,4], Vec [1,0,6], Vec [0,8,9]],Vec [4,5,6])
-- ([1.0,0.0,0.0]
-- [1.0,0.0,0.0]
-- [0.0,8.0,9.0]
-- ,[4.107965009208104,5.027777777777778,6.0])


\end{code}

Finalmente, podemos realizar el método de Gauss-Jordan, con el objetivo de resolver un sistema de ecuaciones de la forma $A\vec{x}=\vec{b}$. Primero obtenemos la matriz con solo la diagonal que es la obtenida tras aplicar Gauss-Jordan esto lo obtenemos con la función que denotaremos $gaussElim$. \\

La última función que denotaremos $gaussElimCorrect$, recibe la partición de la matriz $A$ y el vector columna $\vec{b}$. Con ella comprobamos dos cosas. La primera que la dimensión de las filas de la matriz $A$ coincida con la dimensión del vector $\vec{b}$ y que $A$ sea una matriz cuadrada. Una vez se cumple esto lo siguiente que comprueba es que el vector que se obtiene de $gaussElim$ al multiplicarlo por la matriz $A$ coincide con el vector $\vec{b}$.
\index{\texttt{gaussElim}}
\index{\texttt{gaussElimCorrect}}
\begin{code}
-- | Eliminación por Gauss-Jordan: Dados A y b resuelve Ax=b.
gaussElim :: (Field a, Eq a, Show a) =>
             (Matrix a, Vector a) -> (Matrix a, Vector a)
gaussElim = jordan . forwardElim

gaussElimCorrect :: (Field a, Eq a, Arbitrary a, Show a) =>
                    (Matrix a, Vector a) -> Property
gaussElimCorrect m@(a,b) =
  fst (dimension a) == lengthVec b && isSquareMatrix a ==>
  matrixToVector (transpose
  (a `mulM` transpose (M [snd (gaussElim m)]))) == b
\end{code}
