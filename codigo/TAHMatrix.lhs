Antes de comenzar, importaremos algunas librerías necesarias para construir las matrices. Entre ellas utilizaremos $'Control.Arrow'$, de ella tenemos que excluir la suma $(<+>)$ pues nosotros utilizamos la definida en anillos.

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

Del mismo modo que para vectores, para matrices volveremos a utilizar la clase de tipos $Functor$ para establecer matrices en forma de listas.
\begin{code}
instance Functor Matrix where
  fmap f = M . map (fmap f) . unM
\end{code}

Una vez implementado el tipo de las matrices vamos a definir la función para construir una matriz de dimensión $mxn$ a partir de una lista de listas, de forma que cada lista es una fila de la matriz (todas de la misma longitud) y la longitud de un lista es el número de columnas. Vamos a dar una función para que devuelva la matriz de la forma en que visualmente la vemos, es decir una fila debajo de la otra.
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

Las siguientes funciones son para mostrar una matriz como lista de vectores, y aplicar funciones con este formato sobre ella. Pasar de matrices a vectores y viceversa, así como una función para obtener una submatriz.
\begin{code}
-- | Mostrar la matriz como lista de vectores.
unM :: Matrix r -> [Vector r]
unM (M xs) = xs

-- | Aplicamos la función 'unM' a cada vector de la lista.
unMVec :: Matrix r -> [[r]]
unMVec = map unVec . unM

-- | De vector a matriz.
vectorToMatrix :: Vector r -> Matrix r
vectorToMatrix = matrix . (:[]) . unVec

-- | De matriz a vector.
matrixToVector :: Matrix r -> Vector r
matrixToVector m | fst (dimension m) == 1 = head (unM m)
                 | otherwise = error "No pueden tener dimensiones distintas"

-- | Obtener una submatriz.
(!!!) :: Matrix a -> (Int,Int) -> a
m !!! (r,c) | r >= 0 && r < rows && c >= 0 && c < cols = unMVec m !! r !! c
            | otherwise = error "!!!: Fuera de los límetes"
  where
  (rows,cols) = dimension m 
\end{code}

Utilizando las funciones anteriores podemos implementar propiedades y operaciones con las matrices. Daremos la dimensión de la matriz, una función que compruebe si la matriz es cuadrada, es decir, que el número de filas coincide con el número de columnas. Y la función para transponer una matriz, es decir, pasar las filas a columnas. Para esta última, utilizaremos la función $'transpose'$ de la librería $Data.List$ que se aplica sobre listas de forma que agrupa los elementos para que las listas de filas estén en la posición de la columna correspondiente.
\begin{code}
-- | Dimensión de la matriz.
dimension :: Matrix r -> (Int, Int)
dimension (M xs) | null xs   = (0,0)
                 | otherwise = (length xs, length (unVec (head xs)))

-- | Comprobar si una matriz es cuadrada.
isSquareMatrix :: Matrix r -> Bool
isSquareMatrix (M xs) = all (== l) (map lengthVec xs)
                        where l = length xs

-- | Transponer la matriz.
transpose :: Matrix r -> Matrix r
transpose (M xs) = matrix (L.transpose (map unVec xs))
\end{code}
 
La suma y multiplicación la restringiremos a la clase de los anillos, $Ring$. La suma de matrices recordamos que da una matriz cuyas entradas son la suma de las entradas correspondientes de las matrices a sumar. Para esta suma lo haremos mediante suma de listas ya que utilizaremos la función $'matrix'$ para mostrar la matriz correspondiente y esta recibe como argumento de entrada una lista de listas.\\

Por otro lado la multiplicación de matrices recordamos que consiste en multiplicar cada fila de la primera matriz por cada columna de la segunda matriz, obteniendo así un elemento en la entrada correspondiente al par de la fila y columna multiplicada. Aquí si podemos utilizar la operación $'mulVec'$ entre vectores pues devuelve un valor no un vector, por tanto obtenemos una lista de listas. Recordamos que para poder realizar multiplicaciones entre matrices el número de columnas de la primera matriz tiene que ser igual al número de filas de la segunda matriz.

\begin{code}
-- | Suma de matrices.
addM :: Ring r => Matrix r -> Matrix r -> Matrix r
addM (M xs) (M ys)
  | dimension (M xs) == dimension (M ys) = m
  | otherwise = error "Las dimensiones de las matrices son distintas"
  where
    m = matrix (zipWith (zipWith (<+>)) (map unVec xs) (map unVec ys))
   
-- | Multiplicación de matrices.
mulM :: Ring r => Matrix r -> Matrix r -> Matrix r
mulM (M xs) (M ys)
  | snd (dimension (M xs)) == fst (dimension (M ys)) = m
  | otherwise = error "La dimensión de colunmas y filas es distinta"
    where
    m = matrix [ [mulVec x y | y <- unM (transpose (M ys)) ]
               | x <- unM (M xs) ]
  
\end{code}

Para utilizar matrices sobre los anillos debemos implementarlo mediante las instancias, pero hay que tener cuidado pues el tamaño de la matriz debe codificarse al dar el tipo, las dimensiones de las matrices tienen que ser las adecuadas para que la suma y multiplicación no den errores, y tenemos que dar el vector neutro para la suma según la dimensión que vayamos a utilizar. Por estos motivos damos el código comentado.
\begin{code}
{-
instance Ring r => Ring (Matrix r) where
  (<+>) = add
  (<**>) = mul
  neg (Vec xs d) = Vec [ map neg x | x <- xs ] d
  zero  = undefined
  one = undefined
-}
\end{code}

Introducimos las propiedades básicas de la matriz identidad. Estas estarán restringidas a la clase de dominio de integridad, $IntegralDomain$.
\begin{code}
-- | Construcción de la matriz identidad nxn.
identity :: IntegralDomain r => Int -> Matrix r
identity n = matrix (xs 0)
  where
  xs x | x == n    = []
       | otherwise = (replicate x zero ++ [one] ++
                      replicate (n-x-1) zero) : xs (x+1)

-- Propiedades de la multiplicación a izquierda y derecha de la
-- matriz identidad.
propLeftIdentity :: (IntegralDomain r, Eq r) => Matrix r -> Bool
propLeftIdentity a = a == identity n `mulM` a
  where n = fst (dimension a)

propRightIdentity :: (IntegralDomain r, Eq r) => Matrix r -> Bool
propRightIdentity a = a == a `mulM` identity m
  where m = snd (dimension a)
\end{code}

A continuación  vamos a trabajar con matrices sobre anillos conmutativos, por ello restringiremos a la clase $CommutRing$. Realizaremos operaciones entre filas y columnas, y veremos que estas operaciones no afectan a la dimensión de la matriz. Hacemos esta restricción debido a que uno de los objetivos es poder aplicar el método de Gauss-Jordan, y para ello exigiremos que las matrices pertenezcan a anillos conmutativos, debido a que en el siguiente capítulo necesitaremos estas operaciones con matrices y estamos restringidos a anillos conmutativos. \\

 Damos una breve descripción de la primera operación. El objetivo es multiplicar una fila por un escalar, de forma que la matriz obtenida sea la misma con la fila que queramos modificada como el resultado de multiplicar esta fila por un número o escalar, quedando el resto de filas sin modificar, los argumentos de entrada serán la matriz, el número de la fila que queremos modificar menos 1 (pues la función $(!! r)$ de la librería Data.List selecciona el elemento $r+1$ de la lista, pues es un índice y comienza en 0). Comprobaremos que esta operación no afecta a la dimensión, pues la dimensión de la matriz resultante es la misma que la primera matriz.

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

-- La dimensión no varía.
propScaleDimension :: (Arbitrary r, CommutRing r) => Matrix r -> Int -> r -> Bool
propScaleDimension m r s = d == dimension (scaleMatrix m (mod r rows) s)
  where d@(rows,_) = dimension m
\end{code}

La siguiente operación consiste en intercambiar filas, el objetivo de $(swap \,\,m\,\,i\,\,j)$ es dada una matriz $m$ intercambiar las filas $i$ y $j$, de forma que la fila $i$ acabe en la posición de la fila $j$ y viceversa. Comprobamos que no varía de dimensión. Comprobaremos también que si realizamos el mismo intercambio dos veces obtenemos la matriz inicial.

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

-- Al intercambiar filas de una matriz no varía la dimensión.
propSwapDimension :: Matrix () -> Int -> Int -> Bool
propSwapDimension m i j = d == dimension (swap m (mod i r) (mod j r))
  where d@(r,_) = dimension m

-- | El intercambio es en sí mismo identidad.
propSwapIdentity :: Matrix () -> Int -> Int -> Bool
propSwapIdentity m i j = m == swap (swap m i' j') i' j'
  where
  d@(r,_) = dimension m
  i'      = mod i r
  j'      = mod j r
\end{code}

Mediante la función $(addRow\,\, m\,\, row@(Vec xs)\,\, x)$ realizamos la operación de sumar un vector ($row@(Vec xs)$)  a la fila $x+1$ de una matriz $m$ dada, recordamos que es importante que el vector tenga la misma dimensión que el número de colunmas de la matriz. Verificamos que la dimensión no varía. Seguidamente realizamos la misma operación sobre las columnas, para ello basta transponer la matriz y aplicar la función sobre las filas.
\begin{code}
-- | Sumar un vector a una fila de la matriz .
addRow :: CommutRing a => Matrix a -> Vector a -> Int -> Matrix a
addRow m row@(Vec xs) x
  | 0 <= x && x < r = matrix $ take x m' ++
                               zipWith (<+>) (m' !! x) xs :
                               drop (x+1) m'
  | c /= lengthVec row  = error "SumaFila: La longitud de la fila es distinta."
  | otherwise       = error "SumaFila: Error al seleccionar la fila."
    where
    (r,c) = dimension m
    m'    = unMVec m

-- La operación no afectan a la dimensión.
propAddRowDimension :: (CommutRing a, Arbitrary a)
                    => Matrix a -> Vector a -> Int -> Property
propAddRowDimension m row@(Vec xs) r =
  length xs == c ==> d == dimension (addRow m row (mod r r'))
  where d@(r',c) = dimension m

-- | Sumar un vector columna a una columna de la matriz.
addCol :: CommutRing a => Matrix a -> Vector a -> Int -> Matrix a
addCol m c x = transpose $ addRow (transpose m) c x
\end{code}

Finalmente, realizaremos la operación anterior pero esta vez restando un vector, es decir, la matriz resultante mantiene todas las filas menos la fila seleccionada, a la cuál se le resta un vector dado. 
\begin{code}
-- Restar un vector fila o columna a una fila o colunma, respectivamente,
-- de una matriz.
subRow, subCol :: CommutRing a => Matrix a -> Vector a -> Int -> Matrix a
subRow m (Vec xs) x = addRow m (Vec (map neg xs)) x
subCol m (Vec xs) x = addCol m (Vec (map neg xs)) x
\end{code}

Gracias a todo lo anterior ahora podemos implementar el método de Gauss-Jordan para poder resolver sistemas $Ax=b$ donde $A$ es una matriz $mxn$ y $b$ es un vector columna de $n$ filas. Para ello exigiremos que las matrices pertenezcan a anillos conmutativos. Comenzaremos por obtener los pivotes en cada fila, escalonar la matriz y finalmente hacer el paso de Jordan para finalmente conseguir la solución del sistema. El paso de Jordan consiste en hacer ceros por encima de la diagonal de la matriz cuando previamente se ha obtenido ceros debajo de la diagonal de la matriz, esta primera parte se conoce como aplicar Gauss o realizar el método de Gauss.\\

Para empezar damos las funciones de obtener un 0 en la posición del pivote y la segunda función consiste en localizar el siguiente pivote.
\begin{code}
-- | Multiplicar por el escalar correspondiente  la fila donde está
-- el pivote y sumarle la fila en la que queremos hacer un 0.
-- El escalar se elige de forma que al sumar la fila consigamos un 0
-- en la posición del pivote.
pivot :: CommutRing a => Matrix a -> a -> Int -> Int -> Matrix a
pivot m s p t = addRow m (fmap (s <**>) (unM m !! p)) t

-- | Encontrar el primer cero en las filas debajo del pivot y
-- devolver el valor y el número de la fila en la que está.
findPivot :: (CommutRing a, Eq a) => Matrix a -> (Int,Int) -> Maybe (a,Int)
findPivot m (r,c) = safeHead $ filter ((/= zero) . fst) $ drop (r+1) $
                    zip (head $ drop c $ unMVec $ transpose m) [0..]
  where
  m' = unMVec m

  safeHead []     = Nothing
  safeHead (x:xs) = Just x
\end{code}

Con la siguiente función buscamos modificar la fila del pivote de forma que obtengamos el cero en la posición del pivote. Para ello necesitamos que sea un cuerpo pues necesitamos que exista inverso, ya que el valor del escalar al multiplicarse por la fila en la posición del pivote debemos obtener el inverso del pivote para que al sumarlo obtengamos un cero.
\begin{code}
-- | Modificamos las filas para hacer 0 en la columna del pivot.
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

  xs = unMVec m
\end{code}

Para calcular la forma escalonada seguimos necesitando que los elementos de las matrices pertenezca a un cuerpo. Primero aplicamos Gauss, es decir, obtenemos ceros por debajo de la diagonal.
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
      -- El algoritmo se hace cuando llega a la última columna o fila.
    | c == mc || r == mr =
      -- Descompone la matriz en A y b de nuevo.
      (matrix *** Vec) $ unzip $ map (init &&& last) $ unMVec m

    | m !!! rc == zero   = case findPivot m rc of
      -- Si el pivot de la fila pivot es cero entonces intercambiamos la
      -- fila pivot por la primera fila con elemento no nulo en la columna
      -- del pivot.
      Just (_,r') -> fE (swap m r r') rc
      -- Si todos los elementos de la columna pivot son cero entonces nos
      -- movemos a la siguiente columna por la derecha.
      Nothing     -> fE m (r,c+1)

    | m !!! rc /= one    =
      -- Convertir el pivot en 1.
      fE (scaleMatrix m r (inv (m !!! rc))) rc

    | otherwise          = case findPivot m rc of
      -- Hacer 0 el primer elemento distinto de cero en la fila pivot.
      Just (v,r') -> fE (pivot m (neg v) r r') (r,c)
      -- Si todos los elementos en la columna pivot son 0 entonces nos
      --  vemos a la fila de abajo y hacia la columna de la derecha.
      Nothing     -> fE m (r+1,c+1)

  (mr,mc) = dimension m

  -- Divide la matriz en A y b, donde b es la última columna de la matriz
  -- y A el resto de la matriz.
  m' = matrix $ [ r ++ [x] | (r,x) <- zip (unMVec m) (unVec v) ]
\end{code}

En segundo lugar aplicamos el paso de Jordan que consiste en obtener ceros por encima de la diagonal. Para aplicar el método de Gauss-Jordan es necesario aplicar antes el paso de Gauss y después el de Jordan.

\begin{code}
-- | Realizar el paso "Jordan" en la eliminación de Gauss-Jordan. Esto es hacer que cada
-- elemento encima de la diagonal sea cero.

jordan :: (Field a, Eq a) => (Matrix a, Vector a) -> (Matrix a, Vector a)
jordan (m, Vec ys) = case L.unzip (jordan' (zip (unMVec m) ys) (r-1)) of
  (a,b) -> (matrix a, Vec b)
  where
  (r,_) = dimension m

  jordan' [] _ = []
  jordan' xs c =
    jordan' [ (take c x ++ zero : drop (c+1) x, v <-> x !! c <**> snd (last xs))
            | (x,v) <- init xs ] (c-1) ++ [last xs]
\end{code}

Finalmente, podemos realizar el método de Gauss-Jordan, con el objetivo de resolver un sistema de ecuaciones de la forma $Ax=b$, primero obtenemos la matriz con solo la diagonal que es la obtenida tras aplicar Gauss y luego Jordan esto lo obtenemos con la función de denotaremos $gaussElim$. \\

Con la función que denotaremos $gaussElimCorrect$ recibe la partición de la matriz $A$ y la matriz $b$ con ella comprobamos que las dimensiones de ambas son correctas de esta forma hemos obtenido la solución del sistema, ya que en la diagonal nos ha quedado nuestro vector de incógnitas con coeficiente igual a 1 y en $b$ se encuentra los valores de nuestras incógnitas.

\begin{code}
-- | Eliminación por Gauss-Jordan: Dados A y b resuelve Ax=b.
gaussElim :: (Field a, Eq a, Show a) => (Matrix a, Vector a) -> (Matrix a, Vector a)
gaussElim = jordan . forwardElim

gaussElimCorrect :: (Field a, Eq a, Arbitrary a, Show a) => (Matrix a, Vector a) -> Property
gaussElimCorrect m@(a,b) = fst (dimension a) == lengthVec b && isSquareMatrix a ==>
  matrixToVector (transpose (a `mulM` transpose (M [snd (gaussElim m)]))) == b
\end{code}
