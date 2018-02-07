\begin{code}
-- | Una pequeña librería de matrices simples.
module TAHMatriz
  ( Vector(Vec)
  , unVec, lengthVec
  , Matrix(M), matrix
  , matrixToVector, vectorToMatrix, unMVec, unM, (!!!)
  , identity, propLeftIdentity, propRightIdentity
  , mulM, addM, transpose, isSquareMatrix, dimension
  , scale, swap, pivot
  , addRow, subRow, addCol, subCol
  , findPivot, forwardElim, gaussElim, gaussElimCorrect
  ) where

import qualified Data.List as L
import Data.Function (on)
import Control.Monad (liftM)
import Control.Arrow hiding ((<+>))
import Test.QuickCheck

import TAHCuerpo

import Debug.Trace

\end{code}

Comenzamos por implementar las nocines básicas de los vectores. Creamos un nuevo tipo para definir un vector, usaremos las listas para aplicarlas sobre el tipo $Vector$ y trabajar con ellas como vectores en Haskell:
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

-- Aplicar una función f a un vector.
instance Functor Vector where 
  fmap f = Vec . map f . unVec
\end{code}

Ahora vamos a definir la suma y multiplicación de vectores sobre un anillo. Estas operaciones tenemos que dejarlas comentadas pues para que funcionen tenemos que asignar el elemento neutro para la suma y producto, pues estamos definiendolo como una instancia de la clase $Ring$. Recordamos que para realizar operaciones con vectores estos tienen que tener la misma dimensión.
\begin{code}
{-
instance Ring r => Ring (Vector r) where
  (Vec xs) <+> (Vec ys) | length xs == length ys = Vec (zipWith (<+>) xs ys)
                        | otherwise = error "Los vectores no se pueden sumar porque tienen dimensiones diferentes"
  (Vec xs) <**> (Vec ys) | length xs == length ys = Vec (zipWith (<**>) xs ys)
                         | otherwise = error "Los vectores no se pueden multiplicar porque tienen dimensiones diferentes"
  one  = ?
  zero = ?
-}
\end{code}

Para acabar con los vectores damos la función que muestra el vector y la que mide la longitud de un vector en ese formato.

\begin{code}
unVec :: Vector r -> [r]
unVec (Vec vs) = vs

lengthVec :: Vector r -> Int
lengthVec = length . unVec
\end{code}

Una vez dadas las nocines de los vectores podemos comenzar a implementar las nociones de las matrices, notesé que cada fila o columna de una matriz puede verse como un vector. Haciendo uso del tipo $Vector$ implementamos las matrices como nuevo tipo.
\begin{code}
-- | Matrices
newtype Matrix r = M [Vector r]
  deriving (Eq)

instance Show r => Show (Matrix r) where
  show xs = case unlines (map show (unMVec xs)) of
    [] -> "[]" 
    xs -> init xs ++ "\n"

-- Generar matrices con como mucho 10 filas.
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

-- aplicar una función f a una matriz.
instance Functor Matrix where
  fmap f = M . map (fmap f) . unM
\end{code}

Una vez implementado el tipo de las matrices vamos a crear la función para construir una matriz de dimensión mxn a partir de una lista de vectores, de forma que cada vector es una fila de la matriz (todos de la misma longitud) y la longitud un vector es el número de columnas.
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

Las siguientes funciones son para mostrar una matriz como lista de vectores, y aplicar funciones con este formato sobre ella. Pasar de matrices a vectores y viceversa, así como una función para comprobar que las dimensiones de la matriz son correctas y ninguna es mayor de 10 (Notesé que para esta última función hemos utilizado el símbolo $(!!!)$ que se utiliza en mátematicas para las contradicciones).
\begin{code}
-- Mostrar la matriz como lista de vectores.
unM :: Matrix r -> [Vector r]
unM (M xs) = xs

-- Aplicar lo anterior a cada vector de la lista.
unMVec :: Matrix r -> [[r]]
unMVec = map unVec . unM

-- De vector a matriz.
vectorToMatrix :: Vector r -> Matrix r
vectorToMatrix = matrix . (:[]) . unVec

-- De matriz a vector.
matrixToVector :: Matrix r -> Vector r
matrixToVector m | fst (dimension m) == 1 = head (unM m)
                 | otherwise              = error "No pueden tener dimensiones distintas"

-- Comprobar si la dimensión es correcta según los parámetros que hemos establecido.
(!!!) :: Matrix a -> (Int,Int) -> a
m !!! (r,c) | r >= 0 && r < rows && c >= 0 && c < cols = unMVec m !! r !! c
            | otherwise = error "!!!: Fuera de los límetes"
  where
  (rows,cols) = dimension m 
\end{code}

Utilizando las funciones anteriores podemos implementar propiedades y operaciones con las matrices.

\begin{code}
-- | Dimensión de la matriz.
dimension :: Matrix r -> (Int, Int)
dimension (M xs) | null xs   = (0,0)
                 | otherwise = (length xs, length (unVec (head xs)))

-- | Comprobar si una matriz es cuadrada.
isSquareMatrix :: Matrix r -> Bool
isSquareMatrix (M xs) = all (== length xs) (map lengthVec xs)

-- | Transponer la matriz.
transpose :: Matrix r -> Matrix r
transpose (M xs) = matrix (L.transpose (map unVec xs))

-- | Suma de matrices.
addM :: Ring r => Matrix r -> Matrix r -> Matrix r
addM (M xs) (M ys)
  | dimension (M xs) == dimension (M ys) = m
  | otherwise = error "Las dimensiones de las matrices no pueden ser distintas"
  where
  m = matrix (zipWith (zipWith (<+>)) (map unVec xs) (map unVec ys))

-- | Multiplicación de matrices.
mulM :: Ring r => Matrix r -> Matrix r -> Matrix r
mulM (M xs) (M ys)
  | snd (dimension (M xs)) == fst (dimension (M ys)) = m
  | otherwise = error "Las dimensiones de las matrices no pueden ser distintas"
    where
    m = matrix [ [ mulVec x y | y <- L.transpose (map unVec ys) ]
               | x <- map unVec xs ]

-- | Multiplicación de Vectores
mulVec xs ys | length xs == length ys = foldr (<+>) zero $ zipWith (<**>) xs ys
             | otherwise = error "Las dimensiones de los vectores no pueden ser distintas"
\end{code}

Para utilizar matrices sobre los anillos debemos implementarlo mediante las instancias, pero hay que tener cuidado pues el tamaño de la matriz debe codificarse al dar el tipo, las dimensiones de las matrices tienen que ser las adecuadas para que la suma y multiplicación no den errores, y tenemos que dar el vector neutro para la suma según la dimensión que vayamos a utilizar. Por estos motivos damos el código comentado.
\begin{code}
{-
instance Ring r => Ring (Matrix r) where
  (<+>) = add
  (<**>) = mul
  neg (Vec xs d) = Vec [ map neg x | x <- xs ] d
  zero  = undefined
-}
\end{code}

Introducimos ahora las nociones básicas de la matriz identidad.
\begin{code}
-- | Construcción de la matriz identidad nxn.
identity :: IntegralDomain r => Int -> Matrix r
identity n = matrix (xs 0)
  where
  xs x | x == n    = []
       | otherwise = (replicate x zero ++ [one] ++
                      replicate (n-x-1) zero) : xs (x+1)

-- Propiedades de la multiplicación a izquierda y derecha de la matriz identidad.
propLeftIdentity :: (IntegralDomain r, Eq r) => Matrix r -> Bool
propLeftIdentity a = a == identity n `mulM` a
  where n = fst (dimension a)

propRightIdentity :: (IntegralDomain r, Eq r) => Matrix r -> Bool
propRightIdentity a = a == a `mulM` identity m
  where m = snd (dimension a)
\end{code}

A continuación  vamos a trabajar con matrices sobre anillos conmutativos. Realizaremos suma entre filas y columnas, definiremos el concepto de matriz escalar y dado que estas operaciones no afectan a la dimensión daremos funciones para comprobarlo. Una matriz escalar es una matriz diagonal en la que los elementos de la diagonal principal son iguales. 
\begin{code}
-- | Escalar una fila en la matriz.
scaleMatrix :: CommutRing a => Matrix a -> Int -> a -> Matrix a
scaleMatrix m r s
  | 0 <= r && r < rows = matrix $ take r m' ++ map (s <**>) (m' !! r) : drop (r+1) m'
  | otherwise = error "Escala: índice fuera de los límites"
  where
  (rows,_) = dimension m
  m'       = unMVec m

-- Escalar una matriz no afecta a la dimensión.
propScaleDimension :: (Arbitrary r, CommutRing r) => Matrix r -> Int -> r -> Bool
propScaleDimension m r s = d == dimension (scaleMatrix m (mod r rows) s)
  where d@(rows,_) = dimension m

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

-- Intercambiar filas de una matriz no afecta a la dimensión.
propSwapDimension :: Matrix () -> Int -> Int -> Bool
propSwapDimension m i j = d == dimension (swap m (mod i r) (mod j r))
  where d@(r,_) = dimension m

-- El intercambio es en sí mismo identidad, es decir, intercambiar dos filas ya
-- intercambiadas entre ellas vuelve a estar como al principio.
propSwapIdentity :: Matrix () -> Int -> Int -> Bool
propSwapIdentity m i j = m == swap (swap m i' j') i' j'
  where
  d@(r,_) = dimension m
  i'      = mod i r
  j'      = mod j r


-- Sumar dos filas de la matriz .
addRow :: CommutRing a => Matrix a -> Vector a -> Int -> Matrix a
addRow m row@(Vec xs) x
  | 0 <= x && x < r = matrix $ take x m' ++
                               zipWith (<+>) (m' !! x) xs :
                               drop (x+1) m'
  | c /= length xs  = error "SumaFila: La longitud de la fila es distinta."
  | otherwise       = error "SumaFila: Error al seleccionar la fila."
    where
    (r,c) = dimension m
    m'    = unMVec m

-- Las operaciones de suma entre filas no afectan a la dimensión.
propAddRowDimension :: (CommutRing a, Arbitrary a)
                    => Matrix a -> Vector a -> Int -> Property
propAddRowDimension m row@(Vec xs) r =
  length xs == c ==> d == dimension (addRow m row (mod r r'))
  where d@(r',c) = dimension m

-- Sumar dos columnas de la matriz.
addCol :: CommutRing a => Matrix a -> Vector a -> Int -> Matrix a
addCol m c x = transpose $ addRow (transpose m) c x

-- Restar filas y columnas.
subRow, subCol :: CommutRing a => Matrix a -> Vector a -> Int -> Matrix a
subRow m (Vec xs) x = addRow m (Vec (map neg xs)) x
subCol m (Vec xs) x = addCol m (Vec (map neg xs)) x
\end{code}

Gracias a todo lo anterior ahora podemos implementar el método de Gauss-Jordan para poder resolver sistemas $Ax=b$ donde $A$ es una matriz $mxn$ y $b$ es un vector columna de $n$ filas. Comenzaremos por obtener los pivots en cada fila, escalonar la matriz y finalmente hacer el paso de "Jordan" para finalmente conseguir la solución del sistema.
\begin{code}
-- Multiplicar la fila donde está el pivot y sumarle la fila en la que queremos hacer un 0.
pivot :: CommutRing a => Matrix a -> a -> Int -> Int -> Matrix a
pivot m s p t = addRow m (fmap (s <**>) (unM m !! p)) t

-- Encontrar el primer cero en las filas debajo del pivot y devolver el valor y el número
-- de la fila en la que está.
findPivot :: (CommutRing a, Eq a) => Matrix a -> (Int,Int) -> Maybe (a,Int)
findPivot m (r,c) = safeHead $ filter ((/= zero) . fst) $ drop (r+1) $ zip (head $ drop c $ unMVec $ transpose m) [0..]
  where
  m' = unMVec m

  safeHead []     = Nothing
  safeHead (x:xs) = Just x

fE :: (Field a, Eq a) => Matrix a -> Matrix a
fE (M [])         = M []
fE (M (Vec []:_)) = M []
fE m     = case L.findIndices (/= zero) (map head xs) of
  (i:is) -> case fE (cancelOut m [ (i,map head xs !! i) | i <- is ] (i,map head xs !! i)) of
    ys -> matrix (xs !! i : map (zero :) (unMVec ys))
  []     -> case fE (matrix (map tail xs)) of
    ys -> matrix (map (zero:) (unMVec ys))
  where
  cancelOut :: (Field a, Eq a) => Matrix a -> [(Int,a)] -> (Int,a) -> Matrix a
  cancelOut m [] (i,_)    = let xs = unMVec m in matrix $ map tail (L.delete (xs !! i) xs)
  cancelOut m ((t,x):xs) (i,p) = cancelOut (pivot m (neg (x </> p)) i t) xs (i,p)

  xs = unMVec m


-- | Calcular la forma escalonada de un sistema Ax = b.
forwardElim :: (Field a, Eq a) => (Matrix a,Vector a) -> (Matrix a,Vector a)
forwardElim (m,v) = fE m' (0,0)
  where
  -- fE coge la matriz a escalonar y la fila y columnas correspondientes.
  fE :: (Field a, Eq a) => Matrix a -> (Int,Int) -> (Matrix a,Vector a)
  fE (M []) _  = error "forwardElim: La matriz dada es vacía."
  fE m rc@(r,c)
      -- El algoritmo se hace cuando llega a la última columna o fila.
    | c == mc || r == mr =
      -- Descompone la matriz en A y b de nuevo.
      (matrix *** Vec) $ unzip $ map (init &&& last) $ unMVec m

    | m !!! rc == zero   = case findPivot m rc of
      -- Si el pivot de la fila pivot es cero entonces intercambiamos la fila pivot
      -- por la primera fila con elemento no nulo en la columna del pivot.
      Just (_,r') -> fE (swap m r r') rc
      -- Si todos los elementos de la columna pivot son cero entonces nos movemos
      -- a la siguiente columna por la derecha.
      Nothing     -> fE m (r,c+1)

    | m !!! rc /= one    =
      -- Convertir el pivot en 1.
      fE (scaleMatrix m r (inv (m !!! rc))) rc

    | otherwise          = case findPivot m rc of
      -- Hacer 0 el primer elemento distinto de cero en la fila pivot.
      Just (v,r') -> fE (pivot m (neg v) r r') (r,c)
      -- Si todos los elementos en la columna pivot son 0 entonces nos vemos a la
      -- fila de abajo y hacia la columna de la derecha.
      Nothing     -> fE m (r+1,c+1)

  (mr,mc) = dimension m

  -- Combina A y b una matriz donde la última columna es b.
  m' = matrix $ [ r ++ [x] | (r,x) <- zip (unMVec m) (unVec v) ]


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


-- | Eliminación por Gauss-Jordan: Dados A y B resuelve Ax=B.
gaussElim :: (Field a, Eq a, Show a) => (Matrix a, Vector a) -> (Matrix a, Vector a)
gaussElim = jordan . forwardElim

gaussElimCorrect :: (Field a, Eq a, Arbitrary a, Show a) => (Matrix a, Vector a) -> Property
gaussElimCorrect m@(a,b) = fst (dimension a) == lengthVec b && isSquareMatrix a ==>
  matrixToVector (transpose (a `mulM` transpose (M [snd (gaussElim m)]))) == b
\end{code}
