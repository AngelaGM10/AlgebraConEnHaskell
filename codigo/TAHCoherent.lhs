\begin{code}
module TAHCoherent
  ( Coherent(solve)
  , propCoherent, isSolution
  , solveMxN, propSolveMxN
  , solveWithIntersection
  , solveGeneralEquation, propSolveGeneralEquation
  , solveGeneral, propSolveGeneral
  ) where

import Test.QuickCheck

import TAHIntegralDomain
import TAHIdeal
import TAHStronglyDiscrete
import TAHMatrix

\end{code}

\begin{defi}
Un anillo R es coherente si dada una matriz $M \in\, R^{1\times n}$ existe una matriz $L \in\,\mathbb{R}^{n\times m}$ para $m \in\, \mathbb{N}$ tal que $ML=0$ y
\begin{center}
$MX = 0 \Leftrightarrow \exists Y \in\, R^{m\times 1}.\,\, X = LY$
\end{center}
\end{defi}

De esta forma es posible calcular un conjunto de generadores para soluciones
de ecuaciones en un anillo coherente. En otras palabras, el conjunto de soluciones para $MX = 0$ esta generado finitamente. Comenzamos por establecer la clase de los anillos coherentes:

\begin{code}
class IntegralDomain a => Coherent a where
  solve :: Vector a -> Matrix a
\end{code}

Damos funciones para comprobar soluciones y resolver sistemas de ecuaciones sobre anillos conmutativos, para ello usaremos recursión.

\begin{code}
-- | Test para comprobar que la segunda matriz es una solución de la primera.
isSolution :: (CommutRing a, Eq a) => Matrix a -> Matrix a -> Bool
isSolution m sol = all (==zero) (concat (unMVec (m `mulM` sol)))

propCoherent :: (Coherent a, Eq a) => Vector a -> Bool
propCoherent m = isSolution (vectorToMatrix m) (solve m)
\end{code}

Con la siguiente función podemos resolver de forma recursiva todos los subsistemas para obtener mediante recursión la solución $X$. Si la solución calculada es de hecho una solución del siguiente conjunto de ecuaciones, entonces no hace nada. Gracias a esto resolvemos los problemas que tienen muchas filas idénticas en el sistema, como [[1,1], [1,1]].

\begin{code}
solveMxN :: (Coherent a, Eq a) => Matrix a -> Matrix a
solveMxN (M (l:ls)) = solveMxN' (solve l) ls
  where
  solveMxN' :: (Coherent a, Eq a) => Matrix a -> [Vector a] -> Matrix a
  solveMxN' m []      = m
  solveMxN' m1 (x:xs) = if isSolution (vectorToMatrix x) m1
                           then solveMxN' m1 xs
                           else solveMxN' (m1 `mulM` m2) xs
    where m2 = solve (matrixToVector (mulM (vectorToMatrix x) m1))


-- | Test para comprobar que la solución de un sistema MxN obtenido con $solveMxN$ es de hecho una solución del sistema. 
propSolveMxN :: (Coherent a, Eq a) => Matrix a -> Bool
propSolveMxN m = isSolution m (solveMxN m)

\end{code}

Vemos como funciona $solveMxN$ con más detalle. Toma una matriz de entrada y selecciona el primer vector (o la primera fila de la matriz) para aplicar $solveMxN'$. Esta toma dos matrices de entrada, veamos el caso de $(solveMxN'\,\, m1\,\, (x:xs))$, comprobamos que la matriz $m1$ es solución de $x$. En esta caso, resolvemos con $(solveMxN' m1 xs)$ aplicando la recursión. En caso contrario, multiplicamos la matriz $m1$ por la matriz $x$, la matriz resultante la transformamos en vector y aplicamos $solve$ sobre ella. A continuación se aplica $solveMxN'$ sobre la matriz resultante tras aplicar solve al vector obtenido  y sobre $xs$.\\

Si hay un algoritmo para calcular un conjunto de generadores finitamente generados para
la intersección de dos ideales finitamente generados entonces el anillo es coherente.\\

$Prueba$: 
Cogemos el vector a  resolver, $[x1,...,xn]$, y una función $(int)$ que calcule la intersección de dos ideales.\\
Si $[x_1, ..., x_n]\,\, `int`\,\,[ y_1, ..., y_m] = [ z_1, ..., z_l]$.\\
Entonces $(int)$ debería devolver $us$ y $vs$ tales que:\\
$z_k = n_k1 * x_1 + ... + u_kn * x_n = u_k1 * y_1 + ... + n_km * y_m$\\

Así podemos obtener una solución del sistema mediante la intersección.
\begin{code}
solveWithIntersection :: (IntegralDomain a, Eq a)
                      => Vector a
                      -> (Ideal a -> Ideal a -> (Ideal a,[[a]],[[a]]))
                      -> Matrix a
solveWithIntersection (Vec xs) int = transpose $ matrix $ solveInt xs
  where
  solveInt []     = error "solveInt: No puede resolver un sistema vacío"
  solveInt [x]    = [[zero]] -- Caso base, podría ser [x,y] también...
                             -- Este no daría la solución trivial
  solveInt [x,y]  | x == zero || y == zero = [[zero,zero]]
                  | otherwise =
    let (Id ts,us,vs) = (Id [x]) `int` (Id [neg y])
    in [ u ++ v | (u,v) <- zip us vs ]
  solveInt (x:xs)
    | x == zero             = (one : replicate (length xs) zero) : (map (zero:) $ solveInt xs)
    | isSameIdeal int as bs = s ++ m'
    | otherwise             = error "solveInt: No se puede calcular la intersección"
      where
      as            = Id [x]
      bs            = Id (map neg xs)

      -- Calculamos al intersección de <x1> y <-x2,...,-xn>
      (Id ts,us,vs) = as `int` bs
      s             = [ u ++ v | (u,v) <- zip us vs ]

      -- Resuelve <0,x2,...,xn> recursivamente
      m             = solveInt xs
      m'            = map (zero:) m

\end{code}

De este código destacamos la función $solveInt$, vamos a explicar brevemente como funciona. Es una función recursiva, obviando los casos base, dada una lista $(x:xs)$ hay 3 casos por orden de prioridad. En primer lugar si x es 0 ejecuta las órdenes de añadir la lista que comienza por 1 seguida de tantos ceros como longitud de la lista $xs$ y esta pequeña lista se añade al comienzo de la segunda lista formada por añadir un 0 a la solución obtenida mediante recursión de la lista $xs$ con $(solveInt\,\, xs)$. En segundo lugar, en el caso de que $x$ sea distinto de 0, aplicamos $isSameIdeal$ para comprobar que la intersección se pueda hacer si resulta ser $True$ aplicamos la concatenación de la lista $s$ con $m'$. Donde $s$ se obtiene a partir de la intersección del ideal $<x>$ y del ideal obtenido tras aplicar $neg$ a cada elemento de $xs$ y $m'$ es la lista tras añadir 0 a cada lista de la matriz $m$.\\

Dentro de los anillos anillos coherentes, encontramos los anillos coherentes fuertemente discretos. Restringiendo la clase de anillos a la clase de fuertemente discreto, esto nos permite una facilidad mayor a la hora de resolver sistemas. Puesto que, si un anillo es fuertemente discreto y coherente entonces podemos resolver cualquier ecuación del tipo $AX=b$.

\begin{code}
solveGeneralEquation :: (Coherent a, StronglyDiscrete a) => Vector a -> a -> Maybe (Matrix a)
solveGeneralEquation v@(Vec xs) b =
  let sol = solve v
  in case b `member` (Id xs) of
    Just as -> Just $ transpose (M (replicate (length (head (unMVec sol))) (Vec as)))
                      `addM` sol
    Nothing -> Nothing


propSolveGeneralEquation :: (Coherent a, StronglyDiscrete a, Eq a)
                         => Vector a
                         -> a
                         -> Bool
propSolveGeneralEquation v b = case solveGeneralEquation v b of
  Just sol -> all (==b) $ concat $ unMVec $ vectorToMatrix v `mulM` sol
  Nothing  -> True
\end{code}

La primera función, $solveGeneralEquation$ calcula una solución general. Para ello toma un vector $(Vec xs)$ el cuál se llamará $v$ gracias al $@$ y el vector solución $b$. A continuación llamamos $sol$ a $solve v$, de esta forma pasamos de vector a matriz gracias a $solve$. Seguidamente comprobamos si $b$ pertenece al ideal de $xs$ en ese caso guardamos en as 

--explicar el just y nothing---

Con la siguiente función comprobaremos si la solución obtenida anteriormente ($sol$) es correcta. Para ello comprobaremos que al realizar la multiplicación de nuestra matriz A por la solución obtenida coincide componente a componente con el vector solución $b$.

\begin{code}
isSolutionB v sol b = all (==b) $ concat $ unMVec $ vectorToMatrix v `mulM` sol
\end{code}

Ahora vamos a resolver sistemas lineales generales de la forma $AX = B$.
\begin{code}
solveGeneral :: (Coherent a, StronglyDiscrete a, Eq a)
             => Matrix a   -- A
             -> Vector a   -- B
             -> Maybe (Matrix a, Matrix a)  -- (L,X0)
solveGeneral (M (l:ls)) (Vec (a:as)) =
  case solveGeneral' (solveGeneralEquation l a) ls as [(l,a)] of
    Just x0 -> Just (solveMxN (M (l:ls)), x0)
    Nothing -> Nothing
  where
  -- Calculamos una nueva solución de forma inductiva y verificamos que la nueva solución
  -- satisface todas las ecuaciones anteriores.
  solveGeneral' Nothing _ _ _              = Nothing
  solveGeneral' (Just m) [] [] old         = Just m
  solveGeneral' (Just m) (l:ls) (a:as) old =
    if isSolutionB l m a
       then solveGeneral' (Just m) ls as old
       else case solveGeneralEquation (matrixToVector (vectorToMatrix l `mulM` m)) a of
         Just m' -> let m'' = m `mulM` m'
                    in if all (\(x,y) -> isSolutionB x m'' y) old
                          then solveGeneral' (Just m'') ls as ((l,a):old)
                          else Nothing
         Nothing -> Nothing
  solveGeneral' _ _ _ _ = error "solveGeneral: Error en la entrada"
\end{code}

De $solveGeneral$ explicaremos con detalle como funciona $solveGeneral'$ ---Explicar hay mucho Nothing y Just---


Con la siguiente propiedad, comprobaremos que la solución es correcta. Primero tenemos que comprobar que las filas de $A$ (se presentará en código por $m$) son de la misma longitud que $b$. Después, multiplicamos la matriz $A$ con la matriz solución $X$ y vemos si coincide componente a componente con el vector solución $b$. Devolviendo al final un $True$.
\begin{code}
propSolveGeneral :: (Coherent a, StronglyDiscrete a, Eq a) => Matrix a -> Vector a -> Property
propSolveGeneral m b = length (unM m) == length (unVec b) ==> case solveGeneral m b of
  Just (l,x) -> all (==b) (unM (transpose (m `mulM` x))) &&
                isSolution m l
  Nothing -> True

\end{code}

