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
import TAHStronglyDiscrete
import TAHMatriz
import TAHIdeal

\end{code}

\begin{defi}
Un anillo R es coherente si todo ideal generado finitamente es finito. Esto significa que dado una matriz $M \in\, R^{1\times n}$ existe una matriz $L \in\, R^{n\times m}$ para $m \in\, \mathbb{N}$ tal que $ML=0$ y\\
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

Empezamos por dar funciones para comprobar soluciones y resolver sistemas de ecuaciones sobre anillos conmutativos.
\begin{code}
-- | Test para comprobar que la segunda matriz es una solución de la primero.
isSolution :: (CommutRing a, Eq a) => Matrix a -> Matrix a -> Bool
isSolution m sol = all (==zero) (concat (unMVec (m `mulM` sol)))

propCoherent :: (Coherent a, Eq a) => Vector a -> Bool
propCoherent m = isSolution (vectorToMatrix m) (solve m)

-- | Resolver un sistema de ecuaciones.
solveMxN :: (Coherent a, Eq a) => Matrix a -> Matrix a
solveMxN (M (l:ls)) = solveMxN' (solve l) ls
  where
  -- Resolver de forma recursiva todos los subsistemas. Si la solución calculada es de
  -- hecho una solución del siguiente conjunto de ecuaciones, entonces no hagas nada.
  -- Esto resuelve los problemas que tienen muchas filas idénticas en el sistema,
  -- como [[1,1], [1,1]].
  solveMxN' :: (Coherent a, Eq a) => Matrix a -> [Vector a] -> Matrix a
  solveMxN' m []      = m
  solveMxN' m1 (x:xs) = if isSolution (vectorToMatrix x) m1
                           then solveMxN' m1 xs
                           else solveMxN' (m1 `mulM` m2) xs
    where m2 = solve (matrixToVector (mulM (vectorToMatrix x) m1))


-- | Test para comprobar que la solución de un sistema MxN es de hecho una solución del sistema. 
propSolveMxN :: (Coherent a, Eq a) => Matrix a -> Bool
propSolveMxN m = isSolution m (solveMxN m)
\end{code}

Implementamos la solución por intersección. Vamos a ver que si hay un algoritmo para calcular un f.g. conjunto de generadores para
la intersección de dos f.g. ideales entonces el anillo es coherente. Cogemos el vector a resolver, $\[x_1,..,x_n\]$, y una función $(int)$ que calcule la intersección de dos ideales.\\

\begin{code}
solveWithIntersection :: (IntegralDomain a, Eq a)
                      => Vector a
                      -> (Ideal a -> Ideal a -> (Ideal a,[[a]],[[a]]))
                      -> Matrix a
solveWithIntersection (Vec xs) int = transpose $ matrix $ solveInt xs
  where
  solveInt []     = error "solveInt: No se puede resolver un sistema vacío"
  solveInt [x]    = [[zero]] -- Caso base, podría ser [x, y] también ...
                             -- Eso no daría la solución trivial ...
  solveInt [x,y]  | x == zero || y == zero = [[zero,zero]]
                  | otherwise =
    let (Id ts,us,vs) = (Id [x]) `int` (Id [neg y])
    in [ u ++ v | (u,v) <- zip us vs ]
  solveInt (x:xs)
    | x == zero             = (one : replicate (length xs) zero) : (map (zero:) $ solveInt xs)
    | isSameIdeal int as bs = s ++ m'
    | otherwise             = error "solveInt: No puede calcularse la intersección"
      where
      as            = Id [x]
      bs            = Id (map neg xs)

      -- Calculamos la intersección de <x1> and <-x2,...,-xn>
      (Id ts,us,vs) = as `int` bs
      s             = [ u ++ v | (u,v) <- zip us vs ]

      -- Resuelve <0,x2,...,xn> recursivamente
      m             = solveInt xs
      m'            = map (zero:) m
\end{code}

La propiedad de ser fuertemente discreto es una propiedad muy fuerte que pueden poseer los anillos. Pues si el anillo es muy discreto y coherente, no solo es posible resolver sistemas como $MX = 0$, también es posible resolver sistemas generales del tipo $MX = A$.

Si R es un dominio de integridad coherente fuertemente discreto entonces es posible resolver sistemas lineales arbitrarios.
Dado $MX = A$ es posible calcular $X_0$ y $L$ tal que $ML = 0$ y
\begin{center}
$MX = A \leftrightarrow \,\exists\,\, YX = LY + X_0$
\end{center}

Implementamos la resolución de estos anillos coherentes fuertemente discretos:
\begin{code}
-- | Anillos coherentes fuertemente discretos.
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


isSolutionB v sol b = all (==b) $ concat $ unMVec $ vectorToMatrix v `mulM` sol

-- | Resolver un sistema general de ecuaciones lineales de la forma AX=B.
-- A es una matriz dada y B viene dada como un vector fila
-- (este debería ser un vector columna).
solveGeneral :: (Coherent a, StronglyDiscrete a, Eq a)
             => Matrix a   -- M
             -> Vector a   -- B
             -> Maybe (Matrix a, Matrix a)  -- (L,X0)
solveGeneral (M (l:ls)) (Vec (a:as)) =
  case solveGeneral' (solveGeneralEquation l a) ls as [(l,a)] of
    Just x0 -> Just (solveMxN (M (l:ls)), x0)
    Nothing -> Nothing
  where
  -- Calculamos una nueva solución de forma inductiva y verificando que la nueva solución
  -- cumple todas las ecuaciones anteriores.
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
  solveGeneral' _ _ _ _ = error "solveGeneral: La entrada no es válida"


-- Estaría bien poder generar solo sistemas con solución ...
propSolveGeneral :: (Coherent a, StronglyDiscrete a, Eq a) => Matrix a -> Vector a -> Property
propSolveGeneral m b = length (unM m) == length (unVec b) ==> case solveGeneral m b of
  Just (l,x) -> all (==b) (unM (transpose (m `mulM` x))) &&
                isSolution m l
  Nothing -> True

\end{code}
