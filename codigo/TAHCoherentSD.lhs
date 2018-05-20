\begin{code}
module TAHCoherentSD
  ( solveGeneralEquation, propSolveGeneralEquation
  , solveGeneral, propSolveGeneral
  ) where

import Test.QuickCheck

import TAHIntegralDomain
import TAHIdeal
import TAHStronglyDiscrete
import TAHVector
import TAHMatrix
import TAHCoherent

\end{code}

--meter introducción para la primera función

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

{-\begin{code}
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
\end{code}-}



De $solveGeneral$ explicaremos con detalle como funciona $solveGeneral'$ ---Explicar hay mucho Nothing y Just---


Con la siguiente propiedad, comprobaremos que la solución es correcta. Primero tenemos que comprobar que las filas de $A$ (se presentará en código por $m$) son de la misma longitud que $b$. Después, multiplicamos la matriz $A$ con la matriz solución $X$ y vemos si coincide componente a componente con el vector solución $b$. Devolviendo al final un $True$.

{-\begin{code}
propSolveGeneral :: (Coherent a, StronglyDiscrete a, Eq a) => Matrix a -> Vector a -> Property
propSolveGeneral m b = length (unM m) == length (unVec b) ==> case solveGeneral m b of
  Just (l,x) -> all (==b) (unM (transpose (m `mulM` x))) &&
                isSolution m l
  Nothing -> True

\end{code}-}

