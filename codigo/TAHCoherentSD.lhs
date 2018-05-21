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

Para decidir si un elemento pertenece a un ideal, hay un método constructivo. Si $\,x\,\in\,<x_1,\cdots ,x_n>\,$ también debería de dar los coeficientes, pues si $\,x\,$ pertenece a un ideal entonces este se puede escribir como combinación lineal de los generadores del ideal, sean $\,w_i\,$ los coeficientes de estos generadores. Entonces, podemos escribir $\,x\,$ como combinación lineal, $\,x = \sum_i w_ix_i\,$.\\

\begin{prop}
Si $R$ es un dominio de integridad fuertemente discreto y coherente entonces es posible resolver sistemas lineales arbitrarios. Dado $\,MX=A\,$ es posible calcular $\,X_0\,$ y $\,L\,$ tal que $\,ML=0\,$ y 
\begin{equation*}
MX=A\,\, \Leftrightarrow \,\,\exists\,\,Y\,\,/\,\,X=LY+X_0
\end{equation} 
\end{prop}

\begin{dem}
Por coherencia, podemos calcular la matriz $\,L\,$ del sistema $\,MX=0\,$ mediante la proposición 1. La solución particular $\,X_0\,$ puede calcularse utilizando el mismo método. \\

El caso base es cuando $\,M\,$ solo tiene una fila, aquí es trivial ya que $R$ es fuertemente discreto.Esto es, si $\,M=(x_1,\cdots ,x_n)\,$ y $\,A = (a)\,$ entonces decidir si pertenece al ideal o no, se verifica si $\,a\,\in\,<x_1,\cdots ,x_n> entonces se tiene que obtener los coeficientes $\,w_i\,$ tales que $\,a=x_1w_1 + \cdots + x_nw_n\,$.
\end{dem}

Mediante la función que denotaremos $\,solveGeneralEquation\,$ obtendremos el primer paso para calcular la solución de un sistema del tipo $\,AX=b\,$, partiendo de que estamos en un anillo fuertemente discreto. Esta función recibe el vector $\,v\,$ y la solución $\,b\,$. Aplicamos $\,solve\,$ sobre dicho vector para encontrar la matriz $\,L\,$ para verificar que se trata de un anillo coherente. Después con $\,member\,$ se generará la lista de coeficientes de la combinación lineal. Finalmente se suman ambas.

\begin{code}
solveGeneralEquation :: (Coherent a, StronglyDiscrete a) =>
                        Vector a -> a -> Maybe (Matrix a)
solveGeneralEquation v@(Vec xs) b =
  let sol = solve v  -- obtenemos la matriz L
  in case b `member` (Id xs) of
    Just as -> Just $ transpose
       (M (replicate (length (head (unMVec sol))) (Vec as)))
       `addM` sol
        -- Suma a L a los coeficientes de la comb. lineal de b
    Nothing -> Nothing


-- | Comprueba que al multiplicar el vector v por la
--   matriz generada por solve se obtiene el vector b
propSolveGeneralEquation :: (Coherent a, StronglyDiscrete a, Eq a)
                         => Vector a
                         -> a
                         -> Bool
propSolveGeneralEquation v b = case solveGeneralEquation v b of
  Just sol -> all (==b) $ concat $ unMVec $ vectorToMatrix v `mulM` sol
  Nothing  -> True
\end{code}


Con la siguiente función comprobaremos si la matriz solución obtenida con $\,solve\,$ ($sol$) es correcta. Para ello comprobaremos que al realizar la multiplicación del vector $\,v\,$ por la matriz obtenida con $\,solve\,$ coincide componente a componente con el vector solución $b$.

\begin{code}
isSolutionB v sol b =
  all (==b) $ concat $ unMVec $ vectorToMatrix v `mulM` sol
\end{code}

Ahora vamos a resolver sistemas lineales generales de la forma $AX = b$.

\begin{code}
solveGeneral :: (Coherent a, StronglyDiscrete a, Eq a)
             => Matrix a   -- A
             -> Vector a   -- b
             -> Maybe (Matrix a, Matrix a)  -- (L,X0)
solveGeneral (M (l:ls)) (Vec (a:as)) =
  case solveGeneral' (solveGeneralEquation l a) ls as [(l,a)] of
    Just x0 -> Just (solveMxN (M (l:ls)), x0)
    Nothing -> Nothing
  where
  -- Calculamos una nueva solución de forma inductiva y verificamos
  -- que la nueva solución satisface todas las ecuaciones anteriores.
  solveGeneral' Nothing _ _ _              = Nothing
  solveGeneral' (Just m) [] [] old         = Just m
  solveGeneral' (Just m) (l:ls) (a:as) old =
    if isSolutionB l m a
       then solveGeneral' (Just m) ls as old
       else case solveGeneralEquation (matrixToVector
                 (vectorToMatrix l `mulM` m)) a of
         Just m' -> let m'' = m `mulM` m'
                    in if all (\(x,y) -> isSolutionB x m'' y) old
                          then solveGeneral' (Just m'') ls as ((l,a):old)
                          else Nothing
         Nothing -> Nothing
  solveGeneral' _ _ _ _ = error "solveGeneral: Error en la entrada"
\end{code}

Finalmente, con la siguiente propiedad comprobaremos que la solución es correcta. Primero tenemos que comprobar que las filas de $\,A\,$ (se representará en código por $\,m\,$) son de la misma longitud que $\,b\,$. Después, multiplicamos la matriz $\,A\,$ con la matriz solución $\,X\,$ y vemos si coincide componente a componente con el vector $b$.

\begin{code}
propSolveGeneral :: (Coherent a, StronglyDiscrete a, Eq a) =>
                    Matrix a -> Vector a -> Property
propSolveGeneral m b = length (unM m) == length (unVec b) ==>
  case solveGeneral m b of
   Just (l,x) -> all (==b) (unM (transpose (m `mulM` x))) &&
                isSolution m l
   Nothing -> True

\end{code}

