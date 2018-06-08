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

Al estar en un anillo fuertemente discreto, la pertenencia al ideal es decidible de forma constructiva. Por lo que, si $\,x\,\in\,<x_1,\cdots ,x_n>\,$ entonces existen unos coeficientes  $\,w_i\,$ de forma que $\,x\,$ puede escribir como combinación lineal de los generadores del ideal. Entonces, podemos escribir $\,x\,$ como $\,x = \sum_i w_ix_i\,$.\\

\begin{prop}
Si $R$ es un dominio de integridad fuertemente discreto y coherente entonces es posible resolver sistemas lineales arbitrarios. Dado $\,M\vec{X}=\vec{b}\,$ es posible calcular $\,\vec{X_0}\,$ y $\,L\,$ tal que $\,ML=\vec{0}\,$ y 
\begin{equation*}
M\vec{X}=\vec{b}\,\, \Leftrightarrow \,\,\exists\,\,\vec{Y}\,\,/\,\,\vec{X}=L\vec{Y}+\vec{X_0}
\end{equation} 
\end{prop}

\begin{dem}
Por coherencia, podemos calcular la matriz $\,L\,$ del sistema $\,M\vec{X}=\vec{0}\,$ mediante la proposición 1. La solución particular $\,\vec{X_0}\,$ puede calcularse utilizando el siguiente método que utilizaremos para encontrar la solución de $\,\vec{X}\,$: \\

El caso base es cuando $\,M\,$ solo tiene una fila, la denotamos $\,\vec{m}\,$. Aquí es trivial ya que $R$ es fuertemente discreto. Esto es, si $\,\vec{m}=(m_1,\cdots ,m_n)\,$ y $\,\vec{b} = (b)\,$ entonces resolver $\,\vec{m}X=(b)\,$ es decidir si $\,(b)\,$ pertenece al ideal $\,<m_1,\cdots ,m_n>\,$ o no.\\
Si $\,b\,\in\,<m_1,\cdots ,m_n>\,$ entonces se tiene que obtener los coeficientes $\,w_i\,$ tales que\\
$b=m_1w_1 + \cdots + m_nw_n\,$. Por tanto, $\,(w_1,\cdots ,w_n)\,$ es solución.
\end{dem}

Mediante la función que denotaremos $\,solveGeneralEquation\,$ obtendremos el primer paso para calcular la solución de un sistema del tipo $\,M\vec{X}=\vec{b}\,$, partiendo de que estamos en un anillo fuertemente discreto. Esta función recibe el vector $\,v\,$ y la solución $\,b\,$. Aplicamos $\,solve\,$ sobre dicho vector para encontrar la matriz $\,L\,$ para verificar que se trata de un anillo coherente. Después con $\,member\,$ se generará la lista de coeficientes de la combinación lineal. Finalmente se suman ambas.
\index{\texttt{solveGeneralEquation}}
\index{\texttt{isSolutionB}}
\index{\texttt{propSolveGeneralEquation}}
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

 
isSolutionB :: (CommutRing a, Eq a) => Vector a -> Matrix a -> a -> Bool
isSolutionB v sol b =
  all (==b) $ concat $ unMVec $ vectorToMatrix v `mulM` sol


-- | Comprueba que al multiplicar el vector v por la
--   matriz generada por solveGeneralEquation se obtiene el vector b
propSolveGeneralEquation :: (Coherent a, StronglyDiscrete a, Eq a)
                         => Vector a
                         -> a
                         -> Bool
propSolveGeneralEquation v b = case solveGeneralEquation v b of
  Just sol -> isSolutionB v sol b
  Nothing  -> True
\end{code}

La función $\,isSolutionB\,$ es similar a $\,isSolution\,$. Ambas tienen el mismo objetivo, comprobar que la solución del sistema obtenida es correcta. Solo que una es para sistemas no homogéneos y la otra es para sistemas homogéneos, respectivamente.\\

Ahora vamos a resolver sistemas lineales generales de la forma $\,M\vec{X}=\vec{b}\,$.
\index{\texttt{solveGeneral}}
\begin{code}
solveGeneral :: (Coherent a, StronglyDiscrete a, Eq a)
             => Matrix a   -- M
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

Las dos funciones anteriores, $\,solveGeneralEquation\,$ y $\,solveGeneral\,$ también son similares. La diferencia es que $\,solveGeneralEquation\,$ resuelve un sistema de la forma $\,\vec{m}\vec{X}=(b)\,$, es decir, para el caso en el que $M$ es un vector y no una matriz. Mientras que $\,solveGeneral\,$ nos permite calcular la solución de un sistema $M\vec{X} = \vec{b}$ donde M es una matriz. Ambas funciones están basadas en la proposición 4, solo que cada una es un caso de la prueba 4.\\

La función $\,solveGeneral\,$ consiste en obtener el sistema de generadores de la solución. Para ello con $\,solveGeneralEquation\,$ conseguimos un generador de la solución, a partir del cuál se comprueba que sea un generador para todas las ecuaciones del sistema.\\

Finalmente, con la siguiente propiedad comprobaremos que la solución es correcta. Primero tenemos que comprobar que las filas de $\,M\,$ son de la misma longitud que $\,\vec{b}\,$. Después, multiplicamos la matriz $\,M\,$ con la matriz solución y vemos si coincide componente a componente con el vector $\,\vec{b}\,$.
\index{\texttt{propSolveGeneral}}
\begin{code}
propSolveGeneral :: (Coherent a, StronglyDiscrete a, Eq a) =>
                    Matrix a -> Vector a -> Property
propSolveGeneral m b = length (unM m) == length (unVec b) ==>
  case solveGeneral m b of
   Just (l,x) -> all (==b) (unM (transpose (m `mulM` x))) &&
                isSolution m l
   Nothing -> True

\end{code}

