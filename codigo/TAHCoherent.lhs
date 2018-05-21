\begin{code}
module TAHCoherent
  ( Coherent(solve)
  , propCoherent, isSolution
  , solveMxN, propSolveMxN
  , solveWithIntersection
  ) where

import Test.QuickCheck

import TAHIntegralDomain
import TAHIdeal
import TAHStronglyDiscrete
import TAHVector
import TAHMatrix


\end{code}
\vspace{3mm}
\begin{defi}
Un anillo R es coherente si dado un vector $\,M \in\, \mathbb{R}^{1\times n}\,$ existe una matriz $\,L \in\,\mathbb{R}^{n\times m}\,$ para $\,m \in\, \mathbb{N}\,$ tal que $\,ML=0\,$ y
\begin{center}
$MX = 0 \Leftrightarrow \exists \,\,Y\, \in\, \mathbb{R}^{m\times 1}\,$ tal que $\, X = LY$
\end{center}
esto es,
\begin{equation*}
\begin{array}{ccc}
\[ \left( \begin{array}{rccc}
    m_1 & m_2 & \cdots & m_n 
   \end{array} \right) \left( \begin{array}{cccc}
       l_{11} & l_{12} & \cdots & l_{1m}\\ 
       l_{21} & l_{22} & \cdots & l_{2m}\\
       \vdots & \vdots & \ddots & \vdots\\
       l_{n1} & l_{n2} & \cdots & l_{nm}
      \end{array} \right) = \left( \begin{array}{rccc}
                             0 & \cdots & 0 
                             \end{array} \right)_{1\times m}  \]\,\,\,\, y\\

\[\left( \begin{array}{rccc}
          m_1 & m_2 & \cdots & m_n
         \end{array} \right)  \left( \begin{array}{c}
                              x_1 \\
                              x_2 \\
                              \vdots \\
                              x_n 
                             \end{array} \right) = 0 \,\,\Leftrightarrow\,\, \exists\,\, 
\left( \begin{array}{c}
        y_1 \\
        y_2 \\
        \vdots \\
        y_m 
\end{array} \right) \,\,\,\, tal\,\, que\] \\
\[ \left( \begin{array}{c}
        x_1 \\
        x_2 \\
        \vdots \\
        x_n 
       \end{array} \right) =  \left( \begin{array}{cccc}
                                     l_{11} & l_{12} & \cdots & l_{1m}\\ 
                                     l_{21} & l_{22} & \cdots & l_{2m}\\
                                     \vdots & \vdots & \ddots & \vdots\\
                                     l_1{n1} & l_{n2} & \cdots & l_{nm}
                                     \end{array} \right)  \left( \begin{array}{c}
                                                                  y_1 \\
                                                                  y_2 \\
                                                                  \vdots \\
                                                                  y_m
                                                                 \end{array} \right)\]

\end{array}
\end{equation}
\end{defi}

De esta forma es posible calcular un conjunto de generadores para soluciones
de ecuaciones en un anillo coherente. En otras palabras, el conjunto de soluciones para $MX = 0$ esta generado finitamente.\\

La propiedad de la coherencia es bastante difícil de implementar
en Haskell. El contenido que se puede implementar es que es posible calcular
la matriz $L$ dada $M$ tal que $ML\, =\, 0$.\\

En esta sección todos los anillos de los que partimos son dominios de integridad, por lo que al construir la clase de los anillos coherentes haremos una restricción a la clase de $IntegralDomain$. Introducimos la clase de anillos coherentes:

\begin{code}
class IntegralDomain a => Coherent a where
  solve :: Vector a -> Matrix a
\end{code}

Al igual que ocurría con $member$ en el anterior capítulo, aquí $solve$ es una función que no tiene una especificación concreta. El objetivo de esta función es comprobar que dado un vector $M$ exista una matriz $L$ que cumpla las condiciones de la definición de anillo coherente. Es decir, $solve$ recibe un vector $M \in\, R^{1\times n}$ y devolverá una matriz $L \in\,\mathbb{R}^{n\times m}$ de forma que al multiplicar ambos el vector resultante sea un vector fila de ceros.\\

Para verificar que una especificación concreta de $solve$ es correcta especificamos unas funciones para realizar dicha comprobación. La función que denotaremos\\
$\,propCoherent\,$ es la encargada de comprobar que la multiplicación de $M$ por $L$ sea nula. Para ello, se ayuda de una segunda función que denotaremos por $isSolution$, esta comprueba que el vector que se obtiene tras la multiplicación de $ML$ es un vector de ceros.

\begin{code}
-- | Test para comprobar que la multiplicación del vector M por la matriz
--   encontrada por solve (la matriz L) sea un vector de ceros.
isSolution :: (CommutRing a, Eq a) => Matrix a -> Matrix a -> Bool
isSolution m sol = all (==zero) (concat (unMVec (m `mulM` sol)))

propCoherent :: (Coherent a, Eq a) => Vector a -> Bool
propCoherent m = isSolution (vectorToMatrix m) (solve m)
\end{code}
\vspace{3mm}

\begin{prop}
En un anillo coherente es posible resolver un sistema $MX = 0$ donde $M\, \in \,\,\mathbb{R}^{r\times n}\,$ y $X\, \in \,\,\mathbb{R}^{n\times 1}\,$. Es decir, 
\begin{equation}
\[ \left( \begin{array}{cccc}
    m_{11} & m_{12} & \cdots & m_{1n}\\ 
    m_{21} & m_{22} & \cdots & m_{2n}\\
    \vdots & \vdots & \ddots & \vdots\\
    m_{r1} & m_{r2} & \cdots & m_{rn}
   \end{array} \right) \left( \begin{array}{c}
                              x_1 \\
                              x_2 \\
                              \vdots \\
                              x_n 
                             \end{array} \right) = \left( \begin{array}{c}
                                                           0 \\
                                                           \vdots \\
                                                           0 
                                                           \end{array} \right)_{r\times 1} \]
\end{equation}
\end{prop}

\begin{dem}
Sean $M_{i}\,\in\,\,\mathbb{R}^{1\times n}\,$, $  M_{i} = \left( \begin{array}{ccc}
                                                        m_{i1} & \cdots & m_{in}
                                                      \end{array} \right)  $ las filas de M.\\ 
Por coherencia es posible resolver $M_1X=0$ y obtener un $L_1\,\in\,\,\mathbb{R}^{n\times p_1}\,$ tal que
\begin{equation*}
\[ \left( \begin{array}{ccc}
            m_{11} & \cdots & m_{1n}
          \end{array} \right)  \left( \begin{array}{c}
                                       x_1 \\
                                       x_2 \\
                                      \vdots \\
                                       x_n 
                                      \end{array} \right) = 0 \,\,\Leftrightarrow\,\, \exists\,\, 
\left( \begin{array}{c}
       y_1 \\
       y_2 \\ 
       \vdots \\
       y_{p_1}
       \end{array} \right)\,\, tal\,\, que \]
\[ \left( \begin{array}{c}
        x_1 \\
        x_2 \\
        \vdots \\
        x_n 
       \end{array} \right) =  \left( \begin{array}{cccc}
                                     {l_1}_{11} & {l_1}_{12} & \cdots & {l_1}_{1p_1}\\ 
                                     {l_1}_{21} & {l_1}_{22} & \cdots & {l_1}_{2p_1}\\
                                     \vdots & \vdots & \ddots & \vdots\\
                                     {l_1}_{n1} & {l_1}_{n2} & \cdots & {l_1}_{np_1}
                                     \end{array} \right) \left( \begin{array}{c}
                                                                 y_1 \\
                                                                 y_2 \\ 
                                                                 \vdots \\
                                                                 y_{p_1}
                                                                 \end{array} \right)\]
\end{equation}
\textit{De esta forma, $M_2X=0$ y como $X=L_1Y  \,\,\Rightarrow\,\, M_2L_1Y=0$.\\
Por coherencia, obtenemos una nueva matriz $L_2\,\in\,\,\mathbb{R}^{p_1\times p_2}\,$ tal que}
\begin{equation*}
M_1X\,=\,M_2X\,=\,0 \,\,\Leftrightarrow\,\,  
\left\{ \begin{array}{ll} 
\exists\,\, Y\,\in\,\,\mathbb{R}^{p_1\times 1}\,\, /\,\, X\,=\,L_1Y\, , \, M_2L_1Y\,=\,0\\
\exists\,\, Z\,\in\,\,\mathbb{R}^{p_2\times 1}\,\, /\,\, X\,=\,L_1L_2Z 
\end{array}
\end{equation}
\textit{Iterando este método la solución $X=L_1L_2\cdots L_rZ\,$ con $\,L_i\,\in\,\,\mathbb{R}^{p_{i-1}\times p_i}\,$, $\,p_0\,=\,n\,$ y $\,Z\,\in\,\,\mathbb{R}^{p_{m}\times 1}\,$ puede ser calculada.}

\end{dem}

La proposición anterior nos muestra la forma de resolver mediante recursión un sistema $MX=0$, veamos como hacerlo en Haskell. Siguiendo la prueba de la proposición anterior, comenzamos a aplicar coherencia con la primera fila de la matriz $M$ y así vamos obteniendo por coherencia una nueva matriz en cada iteración hasta obtener la solución de $X$. Con una segunda función, que denotaremos $propSolveMxN$ comprobaremos que para esta instancia en concreto de solve, la matriz $L$ que ha encontrado verifica la propiedad de $ML=0$.

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


-- |Test para comprobar que esta especificación de solve devuelve
--  un vector de ceros.
propSolveMxN :: (Coherent a, Eq a) => Matrix a -> Bool
propSolveMxN m = isSolution m (solveMxN m)

\end{code}

Ahora consideraremos la intersección de dos ideales finitamente generados en anillos coherentes. Esto proporciona otra forma de caracterizar los anillos coherentes en términos de intersección de ideales.
\vspace{3mm}

\begin{prop}
La intersección de dos ideales finitamente generados en un anillo coherente $R$ está finitamente generada.\\[7pt]
\end{prop}


\begin{dem}
Sean $\,I=<a_1,\cdots,a_n>\,$ y $\,J=<b_1,\cdots,b_m>\,$ dos ideales finitamente generados en $R$. Consideramos el sistema $AX-BY=0$, donde 
$A = \left( \begin{array}{ccc}
      a_1 & \cdots & a_n
    \end{array} \right)$ y $B = \left( \begin{array}{ccc}
                                        b_1 & \cdots & b_m
                                       \end{array} \right)$ son vectores filas.\\[8pt]
Como el anillo es coherente, entonces es posible calcular un número finito de generadores $\,\{(X_1,Y_1), \cdots,(X_p,Y_p)\}\,$ de la solución.\\[8pt]
Esto es,
\begin{equation*}
\begin{array}{ccc}
AX_1=BY_1 \\
\vdots\\
AX_p=BY_p
\end{array}
\end{equation}
Si $\,\alpha \,\in\,\,I\cap J\, \Rightarrow\,\,\alpha \,\in\,\, I\,\, ,\,\,\alpha \,\in\,\, J$. Esto es,
\begin{equation*}
\begin{array}{ccc}
\exists\,\,x_i,y_i\,\, /\,\,\alpha =a_1x_1+\cdots + a_nx_n\,\, , \,\,\alpha =b_1y_1+\cdots + b_my_m\\[10pt]
\Rightarrow\,\, a_1x_1+\cdots + a_nx_n\,=\,b_1y_1+\cdots + b_my_m
\end{array}
\end{equation}
estos son exactamente los generadores dados anteriormente.\\[15pt]
Por tanto, un conjunto de generadores para la intersección es $\,\{AX_1,\cdots ,AX_p\}\,$ y otro conjunto de generadores es $\, \{BY_1,\cdots ,BY_p\}$.
\end{dem}

De hecho, esta afirmación se puede probar en la otra dirección también. La siguiente proposición es la más importante en esta sección y todas las pruebas de coherencia se basarán en esta.
\vspace{3mm}

\begin{prop}
Si $R$ es un dominio de integridad tal que la intersección de dos ideales finitamente generados está finitamente generada, entonces $R$ es coherente.\\[7pt]
\end{prop}

\begin{dem}
Lo probaremos mediante inducción en la longitud del sistema a resolver. Primero consideramos $\,ax=0$. Aquí la solución es trivial. Suponemos cierto que es posible resolver un sistema en 
$\,(n-1)\,$ variables y consideramos el caso con $\,n\,\geq \,2\,$ variables:
\begin{equation*}
a_1x_1+\cdots +a_nx_n=0
\end{equation}
Si $\,a_1=0\,$ un conjunto de soluciones del sistema está generado por $\,(1,0,\cdots ,0)\,$, pero también es posible usar la hipótesis de inducción y obtener los generadores $\,\{ v_{i2},\cdots ,v_{in}\}\,$ para el sistema con $\,x_2,\cdots ,x_n\,$ y las soluciones del sistema con $\,n\,$ incógnitas están generadas por $\, (0,v_{i2},\cdots ,v_{in}) \,$ y $\,(1,0,\cdots ,0)\,$.\\

Si $\,a_1\neq 0\,$ el conjunto $\, (0,v_{i2},\cdots ,v_{in}) \,$ de soluciones puede obtenerse también por hipótesis de inducción. Además, por hipótesis es posible encontrar $\, t_1,\cdots ,t_p\,$ tales que
\begin{equation*}
<a_1>\cap <-a_2,\cdots ,-a_n>\,=\,< t_1,\cdots ,t_p>
\end{equation} 
donde $t_i\,=\,a_1w_{i1}\,=\,-a_2w_{i2}-\cdots -a_nw_{in}$.\\
Luego, si $\,a_1x_1+\cdots +a_nx_n\,=\,0\,\,\,\Rightarrow\,\, 
a_1x_1\,=\,-a_2x_2,\cdots ,-a_nx_n\,$.\\
También tenemos $\,u_i\,$ tal que
\begin{equation*}
a_1x_1\,=\,-a_2x_2,\cdots ,-a_nx_n\,=\,\sum^p_{i=1} u_it_i
\end{equation} 
Por tanto se tiene que 
\begin{equation*}
a_1x_1\,=\,\sum^p_{i=1} u_it_i\,=\,\sum^p_{i=1} u_ia_1w_{i1} \,\,\Rightarrow\,\, x_1\,=\,\sum^p_{i=1} u_iw_{i1}
\end{equation} 
De forma análoga,
\begin{equation*}
-a_2x_2,\cdots ,-a_nx_n\,=\,\sum^p_{i=1} u_it_i\,=\,\sum^p_{i=1} u_i(-a_2w_{i2}-\cdots -a_nw_{in})
\end{equation} 
Reorganizando nos queda
\begin{equation*}
a_2(x_2 - \sum^p_{i=1} u_iw_{i2} ) + \cdots + a_n(x_n - \sum^p_{i=1} u_iw_{in} ) = 0
\end{equation} 
Luego, obtenemos $\,(w_{i1},\cdots ,w_{in})\,$ y $\, (0,v_{i2},\cdots ,v_{in}) \,$ que generan el módulo de la solución.
\end{dem}

Esto proporciona un método para probar que los anillos son coherentes. Ahora vamos a ver como calcular la intersección de los ideales finitamente generados. Esto implicará que el anillo es coherente. También muestra que la coherencia de
los anillos se puede caracterizar solo en términos de la intersección finita de
ideales finitamente generados.


Algo que vale la pena enfatizar aquí es la dependencia de los coeficientes de la intersección. Estos se obtienen de dos ideales finitamente generados $\,I=<x_1,\cdots ,x_n>\,$ y $\,J=<y_1,\cdots ,y_m>\,$ las funciones que calculan la intersección también deben dar un conjunto de coeficientes. Si la intersección $\,I\cap J\,=\,<z_1,\cdots ,z_l>\,$ entonces la función debe dar $\,u_{ij}\,$ y $\,v_{ij}\,$ tales que
\begin{equation*}
\begin{array}{lcc}
z_k\,=\,u_{k1}x_1+ \cdots +u_{kn}x_n\\
\hspace{15pt} =\,v_{k1}y_1+ \cdots +v_{km}y_m
\end{array}
\end{equation}
Nótese que solo devuelve los coeficientes en una dirección, es decir, si $\,x\,\in\,I\cap J\,$ entonces $\,x\,\in\,I\,$ y $\,x\,\in\,J\,$.\\

Vamos a dar un algoritmo para obtener una solución del sistema mediante la intersección, basándonos en las propocisiones anteriores.

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
    | x == zero =
       (one:replicate (length xs) zero):(map (zero:) $ solveInt xs)
    | isSameIdeal int as bs = s ++ m'
    | otherwise = error "solveInt: No se puede calcular la intersección"
      where
      as = Id [x]
      bs = Id (map neg xs)

      -- Calculamos al intersección de <x1> y <-x2,...,-xn>
      (Id ts,us,vs) = as `int` bs
      s  = [ u ++ v | (u,v) <- zip us vs ]

      -- Resuelve <0,x2,...,xn> recursivamente
      m  = solveInt xs
      m' = map (zero:) m

\end{code}



