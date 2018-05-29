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
Un anillo R es coherente si dado un vector $\,\vec{m} \in\, R^{1\times n}\,$ existe una matriz $\,L \in\,R^{n\times r}\,$ para $\,r \in\, \mathbb{N}\,$ tal que $\,ML=\vec{0}\,$ y
\begin{center}
$MX = 0 \Leftrightarrow \exists \,\,Y\, \in\, R^{r\times 1}\,$ tal que $\, X = LY$
\end{center}
esto es,
\begin{equation*}
\begin{array}{ccc}
\[ \left( \begin{array}{rccc}
    m_1 & m_2 & \cdots & m_n 
   \end{array} \right) \left( \begin{array}{cccc}
       l_{11} & l_{12} & \cdots & l_{1r}\\ 
       l_{21} & l_{22} & \cdots & l_{2r}\\
       \vdots & \vdots & \ddots & \vdots\\
       l_{n1} & l_{n2} & \cdots & l_{nr}
      \end{array} \right) = \left( \begin{array}{rccc}
                             0 & \cdots & 0 
                             \end{array} \right)_{1\times r}  \]\,\,\,\, y\\

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
        y_r 
\end{array} \right) \,\,\,\, tal\,\, que\] \\
\[ \left( \begin{array}{c}
        x_1 \\
        x_2 \\
        \vdots \\
        x_n 
       \end{array} \right) =  \left( \begin{array}{cccc}
                                     l_{11} & l_{12} & \cdots & l_{1r}\\ 
                                     l_{21} & l_{22} & \cdots & l_{2r}\\
                                     \vdots & \vdots & \ddots & \vdots\\
                                     l_1{n1} & l_{n2} & \cdots & l_{nr}
                                     \end{array} \right)  \left( \begin{array}{c}
                                                                  y_1 \\
                                                                  y_2 \\
                                                                  \vdots \\
                                                                  y_r
                                                                 \end{array} \right)\]

\end{array}
\end{equation}
\end{defi}

De esta forma es posible calcular las soluciones de un sistema de ecuaciones en un anillo coherente. El vector $\,\vec{m}\,$ es solución del sistema homogéneo y la matriz $\,L\,$ nos proporciona un conjunto de generadores finito de las soluciones del sistema. De esta forma, podemos obtener todas las posibles soluciones del sistema.\\

La propiedad de la coherencia es bastante difícil de implementar
en Haskell. El contenido que se puede implementar es que es posible calcular
la matriz $\,L\,$ dada $\,\vec{m}\,$ tal que $\,\vec{m}L\, =\, 0$.\\

En esta sección todos los anillos de los que partimos son dominios de integridad, por lo que al construir la clase de los anillos coherentes haremos una restricción a la clase de $IntegralDomain$. Introducimos la clase de anillos coherentes:

\begin{code}
class IntegralDomain a => Coherent a where
  solve :: Vector a -> Matrix a
\end{code}

Al igual que ocurría con $member$ en el anterior capítulo, aquí $solve$ es una función que no tiene una definición concreta. El objetivo de esta función es que dado un vector $\,\vec{m}\,\in\,R^n$ devuelva una matriz $L \in\,R^{n\times r}$ de forma que al multiplicar ambos el vector resultante sea un vector fila de ceros.\\

Para verificar que una definición concreta de $solve$ es correcta especificamos unas funciones para realizar dicha comprobación. La función que denotaremos\\
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
Empezaremos por resolver sistemas de ecuaciones homogéneos sobre un anillo coherente. Nuestro objetivo es encontrar todas las posibles soluciones del sistema homogéneo, solo que esta vez tenemos una matriz $\,M\,$ y no un vector.

\begin{prop}
En un anillo coherente $\,R\,$ es posible resolver un sistema $MX = \vec{0}$ donde $M\, \in \,\,R^{r\times n}\,$ y $X\, \in \,\,R^{n\times 1}\,$. Es decir, 
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
Sean $\vec{m_{i}}\,\in\,\,R^n\,$, $  \vec{m_{i}} = \left( \begin{array}{ccc}
                                                        m_{i1} & \cdots & m_{in}
                                                      \end{array} \right)  $ las filas de M.\\ 
Por coherencia es posible resolver $\vec{m_{1}}X=0$ y obtener un $L_1\,\in\,\,R^{n\times p_1}\,$ tal que
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
                                     {l_1}_{(11)} & {l_1}_{(12)} & \cdots & {l_1}_{(1p_1)}\\ 
                                     {l_1}_{(21)} & {l_1}_{(22)} & \cdots & {l_1}_{(2p_1)}\\
                                     \vdots & \vdots & \ddots & \vdots\\
                                     {l_1}_{(n1)} & {l_1}_{(n2)} & \cdots & {l_1}_{(np_1)}
                                     \end{array} \right) \left( \begin{array}{c}
                                                                 y_1 \\
                                                                 y_2 \\ 
                                                                 \vdots \\
                                                                 y_{p_1}
                                                                 \end{array} \right)\]
\end{equation}
\textit{Si imponemos, $\, \vec{m_{2}}X=0\,$ , como $\,X=L_1Y  \,\,\Rightarrow\,\,  \vec{m_{2}}L_1Y=0\,$.\\
Por coherencia sobre $\,Y\,$ se tiene que $ \vec{m_{2}}L_1Y=0\,\,\Leftrightarrow\,\,\exists\,\,Z\,\in\,\,R^{p_2\times 1}\,$ tal que $\,Y=L_2Z\,$ obtenemos la nueva matriz $L_2\,\in\,\,R^{p_1\times p_2}\,$.}\\
\vspace{15pt}
\textit{Por tanto, nos queda que}
\begin{equation*}
\left\{ \begin{array}{ll}
X=L_1_{(n\times p_1)}Y_{(p_1\times 1)} \\
Y={L_2}_{(p_1\times p_2)}Z_{(p_2\times 1)}
\end{array} \Rightarrow\,\,X={L_1}_{(n\times p_1)}{L_2}_{(p_1\times p_2)}Z_{(p_2\times 1)} 
\end{equation}
\textit{Iterando este método la solución $X=L_1L_2\cdots L_rZ\,$ con $\,L_i\,\in\,\,R^{p_{i-1}\times p_i}\,$, $\,p_0\,=\,n\,$ y $\,Z\,\in\,\,R^{p_{m}\times 1}\,$ puede ser calculada.}

\end{dem}

La proposición anterior nos muestra la forma de resolver mediante recursión un sistema $\,MX=\vec{0}\,$, veamos como hacerlo en Haskell. Siguiendo la prueba de la proposición anterior, comenzamos a aplicar coherencia con la primera fila de la matriz $\,M\,$ y así vamos obteniendo por coherencia una nueva matriz en cada iteración hasta obtener la solución del sistema de ecuaciones. Mediante la función $\,solveMxN\,$ calcula la matriz obtenida por recursión $\,L_1L_2\cdots L_r\,$. Con una segunda función, que denotaremos $propSolveMxN$ comprobaremos que la matriz obtenida por $\,solveMxN\,$ al multiplicarla por la matriz dada $\,M\,$ es solución del sistema homogéneo es decir el resultado de la multiplicación esun vector de ceros.

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

Ahora consideraremos la intersección de dos ideales finitamente generados en un anillo coherente. Esto es necesario para poder resolver más adelante sistemas utilizando la intersección entre ideales.
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

La proposición anterior también se puede probar en la otra dirección. A continuación daremos una proposición importante en la teoría de anillos coherentes, con ella podemos probar si un anillo $R$ es coherente.
\vspace{3mm}

\begin{prop}
Si $R$ es un dominio de integridad tal que la intersección de dos ideales finitamente generados está finitamente generada, entonces $R$ es coherente.\\[7pt]
\end{prop}

\begin{dem}
Lo probaremos mediante inducción en la longitud del sistema a resolver. Primero consideramos $\,ax=0$. Aquí la solución es trivial, pues R es un dominio de integridad, por lo que $\,a\neq 0\,$, por tanto se tiene que $\,x=0\,$. Suponemos cierto que es posible resolver un sistema en 
$\,(n-1)\,$ variables y consideramos el caso con $\,n\,\geq \,2\,$ variables:
\begin{equation*}
a_1x_1+\cdots +a_nx_n=0
\end{equation}
Si $\,a_1=0\,$ un conjunto de soluciones del sistema está generado por $\,(1,0,\cdots ,0)\,$, pero también es posible usar la hipótesis de inducción y obtener los generadores $\,\{v_{i2},\cdots ,v_{in}\}\,$ para el sistema con $\,x_2,\cdots ,x_n\,$ y las soluciones del sistema con $\,n\,$ incógnitas están generadas por $\,(0,v_{12},\cdots ,v_{1n}),\cdots ,(0,v_{s2},\cdots ,v_{sn}) \,$ y $\,(1,0,\cdots ,0)\,$.\\

Si $\,a_1\neq 0\,$ el conjunto de generadores $\,(0,v_{12},\cdots ,v_{1n}),\cdots ,(0,v_{s2},\cdots ,v_{sn})\,$ de las soluciones puede obtenerse también por hipótesis de inducción. Además, por hipótesis es posible encontrar $\, t_1,\cdots ,t_p\,$ tales que
\begin{equation*}
<a_1>\cap <-a_2,\cdots ,-a_n>\,=\,< t_1,\cdots ,t_p>
\end{equation} 
donde $t_i\,=\,a_1w_{i1}\,=\,-a_2w_{i2}-\cdots -a_nw_{in}$.\\
\begin{equation*}
Si\,\,\,x_1,\cdots ,x_n\,\,\,\textrm{es solución}\,\,\,\Rightarrow\,\,
\left\{ \begin{array}{lll}
a_1x_1+\cdots +a_nx_n\,=\,0\,\,\,\Rightarrow\,\, 
a_1x_1\,=\,-a_2x_2-\cdots -a_nx_n\,\,\Rightarrow\,\,\\
a_1x_1\,\,\in\,\,< t_1,\cdots ,t_p>\,\,\,\,y\\
-a_2x_2-\cdots -a_nx_n\,\,\in\,\,< t_1,\cdots ,t_p>
\end{array}
\end{equation}
Por lo que existen unos $\,u_i\,$ tales que
\begin{equation*}
a_1x_1\,=\,-a_2x_2,\cdots ,-a_nx_n\,=\,\sum^p_{i=1} u_it_i
\end{equation} 
Por tanto se tiene que 
\begin{equation*}
a_1x_1\,=\,\sum^p_{i=1} u_it_i\,=\,\sum^p_{i=1} u_ia_1w_{i1} \,\,\Rightarrow\,\, x_1\,=\,\sum^p_{i=1} u_iw_{i1}
\end{equation} 
Esta implicación podemos hacerla ya que $\,a\neq 0\,$ y $\,R\,$ es dominio de integridad.
De forma análoga,
\begin{equation*}
-a_2x_2-\cdots -a_nx_n\,=\,\sum^p_{i=1} u_it_i\,=\,\sum^p_{i=1} u_i(-a_2w_{i2}-\cdots -a_nw_{in})
\end{equation} 
Reorganizando nos queda
\begin{equation*}
\begin{array}{llll}
a_2(x_2 - \sum^p_{i=1} u_iw_{i2} ) + \cdots + a_n(x_n - \sum^p_{i=1} u_iw_{in} ) = 0\,\,\Rightarrow\\[12pt]
\(x_2-\sum^p_{i=1}u_iw_{i2},\cdots ,x_n-\sum^p_{i=1}u_iw_{in}\) \,\,\,\textrm{es combinación lineal de}\\[12pt]
(0,v_{12},\cdots ,v_{1n}),\cdots ,(0,v_{s2},\cdots ,v_{sn})\,\,\,  \textrm{que recordamos que son los generadores}\\[12pt]
\textrm{de las soluciones de}\,\,\, a_2x_2+\cdots + a_nx_n=0
\end{array}
\end{equation} 
Existen unos coeficientes $\,\alpha_i\,$ con $i = 1,\cdots ,s$ tales que
\begin{equation*}
\begin{array}{cccc}
x_1 = \sum^p_{i=1} u_iw_{i1}\\[12pt]
x_2 = \sum^p_{i=1} u_iw_{i2} + \alpha_1v_{12}+\cdots +\alpha_sv_{s2}\\[12pt]
\vdots \\[12pt]
x_n = \sum^p_{i=1} u_iw_{in} + \alpha_1v_{1n}+\cdots +\alpha_sv_{sn}\\
\end{array}
\end{equation}
Esto es,
\begin{equation*}
\[ \left( \begin{array}{c}
   x_1 \\
   x_2 \\
   \vdots \\
   x_n 
   \end{array} \right) = u_1\left( \begin{array}{c}
                                   w_11 \\
                                   w_12 \\
                                   \vdots \\
                                   w_1n 
                                   \end{array} \right)+\cdots +u_p\left( \begin{array}{c}
                                   w_p1 \\
                                   w_p2 \\
                                   \vdots \\
                                   w_pn 
                                   \end{array} \right)+\alpha_1\left( \begin{array}{c}
                                   0\\
                                   v_12 \\
                                   \vdots \\
                                   v_1n 
                                   \end{array} \right)+\cdots +\alpha_s\left( \begin{array}{c}
                                   0\\
                                   v_s2 \\
                                   \vdots \\
                                   v_sn 
                                   \end{array} \right)
\end{equation}
Luego, obtenemos $\,(w_{11},\cdots ,w_{1n}),\cdots ,(w_{r1},\cdots ,w_{rn})\,$ y $\, \,(0,v_{12},\cdots ,v_{1n}),\cdots ,(0,v_{s2},\cdots ,v_{sn}) \, \,$ que generan el conjunto de las solución.
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



