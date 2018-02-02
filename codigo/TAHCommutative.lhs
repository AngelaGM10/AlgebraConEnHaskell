\begin{code}
module TAHCommutative
   (module TAH
   , CommutRing(..)
   , propMulComm, propCommutRing
   ) where

import Test.QuickCheck
import TAH
\end{code}

En este módulo introducimos el concepto de anillo conmutativo, que visto desde el punto de vista de la programación funcional, es una subclase de la clase $Ring$. Solo necesitaremos una función para definirlo, damos primero su definición teórica.\\

\begin{defi}
Un anillo conmutativo es un anillo $(R, +, *)$ en el que la operación de multiplicación $*$ es conmutativa, es decir,
 $\,\,\,\forall\,\, a,b\,\in\,R.\,\,\, a*b = b*a$\\
\end{defi}


\begin{code}
class Ring a => CommutRing a
propMulComm :: (CommutRing a, Eq a) => a -> a -> Bool
propMulComm a b = a <**> b == b <**> a
\end{code}

Para saber si un anillo es commutativo se necesita una función que verifique la propiedad:
\begin{code}
-- | Test que comprueba si un anillo es commutativo.
propCommutRing :: (CommutRing a, Eq a) => a -> a -> a -> Property
propCommutRing a b c = if propMulComm a b 
                               then propRing a b c 
                               else whenFail (print "propMulComm") False
\end{code}
