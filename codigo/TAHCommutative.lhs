\begin{code}
module TAHCommutative
   (module TAH
   , CommutRing(..)
   , propMulComm, propCommutRing
   ) where

import Test.QuickCheck
import TAH
\end{code}

En este módulo introducimos el concepto de anillo conmutativo. Aquí hemos importado el módulo $TAH$ con el comando $import$, para poder usar las clases y funciones definidas en dicho módulo. Vito desde el punto de vista de la programación funcional,un anillo conmutativo es una subclase de la clase $Ring$. Solo necesitaremos una función para definirlo. Damos primero su definición teórica.\\

\begin{defi}
Un anillo conmutativo es un anillo $(R, +, *)$ en el que la operación de multiplicación $*$ es conmutativa, es decir,
 $\,\,\,\forall\,\, a,b\,\in\,R.\,\,\, a*b = b*a$\\
\end{defi}


\begin{code}
class Ring a => CommutRing a
propMulComm :: (CommutRing a, Eq a) => a -> a -> Bool
propMulComm a b = a <**> b == b <**> a
\end{code}

Para saber si un anillo es commutativo crearemos una propiedad que compruebe, en cada caso particular, que las operaciones concretas de una instancia verifique los axiomas para ser un anillo conmutativo y por consiguiente un anillo :
\begin{code}
-- | Test que comprueba si un anillo es commutativo.
propCommutRing :: (CommutRing a, Eq a) => a -> a -> a -> Property
propCommutRing a b c = if propMulComm a b 
                               then propRing a b c 
                               else whenFail (print "propMulComm") False
\end{code}
