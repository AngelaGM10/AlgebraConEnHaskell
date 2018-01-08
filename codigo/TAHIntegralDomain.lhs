\begin{code}
module TAHIntegralDomain
   (module TAHCommutative
   , IntegralDomain
   , propZeroDivisors, propIntegralDomain
   ) where

import Test.QuickCheck
import TAH
import TAHCommutative
\end{code}

\begin{defi}
Dado un anillo $A$, un elemento $a \in\, A$ se dice que es un divisor de cero si existe $b \in\, A- \{0\}$ tal que $a*b = 0$.
Un anillo A se dice dominio de integridad, si el único divisor de cero es $0$.\\
$\forall\,\, a,b\,\in\,R.\,\,\, a*b = 0 \Rigtharrow \,\, a = 0 \,\,or\,\, b = 0$
\end{defi}
\begin{code}
-- | Definición de dominios integrales.
class CommutRing a => IntegralDomain a
-- | Un dominio integral es un anillo que
propZeroDivisors :: (IntegralDomain a, Eq a) => a -> a -> Bool
propZeroDivisors a b = if a <**> b == zero then
                              a == zero || b == zero else True
\end{code}

Para saber si un anillo es un dominio de integridad usaremos la siguiente función:

\begin{code}
propIntegralDomain :: (IntegralDomain a, Eq a) => a -> a -> a -> Property
propIntegralDomain a b c = if propZeroDivisors a b
                              then propCommutRing a b c 
                              else whenFail (print "propZeroDivisors") False
\end{code}
