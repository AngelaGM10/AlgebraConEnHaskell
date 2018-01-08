\begin{code}
module TAHCuerpo
  ( module TAHIntegralDomain
  , Field(inv)
  , propMulInv, propField
  , (</>)
  ) where

import Test.QuickCheck

import TAH
import TAHIntegralDomain
\end{code}

\begin{defi}
Un cuerpo es un anillo conmutativo con elemento unidad tal $(A- \{0\})$ también es un grupo abeliano, es decir, cumple las 4 primeras propiedades de un anillo.
\end{defi}
\begin{code}
-- | Definición de cuerpo.
class IntegralDomain a => Field a where
  inv :: a -> a
propMulInv :: (Field a, Eq a) => a -> Bool
propMulInv a = a == zero || inv a <**> a == one
\end{code}

Para saber si un anillo conmutativo es un cuerpo usaremos la función:
\begin{code}
propField :: (Field a, Eq a) => a -> a -> a -> Property
propField a b c = if propMulInv a
                     then propIntegralDomain a b c 
                     else whenFail (print "propMulInv") False
\end{code}

Los cuerpos poseen otras operaciones además de las que un anillo conmutativo pueda tener, como es la división. Para poder dar dicha definición establecemos el orden de prioridad para el símbolo de la división.

\begin{code}
infixl 7 </>

-- | División
(</>) :: Field a => a -> a -> a
x </> y = x <**> inv y
\end{code}
