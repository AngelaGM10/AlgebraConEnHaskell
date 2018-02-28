\begin{code}
module TAHIntegralDomain
   (module TAHCommutative
   , IntegralDomain
   , propZeroDivisors, propIntegralDomain
   ) where

import Test.QuickCheck
import TAHCommutative
\end{code}
Para iniciar este módulo necesitamos importar el módulo $TAHCommutative$ ya que vamos a definir los dominios de integridad sobre anillos conmutativos, por lo que la clase que vamos a definir parte del tipo $CommutRing$ que como hemos definido antes es el tipo de los anillos conmutativos. Damos su definición.\\

\begin{defi}
Dado un anillo $(A,+,*)$, un elemento $a \in\, A$ se dice que es un divisor de cero si existe $b \in\, A- \{0\}$ tal que $a*b = 0$.
Un anillo A se dice dominio de integridad, si el único divisor de cero es $0$. Es decir, $\forall\,\, a,b\,\in\,R.\,\,\, a*b = 0 \Rightarrow \,\, a = 0 \,\,or\,\, b = 0$
\end{defi}

\begin{code}
-- | Definición de dominio de integridad.
class CommutRing a => IntegralDomain a
-- | Un dominio de integridad es un anillo cuyo único divisor de cero es 0.
propZeroDivisors :: (IntegralDomain a, Eq a) => a -> a -> Bool
propZeroDivisors a b = if a <**> b == zero then
                              a == zero || b == zero else True
\end{code}
Como ocurría con los axiomas de los anillos, la función $propZeroDivisors$ requiere que los elementos que recibe sean de la clase de tipo $IntegralDomain$ y de tipo $Eq$ pues estamos definiendo operaciones en las que se tiene que dar una igualdad, y devuelva un valor booleano, por ello el elemento de salida es de tipo $Bool$.\\

Para determinar si un anillo es un dominio de integridad usaremos la siguiente propiedad, esta tal y como ocurre con las anteriores propiedades, se encarga de comprobar que para cualquier instancia que demos se cumplan los axiomas que tiene que verificar, en este caso, para ser un  dominio de integridad:

\begin{code}
propIntegralDomain :: (IntegralDomain a, Eq a) => a -> a -> a -> Property
propIntegralDomain a b c = if propZeroDivisors a b
                              then propCommutRing a b c 
                              else whenFail (print "propZeroDivisors") False
\end{code}
