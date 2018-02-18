\begin{code}
module TAHField
  ( module TAHIntegralDomain
  , Field(inv)
  , propMulInv, propField
  , (</>)
  ) where

import Test.QuickCheck
import TAHIntegralDomain 

\end{code}
Para poder implementar la noción de cuerpo, necesitamos importar el módulo anterior $TAHIntegralDomain$, pues si una terna $(A,+,*)$ es un cuerpo por consiguiente es dominio de integridad, y al definir la clase de cuerpo le imponemos la restricción de que sea un dominio de integridad, veamos la definición teórica de cuerpo. \\

\begin{defi}
Un cuerpo es un anillo de división conmutativo, es decir, un anillo conmutativo y unitario en el que todo elemento distinto de cero es invertible respecto del producto. Otra forma de definirlo es la siguiente, un cuerpo R es un dominio de integridad tal que para cada elemento $a \neq\, 0$, existe un inverso $a^{-1}$ que verifica la igualdad: $a^{-1}a = 1$.​ 
\end{defi}

Esta segunda definición es la que usaremos para la implementación, por ser más constructiva. La primera definición es la más común a nivel de teoría algebraica, y para aquellos familiarizados con conceptos básicos de álgebra, conocen la definición de cuerpo como la primera que hemos dado.\\ 

En Haskell especificamos el inverso de cada elemento mediante la función $inv$. La función $propMulInv$ esta restringida a la clase de tipo $Field$ pues requerimos que sea cuerpo y al tipo $Eq$ pues se tiene que dar la igualdad.

\begin{code}
-- | Definición de cuerpo.
class IntegralDomain a => Field a where
  inv :: a -> a
-- | Propiedad de los inversos.
propMulInv :: (Field a, Eq a) => a -> Bool
propMulInv a = a == zero || inv a <**> a == one
\end{code}

Especificamos la propiedad que han de verificar los ejemplos de cuerpos. Es decir, dada una terna $(A,+,*)$ para una instancia concreta, esta tiene que verificar los axiomas para ser un cuerpo.

\begin{code}
propField :: (Field a, Eq a) => a -> a -> a -> Property
propField a b c = if propMulInv a
                     then propIntegralDomain a b c 
                     else whenFail (print "propMulInv") False
\end{code}

En un cuerpo se puede definir la división. Para poder dar dicha definición establecemos el orden de prioridad para el símbolo de la división.

\begin{code}
infixl 7 </>

-- | División
(</>) :: Field a => a -> a -> a
x </> y = x <**> inv y
\end{code}