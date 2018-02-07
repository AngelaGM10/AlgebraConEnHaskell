\begin{code}
module TAH
   ( Ring(..)
   , propAddAssoc, propAddIdentity, propAddInv, propAddComm
   , propMulAssoc, propMulIdentity, propRightDist, propLeftDist
   , propRing
   , (<->)
   , sumRing, productRing
   , (<^>), (~~), (<**)
   ) where

import Data.List
import Test.QuickCheck
\end{code}

En esta sección, que corresponde con el fichero TAH.lhs, introducimos
los conceptos básicos de la Teoría de Anillos. El objetivo es definir
los conceptos mediante programación funcional y teoría de tipos.

En primer lugar, damos la definición teórica de anillos:\\

\begin{defi}
Un anillo es una terna $(R,+,*)$, donde $R$ es un conjunto y $+,*$ son
dos operaciones binarias $+,*:R\,\times\,R \rightarrow R$, (llamadas
usualmente suma y multiplicación) verificando las siguientes propiedades: 


1. Asociatividad de la suma: $\forall\,\, a,b,c\,\in\,R.\,\,\,\,(a+b)+c=a+(b+c)$\\

2. Existencia del elemento neutro para la suma:  $\exists\,\,0\,\in\,R.\,\,\forall\,\,a\,\in\,R.\,\,\,0+a=a+0=a$\\

3. Existencia del inverso para la suma:  $\forall\,\, a\,\in\,R,\,\exists\,\,b\,\in\,R.\,\,\,a+b=b+a=0$\\

4. La suma es commutativa:  $\forall\,\, a,b\,\in\,R.\,\,\,a+b=b+a$\\

5. Asociatividad de la multiplicación: $\forall\,\, a,b,c\,\in\,R.\,\,\,(a*b)*c=a*(b*c)$\\

6. Existencia del elemento neutro para la multiplicación: 
\begin{center}
$\exists\,\,1\,\in\,R.\,\,\,\,\forall\,\,a\,\in\,R.\,\,\,\,\,1*a=a*1=a$
\end{center}

7. Propiedad distributiva a la izquierda de la multiplicación sobre la suma:
\begin{center}
$\forall\,\, a,b,c\,\in\,R.\,\,\,\,a*(b+c)=(a*b)+(a*c)$
\end{center}

8. Propiedad distributiva a la derecha de la multiplicación sobre la suma:
\begin{center}
$\forall\,\, a,b,c\,\in\,R.\,\,\,\,(a+b)*c=(a*c)+(b*c)$
\end{center}
\end{defi}

Representaremos la noción de anillo en Haskell mediante una clase. Para
ello, declaramos la clase Ring sobre un tipo a con las operaciones
internas que denotaremos con los símbolos $<+>$ y $<**>$ (nótese que de
esta forma no coinciden con ninguna operación previamente definida en
Haskell). Representamos el elemento neutro de la suma mediante la
constante $zero$ y el de la multiplicación mediante la constante
$one$. Asímismo, mediante la operacion $neg$ representamos el elemento
inverso para la suma.

\begin{code}
infixl 6 <+>
infixl 7 <**>

class Ring a where
   (<+>) :: a -> a -> a
   (<**>) :: a -> a -> a
   neg :: a -> a
   zero :: a
   one :: a
-- |1. Asociatividad de la suma.
propAddAssoc :: (Ring a, Eq a) => a -> a -> a -> (Bool,String)
propAddAssoc a b c = ((a <+> b) <+> c == a <+> (b <+> c), "propAddAssoc")
-- |2. Existencia del elemento neutro para la suma.
propAddIdentity :: (Ring a, Eq a) => a -> (Bool,String)
propAddIdentity a = (a <+> zero == a && zero <+> a == a, "propAddIdentity")
-- |3. Existencia del inverso para la suma.
propAddInv :: (Ring a, Eq a) => a -> (Bool,String)
propAddInv a = (neg a <+> a == zero && a <+> neg a == zero, "propAddInv")
-- |4. La suma es commutativa.
propAddComm :: (Ring a, Eq a) => a -> a -> (Bool,String)
propAddComm x y = (x <+> y == y <+> x, "propAddComm")
-- |5. Asociatividad de la multiplicación.
propMulAssoc :: (Ring a, Eq a) => a -> a -> a -> (Bool,String)
propMulAssoc a b c = ((a <**> b) <**> c == a <**> (b <**> c), "propMulAssoc")
-- |6. Existencia del elemento neutro para la multiplicación.
propMulIdentity :: (Ring a, Eq a) => a -> (Bool,String)
propMulIdentity a = (one <**> a == a && a <**> one == a, "propMulIdentity")
-- |7. Propiedad distributiva a la izquierda de la multiplicación sobre la suma.
propRightDist :: (Ring a, Eq a) => a -> a -> a -> (Bool,String)
propRightDist a b c = 
  ((a <+> b) <**> c == (a <**> c) <+> (b <**> c), "propRightDist")
-- |8. Propiedad distributiva a la derecha de la multiplicación sobre la suma.
propLeftDist :: (Ring a, Eq a) => a -> a -> a -> (Bool,String)
propLeftDist a b c = 
 (a <**> (b <+> c) == (a <**> b) <+> (a <**> c), "propLeftDist")
\end{code}

Para saber si una terna $(a,<+>,<**>)$ es un anillo se necesita una función que
verifique las propiedades correspondientes:

\begin{code}
-- | Test para ver que se satisfacen los axiomas de los anillos.
propRing :: (Ring a, Eq a) => a -> a -> a -> Property
propRing a b c = whenFail (print errorMsg) cond
  where
  (cond,errorMsg) = 
    propAddAssoc a b c &&& propAddIdentity a  &&& propAddInv a        &&&
    propAddComm a b    &&& propMulAssoc a b c &&& propRightDist a b c &&&
    propLeftDist a b c &&& propMulIdentity a
  (False,x) &&& _         = (False,x)
  _         &&& (False,x) = (False,x)
  _         &&& _         = (True,"")
\end{code}

Veamos algunos ejemplos de anillos. Para ello, mediante instancias,
especificamos las operaciones que dotan al conjunto de estructura de
anillo. Por ejemplo, el anillo de los números enteros $\mathbb{Z}$ (en
Haskell es el tipo $Integer$), con la suma y la multiplicación.
Ejemplo:\\

\begin{code}
-- | El anillo de los enteros con la operaciones usuales:
instance Ring Integer where
     (<+>)  = (+)
     (<**>) = (*)
     neg    = negate
     zero   = 0
     one    = 1

\end{code}

Veamos ahora cómo definir nuevas operaciones en un anillo a partir de
las propias del anillo. En particular, vamos a definir la diferencia, la
potencia, etc. Estas operaciones se heredan a las instancias de la clase
anillo y, por tanto, no habría que volver a definirlas para cada anillo
particular. 

En primer lugar, establecemos el orden de prioridad para los símbolos
que vamos a utilizar para denotar las operaciones.

\begin{code}
infixl 8 <^>
infixl 6 <->
infixl 4 ~~
infixl 7 <**
\end{code}


\begin{code}
-- | Diferencia.
(<->) :: Ring a => a -> a -> a
a <-> b = a <+> neg b
-- | Suma de una lista de elementos.
sumRing :: Ring a => [a] -> a
sumRing = foldr (<+>) zero
-- | Producto de una lista de elementos.
productRing :: Ring a => [a] -> a
productRing = foldr (<**>) one
-- | Potencia.
(<^>) :: Ring a => a -> Integer -> a
x <^> 0 = one
x <^> y | y < 0     = error "<^>: La entrada debe ser positiva."
        | otherwise = x <**> x <^> (y-1)
-- | Relación de semi-igualdad: dos elementos son semi-iguales si son
--   iguales salvo el signo.
(~~) :: (Ring a, Eq a) => a -> a -> Bool
x ~~ y = x == y || neg x == y || x == neg y || neg x == neg y
\end{code}

Finalmente definimos la multiplicación de un entero por la derecha, la multiplicación de un entero por la izquierda se tiene debido a que la operación $<+>\,$ es commutativa.

\begin{code}
-- |Multiplicación de un entero por la derecha.
(<**) :: Ring a => a -> Integer -> a
_ <** 0 = zero
x <** n | n > 0     = x <+> x <** (n-1)
        | otherwise = neg (x <** abs n) -- error "<**: Entrada Negativa."
\end{code}
