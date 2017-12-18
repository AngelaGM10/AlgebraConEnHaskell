\begin{code}
module TAH where 

import Data.List
import Test.QuickCheck

--infixl 8 <^>
infixl 7 <**>
infixl 6 <+>
--infixl 6 <->

\end{code}


\section{Anillos en Haskell}

Comenzamos por definir los anillos en Haskell. Crearemos un modulo llamado TAH que contendrá todas las funciones necesarias para crear un anillo, así como sus principales propiedades. Primero daremos la definición teórica de anillos:\\

\begin{defi}
Un anillo es un conjunto R definido por dos operaciones binarias llamadas suma y multiplicación denotadas $+,*:R\,\times\,R \rightarrow R$ respectivamente.\\
Los axiomas de la terna $(R,+,*)$ deben satisfacer:\\

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

Para dar la definición de anillos en Haskell usaremos las clases, declaramos la clase $\,Ring \,\,a$ como la clase de los anillos donde $Ring$ es el nombre de la clase para poder usarla sobre cualquier anillo $\,a$. Daremos las operaciones internas que necesita un anillo para ser definido, que son la suma ($(<+>)$), multiplicación ($(<**>)$), los elementos neutros para la suma ($zero$) y multiplicación ($one$) y el elemento inverso para la suma ($neg$). Para definir bien las operaciones que hemos usado al principio el comando $infixl$. Una vez construida la clase de los anillos, construimos las funciones de cada una de las propiedades que debe de cumplir $a$ para ser un anillo.


\begin{code}
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

Para saber si un conjunto $a$ es un anillo o no necesitaremos una función que compruebe que el conjunto dado verifique las propiedades dadas anteriormente:

\begin{code}

-- | Specification of rings. Test that the arguments satisfy the ring axioms.
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

Veamos unos ejemplos de conjuntos que son anillos, para ello usaremos las instancias, de esta forma damos las operaciones que el conjunto tiene asociado para poder ser un anillo. El conjunto de los números enteros $\mathbb{Z}$ (en Haskell es el tipo $Integer$), 
Ejemplo:\\
\begin{code}
-- | El conjunto de los enteros. 
instance Ring Integer where
     (<+>)  = (+)
     (<**>) = (*)
     neg    = negate
     zero   = 0
     one    = 1



\end{code}



