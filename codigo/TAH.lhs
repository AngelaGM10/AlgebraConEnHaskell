\begin{code}
module TAH where 

import Data.List
import Test.QuickCheck

infixl 8 <^>
infixl 7 <**>
infixl 6 <+>
infixl 6 <->
infixl 4 ~~
infixl 7 **>
infixl 7 <**
infixl 7 </>
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

-- | Test para ver que las propiedades satisfacen los axiomas de los anillos.
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

A partir de lo anterior podemos implementar operaciones que tienen los anillos así como la resta de dos anillos, sumar los elementos de un anillo o multiplicarlos, elevar a una potencia y comparar dos anillos. Los conjuntos que verifican la función $propRing$ poseen también dichas operaciones.

\begin{code}

-- | Resta de anillos.
(<->) :: Ring a => a -> a -> a
a <-> b = a <+> neg b

-- | Suma los elementos del anillo.
sumRing :: Ring a => [a] -> a
sumRing = foldr (<+>) zero

-- | Producto de los elementos del anillo.
productRing :: Ring a => [a] -> a
productRing = foldr (<**>) one

-- | Exponente de un anillo.
(<^>) :: Ring a => a -> Integer -> a
x <^> 0 = one
x <^> y = if y < 0
             then error "<^>: Input should be positive"
             else x <**> x <^> (y-1)

-- | Comprobar que dos anillos a y b son:
--   a == b o -a == b o a == -b o -a == -b
(~~) :: (Ring a, Eq a) => a -> a -> Bool
x ~~ y = x == y || neg x == y || x == neg y || neg x == neg y

\end{code}

A continuación vamos a añadir dos funciones a las operaciones que podemos realizar con los anillos. Estas son similiares a las propiedades 7 y 8:

\begin{code}

-- |Multiplicar por la izquierda al anillo con un número entero.
-- esto es: n **> x = x + x + ... + x, n veces.
(**>) :: Ring a => Integer -> a -> a
0 **> _ = zero
n **> x | n > 0     = x <+> x <** (n-1)
        | otherwise = neg (abs n **> x) -- error "<**: Negative input"

-- |Multiplicar por la derecha al anillo con un número entero.
(<**) :: Ring a => a -> Integer -> a
_ <** 0 = zero
x <** n | n > 0     = x <+> x <** (n-1)
        | otherwise = neg (x <** abs n) -- error "<**: Negative input"

\end{code}

\begin{defi}
un anillo conmutativo es un anillo (R, +, *) con elemento unidad, el elemento neutro, en el que la operación de multiplicación * es conmutativa; es decir,\\
 $\forall\,\, a,b\,\in\,R.\,\,\, a*b = b*a$\\
\end{defi}

Para definir los anillos conmutativos en Haskell usaremos la clase $CommutRing$ que es una subclase de $Ring$ y definiremos la función $propCommutRing$ que sirve para comprobar si un anillo es conmutativo o no.

\begin{code}

class Ring a => CommutRing a

propMulComm :: (CommutRing a, Eq a) => a -> a -> Bool
propMulComm a b = a <**> b == b <**> a


-- | Test para ver que la multiplicación es conmutativa y que satisface
-- los axiomas de los anillos.
propCommutRing :: (CommutRing a, Eq a) => a -> a -> a -> Property
propCommutRing a b c = if propMulComm a b 
                               then propRing a b c 
                               else whenFail (print "propMulComm") False

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

-- | Test para ver que no tiene divisores de cero y que se satisface
-- los axiomas de los anillos conmutativos.
propIntegralDomain :: (IntegralDomain a, Eq a) => a -> a -> a -> Property
propIntegralDomain a b c = if propZeroDivisors a b
                              then propCommutRing a b c 
                              else whenFail (print "propZeroDivisors") False

\end{code}

\begin{defi}
Un cuerpo es un anillo conmutativo con elemento unidad tal $(A- \{0\})$ también es un grupo abeliano, es decir, cumple las 4 primeras propiedades.
\end{defi}

\begin{code}

-- | Definición de cuerpo.

class IntegralDomain a => Field a where
  inv :: a -> a

propMulInv :: (Field a, Eq a) => a -> Bool
propMulInv a = a == zero || inv a <**> a == one

-- | Test para ver que los inversos multiplicativos se comportan como se
-- espera y que satisface los axiomas de los dominios integrales.
propField :: (Field a, Eq a) => a -> a -> a -> Property
propField a b c = if propMulInv a
                     then propIntegralDomain a b c 
                     else whenFail (print "propMulInv") False


-- | Operaciones que se pueden realizar en un cuerpo a partir de lo anterior.

-- | División
(</>) :: Field a => a -> a -> a
x </> y = x <**> inv y
\end{code}
