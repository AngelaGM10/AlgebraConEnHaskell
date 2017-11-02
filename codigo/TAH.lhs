\begin{code}
module TAH where 
import Data.List
\end{code}


\section{Anillos en Haskell}

Antes de dar la definición de anillos en Haskell daremos el tipo de clase (veáse que usaremos $**$ para la multiplicación definida anteriormente por $*$):
\begin{code}
class Ring a where
(<+>) :: a -> a -> a
(<**>) :: a -> a -> a
neg :: a -> a
zero :: a
one :: a
\end{code}
\\

\begin{defi}
Un anillo es un conjunto R definido por dos operaciones binarias llamadas suma y multiplicación denotadas $+,*:R\,\times\,R \rightarrow R$ respectivamente.\\
Los axiomas de la terna $(R,+,*)$ deben satisfacer:\\

1. Cerrado para la suma: $\forall\,\, a,b\,\in\,R.\,\,\,\,a+b\,\in\,R$\\

2. Asociatividad de la suma: $\forall\,\, a,b,c\,\in\,R.\,\,\,\,(a+b)+c=a+(b+c)$\\

3. Existencia del elemento neutro para la suma:  $\exists\,\,0\,\in\,R.\,\,\forall\,\,a\,\in\,R.\,\,\,0+a=a+0=a$\\

4. Existencia del inverso para la suma:  $\forall\,\, a\,\in\,R,\,\exists\,\,b\,\in\,R.\,\,\,a+b=b+a=0$\\

Estas cuatro condiciones definen un grupo. 

\begin{code}

-- |2. Addition is associative.
propAddAssoc :: (Ring a, Eq a) => a -> a -> a -> (Bool,String)
propAddAssoc a b c = ((a <+> b) <+> c == a <+> (b <+> c), "propAddAssoc")

-- |3. Zero is the additive identity.
propAddIdentity :: (Ring a, Eq a) => a -> (Bool,String)
propAddIdentity a = (a <+> zero == a && zero <+> a == a, "propAddIdentity")

-- |4. Negation give the additive inverse.
propAddInv :: (Ring a, Eq a) => a -> (Bool,String)
propAddInv a = (neg a <+> a == zero && a <+> neg a == zero, "propAddInv")

\end{code}

Una quinta condición define un grupo abeliano:

5. La suma es commutativa:  $\forall\,\, a,b\,\in\,R.\,\,\,a+b=b+a$\\

\begin{code}
-- |5. Addition is commutative.
propAddComm :: (Ring a, Eq a) => a -> a -> (Bool,String)
propAddComm x y = (x <+> y == y <+> x, "propAddComm")
\end{code}

Para definir un anillo, es necesario agregar tres condiciones más sobre la segunda operación binaria:

6. Cerrado bajo la multiplicación: $\forall\,\, a,b\,\in\,R.\,\,\,a*b \in R$\\

7. Asociatividad de la multiplicación: $\forall\,\, a,b,c\,\in\,R.\,\,\,(a*b)*c=a*(b*c)$\\

8. Existencia del elemento neutro para la multiplicación: 
\begin{center}
$\exists\,\,1\,\in\,R.\,\,\,\,\forall\,\,a\,\in\,R.\,\,\,\,\,1*a=a*1=a$
\end{center}

9. Propiedad distributiva a la izquierda de la multiplicación sobre la suma:
\begin{center}
$\forall\,\, a,b,c\,\in\,R.\,\,\,\,a*(b+c)=(a*b)+(a*c)$
\end{center}

10. Propiedad distributiva a la derecha de la multiplicación sobre la suma:
\begin{center}
$\forall\,\, a,b,c\,\in\,R.\,\,\,\,(a+b)*c=(a*c)+(b*c)$
\end{center}

\begin{code}

-- |7. Multiplication is associative.
propMulAssoc :: (Ring a, Eq a) => a -> a -> a -> (Bool,String)
propMulAssoc a b c = ((a <**> b) <**> c == a <**> (b <**> c), "propMulAssoc")

-- |8. One is the multiplicative identity.
propMulIdentity :: (Ring a, Eq a) => a -> (Bool,String)
propMulIdentity a = (one <**> a == a && a <**> one == a, "propMulIdentity")

-- |9. Multiplication is right-distributive over addition.
propRightDist :: (Ring a, Eq a) => a -> a -> a -> (Bool,String)
propRightDist a b c = 
  ((a <+> b) <**> c == (a <**> c) <+> (b <**> c), "propRightDist")

-- |10. Multiplication is left-ditributive over addition.
propLeftDist :: (Ring a, Eq a) => a -> a -> a -> (Bool,String)
propLeftDist a b c = 
 (a <**> (b <+> c) == (a <**> b) <+> (a <**> c), "propLeftDist")

\end{code}

Y agregando una última condición, se define un anillo conmutativo:
\begin{code}
-- | 11. Multiplication is commutative.
propMulComm :: (Ring a, Eq a) => a -> a -> (Bool,String)
propMulComm x y = (x <**> y == y <**> x, "propMulComm")
\end{code}
\end{defi}

Un anillo conmutativo puede ser representado como un tipo de clase vacío en Haskell ya que no contiene ninguna nueva operación a la estructura. Pues es un axioma que ya estaba representado.

Si un anillo cuenta con un elemento neutro para la segunda operación se llama anillo unitario. A dicho elemento se le suele llamar la unidad (1) para diferenciarlo del elemento neutro de la primera operación (usualmente el 0).

El conjunto de los elementos no nulos de un anillo se escriben como $R^*$. Ejemplos de anillos como $(\mathbb{Z},+,*)$ donde $+$ y $*$ denotan la suma y multiplicación ordinaria para los enteros. Otros ejemplos son $\mathbb{Q},\mathbb{R},\mathbb{C}$ con la definición usual de suma y multiplicación.\\

En Haskell esto puede representarse como un tipo de clase (veáse que usaremos $**$ para la multiplicación definida anteriormente por $*$), Los axiomas de los anillos también pueden ser representados en Haskell.Estos son representados como funciones que deben ser usadas para testear que una implementación satisface las condiciones:\\

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

Solo consideraremos los anillos commutativos, todos los ejemplos que daremos serán de anillos commutativos. Una clase fundamental de anillos finitos son \textit{el anillo de los enteros en modulo $n$}, denotado por $\mathbb{Z}_n$. Esto se corresponde con los elementos $a \in\, \mathbb{Z}$ en la misma clase de congruencias modulo n, por ejemplo $\mathbb{Z}_3 \simeq \{0,1,2\}$ hay tres clases de congruencias modulo 3. La suma y multiplicación son definidas usando la suma y multiplicación de $\mathbb{Z}$ en modulo $n$.

El compilador de Haskell debería distinguir elementos de diferentes anillos y verificar que no se dupliquen. Por ejemplo el tipo de clase de $\mathbb{Z}$ depende de los valores de n. Es posible representar enteros segunla clase de Haskell pero es un poco difícil y dependemos de las clases que queremos tener.

\begin{defi} 
Un dominio integral es un anillo conmutativo satisfaciendo:
\begin{center}
$a*b=0\,\, \Rightarrow \,\,a = 0 \vee b = 0, \,\,\,\,\,\,\forall\,\, a,b \in\,\, R.$
\end{center}
\end{defi}

Los anillos $\mathbb{Z},\mathbb{Q},\mathbb{R},\mathbb{C}$ son dominios integrales con la definición de suma y multiplicación. Para $\mathbb{Z_n}$ es un poco más complicado, por ejemplo  $\mathbb{Z_6}$ no es un dominio integral ya que $2*3=0$ modulo 6.Por tanto $\mathbb{Z_n}$ es un dominio integral si y solo $n$ es primo. 
