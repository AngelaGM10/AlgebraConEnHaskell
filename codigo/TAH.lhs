
Antes de empezar tenemos que crear nuestro módulo, todos tienen la misma estructura, se usa el comando de Haskell $module$ seguido del nombre que le queramos dar al módulo. A continuación entre paréntesis introducimos todas las clases y funciones que vamos a definir y que queramos exportar cuando en otro fichero importemos este módulo, seguido del paréntesis escribimos $where$ y finalmente importamos las librerías y módulos que vayamos a necesitar. Para importarlas usamos el comando $import$. \\

Para nuestro primer módulo solo usaremos la conocida librería de Haskell $Data.List$ la cual comprende las operaciones con listas, y $Test.QuickCheck$ esta librería contine las funciones para probar una propiedad e imprimir los resultados.

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



Comenzamos con la parte teórica, damos la definición teórica de anillos:\\

\begin{defi}
Un anillo es una terna $(R,+,*)$, donde $R$ es un conjunto y $+,*$ son
dos operaciones binarias $+,*:R\,\times\,R \rightarrow R$, (llamadas
usualmente suma y multiplicación) verificando lo siguiente: 


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

Una vez tenemos la teoría, pasamos a implementarlo en Haskell. Representaremos la noción de anillo en Haskell mediante una clase. Para
ello, declaramos la clase $Ring$ sobre un tipo $a$ (es decir, $a$ no está restringido a ningún otro tipo) con las operaciones internas que denotaremos con los símbolos $<+>$ y $<**>$ (nótese que de esta forma no coinciden con ninguna operación previamente definida en Haskell). Representamos el elemento neutro de la suma mediante la constante $zero$ y el de la multiplicación mediante la constante $one$.\\

Asímismo, mediante la función $neg$ representamos el elemento inverso para la suma, es decir, para cada elemento $x$ del anillo, $neg x$ representará el inverso de $x$ respecto de la suma $<+>$. Todas ellas varían según el anillo que queramos definir.\\

Para utilizar operaciones que definimos nosotros, (es decir, que no están implementadas en Haskell como puede ser la suma) usamos el comando de Haskell $infixl$, para introducir el símbolo de la operación que vamos a definir.

\begin{code}
infixl 6 <+>
infixl 7 <**>

class Ring a where
   (<+>) :: a -> a -> a
   (<**>) :: a -> a -> a
   neg :: a -> a
   zero :: a
   one :: a
\end{code}

Una vez establecida la clase de los anillos, pasamos a implementar los axiomas de este. En Haskell un tipo es como una etiqueta que posee toda expresión. Esta etiqueta nos dice a que categoría de cosas se ajusta la expresión.\\

Todos los axiomas que tenemos que introducir tienen la misma estructura, recibe elementos que son del tipo $Ring$ y del tipo $Eq$ para devolver elementos del tipo $Bool$ y $String$.\\

La clase $Ring$ la acabamos de definir y la clase de tipos $Eq$ proporciona una interfaz para las comparaciones de igualdad. Cualquier tipo que tenga sentido comparar dos valores de ese tipo por igualdad debe ser miembro de la clase $Eq$. El tipo $Bool$ devuelve un booleano con $True$ y $False$, en nuestras funciones es necesario pues necesitamos que nos devuelva $True$ si se verifica el axioma y $False$ en caso contrario. El tipo $String$ es sinónimo del tipo $Char$ este es necesario pues los booleanos son una cadena de carácteres.

\begin{code}
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

Para saber si una terna $(a,<+>,<**>)$ es un anillo crearemos una propiedad que se encargue de comprobar que los axiomas anteriores se verifiquen, para cada caso particular de una instancia dada. La estructura que tiene es la siguiente: recibe un elemento de tipo $Ring$ y $Eq$ y devuelve un elemento de tipo Property. Este es un tipo que convierte lo que recibe en una propiedad, es una función importada desde el módulo $Test.QuickCheck$.

\begin{code}
-- | Test para ver si se verifican los axiomas de un anillo.
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
anillo. Por ejemplo, el anillo de los números enteros $\mathbb{Z}$, en
Haskell es el tipo $Integer$, con la suma y la multiplicación.
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

Se admite esta instancia porque se ha comprobado que se verifican los axiomas para ser un anillo. 
En caso contrario, proporcionaría un error.

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

En la función $sumRing$ hemos usado el comando $foldr x c$, este se usa para aplicar la operación $x$ a los elementos de una lista tomando como elemento de inicio a $c$.\\

Finalmente definimos la multiplicación de un entero por la derecha, la multiplicación de un entero por la izquierda se tiene debido a que la operación $<+>\,$ es commutativa. Esta función al igual que la anterior de potencia recibe un elemento de tipo $Ring$ y devuelve un número entero, que es el tipo $Integer$. Cuando lo que devuelve no tiene ningún tipo especificado significa que no tiene restricción de tipo. 

\begin{code}
-- |Multiplicación de un entero por la derecha.
(<**) :: Ring a => a -> Integer -> a
_ <** 0 = zero
x <** n | n > 0     = x <+> x <** (n-1)
        | otherwise = neg (x <** abs n) -- error "<**: Entrada Negativa."
\end{code}
