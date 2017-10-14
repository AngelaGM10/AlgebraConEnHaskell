\begin{code}
module TAH where 
import Data.List
\end{code}


\section{Anillos en Haskell}

\begin{defi}
Un anillo es un conjunto R definido por dos operaciones binarias llamadas suma y multiplicación denotadas $+,*:R\,\times\,R \rightarrow R$ respectivamente.\\
Los axiomas de la terna $(R,+,*)$ deben satisfacer:\\

1. Cerrado para la suma: $\forall\,\, a,b\,\in\,R.\,\,\,\,a+b\,\in\,R$\\

2. Asociatividad de la suma: $\forall\,\, a,b,c\,\in\,R.\,\,\,\,(a+b)+c=a+(b+c)$\\

3. Existencia del elemento neutro para la suma:  $\exists\,\,0\,\in\,R.\,\,\forall\,\,a\,\in\,R.\,\,\,0+a=a+0=a$\\

4. Existencia del inverso para la suma:  $\forall\,\, a\,\in\,R,\,\exists\,\,b\,\in\,R.\,\,\,a+b=b+a=0$\\

5. La suma es commutativa:  $\forall\,\, a,b\,\in\,R.\,\,\,a+b=b+a$\\

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

\end{defi}

El conjunto de los elementos no nulos de un anillo se escriben como $R^*$. Ejemplos de anillos como $(\mathbb{Z},+,*)$ donde + y * denotan la suma y multiplicación ordinaria para los enteros. Otros ejemplos son $\mathbb{Q},\mathbb{R},\mathbb{C}$ con la definición usual de suma y multiplicación.\\

\textbf{Nota para la implementación:} En Haskell esto puede representarse como un tipo de clase (veáse que usaremos ** para la multiplicación definida anteriormente por *):\\

\begin{code}
class Ring a where
(<+>) :: a -> a -> a
(<**>) :: a -> a -> a
neg :: a -> a
zero :: a
one :: a
\end{code}

Los axiomas de los anillos también pueden ser representados en Haskell. Los axiomas son representados como funciones las cuales deben ser usadas para testear que una implementación satisface las condiciones. Por ejemplo la propiedad donde la multiplicación es distributiva por la izquierda sobre la suma puede especificarse como:

\begin{code}
propLeftDist :: (Ring a, Eq a) => a -> a -> a -> Bool
propLeftDist a b c = a <**> (b <+> c) == (a <**> b) <+> (a <*> c)
\end{code}

El tipo de la teoría de los axiomas posiblemente puede ser representado por un nivel de tipo de archivos dependientes. 
Entonces la estructura contendría también los axiomas y el usuario tendría que probar que una estructura las satisface en orden para construir una instancia. Esto es mejor ya que la implementación se probaría correcta y no solo aleatoriamente testeado.\\

\begin{defi}
Un anillo commutativo  es un anillo $(\mathbb{R},+,*)$ satisfaciendo el axioma de la multiplicación es conmutativa:
\begin{center}
$\forall \,\, a,b \in \, R. \,\,\,\, a*b = b*a$
\end{center}
\end{defi}
