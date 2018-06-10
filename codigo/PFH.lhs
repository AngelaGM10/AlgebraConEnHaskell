\begin{code}
module PFH where 
import Data.List
\end{code}

\section{Introducción a Haskell}

En esta sección se introducirán funciones básicas para la programación   
en Haskell. Como método didáctico, se empleará la definición de   
funciones ejemplos, así como la redefinición de funciones que Haskell
ya tiene predefinidas, con el objetivo de que el lector aprenda 
``\textit{a montar en bici, montando}''.

A continuación se muestra la definición \texttt{(cuadrado x)} es el cuadrado de \texttt{x}. 
Por ejemplo,
La definición es
\index{\texttt{cuadrado}}
\begin{code}
-- |
-- >>> cuadrado 3
-- 9
-- >>> cuadrado 4
-- 16
cuadrado :: Int -> Int
cuadrado x = x * x
\end{code}


A continuación se muestra la definición \texttt{(cubo x)} es el cuadrado de \texttt{x}. 
Por ejemplo,
La definición es
\index{\texttt{cubo}}
\begin{code}
-- |
-- >>> cubo 3
-- 27
-- >>> cubo 2
-- 8
-- >>> cubo 4
-- 64
cubo :: Int -> Int
cubo x = x^3
\end{code}


S continuación se muestra la definición \texttt{(suma x y)} es la suma de \texttt{x} e  \texttt{y}. 
Por ejemplo,
La definición es
\index{\texttt{suma}}
\begin{code}
-- |
-- >>> suma 3 5
-- 8
-- >>> suma 4 2
-- 6
suma :: Int -> Int -> Int
suma x y = x + y
\end{code}


La función $foldr\,\, f\,\, c$, este se usa para aplicar la operación $f$ a los elementos de una lista tomando como elemento de inicio a $c$.\\

La clase $Show$ convierte el elemento que recibe en una cadena legible, es decir, cuando intentamos mostrar un valor por pantalla, primero Haskell ejecuta la función $show$ para obtener la representación en texto de un dato y luego lo muestra en la terminal.\\

La función $intersperse$ toma un elemento y una lista, e intercala el elemento entre cada uno de los elementos de la lista. Por ejemplo:
\begin{code}
-- λ> intersperse ',' "abcde"
-- "a,b,c,d,e"
\end{code}

La función $filter$ es una función que toma un predicado (un predicado es una función que dice si algo es cierto o falso, o en nuestro caso, una función que devuelve un valor booleano) y una lista y devuelve una lista con los elementos que satisfacen el predicado. La función $filter$ la utilizamos para eliminar los elementos nulos, si los hubiese, de la lista que toma.\\

Tanto la función $filter$ como $foldr$ son funciones de orden superior. Las funciones de Haskell pueden tomar funciones como parámetros y devolver funciones como resultado. Una función que hace ambas cosas o alguna de ellas se llama función de orden superior.\\

La función $zipWith$ generaliza a la función $zip$ comprimiendo con la función dada como primer argumento, en lugar de una función de tuplas.Por ejemplo, $zipWith (+)$ se aplica a dos listas para producir la lista de sumas correspondientes.
\begin{code}
--λ> zipWith (+) [1,2,3] [4,5]
-- [5,7]
\end{code}

 La función $sequence$ evalua cada acción en la secuencia de izquierda a derecha y recopila los resultados, es decir, va a aplicar la acción dada a cada elemento de la lista.

 $Maybe\,a$, un constructor de tipo. La $a$ es un parámetro de tipo. Ningún valor puede tener un tipo que sea simplemente $Maybe$, ya que eso no es un tipo por si mismo, es un constructor de tipos. Para que sea un tipo real que algún valor pueda tener, tiene que tener todos los parámetros de tipo definidos.
