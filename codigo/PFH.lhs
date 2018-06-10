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

A continuación se muestra la definición \texttt{(cubo x)} es el cubo de \texttt{x}. 
Por ejemplo,
La definición es
\index{\texttt{cubo}}
\begin{code}
cubo :: Int -> Int
cubo x = x^3
--λ> cubo 3
-- 27
--λ> cubo 4
-- 64
\end{code}

\subsection{Listas por comprensión}
En este trabajo se ha utilizado las listas para implementar el álgebra constructiva en Haskell. Las listas en Haskell son un conjunto ordenado de elemento, la posición del primer elemento de una lista es \texttt{0}. Así, una lista de longitud 3 por ejemplo \texttt{[1,2,3]} tiene las posiciones de sus elementos como \texttt{0,1,2}. Vamos a dar unas funciones básicas de Haskell que se aplican a listas. Estas funciones predefinidas en Haskell la redefiniremos usando listas por comprensión. Estas permite trabajar con listas haciendo operaciones o filtrando sus elementos mediantes condiciones que se le impone, son de la forma:
\begin{center}
[f(x) | x <- xs, p(x)] 
\end{center}
[función que se aplica al elemento | elemento <- (que recorre) la lista de elementos, condiciones que tiene que cumplir el elemento]\\
Devolviendo la lista de todos los elementos de \texttt{xs} que verifican la condición \texttt{p(x)} con la función \texttt{x} aplicada.

Empezaremos por la función \texttt{(map f xs)} que aplica la función \texttt{f} a cada elemento de la lista \texttt{xs}. Para redefinirla la llamaremos \texttt{(mimap f xs)}:
\begin{code}
--λ> map (cubo) [1,2,3]
-- [1,8,27]
--λ> map (+2) [1,0,3]
-- [3,2,5]

mimap :: (a -> b) -> [a] -> [b]
mimap f xs = [f(x) | x <- xs]

--λ> mimap (cubo) [1,2,3]
-- [1,8,27]
--λ> mimap (+2) [1,0,3]
-- [3,2,5]

\end{code}

La función \texttt{(intersperse p xs)} intercala el elemento \texttt{p} entre cada uno de los elementos de la lista \texttt{xs}. La denotaremos por \texttt{(intercalado p xs)} y vamos a dar una definición por recursión. Una definición por recursión es aquella en la que se establecen los casos bases y se utiliza la misma función a definir para el caso general.
\begin{code}
-- λ> intersperse ',' "abcde"
-- "a,b,c,d,e"

intercalado :: a -> [a] -> [a]
intercalado p [] = []
intercalado p [x] = [x]
intercalado p (x:xs) = [x,p] ++ intercalado p xs

--λ> intercalado ',' "abcde"
-- "a,b,c,d,e"
\end{code}


--añadir el resto de funciones.

 La función $sequence$ evalua cada acción en la secuencia de izquierda a derecha y recopila los resultados, es decir, va a aplicar la acción dada a cada elemento de la lista.

\subsection{Funciones de orden superior}

Las funciones de Haskell pueden tomar funciones como parámetros y devolver funciones como resultado. Una función que hace ambas cosas o alguna de ellas se llama función de orden superior. En esta sección veremos las funciones de orden superior que hemos utilizado a lo largo del trabajo.\\

La función \texttt{(zipWith f xs ys)} generaliza a la función \texttt{(zip xs ys)}, devuelve la lista resultante de aplicar la función \texttt{f} entre las listas \texttt{xs} e \texttt{ys}. La redefinimos por recursión como \texttt{(mizipwith f xs ys)}
\begin{code}
--λ> zipWith (+) [1,2,3] [4,5]
-- [5,7]

mizipwith :: (a -> b -> c) -> [a] -> [b] -> [c]
mizipwith _ [] _ = []  
mizipwith _ _ [] = []  
mizipwith f (x:xs) (y:ys) = f x y : mizipwith f xs ys

--λ> mizipwith (+) [1,2,3] [4,5]
-- [5,7]
\end{code}

La función \texttt{(foldr f c xs)} se usa para aplicar la operación \texttt{f} a los elementos de la lista \texttt{xs} tomando a \texttt{c} como elemento de inicio. La redefinimos como \texttt{(mifoldr f c xs)}\\
--añadir código

La función \texttt{(filter p xs)} devuelve una lista con los elementos de la lista \texttt{xs} que verifican la condición o predicado \texttt{p}.\\
--añadir código

\subsection{clases y tipos}
La clase \texttt{Show} convierte el elemento que recibe en una cadena legible, es decir, cuando intentamos mostrar un valor por pantalla, primero Haskell ejecuta la función \texttt{show} para obtener la representación en texto de un dato y luego lo muestra en la terminal.\\

 \texttt{Maybe} es un constructor de tipo. Ningún valor puede tener un tipo que sea simplemente $Maybe$, ya que eso no es un tipo por si mismo, es un constructor de tipos. Para que sea un tipo real que algún valor pueda tener, tiene que tener todos los parámetros de tipo definidos. 
-- Explicar tipos, clases, constructor e instancias. Sin ejemplos de código.
