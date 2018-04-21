Martin Escardo, 2011-2018.

This is a univalent foundations library (in Agda notation), with some
things developed using the Yoneda-lemma view of the identity type, as
put forward in http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF where

open import SpartanMLTT public
open import UF-Base public
open import UF-Subsingletons public
open import UF-Yoneda public
open import UF-Retracts public
open import UF-Subsingletons-Retracts public
open import UF-Equiv public
open import UF-LeftCancellable public
open import UF-FunExt public
open import UF-Univalence public
open import UF-Embedding public
open import UF-Subsingletons-FunExt public
open import UF-Retracts-FunExt public
open import UF-Prop public
open import UF-PropTrunc public
open import UF-ImageAndSurjection public
open import UF-ExcludedMiddle public
open import UF-Equiv-FunExt public
open import UF-IdEmbedding public

\end{code}
