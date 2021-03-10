Ayberk Tosun, 10 March 2021.

Based in part on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-PropTrunc
open import UF-FunExt
open import UF-PropTrunc
open import UF-Univalence
open import UF-UA-FunExt

module InitialFrame
        (𝓤 : Universe)
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (ua : is-univalent 𝓤)
       where

open import UF-Subsingletons
open import UF-Subsingleton-Combinators
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import Frame pt fe
open AllCombinators pt fe

\end{code}

\section{The underlying poset}

We start with the partial ordering on `Ω`:

\begin{code}

_⊑_ : Ω 𝓥 → Ω 𝓦 → Ω (𝓥 ⊔ 𝓦)
P ⊑ Q = P ⇒ Q

⊑-is-reflexive : is-reflexive {A = Ω 𝓤} _⊑_ holds
⊑-is-reflexive P = id

⊑-is-transitive : is-transitive {A = Ω 𝓤} _⊑_ holds
⊑-is-transitive _ _ _ p q = q ∘ p

⊑-is-antisymmetric : is-antisymmetric {A = Ω 𝓤} _⊑_
⊑-is-antisymmetric = Ω-ext-from-univalence ua

⊑-is-partial : is-partial (Ω 𝓤) _⊑_
⊑-is-partial = (⊑-is-reflexive , ⊑-is-transitive) , ⊑-is-antisymmetric

\end{code}

This gives us a poset structure at universe 𝓤:

\begin{code}

𝟎F-poset-str : poset-structure 𝓤 (Ω 𝓤)
𝟎F-poset-str = _⊑_
             , (⊑-is-reflexive , ⊑-is-transitive)
             , ⊑-is-antisymmetric

𝟎F-poset : poset (𝓤 ⁺) 𝓤
𝟎F-poset = Ω 𝓤 , 𝟎F-poset-str

\end{code}

\section{Definition of the initial frame}

\begin{code}

𝟎-𝔽𝕣𝕞 : frame (𝓤 ⁺) 𝓤 𝓤
𝟎-𝔽𝕣𝕞 = Ω 𝓤 , (_⊑_ , ⊤Ω {𝓤} , _∧_ , ⋁_)
      , ⊑-is-partial , top , meet , {!!}
 where
  ⋁_ : Fam 𝓤 (Ω 𝓤) → Ω 𝓤
  ⋁ U = ∃[ i ∶ index U ] U [ i ]

  open Meets _⊑_

  top : is-top (⊤Ω {𝓤}) holds
  top _ _ = *

  meet : (∀[ (P , Q) ] (P ∧ Q) is-glb-of (P , Q)) holds
  meet (P , Q) = β , γ
   where
    β : ((P ∧ Q) is-a-lower-bound-of (P , Q)) holds
    β = pr₁ , pr₂

    γ : {!!}
    γ = {!!}

\end{code}

\section{Proof of initiality}

\end{code}
