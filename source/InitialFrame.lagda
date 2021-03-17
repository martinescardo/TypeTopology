Ayberk Tosun, 10 March 2021.

Based in part on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-PropTrunc
open import UF-FunExt
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

⊑-is-partial-order : is-partial-order (Ω 𝓤) _⊑_
⊑-is-partial-order = (⊑-is-reflexive , ⊑-is-transitive) , ⊑-is-antisymmetric

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

open propositional-truncations-exist pt

𝟎-𝔽𝕣𝕞 : frame (𝓤 ⁺) 𝓤 𝓤
𝟎-𝔽𝕣𝕞 = Ω 𝓤 , (_⊑_ , ⊤Ω {𝓤} , _∧_ , ⋁_)
      , ⊑-is-partial-order , top , meet , join , dist
 where
  ⋁_ : Fam 𝓤 (Ω 𝓤) → Ω 𝓤
  ⋁ U = ∃[ i ∶ index U ] ((U [ i ]) holds)

  open Meets _⊑_

  top : is-top (⊤Ω {𝓤}) holds
  top _ _ = *

  meet : (∀[ (P , Q) ] (P ∧ Q) is-glb-of (P , Q)) holds
  meet (P , Q) = β , γ
   where
    β : ((P ∧ Q) is-a-lower-bound-of (P , Q)) holds
    β = pr₁ , pr₂

    γ : (∀[ (R , _) ∶ lower-bound (P , Q ) ] R ⊑ (P ∧ Q)) holds
    γ (R , ϕ , ψ) r = ϕ r , ψ r

  open Joins        _⊑_
  open JoinNotation ⋁_

  join : (∀[ U ∶ Fam 𝓤 (Ω 𝓤) ] ((⋁ U) is-lub-of U)) holds
  join U = (λ i u → ∣ i , u ∣) , γ
   where
    γ : (∀[ (P , _) ∶ upper-bound U ] (⋁ U) ⊑ P) holds
    γ ((A , A-prop) , q) r = ∥∥-rec A-prop (uncurry q) r

  iss : is-set (Ω 𝓤)
  iss = carrier-of-[ 𝟎F-poset ]-is-set

  dist : (∀[ (P , U) ∶ Ω 𝓤 × Fam 𝓤 (Ω 𝓤) ]
          (P ∧ (⋁ U) ≡[ iss ]≡  ⋁⟨ i ⟩ P ∧ U [ i ])) holds
  dist (P , U) = Ω-ext-from-univalence ua β γ
   where
    β : (P ∧ ⋁ U ⇒ (⋁⟨ i ⟩ (P ∧ U [ i ]))) holds
    β (p , u) = ∥∥-rec (holds-is-prop (⋁⟨ i ⟩ (P ∧ U [ i ]))) α u
     where
      α : Σ i ꞉ index U , (U [ i ]) holds → (⋁⟨ i ⟩ P ∧ U [ i ]) holds
      α (i , uᵢ) = ∣ i , p , uᵢ ∣

    γ : ((⋁⟨ i ⟩ P ∧ U [ i ]) ⇒ P ∧ ⋁ U) holds
    γ p = ∥∥-rec (holds-is-prop (P ∧ (⋁ U))) δ p
     where
      δ : Sigma (index (index U , (λ i → P ∧ U [ i ])))
            (λ i → ((index U , (λ i₁ → P ∧ U [ i₁ ])) [ i ]) holds) →
            (P ∧ (⋁ U)) holds
      δ (i , q , uᵢ) = q , ∣ i , uᵢ ∣

\end{code}

\section{Proof of initiality}

\end{code}
