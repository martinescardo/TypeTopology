Brendan Hart 2019-2020

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.Basics.FunctionComposition
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
       where

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.Pointed pt fe 𝓥

open import Posets.Poset fe

open PosetAxioms

[_,_,_]_∘ᵈᶜᵖᵒ_ : (𝓓 : DCPO {𝓤} {𝓤'})
                 (𝓔 : DCPO {𝓣} {𝓣'})
                 (𝓕 : DCPO {𝓦} {𝓦'})
               → DCPO[ 𝓔 , 𝓕 ]
               → DCPO[ 𝓓 , 𝓔 ]
               → DCPO[ 𝓓 , 𝓕 ]
[ 𝓓 , 𝓔 , 𝓕 ] g ∘ᵈᶜᵖᵒ f = h , c
 where
  h : ⟨ 𝓓 ⟩ → ⟨ 𝓕 ⟩
  h = pr₁ g ∘ pr₁ f

  h-is-monotone : is-monotone 𝓓 𝓕 h
  h-is-monotone x y p = γ
   where
    δ : pr₁ f x ⊑⟨ 𝓔 ⟩ pr₁ f y
    δ = monotone-if-continuous 𝓓 𝓔 f x y p

    γ : h x ⊑⟨ 𝓕 ⟩ h y
    γ = monotone-if-continuous 𝓔 𝓕 g (pr₁ f x) (pr₁ f y) δ

  c : is-continuous 𝓓 𝓕 h
  c I α δ = u , v
    where
     u : is-upperbound (underlying-order 𝓕) (h (∐ 𝓓 δ)) (λ i → h (α i))
     u i = h-is-monotone (α i) (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ i)

     v : (z : ⟨ 𝓕 ⟩) →
         ((i : I) → h (α i) ⊑⟨ 𝓕 ⟩ z) →
         h (∐ 𝓓 δ) ⊑⟨ 𝓕 ⟩ z
     v z p = transport (λ - → - ⊑⟨ 𝓕 ⟩ z) (e ⁻¹) q
       where
        isdir₁ : is-Directed 𝓔 (λ i → pr₁ f (α i))
        isdir₁ = image-is-directed 𝓓 𝓔 (monotone-if-continuous 𝓓 𝓔 f) δ

        isdir₂ : is-Directed 𝓕 (λ i → (pr₁ g ∘ pr₁ f) (α i))
        isdir₂ = image-is-directed 𝓔 𝓕 (monotone-if-continuous 𝓔 𝓕 g) isdir₁

        e : h (∐ 𝓓 δ) ＝ ∐ 𝓕 isdir₂
        e = h (∐ 𝓓 δ)          ＝⟨ ap (λ - → pr₁ g -) (continuous-∐-＝ 𝓓 𝓔 f δ) ⟩
            pr₁ g (∐ 𝓔 isdir₁) ＝⟨ continuous-∐-＝ 𝓔 𝓕 g isdir₁ ⟩
            ∐ 𝓕 isdir₂         ∎

        q : ∐ 𝓕 isdir₂ ⊑⟨ 𝓕 ⟩ z
        q = ∐-is-lowerbound-of-upperbounds 𝓕 isdir₂ z p

[_,_,_]_∘ᵈᶜᵖᵒ⊥_ : (𝓓 : DCPO⊥ {𝓤} {𝓤'})
                  (𝓔 : DCPO⊥ {𝓣} {𝓣'})
                  (𝓕 : DCPO⊥ {𝓦} {𝓦'})
                → DCPO⊥[ 𝓔 , 𝓕 ]
                → DCPO⊥[ 𝓓 , 𝓔 ]
                → DCPO⊥[ 𝓓 , 𝓕 ]
[ 𝓓 , 𝓔 , 𝓕 ] g ∘ᵈᶜᵖᵒ⊥ f = [ (𝓓 ⁻) , (𝓔 ⁻) , (𝓕 ⁻) ] g ∘ᵈᶜᵖᵒ f

\end{code}
