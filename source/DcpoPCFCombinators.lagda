Tom de Jong, 27 May 2019.
Refactored December 2021.

* Continuous K and S functions. These will interpret the K and S combinators of
  PCF in ScottModelOfPCF.lagda.
* Continuous ifZero function specific to the lifting of the natural numbers.
  This will then be used to interpret the ifZero combinator of PCF in
  ScottModelOfPCF.lagda.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-PropTrunc

module DcpoPCFCombinators
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
       where

open PropositionalTruncation pt

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open import Poset fe
open import Dcpo pt fe 𝓥
open import DcpoMiscelanea pt fe 𝓥
open import DcpoExponential pt fe 𝓥

\end{code}

We start by defining continuous K and S functions. These will interpret the K
and S combinators of PCF in ScottModelOfPCF.lagda.

This requires a little (straightforward) work, because S must be continuous in
all of its arguments.
Therefore, it is not enough to have S of type
  DCPO[ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ] → DCPO[ 𝓓 , 𝓔 ] → DCPO[ 𝓓 , 𝓕 ].
Rather we should have S of type
  DCPO[𝓓 ⟹ᵈᶜᵖᵒ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 , (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ⟹ᵈᶜᵖᵒ (𝓓 ⟹ᵈᶜᵖᵒ 𝓕) ].

\begin{code}

module _ (𝓓 : DCPO {𝓤} {𝓣})
         (𝓔 : DCPO {𝓤'} {𝓣'})
       where

 Kᵈᶜᵖᵒ : DCPO[ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ 𝓓 ]
 Kᵈᶜᵖᵒ = k , c where
  k : ⟨ 𝓓 ⟩ → DCPO[ 𝓔 , 𝓓 ]
  k x = (λ _ → x) , (constant-functions-are-continuous 𝓔 𝓓 x)
  c : (I : 𝓥 ̇ ) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
    → is-sup (underlying-order (𝓔 ⟹ᵈᶜᵖᵒ 𝓓)) (k (∐ 𝓓 δ)) (λ (i : I) → k (α i))
  c I α δ = u , v where
   u : (i : I) (e : ⟨ 𝓔 ⟩) → α i ⊑⟨ 𝓓 ⟩ (∐ 𝓓 δ)
   u i e = ∐-is-upperbound 𝓓 δ i
   v : (f : DCPO[ 𝓔 , 𝓓 ])
     → ((i : I) → k (α i) ⊑⟨ 𝓔 ⟹ᵈᶜᵖᵒ 𝓓 ⟩ f)
     → (e : ⟨ 𝓔 ⟩) → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ [ 𝓔 , 𝓓 ]⟨ f ⟩ e
   v (f , _) l e = ∐-is-lowerbound-of-upperbounds 𝓓 δ (f e)
                   (λ (i : I) → (l i) e)

 module _ (𝓕 : DCPO {𝓦} {𝓦'}) where

  S₀ᵈᶜᵖᵒ : DCPO[ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ]
         → DCPO[ 𝓓 , 𝓔 ]
         → DCPO[ 𝓓 , 𝓕 ]
  S₀ᵈᶜᵖᵒ (f , cf) (g , cg) = (λ x → [ 𝓔 , 𝓕 ]⟨ f x ⟩ (g x)) , c
   where

    c : is-continuous 𝓓 𝓕 (λ x → [ 𝓔 , 𝓕 ]⟨ f x ⟩ (g x))
    c I α δ = u , v
     where
      u : (i : I) → [ 𝓔 , 𝓕 ]⟨ f (α i) ⟩   (g (α i)) ⊑⟨ 𝓕 ⟩
                    [ 𝓔 , 𝓕 ]⟨ f (∐ 𝓓 δ) ⟩ (g (∐ 𝓓 δ))
      u i = [ 𝓔 , 𝓕 ]⟨ f (α i)   ⟩ (g (α i))   ⊑⟨ 𝓕 ⟩[ ⦅1⦆ ]
            [ 𝓔 , 𝓕 ]⟨ f (∐ 𝓓 δ) ⟩ (g (α i))   ⊑⟨ 𝓕 ⟩[ ⦅2⦆ ]
            [ 𝓔 , 𝓕 ]⟨ f (∐ 𝓓 δ) ⟩ (g (∐ 𝓓 δ)) ∎⟨ 𝓕 ⟩
       where
        ⦅1⦆ = monotone-if-continuous 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (f , cf) (α i)
               (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ i) (g (α i))
        ⦅2⦆ = monotone-if-continuous 𝓔 𝓕 (f (∐ 𝓓 δ)) (g (α i)) (g (∐ 𝓓 δ))
               (monotone-if-continuous 𝓓 𝓔 (g , cg) (α i) (∐ 𝓓 δ)
                 (∐-is-upperbound 𝓓 δ i))
      v : (y : ⟨ 𝓕 ⟩)
        → ((i : I) → ([ 𝓔 , 𝓕 ]⟨ f (α i) ⟩ (g (α i))) ⊑⟨ 𝓕 ⟩ y)
        → ([ 𝓔 , 𝓕 ]⟨ f (∐ 𝓓 δ) ⟩ (g (∐ 𝓓 δ))) ⊑⟨ 𝓕 ⟩ y
      v y ineqs = γ
       where
        γ : [ 𝓔 , 𝓕 ]⟨ f (∐ 𝓓 δ) ⟩ (g (∐ 𝓓 δ)) ⊑⟨ 𝓕 ⟩ y
        γ = transport (λ - → [ 𝓔 , 𝓕  ]⟨ f (∐ 𝓓 δ) ⟩ - ⊑⟨ 𝓕 ⟩ y)
            e₀ γ₀
         where
          e₀ : ∐ 𝓔 (image-is-directed' 𝓓 𝓔 (g , cg) δ) ≡ g (∐ 𝓓 δ)
          e₀ = (continuous-∐-≡ 𝓓 𝓔 (g , cg) δ) ⁻¹
          ε₀ : is-Directed 𝓔 (g ∘ α)
          ε₀ = image-is-directed' 𝓓 𝓔 (g , cg) δ
          γ₀ : [ 𝓔 , 𝓕 ]⟨ f (∐ 𝓓 δ) ⟩ (∐ 𝓔 ε₀) ⊑⟨ 𝓕 ⟩ y
          γ₀ = transport (λ - → - ⊑⟨ 𝓕 ⟩ y) e₁ γ₁
           where
            e₁ : ∐ 𝓕 (image-is-directed' 𝓔 𝓕 (f (∐ 𝓓 δ)) ε₀) ≡
                 [ 𝓔 , 𝓕 ]⟨ f (∐ 𝓓 δ) ⟩ (∐ 𝓔 ε₀)
            e₁ = (continuous-∐-≡ 𝓔 𝓕 (f (∐ 𝓓 δ)) ε₀) ⁻¹
            ε₁ : is-Directed 𝓕 ([ 𝓔 , 𝓕 ]⟨ f (∐ 𝓓 δ) ⟩ ∘ (g ∘ α))
            ε₁ = image-is-directed' 𝓔 𝓕 (f (∐ 𝓓 δ)) ε₀
            γ₁ : (∐ 𝓕 ε₁) ⊑⟨ 𝓕 ⟩ y
            γ₁ = ∐-is-lowerbound-of-upperbounds 𝓕 ε₁ y γ₂
             where
              γ₂ : (i : I) → [ 𝓔 , 𝓕 ]⟨ f (∐ 𝓓 δ) ⟩ (g (α i)) ⊑⟨ 𝓕 ⟩ y
              γ₂ i = transport (λ - → [ 𝓔 , 𝓕 ]⟨ - ⟩ (g (α i)) ⊑⟨ 𝓕 ⟩ y) e₂ γ₃
               where
                ε₂ : is-Directed (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (f ∘ α)
                ε₂ = image-is-directed' 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (f , cf) δ
                e₂ : ∐ (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) {I} {f ∘ α} ε₂ ≡ f (∐ 𝓓 δ)
                e₂ = (continuous-∐-≡ 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (f , cf) δ) ⁻¹
                γ₃ : [ 𝓔 , 𝓕 ]⟨ ∐ (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) {I} {f ∘ α} ε₂ ⟩ (g (α i)) ⊑⟨ 𝓕 ⟩ y
                γ₃ = ∐-is-lowerbound-of-upperbounds 𝓕
                      (pointwise-family-is-directed 𝓔 𝓕 (f ∘ α) ε₂ (g (α i)))
                      y h
                 where
                  h : (j : I) → [ 𝓔 , 𝓕 ]⟨ f (α j) ⟩ (g (α i)) ⊑⟨ 𝓕 ⟩ y
                  h j = ∥∥-rec (prop-valuedness 𝓕
                         ([ 𝓔 , 𝓕 ]⟨ f (α j) ⟩ (g (α i))) y)
                         r (semidirected-if-Directed 𝓓 α δ i j)
                   where
                    r : (Σ k ꞉ I , α i ⊑⟨ 𝓓 ⟩ α k × α j ⊑⟨ 𝓓 ⟩ α k)
                      → [ 𝓔 , 𝓕 ]⟨ f (α j) ⟩ (g (α i)) ⊑⟨ 𝓕 ⟩ y
                    r (k , l , m ) = [ 𝓔 , 𝓕 ]⟨ f (α j) ⟩ (g (α i)) ⊑⟨ 𝓕 ⟩[ ⦅1⦆ ]
                                     [ 𝓔 , 𝓕 ]⟨ f (α k) ⟩ (g (α i)) ⊑⟨ 𝓕 ⟩[ ⦅2⦆ ]
                                     [ 𝓔 , 𝓕 ]⟨ f (α k) ⟩ (g (α k)) ⊑⟨ 𝓕 ⟩[ ⦅3⦆ ]
                                     y                              ∎⟨ 𝓕 ⟩
                     where
                      ⦅1⦆ = monotone-if-continuous 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (f , cf)
                             (α j) (α k) m (g (α i))
                      ⦅2⦆ = monotone-if-continuous 𝓔 𝓕 (f (α k))
                             (g (α i)) (g (α k))
                             (monotone-if-continuous 𝓓 𝓔 (g , cg) (α i) (α k) l)
                      ⦅3⦆ = ineqs k

  S₁ᵈᶜᵖᵒ : DCPO[ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ]
         → DCPO[ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 , 𝓓 ⟹ᵈᶜᵖᵒ 𝓕 ]
  S₁ᵈᶜᵖᵒ (f , cf) = h , c
   where
    h : DCPO[ 𝓓 , 𝓔 ] → DCPO[ 𝓓 , 𝓕 ]
    h = (S₀ᵈᶜᵖᵒ (f , cf))
    c : is-continuous (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) (𝓓 ⟹ᵈᶜᵖᵒ 𝓕) h
    c I α δ = u , v
     where
      u : (i : I) (d : ⟨ 𝓓 ⟩)
        → [ 𝓓 , 𝓕 ]⟨ h (α i) ⟩ d ⊑⟨ 𝓕 ⟩
          [ 𝓓 , 𝓕 ]⟨ h (∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ )⟩ d
      u i d = monotone-if-continuous 𝓔 𝓕 (f d)
              ([ 𝓓 , 𝓔 ]⟨ α i ⟩ d)
              ([ 𝓓 , 𝓔 ]⟨ ∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ ⟩ d)
              (∐-is-upperbound 𝓔 (pointwise-family-is-directed 𝓓 𝓔 α δ d) i)
      v : (g : DCPO[ 𝓓 , 𝓕 ])
        → ((i : I) → h (α i) ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ 𝓕 ⟩ g)
        → (d : ⟨ 𝓓 ⟩)
        → [ 𝓓 , 𝓕 ]⟨ h (∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ) ⟩ d ⊑⟨ 𝓕 ⟩ [ 𝓓 , 𝓕 ]⟨ g ⟩ d
      v g l d = transport (λ - → - ⊑⟨ 𝓕 ⟩ [ 𝓓 , 𝓕 ]⟨ g ⟩ d) e s
       where
        ε : is-Directed 𝓔 (pointwise-family 𝓓 𝓔 α d)
        ε = pointwise-family-is-directed 𝓓 𝓔 α δ d
        e : ∐ 𝓕 (image-is-directed' 𝓔 𝓕 (f d) ε)
            ≡ [ 𝓓 , 𝓕 ]⟨ h (∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ) ⟩ d
        e = (continuous-∐-≡ 𝓔 𝓕 (f d) ε) ⁻¹
        φ : is-Directed 𝓕
            ([ 𝓔 , 𝓕 ]⟨ f d ⟩ ∘ (pointwise-family 𝓓 𝓔 α d))
        φ = image-is-directed' 𝓔 𝓕 (f d) ε
        s : ∐ 𝓕 φ ⊑⟨ 𝓕 ⟩ [ 𝓓 , 𝓕 ]⟨ g ⟩ d
        s = ∐-is-lowerbound-of-upperbounds 𝓕 φ ([ 𝓓 , 𝓕 ]⟨ g ⟩ d)
            (λ (i : I) → l i d)

  Sᵈᶜᵖᵒ : DCPO[ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 , (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ⟹ᵈᶜᵖᵒ (𝓓 ⟹ᵈᶜᵖᵒ 𝓕) ]
  Sᵈᶜᵖᵒ = S₁ᵈᶜᵖᵒ , c
   where
    c : is-continuous (𝓓 ⟹ᵈᶜᵖᵒ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕)
                      ((𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ⟹ᵈᶜᵖᵒ (𝓓 ⟹ᵈᶜᵖᵒ 𝓕))
                      S₁ᵈᶜᵖᵒ
    c I α δ = u , v
     where
      u : (i : I) ((g , _) : DCPO[ 𝓓 , 𝓔 ]) (d : ⟨ 𝓓 ⟩)
        → [ 𝓔 , 𝓕 ]⟨ [ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ]⟨ α i ⟩ d ⟩ (g d) ⊑⟨ 𝓕 ⟩
          [ 𝓔 , 𝓕 ]⟨ [ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ]⟨ ∐ (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⟹ᵈᶜᵖᵒ 𝓕)) {I} {α} δ ⟩ d ⟩
           (g d)
      u i (g , _) d = ∐-is-upperbound 𝓕
                       (pointwise-family-is-directed 𝓔 𝓕 β ε (g d)) i
       where
        β : I → DCPO[ 𝓔 , 𝓕 ]
        β = pointwise-family 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) α d
        ε : is-Directed (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) β
        ε = pointwise-family-is-directed 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) α δ d
      v : (f : DCPO[ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 , 𝓓 ⟹ᵈᶜᵖᵒ 𝓕 ])
        → ((i : I) → S₁ᵈᶜᵖᵒ (α i) ⊑⟨ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ⟹ᵈᶜᵖᵒ (𝓓 ⟹ᵈᶜᵖᵒ 𝓕) ⟩ f)
        → (g : DCPO[ 𝓓 , 𝓔 ]) (d : ⟨ 𝓓 ⟩)
        → [ 𝓔 , 𝓕 ]⟨ [ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ]⟨ ∐ (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⟹ᵈᶜᵖᵒ 𝓕)) {I} {α} δ ⟩ d ⟩
           ([ 𝓓 , 𝓔 ]⟨ g ⟩ d)
        ⊑⟨ 𝓕 ⟩
          [ 𝓓 , 𝓕 ]⟨ [ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 , 𝓓 ⟹ᵈᶜᵖᵒ 𝓕 ]⟨ f ⟩ g ⟩ d
      v (f , _) l g d = ∐-is-lowerbound-of-upperbounds 𝓕 ε ([ 𝓓 , 𝓕 ]⟨ f g ⟩ d)
                         (λ (i : I) → l i g d)
       where
        ε : is-Directed 𝓕
             (λ i → [ 𝓓 , 𝓕 ]⟨ [ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 , 𝓓 ⟹ᵈᶜᵖᵒ 𝓕 ]⟨ S₁ᵈᶜᵖᵒ (α i) ⟩ g ⟩ d)
        ε = pointwise-family-is-directed 𝓔 𝓕 β φ ([ 𝓓 , 𝓔 ]⟨ g ⟩ d)
         where
          β : I → DCPO[ 𝓔 , 𝓕 ]
          β i = [ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ]⟨ α i ⟩ d
          φ : is-Directed (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) β
          φ = pointwise-family-is-directed 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) α δ d

module _ (𝓓 : DCPO⊥ {𝓤} {𝓣})
         (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
       where

 Kᵈᶜᵖᵒ⊥ : DCPO⊥[ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ]
 Kᵈᶜᵖᵒ⊥ = Kᵈᶜᵖᵒ (𝓓 ⁻) (𝓔 ⁻)

 Sᵈᶜᵖᵒ⊥ : (𝓕 : DCPO⊥ {𝓦} {𝓦'})
        → DCPO⊥[ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓔 ⟹ᵈᶜᵖᵒ⊥ 𝓕 , (𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓔) ⟹ᵈᶜᵖᵒ⊥ (𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓕) ]
 Sᵈᶜᵖᵒ⊥ 𝓕 = Sᵈᶜᵖᵒ (𝓓 ⁻) (𝓔 ⁻) (𝓕 ⁻)

\end{code}

TODO: Revise comments

Finally, we construct the continuous ifZero function, specific to the lifting of
ℕ. This will then be used to interpret the ifZero combinator of PCF in
ScottModelOfPCF.lagda.

\begin{code}

module IfZeroDenotationalSemantics
        (pe : propext 𝓥)
       where

 open import Lifting 𝓥
 open import LiftingMiscelanea 𝓥
 open import LiftingMiscelanea-PropExt-FunExt 𝓥 pe fe
 open import LiftingMonad 𝓥

 open import DcpoLifting pt fe 𝓥 pe

 open import UF-Miscelanea

 open import NaturalNumbers-Properties

 𝓛ᵈℕ : DCPO⊥ {𝓥 ⁺} {𝓥 ⁺}
 𝓛ᵈℕ = 𝓛-DCPO⊥ ℕ-is-set

 ⦅ifZero⦆₀ : 𝓛 ℕ → 𝓛 ℕ → ℕ → 𝓛 ℕ
 ⦅ifZero⦆₀ a b zero     = a
 ⦅ifZero⦆₀ a b (succ n) = b

 ⦅ifZero⦆₁ : 𝓛 ℕ → 𝓛 ℕ → DCPO⊥[ 𝓛ᵈℕ , 𝓛ᵈℕ ]
 ⦅ifZero⦆₁ a b =
  (⦅ifZero⦆₀ a b) ♯ , ♯-is-continuous ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ a b)

 ⦅ifZero⦆₂ : 𝓛 ℕ → DCPO⊥[ 𝓛ᵈℕ , 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ]
 ⦅ifZero⦆₂ a = ⦅ifZero⦆₁ a , c
  where
   c : is-continuous (𝓛ᵈℕ ⁻) ((𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ⁻) (⦅ifZero⦆₁ a)
   c I α δ = u , v
    where
     u : (i : I) (l : 𝓛 ℕ) (d : is-defined (((⦅ifZero⦆₀ a (α i)) ♯) l))
       → ((⦅ifZero⦆₀ a (α i)) ♯) l ≡ ((⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ)) ♯) l
     u i l d = ((⦅ifZero⦆₀ a (α i)) ♯) l             ≡⟨ q₁ ⟩
               ⦅ifZero⦆₀ a (α i) (value l e)         ≡⟨ q₂ ⟩
               ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) (value l e) ≡⟨ q₃ ⟩
               ((⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ)) ♯) l     ∎
      where
       e : is-defined l
       e = ♯-is-defined (⦅ifZero⦆₀ a (α i)) l d
       q₁ = ♯-on-total-element (⦅ifZero⦆₀ a (α i)) e
       q₃ = (♯-on-total-element (⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ)) {l} e) ⁻¹
       q₂ = ℕ-cases {𝓥 ⁺} {λ (n : ℕ) → ⦅ifZero⦆₀ a (α i) n
                                     ≡ ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) n} (value l e) p₀ pₛ
        where
         p₀ : value l e ≡ zero
            → ⦅ifZero⦆₀ a (α i) (value l e) ≡ ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) (value l e)
         p₀ q = ⦅ifZero⦆₀ a (α i) (value l e)         ≡⟨ ap (⦅ifZero⦆₀ a (α i)) q  ⟩
                ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) zero        ≡⟨ ap (⦅ifZero⦆₀ a _) (q ⁻¹) ⟩
                ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) (value l e) ∎
         pₛ : (n : ℕ) → value l e ≡ succ n
            → ⦅ifZero⦆₀ a (α i) (value l e) ≡ ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) (value l e)
         pₛ n q = ⦅ifZero⦆₀ a (α i) (value l e)         ≡⟨ ⦅1⦆  ⟩
                  ⦅ifZero⦆₀ a (α i) (succ n)            ≡⟨ refl ⟩
                  α i                                   ≡⟨ ⦅2⦆  ⟩
                  ∐ (𝓛ᵈℕ ⁻) δ                           ≡⟨ refl ⟩
                  ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) (succ n)    ≡⟨ ⦅3⦆  ⟩
                  ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) (value l e) ∎
          where
           ⦅1⦆ = ap (⦅ifZero⦆₀ a (α i)) q
           ⦅3⦆ = ap (⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ)) (q ⁻¹)
           ⦅2⦆ = family-defined-somewhere-sup-≡ ℕ-is-set δ i eᵢ
            where
             eᵢ : is-defined (α i)
             eᵢ = ≡-to-is-defined (ap (⦅ifZero⦆₀ a (α i)) q)
                   (≡-to-is-defined
                     (♯-on-total-element (⦅ifZero⦆₀ a (α i)) {l} e) d)

     v : (f : DCPO⊥[ 𝓛ᵈℕ , 𝓛ᵈℕ ])
       → ((i : I) → ⦅ifZero⦆₁ a (α i) ⊑⟪ 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ⟫ f)
       → (l : 𝓛 ℕ) (d : is-defined (((⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ)) ♯) l))
       → ((⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ)) ♯) l ≡ [ 𝓛ᵈℕ ⁻ , 𝓛ᵈℕ ⁻ ]⟨ f ⟩ l
     v (f , _) ineqs l d = ((⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ)) ♯) l     ≡⟨ q₁ ⟩
                           ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) (value l e) ≡⟨ q₂ ⟩
                           f l                                  ∎
      where
       e : is-defined l
       e = ♯-is-defined (⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ)) l d
       q₁ = ♯-on-total-element (⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ)) {l} e
       q₂ = ℕ-cases {𝓥 ⁺} {λ (n : ℕ) → ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) n ≡ f l}
             (value l e) p₀ pₛ
        where
         p₀ : value l e ≡ zero
            → ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) (value l e) ≡ f l
         p₀ q = ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) (value l e) ≡⟨ ⦅1⦆  ⟩
                ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) zero        ≡⟨ refl ⟩
                a                                     ≡⟨ ⦅2⦆  ⟩
                f l                                   ∎
          where
           ⦅1⦆ = ap (⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ)) q
           ⦅2⦆ = ∥∥-rec (lifting-of-set-is-set ℕ-is-set)
                  h (inhabited-if-Directed (𝓛ᵈℕ ⁻) α δ)
            where
             h : (i : I) → a ≡ f l
             h i = a                             ≡⟨ ⦅1'⦆ ⟩
                   ⦅ifZero⦆₀ a (α i) (value l e) ≡⟨ ⦅2'⦆ ⟩
                   ((⦅ifZero⦆₀ a (α i)) ♯) l     ≡⟨ ⦅3'⦆ ⟩
                   f l                           ∎
              where
               ⦅1'⦆ = ap (⦅ifZero⦆₀ a (α i)) (q ⁻¹)
               ⦅2'⦆ = (♯-on-total-element (⦅ifZero⦆₀ a (α i)) e) ⁻¹
               ⦅3'⦆ = ineqs i l (≡-to-is-defined r d)
                where
                 r : ((⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ)) ♯) l
                   ≡ ((⦅ifZero⦆₀ a (α i)) ♯) l
                 r = q₁ ∙ ⦅1⦆ ∙ ⦅1'⦆ ∙ ⦅2'⦆

         pₛ : (m : ℕ) → value l e ≡ succ m
            → ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) (value l e) ≡ f l
         pₛ m q = ∥∥-rec (lifting-of-set-is-set ℕ-is-set) h e'
          where
           ⦅1⦆ : (⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) ♯) l
               ≡ ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) (value l e)
           ⦅1⦆ = ♯-on-total-element (⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ)) {l} e
           ⦅2⦆ : ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) (value l e) ≡ ∐ (𝓛ᵈℕ ⁻) δ
           ⦅2⦆ = ap (⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ)) q
           e' : is-defined (∐ (𝓛ᵈℕ ⁻) δ)
           e' = ≡-to-is-defined (⦅1⦆ ∙ ⦅2⦆) d
           h : (Σ i ꞉ I , is-defined (α i))
             → ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) (value l e) ≡ f l
           h (i , dᵢ) = ⦅ifZero⦆₀ a (∐ (𝓛ᵈℕ ⁻) δ) (value l e) ≡⟨ ⦅1'⦆ ⟩
                        ∐ (𝓛ᵈℕ ⁻) δ                           ≡⟨ ⦅2'⦆ ⟩
                        α i                                   ≡⟨ ⦅3'⦆ ⟩
                        ((⦅ifZero⦆₀ a (α i)) ♯) l             ≡⟨ ⦅4'⦆ ⟩
                        f l                                   ∎
            where
             ⦅1'⦆ = ⦅2⦆
             ⦅2'⦆ = (family-defined-somewhere-sup-≡ ℕ-is-set δ i dᵢ) ⁻¹
             ⦅3'⦆ = (♯-on-total-element (⦅ifZero⦆₀ a (α i)) e
                     ∙ ap (⦅ifZero⦆₀ a (α i)) q) ⁻¹
             ⦅4'⦆ = ineqs i l (≡-to-is-defined ⦅3'⦆ dᵢ)

\end{code}

We can exploit the fact that ifZero a b 0 ≡ ifZero b a 1, to reduce the proof
that ifZero is continuous in its first argument to continuity in its second
argument. The "flip"-code below prepares for this.

\begin{code}

 ℕ-flip : ℕ → ℕ
 ℕ-flip zero     = succ zero
 ℕ-flip (succ n) = zero

 ifZero-flip-equation : (a b : 𝓛 ℕ) (n : ℕ)
                      → ⦅ifZero⦆₀ a b n ≡ ⦅ifZero⦆₀ b a (ℕ-flip n)
 ifZero-flip-equation a b zero     = refl
 ifZero-flip-equation a b (succ n) = refl

 𝓛ℕ-flip : 𝓛 ℕ → 𝓛 ℕ
 𝓛ℕ-flip (P , ϕ , ρ) = (P , ℕ-flip ∘ ϕ , ρ)

 ifZero♯-flip-equation : (a b : 𝓛 ℕ) (l : 𝓛 ℕ)
                      → ((⦅ifZero⦆₀ a b) ♯) l ≡ ((⦅ifZero⦆₀ b a) ♯) (𝓛ℕ-flip l)
 ifZero♯-flip-equation a b l = ⊑'-is-antisymmetric u v
  where
   l' : 𝓛 ℕ
   l' = 𝓛ℕ-flip l
   lemma : (p : is-defined l)
         → (⦅ifZero⦆₀ a b ♯) l ≡ (⦅ifZero⦆₀ b a ♯) l'
   lemma p = (⦅ifZero⦆₀ a b ♯) l        ≡⟨ ⦅1⦆ ⟩
             ⦅ifZero⦆₀ a b (value l  p) ≡⟨ ⦅2⦆ ⟩
             ⦅ifZero⦆₀ b a (value l' p) ≡⟨ ⦅3⦆ ⟩
             (⦅ifZero⦆₀ b a ♯) l'       ∎
    where
     ⦅1⦆ = ♯-on-total-element (⦅ifZero⦆₀ a b) p
     ⦅2⦆ = ifZero-flip-equation a b (value l p)
     ⦅3⦆ = (♯-on-total-element (⦅ifZero⦆₀ b a) p) ⁻¹
   u : (⦅ifZero⦆₀ a b ♯) l ⊑' (⦅ifZero⦆₀ b a ♯) l'
   u q = lemma (♯-is-defined (⦅ifZero⦆₀ a b) l q)
   v : (⦅ifZero⦆₀ b a ♯) l' ⊑' (⦅ifZero⦆₀ a b ♯) l
   v q = (lemma (♯-is-defined (⦅ifZero⦆₀ b a) l' q)) ⁻¹

\end{code}

We are now ready to give the final continuity proof.

\begin{code}

 ⦅ifZero⦆ : DCPO⊥[ 𝓛ᵈℕ , 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ  ]
 ⦅ifZero⦆ = ⦅ifZero⦆₂ , c
  where
   c : is-continuous (𝓛ᵈℕ ⁻) ((𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ⁻) ⦅ifZero⦆₂
   c I α δ = u , v
    where
     u : (i : I) (b : 𝓛 ℕ) (l : 𝓛 ℕ)
       → ((⦅ifZero⦆₀ (α i) b) ♯) l ⊑⟪ 𝓛ᵈℕ ⟫ ((⦅ifZero⦆₀ (∐ (𝓛ᵈℕ ⁻) δ) b) ♯) l
     u i b l = ((⦅ifZero⦆₀ (α i) b) ♯) l           ⊑⟪ 𝓛ᵈℕ ⟫[ ⦅1⦆ ]
               ((⦅ifZero⦆₀ b (α i)) ♯) l'          ⊑⟪ 𝓛ᵈℕ ⟫[ ⦅2⦆ ]
               ((⦅ifZero⦆₀ b (∐ (𝓛ᵈℕ ⁻) δ)) ♯) l'  ⊑⟪ 𝓛ᵈℕ ⟫[ ⦅3⦆ ]
               ((⦅ifZero⦆₀ (∐ (𝓛ᵈℕ ⁻) δ) b) ♯) l   ∎⟪ 𝓛ᵈℕ ⟫
      where
       l' : 𝓛 ℕ
       l' = 𝓛ℕ-flip l
       ⦅1⦆ = ≡-to-⊑ (𝓛ᵈℕ ⁻) (ifZero♯-flip-equation (α i) b l)
       ⦅2⦆ = (monotone-if-continuous (𝓛ᵈℕ ⁻) ((𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ⁻)
              (⦅ifZero⦆₂ b) (α i) (∐ (𝓛ᵈℕ ⁻) δ)
              (∐-is-upperbound (𝓛ᵈℕ ⁻) δ i))
             l'
       ⦅3⦆ = ≡-to-⊑ (𝓛ᵈℕ ⁻) ((ifZero♯-flip-equation (∐ (𝓛ᵈℕ ⁻) δ) b l) ⁻¹)

     v : ((f , _) : DCPO⊥[ 𝓛ᵈℕ , 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ])
       → ((i : I) (b : 𝓛 ℕ) → ⦅ifZero⦆₁ (α i) b ⊑⟪ 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ⟫ f b)
       → (b : 𝓛 ℕ) (l : 𝓛 ℕ)
       → ((⦅ifZero⦆₀ (∐ (𝓛ᵈℕ ⁻) δ) b) ♯) l ⊑⟪ 𝓛ᵈℕ ⟫ [ 𝓛ᵈℕ ⁻ , 𝓛ᵈℕ ⁻ ]⟨ f b ⟩ l
     v (f , _) ineqs b l =
      ((⦅ifZero⦆₀ (∐ (𝓛ᵈℕ ⁻) δ) b) ♯) l                 ⊑⟪ 𝓛ᵈℕ ⟫[ ⦅1⦆ ]
      ((⦅ifZero⦆₀ b (∐ (𝓛ᵈℕ ⁻) δ)) ♯) l'                ⊑⟪ 𝓛ᵈℕ ⟫[ ⦅2⦆ ]
      [ 𝓛ᵈℕ ⁻ , 𝓛ᵈℕ ⁻ ]⟨ ⦅ifZero⦆₁ b (∐ (𝓛ᵈℕ ⁻) δ) ⟩ l' ⊑⟪ 𝓛ᵈℕ ⟫[ ⦅3⦆ ]
      ∐ (𝓛ᵈℕ ⁻) {I} {α'} δ'                             ⊑⟪ 𝓛ᵈℕ ⟫[ ⦅4⦆ ]
      ∐ (𝓛ᵈℕ ⁻) {I} {α''} δ''                           ⊑⟪ 𝓛ᵈℕ ⟫[ ⦅5⦆ ]
      [ 𝓛ᵈℕ ⁻ , 𝓛ᵈℕ ⁻ ]⟨ f b ⟩ l                        ∎⟪ 𝓛ᵈℕ ⟫
       where
        l' : 𝓛 ℕ
        l' = 𝓛ℕ-flip l
        α' : (i : I) → ⟪ 𝓛ᵈℕ ⟫
        α' i = ((⦅ifZero⦆₀ b (α i)) ♯) l'
        δ' : is-Directed (𝓛ᵈℕ ⁻) α'
        δ' = pointwise-family-is-directed (𝓛ᵈℕ ⁻) (𝓛ᵈℕ ⁻) (⦅ifZero⦆₁ b ∘ α) ε l'
         where
          ε : is-Directed ((𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ⁻) (⦅ifZero⦆₁ b ∘ α)
          ε = image-is-directed' (𝓛ᵈℕ ⁻) ((𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ⁻) (⦅ifZero⦆₂ b) δ
        α'' : (i : I) → ⟪ 𝓛ᵈℕ ⟫
        α'' i = ((⦅ifZero⦆₀ (α i) b) ♯) l
        e : α' ≡ α''
        e = dfunext fe (λ i → (ifZero♯-flip-equation (α i) b l) ⁻¹)
        δ'' : is-Directed (𝓛ᵈℕ ⁻) α''
        δ'' = transport (is-Directed (𝓛ᵈℕ ⁻)) e δ'

        ⦅1⦆ = ≡-to-⊑ (𝓛ᵈℕ ⁻) (ifZero♯-flip-equation (∐ (𝓛ᵈℕ ⁻) δ) b l)
        ⦅2⦆ = reflexivity (𝓛ᵈℕ ⁻) _
        ⦅3⦆ = ≡-to-⊑ (𝓛ᵈℕ ⁻)
              (ap (λ - → [ 𝓛ᵈℕ ⁻ , 𝓛ᵈℕ ⁻ ]⟨ - ⟩ l')
                  (continuous-∐-≡ (𝓛ᵈℕ ⁻) ((𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ⁻)
                    (⦅ifZero⦆₂ b) {I} {α} δ))
        ⦅4⦆ = ≡-to-⊑ (𝓛ᵈℕ ⁻) (∐-family-≡ (𝓛ᵈℕ ⁻) e δ')
        ⦅5⦆ = ∐-is-lowerbound-of-upperbounds (𝓛ᵈℕ ⁻) δ''
              ([ 𝓛ᵈℕ ⁻ , 𝓛ᵈℕ ⁻ ]⟨ f b ⟩ l) (λ i → ineqs i b l)

\end{code}
