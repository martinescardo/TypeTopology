Tom de Jong, 27 May 2019.

* Dcpo of continuous functions (i.e. the exponential in the category of dcpos)
* Continuous K and S functions
* The lifting of a set is a dcpo
* Continuous ifZero function specific to the lifting of the natural numbers

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-Subsingletons
open import UF-PropTrunc

module DcpoConstructions
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt
open import UF-Base
open import UF-Miscelanea
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open import Poset fe
open import Dcpo pt fe 𝓥
open import DcpoBasics pt fe 𝓥
open import DcpoExponential pt fe 𝓥

\end{code}

We proceed by defining continuous K and S functions.
This will be used in ScottModelOfPCF.

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
     → (e : ⟨ 𝓔 ⟩) → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ (underlying-function 𝓔 𝓓 f e)
   v (f , _) l e = ∐-is-lowerbound-of-upperbounds 𝓓 δ (f e)
                   (λ (i : I) → (l i) e)

 module _ (𝓕 : DCPO {𝓦} {𝓦'}) where

  S₀ᵈᶜᵖᵒ : DCPO[ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ]
         → DCPO[ 𝓓 , 𝓔 ]
         → DCPO[ 𝓓 , 𝓕 ]
  S₀ᵈᶜᵖᵒ (f , cf) (g , cg) = (λ x → underlying-function 𝓔 𝓕 (f x) (g x)) , c
   where

    c : is-continuous 𝓓 𝓕 (λ x → underlying-function 𝓔 𝓕 (f x) (g x))
    c I α δ = u , v
     where
      u : (i : I) → underlying-function 𝓔 𝓕 (f (α i)) (g (α i)) ⊑⟨ 𝓕 ⟩
                    underlying-function 𝓔 𝓕 (f (∐ 𝓓 δ)) (g (∐ 𝓓 δ))
      u i = transitivity 𝓕
            (underlying-function 𝓔 𝓕 (f (α i)) (g (α i)))
            (underlying-function 𝓔 𝓕 (f (∐ 𝓓 δ)) (g (α i)))
            (underlying-function 𝓔 𝓕 (f (∐ 𝓓 δ)) (g (∐ 𝓓 δ)))
            (l (g (α i)))
            (monotone-if-continuous 𝓔 𝓕 (f (∐ 𝓓 δ)) (g (α i))
             (g (∐ 𝓓 δ)) m)
       where
        l : f (α i) ⊑⟨ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ⟩ f (∐ 𝓓 δ)
        l = monotone-if-continuous 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (f , cf) (α i)
            (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ i)
        m : g (α i) ⊑⟨ 𝓔 ⟩ g (∐ 𝓓 δ)
        m = monotone-if-continuous 𝓓 𝓔 (g , cg) (α i) (∐ 𝓓 δ)
            (∐-is-upperbound 𝓓 δ i)
      v : (y : ⟨ 𝓕 ⟩)
        → ((i : I) → (underlying-function 𝓔 𝓕 (f (α i)) (g (α i))) ⊑⟨ 𝓕 ⟩ y)
        → (underlying-function 𝓔 𝓕  (f (∐ 𝓓 δ)) (g (∐ 𝓓 δ))) ⊑⟨ 𝓕 ⟩ y
      v y ineqs = γ
       where
        γ : underlying-function 𝓔 𝓕 (f (∐ 𝓓 δ)) (g (∐ 𝓓 δ)) ⊑⟨ 𝓕 ⟩ y
        γ = transport (λ - → underlying-function 𝓔 𝓕 (f (∐ 𝓓 δ)) - ⊑⟨ 𝓕 ⟩ y)
            e₀ γ₀
         where
          e₀ : ∐ 𝓔 (image-is-directed' 𝓓 𝓔 (g , cg) δ) ≡ g (∐ 𝓓 δ)
          e₀ = (continuous-∐-≡ 𝓓 𝓔 (g , cg) δ) ⁻¹
          ε₀ : is-Directed 𝓔 (g ∘ α)
          ε₀ = image-is-directed' 𝓓 𝓔 (g , cg) δ
          γ₀ : (underlying-function 𝓔 𝓕 (f (∐ 𝓓 δ)) (∐ 𝓔 ε₀)) ⊑⟨ 𝓕 ⟩ y
          γ₀ = transport (λ - → - ⊑⟨ 𝓕 ⟩ y) e₁ γ₁
           where
            e₁ : ∐ 𝓕 (image-is-directed' 𝓔 𝓕 (f (∐ 𝓓 δ)) ε₀) ≡
                 underlying-function 𝓔 𝓕 (f (∐ 𝓓 δ)) (∐ 𝓔 ε₀)
            e₁ = (continuous-∐-≡ 𝓔 𝓕 (f (∐ 𝓓 δ)) ε₀) ⁻¹
            ε₁ : is-Directed 𝓕
                 (underlying-function 𝓔 𝓕 (f (∐ 𝓓 δ)) ∘ (g ∘ α))
            ε₁ = image-is-directed' 𝓔 𝓕 (f (∐ 𝓓 δ)) ε₀
            γ₁ : (∐ 𝓕 ε₁) ⊑⟨ 𝓕 ⟩ y
            γ₁ = ∐-is-lowerbound-of-upperbounds 𝓕 ε₁ y γ₂
             where
              γ₂ : (i : I)
                 → (underlying-function 𝓔 𝓕 (f (∐ 𝓓 δ))) (g (α i)) ⊑⟨ 𝓕 ⟩ y
              γ₂ i = transport
                     (λ - → (underlying-function 𝓔 𝓕 -) (g (α i)) ⊑⟨ 𝓕 ⟩ y )
                     e₂ γ₃
               where
                ε₂ : is-Directed (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (f ∘ α)
                ε₂ = image-is-directed' 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (f , cf) δ
                e₂ : ∐ (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) {I} {f ∘ α} ε₂ ≡ f (∐ 𝓓 δ)
                e₂ = (continuous-∐-≡ 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (f , cf) δ) ⁻¹
                γ₃ : underlying-function 𝓔 𝓕 (∐ (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) {I} {f ∘ α} ε₂) (g (α i))
                   ⊑⟨ 𝓕 ⟩ y
                γ₃ = ∐-is-lowerbound-of-upperbounds 𝓕
                      (pointwise-family-is-directed 𝓔 𝓕 (f ∘ α) ε₂ (g (α i)))
                      y h
                 where
                  h : (j : I) → (pr₁ (f (α j)) (g (α i))) ⊑⟨ 𝓕 ⟩ y
                  h j = ∥∥-rec (prop-valuedness 𝓕 (pr₁ (f (α j)) (g (α i))) y)
                        r (semidirected-if-Directed 𝓓 α δ i j)
                   where
                    r : (Σ  k ꞉ I , α i ⊑⟨ 𝓓 ⟩ α k × α j ⊑⟨ 𝓓 ⟩ α k)
                      → (underlying-function 𝓔 𝓕 (f (α j)) (g (α i))) ⊑⟨ 𝓕 ⟩ y
                    r (k , l , m ) = transitivity 𝓕
                                      (underlying-function 𝓔 𝓕 (f (α j))
                                       (g (α i)))
                                      (underlying-function 𝓔 𝓕 (f (α k))
                                       (g (α k)))
                                      y
                                      (transitivity 𝓕
                                        (underlying-function 𝓔 𝓕 (f (α j))
                                          (g (α i)))
                                        (underlying-function 𝓔 𝓕 (f (α k))
                                          (g (α i)))
                                      (underlying-function 𝓔 𝓕 (f (α k))
                                          (g (α k)))
                                      (s (g (α i)))
                                      (monotone-if-continuous 𝓔 𝓕
                                        (f (α k)) (g (α i)) (g (α k))
                                       (monotone-if-continuous 𝓓 𝓔
                                        (g , cg) (α i) (α k) l)))
                                     (ineqs k)
                     where
                      s : f (α j) ⊑⟨ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ⟩ f (α k)
                      s = monotone-if-continuous 𝓓
                           (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (f , cf) (α j) (α k) m


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
        → underlying-function 𝓓 𝓕 (h (α i)) d ⊑⟨ 𝓕 ⟩
          underlying-function 𝓓 𝓕 (h (∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ)) d
      u i d = monotone-if-continuous 𝓔 𝓕 (f d)
              (underlying-function 𝓓 𝓔 (α i) d)
              (underlying-function 𝓓 𝓔 (∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ) d)
              (∐-is-upperbound 𝓔 (pointwise-family-is-directed 𝓓 𝓔 α δ d) i)
      v : (g : DCPO[ 𝓓 , 𝓕 ])
        → ((i : I) → h (α i) ⊑⟨ 𝓓 ⟹ᵈᶜᵖᵒ 𝓕 ⟩ g)
        → (d : ⟨ 𝓓 ⟩) → underlying-function 𝓓 𝓕 (h (∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔)
                          {I} {α} δ)) d
                         ⊑⟨ 𝓕 ⟩ underlying-function 𝓓 𝓕 g d
      v g l d = transport (λ - → - ⊑⟨ 𝓕 ⟩ underlying-function 𝓓 𝓕 g d) e s
       where
        ε : is-Directed 𝓔 (pointwise-family 𝓓 𝓔 α d)
        ε = pointwise-family-is-directed 𝓓 𝓔 α δ d
        e : ∐ 𝓕 (image-is-directed' 𝓔 𝓕 (f d) ε)
            ≡ underlying-function 𝓓 𝓕 (h (∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ)) d
        e = (continuous-∐-≡ 𝓔 𝓕 (f d) ε) ⁻¹
        φ : is-Directed 𝓕
            (underlying-function 𝓔 𝓕 (f d) ∘ (pointwise-family 𝓓 𝓔 α d))
        φ = image-is-directed' 𝓔 𝓕 (f d) ε
        s : ∐ 𝓕 φ ⊑⟨ 𝓕 ⟩ (underlying-function 𝓓 𝓕 g) d
        s = ∐-is-lowerbound-of-upperbounds 𝓕 φ (underlying-function 𝓓 𝓕 g d)
            (λ (i : I) → l i d)

  Sᵈᶜᵖᵒ : DCPO[ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 , (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ⟹ᵈᶜᵖᵒ (𝓓 ⟹ᵈᶜᵖᵒ 𝓕) ]
  Sᵈᶜᵖᵒ = S₁ᵈᶜᵖᵒ , c
   where
    c : is-continuous (𝓓 ⟹ᵈᶜᵖᵒ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕)
                      ((𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ⟹ᵈᶜᵖᵒ (𝓓 ⟹ᵈᶜᵖᵒ 𝓕))
                      S₁ᵈᶜᵖᵒ
    c I α δ = u , v
     where
      u : (i : I) (g : DCPO[ 𝓓 , 𝓔 ]) (d : ⟨ 𝓓 ⟩)
        → pr₁ (pr₁ (α i) d) (pr₁ g d)
          ⊑⟨ 𝓕 ⟩ pr₁ (pr₁ (∐ (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⟹ᵈᶜᵖᵒ 𝓕)) {I} {α} δ) d) (pr₁ g d)
      u i g d = ∐-is-upperbound 𝓕
                (pointwise-family-is-directed 𝓔 𝓕 β ε (pr₁ g d)) i
       where
        β : I → DCPO[ 𝓔 , 𝓕 ]
        β = pointwise-family 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) α d
        ε : is-Directed (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) β
        ε = pointwise-family-is-directed 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) α δ d
      v : (f : DCPO[ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 , 𝓓 ⟹ᵈᶜᵖᵒ 𝓕 ])
        → ((i : I) → S₁ᵈᶜᵖᵒ (α i) ⊑⟨ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ⟹ᵈᶜᵖᵒ (𝓓 ⟹ᵈᶜᵖᵒ 𝓕) ⟩ f)
        → (g : DCPO[ 𝓓 , 𝓔 ]) (d : ⟨ 𝓓 ⟩)
          → pr₁ (pr₁ (∐ (𝓓 ⟹ᵈᶜᵖᵒ (𝓔 ⟹ᵈᶜᵖᵒ 𝓕)) {I} {α} δ) d) (pr₁ g d)
            ⊑⟨ 𝓕 ⟩ (pr₁ (pr₁ f g) d)
      v f l g d = ∐-is-lowerbound-of-upperbounds 𝓕 ε (pr₁ (pr₁ f g) d)
                  (λ (i : I) → l i g d)
       where
        ε : is-Directed 𝓕 (λ (i : I) → pr₁ (pr₁ (S₁ᵈᶜᵖᵒ (α i)) g) d)
        ε = pointwise-family-is-directed 𝓔 𝓕 β φ (underlying-function 𝓓 𝓔 g d)
         where
          β : I → DCPO[ 𝓔 , 𝓕 ]
          β i = underlying-function 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (α i) d
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

In the following we show that the lifting of a set is a 𝓤₀-dcpo with bottom.

-- \begin{code}

--  module LiftingDcpo
--          (𝓣 : Universe)
--          (pe : propext 𝓣)
--         where

--   open import UF-ImageAndSurjection
--   open ImageAndSurjection pt

--   open import Lifting 𝓣
--   open import LiftingMiscelanea 𝓣
--   open import LiftingMiscelanea-PropExt-FunExt 𝓣 pe fe
--   open import LiftingMonad 𝓣

--   module _ {𝓤 : Universe}
--            {X : 𝓤 ̇ }
--            (s : is-set X)
--          where

--    family-value-map : {I : 𝓤₀ ̇ }
--                     → (α : I → 𝓛 X)
--                     → (Σ i ꞉ I , is-defined (α i)) → X
--    family-value-map α (i , d) = value (α i) d

--    directed-family-value-map-is-wconstant : {I : 𝓤₀ ̇ }
--                                           → (α : I → 𝓛 X)
--                                           → (δ : is-directed _⊑'_ α )
--                                           → wconstant (family-value-map α)
--    directed-family-value-map-is-wconstant {I} α δ (i₀ , d₀) (i₁ , d₁) =
--     γ (semidirected-if-directed _⊑'_ α δ i₀ i₁)
--      where
--       f : Σ (λ i → is-defined (α i)) → X
--       f = family-value-map α
--       γ : (∃ k ꞉ I , (α i₀ ⊑' α k) × (α i₁ ⊑' α k)) → f (i₀ , d₀) ≡ f (i₁ , d₁)
--       γ = ∥∥-rec s g
--        where
--         g : (Σ k ꞉ I , (α i₀ ⊑' α k)
--                      × (α i₁ ⊑' α k)) → f (i₀ , d₀) ≡ f (i₁ , d₁)
--         g (k , l , m) =
--          f (i₀ , d₀)                             ≡⟨ refl ⟩
--          value (α i₀) d₀                         ≡⟨ ≡-of-values-from-≡ (l d₀) ⟩
--          value (α k) (≡-to-is-defined (l d₀) d₀) ≡⟨ ≡-of-values-from-≡ ((m d₁) ⁻¹) ⟩
--          value (α i₁) d₁                         ≡⟨ refl ⟩
--          f (i₁ , d₁)                             ∎

--    lifting-sup-value : {I : 𝓤₀ ̇ }
--                      → (α : I → 𝓛 X)
--                      → (δ : is-directed _⊑'_ α )
--                      → (∃ i ꞉ I , is-defined (α i)) → X
--    lifting-sup-value {I} α δ =
--     wconstant-map-to-set-truncation-of-domain-map
--      (Σ i ꞉ I , is-defined (α i))
--      s (family-value-map α) (directed-family-value-map-is-wconstant α δ)

--    lifting-sup : {I : 𝓤₀ ̇ } → (α : I → 𝓛 X) → (δ : is-directed _⊑'_ α) → 𝓛 X
--    lifting-sup {I} α δ =
--     (∃ i ꞉ I , is-defined (α i)) , lifting-sup-value α δ , ∥∥-is-prop

--    lifting-sup-is-upperbound : {I : 𝓤₀ ̇ } → (α : I → 𝓛 X)
--                                (δ : is-directed _⊑'_ α)
--                              → (i : I) → α i ⊑' lifting-sup α δ
--    lifting-sup-is-upperbound {I} α δ i = γ
--     where
--      γ : α i ⊑' lifting-sup α δ
--      γ = ⊑-to-⊑' (f , v)
--       where
--        f : is-defined (α i) → is-defined (lifting-sup α δ)
--        f d = ∣ i , d ∣
--        v : (d : is-defined (α i)) → value (α i) d ≡ value (lifting-sup α δ) (f d)
--        v d = value (α i) d                 ≡⟨ p ⟩
--              lifting-sup-value α δ (f d)   ≡⟨ refl ⟩
--              value (lifting-sup α δ) (f d) ∎
--         where
--          p = wconstant-map-to-set-factors-through-truncation-of-domain
--               (Σ j ꞉ I , is-defined (α j)) s
--               (family-value-map α)
--               (directed-family-value-map-is-wconstant α δ)
--               (i , d)

--    family-defined-somewhere-sup-≡ : {I : 𝓤₀ ̇ } {α : I → 𝓛 X}
--                                   → (δ : is-directed _⊑'_ α)
--                                   → (i : I)
--                                   → is-defined (α i)
--                                   → α i ≡ lifting-sup α δ
--    family-defined-somewhere-sup-≡ {I} {α} δ i d =
--     (lifting-sup-is-upperbound α δ i) d

--    lifting-sup-is-lowerbound-of-upperbounds : {I : 𝓤₀ ̇ }
--                                             → {α : I → 𝓛 X}
--                                             → (δ : is-directed _⊑'_ α)
--                                             → (v : 𝓛 X)
--                                             → ((i : I) → α i ⊑' v)
--                                             → lifting-sup α δ ⊑' v
--    lifting-sup-is-lowerbound-of-upperbounds {I} {α} δ v b = h
--     where
--      h : lifting-sup α δ ⊑' v
--      h d = ∥∥-rec (lifting-of-set-is-set s) g d
--       where
--        g : (Σ i ꞉ I , is-defined (α i)) → lifting-sup α δ ≡ v
--        g (i , dᵢ) = lifting-sup α δ ≡⟨ (family-defined-somewhere-sup-≡ δ i dᵢ) ⁻¹ ⟩
--                     α i             ≡⟨ b i dᵢ ⟩
--                     v               ∎

--    𝓛-DCPO : DCPO {𝓣 ⁺ ⊔ 𝓤} {𝓣 ⁺ ⊔ 𝓤}
--    𝓛-DCPO = 𝓛 X , _⊑'_ , sl , p , r , t , a , c
--     where
--      sl : is-set (𝓛 X)
--      sl = lifting-of-set-is-set s
--      p : is-prop-valued (_⊑'_)
--      p _ _ = ⊑'-prop-valued s
--      r : is-reflexive (_⊑'_)
--      r _ = ⊑'-is-reflexive
--      a : is-antisymmetric (_⊑'_)
--      a _ _ = ⊑'-is-antisymmetric
--      t : is-transitive (_⊑'_)
--      t _ _ _ = ⊑'-is-transitive
--      c : (I : 𝓤₀ ̇ ) (α : I → 𝓛 X) → is-directed _⊑'_ α → has-sup _⊑'_ α
--      c I α δ = lifting-sup α δ ,
--                lifting-sup-is-upperbound α δ ,
--                lifting-sup-is-lowerbound-of-upperbounds δ

--    𝓛-DCPO⊥ : DCPO⊥ {𝓣 ⁺ ⊔ 𝓤} {𝓣 ⁺ ⊔ 𝓤}
--    𝓛-DCPO⊥ = 𝓛-DCPO , ⊥ , λ _ → unique-from-𝟘

-- \end{code}

-- Now that we have the lifting as a dcpo, we prove that the lifting functor and
-- Kleisli extension yield continuous maps

-- \begin{code}

--   module _ {𝓤 : Universe}
--            {X : 𝓤 ̇ }
--            (s₀ : is-set X)
--            {𝓥 : Universe}
--            {Y : 𝓥 ̇ }
--            (s₁ : is-set Y)
--          where

--    ♯-is-monotone : (f : X → 𝓛 Y) → is-monotone (𝓛-DCPO s₀) (𝓛-DCPO s₁) (f ♯)
--    ♯-is-monotone f l m ineq d = ap (f ♯) (ineq (♯-is-defined f l d))

--    ♯-is-continuous : (f : X → 𝓛 Y) → is-continuous (𝓛-DCPO s₀) (𝓛-DCPO s₁) (f ♯)
--    ♯-is-continuous f I α δ = u , v
--     where
--      u : (i : I) → (f ♯) (α i) ⊑⟨ (𝓛-DCPO s₁) ⟩ (f ♯) (∐ (𝓛-DCPO s₀) δ)
--      u i = ♯-is-monotone f (α i) (∐ (𝓛-DCPO s₀) δ)
--            (∐-is-upperbound (𝓛-DCPO s₀) δ i)
--      v : (m : ⟨ 𝓛-DCPO s₁ ⟩)
--        → ((i : I) → (f ♯) (α i) ⊑⟨ (𝓛-DCPO s₁) ⟩ m)
--        → (f ♯) (∐ (𝓛-DCPO s₀) δ) ⊑⟨ (𝓛-DCPO s₁) ⟩ m
--      v m ineqs d =
--       ∥∥-rec (lifting-of-set-is-set s₁) g (♯-is-defined f (∐ (𝓛-DCPO s₀) δ) d)
--        where
--         g : (Σ i ꞉ I , is-defined (α i)) → (f ♯) (∐ (𝓛-DCPO s₀) δ) ≡ m
--         g (i , dᵢ) = (f ♯) (∐ (𝓛-DCPO s₀) δ) ≡⟨ h i dᵢ ⟩
--                      (f ♯) (α i)             ≡⟨ ineqs i (≡-to-is-defined (h i dᵢ) d) ⟩
--                      m                       ∎
--          where
--           h : (i : I) → is-defined (α i) → (f ♯) (∐ (𝓛-DCPO s₀) δ) ≡ (f ♯) (α i)
--           h i d = ap (f ♯) ((family-defined-somewhere-sup-≡ s₀ δ i d) ⁻¹)

--    𝓛̇-continuous : (f : X → Y) → is-continuous (𝓛-DCPO s₀) (𝓛-DCPO s₁) (𝓛̇ f)
--    𝓛̇-continuous f = transport
--                      (is-continuous (𝓛-DCPO s₀) (𝓛-DCPO s₁))
--                      (dfunext fe (𝓛̇-♯-∼ f))
--                      (♯-is-continuous (η ∘ f))

-- \end{code}

-- Finally, we construct the ifZero function, specific to the lifting of ℕ.
-- Again, this will be used in ScottModelOfPCF.

-- The continuity proofs are not very appealing and the second proof could perhaps
-- be simplified by exploiting the "symmetry" of ifZero: for example,
-- ifZero a b 0 ≡ ifZero b a 1).
-- The second proof is essentially identical to the
-- first proof; the only difference is that we have to introduce an additional
-- parameter in the second proof. We leave simplifications of the proofs for
-- future work.

-- \begin{code}

--   𝓛ᵈℕ : DCPO⊥
--   𝓛ᵈℕ = 𝓛-DCPO⊥ ℕ-is-set

--   ⦅ifZero⦆₀ : 𝓛 ℕ → 𝓛 ℕ → ℕ → 𝓛 ℕ
--   ⦅ifZero⦆₀ a b zero     = a
--   ⦅ifZero⦆₀ a b (succ n) = b

--   ⦅ifZero⦆₁ : 𝓛 ℕ → 𝓛 ℕ → DCPO⊥[ 𝓛ᵈℕ , 𝓛ᵈℕ ]
--   ⦅ifZero⦆₁ a b =
--    (⦅ifZero⦆₀ a b) ♯ , ♯-is-continuous ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ a b)

--   ⦅ifZero⦆₂ : 𝓛 ℕ → DCPO⊥[ 𝓛ᵈℕ , 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ]
--   ⦅ifZero⦆₂ a = ⦅ifZero⦆₁ a , c
--    where
--     c : is-continuous ⟪ 𝓛ᵈℕ ⟫ ⟪ 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ⟫ (⦅ifZero⦆₁ a)
--     c I α δ = u , v
--      where
--       u : (i : I) (l : 𝓛 ℕ) (d : is-defined (((⦅ifZero⦆₀ a (α i)) ♯) l))
--         → ((⦅ifZero⦆₀ a (α i)) ♯) l ≡ ((⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) ♯) l
--       u i l d = ((⦅ifZero⦆₀ a (α i)) ♯) l              ≡⟨ q₀ ⟩
--                 ⦅ifZero⦆₀ a (α i) (value l e)          ≡⟨ q₁ ⟩
--                 ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e) ≡⟨ q₂ ⟩
--                 ((⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) ♯) l     ∎
--        where
--         e : is-defined l
--         e = ♯-is-defined (⦅ifZero⦆₀ a (α i)) l d
--         p₀ : value l e ≡ zero → ⦅ifZero⦆₀ a (α i) (value l e)
--            ≡ ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e)
--         p₀ q = ⦅ifZero⦆₀ a (α i) (value l e)
--                   ≡⟨ ap (⦅ifZero⦆₀ a (α i)) q ⟩
--                ⦅ifZero⦆₀ a (α i) zero
--                   ≡⟨ refl ⟩
--                a
--                   ≡⟨ refl ⟩
--                ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) zero
--                   ≡⟨ ap (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) (q ⁻¹) ⟩
--                ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e)
--                   ∎
--         pₛ : (n : ℕ) → value l e ≡ succ n → ⦅ifZero⦆₀ a (α i) (value l e)
--                                           ≡ ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e)
--         pₛ n q = ⦅ifZero⦆₀ a (α i) (value l e)
--                     ≡⟨ ap (⦅ifZero⦆₀ a (α i)) q ⟩
--                  ⦅ifZero⦆₀ a (α i) (succ n)
--                     ≡⟨ refl ⟩
--                  α i
--                     ≡⟨ family-defined-somewhere-sup-≡ ℕ-is-set δ i e₁ ⟩
--                  ∐ ⟪ 𝓛ᵈℕ ⟫ δ
--                     ≡⟨ refl ⟩
--                  ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (succ n)
--                      ≡⟨ ap (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) (q ⁻¹) ⟩
--                  ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e)
--                     ∎
--          where
--           e₁ : is-defined (α i)
--           e₁ = ≡-to-is-defined (ap (⦅ifZero⦆₀ a (α i)) q)
--                (≡-to-is-defined (♯-on-total-element (⦅ifZero⦆₀ a (α i)) {l} e) d)
--         q₀ = ♯-on-total-element (⦅ifZero⦆₀ a (α i)) e
--         q₁ = ℕ-cases {𝓣 ⁺} {λ (n : ℕ) → ⦅ifZero⦆₀ a (α i) n
--                                       ≡ ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) n} (value l e) p₀ pₛ
--         q₂ = (♯-on-total-element (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) {l} e) ⁻¹
--       v : (f : DCPO⊥[ 𝓛ᵈℕ , 𝓛ᵈℕ ])
--         → ((i : I) → ⦅ifZero⦆₁ a (α i) ⊑⟨ ⟪ 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ⟫ ⟩ f)
--         → (l : 𝓛 ℕ) (d : is-defined (((⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) ♯) l))
--         → ((⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) ♯) l ≡ pr₁ f l
--       v f ineqs l d = ((⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) ♯) l
--                         ≡⟨ ♯-on-total-element (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) {l} e ⟩
--                       ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e)
--                         ≡⟨ ℕ-cases {𝓣 ⁺} {λ (n : ℕ) → ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) n
--                                                     ≡ pr₁ f l}
--                             (value l e) p₀ pₛ ⟩
--                       pr₁ f l
--                         ∎
--        where
--         e : is-defined l
--         e = ♯-is-defined (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) l d
--         p₀ : value l e ≡ zero → ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e) ≡ pr₁ f l
--         p₀ q = ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e)
--                   ≡⟨ ap (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) q ⟩
--                ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) zero
--                   ≡⟨ refl ⟩
--                a
--                   ≡⟨ r ⟩
--                pr₁ f l
--                   ∎
--          where
--           r : a ≡ pr₁ f l
--           r = ∥∥-rec (lifting-of-set-is-set ℕ-is-set)
--                h (inhabited-if-Directed ⟪ 𝓛ᵈℕ ⟫ α δ)
--            where
--             h : (i : I) → a ≡ pr₁ f l
--             h i = a                         ≡⟨ g ⟩
--                   ((⦅ifZero⦆₀ a (α i)) ♯) l ≡⟨ ineqs i l e₀ ⟩
--                   pr₁ f l                   ∎
--              where
--               g = a
--                      ≡⟨ refl ⟩
--                   ⦅ifZero⦆₀ a (α i) zero
--                      ≡⟨ ap (⦅ifZero⦆₀ a (α i)) (q ⁻¹) ⟩
--                   ⦅ifZero⦆₀ a (α i) (value l e)
--                      ≡⟨ (♯-on-total-element (⦅ifZero⦆₀ a (α i)) e) ⁻¹ ⟩
--                   ((⦅ifZero⦆₀ a (α i)) ♯) l
--                      ∎
--               e₀ : is-defined (((⦅ifZero⦆₀ a (α i)) ♯) l)
--               e₀ = ≡-to-is-defined (g' ∙ g) d
--                where
--                 g' = ((⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) ♯) l
--                          ≡⟨ ♯-on-total-element (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) {l} e ⟩
--                      ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e)
--                          ≡⟨ ap (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) q ⟩
--                      ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) zero
--                          ≡⟨ refl ⟩
--                      a
--                          ∎

--         pₛ : (m : ℕ) → value l e ≡ succ m → ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e)
--                                           ≡ pr₁ f l
--         pₛ m q = ∥∥-rec (lifting-of-set-is-set ℕ-is-set) h eₛ
--          where
--           g : (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) ♯) l ≡ ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e)
--           g = ♯-on-total-element (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) {l} e
--           g' = ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e)
--                   ≡⟨ ap (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) q ⟩
--                ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (succ m)
--                   ≡⟨ refl ⟩
--               ∐ ⟪ 𝓛ᵈℕ ⟫ δ
--                   ∎
--           eₛ : is-defined (∐ ⟪ 𝓛ᵈℕ ⟫ δ)
--           eₛ = ≡-to-is-defined (g ∙ g') d
--           h : (Σ i ꞉ I , is-defined (α i))
--             → ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e) ≡ pr₁ f l
--           h (i , dᵢ) = ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e)
--                           ≡⟨ g' ⟩
--                        ∐ ⟪ 𝓛ᵈℕ ⟫ δ
--                           ≡⟨ (family-defined-somewhere-sup-≡ ℕ-is-set δ i dᵢ) ⁻¹ ⟩
--                        α i
--                           ≡⟨ h' ⟩
--                        ((⦅ifZero⦆₀ a (α i)) ♯) l
--                           ≡⟨ ineqs i l (≡-to-is-defined h' dᵢ) ⟩
--                        pr₁ f l
--                           ∎
--            where
--             h' = α i
--                     ≡⟨ refl ⟩
--                  ⦅ifZero⦆₀ a (α i) (succ m)
--                     ≡⟨ ap (⦅ifZero⦆₀ a (α i)) (q ⁻¹) ⟩
--                  ⦅ifZero⦆₀ a (α i) (value l e)
--                     ≡⟨ (♯-on-total-element (⦅ifZero⦆₀ a (α i)) {l} e) ⁻¹ ⟩
--                  ((⦅ifZero⦆₀ a (α i)) ♯) l
--                     ∎

--   ⦅ifZero⦆ : DCPO⊥[ 𝓛ᵈℕ , 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ  ]
--   ⦅ifZero⦆ = ⦅ifZero⦆₂ , c
--    where
--     c : is-continuous ⟪ 𝓛ᵈℕ ⟫ ⟪ 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ⟫ ⦅ifZero⦆₂
--     c I α δ = u , v
--      where
--       u : (i : I) (b : 𝓛 ℕ) (l : 𝓛 ℕ) (d : is-defined (((⦅ifZero⦆₀ (α i) b) ♯) l))
--         → ((⦅ifZero⦆₀ (α i) b) ♯) l ≡ ((⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) ♯) l
--       u i b l d = ((⦅ifZero⦆₀ (α i) b) ♯) l
--                      ≡⟨ ♯-on-total-element (⦅ifZero⦆₀ (α i) b) e ⟩
--                   ⦅ifZero⦆₀ (α i) b (value l e)
--                      ≡⟨ ℕ-cases {𝓣 ⁺} {λ (n : ℕ) →  ⦅ifZero⦆₀ (α i) b n
--                                                  ≡ ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b n}
--                           (value l e) p₀ pₛ ⟩
--                   ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)
--                      ≡⟨ (♯-on-total-element (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) {l} e) ⁻¹ ⟩
--                   ((⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) ♯) l
--                      ∎
--        where
--         e : is-defined l
--         e = ♯-is-defined (⦅ifZero⦆₀ (α i) b) l d
--         p₀ : value l e ≡ zero → ⦅ifZero⦆₀ (α i) b (value l e)
--                               ≡ ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)
--         p₀ q = ⦅ifZero⦆₀ (α i) b (value l e)
--                   ≡⟨ ap (⦅ifZero⦆₀ (α i) b) q ⟩
--                ⦅ifZero⦆₀ (α i) b zero
--                   ≡⟨ refl ⟩
--                α i
--                   ≡⟨ family-defined-somewhere-sup-≡ ℕ-is-set δ i e₁ ⟩
--                ∐ ⟪ 𝓛ᵈℕ ⟫ δ
--                   ≡⟨ refl ⟩
--                ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b zero
--                   ≡⟨ ap (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) (q ⁻¹) ⟩
--                ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)
--                   ∎
--          where
--           e₁ : is-defined (α i)
--           e₁ = ≡-to-is-defined (ap (⦅ifZero⦆₀ (α i) b) q)
--                (≡-to-is-defined (♯-on-total-element (⦅ifZero⦆₀ (α i) b) {l} e) d)
--         pₛ : (n : ℕ) → value l e ≡ succ n → ⦅ifZero⦆₀ (α i) b (value l e)
--                                           ≡ ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)
--         pₛ n q = ⦅ifZero⦆₀ (α i) b (value l e)
--                     ≡⟨ ap (⦅ifZero⦆₀ (α i) b) q ⟩
--                  ⦅ifZero⦆₀ (α i) b (succ n)
--                     ≡⟨ refl ⟩
--                  b
--                     ≡⟨ refl ⟩
--                  ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (succ n)
--                     ≡⟨ ap (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) (q ⁻¹) ⟩
--                  ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)
--                     ∎

--       v : (f : DCPO⊥[ 𝓛ᵈℕ , 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ])
--         → ((i : I) (b : 𝓛 ℕ) → ⦅ifZero⦆₁ (α i) b ⊑⟨ ⟪ 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ⟫ ⟩ pr₁ f b)
--         → (b : 𝓛 ℕ) (l : 𝓛 ℕ) (d : is-defined (((⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) ♯) l))
--         → ((⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) ♯) l ≡ pr₁ (pr₁ f b) l
--       v f ineqs b l d = ((⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) ♯) l
--                            ≡⟨ ♯-on-total-element (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) {l} e ⟩
--                         ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)
--                            ≡⟨ ℕ-cases {𝓣 ⁺} {λ (n : ℕ) →  ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b n
--                                                        ≡ pr₁ (pr₁ f b) l}
--                                 (value l e) p₀ pₛ ⟩
--                         pr₁ (pr₁ f b) l
--                            ∎
--        where
--         e : is-defined l
--         e = ♯-is-defined (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) l d
--         p₀ : value l e ≡ zero → ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e) ≡ pr₁ (pr₁ f b) l
--         p₀ q = ∥∥-rec (lifting-of-set-is-set ℕ-is-set) h e₀
--          where
--           g : (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b ♯) l ≡ ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)
--           g = ♯-on-total-element (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) {l} e
--           g' = ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e) ≡⟨ ap (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) q ⟩
--                ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b zero        ≡⟨ refl ⟩
--                ∐ ⟪ 𝓛ᵈℕ ⟫ δ                           ∎
--           e₀ : is-defined (∐ ⟪ 𝓛ᵈℕ ⟫ δ)
--           e₀ = ≡-to-is-defined (g ∙ g') d
--           h : (Σ i ꞉ I , is-defined (α i))
--             → ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e) ≡ pr₁ (pr₁ f b) l
--           h (i , dᵢ) = ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)
--                           ≡⟨ g' ⟩
--                        ∐ ⟪ 𝓛ᵈℕ ⟫ δ
--                           ≡⟨ (family-defined-somewhere-sup-≡ ℕ-is-set δ i dᵢ) ⁻¹ ⟩
--                        α i
--                           ≡⟨ h' ⟩
--                        ((⦅ifZero⦆₀ (α i) b) ♯) l
--                           ≡⟨ ineqs i b l (≡-to-is-defined h' dᵢ) ⟩
--                        pr₁ (pr₁ f b) l
--                           ∎
--            where
--             h' = α i
--                     ≡⟨ refl ⟩
--                  ⦅ifZero⦆₀ (α i) b zero
--                     ≡⟨ ap (⦅ifZero⦆₀ (α i) b) (q ⁻¹) ⟩
--                  ⦅ifZero⦆₀ (α i) b (value l e)
--                     ≡⟨ (♯-on-total-element (⦅ifZero⦆₀ (α i) b) {l} e) ⁻¹ ⟩
--                  ((⦅ifZero⦆₀ (α i) b) ♯) l
--                     ∎

--         pₛ : (m : ℕ) → value l e ≡ succ m → ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)
--                                           ≡ pr₁ (pr₁ f b) l
--         pₛ m q = ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)
--                     ≡⟨ ap (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) q ⟩
--                  ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (succ m)
--                     ≡⟨ refl ⟩
--                  b
--                     ≡⟨ r ⟩
--                  pr₁ (pr₁ f b) l
--                     ∎
--          where
--           r : b ≡ pr₁ (pr₁ f b) l
--           r = ∥∥-rec (lifting-of-set-is-set ℕ-is-set) h
--                (inhabited-if-Directed ⟪ 𝓛ᵈℕ ⟫ α δ)
--            where
--             h : (i : I) → b ≡ pr₁ (pr₁ f b) l
--             h i = b                         ≡⟨ g ⟩
--                   ((⦅ifZero⦆₀ (α i) b) ♯) l ≡⟨ ineqs i b l eₛ ⟩
--                   pr₁ (pr₁ f b) l          ∎
--              where
--               g = b
--                      ≡⟨ refl ⟩
--                   ⦅ifZero⦆₀ (α i) b (succ m)
--                      ≡⟨ ap (⦅ifZero⦆₀ (α i) b) (q ⁻¹) ⟩
--                   ⦅ifZero⦆₀ (α i) b (value l e)
--                      ≡⟨ (♯-on-total-element (⦅ifZero⦆₀ (α i) b) e) ⁻¹ ⟩
--                   ((⦅ifZero⦆₀ (α i) b) ♯) l
--                      ∎
--               eₛ : is-defined (((⦅ifZero⦆₀ (α i) b) ♯) l)
--               eₛ = ≡-to-is-defined (g' ∙ g) d
--                where
--                 g' = ((⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) ♯) l
--                         ≡⟨ ♯-on-total-element (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) {l} e ⟩
--                      ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)
--                         ≡⟨ ap (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) q ⟩
--                      ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (succ m)
--                         ≡⟨ refl ⟩
--                      b
--                         ∎

-- \end{code}
