Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
April 2024. Major additions and refactorings in September—December 2024.

We give an abstract construction of ordinal exponentiation using suprema of
ordinals.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.Supremum
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import MLTT.Spartan

open import UF.Base
open import UF.ImageAndSurjection pt
open import UF.Subsingletons
open import UF.UniverseEmbedding

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Exponentiation.Specification ua pt sr
open import Ordinals.Maps
open import Ordinals.MultiplicationProperties ua
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying

open PropositionalTruncation pt
open suprema pt sr

\end{code}

We define
  α ^ₒ β = sup {1 + ⟨ β ⟩} (inl _ ↦ 𝟙ₒ; inr b ↦ α ^ₒ (β ↓ b) ×ₒ α)
by transfinite recursion on β.

As we will show, this gives a well defined ordinal exponentiation function
whenever α ⊵ 𝟙ₒ. Moreover, many desirable properties also hold in the absence of
this assumption)

\begin{code}

exp-bundled :
   (α : Ordinal 𝓤)
 → Σ f ꞉ (Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥)) ,
     ((β : Ordinal 𝓥)
       → f β ＝ sup {I = 𝟙 + ⟨ β ⟩} (cases (λ _ → 𝟙ₒ) (λ b → f (β ↓ b) ×ₒ α)))
exp-bundled {𝓤} {𝓥} α =
 transfinite-recursion-on-OO-bundled
  (Ordinal (𝓤 ⊔ 𝓥))
  (λ β ih → sup {I = 𝟙 {𝓤} + ⟨ β ⟩} (cases (λ _ → 𝟙ₒ) λ b → ih b ×ₒ α))

abstract
 _^ₒ_ : (α : Ordinal 𝓤) → (β : Ordinal 𝓥) → Ordinal (𝓤 ⊔ 𝓥)
 _^ₒ_ α = pr₁ (exp-bundled α)

 infixr 8 _^ₒ_

 ^ₒ-behaviour :
    (α : Ordinal 𝓤) (β : Ordinal 𝓥)
  → α ^ₒ β
    ＝ sup {I = 𝟙 {𝓤} + ⟨ β ⟩} (cases (λ _ → 𝟙ₒ) (λ b → α ^ₒ (β ↓ b) ×ₒ α))
 ^ₒ-behaviour α = pr₂ (exp-bundled α)

 module _
  (α : Ordinal 𝓤)
  (β : Ordinal 𝓥)
  where

  ^ₒ-family : 𝟙 {𝓤} + ⟨ β ⟩ → Ordinal (𝓤 ⊔ 𝓥)
  ^ₒ-family = cases (λ _ → 𝟙ₒ) (λ b → α ^ₒ (β ↓ b) ×ₒ α)

  ^ₒ-is-upper-bound : (x : 𝟙 + ⟨ β ⟩) → ^ₒ-family x ⊴ α ^ₒ β
  ^ₒ-is-upper-bound x =
   transport⁻¹
    (^ₒ-family x ⊴_)
    (^ₒ-behaviour α β)
    (sup-is-upper-bound ^ₒ-family x)

  ^ₒ-is-upper-bound₁ : 𝟙ₒ ⊴ α ^ₒ β
  ^ₒ-is-upper-bound₁ = ^ₒ-is-upper-bound (inl ⋆)

  ^ₒ-is-upper-bound₂ : {b : ⟨ β ⟩} → α ^ₒ (β ↓ b) ×ₒ α ⊴ α ^ₒ β
  ^ₒ-is-upper-bound₂ {b} = ^ₒ-is-upper-bound (inr b)

  ^ₒ-is-lower-bound-of-upper-bounds :
     (γ : Ordinal (𝓤 ⊔ 𝓥))
   → 𝟙ₒ ⊴ γ
   → ((b : ⟨ β ⟩) → α ^ₒ (β ↓ b) ×ₒ α ⊴ γ)
   → α ^ₒ β ⊴ γ
  ^ₒ-is-lower-bound-of-upper-bounds γ l₁ l₂ =
   transport⁻¹ (_⊴ γ)
    (^ₒ-behaviour α β)
    (sup-is-lower-bound-of-upper-bounds
      ^ₒ-family γ (dep-cases (λ _ → l₁) l₂))

\end{code}

Since ^ₒ is defined as a supremum which in turn can be realized as a quotient,
it enjoyes an induction principle which we formulate and prove below.

\begin{code}

  ^ₒ-⊥ : ⟨ α ^ₒ β ⟩
  ^ₒ-⊥ = [ 𝟙ₒ , α ^ₒ β ]⟨ ^ₒ-is-upper-bound₁ ⟩ ⋆

  ×ₒ-to-^ₒ : {b : ⟨ β ⟩} → ⟨ α ^ₒ (β ↓ b) ×ₒ α ⟩ → ⟨ α ^ₒ β ⟩
  ×ₒ-to-^ₒ {b} = [ α ^ₒ (β ↓ b) ×ₒ α , α ^ₒ β ]⟨ ^ₒ-is-upper-bound₂ ⟩

  private
   ι : (x : 𝟙 + ⟨ β ⟩) → ⟨ ^ₒ-family x ⟩ → ⟨ α ^ₒ β ⟩
   ι x = [ ^ₒ-family x , α ^ₒ β ]⟨ ^ₒ-is-upper-bound x ⟩

   ι-is-jointly-surjective :
      (e : ⟨ α ^ₒ β ⟩)
     → ∃ x ꞉ 𝟙 + ⟨ β ⟩ , Σ y ꞉ ⟨ ^ₒ-family x ⟩ , ι x y ＝ e
   ι-is-jointly-surjective e = ∥∥-functor II III
    where
     σ = λ (x : 𝟙 + ⟨ β ⟩)
           → [ ^ₒ-family x , sup ^ₒ-family ]⟨ sup-is-upper-bound ^ₒ-family x ⟩

     I : {γ : Ordinal (𝓤 ⊔ 𝓥)} (e : ⟨ γ ⟩)
         (p : γ ＝ sup ^ₒ-family) {x : 𝟙 + ⟨ β ⟩} {y : ⟨ ^ₒ-family x ⟩}
       → σ x y ＝ Idtofun (ap ⟨_⟩ p) e
       → [ ^ₒ-family x , γ ]⟨
            transport⁻¹ (^ₒ-family x ⊴_) p (sup-is-upper-bound ^ₒ-family x) ⟩ y
         ＝ e
     I _ refl = id

     p = ^ₒ-behaviour α β
     q = ap ⟨_⟩ p
     e' = Idtofun q e

     II : (Σ x ꞉ 𝟙 + ⟨ β ⟩ , Σ y ꞉ ⟨ ^ₒ-family x ⟩ , σ x y ＝ e')
        → (Σ x ꞉ 𝟙 + ⟨ β ⟩ , Σ y ꞉ ⟨ ^ₒ-family x ⟩ , ι x y ＝ e)
     II (x , y , eq) = x , y , I e p eq

     III : ∃ x ꞉ 𝟙 + ⟨ β ⟩ , Σ y ꞉ ⟨ ^ₒ-family x ⟩ , σ x y ＝ e'
     III = sup-is-upper-bound-jointly-surjective ^ₒ-family (Idtofun q e)

  ^ₒ-induction : {𝓦 : Universe} (P : ⟨ α ^ₒ β ⟩ → 𝓦 ̇  )
               → ((e : ⟨ α ^ₒ β ⟩) → is-prop (P e))
               → P ^ₒ-⊥
               → ((b : ⟨ β ⟩) (y : ⟨ α ^ₒ (β ↓ b) ×ₒ α ⟩) → P (×ₒ-to-^ₒ y))
               → (e : ⟨ α ^ₒ β ⟩) → P e
  ^ₒ-induction P P-is-prop-valued P-⊥ P-component =
   surjection-induction σ σ-is-surjection P P-is-prop-valued ρ
    where
     σ : (Σ x ꞉ 𝟙 + ⟨ β ⟩ , ⟨ ^ₒ-family x ⟩) → ⟨ α ^ₒ β ⟩
     σ (x , y) = ι x y

     σ-is-surjection : is-surjection σ
     σ-is-surjection e =
      ∥∥-functor
       (λ (x , y , p) → (x , y) , p)
       (ι-is-jointly-surjective e)

     ρ : ((x , y) : domain σ) → P (ι x y)
     ρ (inl ⋆ , ⋆) = P-⊥
     ρ (inr b , y) = P-component b y

\end{code}

We introduce a more descriptive name for the fact that our exponentiation
function is always at least 𝟙ₒ and derive the corollary that 𝟘ₒ is strictly
below any exponentiated ordinal.

\begin{code}

^ₒ-has-least-element : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → 𝟙ₒ ⊴ α ^ₒ β
^ₒ-has-least-element = ^ₒ-is-upper-bound₁

^ₒ-is-positive : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → 𝟘ₒ ⊲ α ^ₒ β
^ₒ-is-positive α β =
 ⊲-⊴-gives-⊲ 𝟘ₒ 𝟙ₒ (α ^ₒ β) 𝟘ₒ-⊲-𝟙ₒ (^ₒ-has-least-element α β)

\end{code}

The exponentiation function meets the zero specification as formulated in
Ordinals.Exponentiation.Specification.

\begin{code}

^ₒ-satisfies-zero-specification : {𝓤 𝓥 : Universe} (α : Ordinal 𝓤)
                                → exp-specification-zero {𝓤} {𝓥} α (α ^ₒ_)
^ₒ-satisfies-zero-specification {𝓤} {𝓥} α = ⊴-antisym (α ^ₒ 𝟘ₒ) 𝟙ₒ I II
 where
  I : α ^ₒ 𝟘ₒ ⊴ 𝟙ₒ
  I = ^ₒ-is-lower-bound-of-upper-bounds α 𝟘ₒ 𝟙ₒ (⊴-refl 𝟙ₒ) 𝟘-induction

  II : 𝟙ₒ ⊴ α ^ₒ 𝟘ₒ
  II = ^ₒ-has-least-element α 𝟘ₒ

\end{code}

The exponentiation function meets the successor specification (as formulated in
Ordinals.Exponentiation.Specification) for base ordinals α ⊵ 𝟙ₒ.

The proof relies on the following general lemma.

\begin{code}

^ₒ-×ₒ-right-⊴ : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (γ : Ordinal 𝓦)
              → 𝟙ₒ {𝓣} ⊴ γ
              → α ^ₒ β ⊴ α ^ₒ β ×ₒ γ
^ₒ-×ₒ-right-⊴ α β γ l =
 ⊴-trans (α ^ₒ β) (α ^ₒ β ×ₒ 𝟙ₒ) (α ^ₒ β ×ₒ γ)
  (＝-to-⊴ (α ^ₒ β) (α ^ₒ β ×ₒ 𝟙ₒ) ((𝟙ₒ-right-neutral-×ₒ (α ^ₒ β)) ⁻¹))
  (×ₒ-right-monotone-⊴ (α ^ₒ β) 𝟙ₒ γ (𝟙ₒ-⊴-shift γ l))

^ₒ-satisfies-succ-specification : {𝓤 𝓥 : Universe} (α : Ordinal 𝓤)
                                → 𝟙ₒ {𝓤} ⊴ α
                                → exp-specification-succ {𝓤} {𝓥} α (α ^ₒ_)
^ₒ-satisfies-succ-specification {𝓤} {𝓥} α l β =
 ⊴-antisym (α ^ₒ (β +ₒ 𝟙ₒ)) (α ^ₒ β ×ₒ α) I II
  where
   I : α ^ₒ (β +ₒ 𝟙ₒ) ⊴ α ^ₒ β ×ₒ α
   I = ^ₒ-is-lower-bound-of-upper-bounds α (β +ₒ 𝟙ₒ) (α ^ₒ β ×ₒ α) I₁ I₂
    where
     I₁ : 𝟙ₒ ⊴ α ^ₒ β ×ₒ α
     I₁ = ⊴-trans 𝟙ₒ (α ^ₒ β) (α ^ₒ β ×ₒ α)
           (^ₒ-is-upper-bound₁ α β)
           (^ₒ-×ₒ-right-⊴ α β α l)
     I₂ : (x : ⟨ β +ₒ 𝟙ₒ ⟩) → α ^ₒ ((β +ₒ 𝟙ₒ) ↓ x) ×ₒ α ⊴ α ^ₒ β ×ₒ α
     I₂ (inl b) = ⊴-trans
                   (α ^ₒ ((β +ₒ 𝟙ₒ) ↓ inl b) ×ₒ α)
                   (α ^ₒ β)
                   (α ^ₒ β ×ₒ α)
                   (transport (_⊴ α ^ₒ β)
                     (ap (λ - → α ^ₒ - ×ₒ α) (+ₒ-↓-left b))
                     (^ₒ-is-upper-bound₂ α β))
                   (^ₒ-×ₒ-right-⊴ α β α l)
     I₂ (inr ⋆) = ＝-to-⊴
                   (α ^ₒ ((β +ₒ 𝟙ₒ) ↓ inr ⋆) ×ₒ α)
                   (α ^ₒ β ×ₒ α)
                   (ap (λ - → α ^ₒ - ×ₒ α) (successor-lemma-right β))
   II : α ^ₒ β ×ₒ α ⊴ α ^ₒ (β +ₒ 𝟙ₒ)
   II = transport
         (_⊴ α ^ₒ (β +ₒ 𝟙ₒ))
         (ap (λ - → α ^ₒ - ×ₒ α) (successor-lemma-right β))
         (^ₒ-is-upper-bound₂ α (β +ₒ 𝟙ₒ))

\end{code}

The exponentiation function meets the supremum specification (as formulated in
Ordinals.Exponentiation.Specification).

The proof relies on the following monotonicity property of the exponentiation.

\begin{code}

^ₒ-monotone-in-exponent : (α : Ordinal 𝓤) (β γ : Ordinal 𝓥)
                        → β ⊴ γ → α ^ₒ β ⊴ α ^ₒ γ
^ₒ-monotone-in-exponent {𝓤} {𝓥} α β γ 𝕗@(f , _) =
 transport₂⁻¹ _⊴_
  (^ₒ-behaviour α β) (^ₒ-behaviour α γ)
  (transport (λ - → sup - ⊴ sup G) I (sup-composition-⊴ f' G))
  where
   F = ^ₒ-family α β
   G = ^ₒ-family α γ

   f' : 𝟙 + ⟨ β ⟩ → 𝟙 + ⟨ γ ⟩
   f' = cases (λ _ → inl ⋆) (λ b → inr (f b))

   initial-segments-agree : (b : ⟨ β ⟩) → β ↓ b ＝ γ ↓ f b
   initial-segments-agree b = simulations-preserve-↓ β γ 𝕗 b

   I : G ∘ f' ＝ F
   I = dfunext fe' II
    where
     II : (x : 𝟙 + ⟨ β ⟩) → G (f' x) ＝ F x
     II (inl ⋆) = refl
     II (inr b) = ap (λ - → α ^ₒ - ×ₒ α) (initial-segments-agree b ⁻¹)

^ₒ-monotone-in-exponent' : (α : Ordinal 𝓤)
                         → is-monotone (OO 𝓥) (OO (𝓤 ⊔ 𝓥)) (α ^ₒ_)
^ₒ-monotone-in-exponent' {𝓤} {𝓥} α β γ l =
 ⊴-gives-≼ (α ^ₒ β) (α ^ₒ γ) (^ₒ-monotone-in-exponent α β γ (≼-gives-⊴ β γ l))

^ₒ-satisfies-sup-specification-generalized :
   {𝓤 𝓥 : Universe} (α : Ordinal 𝓤)
 → exp-specification-sup-generalized {𝓤} {𝓥} α (α ^ₒ_)
^ₒ-satisfies-sup-specification-generalized {𝓤} {𝓥} α _ {S} S-inh F =
 ⊴-antisym (α ^ₒ sup F) (sup (λ - → α ^ₒ F (lower -))) I II
  where
   II : sup (λ - → α ^ₒ F (lower -)) ⊴ α ^ₒ sup F
   II = sup-is-lower-bound-of-upper-bounds
         (λ - → α ^ₒ F (lower -))
         (α ^ₒ sup F)
         (λ i → ^ₒ-monotone-in-exponent α (F (lower i)) (sup F)
                 (sup-is-upper-bound F (lower i)))

   I : α ^ₒ sup F ⊴ sup (λ - → α ^ₒ F (lower -))
   I = ^ₒ-is-lower-bound-of-upper-bounds
        α
        (sup F)
        (sup (λ - → α ^ₒ F (lower -)))
        I₁
        I₂
    where
     I₁ : 𝟙ₒ ⊴ sup (λ - → α ^ₒ F (lower -))
     I₁ = ∥∥-rec (⊴-is-prop-valued 𝟙ₒ (sup (λ - → α ^ₒ F (lower -)))) I₁' S-inh
      where
       I₁' : S → 𝟙ₒ ⊴ sup (λ - → α ^ₒ F (lower -))
       I₁' s₀ = ⊴-trans
                 𝟙ₒ
                 (α ^ₒ (F s₀))
                 (sup (λ - → α ^ₒ F (lower -)))
                 (^ₒ-is-upper-bound₁ α (F s₀))
                 (sup-is-upper-bound (λ - → α ^ₒ F (lower -)) (lift 𝓤 s₀))
     I₂ : (y : ⟨ sup F ⟩)
        → α ^ₒ (sup F ↓ y) ×ₒ α ⊴ sup (λ - → α ^ₒ F (lower -))
     I₂ y = ∥∥-rec
             (⊴-is-prop-valued
               (α ^ₒ (sup F ↓ y) ×ₒ α)
               (sup (λ - → α ^ₒ F (lower -))))
             I₂'
             (initial-segment-of-sup-is-initial-segment-of-some-component F y)
      where
       I₂' : (Σ s ꞉ S , Σ x ꞉ ⟨ F s ⟩ , sup F ↓ y ＝ F s ↓ x)
           → α ^ₒ (sup F ↓ y) ×ₒ α ⊴ sup (λ - → α ^ₒ F (lower -))
       I₂' (s , x , p) =
        transport⁻¹
         (_⊴ sup (λ - → α ^ₒ F (lower -)))
         (ap (λ - → α ^ₒ - ×ₒ α) p)
         (⊴-trans
          (α ^ₒ (F s ↓ x) ×ₒ α)
          (α ^ₒ F s)
          (sup (λ - → α ^ₒ (F (lower -))))
          (^ₒ-is-upper-bound₂ α (F s))
          (sup-is-upper-bound (λ - → α ^ₒ (F (lower -))) (lift 𝓤 s)))

^ₒ-satisfies-sup-specification : (α : Ordinal 𝓤)
                               → exp-specification-sup α (α ^ₒ_)
^ₒ-satisfies-sup-specification α =
 exp-specification-sup-from-generalized
  α (α ^ₒ_) (^ₒ-satisfies-sup-specification-generalized α)

\end{code}

Added 29 January 2025 by Tom de Jong.

^ₒ also satisfies the strong supremum specification, yielding yet another proof
that it satisfies the (ordinary) supremum specification.

\begin{code}

^ₒ-satisfies-strong-sup-specification : (α : Ordinal 𝓤)
                                      → exp-specification-sup-strong α (α ^ₒ_)
^ₒ-satisfies-strong-sup-specification {𝓤} α S F =
 ⊴-antisym (α ^ₒ sup F) (sup (cases (λ _ → 𝟙ₒ) (λ s → α ^ₒ F s))) I II
  where
   G : 𝟙{𝓤} + S → Ordinal 𝓤
   G = cases (λ _ → 𝟙ₒ) (λ s → α ^ₒ F s)
   I : α ^ₒ sup F ⊴ sup G
   I = ^ₒ-is-lower-bound-of-upper-bounds α (sup F) (sup G) I₁ I₂
    where
     I₁ : 𝟙ₒ ⊴ sup G
     I₁ = sup-is-upper-bound G (inl ⋆)
     I₂ : (y : ⟨ sup F ⟩) → α ^ₒ (sup F ↓ y) ×ₒ α ⊴ sup G
     I₂ y = ∥∥-rec
             (⊴-is-prop-valued (α ^ₒ (sup F ↓ y) ×ₒ α) (sup G))
             I₃
             (sup-is-upper-bound-jointly-surjective F y)
      where
       ι : {s : S} → ⟨ F s ⟩ → ⟨ sup F ⟩
       ι {s} = [ F s , sup F ]⟨ sup-is-upper-bound F s ⟩
       I₃ : (Σ s ꞉ S , Σ x ꞉ ⟨ F s ⟩ , ι x ＝ y)
          → α ^ₒ (sup F ↓ y) ×ₒ α ⊴ sup G
       I₃ (s , x , refl) = transport⁻¹ (_⊴ sup G) e l
        where
         e : α ^ₒ (sup F ↓ y) ×ₒ α ＝ α ^ₒ (F s ↓ x) ×ₒ α
         e = ap (λ - → α ^ₒ - ×ₒ α) (initial-segment-of-sup-at-component F s x)
         l : α ^ₒ (F s ↓ x) ×ₒ α ⊴ sup G
         l = ⊴-trans (α ^ₒ (F s ↓ x) ×ₒ α) (α ^ₒ F s) (sup G)
              (^ₒ-is-upper-bound₂ α (F s))
              (sup-is-upper-bound G (inr s))
   II : sup G ⊴ α ^ₒ sup F
   II = sup-is-lower-bound-of-upper-bounds G (α ^ₒ sup F) II'
    where
     II' : (x : 𝟙 + S) → G x ⊴ α ^ₒ sup F
     II' (inl ⋆) = ^ₒ-has-least-element α (sup F)
     II' (inr s) = ^ₒ-monotone-in-exponent α (F s) (sup F)
                    (sup-is-upper-bound F s)

^ₒ-satisfies-sup-specification' : (α : Ordinal 𝓤)
                                → exp-specification-sup α (α ^ₒ_)
^ₒ-satisfies-sup-specification' α =
 exp-specification-sup-from-strong α
  (α ^ₒ_)
  (^ₒ-satisfies-strong-sup-specification α)

\end{code}

Exponentiating by 𝟙ₒ and 𝟚ₒ behaves as expected (and this behaviour follows
abstractly from the zero and successor specifications).

\begin{code}

𝟙ₒ-neutral-^ₒ : (α : Ordinal 𝓤) → 𝟙ₒ ⊴ α → α ^ₒ 𝟙ₒ ＝ α
𝟙ₒ-neutral-^ₒ α l = 𝟙ₒ-neutral-exp α (α ^ₒ_)
                     (^ₒ-satisfies-zero-specification α)
                     (^ₒ-satisfies-succ-specification α l)

^ₒ-𝟚ₒ-is-×ₒ : (α : Ordinal 𝓤) → 𝟙ₒ ⊴ α → α ^ₒ 𝟚ₒ ＝ α ×ₒ α
^ₒ-𝟚ₒ-is-×ₒ α l = exp-𝟚ₒ-is-×ₒ α (α ^ₒ_)
                   (^ₒ-satisfies-zero-specification α)
                   (^ₒ-satisfies-succ-specification α l)

\end{code}

More generally, we have
  α ^ₒ (β +ₒ γ) ＝ α ^ₒ β ×ₒ α ^ₒ γ,
the proof of which makes use of the following general lemma which folds the
product into the supremum.

\begin{code}

×ₒ-^ₒ-lemma :
   (α : Ordinal 𝓤) (β : Ordinal 𝓥) (γ : Ordinal (𝓤 ⊔ 𝓥))
 → γ ×ₒ α ^ₒ β
   ＝ sup (cases (λ (_ : 𝟙  {𝓤}) → γ) (λ (b : ⟨ β ⟩) → γ ×ₒ α ^ₒ (β ↓ b) ×ₒ α))
×ₒ-^ₒ-lemma {𝓤} {𝓥} α β γ =
 γ ×ₒ α ^ₒ β                        ＝⟨ I   ⟩
 γ ×ₒ sup (^ₒ-family α β)           ＝⟨ II  ⟩
 sup (λ - → γ ×ₒ (^ₒ-family α β -)) ＝⟨ III ⟩
 sup F                              ∎
  where
   F : 𝟙 + ⟨ β ⟩ → Ordinal (𝓤 ⊔ 𝓥)
   F = cases (λ _ → γ) (λ b → γ ×ₒ α ^ₒ (β ↓ b) ×ₒ α)

   I   = ap (γ ×ₒ_) (^ₒ-behaviour α β)
   II  = ×ₒ-preserves-suprema pt sr γ _ (^ₒ-family α β)
   III = ap sup (dfunext fe' h)
    where
     h : (λ - → γ ×ₒ ^ₒ-family α β -) ∼ F
     h (inl ⋆) = 𝟙ₒ-right-neutral-×ₒ γ
     h (inr b) = (×ₒ-assoc γ (α ^ₒ (β ↓ b)) α) ⁻¹

^ₒ-by-+ₒ : {𝓤 𝓥 : Universe} (α : Ordinal 𝓤) (β γ : Ordinal 𝓥)
         → α ^ₒ (β +ₒ γ) ＝ α ^ₒ β ×ₒ α ^ₒ γ
^ₒ-by-+ₒ {𝓤} {𝓥} α β =
 transfinite-induction-on-OO (λ γ → α ^ₒ (β +ₒ γ) ＝ α ^ₒ β ×ₒ α ^ₒ γ) I
  where
   I : (γ : Ordinal 𝓥)
     → ((c : ⟨ γ ⟩) → α ^ₒ (β +ₒ (γ ↓ c)) ＝ α ^ₒ β ×ₒ α ^ₒ (γ ↓ c))
     → α ^ₒ (β +ₒ γ) ＝ α ^ₒ β ×ₒ α ^ₒ γ
   I γ IH = α ^ₒ (β +ₒ γ)    ＝⟨ ⊴-antisym (α ^ₒ (β +ₒ γ)) (sup F) II III ⟩
            sup F            ＝⟨ (×ₒ-^ₒ-lemma α γ (α ^ₒ β)) ⁻¹ ⟩
            α ^ₒ β ×ₒ α ^ₒ γ ∎
    where
     F : 𝟙 + ⟨ γ ⟩ → Ordinal (𝓤 ⊔ 𝓥)
     F = cases (λ _ → α ^ₒ β) (λ c → α ^ₒ β ×ₒ α ^ₒ (γ ↓ c) ×ₒ α)

     eq : (c : ⟨ γ ⟩)
        → α ^ₒ β ×ₒ α ^ₒ (γ ↓ c) ×ₒ α ＝ α ^ₒ ((β +ₒ γ) ↓ inr c) ×ₒ α
     eq c = α ^ₒ β ×ₒ α ^ₒ (γ ↓ c) ×ₒ α  ＝⟨ e₁ ⟩
            α ^ₒ (β +ₒ (γ ↓ c)) ×ₒ α     ＝⟨ e₂ ⟩
            α ^ₒ ((β +ₒ γ) ↓ inr c) ×ₒ α ∎
      where
       e₁ = ap (_×ₒ α) ((IH c) ⁻¹)
       e₂ = ap (λ - → α ^ₒ - ×ₒ α) (+ₒ-↓-right c)

     II : α ^ₒ (β +ₒ γ) ⊴ sup F
     II = ^ₒ-is-lower-bound-of-upper-bounds α (β +ₒ γ) (sup F)
            II₁ II₂
       where
        II₁ : 𝟙ₒ ⊴ sup F
        II₁ = ⊴-trans 𝟙ₒ (α ^ₒ β) (sup F)
               (^ₒ-has-least-element α β)
               (sup-is-upper-bound _ (inl ⋆))
        II₂ : (x : ⟨ β +ₒ γ ⟩) → α ^ₒ (β +ₒ γ ↓ x) ×ₒ α ⊴ sup F
        II₂ (inl b) = transport
                       (_⊴ sup F)
                       (ap (λ - → α ^ₒ - ×ₒ α) (+ₒ-↓-left b))
                       (⊴-trans (α ^ₒ (β ↓ b) ×ₒ α) (α ^ₒ β) (sup F)
                         (^ₒ-is-upper-bound₂ α β)
                         (sup-is-upper-bound F (inl ⋆)))
        II₂ (inr c) =
         transport (_⊴ sup F) (eq c) (sup-is-upper-bound F (inr c))

     III : sup F ⊴ α ^ₒ (β +ₒ γ)
     III = sup-is-lower-bound-of-upper-bounds _ (α ^ₒ (β +ₒ γ)) III'
      where
       III' : (x : 𝟙 + ⟨ γ ⟩) → F x ⊴ α ^ₒ (β +ₒ γ)
       III' (inl ⋆) = ^ₒ-monotone-in-exponent α β (β +ₒ γ) (+ₒ-left-⊴ β γ)
       III' (inr c) =
        transport⁻¹ (_⊴ α ^ₒ (β +ₒ γ)) (eq c) (^ₒ-is-upper-bound₂ α (β +ₒ γ))

\end{code}

The general lemma
  α ^ₒ (β +ₒ γ) ＝ α ^ₒ β ×ₒ α ^ₒ γ
has the successor specification
  α ^ₒ (β +ₒ 𝟙ₒ) = α ^ₒ β ×ₒ α
as a special case, but deriving it like this forces the universe parameters to
be less general compared to the direct proof given above in
^ₒ-satisifies-succ-specification.

The proof above of 𝟙ₒ-neutral-^ₒ goes via
^ₒ-satisifies-succ-specification, so in order to avoid an implicit
dependency on that proof, we reprove it from scratch here.

\begin{code}

^ₒ-satisfies-succ-specification' : (α : Ordinal 𝓤)
                                 → 𝟙ₒ ⊴ α
                                 → exp-specification-succ {𝓤} {𝓤} α (α ^ₒ_)
^ₒ-satisfies-succ-specification' {𝓤} α l β =
 α ^ₒ (β +ₒ 𝟙ₒ)    ＝⟨ ^ₒ-by-+ₒ α β 𝟙ₒ ⟩
 α ^ₒ β ×ₒ α ^ₒ 𝟙ₒ ＝⟨ ap (α ^ₒ β ×ₒ_) (𝟙ₒ-neutral-^ₒ' α l) ⟩
 α ^ₒ β ×ₒ α       ∎
  where
   𝟙ₒ-neutral-^ₒ' : (α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → α ^ₒ 𝟙ₒ ＝ α
   𝟙ₒ-neutral-^ₒ' α l = ⊴-antisym (α ^ₒ 𝟙ₒ) α II III
    where
     I = α ^ₒ (𝟙ₒ ↓ ⋆) ×ₒ α ＝⟨ ap (λ - → α ^ₒ - ×ₒ α) 𝟙ₒ-↓ ⟩
         α ^ₒ 𝟘ₒ ×ₒ α       ＝⟨ ap (_×ₒ α) (^ₒ-satisfies-zero-specification α) ⟩
         𝟙ₒ ×ₒ α            ＝⟨ 𝟙ₒ-left-neutral-×ₒ α ⟩
         α                  ∎

     II : α ^ₒ 𝟙ₒ ⊴ α
     II = ^ₒ-is-lower-bound-of-upper-bounds α 𝟙ₒ α l (λ _ → II')
      where
       II' : α ^ₒ (𝟙ₒ ↓ ⋆) ×ₒ α ⊴ α
       II' = transport⁻¹ (_⊴ α) I (⊴-refl α)

     III : α ⊴ α ^ₒ 𝟙ₒ
     III = transport (_⊴ α ^ₒ 𝟙ₒ) I (^ₒ-is-upper-bound₂ α 𝟙ₒ)

\end{code}

Exponentiating by a product is iterated exponentiation:

\begin{code}

^ₒ-by-×ₒ : {𝓤 𝓥 : Universe} (α : Ordinal 𝓤) (β γ : Ordinal 𝓥)
         → α ^ₒ (β ×ₒ γ) ＝ (α ^ₒ β) ^ₒ γ
^ₒ-by-×ₒ {𝓤} {𝓥} α β =
 transfinite-induction-on-OO (λ γ → α ^ₒ (β ×ₒ γ) ＝ (α ^ₒ β) ^ₒ γ) I
  where
   I : (γ : Ordinal 𝓥)
     → ((c : ⟨ γ ⟩) → α ^ₒ (β ×ₒ (γ ↓ c)) ＝ (α ^ₒ β) ^ₒ (γ ↓ c))
     → α ^ₒ (β ×ₒ γ) ＝ (α ^ₒ β) ^ₒ γ
   I γ IH = ⊴-antisym (α ^ₒ (β ×ₒ γ)) ((α ^ₒ β) ^ₒ γ) II III
    where
     II : α ^ₒ (β ×ₒ γ) ⊴ (α ^ₒ β) ^ₒ γ
     II = ^ₒ-is-lower-bound-of-upper-bounds α (β ×ₒ γ) ((α ^ₒ β) ^ₒ γ)
           (^ₒ-is-upper-bound₁ (α ^ₒ β) γ)
           II'
      where
       II' : (x : ⟨ β ×ₒ γ ⟩) → α ^ₒ (β ×ₒ γ ↓ x) ×ₒ α ⊴ (α ^ₒ β) ^ₒ γ
       II' (b , c) =
        transport⁻¹ (_⊴ (α ^ₒ β) ^ₒ γ) eq
         (⊴-trans
           ((α ^ₒ β) ^ₒ (γ ↓ c) ×ₒ (α ^ₒ (β ↓ b) ×ₒ α))
           ((α ^ₒ β) ^ₒ (γ ↓ c) ×ₒ α ^ₒ β)
           ((α ^ₒ β) ^ₒ γ)
           (×ₒ-right-monotone-⊴
             ((α ^ₒ β) ^ₒ (γ ↓ c))
             (α ^ₒ (β ↓ b) ×ₒ α)
             (α ^ₒ β)
             (^ₒ-is-upper-bound₂ α β))
           (^ₒ-is-upper-bound₂ (α ^ₒ β) γ))
        where
         eq = α ^ₒ (β ×ₒ γ ↓ (b , c)) ×ₒ α               ＝⟨ e₁ ⟩
              α ^ₒ (β ×ₒ (γ ↓ c) +ₒ (β ↓ b)) ×ₒ α        ＝⟨ e₂ ⟩
              α ^ₒ (β ×ₒ (γ ↓ c)) ×ₒ α ^ₒ (β ↓ b) ×ₒ α   ＝⟨ e₃ ⟩
              (α ^ₒ β) ^ₒ (γ ↓ c) ×ₒ α ^ₒ (β ↓ b) ×ₒ α   ＝⟨ e₄ ⟩
              (α ^ₒ β) ^ₒ (γ ↓ c) ×ₒ (α ^ₒ (β ↓ b) ×ₒ α) ∎
          where
           e₁ = ap (λ - → α ^ₒ - ×ₒ α) (×ₒ-↓ β γ)
           e₂ = ap (_×ₒ α) (^ₒ-by-+ₒ α (β ×ₒ (γ ↓ c)) (β ↓ b))
           e₃ = ap (λ - → - ×ₒ α ^ₒ (β ↓ b) ×ₒ α) (IH c)
           e₄ = ×ₒ-assoc ((α ^ₒ β) ^ₒ (γ ↓ c)) (α ^ₒ (β ↓ b)) α

     III : (α ^ₒ β) ^ₒ γ ⊴ α ^ₒ (β ×ₒ γ)
     III = ^ₒ-is-lower-bound-of-upper-bounds (α ^ₒ β) γ (α ^ₒ (β ×ₒ γ))
            (^ₒ-is-upper-bound₁ α (β ×ₒ γ))
            III'
      where
       III' : (c : ⟨ γ ⟩) → (α ^ₒ β) ^ₒ (γ ↓ c) ×ₒ α ^ₒ β ⊴ α ^ₒ (β ×ₒ γ)
       III' c =
        transport⁻¹ (_⊴ α ^ₒ (β ×ₒ γ)) eq
         (^ₒ-monotone-in-exponent α (β ×ₒ ((γ ↓ c) +ₒ 𝟙ₒ)) (β ×ₒ γ)
           (×ₒ-right-monotone-⊴ β ((γ ↓ c) +ₒ 𝟙ₒ) γ
             (upper-bound-of-successors-of-initial-segments γ c)))
        where
         eq = (α ^ₒ β) ^ₒ (γ ↓ c) ×ₒ α ^ₒ β ＝⟨ e₁ ⟩
              α ^ₒ (β ×ₒ (γ ↓ c)) ×ₒ α ^ₒ β ＝⟨ e₂ ⟩
              α ^ₒ (β ×ₒ (γ ↓ c) +ₒ β)      ＝⟨ e₃ ⟩
              α ^ₒ (β ×ₒ ((γ ↓ c) +ₒ 𝟙ₒ))   ∎
          where
           e₁ = ap (_×ₒ α ^ₒ β) ((IH c) ⁻¹)
           e₂ = (^ₒ-by-+ₒ α (β ×ₒ (γ ↓ c)) β) ⁻¹
           e₃ = ap (α ^ₒ_) (×ₒ-successor β (γ ↓ c) ⁻¹)

\end{code}

The following characterizes initial segments of exponentiated ordinals.

\begin{code}

^ₒ-↓-⊥ : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
       → α ^ₒ β ↓ ^ₒ-⊥ α β ＝ 𝟘ₒ
^ₒ-↓-⊥ α β = α ^ₒ β ↓ ^ₒ-⊥ α β ＝⟨ I ⟩
             𝟙ₒ ↓ ⋆            ＝⟨ 𝟙ₒ-↓ ⟩
             𝟘ₒ                ∎
 where
  I = (simulations-preserve-↓ 𝟙ₒ (α ^ₒ β) (^ₒ-is-upper-bound₁ α β) ⋆) ⁻¹

^ₒ-↓-×ₒ-to-^ₒ : (α β : Ordinal 𝓤)
                {b : ⟨ β ⟩} {e : ⟨ α ^ₒ (β ↓ b) ⟩} {a : ⟨ α ⟩}
              → α ^ₒ β ↓ ×ₒ-to-^ₒ α β (e , a)
                ＝ α ^ₒ (β ↓ b) ×ₒ (α ↓ a) +ₒ (α ^ₒ (β ↓ b) ↓ e)
^ₒ-↓-×ₒ-to-^ₒ α β {b} {e} {a} =
 α ^ₒ β ↓ ×ₒ-to-^ₒ α β (e , a)                 ＝⟨ I ⟩
 α ^ₒ (β ↓ b) ×ₒ α ↓ (e , a)                   ＝⟨ II ⟩
 α ^ₒ (β ↓ b) ×ₒ (α ↓ a) +ₒ (α ^ₒ (β ↓ b) ↓ e) ∎
  where
   I = (simulations-preserve-↓
         (α ^ₒ (β ↓ b) ×ₒ α)
         (α ^ₒ β)
         (^ₒ-is-upper-bound₂ α β)
         (e , a)) ⁻¹
   II = ×ₒ-↓ (α ^ₒ (β ↓ b)) α

^ₒ-↓ :
   (α β : Ordinal 𝓤) {x : ⟨ α ^ₒ β ⟩}
 → (α ^ₒ β ↓ x ＝ 𝟘ₒ)
 ∨ (Σ b ꞉ ⟨ β ⟩ , Σ e ꞉ ⟨ α ^ₒ (β ↓ b) ⟩ , Σ a ꞉ ⟨ α ⟩ ,
     α ^ₒ β ↓ x ＝ α ^ₒ (β ↓ b) ×ₒ (α ↓ a) +ₒ (α ^ₒ (β ↓ b) ↓ e))
^ₒ-↓ {𝓤} α β {x} =
 ^ₒ-induction α β P
  (λ _ → ∥∥-is-prop)
  (∣ inl (^ₒ-↓-⊥ α β) ∣)
  (λ b (e , a) → ∣ inr (b , e , a , ^ₒ-↓-×ₒ-to-^ₒ α β) ∣)
  x
 where
  P : (x : ⟨ α ^ₒ β ⟩) → 𝓤 ⁺ ̇
  P x = (α ^ₒ β ↓ x ＝ 𝟘ₒ)
      ∨ (Σ b ꞉ ⟨ β ⟩ , Σ e ꞉ ⟨ α ^ₒ (β ↓ b) ⟩ , Σ a ꞉ ⟨ α ⟩ ,
          α ^ₒ β ↓ x ＝ α ^ₒ (β ↓ b) ×ₒ (α ↓ a) +ₒ (α ^ₒ (β ↓ b) ↓ e))

\end{code}

Finally, using the above characterization of initial segments, we show that ^ₒ
is (strictly) order preserving in the exponent (provided that the base is
strictly greater than 𝟙ₒ).

\begin{code}

^ₒ-⊲-lemma : (α β : Ordinal 𝓤)
           → 𝟙ₒ ⊲ α
           → {b : ⟨ β ⟩} → α ^ₒ (β ↓ b) ⊲ α ^ₒ β
^ₒ-⊲-lemma α β (a₁ , p) {b} = e , (q ⁻¹)
 where
  ⊥ : ⟨ α ^ₒ (β ↓ b) ⟩
  ⊥ = ^ₒ-⊥ α (β ↓ b)
  e : ⟨ α ^ₒ β ⟩
  e = ×ₒ-to-^ₒ α β (⊥ , a₁)
  q = α ^ₒ β ↓ e                                     ＝⟨ I   ⟩
      α ^ₒ (β ↓ b) ×ₒ (α ↓ a₁) +ₒ (α ^ₒ (β ↓ b) ↓ ⊥) ＝⟨ II  ⟩
      α ^ₒ (β ↓ b) ×ₒ (α ↓ a₁) +ₒ 𝟘ₒ                 ＝⟨ III ⟩
      α ^ₒ (β ↓ b) ×ₒ (α ↓ a₁)                       ＝⟨ IV  ⟩
      α ^ₒ (β ↓ b) ×ₒ 𝟙ₒ                             ＝⟨ V   ⟩
      α ^ₒ (β ↓ b)                                   ∎
   where
    I   = ^ₒ-↓-×ₒ-to-^ₒ α β
    II  = ap (α ^ₒ (β ↓ b) ×ₒ (α ↓ a₁) +ₒ_) (^ₒ-↓-⊥ α (β ↓ b))
    III = 𝟘ₒ-right-neutral (α ^ₒ (β ↓ b) ×ₒ (α ↓ a₁))
    IV  = ap (α ^ₒ (β ↓ b) ×ₒ_) (p ⁻¹)
    V   = 𝟙ₒ-right-neutral-×ₒ (α ^ₒ (β ↓ b))

^ₒ-order-preserving-in-exponent : (α β γ : Ordinal 𝓤)
                                → 𝟙ₒ ⊲ α
                                → β ⊲ γ → α ^ₒ β ⊲ α ^ₒ γ
^ₒ-order-preserving-in-exponent α β γ h (c , refl) = ^ₒ-⊲-lemma α γ h

\end{code}

Added 11 April 2025.

Provided α and β have least elements, trichotomy of the least element of α ^ₒ β
implies trichotomy of the least element of α.

This provides the converse to ^ₒ-has-trichotomous-least-element from
Ordinals.Exponentiation.PropertiesViaTransport.

\begin{code}

open import Ordinals.Exponentiation.TrichotomousLeastElement ua pt

^ₒ-reflects-trichotomous-least-in-base
 : (α β : Ordinal 𝓤) (a₀ : ⟨ α ⟩)
 → is-least α a₀
 → 𝟙ₒ ⊴ β
 → is-trichotomous-least (α ^ₒ β) (^ₒ-⊥ α β)
 → is-trichotomous-least α a₀
^ₒ-reflects-trichotomous-least-in-base α β a₀ a₀-is-least (f , f-sim) = III
 where
  b₀ : ⟨ β ⟩
  b₀ = f ⋆
  b₀-eq : β ↓ b₀ ＝ 𝟘ₒ
  b₀-eq = (simulations-preserve-↓ 𝟙ₒ β (f , f-sim) ⋆) ⁻¹ ∙ 𝟙ₒ-↓

  I : (a : ⟨ α ⟩)
    → α ^ₒ β ↓ ×ₒ-to-^ₒ α β (^ₒ-⊥ α (β ↓ b₀) , a) ＝ α ↓ a
  I a = α ^ₒ β ↓ ×ₒ-to-^ₒ α β (^ₒ-⊥ α (β ↓ b₀) , a)                   ＝⟨ I₁ ⟩
        α ^ₒ (β ↓ b₀) ×ₒ (α ↓ a) +ₒ (α ^ₒ (β ↓ b₀) ↓ ^ₒ-⊥ α (β ↓ b₀)) ＝⟨ I₂ ⟩
        α ^ₒ (β ↓ b₀) ×ₒ (α ↓ a) +ₒ 𝟘ₒ                                ＝⟨ I₃ ⟩
        α ^ₒ (β ↓ b₀) ×ₒ (α ↓ a)                                      ＝⟨ I₄ ⟩
        α ^ₒ 𝟘ₒ ×ₒ (α ↓ a)                                            ＝⟨ I₅ ⟩
        𝟙ₒ ×ₒ (α ↓ a)                                                 ＝⟨ I₆ ⟩
        α ↓ a                                                         ∎
   where
    I₁ = ^ₒ-↓-×ₒ-to-^ₒ α β
    I₂ = ap (α ^ₒ (β ↓ b₀) ×ₒ (α ↓ a) +ₒ_) (^ₒ-↓-⊥ α (β ↓ b₀))
    I₃ = 𝟘ₒ-right-neutral (α ^ₒ (β ↓ b₀) ×ₒ (α ↓ a))
    I₄ = ap (λ - → α ^ₒ - ×ₒ (α ↓ a)) b₀-eq
    I₅ = ap (_×ₒ (α ↓ a)) (^ₒ-satisfies-zero-specification α)
    I₆ = 𝟙ₒ-left-neutral-×ₒ (α ↓ a)

  II = α ↓ a₀            ＝⟨ II' ⟩
       𝟘ₒ                ＝⟨ ^ₒ-↓-⊥ α β ⁻¹ ⟩
       α ^ₒ β ↓ ^ₒ-⊥ α β ∎
   where
    II' = initial-segment-of-least-element-is-𝟘ₒ α a₀ a₀-is-least

  III : is-trichotomous-least (α ^ₒ β) (^ₒ-⊥ α β)
      → is-trichotomous-least α a₀
  III τ a = III' a (τ (×ₒ-to-^ₒ α β (^ₒ-⊥ α (β ↓ b₀) , a)))
   where
    III' : (a : ⟨ α ⟩)
         → (^ₒ-⊥ α β ＝ ×ₒ-to-^ₒ α β (^ₒ-⊥ α (β ↓ b₀) , a))
           + (^ₒ-⊥ α β ≺⟨ α ^ₒ β ⟩ ×ₒ-to-^ₒ α β (^ₒ-⊥ α (β ↓ b₀) , a))
         → (a₀ ＝ a) + (a₀ ≺⟨ α ⟩ a)
    III' a (inl e) = inl (↓-lc α a₀ a e')
     where
      e' = α ↓ a₀                                      ＝⟨ II ⟩
           α ^ₒ β ↓ ^ₒ-⊥ α β                           ＝⟨ ap (α ^ₒ β ↓_) e ⟩
           α ^ₒ β ↓ ×ₒ-to-^ₒ α β (^ₒ-⊥ α (β ↓ b₀) , a) ＝⟨ I a ⟩
           α ↓ a                                       ∎
    III' a (inr l) = inr (↓-reflects-order α a₀ a
                           (transport₂ _⊲_ (II ⁻¹) (I a)
                            (↓-preserves-order (α ^ₒ β) _ _ l)))

\end{code}

In particular, we can fix β ＝ 𝟙ₒ.

\begin{code}

^ₒ-reflects-trichotomous-least-in-base'
 : (α : Ordinal 𝓤) (a₀ : ⟨ α ⟩)
 → is-least α a₀
 → is-trichotomous-least (α ^ₒ 𝟙ₒ) (^ₒ-⊥ α 𝟙ₒ)
 → is-trichotomous-least α a₀
^ₒ-reflects-trichotomous-least-in-base' α a₀ l t =
 ^ₒ-reflects-trichotomous-least-in-base α 𝟙ₒ a₀ l (⊴-refl 𝟙ₒ) t

\end{code}
