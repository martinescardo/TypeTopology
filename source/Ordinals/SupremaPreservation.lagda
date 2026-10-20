Tom de Jong, 14-16 October 2026.

Some of the below used to be part of OrdinalOfOrdinalsSuprema and was
implemented by Tom de Jong and Fredrik Nordvall Forsberg on 5 December 2024,
after it was developed in February 2024 in collaboration with Nicolai Kraus and
Chuangjie Xu. It was moved here to avoid code duplication.

For an operation F on ordinals, we consider several forms of the preservation of
(some) suprema:
  * F preserves all suprema (F is continuous)
  * F preserves inhabited suprema
  * F preserves (arbitrary) suprema up to a binary join with some fixed
    ordinal α, i.e. F (sup γ) ＝ α ∨ sup (F ∘ γ).

Clearly, any continuous operation preserves inhabited suprema.
Moreover, if F preserves suprema up to a join with α, then F preserves inhabited
suprema and α ＝ F 𝟘ₒ.
Nicolai Kraus observed that the converse holds too constructively: if α ＝ F 𝟘ₒ
and F preserves inhabited suprema, then F preserves arbitrary suprema up to a
join with α. This is the main result of this file.

We also show that if F preserves suprema up to a binary join then F is
monontone, and similarly for the other preservation conditions.

The above results are instantiated for
  F = β +ₒ (-), F = β ×ₒ (-) and F = β ^ₒ (-)
in other files.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.SupremaPreservation
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Type

open PropositionalTruncation pt
open suprema pt sr

is-continuous : (Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
is-continuous {𝓤} F =
 {I : 𝓤 ̇ } (γ : I → Ordinal 𝓤) → F (sup γ) ＝ sup (F ∘ γ)

being-continuous-is-prop : (F : Ordinal 𝓤 → Ordinal 𝓤)
                         → is-prop (is-continuous F)
being-continuous-is-prop {𝓤} F =
 implicit-Π-is-prop fe'
  (λ _ → Π-is-prop fe'
          (λ _ → the-type-of-ordinals-is-a-set (ua 𝓤) fe'))

preserves-inhabited-suprema : (Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
preserves-inhabited-suprema {𝓤} F =
 {I : 𝓤 ̇  } → ∥ I ∥ → (γ : I → Ordinal 𝓤) → F (sup γ) ＝ sup (F ∘ γ)

preserves-suprema-up-to-join : (Ordinal 𝓤 → Ordinal 𝓤) → Ordinal 𝓤 → 𝓤 ⁺ ̇
preserves-suprema-up-to-join {𝓤} F α =
 {I : 𝓤 ̇ } (γ : I → Ordinal 𝓤)
    → F (sup γ) ＝ sup (cases (λ (_ : 𝟙{𝓤}) → α) (F ∘ γ))

preserves-suprema-up-to-join-is-prop
 : (F : Ordinal 𝓤 → Ordinal 𝓤) (α : Ordinal 𝓤)
 → is-prop (preserves-suprema-up-to-join F α)
preserves-suprema-up-to-join-is-prop {𝓤} F α =
 implicit-Π-is-prop fe'
  (λ _ → Π-is-prop fe'
          (λ _ → the-type-of-ordinals-is-a-set (ua 𝓤) fe'))

preserves-inhabited-suprema-if-continuous :
 (F : Ordinal 𝓤 → Ordinal 𝓤) → is-continuous F → preserves-inhabited-suprema F
preserves-inhabited-suprema-if-continuous F c _ = c

\end{code}

The supremum of an arbitrary family can be replaced by an inhabited
supremum. This simple trick is instrumental.

\begin{code}

module _
        {I : 𝓤 ̇ }
        (β : I → Ordinal 𝓤)
       where

 fattened-family : 𝟙{𝓤} + I → Ordinal 𝓤
 fattened-family = cases (λ _ → 𝟘ₒ) β

 private
  β⁺ = fattened-family

 fattened-family-is-pointed : domain β⁺
 fattened-family-is-pointed = inl ⋆

 fattened-family-is-inhabited : ∥ domain β⁺ ∥
 fattened-family-is-inhabited = ∣ fattened-family-is-pointed ∣

 sup-of-fattened-family-agrees : sup β⁺ ＝ sup β
 sup-of-fattened-family-agrees = ⊴-antisym (sup β⁺) (sup β) ⦅1⦆ ⦅2⦆
  where
   ⦅1⦆ : sup β⁺ ⊴ sup β
   ⦅1⦆ = sup-is-lower-bound-of-upper-bounds β⁺ (sup β) h
    where
     h : (j : 𝟙 + I) → β⁺ j ⊴ sup β
     h (inl _) = ≼-gives-⊴ 𝟘ₒ (sup β) (𝟘ₒ-least _)
     h (inr i) = sup-is-upper-bound β i

   ⦅2⦆ : sup β ⊴ sup β⁺
   ⦅2⦆ = sup-is-lower-bound-of-upper-bounds β (sup β⁺)
         (λ i → sup-is-upper-bound β⁺ (inr i))

empty-sup-is-𝟘ₒ : sup 𝟘-elim ＝ 𝟘ₒ {𝓤}
empty-sup-is-𝟘ₒ {𝓤} =
 ⊴-antisym (sup 𝟘-elim) 𝟘ₒ
  (sup-is-lower-bound-of-upper-bounds 𝟘-elim 𝟘ₒ 𝟘-induction)
  (𝟘ₒ-least-⊴ (sup 𝟘-elim))

\end{code}

We can now show that if F preserves inhabited suprema and F 𝟘ₒ ＝ α,
then F preserves arbitrarys suprema up to a join with α.

\begin{code}

preserves-suprema-up-to-join-criterion
 : (F : Ordinal 𝓤 → Ordinal 𝓤) (α : Ordinal 𝓤)
 → preserves-inhabited-suprema F × (F 𝟘ₒ ＝ α)
 → preserves-suprema-up-to-join F α
preserves-suprema-up-to-join-criterion {𝓤} F α (σ , eq) {I} β =
 F (sup β)    ＝⟨ ap F ((sup-of-fattened-family-agrees β) ⁻¹) ⟩
 F (sup β⁺)   ＝⟨ σ (fattened-family-is-inhabited β) β⁺ ⟩
 sup (F ∘ β⁺) ＝⟨ sup-pointwise-equal (F ∘ β⁺) (F⁺ β) e ⟩
 sup (F⁺ β)   ∎
  where
   F⁺ : {I : 𝓤 ̇ } → (I → Ordinal 𝓤) → 𝟙 + I → Ordinal 𝓤
   F⁺ β = cases (λ _ → α) (F ∘ β)
   β⁺ = fattened-family β
   e : F ∘ β⁺ ∼ F⁺ β
   e = dep-cases (λ ⋆ → eq) (λ i → refl)

\end{code}

For the converse, we first observe that if F preserves suprema up to a join
with α, then this forces α to be the value of F at 𝟘ₒ.

\begin{code}

preserves-suprema-up-to-join-implies-zero-equation
 : (F : Ordinal 𝓤 → Ordinal 𝓤) (α : Ordinal 𝓤)
 → preserves-suprema-up-to-join F α
 → F 𝟘ₒ ＝ α
preserves-suprema-up-to-join-implies-zero-equation {𝓤} F α σ =
 F 𝟘ₒ           ＝⟨ ap F (empty-sup-is-𝟘ₒ ⁻¹) ⟩
 F (sup 𝟘-elim) ＝⟨ σ 𝟘-elim ⟩
 sup F⁺         ＝⟨ ⊴-antisym (sup F⁺) α I II ⟩
 α              ∎
  where
   F⁺ : 𝟙 + 𝟘 → Ordinal 𝓤
   F⁺ = cases (λ _ → α) (F ∘ 𝟘-elim)
   I : sup F⁺ ⊴ α
   I = sup-is-lower-bound-of-upper-bounds F⁺ α
        (dep-cases (λ _ → ⊴-refl α) 𝟘-induction)
   II : α ⊴ sup F⁺
   II = sup-is-upper-bound F⁺ (inl ⋆)

\end{code}

To prove the preservation of inhabited suprema, we will need monotonicity, which
is also of independent utility.

\begin{code}

module _
        (F : Ordinal 𝓤 → Ordinal 𝓤)
       where

 is-monotone-if-preserves-suprema-up-to-join
  : (α : Ordinal 𝓤)
  → preserves-suprema-up-to-join F α
  → is-monotone-⊴ F
 is-monotone-if-preserves-suprema-up-to-join α eqₛ β γ l =
  transport (F β ⊴_) (ap F I) II
   where
    Δ : 𝟙{𝓤} + 𝟙{𝓤} → Ordinal 𝓤
    Δ = cases (λ _ → β) (λ _ → γ)
    Δ⁺ : 𝟙 + (domain Δ) → Ordinal 𝓤
    Δ⁺ = cases (λ _ → α) (F ∘ Δ)

    I : sup Δ ＝ γ
    I = ⊴-antisym (sup Δ) γ
         (sup-is-lower-bound-of-upper-bounds Δ γ
           (dep-cases (λ _ → l)
           (λ _ → ⊴-refl γ)))
         (sup-is-upper-bound Δ (inr ⋆))

    II : F β ⊴ F (sup Δ)
    II = transport⁻¹ (F β ⊴_) (eqₛ Δ) (sup-is-upper-bound Δ⁺ (inr (inl ⋆)))


 is-monotone-if-preserves-inhabited-suprema : preserves-inhabited-suprema F
                                            → is-monotone-⊴ F
 is-monotone-if-preserves-inhabited-suprema σ =
  is-monotone-if-preserves-suprema-up-to-join (F 𝟘ₒ)
   (preserves-suprema-up-to-join-criterion F (F 𝟘ₒ) (σ , refl))

 is-monotone-if-continuous : is-continuous F → is-monotone-⊴ F
 is-monotone-if-continuous c =
  is-monotone-if-preserves-inhabited-suprema
   (preserves-inhabited-suprema-if-continuous F c)

\end{code}

We now prove the logical equivalences between several forms of preservation of
suprema.

\begin{code}

least-value-if-preserves-suprema-up-to-join
 : (F : Ordinal 𝓤 → Ordinal 𝓤) (α : Ordinal 𝓤)
 → preserves-suprema-up-to-join F α
 → (β : Ordinal 𝓤) → α ⊴ F β
least-value-if-preserves-suprema-up-to-join F α σ β =
 transport (_⊴ F β)
           (preserves-suprema-up-to-join-implies-zero-equation F α σ)
           I
  where
   I : F 𝟘ₒ ⊴ F β
   I = is-monotone-if-preserves-suprema-up-to-join F α σ 𝟘ₒ β (𝟘ₒ-least-⊴ β)

preserves-inhabited-suprema-criterion
 : (F : Ordinal 𝓤 → Ordinal 𝓤)
 → preserves-suprema-up-to-join F (F 𝟘ₒ)
 → preserves-inhabited-suprema F
preserves-inhabited-suprema-criterion {𝓤} F σ {I} =
 ∥∥-rec (Π-is-prop fe' (λ _ → the-type-of-ordinals-is-a-set (ua 𝓤) fe')) h
  where
   h : I → (γ : I → Ordinal 𝓤) → F (sup γ) ＝ sup (F ∘ γ)
   h i γ =
    transport⁻¹ (_＝ sup (F ∘ γ)) (σ γ) (⊴-antisym (sup F⁺) (sup (F ∘ γ)) l₁ l₂)
     where
      F⁺ = cases (λ _ → F 𝟘ₒ) (F ∘ γ)

      l₁ : sup F⁺ ⊴ sup (F ∘ γ)
      l₁ = sup-is-lower-bound-of-upper-bounds F⁺ (sup (F ∘ γ))
            (dep-cases (λ _ → ⊴-trans (F 𝟘ₒ) (F (γ i)) (sup (F ∘ γ))
                         (least-value-if-preserves-suprema-up-to-join
                           F (F 𝟘ₒ) σ (γ i))
                         (sup-is-upper-bound (F ∘ γ) i))
                       (sup-is-upper-bound (F ∘ γ)))
      l₂ : sup (F ∘ γ) ⊴ sup F⁺
      l₂ = sup-is-lower-bound-of-upper-bounds (F ∘ γ) (sup F⁺)
            (λ i → sup-is-upper-bound F⁺ (inr i))

preservation-of-suprema-equivalence
 : (F : Ordinal 𝓤 → Ordinal 𝓤) (α : Ordinal 𝓤)
 → ((F 𝟘ₒ ＝ α) × preserves-inhabited-suprema F)
 ↔ preserves-suprema-up-to-join F α
preservation-of-suprema-equivalence F α =
 (λ (eq , σ) → preserves-suprema-up-to-join-criterion F α (σ , eq)) ,
 (λ σ → eq σ ,
        preserves-inhabited-suprema-criterion F (σ' σ (eq σ)))
  where
   module _ (σ : preserves-suprema-up-to-join F α) where
    eq : F 𝟘ₒ ＝ α
    eq = preserves-suprema-up-to-join-implies-zero-equation F α σ
    σ' : F 𝟘ₒ ＝ α → preserves-suprema-up-to-join F (F 𝟘ₒ)
    σ' refl = σ

preservation-of-suprema-continuity-equivalence
 : (F : Ordinal 𝓤 → Ordinal 𝓤)
 → preserves-suprema-up-to-join F 𝟘ₒ
 ↔ is-continuous F
preservation-of-suprema-continuity-equivalence F =
 (λ σ γ → σ γ ∙ sup-of-fattened-family-agrees (F ∘ γ)) ,
 (λ c γ → c γ ∙ (sup-of-fattened-family-agrees (F ∘ γ)) ⁻¹)

\end{code}