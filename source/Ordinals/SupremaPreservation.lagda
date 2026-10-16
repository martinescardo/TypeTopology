TODO

COMMENT AND REVISE

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

\end{code}

TODO. COMMENT

\begin{code}

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

-- TODO. COMMENT

{-
preserves-inhabited-suprema-generalized
 : (Ordinal 𝓤 → Ordinal (𝓤 ⊔ 𝓥)) → (𝓤 ⊔ 𝓥) ⁺ ̇
preserves-inhabited-suprema-generalized {𝓤} {𝓥} F =
 {I : 𝓤 ̇  }  → ∥ I ∥ → (γ : I → Ordinal 𝓤)
             → F (sup γ) ＝ sup (λ (i : Lift 𝓥 I) → F (γ (lower i)))
  where
   open import UF.UniverseEmbedding
-}

-- TODO. COMMENT

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

The supremum of an arbitrary family can be replaced by an inhabited supremum.

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

\end{code}

\begin{code}

empty-sup-is-𝟘ₒ : sup 𝟘-elim ＝ 𝟘ₒ {𝓤}
empty-sup-is-𝟘ₒ {𝓤} =
 ⊴-antisym (sup 𝟘-elim) 𝟘ₒ
  (sup-is-lower-bound-of-upper-bounds 𝟘-elim 𝟘ₒ 𝟘-induction)
  (𝟘ₒ-least-⊴ (sup 𝟘-elim))

\end{code}

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

\begin{code}

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
      F𝟘ₒ-is-least : (β : Ordinal 𝓤) → F 𝟘ₒ ⊴ F β
      F𝟘ₒ-is-least β =
       is-monotone-if-preserves-suprema-up-to-join
        F (F 𝟘ₒ) σ 𝟘ₒ β (𝟘ₒ-least-⊴ β)

      l₁ : sup F⁺ ⊴ sup (F ∘ γ)
      l₁ = sup-is-lower-bound-of-upper-bounds F⁺ (sup (F ∘ γ))
            (dep-cases (λ _ → ⊴-trans (F 𝟘ₒ) (F (γ i)) (sup (F ∘ γ))
                         (F𝟘ₒ-is-least (γ i))
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


-- \begin{code}

-- \end{code}

-- Previously (since 5 December 2024), this was part of OrdinalOfOrdinalsSuprema,
-- and it was implemented by Tom de Jong and Fredrik Nordvall Forsberg, developed
-- in February 2024 in collaboration with Nicolai Kraus and Chuangjie Xu.
-- It was moved here and revised on 15 October 2026 by Tom de Jong.

-- \begin{code}

-- preserves-inhabited-suprema-if-continuous
--  : (F : Ordinal 𝓤 → Ordinal 𝓤) → is-continuous F → preserves-inhabited-suprema F
-- preserves-inhabited-suprema-if-continuous F c _ = c

-- is-monotone-if-preserves-inhabited-suprema-generalized
--  : (F : Ordinal 𝓤 → Ordinal (𝓤 ⊔ 𝓥))
--  → preserves-inhabited-suprema-generalized F
--  → is-monotone-⊴ F
-- is-monotone-if-preserves-inhabited-suprema-generalized
--  {𝓤} {𝓥} F F-cont α β l = IV
--   where
--    open import UF.UniverseEmbedding
--    γ : 𝟙{𝓤} + 𝟙{𝓤} → Ordinal 𝓤
--    γ (inl _) = α
--    γ (inr _) = β

--    β-is-upper-bound : (i : 𝟙 + 𝟙) → γ i ⊴ β
--    β-is-upper-bound (inl _) = l
--    β-is-upper-bound (inr _) = ⊴-refl β

--    I : F (sup γ) ＝ sup (F ∘ γ ∘ lower)
--    I = F-cont ∣ inl ⋆ ∣ γ

--    II : sup γ ＝ β
--    II = ⊴-antisym (sup γ) β
--          (sup-is-lower-bound-of-upper-bounds γ β β-is-upper-bound)
--          (sup-is-upper-bound γ (inr ⋆))

--    III : F α ⊴ sup (F ∘ γ ∘ lower)
--    III = sup-is-upper-bound (F ∘ γ ∘ lower) (lift 𝓥 (inl ⋆))

--    IV : F α ⊴ F β
--    IV = transport (F α ⊴_) (I ⁻¹ ∙ ap F II) III

-- to-preserves-inhabited-suprema-generalized
--  : (F : Ordinal 𝓤 → Ordinal 𝓤)
--  → preserves-inhabited-suprema F
--  → preserves-inhabited-suprema-generalized {𝓤} {𝓤} F
-- to-preserves-inhabited-suprema-generalized {𝓤} F F-cont {S} S-inh γ =
--  transport⁻¹
--   (_＝ sup (F ∘ γ ∘ lower))
--   (F-cont S-inh γ)
--   (⊴-antisym (sup (F ∘ γ)) (sup (F ∘ γ ∘ lower)) I II)
--   where
--    open import UF.UniverseEmbedding
--    I : sup (F ∘ γ) ⊴ sup (F ∘ γ ∘ lower)
--    I = sup-composition-⊴ (lift 𝓤) (F ∘ γ ∘ lower)
--    II : sup (F ∘ γ ∘ lower) ⊴ sup (F ∘ γ)
--    II = sup-composition-⊴ lower (F ∘ γ)

-- is-monotone-if-preserves-inhabited-suprema : (F : Ordinal 𝓤 → Ordinal 𝓤)
--                                            → preserves-inhabited-suprema F
--                                            → is-monotone-⊴ F
-- is-monotone-if-preserves-inhabited-suprema {𝓤} F F-cont =
--  is-monotone-if-preserves-inhabited-suprema-generalized F
--   (to-preserves-inhabited-suprema-generalized F F-cont)

-- is-monotone-if-continuous : (F : Ordinal 𝓤 → Ordinal 𝓤)
--                           → is-continuous F → is-monotone-⊴ F
-- is-monotone-if-continuous F c =
--  is-monotone-if-preserves-inhabited-suprema F
--   (preserves-inhabited-suprema-if-continuous F c)

-- \end{code}

-- TODO: COMMENT.

-- Added 14 October 2026 by Tom de Jong, following an observation by Nicolai Kraus.

-- Given an operation F on ordinals, we have that
--    F preserves inhabited suprema
--    (i.e. suprema of families with inhabited index types)
-- if and only if
--    F preserves all suprema up to a binary join with F 𝟘ₒ, i.e.
--    F (sup β) ＝ F 𝟘ₒ ∨ sup (F ∘ β) holds.

-- This observation is used for the operations of addition and exponentation by a
-- fixed ordinal.
-- For those applications we find it convenient to fix some ordinal α up front that
-- is equal to F 𝟘ₒ.

-- We need a few preliminaries to prove the observation.

-- \begin{code}

-- empty-sup-is-𝟘ₒ : sup 𝟘-elim ＝ 𝟘ₒ {𝓤}
-- empty-sup-is-𝟘ₒ {𝓤} =
--  Antisymmetry (OO 𝓤) (sup 𝟘-elim) 𝟘ₒ
--   (⊴-gives-≼ (sup 𝟘-elim) 𝟘ₒ
--    (sup-is-lower-bound-of-upper-bounds 𝟘-elim 𝟘ₒ 𝟘-induction))
--    (𝟘ₒ-least (sup 𝟘-elim))

-- \end{code}

-- Next, we derive some consequences of preserving suprema up to a join with a
-- fixed ordinal α.

-- \begin{code}

-- module _
--         (α : Ordinal 𝓤)
--         (F : Ordinal 𝓤 → Ordinal 𝓤)
--        where

--  preserves-suprema-up-to-join : 𝓤 ⁺ ̇
--  preserves-suprema-up-to-join =
--   {I : 𝓤 ̇ } (β : I → Ordinal 𝓤)
--      → F (sup β) ＝ sup (cases (λ (_ : 𝟙{𝓤}) → α) (F ∘ β))

--  private
--   α-is-F𝟘ₒ : preserves-suprema-up-to-join
--            → α ＝ F 𝟘ₒ
--   α-is-F𝟘ₒ eqₛ =
--    α                                  ＝⟨ ⊴-antisym α _ l₁ l₂ ⟩
--    sup (cases (λ _ → α) (F ∘ 𝟘-elim)) ＝⟨ (eqₛ 𝟘-elim) ⁻¹ ⟩
--    F (sup 𝟘-elim)                     ＝⟨ ap F empty-sup-is-𝟘ₒ ⟩
--    F 𝟘ₒ                               ∎
--     where
--      F⁺ = cases (λ _ → α) (F ∘ 𝟘-elim)
--      l₁ : α ⊴ sup F⁺
--      l₁ = sup-is-upper-bound _ (inl ⋆)
--      l₂ : sup F⁺ ⊴ α
--      l₂ = sup-is-lower-bound-of-upper-bounds _ α
--            (dep-cases (λ _ → ⊴-refl α) 𝟘-induction)

--   F-is-monotone : preserves-suprema-up-to-join
--                 → is-monotone (OO 𝓤) (OO 𝓤) F
--   F-is-monotone eqₛ β γ l = ⊴-gives-≼ (F β) (F γ) (transport (F β ⊴_) (ap F I) II)
--    where
--     Δ : 𝟙{𝓤} + 𝟙{𝓤} → Ordinal 𝓤
--     Δ = cases (λ _ → β) (λ _ → γ)
--     Δ⁺ : 𝟙 + (domain Δ) → Ordinal 𝓤
--     Δ⁺ = cases (λ _ → α) (F ∘ Δ)

--     I : sup Δ ＝ γ
--     I = ⊴-antisym (sup Δ) γ
--          (sup-is-lower-bound-of-upper-bounds Δ γ
--            (dep-cases (λ _ → ≼-gives-⊴ β γ l)
--            (λ _ → ⊴-refl γ)))
--          (sup-is-upper-bound Δ (inr ⋆))

--     II : F β ⊴ F (sup Δ)
--     II = transport⁻¹ (F β ⊴_) (eqₛ Δ) (sup-is-upper-bound Δ⁺ (inr (inl ⋆)))

--   F𝟘ₒ-least : preserves-suprema-up-to-join
--             → (γ : Ordinal 𝓤) → F 𝟘ₒ ⊴ F γ
--   F𝟘ₒ-least eqₛ γ =
--    ≼-gives-⊴ (F 𝟘ₒ) (F γ) (F-is-monotone eqₛ 𝟘ₒ γ (𝟘ₒ-least γ))

--   α-least : preserves-suprema-up-to-join
--           → (γ : Ordinal 𝓤) → α ⊴ F γ
--   α-least eqₛ γ = transport⁻¹ (_⊴ F γ) (α-is-F𝟘ₒ eqₛ) (F𝟘ₒ-least eqₛ γ)

-- \end{code}

-- Finally, here is proof of the observation announced above.

-- \begin{code}

--  preservation-of-suprema-equivalence
--   : ((F 𝟘ₒ ＝ α) × preserves-inhabited-suprema F)
--   ↔ preserves-suprema-up-to-join
--  preservation-of-suprema-equivalence = ⦅⇒⦆ , ⦅⇐⦆
--   where
--    F⁺ : {I : 𝓤 ̇ } → (I → Ordinal 𝓤) → 𝟙 + I → Ordinal 𝓤
--    F⁺ β = cases (λ _ → α) (F ∘ β)

--    ⦅⇒⦆ : (F 𝟘ₒ ＝ α) × preserves-inhabited-suprema F
--        → preserves-suprema-up-to-join
--    ⦅⇒⦆ (eqₒ , eqₛ) {I} β =
--     F (sup β)    ＝⟨ ap F (sup-of-fattened-family-agrees β) ⟩
--     F (sup β⁺)   ＝⟨ eqₛ (fattened-family-is-inhabited β) β⁺ ⟩
--     sup (F ∘ β⁺) ＝⟨ sup-pointwise-equal (F ∘ β⁺) (F⁺ β) e ⟩
--     sup (F⁺ β)   ∎
--      where
--       β⁺ = fattened-family β
--       e : F ∘ β⁺ ∼ F⁺ β
--       e = dep-cases (λ ⋆ → eqₒ) (λ i → refl)

--    ⦅⇐⦆ : preserves-suprema-up-to-join
--        → (F 𝟘ₒ ＝ α) × preserves-inhabited-suprema F
--    ⦅⇐⦆ eqₛ =
--     ((α-is-F𝟘ₒ eqₛ) ⁻¹) ,
--     (λ {I} →
--      ∥∥-rec (Π-is-prop fe' (λ _ → the-type-of-ordinals-is-a-set (ua 𝓤) fe')) h)
--      where
--       h : {I : 𝓤 ̇ } → I → (β : I → Ordinal 𝓤) → F (sup β) ＝ sup (F ∘ β)
--       h i β =
--        F (sup β)   ＝⟨ eqₛ β ⟩
--        sup (F⁺ β)  ＝⟨ ⊴-antisym (sup (F⁺ β)) (sup (F ∘ β)) l₁ l₂ ⟩
--        sup (F ∘ β) ∎
--         where
--          l₁ : sup (F⁺ β) ⊴ sup (F ∘ β)
--          l₁ = sup-is-lower-bound-of-upper-bounds (F⁺ β) (sup (F ∘ β))
--                (dep-cases (λ _ → l) (λ i → sup-is-upper-bound (F ∘ β) i))
--           where
--            l : α ⊴ sup (F ∘ β)
--            l = ⊴-trans α (F (β i)) (sup (F ∘ β))
--                 (α-least eqₛ (β i))
--                 (sup-is-upper-bound (F ∘ β) i)
--          l₂ : sup (F ∘ β) ⊴ sup (F⁺ β)
--          l₂ = sup-is-lower-bound-of-upper-bounds (F ∘ β) (sup (F⁺ β))
--                (λ i → sup-is-upper-bound (F⁺ β) (inr i))

-- \end{code}