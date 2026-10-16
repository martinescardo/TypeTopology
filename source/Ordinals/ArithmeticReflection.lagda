Tom de Jong, 31 July 2025.
With additions by Fredrik Nordvall Forsberg in October 2025.
Slightly refactored on 16 October 2026.

For a fixed ordinal α, we answer the following question positively:
  Do the functions (α + _), (α × _), and (exp α _) : Ord → Ord reflect
  ≤ and = ?
It is quite trivial to see that α + β ≤ α + γ implies β ≤ γ, but the
question is non-trivial for multiplication and exponentiation.  This
file develops a result for a general function F : Ord → Ord, of which
the functions in question are instances.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.ArithmeticReflection
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import MLTT.Plus-Properties
open import MLTT.Spartan hiding (J)
open import MLTT.List hiding ([_])
open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import Fin.Properties
open import Fin.Type
open import Naturals.Properties
open import UF.Base
open import UF.Equiv

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.Exponentiation.DecreasingList ua pt
open import Ordinals.Exponentiation.Miscellaneous ua pt sr
open import Ordinals.Exponentiation.RelatingConstructions ua pt sr
open import Ordinals.Exponentiation.Supremum ua pt sr
open import Ordinals.Exponentiation.TrichotomousLeastElement ua
open import Ordinals.Fin
open import Ordinals.Maps
open import Ordinals.MultiplicationProperties ua
open import Ordinals.Notions
open import Ordinals.OperationsByCases ua pt sr
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.SupremaPreservation ua pt sr
open import Ordinals.Type
open import Ordinals.Underlying

open PropositionalTruncation pt
open suprema pt sr

\end{code}

We start by briefly noting that right cancellation is just false for
addition, multiplication and exponentiation.

\begin{code}

no-right-cancellation-+ₒ
 : ¬ ((α β γ : Ordinal 𝓤₀) → α +ₒ γ ＝ β +ₒ γ → α ＝ β)
no-right-cancellation-+ₒ hyp =
 𝟘ₒ-is-not-𝟙ₒ (hyp 𝟘ₒ 𝟙ₒ ω (𝟘ₒ+ₒω-is-ω ∙ 𝟙ₒ+ₒω-is-ω ⁻¹))

no-right-cancellation-+ₒ-⊴
 : ¬ ((α β γ : Ordinal 𝓤₀) → α +ₒ γ ⊴ β +ₒ γ → α ⊴ β)
no-right-cancellation-+ₒ-⊴ hyp = no-right-cancellation-+ₒ hyp'
 where
  hyp' : (α β γ : Ordinal 𝓤₀) → α +ₒ γ ＝ β +ₒ γ → α ＝ β
  hyp' α β γ e =
   ⊴-antisym α β (hyp α β γ (＝-to-⊴ _ _ e)) (hyp β α γ (＝-to-⊴ _ _ (e ⁻¹)))

no-right-cancellation-×ₒ
 : ¬ ((α β γ : Ordinal 𝓤₀) → α ×ₒ γ ＝ β ×ₒ γ → α ＝ β)
no-right-cancellation-×ₒ hyp =
 𝟚ₒ-is-not-𝟙ₒ (hyp 𝟚ₒ 𝟙ₒ ω (𝟚ₒ×ₒω-is-ω ∙ 𝟙ₒ×ₒω-is-ω ⁻¹))

no-right-cancellation-×ₒ-⊴
 : ¬ ((α β γ : Ordinal 𝓤₀) → α ×ₒ γ ⊴ β ×ₒ γ → α ⊴ β)
no-right-cancellation-×ₒ-⊴ hyp = no-right-cancellation-×ₒ hyp'
 where
  hyp' : (α β γ : Ordinal 𝓤₀) → α ×ₒ γ ＝ β ×ₒ γ → α ＝ β
  hyp' α β γ e =
   ⊴-antisym α β (hyp α β γ (＝-to-⊴ _ _ e)) (hyp β α γ (＝-to-⊴ _ _ (e ⁻¹)))

no-right-cancellation-^ₒ
 : ¬ ((α β γ : Ordinal 𝓤₀) → α ^ₒ γ ＝ β ^ₒ γ → α ＝ β)
no-right-cancellation-^ₒ hyp =
 Fin3-is-not-Fin2 (hyp (Fin-ordinal 3) (Fin-ordinal 2) ω Fin3^ₒω-is-Fin2^ₒω)
  where
   Fin3^ₒω-is-Fin2^ₒω : Fin-ordinal 3 ^ₒ ω ＝ Fin-ordinal 2 ^ₒ ω
   Fin3^ₒω-is-Fin2^ₒω = Fin-ordinal- 3 ^ₒω-is-ω ⋆ ∙ Fin-ordinal- 2 ^ₒω-is-ω ⋆ ⁻¹

   Fin3-is-not-Fin2 : Fin-ordinal 3 ≠ Fin-ordinal 2
   Fin3-is-not-Fin2 eq = positive-not-zero 0 (succ-lc (succ-lc (3-is-2 eq)))
    where
     3-is-2 : Fin-ordinal 3 ＝ Fin-ordinal 2 → 3 ＝ 2
     3-is-2 eq = Fin-lc 3 2 (idtoeq (Fin 3) (Fin 2) (ap ⟨_⟩ eq))

no-right-cancellation-^ₒ-⊴
 : (∀ {𝓤} → (α β γ : Ordinal 𝓤) → α ^ₒ γ ⊴ β ^ₒ γ → α ⊴ β) → 𝟘
no-right-cancellation-^ₒ-⊴ hyp = no-right-cancellation-^ₒ hyp'
 where
  hyp' : ∀ {𝓤} → (α β γ : Ordinal 𝓤) → α ^ₒ γ ＝ β ^ₒ γ → α ＝ β
  hyp' α β γ e =
   ⊴-antisym α β (hyp α β γ (＝-to-⊴ _ _ e)) (hyp β α γ (＝-to-⊴ _ _ (e ⁻¹)))

\end{code}

The proofs of our results will rely on two auxiliary notions, the
first of which is the type of order-preserving (and possibly
bounded) maps between two ordinals. Since LEM implies that every
order-preserving map induces a simulation, we suggestively write
α ≤ᶜˡ β (and α <ᶜˡ β) for "classical comparisons" consisting of
order-preserving (bounded) maps.

NB. If this finds any application outside this file, then the code
    below should probably be moved to Ordinals.Maps.

\begin{code}

_≤ᶜˡ_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
α ≤ᶜˡ β = Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-order-preserving α β f

_<ᶜˡ_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
α <ᶜˡ β = Σ (f , _) ꞉ α ≤ᶜˡ β , Σ b₀ ꞉ ⟨ β ⟩ , ((a : ⟨ α ⟩) → f a ≺⟨ β ⟩ b₀)

module _ (α : Ordinal 𝓤) (β : Ordinal 𝓥) where

 <ᶜˡ-gives-≤ᶜˡ : α <ᶜˡ β → α ≤ᶜˡ β
 <ᶜˡ-gives-≤ᶜˡ (f , _ , _) = f

 ⊴-gives-≤ᶜˡ : α ⊴ β → α ≤ᶜˡ β
 ⊴-gives-≤ᶜˡ (f , f-sim) = f , simulations-are-order-preserving α β f f-sim

 ≤ᶜˡ-transitivity : (γ : Ordinal 𝓦) → α ≤ᶜˡ β → β ≤ᶜˡ γ → α ≤ᶜˡ γ
 ≤ᶜˡ-transitivity γ (f , f-order-pres) (g , g-order-pres) =
  g ∘ f , (λ a a' l → g-order-pres (f a) (f a') (f-order-pres a a' l))

 <ᶜˡ-≤ᶜˡ-to-<ᶜˡ : (γ : Ordinal 𝓦) → α <ᶜˡ β → β ≤ᶜˡ γ → α <ᶜˡ γ
 <ᶜˡ-≤ᶜˡ-to-<ᶜˡ γ (𝕗@(f , _) , b₀ , f-below-b₀) 𝕘@(g , g-order-pres) =
  ≤ᶜˡ-transitivity γ 𝕗 𝕘 , g b₀ , (λ a → g-order-pres (f a) b₀ (f-below-b₀ a))

 ≤ᶜˡ-<ᶜˡ-to-<ᶜˡ : (γ : Ordinal 𝓦) → α ≤ᶜˡ β → β <ᶜˡ γ → α <ᶜˡ γ
 ≤ᶜˡ-<ᶜˡ-to-<ᶜˡ γ 𝕗@(f , _) (𝕘@(g , _) , c₀ , g-below-c₀) =
  ≤ᶜˡ-transitivity γ 𝕗 𝕘 , c₀ , (λ a → g-below-c₀ (f a))

 <ᶜˡ-transitivity : (γ : Ordinal 𝓦) → α <ᶜˡ β → β <ᶜˡ γ → α <ᶜˡ γ
 <ᶜˡ-transitivity γ 𝕗 𝕘 = ≤ᶜˡ-<ᶜˡ-to-<ᶜˡ γ (<ᶜˡ-gives-≤ᶜˡ 𝕗) 𝕘

⊲-gives-<ᶜˡ : (α β : Ordinal 𝓤) → α ⊲ β → α <ᶜˡ β
⊲-gives-<ᶜˡ α β (b₀ , refl) =
 ⊴-gives-≤ᶜˡ (β ↓ b₀) β (segment-⊴ β b₀) , b₀ , segment-inclusion-bound β b₀

⊲-gives-not-≤ᶜˡ : (α β : Ordinal 𝓤) → α ⊲ β → ¬ (β ≤ᶜˡ α)
⊲-gives-not-≤ᶜˡ α β α-strictly-below-β β-below-α =
 order-preserving-gives-not-⊲ β α β-below-α α-strictly-below-β

<ᶜˡ-irrefl : (α : Ordinal 𝓤) → ¬ (α <ᶜˡ α)
<ᶜˡ-irrefl α ((f , f-order-pres) , a₀ , f-below-a₀) =
 ⊲-gives-not-≤ᶜˡ (α ↓ a₀) α (a₀ , refl) I
  where
   I : α ≤ᶜˡ (α ↓ a₀)
   I = (λ a → f a , f-below-a₀ a) , f-order-pres

⊴-gives-not-<ᶜˡ : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → α ⊴ β → ¬ (β <ᶜˡ α)
⊴-gives-not-<ᶜˡ α β 𝕗 𝕘 =
 <ᶜˡ-irrefl β (<ᶜˡ-≤ᶜˡ-to-<ᶜˡ β α β 𝕘 (⊴-gives-≤ᶜˡ α β 𝕗))

\end{code}

The second auxiliary notion is the following relation. The "unordered
order" derived from a given order relates (a, b) and (a', b') if
(a , b) is pointwise related to either (a', b') or (b', a') in the
original order.

NB. If this finds any application outside this file, then the code
    below should probably be moved to Ordinals.Notions.

\begin{code}

module uo-order
        (A : 𝓤 ̇ ) (_≺_ : A → A → 𝓥 ̇ )
       where

 _≺ᵤₒ_ : A × A → A × A → 𝓥 ̇
 (a₁ , b₁) ≺ᵤₒ (a₂ , b₂) = ((a₁ ≺ a₂) × (b₁ ≺ b₂)) + (a₁ ≺ b₂) × (b₁ ≺ a₂)

 ≺ᵤₒ-is-well-founded : is-well-founded _≺_ → is-well-founded _≺ᵤₒ_
 ≺ᵤₒ-is-well-founded wf = (λ (a , b) → pr₁ (II a b))
  where
   P : A → A → 𝓤 ⊔ 𝓥 ̇
   P a b = is-accessible _≺ᵤₒ_ (a , b) × is-accessible _≺ᵤₒ_ (b , a)

   I : (a : A)
     → ((a' : A) → a' ≺ a → (b : A) → P a' b)
     → (b : A) → P a b
   I a IH = transfinite-induction _≺_ wf (P a) h
    where
     h : (b : A) → ((b' : A) → b' ≺ b → P a b') → P a b
     h b IH' = acc h₁ , acc h₂
      where
       h₁ : (x : A × A) → x ≺ᵤₒ (a , b) → is-accessible _≺ᵤₒ_ x
       h₁ (a' , b') (inl (l₁ , l₂)) = pr₁ (IH a' l₁ b')
       h₁ (a' , b') (inr (l₁ , l₂)) = pr₂ (IH b' l₂ a')
       h₂ : (x : A × A) → x ≺ᵤₒ (b , a) → is-accessible _≺ᵤₒ_ x
       h₂ (a' , b') (inl (l₁ , l₂)) = pr₂ (IH b' l₂ a')
       h₂ (a' , b') (inr (l₁ , l₂)) = pr₁ (IH a' l₁ b')
   II : (a b : A) → P a b
   II = transfinite-induction _≺_ wf (λ a → (b : A) → P a b) I

\end{code}

We introduce additional assumptions on top of the abstract framework from the
file OperationsByCases.

\begin{code}

module framework
        (F : Ordinal 𝓤 → Ordinal 𝓤)
        (S : Ordinal 𝓤 → Ordinal 𝓤)
        (Z : Ordinal 𝓤)
        (F-succ : (β : Ordinal 𝓤) → F (β +ₒ 𝟙ₒ) ＝ S (F β))
        (F-sup : preserves-suprema-up-to-join F Z)
       where

 open operation-by-cases-framework F S Z F-succ F-sup

 Assumption-1 : 𝓤 ⁺ ̇
 Assumption-1 =
  Σ H ꞉ (Ordinal 𝓤 → Ordinal 𝓤) , ((β : Ordinal 𝓤) → S β ＝ β +ₒ H β)

 Assumption-2 : 𝓤 ⁺ ̇
 Assumption-2 = Σ (H , _) ꞉ Assumption-1 , ((β : Ordinal 𝓤) → 𝟘ₒ ⊲ H (F β))

 Assumption-3 : 𝓤 ⁺ ̇
 Assumption-3 = (β γ : Ordinal 𝓤) → β ≤ᶜˡ γ → S β ≤ᶜˡ S γ

\end{code}

The second assumption allows us to prove that F also preserves the
strict order.

\begin{code}

 F-preserves-⊲ : Assumption-2
               → (β γ : Ordinal 𝓤) → β ⊲ γ → F β ⊲ F γ
 F-preserves-⊲ ((H , S-H-eq) , H-has-min) β γ (c₀ , refl) = III
  where
   h₀ : ⟨ H (F (γ ↓ c₀)) ⟩
   h₀ = pr₁ (H-has-min (γ ↓ c₀))
   h₀-eq : H (F (γ ↓ c₀)) ↓ h₀ ＝ 𝟘ₒ
   h₀-eq = (pr₂ (H-has-min (γ ↓ c₀))) ⁻¹

   J : ⟨ γ ⟩ → Ordinal 𝓤
   J c = F (γ ↓ c) +ₒ H (F (γ ↓ c))

   [_,_] : (c : ⟨ γ ⟩) (h : ⟨ H (F (γ ↓ c)) ⟩) → ⟨ sup J ⟩
   [ c , h ] =
    [ F (γ ↓ c) +ₒ H (F (γ ↓ c)) , sup J ]⟨ sup-is-upper-bound J c ⟩ (inr h)

   I : sup J ↓ [ c₀ , h₀ ] ＝ F (γ ↓ c₀)
   I = sup J ↓ [ c₀ , h₀ ]                 ＝⟨ I₁ ⟩
       J c₀ ↓ inr h₀                       ＝⟨ (+ₒ-↓-right h₀) ⁻¹ ⟩
       F (γ ↓ c₀) +ₒ (H (F (γ ↓ c₀)) ↓ h₀) ＝⟨ ap (F (γ ↓ c₀) +ₒ_) h₀-eq ⟩
       F (γ ↓ c₀) +ₒ 𝟘ₒ                    ＝⟨ 𝟘ₒ-right-neutral (F (γ ↓ c₀)) ⟩
       F (γ ↓ c₀)                          ∎
    where
     I₁ = initial-segment-of-sup-at-component J c₀ (inr h₀)

   II : sup J ＝ F γ
   II = sup J                                             ＝⟨ II₁ ⟩
        extended-sup J Z                                  ＝⟨refl⟩
        extended-sup (λ c → F (γ ↓ c) +ₒ H (F (γ ↓ c))) Z ＝⟨ II₂ ⟩
        extended-sup (λ c → S (F (γ ↓ c))) Z              ＝⟨ II₃ ⟩
        F γ                                               ∎
     where
      II₁ = ⊴-antisym (sup J) (extended-sup J Z)
             (sup-composition-⊴ inr (cases (λ _ → Z) J))
             (sup-is-lower-bound-of-upper-bounds (cases (λ _ → Z) J) (sup J) ub)
       where
        ub : (i : 𝟙 + ⟨ γ ⟩) → cases (λ _ → Z) J i ⊴ sup J
        ub (inl ⋆) = ⊴-trans Z (F (γ ↓ c₀)) (sup J)
                      (least-value-if-preserves-suprema-up-to-join
                        F Z F-sup (γ ↓ c₀))
                      (⊴-trans (F (γ ↓ c₀)) (J c₀) (sup J)
                        (+ₒ-left-⊴ (F (γ ↓ c₀)) (H (F (γ ↓ c₀))))
                        (sup-is-upper-bound J c₀))
        ub (inr c) = sup-is-upper-bound J c
      II₂ = ap (λ - → extended-sup - Z)
               (dfunext fe' (λ c → (S-H-eq (F (γ ↓ c))) ⁻¹))
      II₃ = (recursive-equation γ) ⁻¹

   III : F (γ ↓ c₀) ⊲ F γ
   III = Idtofunₒ II [ c₀ , h₀ ] , (I ⁻¹ ∙ Idtofunₒ-↓-lemma II)

\end{code}

The following two results are technical auxiliary lemmas.

\begin{code}

 F-tightening-bounds
  : Assumption-1
  → (β : Ordinal 𝓤)
  → F 𝟘ₒ ⊴ β
  → (γ : Ordinal 𝓤)
  → β ⊲ F γ
  → ∃ γ' ꞉ Ordinal 𝓤 , (γ' ⊲ γ) × (F γ' ⊴ β) × (β ⊲ F (γ' +ₒ 𝟙ₒ))
 F-tightening-bounds (H , H-S-eq) β β-ineq = transfinite-induction-on-OO Q I
  where
   P : Ordinal 𝓤 → Ordinal 𝓤 → (𝓤 ⁺) ̇
   P γ γ' = (γ' ⊲ γ) × (F γ' ⊴ β) × (β ⊲ F (γ' +ₒ 𝟙ₒ))
   Q : Ordinal 𝓤 → (𝓤 ⁺) ̇
   Q γ = β ⊲ F γ → ∃ γ' ꞉ Ordinal 𝓤 , P γ γ'

   I : (γ : Ordinal 𝓤) → ((c : ⟨ γ ⟩) → Q (γ ↓ c)) → Q γ
   I γ IH (x' , refl) =
    ∥∥-rec ∃-is-prop III
      (initial-segment-of-sup-is-initial-segment-of-some-component _ x)
     where
      x = Idtofunₒ (recursive-equation γ) x'

      II : β ＝ (extended-sup (λ c → S (F (γ ↓ c))) Z) ↓ x
      II = Idtofunₒ-↓-lemma (recursive-equation γ)

      III : (Σ i ꞉ 𝟙 + ⟨ γ ⟩ ,
             Σ y ꞉ ⟨ cases (λ _ → Z) (λ c → S (F (γ ↓ c))) i ⟩ ,
              (extended-sup (λ c → S (F (γ ↓ c))) Z) ↓ x
              ＝ cases (λ _ → Z) (λ c → S (F (γ ↓ c))) i ↓ y)
          → ∃ γ' ꞉ Ordinal 𝓤 , P γ γ'
      III (inl ⋆ , y , p) = 𝟘-elim (⊴-gives-not-⊲ (F 𝟘ₒ) β β-ineq l')
       where
        l : β ⊲ Z
        l = y , (II ∙ p)
        l' : β ⊲ F 𝟘ₒ
        l' = transport⁻¹ (β ⊲_)
              (preserves-suprema-up-to-join-implies-zero-equation F Z F-sup)
              l
      III (inr c , y , p) = IV y' (p' ∙ Idtofunₒ-↓-lemma (H-S-eq (F (γ ↓ c))))
       where
        p' : β ＝ S (F (γ ↓ c)) ↓ y
        p' = II ∙ p
        y' : ⟨ F (γ ↓ c) +ₒ H (F (γ ↓ c)) ⟩
        y' = Idtofunₒ (H-S-eq (F (γ ↓ c))) y

        IV : (y' : ⟨ F (γ ↓ c) +ₒ H (F (γ ↓ c)) ⟩)
           → β ＝ (F (γ ↓ c) +ₒ H (F (γ ↓ c))) ↓ y'
           → ∃ γ' ꞉ Ordinal 𝓤 , P γ γ'
        IV (inl z) q = ∥∥-functor IV' ih
         where
          ih : ∃ γ' ꞉ Ordinal 𝓤 , P (γ ↓ c) γ'
          ih = IH c (z , (q ∙ (+ₒ-↓-left z) ⁻¹))
          IV' : Σ γ' ꞉ Ordinal 𝓤 , P (γ ↓ c) γ' → Σ γ' ꞉ Ordinal 𝓤 , P γ γ'
          IV' (γ' , k , l , m) =
           γ' , ⊲-⊴-gives-⊲ γ' (γ ↓ c) γ k (segment-⊴ γ c) , l , m
        IV (inr z) q = ∣ γ ↓ c , (c , refl) , IV₁ , IV₂ ∣
         where
          IV₁ : F (γ ↓ c) ⊴ β
          IV₁ = transport⁻¹ (F (γ ↓ c) ⊴_) e
                            (+ₒ-left-⊴ (F (γ ↓ c)) (H (F (γ ↓ c)) ↓ z))
           where
            e = β                                  ＝⟨ q ⟩
                F (γ ↓ c) +ₒ H (F (γ ↓ c)) ↓ inr z ＝⟨ (+ₒ-↓-right z) ⁻¹ ⟩
                F (γ ↓ c) +ₒ (H (F (γ ↓ c)) ↓ z)   ∎

          IV₂ : β ⊲ F ((γ ↓ c) +ₒ 𝟙ₒ)
          IV₂ = Idtofunₒ ((F-succ (γ ↓ c)) ⁻¹) y ,
                (II ∙ p ∙ Idtofunₒ-↓-lemma ((F-succ (γ ↓ c)) ⁻¹))

 F-impossibility : Assumption-3
                 → (β γ δ : Ordinal 𝓤) (b : ⟨ β ⟩)
                 → F γ ⊴ F (β ↓ b)
                 → F β ⊴ F γ +ₒ δ
                 → F γ +ₒ δ ⊲ F (γ +ₒ 𝟙ₒ)
                 → 𝟘
 F-impossibility asm-3 β γ δ b l₁ l₂ l₃ =
  <ᶜˡ-irrefl (S (F γ)) IV
   where
    I : S (F γ) ≤ᶜˡ S (F (β ↓ b))
    I = asm-3 (F γ) (F (β ↓ b)) (⊴-gives-≤ᶜˡ (F γ) (F (β ↓ b)) l₁)

    II : S (F γ) ≤ᶜˡ F ((β ↓ b) +ₒ 𝟙ₒ)
    II = transport⁻¹ (S (F γ) ≤ᶜˡ_) (F-succ (β ↓ b)) I

    III : F ((β ↓ b) +ₒ 𝟙ₒ) ≤ᶜˡ (F γ +ₒ δ)
    III = ≤ᶜˡ-transitivity (F ((β ↓ b) +ₒ 𝟙ₒ)) (F β) (F γ +ₒ δ)
           (⊴-gives-≤ᶜˡ (F ((β ↓ b) +ₒ 𝟙ₒ)) (F β)
             (is-monotone-if-preserves-suprema-up-to-join F Z F-sup
               ((β ↓ b) +ₒ 𝟙ₒ) β
               (upper-bound-of-successors-of-initial-segments β b)))
           (⊴-gives-≤ᶜˡ (F β) (F γ +ₒ δ) l₂)

    IV₁ : S (F γ) ≤ᶜˡ (F γ +ₒ δ)
    IV₁ = ≤ᶜˡ-transitivity (S (F γ)) (F ((β ↓ b) +ₒ 𝟙ₒ)) (F γ +ₒ δ) II III

    IV₂ : (F γ +ₒ δ) <ᶜˡ S (F γ)
    IV₂ = transport ((F γ +ₒ δ) <ᶜˡ_) (F-succ γ)
                    (⊲-gives-<ᶜˡ (F γ +ₒ δ) (F (γ +ₒ 𝟙ₒ)) l₃)

    IV : S (F γ) <ᶜˡ S (F γ)
    IV = ≤ᶜˡ-<ᶜˡ-to-<ᶜˡ (S (F γ)) (F γ +ₒ δ) (S (F γ)) IV₁ IV₂

\end{code}

The following result is later instantiated with δ ＝ 𝟘ₒ to get that F
is order reflecting. The more technical formulation below allows us to
give a proof by transfinite induction.

\begin{code}

 F-reflects-⊴' : -- Assumption-1 -- redundant in the presence of Assumption-2
                 Assumption-2
               → Assumption-3
               → (β γ δ : Ordinal 𝓤)
               → F β ⊴ F γ +ₒ δ
               → F γ +ₒ δ ⊲ F (γ +ₒ 𝟙ₒ)
               → β ⊴ γ
 F-reflects-⊴' asm-2@((H , H-S-eq) , H-has-min) asm-3 = (λ β γ → VI (β , γ))
  where
   open uo-order (Ordinal 𝓤) _⊲_
   P : Ordinal 𝓤 × Ordinal 𝓤 → 𝓤 ⁺ ̇
   P (β , γ) =
    (δ : Ordinal 𝓤) → F β ⊴ F γ +ₒ δ → F γ +ₒ δ ⊲ F (γ +ₒ 𝟙ₒ) → β ⊴ γ

   I : (X : Ordinal 𝓤 × Ordinal 𝓤)
     → ((Y : Ordinal 𝓤 × Ordinal 𝓤) → Y ≺ᵤₒ X → P Y)
     → P X
   I (β , γ) IH δ l₁ l₂ = to-⊴ β γ V
    where
     module _ (b : ⟨ β ⟩) where
      II₁ : F 𝟘ₒ ⊴ F (β ↓ b)
      II₁ = is-monotone-if-preserves-suprema-up-to-join
             F Z F-sup 𝟘ₒ (β ↓ b) (𝟘ₒ-least-⊴ (β ↓ b))
      II₂ : F (β ↓ b) ⊲ F (γ +ₒ 𝟙ₒ)
      II₂ = ⊲-⊴-gives-⊲ (F (β ↓ b)) (F β) (F (γ +ₒ 𝟙ₒ))
             (F-preserves-⊲ asm-2 (β ↓ b) β (b , refl))
             (⊴-trans (F β) (F γ +ₒ δ) (F (γ +ₒ 𝟙ₒ))
               l₁
               (⊲-gives-⊴ (F γ +ₒ δ) (F (γ +ₒ 𝟙ₒ)) l₂))
      II : ∃ γ' ꞉ Ordinal 𝓤 , (γ' ⊲ γ +ₒ 𝟙ₒ)
                            × (F γ' ⊴ F (β ↓ b))
                            × (F (β ↓ b) ⊲ F (γ' +ₒ 𝟙ₒ))
      II = F-tightening-bounds (H , H-S-eq) (F (β ↓ b)) II₁ (γ +ₒ 𝟙ₒ) II₂

      III : ¬ (F ((γ +ₒ 𝟙ₒ) ↓ inr ⋆) ⊴ F (β ↓ b))
      III l = F-impossibility asm-3 β γ δ b k l₁ l₂
       where
        k : F γ ⊴ F (β ↓ b)
        k = transport⁻¹ (_⊴ F (β ↓ b)) (ap F ((successor-lemma-right γ) ⁻¹)) l

      IV : (c : ⟨ γ ⟩)
         → F (γ ↓ c) ⊴ F (β ↓ b)
         → F (β ↓ b) ⊲ F ((γ ↓ c) +ₒ 𝟙ₒ)
         → β ↓ b ＝ γ ↓ c
      IV c k₁ k₂ = ⊴-antisym (β ↓ b) (γ ↓ c) IV₁ IV₂
       where
        IV₂ : γ ↓ c ⊴ β ↓ b
        IV₂ = IH (γ ↓ c , β ↓ b) (inr ((c , refl) , (b , refl))) 𝟘ₒ
             (transport⁻¹ (F (γ ↓ c) ⊴_) (𝟘ₒ-right-neutral (F (β ↓ b))) k₁)
             (transport⁻¹ (_⊲ F ((β ↓ b) +ₒ 𝟙ₒ)) (𝟘ₒ-right-neutral (F (β ↓ b)))
               (F-preserves-⊲ asm-2 (β ↓ b)
                                    ((β ↓ b) +ₒ 𝟙ₒ)
                                    (successor-increasing (β ↓ b))))

        IV₁ : β ↓ b ⊴ γ ↓ c
        IV₁ = IV₁ᵇ z z-eq
         where
          IV₁ᵃ : F ((γ ↓ c) +ₒ 𝟙ₒ) ＝ F (γ ↓ c) +ₒ H (F (γ ↓ c))
          IV₁ᵃ = F-succ (γ ↓ c) ∙ H-S-eq (F (γ ↓ c))
          z : ⟨ F (γ ↓ c) +ₒ H (F (γ ↓ c)) ⟩
          z = Idtofunₒ IV₁ᵃ (pr₁ k₂)
          z-eq : F (β ↓ b) ＝ (F (γ ↓ c) +ₒ H (F (γ ↓ c))) ↓ z
          z-eq = pr₂ k₂ ∙ Idtofunₒ-↓-lemma IV₁ᵃ
          IV₁ᵇ : (z : ⟨ F (γ ↓ c) +ₒ H (F (γ ↓ c)) ⟩)
               → F (β ↓ b) ＝ (F (γ ↓ c) +ₒ H (F (γ ↓ c))) ↓ z
               → β ↓ b ⊴ γ ↓ c
          IV₁ᵇ (inl z₀) z-eq =
           𝟘-elim (⊴-gives-not-⊲ (F (γ ↓ c)) (F (β ↓ b))
                    k₁
                    (z₀ , (z-eq ∙ (+ₒ-↓-left z₀) ⁻¹)))
          IV₁ᵇ (inr z₀) z-eq =
           IH (β ↓ b , γ ↓ c)
              (inl ((b , refl) , (c , refl)))
              δ' m₁ m₂
            where
             δ' = H (F (γ ↓ c)) ↓ z₀
             m₁ : F (β ↓ b) ⊴ F (γ ↓ c) +ₒ δ'
             m₁ = ＝-to-⊴ (F (β ↓ b))
                          (F (γ ↓ c) +ₒ δ')
                          (z-eq ∙ (+ₒ-↓-right z₀) ⁻¹)
             m₂ : F (γ ↓ c) +ₒ δ' ⊲ F ((γ ↓ c) +ₒ 𝟙ₒ)
             m₂ = transport⁻¹ (_⊲ F ((γ ↓ c) +ₒ 𝟙ₒ))
                              (+ₒ-↓-right z₀ ∙ z-eq ⁻¹)
                              k₂

      V : β ↓ b ⊲ γ
      V = ∥∥-rec (⊲-is-prop-valued (β ↓ b) γ) g II
       where
        g : (Σ γ' ꞉ Ordinal 𝓤 , (γ' ⊲ γ +ₒ 𝟙ₒ)
                              × (F γ' ⊴ F (β ↓ b))
                              × (F (β ↓ b) ⊲ F (γ' +ₒ 𝟙ₒ)))
          → β ↓ b ⊲ γ
        g (γ' , (inl c , refl) , k₁ , k₂) = c , (IV c k₁' k₂')
         where
          k₁' : F (γ ↓ c) ⊴ F (β ↓ b)
          k₁' = transport⁻¹ (_⊴ F (β ↓ b)) (ap F (+ₒ-↓-left c)) k₁
          k₂' : F (β ↓ b) ⊲ F ((γ ↓ c) +ₒ 𝟙ₒ)
          k₂' = transport⁻¹ (F (β ↓ b) ⊲_) (ap F (ap (_+ₒ 𝟙ₒ) (+ₒ-↓-left c))) k₂
        g (γ' , (inr ⋆ , refl) , k₁ , k₂) = 𝟘-elim (III k₁)

   VI : Π P
   VI = transfinite-induction _≺ᵤₒ_ (≺ᵤₒ-is-well-founded ⊲-is-well-founded) P I

\end{code}

As desired, F is order reflecting, in the presence of assumptions 2
and 3, and hence also left cancellable (a.k.a. injective).

\begin{code}

 module framework-with-assumptions
         (asm-2 : Assumption-2)
         (asm-3 : Assumption-3)
        where

  F-reflects-⊴ : is-⊴-reflecting F
  F-reflects-⊴ β γ l =
   F-reflects-⊴' asm-2 asm-3 β γ 𝟘ₒ
    (transport⁻¹ (F β ⊴_) (𝟘ₒ-right-neutral (F γ)) l)
    (transport⁻¹
      (_⊲ F (γ +ₒ 𝟙ₒ))
      (𝟘ₒ-right-neutral (F γ))
      (F-preserves-⊲ asm-2 γ (γ +ₒ 𝟙ₒ) (successor-increasing γ)))

  F-left-cancellable : left-cancellable F
  F-left-cancellable p =
   ⊴-antisym _ _ (F-reflects-⊴ _ _ (＝-to-⊴ _ _ p))
                 (F-reflects-⊴ _ _ (＝-to-⊴ _ _ (p ⁻¹)))

\end{code}

We now instantiate the above framework with F ＝ (-) +ₒ α, and show
that the assumptions are satisfied in this case, to conclude that
addition by α is order reflecting.

\begin{code}

module _ (α : Ordinal 𝓤) where
 private
  open addition-by-fixed-ordinal
  open framework
        (α +ₒ_)
        (_+ₒ 𝟙ₒ)
        α
        (+ₒ-commutes-with-successor α)
        (+ₒ-preserves-suprema-up-to-join α)

  asm-2 : Σ (H , _) ꞉ (Σ H ꞉ (Ordinal 𝓤 → Ordinal 𝓤)
              , ((β : Ordinal 𝓤) → β +ₒ 𝟙ₒ ＝ β +ₒ H β))
              , ((β : Ordinal 𝓤) → 𝟘ₒ ⊲ H (α +ₒ β))
  asm-2 = ((λ β → 𝟙ₒ) , (λ β → refl)) , (λ β → ⋆ , (𝟙ₒ-↓ ⁻¹))

  asm-3 : (β γ : Ordinal 𝓤) → β ≤ᶜˡ γ → (β +ₒ 𝟙ₒ) ≤ᶜˡ (γ +ₒ 𝟙ₒ)
  asm-3 β γ (f , f-order-pres) = g , g-order-pres
   where
    g : ⟨ β +ₒ 𝟙ₒ ⟩ → ⟨ γ +ₒ 𝟙ₒ ⟩
    g (inl b) = inl (f b)
    g (inr ⋆) = inr ⋆
    g-order-pres : is-order-preserving (β +ₒ 𝟙ₒ) (γ +ₒ 𝟙ₒ) g
    g-order-pres (inl b) (inl b') l = f-order-pres b b' l
    g-order-pres (inl b) (inr ⋆)  l = ⋆
    g-order-pres (inr ⋆) (inl b)  l = l
    g-order-pres (inr ⋆) (inr ⋆)  l = l

  open framework-with-assumptions asm-2 asm-3

 +ₒ-reflects-⊴ : is-⊴-reflecting (α +ₒ_)
 +ₒ-reflects-⊴ = F-reflects-⊴

 +ₒ-left-cancellable' : left-cancellable (α +ₒ_)
 +ₒ-left-cancellable' = F-left-cancellable

\end{code}

We now instantiate the above framework with F ＝ (-) ×ₒ α, and show
that the assumptions are satisfied when 𝟘ₒ ⊲ α, to conclude that
multiplication by α is order reflecting (when 𝟘ₒ ⊲ α).

\begin{code}

module _ (α : Ordinal 𝓤) where
 private
  open framework
        (α ×ₒ_)
        (_+ₒ α)
        𝟘ₒ
        (×ₒ-successor α)
        (rl-implication
          (preservation-of-suprema-continuity-equivalence (α ×ₒ_))
          (×ₒ-is-continuous pt sr α))

  asm-2 : 𝟘ₒ ⊲ α
        → Σ (H , _) ꞉ (Σ H ꞉ (Ordinal 𝓤 → Ordinal 𝓤)
              , ((β : Ordinal 𝓤) → β +ₒ α ＝ β +ₒ H β))
              , ((β : Ordinal 𝓤) → 𝟘ₒ ⊲ H (α ×ₒ β))
  asm-2 α-pos =
   ((λ β → α) , (λ β → refl)) , (λ β → α-pos)

  asm-3 : (β γ : Ordinal 𝓤) → β ≤ᶜˡ γ → (β +ₒ α) ≤ᶜˡ (γ +ₒ α)
  asm-3 β γ (f , f-order-pres) = +functor f id , h
   where
    h : is-order-preserving (β +ₒ α) (γ +ₒ α) (+functor f id)
    h (inl b) (inl b') l = f-order-pres b b' l
    h (inl b) (inr a) l = ⋆
    h (inr a) (inl b) l = l
    h (inr a) (inr a') l = l

  module fwa (α-pos : 𝟘ₒ ⊲ α) where
   open framework-with-assumptions (asm-2 α-pos) asm-3 public

 ×ₒ-reflects-⊴ : 𝟘ₒ ⊲ α → is-⊴-reflecting (α ×ₒ_)
 ×ₒ-reflects-⊴ = fwa.F-reflects-⊴

 ×ₒ-left-cancellable' : 𝟘ₒ ⊲ α → left-cancellable (α ×ₒ_)
 ×ₒ-left-cancellable' = fwa.F-left-cancellable

\end{code}

We now instantiate the above framework with F ＝ (-) ^ₒ α, and show
that the assumptions are satisfied when 𝟚ₒ ⊴ α and α further has a
trichotomous least element, to conclude that exponentiation by α is
order reflecting (under the conditions mentioned).

\begin{code}

module _
        (α : Ordinal 𝓤)
        (α-at-least-𝟚ₒ : 𝟚ₒ ⊴ α)
       where
 private
  α-has-least : 𝟙ₒ ⊴ α
  α-has-least = ⊴-trans 𝟙ₒ 𝟚ₒ α (+ₒ-left-⊴ 𝟙ₒ 𝟙ₒ) α-at-least-𝟚ₒ

  open framework
        (α ^ₒ_)
        (_×ₒ α)
        𝟙ₒ
        (^ₒ-satisfies-succ-specification α α-has-least)
        (^ₒ-satisfies-zero-sup-combined-specification α)

  asm-2 : has-trichotomous-least-element α
        →  Σ (H , _) ꞉ (Σ H ꞉ (Ordinal 𝓤 → Ordinal 𝓤)
              , ((β : Ordinal 𝓤) → β ×ₒ α ＝ β +ₒ H β))
              , ((β : Ordinal 𝓤) → 𝟘ₒ ⊲ H (α ^ₒ β))
  asm-2 h = (H , e) , H-has-min
   where
    e : (β : Ordinal 𝓤) → β ×ₒ α ＝ β +ₒ (β ×ₒ α ⁺[ h ])
    e β = β ×ₒ α                     ＝⟨ e₁ ⟩
          β ×ₒ (𝟙ₒ +ₒ α ⁺[ h ])      ＝⟨ e₂ ⟩
          β ×ₒ 𝟙ₒ +ₒ β ×ₒ (α ⁺[ h ]) ＝⟨ e₃ ⟩
          β +ₒ β ×ₒ (α ⁺[ h ])       ∎
     where
      e₁ = ap (β ×ₒ_) (α ⁺[ h ]-part-of-decomposition)
      e₂ = ×ₒ-distributes-+ₒ-right β 𝟙ₒ (α ⁺[ h ])
      e₃ = ap (_+ₒ β ×ₒ (α ⁺[ h ])) (𝟙ₒ-right-neutral-×ₒ β)

    H : Ordinal 𝓤 → Ordinal 𝓤
    H β = β ×ₒ (α ⁺[ h ])
    α⁺-pos : 𝟙ₒ ⊴ α ⁺[ h ]
    α⁺-pos =
     +ₒ-reflects-⊴ 𝟙ₒ 𝟙ₒ
      (α ⁺[ h ])
      (transport (𝟚ₒ ⊴_) (α ⁺[ h ]-part-of-decomposition) α-at-least-𝟚ₒ)

    H-has-min' : (γ : Ordinal 𝓤) → 𝟙ₒ ⊴ γ → 𝟙ₒ ⊴ H γ
    H-has-min' γ l =
     to-⊴ 𝟙ₒ (H γ) λ ⋆ → (f ⋆ , g ⋆) ,
     (𝟙ₒ ↓ ⋆ ＝⟨ 𝟙ₒ-↓ ⟩
      𝟘ₒ ＝⟨ (×ₒ-𝟘ₒ-right γ) ⁻¹ ⟩
      γ ×ₒ 𝟘ₒ                            ＝⟨ I ⟩
      γ ×ₒ (α ⁺[ h ] ↓ g ⋆)              ＝⟨ II ⟩
      γ ×ₒ (α ⁺[ h ] ↓ g ⋆) +ₒ 𝟘ₒ        ＝⟨ III ⟩
      γ ×ₒ (α ⁺[ h ] ↓ g ⋆) +ₒ (γ ↓ f ⋆) ＝⟨ (×ₒ-↓ γ (α ⁺[ h ])) ⁻¹ ⟩
      γ ×ₒ (α ⁺[ h ]) ↓ (f ⋆ , g ⋆)      ＝⟨refl⟩
      H γ ↓ (f ⋆ , g ⋆) ∎)
     where
      f = pr₁ l
      g = pr₁ α⁺-pos

      I   = ap (γ ×ₒ_) (𝟙ₒ-↓ ⁻¹ ∙ simulations-preserve-↓ 𝟙ₒ (α ⁺[ h ]) α⁺-pos ⋆)
      II  = (𝟘ₒ-right-neutral (γ ×ₒ (α ⁺[ h ] ↓ g ⋆))) ⁻¹
      III = ap (γ ×ₒ ((α ⁺[ h ]) ↓ g ⋆) +ₒ_)
               (((simulations-preserve-↓ 𝟙ₒ γ l ⋆) ⁻¹ ∙ 𝟙ₒ-↓) ⁻¹)
    H-has-min : (β : Ordinal 𝓤) → 𝟘ₒ ⊲ H (α ^ₒ β)
    H-has-min β = lr-implication (at-least-𝟙₀-iff-greater-than-𝟘ₒ (H (α ^ₒ β)))
                                 (H-has-min' (α ^ₒ β) (^ₒ-has-least-element α β))

  asm-3 : (β γ : Ordinal 𝓤) → β ≤ᶜˡ γ → (β ×ₒ α) ≤ᶜˡ (γ ×ₒ α)
  asm-3 β γ (f , f-order-pres) = g , g-order-pres
   where
    g : ⟨ β ×ₒ α ⟩ → ⟨ γ ×ₒ α ⟩
    g (b , a) = (f b , a)
    g-order-pres : is-order-preserving (β ×ₒ α) (γ ×ₒ α) g
    g-order-pres (b , a) (c , a') (inl l) = inl l
    g-order-pres (b , a) (c , a') (inr (refl , l)) = inr (refl , f-order-pres b c l)

  module fwa
          (α-htle : has-trichotomous-least-element α)
         where
   open framework-with-assumptions (asm-2 α-htle) asm-3 public

 ^ₒ-reflects-⊴ : has-trichotomous-least-element α
               → is-⊴-reflecting (α ^ₒ_)
 ^ₒ-reflects-⊴ = fwa.F-reflects-⊴

 ^ₒ-left-cancellable : has-trichotomous-least-element α
                     → left-cancellable (α ^ₒ_)
 ^ₒ-left-cancellable = fwa.F-left-cancellable

\end{code}

The results above imply that any simulation

  (α +ₒ β) ⊴ (α +ₒ γ)
  (α ×ₒ β) ⊴ (α ×ₒ γ)
  (α ^ₒ β) ⊴ (α ^ₒ γ)

computes in the expected way, i.e., that they are all induced from a
simulation β ⊴ γ and leave elements of α untouched.

\begin{code}

+ₒ-simulation-behaviour
 : (α β γ : Ordinal 𝓤)
 → ((g , _) : α +ₒ β ⊴ α +ₒ γ)
 → Σ (f , _) ꞉ β ⊴ γ , ((a : ⟨ α ⟩) → g (inl a) ＝ inl a)
                     × ((b : ⟨ β ⟩) → g (inr b) ＝ inr (f b))
+ₒ-simulation-behaviour α β γ 𝕘@(g , g-sim) = 𝕗 , III , IV
 where
  𝕗 : β ⊴ γ
  𝕗 = +ₒ-reflects-⊴ α β γ 𝕘
  f = pr₁ 𝕗
  𝕙 : α +ₒ β ⊴ α +ₒ γ
  𝕙 = +ₒ-right-monotone-⊴' α β γ 𝕗
  h = pr₁ 𝕙
  I : (a : ⟨ α ⟩) → h (inl a) ＝ inl a
  I a = refl
  II : (b : ⟨ β ⟩) → h (inr b) ＝ inr (f b)
  II b = refl
  𝕘-is-𝕙 : 𝕘 ＝ 𝕙
  𝕘-is-𝕙 = ⊴-is-prop-valued (α +ₒ β) (α +ₒ γ) 𝕘 𝕙
  III : (a : ⟨ α ⟩) → g (inl a) ＝ inl a
  III a = happly (ap pr₁ 𝕘-is-𝕙) (inl a)
  IV : (b : ⟨ β ⟩) → g (inr b) ＝ inr (f b)
  IV b = happly (ap pr₁ 𝕘-is-𝕙) (inr b)

×ₒ-simulation-behaviour
 : (α β γ : Ordinal 𝓤)
 → 𝟘ₒ ⊲ α
 → ((g , _) : α ×ₒ β ⊴ α ×ₒ γ)
 → Σ (f , _) ꞉ β ⊴ γ , ((a : ⟨ α ⟩) (b : ⟨ β ⟩) → g (a , b) ＝ (a , f b))
×ₒ-simulation-behaviour α β γ α-pos 𝕘@(g , g-sim) = 𝕗 , II
 where
  𝕗 : β ⊴ γ
  𝕗 = ×ₒ-reflects-⊴ α α-pos β γ 𝕘
  f = pr₁ 𝕗
  𝕙 : α ×ₒ β ⊴ α ×ₒ γ
  𝕙 = ×ₒ-right-monotone-⊴ α β γ 𝕗
  h = pr₁ 𝕙
  I : (a : ⟨ α ⟩) (b : ⟨ β ⟩) → h (a , b) ＝ (a , f b)
  I a b = refl
  𝕘-is-𝕙 : 𝕘 ＝ 𝕙
  𝕘-is-𝕙 = ⊴-is-prop-valued (α ×ₒ β) (α ×ₒ γ) 𝕘 𝕙
  II : (a : ⟨ α ⟩) (b : ⟨ β ⟩) → g (a , b) ＝ (a , f b)
  II a b = happly (ap pr₁ 𝕘-is-𝕙) (a , b)

\end{code}

For exponentiation, the property seems most conveniently expressed for
the list-based representation.

\begin{code}

exponentiationᴸ-simulation-behaviour
 : (α β γ : Ordinal 𝓤)
 → (h : has-trichotomous-least-element α)
 → 𝟚ₒ ⊴ α
 → ((g , _) : exponentiationᴸ α h β ⊴ exponentiationᴸ α h γ)
 → Σ (f , _) ꞉ β ⊴ γ ,
     (((l , δ) : DecrList₂ (α ⁺[ h ]) β)
               → DecrList₂-list (α ⁺[ h ]) γ (g (l , δ))
                 ＝ map (λ (a , b) → (a , f b)) l)
exponentiationᴸ-simulation-behaviour α β γ ht α-at-least-𝟚ₒ 𝕘@(g , g-sim) =
 𝕗 , II
  where
   𝕗 : β ⊴ γ
   𝕗 = ^ₒ-reflects-⊴ α
        α-at-least-𝟚ₒ
        ht
        β γ
        (transport₂ _⊴_
          (exponentiation-constructions-agree α β ht)
          (exponentiation-constructions-agree α γ ht)
          𝕘)
   f = pr₁ 𝕗
   𝕙 : exponentiationᴸ α ht β ⊴ exponentiationᴸ α ht γ
   𝕙 = expᴸ-is-monotone-in-exponent (α ⁺[ ht ]) β γ 𝕗
   h = pr₁ 𝕙
   I : (((l , δ) : DecrList₂ (α ⁺[ ht ]) β)
     → DecrList₂-list (α ⁺[ ht ]) γ (h (l , δ))
       ＝ map (λ (a , b) → (a , f b)) l)
   I (l , δ) = refl
   𝕘-is-𝕙 : 𝕘 ＝ 𝕙
   𝕘-is-𝕙 =
    ⊴-is-prop-valued (exponentiationᴸ α ht β) (exponentiationᴸ α ht γ) 𝕘 𝕙
   II : (((l , δ) : DecrList₂ (α ⁺[ ht ]) β)
      → DecrList₂-list (α ⁺[ ht ]) γ (g (l , δ))
        ＝ map (λ (a , b) → (a , f b)) l)
   II (l , δ) =
    ap (DecrList₂-list (α ⁺[ ht ]) γ) (happly (ap pr₁ 𝕘-is-𝕙) (l , δ))

\end{code}
