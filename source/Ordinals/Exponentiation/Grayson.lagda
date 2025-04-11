Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu.
April 2025.

An implementation of Robin Grayson's variant of the decreasing list
construction of exponentials.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc

module Ordinals.Exponentiation.Grayson
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       where

open import UF.FunExt
open import UF.UA-FunExt
open import UF.Subsingletons

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua


open import MLTT.List
open import MLTT.Plus-Properties
open import MLTT.Spartan

open import UF.Base
open import UF.Equiv
open import UF.Subsingletons-FunExt

open import Ordinals.Arithmetic fe
open import Ordinals.AdditionProperties ua
open import Ordinals.Equivalence
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua renaming (_≼_ to _≼OO_)
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.WellOrderArithmetic

open import Ordinals.Exponentiation.TrichotomousLeastElement ua
open import Ordinals.Exponentiation.DecreasingList ua

open PropositionalTruncation pt

\end{code}

\begin{code}

data All {X : 𝓤 ̇ } (P : X → 𝓥 ̇ ) : List X → 𝓤 ⊔ 𝓥 ̇  where
  [] : All P []
  _∷_ : {x : X}{xs : List X} → P x → All P xs → All P (x ∷ xs)

All-is-prop : {X : 𝓤 ̇ } (P : X → 𝓥 ̇ )
            → is-prop-valued-family P
            → is-prop-valued-family (All P)
All-is-prop P p [] [] [] = refl
All-is-prop P p (x ∷ l) (a ∷ as) (a' ∷ as') =
 ap₂ _∷_ (p x a a') (All-is-prop P p l as as')

is-positively-non-minimal : {A : 𝓤 ̇  } (R : A → A → 𝓥 ̇  ) → A → 𝓤 ⊔ 𝓥 ̇
is-positively-non-minimal {A = A} R x = ∃ a ꞉ A ,  R a x

\end{code}

\begin{code}

is-positively-non-minimal-iff-positive
 : (α : Ordinal 𝓤)
 → ((⊥ , τ) : has-trichotomous-least-element α)
 → (x : ⟨ α ⟩) → is-positively-non-minimal (underlying-order α) x ↔ ⊥ ≺⟨ α ⟩ x
is-positively-non-minimal-iff-positive α (⊥ , τ) x =
 (∥∥-rec (Prop-valuedness α ⊥ x) I) , (λ l → ∣ ⊥ , l ∣)
 where
   I : (Σ a ꞉ ⟨ α ⟩ , a ≺⟨ α ⟩ x)
     → ⊥ ≺⟨ α ⟩ x
   I (a , l) = I' (τ a)
    where
     I' : (⊥ ＝ a) + (⊥ ≺⟨ α ⟩ a) → ⊥ ≺⟨ α ⟩ x
     I' (inl refl) = l
     I' (inr k) = Transitivity α ⊥ a x k l

\end{code}

\begin{code}

module _ {A B : 𝓤 ̇  } (R : A → A → 𝓥 ̇  )(R' : B → B → 𝓥 ̇  ) where


 is-grayson : List (A × B) → 𝓤 ⊔ 𝓥 ̇
 is-grayson l = is-decreasing R' (map pr₂ l)
              × All (is-positively-non-minimal R) (map pr₁ l)

 is-grayson-is-prop : is-prop-valued R'
                    → is-prop-valued-family is-grayson
 is-grayson-is-prop p' l =
  ×-is-prop (is-decreasing-is-prop R' p' (map pr₂ l))
            (All-is-prop _ (λ x → ∃-is-prop) (map pr₁ l))

 GraysonList : 𝓤 ⊔ 𝓥 ̇
 GraysonList = Σ l ꞉ List (A × B) , is-grayson l

 GraysonList-list : GraysonList → List (A × B)
 GraysonList-list = pr₁

 to-GraysonList-＝ : is-prop-valued R'
                   → {l l' : GraysonList}
                   → GraysonList-list l ＝ GraysonList-list l' → l ＝ l'
 to-GraysonList-＝ p' = to-subtype-＝ (is-grayson-is-prop p')

 Grayson-order : GraysonList → GraysonList → 𝓤 ⊔ 𝓥 ̇
 Grayson-order (l , _) (l' , _) = lex (times.order R R') l l'

 GraysonList-⊥ : GraysonList
 GraysonList-⊥ = [] , ([]-decr , [])

\end{code}

We defined is-trichotomous-least for ordinals only, so we inline that definition
in the following.

\begin{code}

 GraysonList-has-trichotomous-least-element
  : is-prop-valued R'
  → (l : GraysonList) → (GraysonList-⊥ ＝ l) + (Grayson-order GraysonList-⊥ l)
 GraysonList-has-trichotomous-least-element p ([] , g) =
  inl (to-GraysonList-＝ p refl)
 GraysonList-has-trichotomous-least-element p ((_ ∷ l) , g) = inr []-lex

\end{code}

We now fix B = 𝟙ₒ, in order to derive properties on the positively
non-minimal elements of A from properties on GraysonList A B.

\begin{code}

module _ {A : 𝓤 ̇  } (R : A → A → 𝓥 ̇  ) where

 GList : 𝓤 ⊔ 𝓥 ̇
 GList = GraysonList {B = 𝟙} R (λ _ _ → 𝟘)

 A⁺ = Σ a ꞉ A , is-positively-non-minimal R a

 R⁺ : A⁺ → A⁺ → 𝓥 ̇
 R⁺ (a , _) (a' , _) = R a a'

 sing : 𝟙 {𝓤 = 𝓤} + A⁺ → GList
 sing (inl ⋆) = ([] , []-decr , [])
 sing (inr (a , p)) = ([ (a , ⋆) ] , sing-decr , (p ∷ []))

 sing⁻¹ : GList → 𝟙 {𝓤 = 𝓤} + A⁺
 sing⁻¹ ([] , _) = inl ⋆
 sing⁻¹ (((a , ⋆) ∷ _) , (q , (p ∷ _))) = inr (a , p)

 sing-retraction : sing⁻¹ ∘ sing ∼ id
 sing-retraction (inl ⋆) = refl
 sing-retraction (inr (a , p)) = refl

 sing-section : sing ∘ sing⁻¹ ∼ id
 sing-section ([] , []-decr , []) = refl
 sing-section ((a , ⋆ ∷ []) , sing-decr , (p ∷ [])) = refl
 sing-section ((a , ⋆ ∷ a' , ⋆ ∷ l) , many-decr r q , (p ∷ ps)) = 𝟘-elim r

 sing-is-equiv : is-equiv sing
 sing-is-equiv = qinvs-are-equivs sing (sing⁻¹ , sing-retraction , sing-section)

 _≺_ : GList → GList →  𝓤 ⊔ 𝓥 ̇
 _≺_ = Grayson-order {B = 𝟙} R (λ _ _ → 𝟘)

 sing⁺ : (x y : A⁺) → R⁺ x y → sing (inr x) ≺ sing (inr y)
 sing⁺ x y p = head-lex (inr (refl , p))

 R⁺-propvalued : is-prop-valued _≺_ → is-prop-valued R⁺
 R⁺-propvalued prop x y p q = ap pr₂ II
  where
   I : head-lex (inr (refl , p)) ＝ head-lex (inr (refl , q))
   I = prop (sing (inr x)) (sing (inr y)) (sing⁺ x y p) (sing⁺ x y q)

   II : (refl , p) ＝ (refl , q)
   II = inr-lc (head-lex-lc _ _ _ I)

 R⁺-wellfounded : is-well-founded _≺_ → is-well-founded R⁺
 R⁺-wellfounded wf x = I x (wf (sing (inr x)))
  where
   I : (x : A⁺) → is-accessible _≺_ (sing (inr x)) → is-accessible R⁺ x
   I x (acc f) = acc (λ y p → I y (f (sing (inr y)) (sing⁺ y x p)))

 R⁺-extensional : is-extensional _≺_ → is-extensional R⁺
 R⁺-extensional ext x y p q = inr-lc III
  where
   I : (x y : A⁺)
     → ((z : A⁺) → R⁺ z x → R⁺ z y)
     → (l : GList) → l ≺ sing (inr x) → l ≺ sing (inr y)
   I x y e l []-lex = []-lex
   I x y e ((a , ⋆ ∷ l') , _ , (q ∷ _)) (head-lex (inr (_ , r))) =
    head-lex (inr (refl , e (a , q) r))

   II : sing (inr x) ＝ sing (inr y)
   II = ext (sing (inr x)) (sing (inr y)) (I x y p) (I y x q)

   III = inr x ＝⟨ sing-retraction (inr x) ⁻¹ ⟩
         sing⁻¹ (sing (inr x)) ＝⟨ ap sing⁻¹ II ⟩
         sing⁻¹ (sing (inr y)) ＝⟨ sing-retraction (inr y) ⟩
         inr y ∎

 R⁺-transitive : is-transitive _≺_ → is-transitive R⁺
 R⁺-transitive trans a₀ a₁ a₂ p q = II I
  where
   I : sing (inr a₀) ≺ sing (inr a₂)
   I = trans (sing (inr a₀)) (sing (inr a₁)) (sing (inr a₂))
             (sing⁺ a₀ a₁ p) (sing⁺ a₁ a₂ q)

   II : sing (inr a₀) ≺ sing (inr a₂) → R⁺ a₀ a₂
   II (head-lex (inr (_ , r))) = r

 R⁺-wellorder : is-well-order _≺_ → is-well-order R⁺
 R⁺-wellorder (p , w , e , t) =
  R⁺-propvalued p , R⁺-wellfounded w , R⁺-extensional e , R⁺-transitive t

\end{code}

However, it is a constructive taboo that the subtype of positively
non-minimal elements is always an ordinal.

\begin{code}

open import UF.ClassicalLogic
open import UF.SubtypeClassifier

subtype-of-positively-non-minimal-elements-an-ordinal-implies-EM
 : ((α : Ordinal (𝓤 ⁺⁺))
    → is-well-order (subtype-order α (is-positively-non-minimal (underlying-order α))))
 → EM 𝓤
subtype-of-positively-non-minimal-elements-an-ordinal-implies-EM {𝓤} hyp = III
 where
  open import Ordinals.OrdinalOfTruthValues fe 𝓤 pe
  open import UF.DiscreteAndSeparated

  _<_ = subtype-order (OO (𝓤 ⁺)) (is-positively-non-minimal _⊲_)

  <-is-prop-valued : is-prop-valued _<_
  <-is-prop-valued =
   subtype-order-is-prop-valued (OO (𝓤 ⁺)) (is-positively-non-minimal _⊲_)

  hyp' : is-extensional' _<_
  hyp' = extensional-gives-extensional' _<_
          (extensionality _<_ (hyp (OO (𝓤 ⁺))))

  Ord⁺ = Σ α ꞉ Ordinal (𝓤 ⁺) , is-positively-non-minimal _⊲_ α

  Ωₚ : Ord⁺
  Ωₚ = Ωₒ , ∣ 𝟘ₒ , ⊥ , eqtoidₒ (ua (𝓤 ⁺)) fe' 𝟘ₒ (Ωₒ ↓ ⊥) (≃ₒ-trans 𝟘ₒ 𝟘ₒ (Ωₒ ↓ ⊥) II I) ∣
   where
    I : 𝟘ₒ ≃ₒ Ωₒ ↓ ⊥
    I = ≃ₒ-sym (Ωₒ ↓ ⊥) 𝟘ₒ (Ωₒ↓-is-id ua ⊥)

    II : 𝟘ₒ {𝓤 ⁺} ≃ₒ 𝟘ₒ {𝓤}
    II = only-one-𝟘ₒ

  𝟚ₚ : Ord⁺
  𝟚ₚ = 𝟚ₒ , ∣ 𝟘ₒ , inl ⋆ , (prop-ordinal-↓ 𝟙-is-prop ⋆ ⁻¹ ∙ +ₒ-↓-left ⋆) ∣

  I : (γ : Ord⁺) → (γ < Ωₚ ↔ γ < 𝟚ₚ)
  I (γ , p) = ∥∥-rec (↔-is-prop fe' fe' (<-is-prop-valued (γ , p) Ωₚ)
                                        (<-is-prop-valued (γ , p) 𝟚ₚ)) I' p
   where
    I' : Σ (λ a → a ⊲ γ) → ((γ , p) < Ωₚ) ↔ ((γ , p) < 𝟚ₚ)
    I' (.(γ ↓ c') , (c' , refl)) = I₁ , I₂
     where
      I₁ : ((γ , p) < Ωₚ) → ((γ , p) < 𝟚ₚ)
      I₁ (P , refl) = (inr ⋆ , eqtoidₒ (ua (𝓤 ⁺)) fe' _ _ (≃ₒ-trans (Ωₒ ↓ P) Pₒ (𝟚ₒ ↓ inr ⋆) e₁ e₂))
       where
        Pₒ = prop-ordinal (P holds) (holds-is-prop P)

        e₁ : (Ωₒ ↓ P) ≃ₒ Pₒ
        e₁ = Ωₒ↓-is-id ua P

        e₂ : Pₒ ≃ₒ 𝟚ₒ ↓ inr ⋆
        e₂ = transport⁻¹ (Pₒ ≃ₒ_) (successor-lemma-right 𝟙ₒ)
                         ((prop-ordinal-≃ₒ (holds-is-prop P) 𝟙-is-prop
                                           (λ _ → ⋆)
                                           λ _ → ≃ₒ-to-fun (Ωₒ ↓ P) Pₒ e₁ c'))

      I₂ : ((γ , p) < 𝟚ₚ) → ((γ , p) < Ωₚ)
      I₂ l = ⊲-⊴-gives-⊲ γ 𝟚ₒ Ωₒ l (𝟚ₒ-leq-Ωₒ ua)


  II : Ω 𝓤 ＝ ⟨ 𝟚ₒ ⟩
  II = ap (⟨_⟩ ∘ pr₁) (hyp' Ωₚ 𝟚ₚ I)

  III : EM 𝓤
  III = Ω-discrete-gives-EM fe' pe
         (equiv-to-discrete
           (idtoeq (𝟙 + 𝟙) (Ω 𝓤) (II ⁻¹))
           (+-is-discrete 𝟙-is-discrete 𝟙-is-discrete))

\end{code}

Hence, putting everything together, it is also a constructive taboo
that GraysonList α β is an ordinal whenever α and β are.

\begin{code}

GraysonList-always-ordinal-implies-EM
 : ((α β : Ordinal (𝓤 ⁺⁺)) → is-well-order (Grayson-order (underlying-order α) (underlying-order β)))
 → EM 𝓤
GraysonList-always-ordinal-implies-EM {𝓤 = 𝓤} hyp = II
 where
  I : (α : Ordinal (𝓤 ⁺⁺))
        → is-well-order (subtype-order α (is-positively-non-minimal (underlying-order α)))
  I α = R⁺-wellorder (underlying-order α) (hyp α 𝟙ₒ)

  II : EM 𝓤
  II = subtype-of-positively-non-minimal-elements-an-ordinal-implies-EM I


\end{code}
