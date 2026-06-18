Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu
December 2024 (with results potentially going back to November 2023)
With additions from 8 January 2025.

Taboos involving ordinal exponentiation.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.Taboos
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
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

open import MLTT.Spartan
open import MLTT.Plus-Properties

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.MultiplicationProperties ua
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying

open import Ordinals.Exponentiation.DecreasingList ua pt
open import Ordinals.Exponentiation.PropertiesViaTransport ua pt sr
open import Ordinals.Exponentiation.Specification ua pt sr
open import Ordinals.Exponentiation.Supremum ua pt sr
open import Ordinals.Exponentiation.TrichotomousLeastElement ua pt

open import UF.Base
open import UF.ClassicalLogic
open import UF.Equiv
open import UF.SubtypeClassifier

open PropositionalTruncation pt
open suprema pt sr

\end{code}

We will show that, constructively, exponentiation is not in general monotone in
the base. More precisely, the statement
  α ⊴ β → α ^ₒ γ ⊴ α ^ₒ γ (for all ordinals α, β and γ)
implies excluded middle.

Moreover, we can even strengthen the hypothesis to have a strict inequality,
i.e. the weaker statement
  α ⊲ β → α ^ₒ γ ⊴ α ^ₒ γ (for all ordinals α, β and γ)
already implies excluded middle.

Since our concrete exponentiation is only well defined for bases α with a
trichotomous least element, we further add this assumption to the statement (and
still derive excluded middle from it).

Furthermore, we can actually fix γ := 𝟚ₒ in the statement.
Since α ^ₒ 𝟚ₒ ＝ α ×ₒ α for any (reasonable) notion of ordinal exponentiation, we
see that the taboo applies to any such notion and we formalize this as
exponentiation-weakly-monotone-in-base-implies-EM below.

In particular we can reduce the derivation of excluded middle from a statement
about multiplication:

\begin{code}

×ₒ-weakly-monotone-in-both-arguments-implies-EM
 : ((α β : Ordinal 𝓤) → has-trichotomous-least-element α
                      → has-trichotomous-least-element β
                      → α ⊲ β → α ×ₒ α ⊴ β ×ₒ β)
 → EM 𝓤
×ₒ-weakly-monotone-in-both-arguments-implies-EM {𝓤} assumption P P-is-prop =
 IV (f x) refl
  where
   α β Pₒ : Ordinal 𝓤
   α = [ 2 ]ₒ
   Pₒ = prop-ordinal P P-is-prop
   β = [ 3 ]ₒ +ₒ Pₒ

   pattern ⊥β = inl (inl (inl ⋆))

   I : α ⊲ β
   I = inl (inr ⋆) , ((successor-lemma-right α) ⁻¹ ∙ +ₒ-↓-left (inr ⋆))

   α-has-trichotomous-least-element : has-trichotomous-least-element α
   α-has-trichotomous-least-element = inl ⋆ , h
    where
     h : (x : ⟨ α ⟩) → (inl ⋆ ＝ x) + (inl ⋆ ≺⟨ α ⟩ x)
     h (inl ⋆) = inl refl
     h (inr ⋆) = inr ⋆

   β-has-trichotomous-least-element : has-trichotomous-least-element β
   β-has-trichotomous-least-element = ⊥β , h
    where
     h : (y : ⟨ β ⟩) → (⊥β ＝ y) + (⊥β ≺⟨ β ⟩ y)
     h ⊥β                  = inl refl
     h (inl (inl (inr ⋆))) = inr ⋆
     h (inl (inr ⋆))       = inr ⋆
     h (inr p)             = inr ⋆

   II : α ×ₒ α ⊴ β ×ₒ β
   II = assumption α β
         α-has-trichotomous-least-element
         β-has-trichotomous-least-element
         I

   x : ⟨ α ×ₒ α ⟩
   x = (inr ⋆ , inr ⋆)

   f : ⟨ α ×ₒ α ⟩ → ⟨ β ×ₒ β ⟩
   f = [ α ×ₒ α , β ×ₒ β ]⟨ II ⟩

   pattern ₀α = (inl ⋆ , inl ⋆)
   pattern ₁α = (inr ⋆ , inl ⋆)
   pattern ₂α = (inl ⋆ , inr ⋆)
   pattern ₃α = (inr ⋆ , inr ⋆)

   f' : P → ⟨ α ×ₒ α ⟩ → ⟨ β ×ₒ β ⟩
   f' p ₀α = (⊥β , ⊥β)
   f' p ₁α = (inl (inl (inr ⋆)) , ⊥β)
   f' p ₂α = (inl (inr ⋆) , ⊥β)
   f' p ₃α = (inr p , ⊥β)

   f'-simulation : (p : P) → is-simulation (α ×ₒ α) (β ×ₒ β) (f' p)
   f'-simulation p = f'-initial-seg , f'-order-pres
    where
     f'-initial-seg : is-initial-segment (α ×ₒ α) (β ×ₒ β) (f' p)
     f'-initial-seg ₀α (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₀α (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₀α (inl (inl (inl ⋆)) , _) (inr (refl , l)) = 𝟘-elim l
     f'-initial-seg ₀α (inl (inl (inr ⋆)) , _) (inr (refl , l)) = 𝟘-elim l
     f'-initial-seg ₁α (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₁α (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₁α (inl (inl (inl ⋆)) , z) (inr (refl , l)) =
      ₀α , inr (refl , ⋆) , refl
     f'-initial-seg ₂α (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₂α (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₂α (inl (inl (inl ⋆)) , z) (inr (refl , l)) =
      ₀α , inl ⋆ , refl
     f'-initial-seg ₂α (inl (inl (inr ⋆)) , z) (inr (refl , l)) =
      ₁α , inl ⋆ , refl
     f'-initial-seg ₃α (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₃α (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₃α (inl (inl (inl ⋆)) , z) (inr (refl , l)) =
      ₀α , inl ⋆ , refl
     f'-initial-seg ₃α (inl (inl (inr ⋆)) , z) (inr (refl , l)) =
      ₁α , inl ⋆ , refl
     f'-initial-seg ₃α (inl (inr ⋆) , z) (inr (refl , l)) =
      ₂α , inr (refl , ⋆) , refl

     f'-order-pres : is-order-preserving (α ×ₒ α) (β ×ₒ β) (f' p)
     f'-order-pres ₀α ₀α l = 𝟘-elim (cases id pr₂ l)
     f'-order-pres ₀α ₁α l = inr (refl , ⋆)
     f'-order-pres ₀α ₂α l = inr (refl , ⋆)
     f'-order-pres ₀α ₃α l = inr (refl , ⋆)
     f'-order-pres ₁α ₀α l = 𝟘-elim (cases id pr₂ l)
     f'-order-pres ₁α ₁α l = 𝟘-elim (cases id pr₂ l)
     f'-order-pres ₁α ₂α l = inr (refl , ⋆)
     f'-order-pres ₁α ₃α l = inr (refl , ⋆)
     f'-order-pres ₂α ₀α l = 𝟘-elim (cases id pr₂ l)
     f'-order-pres ₂α ₁α (inl l) = 𝟘-elim l
     f'-order-pres ₂α ₁α (inr (e , l)) = 𝟘-elim (+disjoint (e ⁻¹))
     f'-order-pres ₂α ₂α l = 𝟘-elim (cases id pr₂ l)
     f'-order-pres ₂α ₃α l = inr (refl , ⋆)
     f'-order-pres ₃α ₀α l = 𝟘-elim (cases id pr₂ l)
     f'-order-pres ₃α ₁α l = 𝟘-elim (cases id pr₂ l)
     f'-order-pres ₃α ₂α l = 𝟘-elim (cases id pr₂ l)
     f'-order-pres ₃α ₃α l = 𝟘-elim (cases id pr₂ l)

   III : (p : P) → f ∼ f' p
   III p = at-most-one-simulation (α ×ₒ α) (β ×ₒ β)
            f
            (f' p)
            [ α ×ₒ α , β ×ₒ β ]⟨ II ⟩-is-simulation
            (f'-simulation p)

   IV : (y : ⟨ β ×ₒ β ⟩) → f x ＝ y → P + ¬ P
   IV (inr p , y') r = inl p
   IV (inl y , y') r = inr (λ p → +disjoint (ap pr₁ (V p)))
    where
     V : (p : P) → (inl y , y') ＝ (inr p , ⊥β)
     V p = (inl y , y') ＝⟨ r ⁻¹ ⟩
           f x          ＝⟨ III p x ⟩
           (inr p , ⊥β) ∎

\end{code}

As announced, we get excluded middle from (weak) monotonicity of exponentiation
in the base.

\begin{code}

exponentiation-weakly-monotone-in-base-implies-EM
 : (exp : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤)
 → ((α : Ordinal 𝓤) → has-trichotomous-least-element α
                    → exp-specification-zero α (exp α))
 → ((α : Ordinal 𝓤) → has-trichotomous-least-element α
                    → exp-specification-succ α (exp α))
 → ((α β γ : Ordinal 𝓤) → has-trichotomous-least-element α
                        → has-trichotomous-least-element β
                        → α ⊲ β → (exp α γ ⊴ exp β γ))
 → EM 𝓤
exponentiation-weakly-monotone-in-base-implies-EM {𝓤} exp exp-zero exp-succ H =
 ×ₒ-weakly-monotone-in-both-arguments-implies-EM I
  where
   I : (α β : Ordinal 𝓤)
     → has-trichotomous-least-element α
     → has-trichotomous-least-element β
     → α ⊲ β → α ×ₒ α ⊴ β ×ₒ β
   I α β h h' s = transport₂ _⊴_ II III (H α β 𝟚ₒ h h' s)
    where
     II : exp α 𝟚ₒ ＝ α ×ₒ α
     II = exp-𝟚ₒ-is-×ₒ α (exp α) (exp-zero α h) (exp-succ α h)
     III : exp β 𝟚ₒ ＝ β ×ₒ β
     III = exp-𝟚ₒ-is-×ₒ β (exp β) (exp-zero β h') (exp-succ β h')

^ₒ-weakly-monotone-in-base-implies-EM
 : ((α β γ : Ordinal 𝓤) → has-trichotomous-least-element α
                        → has-trichotomous-least-element β
                        → α ⊲ β → α ^ₒ γ ⊴ β ^ₒ γ)
 → EM 𝓤
^ₒ-weakly-monotone-in-base-implies-EM {𝓤} =
 exponentiation-weakly-monotone-in-base-implies-EM _^ₒ_
  (λ α h → ^ₒ-satisfies-zero-specification α)
  (λ α h → ^ₒ-satisfies-succ-specification α
             (trichotomous-least-element-gives-𝟙ₒ-⊴ α h))

^ₒ-monotone-in-base-implies-EM
 : ((α β γ : Ordinal 𝓤) → has-trichotomous-least-element α
                        → has-trichotomous-least-element β
                        → α ⊴ β → α ^ₒ γ ⊴ β ^ₒ γ)
 → EM 𝓤
^ₒ-monotone-in-base-implies-EM m =
 ^ₒ-weakly-monotone-in-base-implies-EM
  (λ α β γ h h' i → m α β γ h h' (⊲-gives-⊴ α β i))

\end{code}

Classically, exponentiation is of course monotone in the base.

\begin{code}

EM-implies-exp-monotone-in-base
 : EM 𝓤
 → (α β γ : Ordinal 𝓤) → α ⊴ β → α ^ₒ γ ⊴ β ^ₒ γ
EM-implies-exp-monotone-in-base {𝓤} em α β γ l =
 transfinite-induction-on-OO _ I γ
 where
  I : (γ : Ordinal 𝓤)
    → ((c : ⟨ γ ⟩) → (α ^ₒ (γ ↓ c) ⊴ β ^ₒ (γ ↓ c)))
    → (α ^ₒ γ ⊴ β ^ₒ γ)
  I γ IH = transport₂⁻¹ _⊴_ (^ₒ-behaviour α γ) (^ₒ-behaviour β γ)
            (sup-monotone
             (cases (λ _ → 𝟙ₒ) (λ c → α ^ₒ (γ ↓ c) ×ₒ α))
             (cases (λ _ → 𝟙ₒ) (λ c → β ^ₒ (γ ↓ c) ×ₒ β))
             κ)
   where
    κ : (i : 𝟙 + ⟨ γ ⟩)
      → cases (λ _ → 𝟙ₒ) (λ c → α ^ₒ (γ ↓ c) ×ₒ α) i
      ⊴ cases (λ _ → 𝟙ₒ) (λ c → β ^ₒ (γ ↓ c) ×ₒ β) i
    κ (inl ⋆) = ⊴-refl 𝟙ₒ
    κ (inr c) = EM-implies-induced-⊴-on-×ₒ em (α ^ₒ (γ ↓ c)) α
                                              (β ^ₒ (γ ↓ c)) β
                                              (IH c) l

\end{code}

The below shows that constructively we cannot expect to have an operation
  exp : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤
that behaves like exponentiation for *all* bases α and exponents β.

In Ordinals.Exponentiation.Suprema we construct an operation _^ₒ_ that is well
behaved for all bases α ⊵ 𝟙₀ and all exponents β.

\begin{code}

module _ (exp : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) where

 exponentiation-defined-everywhere-implies-EM'
  : ((α : Ordinal 𝓤) → exp-specification-zero α (exp α))
  → ((α : Ordinal 𝓤) → exp-specification-succ α (exp α))
  → ((α : Ordinal 𝓤) → α ≠ 𝟘ₒ → is-monotone (OO 𝓤) (OO 𝓤) (exp α))
  → EM 𝓤
 exponentiation-defined-everywhere-implies-EM' exp-zero exp-succ exp-mon P P-is-prop =
  III (f ⋆ , refl)
   where
    α : Ordinal 𝓤
    α = prop-ordinal P P-is-prop +ₒ 𝟙ₒ

    α-not-zero : ¬ (α ＝ 𝟘ₒ)
    α-not-zero e = 𝟘-elim (Idtofun (ap ⟨_⟩ e) (inr ⋆))

    eq₁ : exp α 𝟘ₒ ＝ 𝟙ₒ
    eq₁ = exp-zero α
    eq₂ : exp α 𝟙ₒ ＝ α
    eq₂ = 𝟙ₒ-neutral-exp α (exp α) (exp-zero α) (exp-succ α)

    I : exp α 𝟘ₒ ⊴ exp α 𝟙ₒ
    I = ≼-gives-⊴ (exp α 𝟘ₒ) (exp α 𝟙ₒ) (exp-mon α α-not-zero 𝟘ₒ 𝟙ₒ (𝟘ₒ-least 𝟙ₒ))

    II : 𝟙ₒ ⊴ α
    II = transport₂ _⊴_ eq₁ eq₂ I

    f = [ 𝟙ₒ , α ]⟨ II ⟩

    III : Σ a ꞉ ⟨ α ⟩ , (f ⋆ ＝ a) → P + ¬ P
    III (inl p , _) = inl p
    III (inr ⋆ , r) = inr (λ p → 𝟘-elim (pr₁ (pr₂ (h p))))
     where
      h : (p : P) → Σ u ꞉ 𝟙 , u ≺⟨ 𝟙ₒ ⟩ ⋆ × (f u ＝ inl p)
      h p = simulations-are-initial-segments 𝟙ₒ α
             f
             [ 𝟙ₒ , α ]⟨ II ⟩-is-simulation
             ⋆
             (inl p)
             (transport⁻¹ (λ - → inl p ≺⟨ α ⟩ -) r ⋆)

 exponentiation-defined-everywhere-implies-EM
  : ((α : Ordinal 𝓤) → exp-specification-zero α (exp α))
  → ((α : Ordinal 𝓤) → exp-specification-succ α (exp α))
  → ((α : Ordinal 𝓤) → exp-specification-sup α (exp α))
  → EM 𝓤
 exponentiation-defined-everywhere-implies-EM exp-zero exp-succ exp-sup =
  exponentiation-defined-everywhere-implies-EM'
   exp-zero
   exp-succ
   (λ α ν → is-monotone-if-continuous (exp α) (exp-sup α ν))

\end{code}

And conversely, as is well known, excluded middle gives an exponentiation
function that is defined everywhere.

Below, we use excluded middle to decide if an ordinal α is zero or not, and if
not, to construct α' such that α = 𝟙ₒ +ₒ α'. From there, we can use our concrete
construction from Ordinals.Exponentiation.DecreasingList, but other choices are
also possible, including, for example, using the abstract construction from
Ordinals.Exponentiation.Supremum.

\begin{code}

𝟘^_ : Ordinal 𝓤 → Ordinal 𝓤
𝟘^_ {𝓤} β = prop-ordinal (β ≃ₒ 𝟘ₒ{𝓤}) (≃ₒ-is-prop-valued fe' β 𝟘ₒ)

𝟘^-zero-spec : 𝟘^ 𝟘ₒ {𝓤} ＝ 𝟙ₒ
𝟘^-zero-spec {𝓤} = prop-ordinal-＝
                    (≃ₒ-is-prop-valued fe' 𝟘ₒ 𝟘ₒ) 𝟙-is-prop
                    (λ _ → ⋆) (λ _ → (≃ₒ-refl 𝟘ₒ))

𝟘^-succ-spec : (β : Ordinal 𝓤) → 𝟘^ (β +ₒ 𝟙ₒ) ＝ (𝟘^ β) ×ₒ 𝟘ₒ {𝓤}
𝟘^-succ-spec {𝓤} β = eq ∙ ×ₒ-𝟘ₒ-right (𝟘^ β) ⁻¹
 where
  f : (β +ₒ 𝟙ₒ) ≃ₒ 𝟘ₒ → 𝟘
  f e = ≃ₒ-to-fun (β +ₒ 𝟙ₒ) 𝟘ₒ e (inr ⋆)

  eq :  𝟘^ (β +ₒ 𝟙ₒ) ＝ 𝟘ₒ
  eq = prop-ordinal-＝
        (≃ₒ-is-prop-valued fe' (β +ₒ 𝟙ₒ) 𝟘ₒ) 𝟘-is-prop
        f 𝟘-elim

𝟘^-sup-spec : (β : Ordinal 𝓤) → ¬ (β ＝ 𝟘ₒ) → (𝟘^ β) ＝ 𝟘ₒ
𝟘^-sup-spec β β-ne = prop-ordinal-＝
                      (≃ₒ-is-prop-valued fe' β 𝟘ₒ) 𝟘-is-prop
                      (λ e → 𝟘-elim (β-ne (eqtoidₒ (ua _) fe' _ _ e)))
                      𝟘-elim

\end{code}

We now explicitly include a zero case in the supremum specification:

\begin{code}

exp-specification-sup-revised : Ordinal 𝓤 → (Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
exp-specification-sup-revised {𝓤} α exp =
   exp-specification-sup α exp
 × (α ＝ 𝟘ₒ → (β : Ordinal 𝓤) → β ≠ 𝟘ₒ → exp β ＝ 𝟘ₒ)

exp-full-specification : (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
exp-full-specification {𝓤} exp =
   ((α : Ordinal 𝓤) → exp-specification-zero α (exp α))
 × ((α : Ordinal 𝓤) → exp-specification-succ α (exp α))
 × ((α : Ordinal 𝓤) → exp-specification-sup-revised α (exp α))

Has-trichotomous-least-element-or-is-zero-gives-full-exponentiation
 : Has-trichotomous-least-element-or-is-zero
 → Σ exp ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) , exp-full-specification exp
Has-trichotomous-least-element-or-is-zero-gives-full-exponentiation {𝓤} κ =
 exp , exp-spec
  where
   exp-aux : (α : Ordinal 𝓤)
           → has-trichotomous-least-element-or-is-zero α
           → Ordinal 𝓤 → Ordinal 𝓤
   exp-aux α (inl h) β = exponentiationᴸ α h β
   exp-aux α (inr _) β = 𝟘^ β
   exp : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤
   exp α = exp-aux α (κ α)

   spec₀ : (α : Ordinal 𝓤) (κ : has-trichotomous-least-element-or-is-zero α)
         → exp-specification-zero α (exp-aux α κ)
   spec₀ α (inl h)    = exponentiationᴸ-satisfies-zero-specification α h
   spec₀ α (inr refl) = 𝟘^-zero-spec

   spec₊ : (α : Ordinal 𝓤) (κ : has-trichotomous-least-element-or-is-zero α)
         → exp-specification-succ α (exp-aux α κ)
   spec₊ α (inl h)    = exponentiationᴸ-satisfies-succ-specification α h
   spec₊ α (inr refl) = 𝟘^-succ-spec

   specₛ : (α : Ordinal 𝓤) (κ : has-trichotomous-least-element-or-is-zero α)
         → exp-specification-sup-revised α (exp-aux α κ)
   specₛ α (inl h@(x₀ , _)) = exponentiationᴸ-satisfies-sup-specification α h ,
                              (λ α-is-zero → 𝟘-elim (Idtofunₒ α-is-zero x₀))
   specₛ α (inr r) = (λ α-is-nonzero → 𝟘-elim (α-is-nonzero r)) ,
                     (λ _ → 𝟘^-sup-spec)

   exp-spec : exp-full-specification exp
   exp-spec =
    (λ α → spec₀ α (κ α)) ,
    (λ α → spec₊ α (κ α)) ,
    (λ α → specₛ α (κ α))

EM-gives-full-exponentiation
 : EM 𝓤
 → Σ exp ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) , exp-full-specification exp
EM-gives-full-exponentiation em =
 Has-trichotomous-least-element-or-is-zero-gives-full-exponentiation
  (EM-gives-Has-trichotomous-least-element-or-is-zero em)

\end{code}

Our development of a concrete representation of exponentials only works
for base α which has a trichotomous least element, in which case the
subtype of positive elements again is an ordinal. Here we show that
one cannot avoid the restriction to a *trichotomous* least element
constructively: if the subtype of positive elements of α were an
ordinal for every (very large) ordinal α, then excluded middle would
hold. To derive the taboo, we consider the very large ordinal of large
ordinals OO (𝓤 ⁺), which has a least element 𝟘ₒ. The two (large)
ordinals Ωₒ and 𝟚ₒ are positive in OO (𝓤 ⁺), and have the same
positive predecessors. Hence if the subtype of positive elements would
have an extensional order relation, we would have Ωₒ ＝ 𝟚ₒ, which is
equivalent to excluded middle.

\begin{code}

subtype-of-positive-elements-an-ordinal-implies-EM
 : ((α : Ordinal (𝓤 ⁺⁺)) (x : ⟨ α ⟩)
    → is-least α x
    → is-well-order (subtype-order α (λ - → x ≺⟨ α ⟩ -)))
 → EM 𝓤
subtype-of-positive-elements-an-ordinal-implies-EM {𝓤} hyp = III
 where
  open import Ordinals.OrdinalOfTruthValues fe 𝓤 pe
  open import UF.DiscreteAndSeparated

  _<_ = (subtype-order (OO (𝓤 ⁺)) (λ - → 𝟘ₒ ≺⟨ OO (𝓤 ⁺) ⟩ -))

  hyp' : is-extensional' _<_
  hyp' = extensional-gives-extensional' _<_
          (extensionality _<_ (hyp (OO (𝓤 ⁺)) 𝟘ₒ 𝟘ₒ-least))

  Positive-Ord = Σ α ꞉ Ordinal (𝓤 ⁺) , 𝟘ₒ ⊲ α

  Ωₚ : Positive-Ord
  Ωₚ = Ωₒ , ⊥ , eqtoidₒ (ua (𝓤 ⁺)) fe' 𝟘ₒ (Ωₒ ↓ ⊥) (≃ₒ-trans 𝟘ₒ 𝟘ₒ (Ωₒ ↓ ⊥) II I)
   where
    I : 𝟘ₒ ≃ₒ Ωₒ ↓ ⊥
    I = ≃ₒ-sym (Ωₒ ↓ ⊥) 𝟘ₒ (Ωₒ↓-is-id ua ⊥)

    II : 𝟘ₒ {𝓤 ⁺} ≃ₒ 𝟘ₒ {𝓤}
    II = only-one-𝟘ₒ

  𝟚ₚ : Positive-Ord
  𝟚ₚ = 𝟚ₒ , inl ⋆ , (prop-ordinal-↓ 𝟙-is-prop ⋆ ⁻¹ ∙ +ₒ-↓-left ⋆)

  I : (γ : Positive-Ord) → (γ < Ωₚ ↔ γ < 𝟚ₚ)
  I (γ , u@(c , _)) = I₁ , I₂
   where
    I₁ : ((γ , u) < Ωₚ) → ((γ , u) < 𝟚ₚ)
    I₁ (P , refl) =
     inr ⋆ , eqtoidₒ (ua (𝓤 ⁺)) fe' _ _ (≃ₒ-trans (Ωₒ ↓ P) Pₒ (𝟚ₒ ↓ inr ⋆) e₁ e₂)
      where
       Pₒ = prop-ordinal (P holds) (holds-is-prop P)

       e₁ : (Ωₒ ↓ P) ≃ₒ Pₒ
       e₁ = Ωₒ↓-is-id ua P

       e₂ : Pₒ ≃ₒ 𝟚ₒ ↓ inr ⋆
       e₂ = transport⁻¹ (Pₒ ≃ₒ_) (successor-lemma-right 𝟙ₒ)
                        (prop-ordinal-≃ₒ (holds-is-prop P) 𝟙-is-prop
                                         (λ _ → ⋆)
                                         (λ _ → ≃ₒ-to-fun (Ωₒ ↓ P) Pₒ e₁ c))
    I₂ : ((γ , u) < 𝟚ₚ) → ((γ , u) < Ωₚ)
    I₂ l = ⊲-⊴-gives-⊲ γ 𝟚ₒ Ωₒ l (𝟚ₒ-leq-Ωₒ ua)

  II : Ω 𝓤 ＝ ⟨ 𝟚ₒ ⟩
  II = ap (⟨_⟩ ∘ pr₁) (hyp' Ωₚ 𝟚ₚ I)

  III : EM 𝓤
  III = Ω-discrete-gives-EM fe' pe
         (equiv-to-discrete
           (idtoeq (𝟙 + 𝟙) (Ω 𝓤) (II ⁻¹))
           (+-is-discrete 𝟙-is-discrete 𝟙-is-discrete))

\end{code}

The converse holds too of course.

\begin{code}

EM-implies-subtype-of-positive-elements-an-ordinal
 : EM 𝓤
 → ((α : Ordinal 𝓤) (x : ⟨ α ⟩)
    → is-least α x
    → is-well-order (subtype-order α (λ - → x ≺⟨ α ⟩ -)))
EM-implies-subtype-of-positive-elements-an-ordinal {𝓤} em α x x-least =
   subtype-order-is-prop-valued α P
 , subtype-order-is-well-founded α P
 , EM-implies-subtype-order-is-extensional α P em (Prop-valuedness α x)
 , subtype-order-is-transitive α P
  where
   P : ⟨ α ⟩ → 𝓤 ̇
   P y = x ≺⟨ α ⟩ y

\end{code}

The following is an example of an equation that does not follow from
the specification of exponentiation, since we cannot determine if a
given proposition is zero, a successor, or a supremum. Nevertheless,
it is true, and it can be used to derive a taboo below.

\begin{code}

^ₒ-𝟚ₒ-by-prop : (P : 𝓤 ̇  ) (i : is-prop P)
              → 𝟚ₒ {𝓤} ^ₒ (prop-ordinal P i) ＝ 𝟙ₒ +ₒ prop-ordinal P i
^ₒ-𝟚ₒ-by-prop {𝓤} P i = I ∙ ⊴-antisym (sup F) (𝟙ₒ +ₒ Pₒ) III V
 where
  F : 𝟙 {𝓤} + P → Ordinal 𝓤
  F (inl _) = 𝟙ₒ
  F (inr _) = 𝟚ₒ

  Pₒ = prop-ordinal P i

  I : 𝟚ₒ ^ₒ Pₒ ＝ sup F
  I = transport⁻¹ (_＝ sup F) (^ₒ-behaviour 𝟚ₒ Pₒ) (ap sup (dfunext fe' e))
   where
    e : ^ₒ-family 𝟚ₒ Pₒ ∼ F
    e (inl ⋆) = refl
    e (inr p) = 𝟚ₒ ^ₒ (Pₒ ↓ p) ×ₒ 𝟚ₒ ＝⟨ e₁ ⟩
                𝟚ₒ ^ₒ 𝟘ₒ ×ₒ 𝟚ₒ       ＝⟨ e₂ ⟩
                𝟙ₒ ×ₒ 𝟚ₒ             ＝⟨ 𝟙ₒ-left-neutral-×ₒ 𝟚ₒ ⟩
                𝟚ₒ                   ∎
     where
      e₁ = ap (λ - → 𝟚ₒ ^ₒ - ×ₒ 𝟚ₒ) (prop-ordinal-↓ i p)
      e₂ = ap (_×ₒ 𝟚ₒ) (^ₒ-satisfies-zero-specification 𝟚ₒ)

  II : (p : P) → 𝟙ₒ +ₒ Pₒ ＝ 𝟚ₒ
  II p = ap (𝟙ₒ +ₒ_) (holds-gives-equal-𝟙ₒ i p)

  III : sup F ⊴ 𝟙ₒ +ₒ Pₒ
  III = sup-is-lower-bound-of-upper-bounds F (𝟙ₒ +ₒ Pₒ) III'
   where
    III' : (x : 𝟙 + P) → F x ⊴ 𝟙ₒ +ₒ Pₒ
    III' (inl _) = +ₒ-left-⊴ 𝟙ₒ Pₒ
    III' (inr p) = ＝-to-⊴ 𝟚ₒ (𝟙ₒ +ₒ Pₒ) (II p ⁻¹)

  IV : (x : 𝟙 + P ) → 𝟙ₒ +ₒ Pₒ ↓ x ⊲ sup F
  IV (inl ⋆) =
   ([ 𝟙ₒ , sup F ]⟨ f₁ ⟩ ⋆) ,
    (𝟙ₒ +ₒ Pₒ ↓ inl ⋆               ＝⟨ (+ₒ-↓-left ⋆) ⁻¹ ⟩
     𝟙ₒ ↓ ⋆                         ＝⟨ simulations-preserve-↓ 𝟙ₒ _ f₁ ⋆ ⟩
     sup F ↓ [ 𝟙ₒ , sup F ]⟨ f₁ ⟩ ⋆ ∎)
   where
    f₁ : 𝟙ₒ ⊴ sup F
    f₁ = sup-is-upper-bound F (inl ⋆)
  IV (inr p) =
   ([ 𝟚ₒ , sup F ]⟨ f₂ ⟩ (inr ⋆)) ,
    (𝟙ₒ +ₒ Pₒ ↓ inr p                     ＝⟨ (+ₒ-↓-right p) ⁻¹ ⟩
     𝟙ₒ +ₒ (Pₒ ↓ p)                       ＝⟨ ap (𝟙ₒ +ₒ_) (prop-ordinal-↓ i p) ⟩
     𝟙ₒ +ₒ 𝟘ₒ                             ＝⟨ ap (𝟙ₒ +ₒ_) (𝟙ₒ-↓ ⁻¹) ⟩
     𝟙ₒ +ₒ (𝟙ₒ ↓ ⋆)                       ＝⟨ +ₒ-↓-right ⋆ ⟩
     𝟚ₒ ↓ inr ⋆                           ＝⟨ simulations-preserve-↓ 𝟚ₒ (sup F)
                                               f₂ (inr ⋆) ⟩
     sup F ↓ [ 𝟚ₒ , sup F ]⟨ f₂ ⟩ (inr ⋆) ∎)
   where
    f₂ : 𝟚ₒ ⊴ sup F
    f₂ = sup-is-upper-bound F (inr p)

  V : 𝟙ₒ +ₒ Pₒ ⊴ sup F
  V = to-⊴ (𝟙ₒ +ₒ Pₒ) (sup F) IV

\end{code}

Added 8 January 2025.

Classically, whenever the base α is greater than 𝟙₀, α ^ₒ β is at
least as large as the exponent β. However, this is a constructive
taboo.

\begin{code}

𝟚ₒ^ₒ-as-large-as-exponent-implies-EM
 : ((β : Ordinal 𝓤) → β ⊴ 𝟚ₒ {𝓤} ^ₒ β)
 → EM 𝓤
𝟚ₒ^ₒ-as-large-as-exponent-implies-EM hyp P P-is-prop = IV (f (inr ⋆)) refl
 where
  Pₒ = prop-ordinal P P-is-prop
  β = Pₒ +ₒ 𝟙ₒ

  γ = (𝟙ₒ +ₒ Pₒ) ×ₒ 𝟚ₒ

  I : 𝟚ₒ ^ₒ β ＝ γ
  I = 𝟚ₒ ^ₒ (Pₒ +ₒ 𝟙ₒ) ＝⟨ I₀ ⟩
      𝟚ₒ ^ₒ Pₒ   ×ₒ 𝟚ₒ ＝⟨ ap (_×ₒ 𝟚ₒ) (^ₒ-𝟚ₒ-by-prop P P-is-prop) ⟩
      (𝟙ₒ +ₒ Pₒ) ×ₒ 𝟚ₒ ∎
   where
    I₀ = ^ₒ-satisfies-succ-specification 𝟚ₒ
          (⊲-gives-⊴ 𝟙ₒ 𝟚ₒ (successor-increasing 𝟙ₒ)) Pₒ

  II : β ⊴ γ
  II = transport (β ⊴_) I (hyp β)

  f : ⟨ β ⟩ → ⟨ γ ⟩
  f = [ β , γ ]⟨ II ⟩
  f-sim : is-simulation β γ f
  f-sim = [ β , γ ]⟨ II ⟩-is-simulation

  IV : (x : ⟨ γ ⟩) → f (inr ⋆) ＝ x → P + ¬ P
  IV (inr p , _) r = inl p
  IV (inl ⋆ , inl ⋆) r = inr III
   where
    III : ¬ P
    III p = +disjoint (simulations-are-lc β γ f f-sim III₁)
     where
      III₁ = f (inl p)       ＝⟨ III₂ ⟩
             (inl ⋆ , inl ⋆) ＝⟨ r ⁻¹ ⟩
             f (inr ⋆)       ∎
       where
        III₂ = simulations-preserve-least β γ
                (inl p)
                (inl ⋆ , inl ⋆)
                f f-sim
                (left-preserves-least Pₒ 𝟙ₒ p (prop-ordinal-least P-is-prop p))
                (×ₒ-least (𝟙ₒ +ₒ Pₒ) 𝟚ₒ
                 (inl ⋆)
                 (inl ⋆)
                 (left-preserves-least 𝟙ₒ Pₒ ⋆ ⋆-least)
                 (left-preserves-least 𝟙ₒ 𝟙ₒ ⋆ ⋆-least))
         where
          ⋆-least : is-least 𝟙ₒ ⋆
          ⋆-least = prop-ordinal-least 𝟙-is-prop ⋆
  IV (inl ⋆ , inr ⋆) r = inl (V VII)
   where
    V : Σ y ꞉ ⟨ β ⟩ , (y ≺⟨ β ⟩ inr ⋆) × (f y ＝ (inl ⋆ , inl ⋆)) → P
    V (inl p , _ , _) = p

    VI : (inl ⋆ , inl ⋆) ≺⟨ γ ⟩ f (inr ⋆)
    VI = transport⁻¹ (underlying-order γ (inl ⋆ , inl ⋆)) r (inl ⋆)

    VII : Σ y ꞉ ⟨ β ⟩ , (y ≺⟨ β ⟩ inr ⋆) × (f y ＝ (inl ⋆ , inl ⋆))
    VII = simulations-are-initial-segments β γ f f-sim
                                           (inr ⋆) (inl ⋆ , inl ⋆) VI

^ₒ-as-large-as-exponent-implies-EM
 : ((α β : Ordinal 𝓤) → 𝟙ₒ{𝓤} ⊲ α → β ⊴ α ^ₒ β)
 → EM 𝓤
^ₒ-as-large-as-exponent-implies-EM hyp =
 𝟚ₒ^ₒ-as-large-as-exponent-implies-EM (λ β → hyp 𝟚ₒ β (successor-increasing 𝟙ₒ))

\end{code}

We record that, in fact, β ⊴ α ^ₒ β iff excluded middle holds.

\begin{code}

EM-implies-^ₒ-as-large-as-exponent
 : EM 𝓤
 → (α β : Ordinal 𝓤) → 𝟙ₒ{𝓤} ⊲ α → β ⊴ α ^ₒ β
EM-implies-^ₒ-as-large-as-exponent em α β (a₁ , p) =
 ≼-gives-⊴ β (α ^ₒ β)
           (EM-implies-order-preserving-gives-≼ em β (α ^ₒ β) (f , I))
  where
   f : ⟨ β ⟩ → ⟨ α ^ₒ β ⟩
   f b = ×ₒ-to-^ₒ α β {b} (^ₒ-⊥ α (β ↓ b) , a₁)

   I : is-order-preserving β (α ^ₒ β) f
   I b b' l = ↓-reflects-order (α ^ₒ β) (f b) (f b') III'
    where
     II : (b : ⟨ β ⟩) → α ^ₒ β ↓ f b ＝ α ^ₒ (β ↓ b)
     II b =
      α ^ₒ β ↓ f b                                                ＝⟨ II₀ ⟩
      α ^ₒ (β ↓ b) ×ₒ (α ↓ a₁) +ₒ (α ^ₒ (β ↓ b) ↓ ^ₒ-⊥ α (β ↓ b)) ＝⟨ II₁ ⟩
      α ^ₒ (β ↓ b) ×ₒ 𝟙ₒ +ₒ 𝟘ₒ                                    ＝⟨ II₂ ⟩
      α ^ₒ (β ↓ b) ×ₒ 𝟙ₒ                                          ＝⟨ II₃ ⟩
      α ^ₒ (β ↓ b)                                                ∎
       where
        II₀ = ^ₒ-↓-×ₒ-to-^ₒ α β {b} {^ₒ-⊥ α (β ↓ b)} {a₁}
        II₁ = ap₂ (λ -₁ -₂ → α ^ₒ (β ↓ b) ×ₒ -₁ +ₒ -₂) (p ⁻¹) (^ₒ-↓-⊥ α (β ↓ b))
        II₂ = 𝟘ₒ-right-neutral (α ^ₒ (β ↓ b) ×ₒ 𝟙ₒ)
        II₃ = 𝟙ₒ-right-neutral-×ₒ (α ^ₒ (β ↓ b))

     III : α ^ₒ (β ↓ b) ⊲ α ^ₒ (β ↓ b')
     III = ^ₒ-order-preserving-in-exponent α (β ↓ b) (β ↓ b')
                                           (a₁ , p)
                                           (↓-preserves-order β b b' l)

     III' : α ^ₒ β ↓ f b ⊲ α ^ₒ β ↓ f b'
     III' = transport₂⁻¹ _⊲_ (II b) (II b') III

\end{code}
