Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu
December 2024 (with results potentially going back to November 2023)

Taboos involving ordinal exponentiation.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

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
open import Ordinals.Exponentiation.Specification ua pt sr
open import Ordinals.Exponentiation.Supremum ua pt sr
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.MultiplicationProperties ua
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Base
open import UF.ClassicalLogic
open import UF.Equiv
open import UF.Subsingletons
open import UF.SubtypeClassifier

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

Since our exponentiation is only well defined for base α ⊵ 𝟙ₒ (see also
exponentiation-defined-everywhere-implies-EM), we further add this assumption to
the statement (and still derive excluded middle from it).

Furthermore, we can actually fix γ := 𝟚ₒ in the statement.
Since α ^ₒ 𝟚ₒ ＝ α ×ₒ α for any (reasonable) notion of ordinal exponentiation, we
see that the taboo applies to any such notion and we formalize this as
exponentiation-weakly-monotone-in-base-implies-EM below.

In particular we can reduce the derivation of excluded middle from a statement
about multiplication:

\begin{code}

×ₒ-weakly-monotone-in-both-arguments-implies-EM :
   ((α β : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → α ⊲ β → α ×ₒ α ⊴ β ×ₒ β)
 → EM 𝓤
×ₒ-weakly-monotone-in-both-arguments-implies-EM {𝓤} assumption P P-is-prop =
 IV (f x) refl
  where
   α β Pₒ : Ordinal 𝓤
   α = [ 2 ]ₒ
   Pₒ = prop-ordinal P P-is-prop
   β = [ 3 ]ₒ +ₒ Pₒ

   I : α ⊲ β
   I = inl (inr ⋆) , ((successor-lemma-right α) ⁻¹ ∙ +ₒ-↓-left (inr ⋆))

   α-ineq : 𝟙ₒ ⊴ α
   α-ineq = ⊲-gives-⊴ 𝟙ₒ α (successor-increasing 𝟙ₒ)

   II : α ×ₒ α ⊴ β ×ₒ β
   II = assumption α β α-ineq I

   x : ⟨ α ×ₒ α ⟩
   x = (inr ⋆ , inr ⋆)

   f : ⟨ α ×ₒ α ⟩ → ⟨ β ×ₒ β ⟩
   f = [ α ×ₒ α , β ×ₒ β ]⟨ II ⟩

   pattern ⊥β = inl (inl (inl ⋆))
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

exponentiation-weakly-monotone-in-base-implies-EM :
   (exp : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤)
 → ((α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → exp-specification-zero α (exp α))
 → ((α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → exp-specification-succ α (exp α))
 → ((α β γ : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → α ⊲ β → (exp α γ ⊴ exp β γ))
 → EM 𝓤
exponentiation-weakly-monotone-in-base-implies-EM {𝓤} exp exp-zero exp-succ h =
 ×ₒ-weakly-monotone-in-both-arguments-implies-EM I
  where
   I : (α β : Ordinal 𝓤) → 𝟙ₒ ⊴ α → α ⊲ β → α ×ₒ α ⊴ β ×ₒ β
   I α β l s = transport₂ _⊴_ II III (h α β 𝟚ₒ l s)
    where
     II : exp α 𝟚ₒ ＝ α ×ₒ α
     II = exp-𝟚ₒ-is-×ₒ α (exp α) (exp-zero α l) (exp-succ α l)
     III : exp β 𝟚ₒ ＝ β ×ₒ β
     III = exp-𝟚ₒ-is-×ₒ β (exp β) (exp-zero β l') (exp-succ β l')
      where
       l' : 𝟙ₒ ⊴ β
       l' = ⊴-trans 𝟙ₒ α β l (⊲-gives-⊴ α β s)

^ₒ-weakly-monotone-in-base-implies-EM :
   ((α β γ : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → α ⊲ β → (α ^ₒ γ ⊴ β ^ₒ γ))
 → EM 𝓤
^ₒ-weakly-monotone-in-base-implies-EM {𝓤} =
 exponentiation-weakly-monotone-in-base-implies-EM _^ₒ_
  (λ α l → ^ₒ-satisfies-zero-specification α)
  (λ α l → ^ₒ-satisfies-succ-specification α l)

^ₒ-monotone-in-base-implies-EM :
   ((α β γ : Ordinal 𝓤) → 𝟙ₒ{𝓤} ⊴ α → α ⊴ β → (α ^ₒ γ ⊴ β ^ₒ γ))
 → EM 𝓤
^ₒ-monotone-in-base-implies-EM m =
 ^ₒ-weakly-monotone-in-base-implies-EM
  (λ α β γ l i → m α β γ l (⊲-gives-⊴ α β i))

\end{code}

Classically, exponentiation is of course monotone in the base.

\begin{code}

EM-implies-exp-monotone-in-base : EM 𝓤
 → (α β γ : Ordinal 𝓤) → α ⊴ β → (α ^ₒ γ ⊴ β ^ₒ γ)
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

 exponentiation-defined-everywhere-implies-EM' :
    ((α : Ordinal 𝓤) → exp-specification-zero α (exp α))
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

 exponentiation-defined-everywhere-implies-EM :
    ((α : Ordinal 𝓤) → exp-specification-zero α (exp α))
  → ((α : Ordinal 𝓤) → exp-specification-succ α (exp α))
  → ((α : Ordinal 𝓤) → exp-specification-sup α (exp α))
  → EM 𝓤
 exponentiation-defined-everywhere-implies-EM exp-zero exp-succ exp-sup =
  exponentiation-defined-everywhere-implies-EM'
   exp-zero
   exp-succ
   (λ α ν → is-monotone-if-continuous (exp α) (exp-sup α ν))

\end{code}

The following is not used at the moment, but may come in useful in the future
when aiming to derive a constructive taboo.

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

TODO: REFACTOR
And conversely... (EM gives full exponentiation)

\begin{code}

{-
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
𝟘^-sup-spec β β-not-zero =
   prop-ordinal-＝
           (≃ₒ-is-prop-valued fe' β 𝟘ₒ) 𝟘-is-prop
           (λ e → 𝟘-elim (β-not-zero (eqtoidₒ (ua _) fe' _ _ e))) 𝟘-elim

private
  case : (α : Ordinal 𝓤) → 𝓤 ⁺ ̇
  case {𝓤} α = (Σ α' ꞉ Ordinal 𝓤 , α ＝ 𝟙ₒ +ₒ α')

  has-least-or-is-zero : (α : Ordinal 𝓤) → 𝓤 ⁺ ̇
  has-least-or-is-zero α = case α + (α ＝ 𝟘ₒ)

  Has-least-or-is-zero : 𝓤 ⁺ ̇
  Has-least-or-is-zero {𝓤} = (α : Ordinal 𝓤) → has-least-or-is-zero α

  open ClassicalWellOrder fe' pe pt

  EM-gives-Has-least-or-is-zero : EM 𝓤 → Has-least-or-is-zero {𝓤}
  EM-gives-Has-least-or-is-zero em α = +functor α-inhabited-gives-least underlying-zero-unique α-inhabited-or-zero
   where
    α-inhabited-or-not : ∥ ⟨ α ⟩ ∥ + ¬ ∥ ⟨ α ⟩ ∥
    α-inhabited-or-not = em ∥ ⟨ α ⟩ ∥ ∥∥-is-prop

    α-inhabited-or-zero : ∥ ⟨ α ⟩ ∥ + (⟨ α ⟩ ＝ 𝟘)
    α-inhabited-or-zero = +functor id (λ ni → empty-types-are-＝-𝟘 fe' pe (uninhabited-is-empty ni) ) α-inhabited-or-not

    underlying-zero-unique : (⟨ α ⟩ ＝ 𝟘) → α ＝ 𝟘ₒ
    underlying-zero-unique refl = ⊴-antisym α 𝟘ₒ sim sim'
     where
      sim : (𝟘 , _) ⊴ 𝟘ₒ
      sim = (𝟘-elim , (λ x → 𝟘-elim x) , λ x → 𝟘-elim x)
      sim' : 𝟘ₒ ⊴ (𝟘 , _)
      sim' = (𝟘-elim , (λ x → 𝟘-elim x) , λ x → 𝟘-elim x)

    α-inhabited-gives-least : ∥ ⟨ α ⟩ ∥ → case α
    α-inhabited-gives-least inh = α' , eq
     where
       least-element' : Σ a ꞉ ⟨ α ⟩ , 𝟙 × ((y : ⟨ α ⟩) → 𝟙 → ¬ (y ≺⟨ α ⟩ a))
       least-element' = well-order-gives-minimal (underlying-order α) em (is-well-ordered α) (λ _ → 𝟙) (λ _ → 𝟙-is-prop) (∥∥-functor (λ a → (a , ⋆)) inh)

       a₀ : ⟨ α ⟩
       a₀ = pr₁ least-element'

       a₀-least : ((y : ⟨ α ⟩) → ¬ (y ≺⟨ α ⟩ a₀))
       a₀-least y = pr₂ (pr₂ least-element') y ⋆

       ⟨α'⟩ = Σ x ꞉ ⟨ α ⟩ , a₀ ≺⟨ α ⟩ x

       _<'_ : ⟨α'⟩ → ⟨α'⟩ → _
       _<'_ = subtype-order α (λ - → a₀ ≺⟨ α ⟩ -)

       <'-propvalued : is-prop-valued _<'_
       <'-propvalued = subtype-order-is-prop-valued α (λ - → a₀ ≺⟨ α ⟩ -)

       <'-wellfounded : is-well-founded _<'_
       <'-wellfounded = subtype-order-wellfounded α (λ - → a₀ ≺⟨ α ⟩ -)

       <-trichotomy  : is-trichotomous-order (underlying-order α)
       <-trichotomy = trichotomy (underlying-order α) fe' em (is-well-ordered α)

       <'-extensional : is-extensional _<'_
       <'-extensional (x , p) (y , q) f g = to-subtype-＝ (λ x → Prop-valuedness α a₀ x)
                                                         (Extensionality α x y
                                                           (λ u p → f' u (<-trichotomy u a₀) p)
                                                           λ u p → g' u (<-trichotomy u a₀) p)
        where
         f' : (u : ⟨ α ⟩) → in-trichotomy (underlying-order α) u a₀ → u ≺⟨ α ⟩ x → u ≺⟨ α ⟩ y
         f' u (inl q) r = 𝟘-elim (a₀-least u q)
         f' u (inr (inl refl)) r = q
         f' u (inr (inr q)) r = f (u , q) r

         g' : (u : ⟨ α ⟩) → in-trichotomy (underlying-order α) u a₀ → u ≺⟨ α ⟩ y → u ≺⟨ α ⟩ x
         g' u (inl q) r = 𝟘-elim (a₀-least u q)
         g' u (inr (inl refl)) r = p
         g' u (inr (inr q)) r = g (u , q) r


       <'-transitive : is-transitive _<'_
       <'-transitive = subtype-order-transitive α (λ - → a₀ ≺⟨ α ⟩ -)

       α' : Ordinal _
       α' = ⟨α'⟩ , _<'_ , <'-propvalued , <'-wellfounded , <'-extensional , <'-transitive

       f' : (x : ⟨ α ⟩) → in-trichotomy (underlying-order α) x a₀ → 𝟙 + ⟨ α' ⟩
       f' x (inl q) = 𝟘-elim (a₀-least x q)
       f' x (inr (inl r)) = inl ⋆
       f' x (inr (inr q)) = inr (x , q)

       f : ⟨ α ⟩ → 𝟙 + ⟨ α' ⟩
       f x = f' x (<-trichotomy x a₀)

       g : 𝟙 + ⟨ α' ⟩ → ⟨ α ⟩
       g (inl ⋆) = a₀
       g (inr (x , q)) = x

       f-equiv : is-order-equiv α (𝟙ₒ +ₒ α') f
       f-equiv = f-order-preserving , (qinvs-are-equivs f (g , η , ϵ)) , g-order-preserving
        where
         f'-order-preserving : (x y : ⟨ α ⟩)
                             → (tx : in-trichotomy (underlying-order α) x a₀)
                             → (ty : in-trichotomy (underlying-order α) y a₀)
                             → x ≺⟨ α ⟩ y → f' x tx ≺⟨ 𝟙ₒ +ₒ α' ⟩ f' y ty
         f'-order-preserving x y (inl q) ty p = 𝟘-elim (a₀-least x q)
         f'-order-preserving x y (inr (inl r)) (inl q) p = 𝟘-elim (a₀-least y q)
         f'-order-preserving .a₀ .a₀ (inr (inl refl)) (inr (inl refl)) p = 𝟘-elim (irrefl α a₀ p)
         f'-order-preserving .a₀ y (inr (inl refl)) (inr (inr q)) p = ⋆
         f'-order-preserving x y (inr (inr q)) (inl q') p = 𝟘-elim (a₀-least y q')
         f'-order-preserving x .a₀ (inr (inr q)) (inr (inl refl)) p = 𝟘-elim (a₀-least x p)
         f'-order-preserving x y (inr (inr q)) (inr (inr q')) p = p

         f-order-preserving : is-order-preserving α (𝟙ₒ +ₒ α') f
         f-order-preserving x y p = f'-order-preserving x y (<-trichotomy x a₀) (<-trichotomy y a₀) p

         g-order-preserving : is-order-preserving (𝟙ₒ +ₒ α') α g
         g-order-preserving (inl ⋆) (inr (x , q)) p = q
         g-order-preserving (inr (x , q)) (inr (y , q')) p = p

         η' : (x : ⟨ α ⟩) → (t : in-trichotomy (underlying-order α) x a₀) → g (f' x t) ＝ x
         η' x (inl q) = 𝟘-elim (a₀-least x q)
         η' x (inr (inl refl)) = refl
         η' x (inr (inr q)) = refl

         η : (x : ⟨ α ⟩) → g (f x) ＝ x
         η x = η' x (<-trichotomy x a₀)

         ϵ' : (y : 𝟙 + ⟨ α' ⟩) → (t : in-trichotomy (underlying-order α) (g y) a₀) → f' (g y) t ＝ y
         ϵ' (inl ⋆) (inl q) = 𝟘-elim (a₀-least a₀ q)
         ϵ' (inl ⋆) (inr (inl r)) = refl
         ϵ' (inl ⋆) (inr (inr q)) = 𝟘-elim (irrefl α a₀ q)
         ϵ' (inr (x , p)) (inl q) = 𝟘-elim (a₀-least x q)
         ϵ' (inr (.a₀ , p)) (inr (inl refl)) = 𝟘-elim (irrefl α a₀ p)
         ϵ' (inr (x , p)) (inr (inr q)) = ap inr (to-subtype-＝  ((λ x → Prop-valuedness α a₀ x)) refl)

         ϵ : (y : 𝟙 + ⟨ α' ⟩) → f (g y) ＝ y
         ϵ y = ϵ' y (<-trichotomy (g y) a₀)

       eq : α ＝ 𝟙ₒ +ₒ α'
       eq = eqtoidₒ (ua _) fe' α (𝟙ₒ +ₒ α') (f , f-equiv)

Has-least-or-is-zero-gives-full-spec : Has-least-or-is-zero → Σ exp ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) , exponentiation-specification exp
Has-least-or-is-zero-gives-full-spec {𝓤} cs = exp , exp-spec'
  where
   exp-aux : (α : Ordinal 𝓤)
           → has-least-or-is-zero α
           → Ordinal 𝓤 → Ordinal 𝓤
   exp-aux α (inl (α' , _)) β = [𝟙+ α' ]^ β
   exp-aux α (inr _) β = 𝟘^ β
   exp : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤
   exp α = exp-aux α (cs α)

   spec₀-aux : (α : Ordinal 𝓤) → (cs : has-least-or-is-zero α) → exp-aux α cs 𝟘ₒ ＝ 𝟙ₒ
   spec₀-aux α (inl (α' , refl)) = exp-0-spec α'
   spec₀-aux α (inr refl) = 𝟘^-zero-spec

   specₛ-aux : (α : Ordinal 𝓤) → (cs : has-least-or-is-zero α) → (β : Ordinal 𝓤)
             → exp-aux α cs (β +ₒ 𝟙ₒ) ＝ (exp-aux α cs β ×ₒ α)
   specₛ-aux α (inl (α' , refl)) = exp-succ-spec α'
   specₛ-aux α (inr refl) = 𝟘^-succ-spec

   specₗ-aux-nonzero : (α : Ordinal 𝓤) → (cs : has-least-or-is-zero α) → ¬ (α ＝ 𝟘ₒ) → {I : 𝓤 ̇ } → ∥ I ∥ → (γ : I → Ordinal 𝓤)
                     →  exp-aux α cs (sup γ) ＝ sup (λ i → exp-aux α cs (γ i))
   specₗ-aux-nonzero α (inl (α' , refl)) α-not-zero i γ = exp-sup-spec α' i γ
   specₗ-aux-nonzero α (inr r) α-not-zero = 𝟘-elim (α-not-zero r)

   specₗ-aux-zero : (α : Ordinal 𝓤) → (cs : has-least-or-is-zero α) → α ＝ 𝟘ₒ → (β : Ordinal 𝓤) → ¬ (β ＝ 𝟘ₒ)
                  → exp-aux α cs β ＝ 𝟘ₒ
   specₗ-aux-zero α (inl (α' , r)) α-zero β β-not-zero = 𝟘-elim (zero-no-element (α-zero ⁻¹ ∙ r) )
     where
       zero-no-element : (𝟘ₒ ＝ (𝟙ₒ +ₒ α')) → 𝟘
       zero-no-element p = Idtofun ((ap ⟨_⟩ p) ⁻¹) (inl ⋆)
   specₗ-aux-zero α (inr refl) _ = 𝟘^-sup-spec

   exp-spec' : exponentiation-specification exp
   exp-spec' = (λ α → spec₀-aux α (cs α)) , (λ α → specₛ-aux α (cs α)) , (λ α → specₗ-aux-nonzero α (cs α) , specₗ-aux-zero α (cs α))

EM-gives-full-spec : EM 𝓤 → Σ exp ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) , exponentiation-specification exp
EM-gives-full-spec em = Has-least-or-is-zero-gives-full-spec (EM-gives-Has-least-or-is-zero em)

-- full-spec-gives-Has-least-or-is-zero : Σ exp ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) , exponentiation-specification exp → Has-least-or-is-zero {𝓤}
-- full-spec-gives-Has-least-or-is-zero {𝓤} (exp , exp-spec) = EM-gives-Has-least-or-is-zero (exp-full-spec-gives-EM exp exp-spec)

-}

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
