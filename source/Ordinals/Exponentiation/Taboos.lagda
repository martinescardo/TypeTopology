Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu
December 2024 (with results potentially going back to November 2023)

Taboos involving ordinal exponentation.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

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

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import MLTT.Spartan

open import MLTT.Plus-Properties
open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Exponentiation.Specification ua pt sr
open import Ordinals.Exponentiation.Supremum ua pt sr
open import Ordinals.Maps
open import Ordinals.MultiplicationProperties ua
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Base
open import UF.ClassicalLogic
open import UF.Subsingletons
open suprema pt sr

\end{code}

We will show that, constructively, exponentation is not in general monotone in
the base. More precisely, the statement
  α ⊴ β → α ^ₒ γ ⊴ α ^ₒ γ (for all ordinals α, β and γ)
implies excluded middle.

Moreover, we can even strengthen the hypothesis to have a strict inequality,
i.e. the weaker statement
  α ⊲ β → α ^ₒ γ ⊴ α ^ₒ γ (for all ordinals α, β and γ)
already implies excluded middle.

Since our exponentation is only well defined for base α ⊵ 𝟙ₒ (see also
exp-defined-everywhere-implies-EM), we further add this assumption to the
statement (and still derive excluded middle from it).

Furthermore, we can actually fix γ := 𝟚ₒ in the statement.
Since α ^ₒ 𝟚ₒ ＝ α ×ₒ α for any (reasonable) notion of ordinal exponentation, we
see that the taboo applies to any such notion and we formalize this as
exponentation-weakly-monotone-in-base-implies-EM below.

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
     f'-initial-seg ₁α (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
      = ₀α , inr (refl , l) , refl
     f'-initial-seg ₂α (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
      = ₀α , inl ⋆ , refl
     f'-initial-seg ₂α (inl (inl (inr ⋆)) , .⊥β) (inr (refl , l))
      = ₁α , inl ⋆ , refl
     f'-initial-seg ₃α (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
      = ₀α , inl ⋆ , refl
     f'-initial-seg ₃α (inl (inl (inr ⋆)) , .⊥β) (inr (refl , l))
      = ₁α , inl ⋆ , refl
     f'-initial-seg ₃α (inl (inr ⋆) , .⊥β)       (inr (refl , l))
      = ₂α , inr (refl , l) , refl
     f'-initial-seg ₀α (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
      = 𝟘-elim l
     f'-initial-seg ₀α (inl (inl (inr ⋆)) , .⊥β) (inr (refl , l))
      = 𝟘-elim l
     f'-initial-seg ₀α (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₀α (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₂α (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₂α (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₁α (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₁α (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₃α (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
     f'-initial-seg ₃α (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l

     f'-order-pres : is-order-preserving (α ×ₒ α) (β ×ₒ β) (f' p)
     f'-order-pres ₀α ₂α (inl l) = inr (refl , l)
     f'-order-pres ₀α ₃α (inl l) = inr (refl , l)
     f'-order-pres ₁α ₂α (inl l) = inr (refl , l)
     f'-order-pres ₁α ₃α (inl l) = inr (refl , l)
     f'-order-pres (_ , inr ⋆) (_ , inl ⋆) (inl l) = 𝟘-elim l
     f'-order-pres (_ , inr ⋆) (_ , inr ⋆) (inl l) = 𝟘-elim l
     f'-order-pres ₀α (inr ⋆ , x') (inr (refl , l)) = inr (refl , l)
     f'-order-pres ₂α (inr ⋆ , x') (inr (refl , l)) = inr (refl , l)
     f'-order-pres (inr ⋆ , x') (inl ⋆ , x') (inr (refl , l)) = 𝟘-elim l
     f'-order-pres (inr ⋆ , x') (inr ⋆ , x') (inr (refl , l)) = 𝟘-elim l

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

As announced, we get excluded middle from (weak) monotonicity of exponentation
in the base.

\begin{code}

exponentation-weakly-monotone-in-base-implies-EM :
   (exp : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤)
 → ((α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → exp-specification-zero α (exp α))
 → ((α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → exp-specification-succ α (exp α))
 → ((α β γ : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → α ⊲ β → (exp α γ ⊴ exp β γ))
 → EM 𝓤
exponentation-weakly-monotone-in-base-implies-EM {𝓤} exp exp-zero exp-succ h =
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
 exponentation-weakly-monotone-in-base-implies-EM _^ₒ_
  (λ α l → ^ₒ-satisfies-zero-specification α)
  (λ α l → ^ₒ-satisfies-succ-specification α l)

^ₒ-monotone-in-base-implies-EM :
   ((α β γ : Ordinal 𝓤) → 𝟙ₒ{𝓤} ⊴ α → α ⊴ β → (α ^ₒ γ ⊴ β ^ₒ γ))
 → EM 𝓤
^ₒ-monotone-in-base-implies-EM m =
 ^ₒ-weakly-monotone-in-base-implies-EM
  (λ α β γ l i → m α β γ l (⊲-gives-⊴ α β i))

\end{code}

Classically, exponentation is of course monotone in the base.

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

TODO: WRITE A COMMENT

\begin{code}

module _ (exp : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) where

 exp-defined-everywhere-implies-EM' :
    ((α : Ordinal 𝓤) → exp-specification-zero α (exp α))
  → ((α : Ordinal 𝓤) → exp-specification-succ α (exp α))
  → ((α : Ordinal 𝓤) → α ≠ 𝟘ₒ → is-monotone (OO 𝓤) (OO 𝓤) (exp α))
  → EM 𝓤
 exp-defined-everywhere-implies-EM' exp-zero exp-succ exp-mon P P-is-prop =
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

 exp-defined-everywhere-implies-EM :
    ((α : Ordinal 𝓤) → exp-specification-zero α (exp α))
  → ((α : Ordinal 𝓤) → exp-specification-succ α (exp α))
  → ((α : Ordinal 𝓤) → exp-specification-sup α (exp α))
  → EM 𝓤
 exp-defined-everywhere-implies-EM exp-zero exp-succ exp-sup =
  exp-defined-everywhere-implies-EM'
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