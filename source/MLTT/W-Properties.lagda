Martin Escardo, 19th December 2020

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module MLTT.W-Properties where

open import MLTT.Spartan
open import MLTT.W
open import UF.Base
open import UF.Subsingletons
open import UF.Retracts
open import UF.FunExt
open import UF.Subsingletons-FunExt

W-＝-fold : funext 𝓥 (𝓤 ⊔ 𝓥)
         → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
           {x  : X} {f  : A x  → W X A}
           {x' : X} {f' : A x' → W X A}
         → (Σ p ꞉ x ＝ x' , ((a : A x) → f a ＝ f' (transport A p a)))
         → ssup x f ＝[ W X A ] ssup x' f'
W-＝-fold fe {X} {A} {x} {f} {x} {f'} (refl , ϕ) = ap (ssup x) (dfunext fe ϕ)

W-is-prop : funext 𝓥 (𝓤 ⊔ 𝓥)
          → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
          → is-prop X
          → is-prop (W X A)
W-is-prop fe {X} {A} X-is-prop (ssup x f) (ssup x' f') = γ
 where
  p : x ＝ x'
  p = X-is-prop x x'

  IH : (a : A x) → f a ＝ f' (transport A p a)
  IH a = W-is-prop fe X-is-prop (f a) (f' (transport A p a))

  γ : ssup x f ＝ ssup x' f'
  γ = W-＝-fold fe (p , IH)

W-＝-unfold : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
              {x  : X} {f  : A x  → W X A}
              {x' : X} {f' : A x' → W X A}
            → ssup x f ＝[ W X A ] ssup x' f'
            → Σ p ꞉ x ＝ x' , ((a : A x) → f a ＝ f' (transport A p a))
W-＝-unfold refl = refl , (λ a → refl)

W-＝-fold-unfold : (fe : funext 𝓥 (𝓤 ⊔ 𝓥))
                   {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                   {x  : X} {f  : A x  → W X A}
                   {x' : X} {f' : A x' → W X A}
                 → (q : ssup x f ＝[ W X A ] ssup x' f')
                 → W-＝-fold fe (W-＝-unfold q) ＝ q
W-＝-fold-unfold fe {X} {A} {x} {f} {x} {f} refl = γ
 where
  γ : ap (ssup x) (dfunext fe (λ x → refl)) ＝ refl
  γ = ap (ap (ssup x)) (dfunext-refl fe f)

W-is-set : funext 𝓥 (𝓤 ⊔ 𝓥)
         → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
         → is-set X
         → is-set (W X A)
W-is-set fe {X} {A} X-is-set {ssup x f} {ssup x' f'} = γ
 where
  S = Σ p ꞉ x ＝ x' , ((a : A x) → f a ＝ f' (transport A p a))

  IH : (p : x ＝ x') (a : A x) → is-prop (f a ＝ f' (transport A p a))
  IH p a = W-is-set fe X-is-set {f a} {f' (transport A p a)}

  α : is-prop S
  α = Σ-is-prop X-is-set (λ p → Π-is-prop fe (IH p))

  β : retract (ssup x f ＝ ssup x' f') of S
  β = W-＝-fold fe , W-＝-unfold , W-＝-fold-unfold fe

  γ : is-prop (ssup x f ＝ ssup x' f')
  γ = retract-of-prop β α

\end{code}
