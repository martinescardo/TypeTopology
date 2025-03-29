Martin Escardo 2011.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module NotionsOfDecidability.Complemented where

open import MLTT.Spartan
open import MLTT.Plus-Properties
open import NotionsOfDecidability.Decidable

\end{code}

We again have a particular case of interest.  Complemented subsets,
defined below, are often known as decidable subsets. Agda doesn't
allow overloading of terminology, and hence we gladly accept the
slighly non-universal terminology.

\begin{code}

is-complemented : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-complemented A = ∀ x → is-decidable (A x)

characteristic-function : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                        → is-complemented A
                        → Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ＝ ₀ →   A x)
                                                   × (p x ＝ ₁ → ¬ (A x)))
characteristic-function = indicator

co-characteristic-function : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                           → is-complemented A
                           → Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ＝ ₀ → ¬ (A x))
                                                      × (p x ＝ ₁ →   A x))
co-characteristic-function d = indicator(λ x → +-commutative(d x))

\end{code}


Added by Fredrik Bakke on the 26th of March 2025.

We define a complemented map f to be a map such that each fiber is decidable.

\begin{code}

is-complemented-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-complemented-map f = each-fiber-of f is-decidable

∘-complemented-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y) (g : Y → Z)
                   → left-cancellable g
                   → is-complemented-map g
                   → is-complemented-map f
                   → is-complemented-map (g ∘ f)
∘-complemented-map f g H G F x = cases positive-case negative-case (G x)
 where
  positive-case : fiber g x → is-decidable (fiber (g ∘ f) x)
  positive-case (y , q) =
   decidable-↔
    ((λ (x , p) → x , (ap g p ∙ q)) , (λ (x , r) → x , H (r ∙ q ⁻¹)))
    (F y)

  negative-case : ¬ (fiber g x) → is-decidable (fiber (g ∘ f) x)
  negative-case nu = inr (λ (x , p) → nu (f x , p))

\end{code}
