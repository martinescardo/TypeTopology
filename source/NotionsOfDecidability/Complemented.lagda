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


Added by Fredrik Bakke on the 27th of March 2025.

A type family Y is "uniformly complemented" if either every fiber has an element
or every fiber is empty. We show that complemented type families over decidable
bases with double negation dense equality are uniformly complemented, and hence
that their sums and products are decidable.

\begin{code}

is-uniformly-complemented : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-uniformly-complemented {𝓤} {𝓥} {X} Y =
 ((x : X) → Y x) + ((x : X) → ¬ (Y x))

complemented-families-over-bases-with-double-negation-dense-equality-are-uniformly-complemented : {X : 𝓤 ̇ }
                                                                                                → {Y : X
                                                                                                     → 𝓥 ̇ }
                                                                                                → ((a : X)
                                                                                                 → (b : X)
                                                                                                 → ¬¬ (a ＝ b))
                                                                                                → is-decidable X
                                                                                                → ((x : X)
                                                                                                 → is-decidable (Y x))
                                                                                                → is-uniformly-complemented Y
complemented-families-over-bases-with-double-negation-dense-equality-are-uniformly-complemented {𝓤} {𝓥} {X} {Y} H dX dY = tada
 where
 tada : is-uniformly-complemented Y
 tada = cases positive-case negative-case dX
  where
   positive-case : X → is-uniformly-complemented Y
   positive-case x = map-+ positive-positive-case negative-positive-case (dY x)
    where
    positive-positive-case : Y x → (x' : X) → Y x'
    positive-positive-case y x' =
     ¬¬-elim (dY x') (¬¬-functor (λ p → transport Y p y) (H x x'))

    negative-positive-case : ¬ Y x → (x' : X) → ¬ Y x'
    negative-positive-case ny x' y' = H x' x (λ p → ny (transport Y p y'))

   negative-case : ¬ X → is-uniformly-complemented Y
   negative-case nx = inr (λ x _ → nx x)

\end{code}


Dependent sums of uniformly decidable type families.

\begin{code}

uniformly-complemented-families-over-decidable-bases-give-decidable-Σ : {X : 𝓤 ̇ }
                                                                      → {Y : X
                                                                           → 𝓥 ̇ }
                                                                      → is-decidable X
                                                                      → is-uniformly-complemented Y
                                                                      → is-decidable (Σ Y)
uniformly-complemented-families-over-decidable-bases-give-decidable-Σ {𝓤} {𝓥} {X} {Y} dX dY = tada
 where
 tada : is-decidable (Σ Y)
 tada = cases (positive-case) (negative-case) dX
  where
  positive-case : X → is-decidable (Σ Y)
  positive-case x = map-+ (λ y → x , y x) (λ ny xy → ny (xy .pr₁) (xy .pr₂)) dY

  negative-case : ¬ X → is-decidable (Σ Y)
  negative-case ny = inr (λ xy → ny (xy .pr₁))

complemented-families-over-decidable-bases-with-double-negation-dense-equality-give-decidable-Σ : {X : 𝓤 ̇ }
                                                                                                → {Y : X
                                                                                                     → 𝓥 ̇ }
                                                                                                → ((a : X)
                                                                                                 → (b : X)
                                                                                                 → ¬¬ (a ＝ b))
                                                                                                → is-decidable X
                                                                                                → ((x : X)
                                                                                                 → is-decidable (Y x))
                                                                                                → is-decidable (Σ Y)
complemented-families-over-decidable-bases-with-double-negation-dense-equality-give-decidable-Σ {𝓤} {𝓥} {X} {Y} H dX dY = tada
 where
 tada : is-decidable (Σ Y)
 tada = uniformly-complemented-families-over-decidable-bases-give-decidable-Σ dX ø
  where
  ø : is-uniformly-complemented Y
  ø = complemented-families-over-bases-with-double-negation-dense-equality-are-uniformly-complemented H dX dY

\end{code}

Dependent products of uniformly decidable type families.

\begin{code}

uniformly-complemented-families-over-decidable-bases-give-decidable-Π : {X : 𝓤 ̇ }
                                                                      → {Y : X
                                                                           → 𝓥 ̇ }
                                                                      → is-decidable X
                                                                      → is-uniformly-complemented Y
                                                                      → is-decidable (Π Y)
uniformly-complemented-families-over-decidable-bases-give-decidable-Π {𝓤} {𝓥} {X} {Y} dX dY = tada
 where
 tada : is-decidable (Π Y)
 tada = cases positive-case (λ nx → inl (λ x → 𝟘-elim (nx x))) dX
  where
  positive-case : X → is-decidable (Π Y)
  positive-case x = map-+ id (λ b f → b x (f x)) dY

complemented-families-over-decidable-bases-with-double-negation-dense-equality-give-decidable-Π : {X : 𝓤 ̇ }
                                                                                                → {Y : X
                                                                                                     → 𝓥 ̇ }
                                                                                                → ((a : X)
                                                                                                 → (b : X)
                                                                                                 → ¬¬ (a ＝ b))
                                                                                                → is-decidable X
                                                                                                → ((x : X)
                                                                                                 → is-decidable (Y x))
                                                                                                → is-decidable (Π Y)
complemented-families-over-decidable-bases-with-double-negation-dense-equality-give-decidable-Π {𝓤} {𝓥} {X} {Y} H dX dY = tada
 where
 tada : is-decidable (Π Y)
 tada = uniformly-complemented-families-over-decidable-bases-give-decidable-Π dX ø
  where
  ø : is-uniformly-complemented Y
  ø = complemented-families-over-bases-with-double-negation-dense-equality-are-uniformly-complemented H dX dY

\end{code}
