Martin Escardo. March 2022.

When is Σ discrete and/or totally separated? More generally what do
the isolated points of Σ look like?

This is, in particular, needed in order to prove things about compact
ordinals.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module SigmaDiscreteAndTotallySeparated where

open import SpartanMLTT

open import DiscreteAndSeparated
open import CompactTypes
open import TotallySeparated
open import GenericConvergentSequence
open import PropTychonoff
open import ConvergentSequenceCompact
open import WLPO
open import FailureOfTotalSeparatedness

open import UF-Base
open import UF-Subsingletons renaming (⊤Ω to ⊤ ; ⊥Ω to ⊥)
open import UF-FunExt
open import UF-Equiv
open import UF-Miscelanea

Σ-isolated : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
           → is-isolated x
           → is-isolated y
           → is-isolated (x , y)
Σ-isolated {𝓤} {𝓥} {X} {Y} {x} {y} d e (x' , y') = g (d x')
 where
  g : decidable (x ≡ x') → decidable ((x , y) ≡ (x' , y'))
  g (inl p) = f (e' y')
   where
    e' : is-isolated (transport Y p y)
    e' = equivs-preserve-isolatedness (transport Y p) (transports-are-equivs p) y e

    f : decidable (transport Y p y ≡ y') → decidable ((x , y) ≡ (x' , y'))
    f (inl q) = inl (to-Σ-≡ (p , q))
    f (inr ψ) = inr c
     where
      c : x , y ≡ x' , y' → 𝟘
      c r = ψ q
       where
        p' : x ≡ x'
        p' = ap pr₁ r

        q' : transport Y p' y ≡ y'
        q' = from-Σ-≡' r

        s : p' ≡ p
        s = isolated-is-h-isolated x d p' p

        q : transport Y p y ≡ y'
        q = transport (λ - → transport Y - y ≡ y') s q'

  g (inr φ) = inr (λ q → φ (ap pr₁ q))

Σ-is-discrete : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
              → is-discrete X
              → ((x : X) → is-discrete (Y x))
              → is-discrete (Σ Y)
Σ-is-discrete d e (x , y) (x' , y') = Σ-isolated (d x) (e x y) (x' , y')

×-isolated : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y}
           → is-isolated x
           → is-isolated y
           → is-isolated (x , y)
×-isolated d e = Σ-isolated d e

×-is-discrete : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → is-discrete X
              → is-discrete Y
              → is-discrete (X × Y)
×-is-discrete d e = Σ-is-discrete d (λ _ → e)

×-isolated-left : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y}
                → is-isolated (x , y)
                → is-isolated x
×-isolated-left {𝓤} {𝓥} {X} {Y} {x} {y} i x' = γ (i (x' , y))
 where
  γ : decidable ((x , y) ≡ (x' , y)) → decidable (x ≡ x')
  γ (inl p) = inl (ap pr₁ p)
  γ (inr ν) = inr (λ (q : x ≡ x') → ν (to-×-≡ q refl))

×-isolated-right : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y}
                 → is-isolated (x , y)
                 → is-isolated y
×-isolated-right {𝓤} {𝓥} {X} {Y} {x} {y} i y' = γ (i (x , y'))
 where
  γ : decidable ((x , y) ≡ (x , y')) → decidable (y ≡ y')
  γ (inl p) = inl (ap pr₂ p)
  γ (inr ν) = inr (λ (q : y ≡ y') → ν (to-×-≡ refl q))


Σ-isolated-right : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
                 → is-set X
                 → is-isolated {_} {Σ Y} (x , y)
                 → is-isolated y
Σ-isolated-right {𝓤} {𝓥} {X} {Y} {x} {y} s i y' = γ (i (x , y'))
 where
  γ : decidable ((x , y) ≡ (x , y')) → decidable (y ≡ y')
  γ (inl p) =
    inl (y                               ≡⟨ refl ⟩
         transport Y refl y              ≡⟨ ap (λ - → transport Y - y) (s refl (ap pr₁ p)) ⟩
         transport Y (ap pr₁ p) y        ≡⟨ (transport-ap Y pr₁ p)⁻¹ ⟩
         transport (λ - → Y (pr₁ -)) p y ≡⟨ apd pr₂ p ⟩
         y'                              ∎)
  γ (inr ν) = inr (contrapositive (ap (x ,_)) ν)

\end{code}

Here we need a compactness assumption:

\begin{code}

Σ-isolated-left : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
                → ((x : X) → Compact (Y x))
                → is-isolated (x , y)
                → is-isolated x
Σ-isolated-left {𝓤} {𝓥} {X} {Y} {x} {y} σ i x' = γ δ
 where
   A : (y' : Y x') → 𝓤 ⊔ 𝓥 ̇
   A y' = (x , y) ≡ (x' , y')

   d : detachable A
   d y' = i (x' , y')

   δ : decidable (Σ A)
   δ = σ x' A d

   γ : decidable (Σ A) → decidable (x ≡ x')
   γ (inl (y' , p)) = inl (ap pr₁ p)
   γ (inr ν)        = inr (λ (q : x ≡ x') → ν (transport Y q y , to-Σ-≡ (q , refl)))

\end{code}

TODO. Is this assumption absolutely necessary?

Recall that we proved the following:

\begin{code}

private
 recall : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
        → is-discrete X
        → ((x : X) → is-totally-separated (Y x))
        → is-totally-separated (Σ Y)
 recall = Σ-is-totally-separated-if-index-type-is-discrete

\end{code}

We now derive a constructive taboo from the assumption that totally separated types are closed under Σ.

\begin{code}

module _ (fe : FunExt) where

 private
  fe₀ = fe 𝓤₀ 𝓤₀

 Σ-totally-separated-taboo :

      (∀ {𝓤} {𝓥} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
          → is-totally-separated X
          → ((x : X) → is-totally-separated (Y x))
          → is-totally-separated (Σ Y))
    →
      ¬¬ WLPO

 Σ-totally-separated-taboo τ =
   concrete-example.Failure fe
    (τ ℕ∞ (λ u → u ≡ ∞ → 𝟚)
       (ℕ∞-is-totally-separated fe₀)
          (λ u → Π-is-totally-separated fe₀ (λ _ → 𝟚-is-totally-separated)))
\end{code}

Remark. ¬ WLPO is equivalent to a continuity principle that is compatible with constructive mathematics and with MLTT. Therefore its negatation is not provable. See

  Constructive decidability of classical continuity.
  Mathematical Structures in Computer Science
  Volume 25 , Special Issue 7: Computing with Infinite Data:
  Topological and Logical Foundations Part 1 , October 2015 , pp. 1578-1589
  https://doi.org/10.1017/S096012951300042X

Even compact totally separated types fail to be closed under Σ:

\begin{code}

 Σ-totally-separated-stronger-taboo :

      (∀ {𝓤} {𝓥} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
          → compact X
          → ((x : X) → compact (Y x))
          → is-totally-separated X
          → ((x : X) → is-totally-separated (Y x))
          → is-totally-separated (Σ Y))
   →
      ¬¬ WLPO

 Σ-totally-separated-stronger-taboo τ =
   concrete-example.Failure fe
    (τ ℕ∞ (λ u → u ≡ ∞ → 𝟚)
       (ℕ∞-compact fe₀)
       (λ _ → compact∙-gives-compact (prop-tychonoff fe (ℕ∞-is-set fe₀) (λ _ → 𝟚-compact∙)))
       (ℕ∞-is-totally-separated fe₀)
          (λ u → Π-is-totally-separated fe₀ (λ _ → 𝟚-is-totally-separated)))

\end{code}
