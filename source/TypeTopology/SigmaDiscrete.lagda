Martin Escardo. March 2022.

When is Σ discrete? More generally what do the isolated points of Σ
look like?

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TypeTopology.SigmaDiscrete where

open import MLTT.Spartan
open import NotionsOfDecidability.Complemented
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Sets

Σ-isolated : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
           → is-isolated x
           → is-isolated y
           → is-isolated (x , y)
Σ-isolated {𝓤} {𝓥} {X} {Y} {x} {y} d e (x' , y') = g (d x')
 where
  g : is-decidable (x ＝ x') → is-decidable ((x , y) ＝ (x' , y'))
  g (inl refl) = f (e y')
   where
    f : is-decidable (y ＝ y') → is-decidable ((x , y) ＝[ Σ Y ] (x' , y'))
    f (inl refl) = inl refl
    f (inr ψ)    = inr c
     where
      c : x , y ＝ x' , y' → 𝟘
      c r = ψ t
       where
        p : x ＝ x'
        p = ap pr₁ r

        q : transport Y p y ＝ y'
        q = from-Σ-＝' r

        s : p ＝ refl
        s = isolated-points-are-h-isolated x d p refl

        t : y ＝ y'
        t = transport (λ - → transport Y - y ＝ y') s q

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
  γ : is-decidable ((x , y) ＝ (x' , y)) → is-decidable (x ＝ x')
  γ (inl p) = inl (ap pr₁ p)
  γ (inr ν) = inr (λ (q : x ＝ x') → ν (to-×-＝ q refl))

×-isolated-right : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y}
                 → is-isolated (x , y)
                 → is-isolated y
×-isolated-right {𝓤} {𝓥} {X} {Y} {x} {y} i y' = γ (i (x , y'))
 where
  γ : is-decidable ((x , y) ＝ (x , y')) → is-decidable (y ＝ y')
  γ (inl p) = inl (ap pr₂ p)
  γ (inr ν) = inr (λ (q : y ＝ y') → ν (to-×-＝ refl q))


Σ-isolated-right : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
                 → is-set X
                 → is-isolated {_} {Σ Y} (x , y)
                 → is-isolated y
Σ-isolated-right {𝓤} {𝓥} {X} {Y} {x} {y} s i y' = γ (i (x , y'))
 where
  γ : is-decidable ((x , y) ＝ (x , y')) → is-decidable (y ＝ y')
  γ (inl p) = inl (y                               ＝⟨refl⟩
                   transport Y refl y              ＝⟨ I ⟩
                   transport Y (ap pr₁ p) y        ＝⟨ II ⟩
                   transport (λ - → Y (pr₁ -)) p y ＝⟨ III ⟩
                   y'                              ∎)
                    where
                     I   = ap (λ - → transport Y - y) (s refl (ap pr₁ p))
                     II  = (transport-ap Y pr₁ p)⁻¹
                     III = apd pr₂ p
  γ (inr ν) = inr (contrapositive (ap (x ,_)) ν)

\end{code}

Added 14th October 2024. We reprove some of the above theorems
replacing isolatedness by weak isolatedness.

\begin{code}

Σ-weakly-isolated-right : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
                        → is-set X
                        → is-weakly-isolated {_} {Σ Y} (x , y)
                        → is-weakly-isolated y
Σ-weakly-isolated-right {𝓤} {𝓥} {X} {Y} {x} {y} s i y' = γ δ
 where
  δ : is-decidable ((x , y') ≠ (x , y))
  δ = i (x , y')

  γ : is-decidable ((x , y') ≠ (x , y)) → is-decidable (y' ≠ y)
  γ (inl a) = inl (λ {refl → a refl})
  γ (inr b) = inr (λ (d : y' ≠ y) → b (λ (p : x , y' ＝ x , y)
   → d (y'                               ＝⟨refl⟩
        transport Y refl y'              ＝⟨ I p ⟩
        transport Y (ap pr₁ p) y'        ＝⟨ II p ⟩
        transport (λ - → Y (pr₁ -)) p y' ＝⟨ III p ⟩
        y                                ∎)))
    where
     I   = λ p → ap (λ - → transport Y - y') (s refl (ap pr₁ p))
     II  = λ p → (transport-ap Y pr₁ p)⁻¹
     III = λ p → apd pr₂ p

×-weakly-isolated-left : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y}
                       → is-weakly-isolated (x , y)
                       → is-weakly-isolated x
×-weakly-isolated-left {𝓤} {𝓥} {X} {Y} {x} {y} i x' = γ δ
 where
  δ : is-decidable ((x' , y) ≠ (x , y))
  δ = i (x' , y)

  γ : is-decidable ((x' , y) ≠ (x , y)) → is-decidable (x' ≠ x)
  γ (inl a) = inl (λ {refl → a refl})
  γ (inr b) = inr (λ (c : x' ≠ x)
                   → b (λ (e : (x' , y) ＝ (x , y))
                        → c (ap pr₁ e)))

×-weakly-isolated-right : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y}
                        → is-weakly-isolated (x , y)
                        → is-weakly-isolated y
×-weakly-isolated-right {𝓤} {𝓥} {X} {Y} {x} {y} i y' = γ δ
 where
  δ : is-decidable (x , y' ≠ x , y)
  δ = i (x , y')

  γ : is-decidable (x , y' ≠ x , y) → is-decidable (y' ≠ y)
  γ (inl a) = inl (λ {refl → a refl})
  γ (inr b) = inr (λ (d : y' ≠ y) → b (λ (e : x , y' ＝ x , y) → d (ap pr₂ e)))

\end{code}
