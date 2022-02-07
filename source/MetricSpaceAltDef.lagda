Andrew Sneap


\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_)  -- TypeTopology

open import NaturalsAddition renaming (_+_ to _ℕ+_) -- TypeTopology
open import NaturalsOrder --TypeTopology
open import OrderNotation -- TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-PropTrunc --TypeTopology
open import UF-Subsingletons --TypeTopology

open import Rationals
open import RationalsAddition
open import RationalsOrder

module MetricSpaceAltDef
  (pt : propositional-truncations-exist)
  (fe : Fun-Ext)
  (pe : Prop-Ext)
 where 

open PropositionalTruncation pt
open import DedekindReals pe pt fe
open import DedekindRealsOrder pe pt fe

m1a : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇) → 𝓤 ̇
m1a X B = (x y : X) → ((ε : ℚ) → (l : 0ℚ < ε) → B x y ε l) → x ≡ y

m1b : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇) → 𝓤 ̇
m1b X B = (x : X) → ((ε : ℚ) → (l : 0ℚ < ε) → B x x ε l)

m2 : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇) → 𝓤 ̇
m2 X B = (x y : X) → (ε : ℚ) → (l : 0ℚ < ε) → B x y ε l → B y x ε l

m3 : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇) → 𝓤 ̇
m3 X B = (x y : X) → (ε₁ ε₂ : ℚ) → (l₁ : 0ℚ < ε₁) → (l₂ : 0ℚ < ε₂) → ε₁ < ε₂ → B x y ε₁ l₁ → B x y ε₂ l₂

m4 : {𝓤 : Universe} → (X : 𝓤 ̇) → (B : X → X → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇) → 𝓤 ̇
m4 X B = (x y z : X) → (ε₁ ε₂ : ℚ) → (l₁ : (0ℚ < ε₁)) → (l₂ : (0ℚ < ε₂)) → B x y ε₁ l₁ → B y z ε₂ l₂ → B x z (ε₁ + ε₂) (ℚ<-adding-zero ε₁ ε₂ l₁ l₂)

metric-space : {𝓤 : Universe} → (X : 𝓤 ̇) → 𝓤₁ ⊔ 𝓤 ̇
metric-space X =
 Σ B ꞉ (X → X → (ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇) , m1a X B × m1b X B × m2 X B × m3 X B × m4 X B

\end{code}

A space is a complete metric space if every cauchy sequence in a metric space is also a convergent sequence.

Convergent and Cauchy Sequences are also defined below. In a metric space, all convergent sequences are cauchy sequences.

A definition is also given for what it means for a function to be continous, and what it means for a subspace of a space to be dense.

It is also useful to define the type of positive rationals.

\begin{code}

{- 
bounded-sequence : {𝓤 : Universe} → (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤₀ ̇
bounded-sequence X (B , _) S = ∃ K ꞉ ℚ , ((x y : ℕ) → (l : (0ℚ < K)) → B (S x) (S y) K l)

bounded-sequence-is-prop : {𝓤 : Universe} → (X : 𝓤 ̇) → (m : metric-space X) → (S : ℕ → X) → is-prop (bounded-sequence X m S)
bounded-sequence-is-prop X m S = ∃-is-prop

convergent-sequence : {𝓤 : Universe} → (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤 ̇
convergent-sequence X (B , _) S = ∃ x ꞉ X , ((ε : ℚ) → (l : (0ℚ < ε)) → Σ N ꞉ ℕ , ((n : ℕ) → N < n → B x (S n) ε l))

cauchy-sequence : {𝓤 : Universe} → (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤₀ ̇
cauchy-sequence X (B , _) S = (ε : ℚ) → (l : 0ℚ < ε) → Σ N ꞉ ℕ , ((m n : ℕ) → N < m → N < n → B (S m) (S n) ε l)

convergent→cauchy : {𝓤 : Universe} → (X : 𝓤 ̇) → (m : metric-space X) → (S : ℕ → X) → 𝓤 ̇
convergent→cauchy X m S = convergent-sequence X m S → cauchy-sequence X m S

cauchy→convergent : {𝓤 : Universe} → (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤 ̇
cauchy→convergent X m S = cauchy-sequence X m S → convergent-sequence X m S

complete-metric-space : {𝓤 : Universe} → (X : 𝓤 ̇) → 𝓤₁ ⊔ 𝓤 ̇
complete-metric-space X = Σ m ꞉ (metric-space X) , ((S : ℕ → X) → cauchy→convergent X m S)
-} 

ℚ₊ : 𝓤₀ ̇
ℚ₊ = Σ ε ꞉ ℚ , 0ℚ < ε

bounded-sequence : {𝓤 : Universe} → (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤₀ ̇
bounded-sequence X (B , _) S = ∃ K ꞉ ℚ , ((x y : ℕ) → (l : (0ℚ < K)) → B (S x) (S y) K l)

bounded-sequence-is-prop : {𝓤 : Universe} → (X : 𝓤 ̇) → (m : metric-space X) → (S : ℕ → X) → is-prop (bounded-sequence X m S)
bounded-sequence-is-prop X m S = ∃-is-prop

convergent-sequence : {𝓤 : Universe} → (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤 ̇
convergent-sequence X (B , _) S = ∃ x ꞉ X , (((ε , l) : ℚ₊) → Σ N ꞉ ℕ , ((n : ℕ) → N < n → B x (S n) ε l))

cauchy-sequence : {𝓤 : Universe} → (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤₀ ̇
cauchy-sequence X (B , _) S = ((ε , l) : ℚ₊) → Σ N ꞉ ℕ , ((m n : ℕ) → N < m → N < n → B (S m) (S n) ε l)

convergent→cauchy : {𝓤 : Universe} → (X : 𝓤 ̇) → (m : metric-space X) → (S : ℕ → X) → 𝓤 ̇
convergent→cauchy X m S = convergent-sequence X m S → cauchy-sequence X m S

cauchy→convergent : {𝓤 : Universe} → (X : 𝓤 ̇) → metric-space X → (S : ℕ → X) → 𝓤 ̇
cauchy→convergent X m S = cauchy-sequence X m S → convergent-sequence X m S

complete-metric-space : {𝓤 : Universe} → (X : 𝓤 ̇) → 𝓤₁ ⊔ 𝓤 ̇
complete-metric-space X = Σ m ꞉ (metric-space X) , ((S : ℕ → X) → cauchy→convergent X m S)


\end{code}
