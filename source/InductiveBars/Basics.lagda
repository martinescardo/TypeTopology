Chuangjie Xu and Martin Escardo, December 2013
Revised in November 2026

We study two formulations of inductive bars on finite sequences over an
arbitrary type A and show that they are logically equivalent.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module InductiveBars.Basics where

open import MLTT.Spartan
open import MLTT.List
open import Naturals.Order

open import InductiveBars.Sequences

\end{code}

We work with type-valued predicates.

\begin{code}

_∈_ : {X : 𝓤 ̇} → X → (X → 𝓥 ̇) → 𝓥 ̇
x ∈ V = V x

_∉_ : {X : 𝓤 ̇} → X → (X → 𝓥 ̇) → 𝓥 ̇
x ∉ V = x ∈ V → 𝟘 {𝓤₀}

_⊆_ : {X : 𝓤 ̇}
    → (X → 𝓥 ̇) → (X → 𝓦 ̇)
    → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
V ⊆ W = ∀ x → x ∈ V → x ∈ W

infix 50 _∈_ _∉_
infix 40 _⊆_

\end{code}

The first expresses that a predicate V inductively bars a finite sequence s.

A witness of `V bars s` can be viewed as a well-founded tree. Each internal
node has one outgoing edge labelled a for each a : A. The edge labels along
a path from the root to a leaf form a finite sequence t. That leaf carries
a proof that s ++ t belongs to V.

Different trees may witness the same barring assertion, so `V bars s`
need not be a proposition.

\begin{code}

data _bars_ {A : 𝓤 ̇} (V : List A → 𝓥 ̇) : List A → 𝓤 ⊔ 𝓥 ̇ where
 hit  : {s : List A} → s ∈ V → V bars s
 step : {s : List A} → ((a : A) → V bars (s ++ [ a ])) → V bars s

\end{code}

A generalization of `step` to any finite depth.

\begin{code}

bars-from-level : {A : 𝓤 ̇} (V : List A → 𝓥 ̇) (s : List A) (n : ℕ)
                → ((t : List A) → length t ＝ n → (s ++ t) ∈ V)
                → V bars s
bars-from-level V s 0 p = hit v'
 where
  v : (s ++ []) ∈ V
  v = p [] refl
  v' : s ∈ V
  v' = transport (_∈ V) (([]-right-neutral s) ⁻¹) v
bars-from-level V s (succ n) p = step ih
 where
  ih : ∀ a → V bars (s ++ [ a ])
  ih a = bars-from-level V (s ++ [ a ]) n pᵢ
   where
    pᵢ : ∀ t → length t ＝ n → ((s ++ [ a ]) ++ t) ∈ V
    pᵢ t refl = transport (_∈ V) ((++-assoc s [ a ] t) ⁻¹) (p (a ∷ t) refl)

\end{code}

We say a predicate on finite sequences is monotone if membership is preserved
by appending any finite sequence.  For a monotone predicate V, if V bars the
empty sequence, then V bars every finite sequence.

\begin{code}

is-monotone : {A : 𝓤 ̇} → (List A → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
is-monotone {A = A} V = (s u : List A) → s ∈ V → (s ++ u) ∈ V

monotone-bars-extend
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇) → is-monotone V
 → (s : List A) (a : A)
 → V bars s
 → V bars (s ++ [ a ])
monotone-bars-extend V m s a (hit v) = hit (m s [ a ] v)
monotone-bars-extend V m s a (step φ) = φ a

monotone-bars-append
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇) → is-monotone V
 → (s t : List A)
 → V bars s
 → V bars (s ++ t)
monotone-bars-append V m s [] = transport (V bars_) ([]-right-neutral s)
monotone-bars-append V m s (a ∷ t) b = transport (V bars_) p ih
 where
  claim : V bars (s ++ [ a ])
  claim = monotone-bars-extend V m s a b
  ih : V bars ((s ++ [ a ]) ++ t)
  ih = monotone-bars-append V m (s ++ [ a ]) t claim
  p : (s ++ [ a ]) ++ t ＝ s ++ a ∷ t
  p = ++-assoc s [ a ] t

monotone-bars-root-implies-bars-all
 : {A : 𝓤 ̇}  (V : List A → 𝓥 ̇) → is-monotone V
 → V bars []
 → (s : List A) → V bars s
monotone-bars-root-implies-bars-all V m b s
 = monotone-bars-append V m [] s b

monotone-bars-root-iff-bars-all
 : {A : 𝓤 ̇}  (V : List A → 𝓥 ̇) → is-monotone V
 → (V bars []) ↔ ((s : List A) → V bars s)
monotone-bars-root-iff-bars-all V m
 = monotone-bars-root-implies-bars-all V m , λ b → b []

\end{code}

If V bars the empty sequence, we call V an inductive bar.

We now give an equivalent formulation without an explicit root sequence.
For this, we consider sections of predicates on finite sequences.

Concatenation associates to each predicate V a binary type-valued relation

    Rⱽ s t = (s ++ t) ∈ V.

Fixing its first argument s gives the section of V at s:

    section V s t = (s ++ t) ∈ V

For a singleton prefix [ a ], we write section₁ V a.

\begin{code}

section : {A : 𝓤 ̇} → (List A → 𝓥 ̇) → (List A) → List A → 𝓥 ̇
section V s t = V (s ++ t)

section₁ : {A : 𝓤 ̇} → (List A → 𝓥 ̇) → A → List A → 𝓥 ̇
section₁ V a s = section V [ a ] s

∈-implies-[]∈-section
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇) (s : List A)
 → s ∈ V → [] ∈ section V s
∈-implies-[]∈-section V [] v = v
∈-implies-[]∈-section V (a ∷ s) v = ∈-implies-[]∈-section (section₁ V a) s v

section-append
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇) (s t : List A)
 → section V (s ++ t) ＝ section (section V s) t
section-append V [] t = refl
section-append V (a ∷ s) t = section-append (section₁ V a) s t

\end{code}

As an alternative formulation, the predicate `is-inductive-bar V` is generated
by the following two rules:
 - if V contains the empty sequence, then V is an inductive bar;
 - if the section of V at each a : A is an inductive bar, then so is V.

The type `is-inductive-bar V` need not be a proposition.

\begin{code}

data is-inductive-bar {𝓥 : Universe} {A : 𝓤 ̇}
 : (List A → 𝓥 ̇) → (𝓤 ⊔ 𝓥) ⁺ ̇
 where
 base : {V : List A → 𝓥 ̇}
      → [] ∈ V
      → is-inductive-bar V
 step : {V : List A → 𝓥 ̇}
      → ((a : A) → is-inductive-bar (section₁ V a))
      → is-inductive-bar V

inductive-bar-section-append
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇) (s t : List A)
 → is-inductive-bar (section V (s ++ t))
 → is-inductive-bar (section (section V s) t)
inductive-bar-section-append V s t
 = transport is-inductive-bar (section-append V s t)

inductive-bar-respects-inclusion
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇) (W : List A → 𝓦 ̇)
 → V ⊆ W
 → is-inductive-bar V
 → is-inductive-bar W
inductive-bar-respects-inclusion V W θ (base v) = base (θ [] v)
inductive-bar-respects-inclusion V W θ (step φ) = step ψ
 where
  ψ : ∀ a → is-inductive-bar (section₁ W a)
  ψ a = inductive-bar-respects-inclusion
         (section₁ V a)
         (section₁ W a)
         (λ s → θ (a ∷ s))
         (φ a)

inductive-bar-from-sections
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇) (m : ℕ)
 → ((s : List A) → length s ＝ m → is-inductive-bar (section V s))
 → is-inductive-bar V
inductive-bar-from-sections V 0 φ = φ [] refl
inductive-bar-from-sections V (succ m) φ = step ih
 where
  ih : ∀ a → is-inductive-bar (section₁ V a)
  ih a = inductive-bar-from-sections (section₁ V a) m ψ
   where
    ψ : ∀ s → length s ＝ m → is-inductive-bar (section (section₁ V a) s)
    ψ s e = φ (a ∷ s) (ap succ e)

\end{code}

If V bars the empty sequence, then it is an inductive bar.

\begin{code}

bars-implies-inductive-bar-section
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇) (s : List A)
 → V bars s → is-inductive-bar (section V s)
bars-implies-inductive-bar-section V s (hit v)
 = base (∈-implies-[]∈-section V s v)
bars-implies-inductive-bar-section V s (step φ) = step goal
 where
  ih : ∀ a → is-inductive-bar (section V (s ++ [ a ]))
  ih a = bars-implies-inductive-bar-section V (s ++ [ a ]) (φ a)
  goal : ∀ a → is-inductive-bar (section₁ (section V s) a)
  goal a = inductive-bar-section-append V s [ a ] (ih a)

bars-root-implies-inductive-bar
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇)
 → V bars [] → is-inductive-bar V
bars-root-implies-inductive-bar V
 = bars-implies-inductive-bar-section V []

\end{code}

If V is an inductive bar, then it bars the empty sequence.

\begin{code}

section₁-bars-implies-bars-cons
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇) (a : A) (s : List A)
 → (section₁ V a) bars s
 → V bars (a ∷ s)
section₁-bars-implies-bars-cons V a s (hit v) = hit v
section₁-bars-implies-bars-cons V a s (step φ) = step ih
 where
  ih : ∀ x → V bars (a ∷ s ++ [ x ])
  ih x = section₁-bars-implies-bars-cons V a (s ++ [ x ]) (φ x)

inductive-bar-section-implies-bars
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇) (s : List A)
 → is-inductive-bar (section V s)
 → V bars s
inductive-bar-section-implies-bars V [] (base v) = hit v
inductive-bar-section-implies-bars V [] (step φ)
 = step (λ a → inductive-bar-section-implies-bars V [ a ] (φ a))
inductive-bar-section-implies-bars V (a ∷ s) b
 = section₁-bars-implies-bars-cons V a s
    (inductive-bar-section-implies-bars (section₁ V a) s b)

inductive-bar-section-iff-bars
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇) (s : List A)
 → (is-inductive-bar (section V s)) ↔ (V bars s)
inductive-bar-section-iff-bars V s
 = inductive-bar-section-implies-bars V s
 , bars-implies-inductive-bar-section V s

inductive-bar-implies-bars-root
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇)
 → is-inductive-bar V → V bars []
inductive-bar-implies-bars-root V
 = inductive-bar-section-implies-bars V []

inductive-bar-iff-bars-root
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇)
 → (is-inductive-bar V) ↔ (V bars [])
inductive-bar-iff-bars-root V
 = inductive-bar-implies-bars-root V , bars-root-implies-inductive-bar V

\end{code}

No monotonicity assumption is needed in the above logical equivalence.

If the inductive bar is monotone, then it bars all finite sequences.

\begin{code}

monotone-inductive-bar-bars-all
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇)
 → is-monotone V
 → is-inductive-bar V
 → (s : List A) → V bars s
monotone-inductive-bar-bars-all V m p
 = monotone-bars-root-implies-bars-all V m
    (inductive-bar-implies-bars-root V p)

monotone-inductive-bar-sections
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇)
 → is-monotone V
 → is-inductive-bar V
 → (s : List A)
 → is-inductive-bar (section V s)
monotone-inductive-bar-sections V m b s =
 bars-implies-inductive-bar-section V s
  (monotone-inductive-bar-bars-all V m b s)

\end{code}

If V is an inductive bar, then every infinite sequence has a finite prefix
belonging to V.

\begin{code}

inductive-bar-meets-every-sequence
 : {A : 𝓤 ̇} (V : List A → 𝓥 ̇)
 → is-inductive-bar V
 → (α : ℕ → A)
 → Σ s ꞉ List A , ((α extends s) × (s ∈ V))
inductive-bar-meets-every-sequence V (base v) α = [] , ⋆ , v
inductive-bar-meets-every-sequence V (step φ) α
 using (s , e , p) ←
   inductive-bar-meets-every-sequence (section₁ V (α 0)) (φ (α 0)) (α ∘ succ)
 = (α 0 ∷ s) , (refl , e) , p

\end{code}

Each inductive bar meets all infinite sequences bounded pointwise by
a given sequence within a common finite depth.

\begin{code}

inductive-bar-meets-bounded-sequences-uniformly
 : (V : List ℕ → 𝓥 ̇)
 → is-inductive-bar V
 → (δ : ℕ → ℕ)
 → Σ m ꞉ ℕ ,
    ((α : ℕ → ℕ) → α ≤¹ δ
                 → Σ s ꞉ List ℕ , (length s ≤ℕ m) × (α extends s) × s ∈ V)
inductive-bar-meets-bounded-sequences-uniformly V (base v) δ
 = 0 , (λ _ _ → [] , ⋆ , ⋆ , v)
inductive-bar-meets-bounded-sequences-uniformly V (step φ) δ
 = succ m , goal
 where
  δ₀ : ℕ
  δ₀ = δ 0
  ihs : (i : ℕ)
      → Σ m ꞉ ℕ ,
         ((α : ℕ → ℕ)
          → α ≤¹ (δ ∘ succ)
          → Σ s ꞉ List ℕ , (length s ≤ℕ m) × (α extends s) × s ∈ section₁ V i)
  ihs i = inductive-bar-meets-bounded-sequences-uniformly
          (section₁ V i) (φ i) (δ ∘ succ)
  μ : ℕ → ℕ
  μ i = pr₁ (ihs i)
  m : ℕ
  m = pr₁ (finite-upper-bound μ δ₀)
  upper : (i : ℕ) → i ≤ℕ δ₀ → μ i ≤ℕ m
  upper = pr₂ (finite-upper-bound μ δ₀)
  goal : (α : ℕ → ℕ) → α ≤¹ δ
       → Σ s ꞉ List ℕ , (length s ≤ℕ succ m) × (α extends s) × s ∈ V
  goal α r
   using (s , rs , e , v) ← pr₂ (ihs (α 0)) (α ∘ succ) (r ∘ succ)
   = s' , rs' , e' , v
   where
    s' : List ℕ
    s' = α 0 ∷ s
    rs' : length s' ≤ℕ succ m
    rs' = ≤-trans (length s) (μ (α 0)) m rs (upper (α 0) (r 0))
    e' : α extends s'
    e' = refl , e

\end{code}
