Chuangjie Xu and Martin Escardo, December 2013
Revised in November 2026

We study two formulations of inductive bars on finite sequences of
natural numbers and show that they are logically equivalent.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module InductiveBars.Basics where

open import MLTT.Spartan
open import MLTT.List
open import UF.Powerset
open import Naturals.Order

open import InductiveBars.Sequences

\end{code}

The first expresses that a subset V inductively bars a finite sequence s.

A witness of `V bars s` can be viewed as a well-founded tree whose root
is labelled `s`.  Each internal node branches over ℕ; if it is labelled `t`,
then its nth child is labelled `t ++ [ n ]`.  Each leaf carries a proof
that the sequence labelling it belongs to V.

Different trees may witness the same barring assertion, so `V bars s`
need not be a proposition.

\begin{code}

data _bars_ (V : 𝓟 (List ℕ)) : List ℕ → 𝓤₀ ̇ where
 hit  : {s : List ℕ} → s ∈ V → V bars s
 step : {s : List ℕ} → ((n : ℕ) → V bars (s ++ [ n ])) → V bars s

\end{code}

A generalization of `step` to any finite depth.

\begin{code}

bars-from-level : (V : 𝓟 (List ℕ)) (s : List ℕ) (n : ℕ)
                → ((t : List ℕ) → length t ＝ n → (s ++ t) ∈ V)
                → V bars s
bars-from-level V s 0 p = hit v'
 where
  v : (s ++ []) ∈ V
  v = p [] refl
  v' : s ∈ V
  v' = transport (_∈ V) (([]-right-neutral s) ⁻¹) v
bars-from-level V s (succ n) p = step ih
 where
  ih : (i : ℕ) → V bars (s ++ [ i ])
  ih i = bars-from-level V (s ++ [ i ]) n pᵢ
   where
    pᵢ : (t : List ℕ) → length t ＝ n → ((s ++ [ i ]) ++ t) ∈ V
    pᵢ t refl = transport (_∈ V) ((++-assoc s [ i ] t) ⁻¹) (p (i ∷ t) refl)

\end{code}

We say a subset of finite sequences is monotone if membership is preserved
by appending any finite sequence.  For a monotone subset V, if V bars the
empty sequence, then V bars every finite sequence.

\begin{code}

is-monotone : 𝓟 (List ℕ) → 𝓤₀ ̇
is-monotone V = (s u : List ℕ) → s ∈ V → (s ++ u) ∈ V

monotone-bars-extend
 : (V : 𝓟 (List ℕ)) → is-monotone V
 → (s : List ℕ) (n : ℕ)
 → V bars s
 → V bars (s ++ [ n ])
monotone-bars-extend V m s n (hit v) = hit (m s [ n ] v)
monotone-bars-extend V m s n (step φ) = φ n

monotone-bars-append
 : (V : 𝓟 (List ℕ)) → is-monotone V
 → (s t : List ℕ)
 → V bars s
 → V bars (s ++ t)
monotone-bars-append V m s [] = transport (V bars_) ([]-right-neutral s)
monotone-bars-append V m s (n ∷ t) b = transport (V bars_) p ih
 where
  claim : V bars (s ++ [ n ])
  claim = monotone-bars-extend V m s n b
  ih : V bars ((s ++ [ n ]) ++ t)
  ih = monotone-bars-append V m (s ++ [ n ]) t claim
  p : (s ++ [ n ]) ++ t ＝ s ++ n ∷ t
  p = ++-assoc s [ n ] t

monotone-bars-root-implies-bars-all
 : (V : 𝓟 (List ℕ)) → is-monotone V
 → V bars []
 → (s : List ℕ) → V bars s
monotone-bars-root-implies-bars-all V m b s
 = monotone-bars-append V m [] s b

\end{code}

If V bars the empty sequence, we say it is an inductive bar.

Alternatively, we can define inductive bars without an explicit root sequence.
For this, we consider sections of a subset of finite sequences.

Each subset V gives a relation

    Rⱽ = { (s,t) | s ++ t ∈ V } ⊆ List ℕ × List ℕ

and thus we define a section of V at s by

    section V s = { t | s ++ t ∈ V }.

For a singleton prefix [ n ], we write section₁ V n.

\begin{code}

section : 𝓟 (List ℕ) → (List ℕ) → 𝓟 (List ℕ)
section V s t = V (s ++ t)

section₁ : 𝓟 (List ℕ) → ℕ → 𝓟 (List ℕ)
section₁ V n s = section V [ n ] s

∈-implies-[]∈-section
 : (V : 𝓟 (List ℕ)) (s : List ℕ)
 → s ∈ V → [] ∈ section V s
∈-implies-[]∈-section V [] v = v
∈-implies-[]∈-section V (n ∷ s) v = ∈-implies-[]∈-section (section₁ V n) s v

section-append
 : (V : 𝓟 (List ℕ)) (s t : List ℕ)
 → section V (s ++ t) ＝ section (section V s) t
section-append V [] t = refl
section-append V (n ∷ s) t = section-append (section₁ V n) s t

\end{code}

As an alternative formulation, the predicate `is-inductive-bar V` is generated
by the following two rules:
 - if V contains the empty sequence, then V is an inductive bar;
 - if the section of V at each n is an inductive bar, then so is V.

The type `is-inductive-bar V` need not be a proposition.

\begin{code}

data is-inductive-bar : 𝓟 (List ℕ) → 𝓤₁ ̇ where
 base : {V : 𝓟 (List ℕ)} → [] ∈ V → is-inductive-bar V
 step : {V : 𝓟 (List ℕ)} → ((n : ℕ) → is-inductive-bar (section₁ V n)) → is-inductive-bar V

inductive-bar-section-append
 : (V : 𝓟 (List ℕ)) (s t : List ℕ)
 → is-inductive-bar (section V (s ++ t))
 → is-inductive-bar (section (section V s) t)
inductive-bar-section-append V s t
 = transport is-inductive-bar (section-append V s t)

inductive-bar-respects-inclusion
 : (V W : 𝓟 (List ℕ))
 → V ⊆ W
 → is-inductive-bar V
 → is-inductive-bar W
inductive-bar-respects-inclusion V W θ (base v) = base (θ [] v)
inductive-bar-respects-inclusion V W θ (step φ) = step ψ
 where
  ψ : (n : ℕ) → is-inductive-bar (section₁ W n)
  ψ n = inductive-bar-respects-inclusion
         (section₁ V n)
         (section₁ W n)
         (λ s → θ (n ∷ s))
         (φ n)

inductive-bar-from-sections
 : (V : 𝓟 (List ℕ)) (m : ℕ)
 → ((s : List ℕ) → length s ＝ m → is-inductive-bar (section V s))
 → is-inductive-bar V
inductive-bar-from-sections V 0 φ = φ [] refl
inductive-bar-from-sections V (succ m) φ = step ih
 where
  ih : (n : ℕ) → is-inductive-bar (section₁ V n)
  ih n = inductive-bar-from-sections (section₁ V n) m ψ
   where
    ψ : (s : List ℕ)
      → length s ＝ m → is-inductive-bar (section (section₁ V n) s)
    ψ s e = φ (n ∷ s) (ap succ e)

\end{code}

If V bars the empty sequence, then it is an inductive bar.

\begin{code}

bars-implies-inductive-bar-section
 : (V : 𝓟 (List ℕ)) (s : List ℕ)
 → V bars s → is-inductive-bar (section V s)
bars-implies-inductive-bar-section V s (hit v)
 = base (∈-implies-[]∈-section V s v)
bars-implies-inductive-bar-section V s (step φ) = step goal
 where
  ih : (n : ℕ) → is-inductive-bar (section V (s ++ [ n ]))
  ih n = bars-implies-inductive-bar-section V (s ++ [ n ]) (φ n)
  goal : (n : ℕ) → is-inductive-bar (section₁ (section V s) n)
  goal n = inductive-bar-section-append V s [ n ] (ih n)

bars-root-implies-inductive-bar
 : (V : 𝓟 (List ℕ)) → V bars [] → is-inductive-bar V
bars-root-implies-inductive-bar V = bars-implies-inductive-bar-section V []

\end{code}

If V is an inductive bar, then it bars the empty sequence.

\begin{code}

section₁-bars-implies-bars-cons
 : (V : 𝓟 (List ℕ)) (n : ℕ) (s : List ℕ)
 → (section₁ V n) bars s
 → V bars (n ∷ s)
section₁-bars-implies-bars-cons V n s (hit v) = hit v
section₁-bars-implies-bars-cons V n s (step φ) = step ih
 where
  ih : (i : ℕ) → V bars (n ∷ s ++ [ i ])
  ih i = section₁-bars-implies-bars-cons V n (s ++ [ i ]) (φ i)

inductive-bar-implies-bars-root
 : (V : 𝓟 (List ℕ)) → is-inductive-bar V → V bars []
inductive-bar-implies-bars-root V (base v) = hit v
inductive-bar-implies-bars-root V (step φ) = step goal
 where
  ih : (n : ℕ) → (section₁ V n) bars []
  ih n = inductive-bar-implies-bars-root (section₁ V n) (φ n)
  goal : (n : ℕ) → V bars [ n ]
  goal n = section₁-bars-implies-bars-cons V n [] (ih n)

\end{code}

No monotonicity assumption is needed in the above logical equivalence.

If the inductive bar is monotone, then it bars all finite sequences.

\begin{code}

monotone-inductive-bar-bars-all
 : (V : 𝓟 (List ℕ))
 → is-monotone V
 → is-inductive-bar V
 → (s : List ℕ) → V bars s
monotone-inductive-bar-bars-all V m p
 = monotone-bars-root-implies-bars-all V m
    (inductive-bar-implies-bars-root V p)

monotone-inductive-bar-sections
 : (V : 𝓟 (List ℕ))
 → is-monotone V
 → is-inductive-bar V
 → (s : List ℕ)
 → is-inductive-bar (section V s)
monotone-inductive-bar-sections V m b s =
 bars-implies-inductive-bar-section V s
  (monotone-inductive-bar-bars-all V m b s)

\end{code}

If V is an inductive bar, then every infinite sequence has a finite prefix
belonging to V.

\begin{code}

inductive-bar-meets-every-sequence
 : (V : 𝓟 (List ℕ))
 → is-inductive-bar V
 → (α : ℕ → ℕ)
 → Σ s ꞉ List ℕ , ((α extends s) × (s ∈ V))
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
 : (V : 𝓟 (List ℕ))
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

Each inductive bar gives a dialogue tree.  Its evaluation returns
a finite prefix of its input belonging to the bar.

\begin{code}

open import EffectfulForcing.MFPSAndVariations.Dialogue

shift : {A : 𝓤 ̇} → B A → B A
shift (η n)   = η n
shift (β φ i) = β (shift ∘ φ) (succ i)

shift-spec : {A : 𝓤 ̇} (d : B A) (α : ℕ → ℕ)
           → dialogue (shift d) α ＝ dialogue d (α ∘ succ)
shift-spec (η n) α = refl
shift-spec (β φ i) α = shift-spec (φ (α (succ i))) α

inductive-bar-gives-dialogue
 : (V : 𝓟 (List ℕ))
 → is-inductive-bar V
 → Σ d ꞉ B (List ℕ) ,
    ((α : ℕ → ℕ) → (α extends (dialogue d α)) × (dialogue d α ∈ V))
inductive-bar-gives-dialogue V (base v) = η [] , (λ _ → ⋆ , v)
inductive-bar-gives-dialogue V (step φ) = d , goal
 where
  ihs : (n : ℕ)
      → Σ d ꞉ B (List ℕ) , ((α : ℕ → ℕ) →
         (α extends dialogue d α) × dialogue d α ∈ section₁ V n)
  ihs n = inductive-bar-gives-dialogue (section₁ V n) (φ n)
  ψ : ℕ → B (List ℕ)
  ψ n = B-functor (n ∷_) (shift (pr₁ (ihs n)))
  d : B (List ℕ)
  d = β ψ 0
  goal : (α : ℕ → ℕ) → (α extends (dialogue d α)) × (dialogue d α ∈ V)
  goal α
   using (d₀ , res) ← ihs (α 0)
       | (es , vs) ← res (α ∘ succ)
   = transport (λ s → (α extends s) × (s ∈ V)) e ((refl , es) , vs)
   where
    s : List ℕ
    s = dialogue d₀ (α ∘ succ)
    e₀ : α 0 ∷ decode α (shift d₀) ＝ α 0 ∷ s
    e₀ = ap (α 0 ∷_) (shift-spec d₀ α)
    e₁ : α 0 ∷ decode α (shift d₀) ＝ dialogue d α
    e₁ = decode-α-is-natural (α 0 ∷_) (shift d₀) α
    e : α 0 ∷ s ＝ dialogue d α
    e = e₀ ⁻¹ ∙ e₁

\end{code}
