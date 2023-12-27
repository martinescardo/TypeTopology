Ayberk Tosun.

Formulations of some alternative definitions of the notion of continuity from
`MFPSAndVariations.Continuity` and proofs of their equivalences.

First equivalence, for continuity, proved on 2023-06-13.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.FunExt

module EffectfulForcing.MFPSAndVariations.ContinuityProperties (fe : Fun-Ext) where

open import EffectfulForcing.MFPSAndVariations.Continuity

open import MLTT.Spartan
open import MLTT.Athenian
open import MLTT.Two-Properties
open import Naturals.Order
open import Naturals.Properties using (zero-not-positive; succ-no-fp)
open import UF.Retracts
open import UF.Embeddings
open import UF.Equiv
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import MGS.hlevels using (ℕ-is-set)

\end{code}

We first formulate the `α ＝⦅ n ⦆ β` relation that expresses that two sequences
`α`, `β` of natural numbers are equal up to (not inclusive) some bound `n`.
These have been adapted from the `CantorSearch` module authored by Martín
Escardó (including the proofs `agreement→` and `agreement←`).

\begin{code}

hd : {X : 𝓤₀  ̇} → (ℕ → X) → X
hd α = α 0

tl : {X : 𝓤₀  ̇} → (ℕ → X) → ℕ → X
tl α = α ∘ succ

_＝⦅_⦆_ : {X : 𝓤₀  ̇} → (ℕ → X) → ℕ → (ℕ → X) → 𝓤₀  ̇
α ＝⦅ 0      ⦆ β = 𝟙
α ＝⦅ succ n ⦆ β = (hd α ＝ hd β) × tl α ＝⦅ n ⦆ tl β

\end{code}

\begin{code}

agreement→ : (α α′ : Baire) (n : ℕ)
           → α ＝⦅ n ⦆ α′
           → (i : ℕ) → (i <ℕ n) → α i ＝ α′ i
agreement→ α α′ zero     p         zero     ()
agreement→ α α′ (succ n) (p₁ , p₂) zero     q = p₁
agreement→ α α′ (succ n) (p₁ , p₂) (succ i) q = IH i q
 where
  IH : (j : ℕ) → j <ℕ n → α (succ j) ＝ α′ (succ j)
  IH = agreement→ (tl α) (tl α′) n p₂

agreement← : (α α′ : Baire) (n : ℕ)
           → ((i : ℕ) → (i <ℕ n) → α i ＝ α′ i)
           → α ＝⦅ n ⦆ α′
agreement← α α′ zero     φ = ⋆
agreement← α α′ (succ n) φ = φ 0 ⋆ , (agreement← (tl α) (tl α′) n ψ)
 where
  ψ : (j : ℕ) → j <ℕ n → tl α j ＝ tl α′ j
  ψ j p = φ (succ j) (succ-monotone (succ j) n p)

\end{code}

\section{Continuity}

Using the `_＝⦅_⦆_` relation, we express the “usual” notion of continuity
mentioned in the TODO. We call this `is-continuous₀` and prove at the end of the
module that it is logically equivalent to `is-continuous`.

\begin{code}

is-continuous₀ : (Baire → ℕ) → 𝓤₀  ̇
is-continuous₀ f =
 (α : Baire) → Σ n ꞉ ℕ , ((α′ : Baire) → α ＝⦅ n ⦆ α′ → f α ＝ f α′)

\end{code}

We now formulate an alternative non-inductive version of the `_＝⟪_⟫_` relation
that we call `_＝⟪_⟫₀_` and prove its logical equivalence with `_＝⟪_⟫_`. The
motivation for the non-inductive formulation is to use it as an intermediate
step to simplify our proofs.

\begin{code}

_＝⟪_⟫₀_ : {X : 𝓤₀  ̇} → (ℕ → X) → List ℕ → (ℕ → X) → 𝓤₀  ̇
_＝⟪_⟫₀_ α₁ s α₂ = (i : ℕ) → member i s → α₁ i ＝ α₂ i

\end{code}

It is an obvious fact that equality up to `i ∷ is` (with `_＝⟪_⟫₀_`) entails
equality up to `is`. We record this fact as `＝⟪⟫₀-cons`.

\begin{code}

＝⟪⟫₀-cons : {X : 𝓤₀  ̇} (α α′ : ℕ → X) (i : ℕ) (is : List ℕ)
           → α ＝⟪ i ∷ is ⟫₀ α′ → α ＝⟪ is ⟫₀ α′
＝⟪⟫₀-cons α α′ i is t j p = t j (in-tail p)

\end{code}


We now generalize this fact. Equality up to `ms ++ ns` entails both equality up
to `ms` and up to `ns`. In other words, `α₁ ＝⟪_⟫₀ α₂` is a semigroup
homomorphism from semigroup `(List ℕ, _++_)` into semigroup `(𝓤₀, _×_)`.

\begin{code}

＝⟪⟫-++-lemma₁
 : {X : 𝓤₀  ̇} → (α₁ α₂ : ℕ → X) (ms ns : List ℕ)
 → α₁ ＝⟪ ms ++ ns ⟫₀ α₂ → (α₁ ＝⟪ ms ⟫₀ α₂) × (α₁ ＝⟪ ns ⟫₀ α₂)
＝⟪⟫-++-lemma₁ α₁ α₂ ms ns p = † , ‡
 where
  † : α₁ ＝⟪ ms ⟫₀ α₂
  † n q = p n (right-concatenation-preserves-membership n ms ns q)

  ‡ : α₁ ＝⟪ ns ⟫₀ α₂
  ‡ n q = p n (left-concatenation-preserves-membership n ns ms q)

＝⟪⟫-++-lemma₂
 : {X : 𝓤₀  ̇} (α₁ α₂ : ℕ → X) (ms ns : List ℕ)
 → (α₁ ＝⟪ ms ⟫₀ α₂) × (α₁ ＝⟪ ns ⟫₀ α₂) → α₁ ＝⟪ ms ++ ns ⟫₀ α₂
＝⟪⟫-++-lemma₂ α₁ α₂ ms ns (p , q) i r = cases (p i) (q i) (++-membership₁ i ms ns r)

＝⟪⟫-respects-list-concatenation
 : {X : 𝓤₀  ̇} (α₁ α₂ : ℕ → X) (ms ns : List ℕ)
 → α₁ ＝⟪ ms ++ ns ⟫₀ α₂ ⇔ (α₁ ＝⟪ ms ⟫₀ α₂) × (α₁ ＝⟪ ns ⟫₀ α₂)
＝⟪⟫-respects-list-concatenation α₁ α₂ ms ns = ＝⟪⟫-++-lemma₁ α₁ α₂ ms ns
                                             , ＝⟪⟫-++-lemma₂ α₁ α₂ ms ns

\end{code}

The alternative version of `_＝⟪_⟫_` that we defined implies the original
version and vice versa.

\begin{code}

＝⟪⟫₀-implies-＝⟪⟫ : {X : 𝓤₀  ̇} (α α′ : ℕ → X) (s : List ℕ)
                   → α ＝⟪ s ⟫₀ α′ → α ＝⟪ s ⟫  α′
＝⟪⟫₀-implies-＝⟪⟫ α α′ []       t = []
＝⟪⟫₀-implies-＝⟪⟫ α α′ (i ∷ is) t =
 (t i in-head) ∷ (＝⟪⟫₀-implies-＝⟪⟫ α α′ is (＝⟪⟫₀-cons α α′ i is t))

＝⟪⟫-implies-＝⟪⟫₀ : (α β : Baire) (s : List ℕ) → α ＝⟪ s ⟫ β → α ＝⟪ s ⟫₀ β
＝⟪⟫-implies-＝⟪⟫₀ α α′ []       []       i ()
＝⟪⟫-implies-＝⟪⟫₀ α α′ (i ∷ is) (p ∷ ps) i in-head     = p
＝⟪⟫-implies-＝⟪⟫₀ α α′ (_ ∷ is) (p ∷ ps) j (in-tail q) =
 ＝⟪⟫-implies-＝⟪⟫₀ α α′ is ps j q

\end{code}

We now define the `maximum` function computing the maximum of a given list of
natural numbers.

\begin{code}

maximum : List ℕ → ℕ
maximum = foldr max 0

\end{code}

Recall that the first (logical) equivalence we would like to prove is that
between `is-continuous` and `is-continuous₀`. We tackle this in the next
section, and the converse direction in the section after that.

\section{`is-continuous` implies `is-continuous₀`}

The fact that `is-continuous` implies `is-continuous₀` is the easy direction of
the proof. We need only two minor lemmas to conclude this.

\begin{code}

member-implies-below-max : (s : List ℕ) (i : ℕ) → member i s → i ≤ℕ maximum s
member-implies-below-max (m ∷ ns) m in-head     = max-≤-upper-bound m (maximum ns)
member-implies-below-max (n ∷ ns) m (in-tail p) =
 ≤-trans m _ _ (member-implies-below-max ns m p) (max-≤-upper-bound' (maximum ns) n)


＝⦅⦆-implies-＝⟪⟫-for-suitable-modulus : (α α′ : Baire) (s : List ℕ)
       → α ＝⦅ succ (maximum s) ⦆ α′
       → α ＝⟪ s ⟫ α′
＝⦅⦆-implies-＝⟪⟫-for-suitable-modulus α α′ s t = ＝⟪⟫₀-implies-＝⟪⟫ α α′ s †
 where
  m : ℕ
  m = succ (maximum s)

  † : α ＝⟪ s ⟫₀ α′
  † i p = agreement→ α α′ m t i (member-implies-below-max s i p)


continuity-implies-continuity₀ : (f : Baire → ℕ)
                               → is-continuous f → is-continuous₀ f
continuity-implies-continuity₀ f c = †
 where
  † : is-continuous₀ f
  † α = m , γ
   where
    s = pr₁ (c α)
    m = succ (maximum s)

    γ : (α′ : Baire) → α ＝⦅ m ⦆ α′ → f α ＝ f α′
    γ α′ p = pr₂ (c α) α′ (＝⦅⦆-implies-＝⟪⟫-for-suitable-modulus α α′ s p)

\end{code}

\section{`is-continuous₀` implies `is-continuous`}

We now address the converse direction which is harder.

We first define the `range` function such that `range n` is the list `[0..n]`
ad prove its completeness.

\begin{code}

range : ℕ → List ℕ
range zero     = [ 0 ]
range (succ n) = succ n ∷ range n

range-succ : (i n : ℕ) → member i (range n) → member (succ i) (range (succ n))
range-succ zero     zero     p            = in-head
range-succ (succ i) zero     (in-tail ())
range-succ zero     (succ n) (in-tail p)  = in-tail (range-succ zero n p)
range-succ (succ i) (succ i) in-head      = in-head
range-succ (succ i) (succ n) (in-tail p)  = in-tail (range-succ (succ i) n p)

range-is-complete : (i n : ℕ) → i ≤ℕ n → member i (range n)
range-is-complete zero     zero     p = in-head
range-is-complete zero     (succ n) p = in-tail (range-is-complete zero n p)
range-is-complete (succ i) (succ n) p = range-succ i n (range-is-complete i n p)

\end{code}

We combine all these into a final lemma that we need:

\begin{code}

＝⟪⟫-range-implies-＝⦅⦆ : (α α′ : Baire) (n : ℕ)
                        → α ＝⟪ range n ⟫ α′
                        → α ＝⦅ n ⦆ α′
＝⟪⟫-range-implies-＝⦅⦆ α α′ n p = agreement← α α′ n †
 where
  † : (j : ℕ) → j <ℕ n → α j ＝ α′ j
  † j q = ＝⟪⟫-implies-＝⟪⟫₀ α α′ (range n) p j ‡
   where
    ‡ : member j (range n)
    ‡ = range-is-complete j n (<-coarser-than-≤ j n q)

\end{code}

The result we want now follows easily:

\begin{code}

continuity₀-implies-continuity : (f : Baire → ℕ)
                               → is-continuous₀ f → is-continuous f
continuity₀-implies-continuity f c α = range m , γ
 where
  m = pr₁ (c α)

  γ : (α′ : Baire) → α ＝⟪ range m ⟫ α′ → f α ＝ f α′
  γ α′ p = pr₂ (c α) α′ (＝⟪⟫-range-implies-＝⦅⦆ α α′ m p)

\end{code}

Finally, we record the logical equivalence as a fact in itself.

\begin{code}

continuity₀-iff-continuity : (f : Baire → ℕ)
                           → is-continuous₀ f ⇔ is-continuous f
continuity₀-iff-continuity f = † , ‡
 where
  † = continuity₀-implies-continuity f
  ‡ = continuity-implies-continuity₀ f

\end{code}

We also define the following operation `modulus-at₀` that projects out the
modulus of continuity computed by a proof of `is-continuous₀`:

\begin{code}

modulus-at₀ : (f : Baire → ℕ) → is-continuous₀ f → Baire → ℕ
modulus-at₀ f c α = pr₁ (c α)

\end{code}

\section{Uniform continuity}

We start by defining the notion of being Boolean-valued: a point `α : Baire` of
the Baire space is called Boolean if its range is a subset of `{0, 1}`.

\begin{code}

is-boolean-valued : ℕ → 𝓤₀  ̇
is-boolean-valued n = (n ＝ 0) + (n ＝ 1)

embedding-𝟚-ℕ-gives-boolean : (b : 𝟚) → is-boolean-valued (embedding-𝟚-ℕ b)
embedding-𝟚-ℕ-gives-boolean ₀ = inl refl
embedding-𝟚-ℕ-gives-boolean ₁ = inr refl

to-bool : (n : ℕ) → is-boolean-valued n → 𝟚
to-bool _ (inl p) = ₀
to-bool _ (inr q) = ₁

\end{code}

A point `α : Baire` of the Baire space is called Boolean-valued if its range is
a subset of {`₀`, `₁`}.

\begin{code}

is-boolean-point : Baire → 𝓤₀  ̇
is-boolean-point α = (n : ℕ) → is-boolean-valued (α n)

θ-lemma : (α : Baire) (i : ℕ) → is-prop (is-boolean-valued (α i))
θ-lemma α i    (inl p) (inl q) = ap inl (ℕ-is-set (α i) 0 p q)
θ-lemma α i    (inl p) (inr q) = 𝟘-elim (succ-no-fp 0 ※)
                                  where
                                   ※ : 0 ＝ 1
                                   ※ = 0 ＝⟨ p ⁻¹ ⟩ α i ＝⟨ q ⟩ 1 ∎
θ-lemma α i (inr p) (inl q)    = 𝟘-elim (succ-no-fp 0 ※)
                                  where
                                   ※ : 0 ＝ 1
                                   ※ = 0 ＝⟨ q ⁻¹ ⟩ α i ＝⟨ p ⟩ 1 ∎
θ-lemma α i (inr p) (inr q) = ap inr (ℕ-is-set (α i) 1 p q)

being-boolean-point-is-prop : (α : Baire) → is-prop (is-boolean-point α)
being-boolean-point-is-prop α = Π-is-prop fe (θ-lemma α)

boolean-point-lemma : (α : Baire) (bv : is-boolean-point α) (i : ℕ)
                    → (p : α i ＝ 0)
                    → bv i ＝ inl p
boolean-point-lemma α bv i p = θ-lemma α i (bv i) (inl p)

\end{code}

Using this, we can give an alternative definition of the Cantor space as the
subtype of Baire space consisting of the Boolean points,

\begin{code}

Cantor₀ : 𝓤₀  ̇
Cantor₀ = Σ α ꞉ Baire , is-boolean-point α

point-of : Cantor₀ → Baire
point-of (α , _) = α

\end{code}

which is clearly equivalent to the previous definition.

\begin{code}

to-baire-gives-boolean-point : (α : Cantor) → is-boolean-point (embedding-C-B α)
to-baire-gives-boolean-point α = embedding-𝟚-ℕ-gives-boolean ∘ α

\end{code}

We can prove the equivalence between `Cantor` and `Cantor₀`.

\begin{code}

to-cantor₀ : Cantor → Cantor₀
to-cantor₀ α = embedding-C-B α , to-baire-gives-boolean-point α

to-cantor : Cantor₀ → Cantor
to-cantor (α , p) = λ n → to-bool (α n) (p n)

\end{code}

\begin{code}

embedding-𝟚-ℕ-0-implies-is-₀ : (b : 𝟚) → embedding-𝟚-ℕ b ＝ 0 → b ＝ ₀
embedding-𝟚-ℕ-0-implies-is-₀ ₀ p = refl

embedding-𝟚-ℕ-1-implies-is-₁ : (b : 𝟚) → embedding-𝟚-ℕ b ＝ 1 → b ＝ ₁
embedding-𝟚-ℕ-1-implies-is-₁ ₁ p = refl

embedding-𝟚-ℕ-is-embedding : is-embedding embedding-𝟚-ℕ
embedding-𝟚-ℕ-is-embedding m (b , p) (c , q) = to-subtype-＝ † ♢
 where
  † : (b : 𝟚) → is-prop (embedding-𝟚-ℕ b ＝ m)
  † b = ℕ-is-set (embedding-𝟚-ℕ b) m

  φ : embedding-𝟚-ℕ b ＝ embedding-𝟚-ℕ c
  φ = embedding-𝟚-ℕ b ＝⟨ p ⟩ m ＝⟨ q ⁻¹ ⟩ embedding-𝟚-ℕ c ∎

  ϑ₁ : b ＝ ₀ → c ＝ ₀ → b ＝ c
  ϑ₁ p q = b ＝⟨ p ⟩ ₀ ＝⟨ q ⁻¹ ⟩ c ∎

  ϑ₂ : b ＝ ₀ → c ＝ ₁ → b ＝ c
  ϑ₂ p q = 𝟘-elim (zero-not-positive (embedding-𝟚-ℕ ₀) ϟ)
   where
    ϟ : 0 ＝ 1
    ϟ = 0               ＝⟨ refl                  ⟩
        embedding-𝟚-ℕ ₀ ＝⟨ ap embedding-𝟚-ℕ p ⁻¹ ⟩
        embedding-𝟚-ℕ b ＝⟨ φ                     ⟩
        embedding-𝟚-ℕ c ＝⟨ ap embedding-𝟚-ℕ q    ⟩
        embedding-𝟚-ℕ ₁ ＝⟨ refl                  ⟩
        1               ∎

  ϑ₃ : b ＝ ₁ → c ＝ ₀ → b ＝ c
  ϑ₃ p q = 𝟘-elim (zero-not-positive (embedding-𝟚-ℕ ₀) ϟ)
   where
    ϟ : 0 ＝ 1
    ϟ = 0                  ＝⟨ refl                 ⟩
        embedding-𝟚-ℕ ₀   ＝⟨ ap embedding-𝟚-ℕ q ⁻¹ ⟩
        embedding-𝟚-ℕ c   ＝⟨ φ ⁻¹                  ⟩
        embedding-𝟚-ℕ b   ＝⟨ ap embedding-𝟚-ℕ p    ⟩
        1                  ∎

  ϑ₄ : b ＝ ₁ → c ＝ ₁ → b ＝ c
  ϑ₄ p q = b ＝⟨ p ⟩ ₁ ＝⟨ q ⁻¹ ⟩ c ∎

  ξ : b ＝ ₀ → b ＝ c
  ξ r = cases (ϑ₁ r) (ϑ₂ r) (𝟚-possibilities c)

  ζ : b ＝ ₁ → b ＝ c
  ζ r = cases (ϑ₃ r) (ϑ₄ r) (𝟚-possibilities c)

  ♢ : b ＝ c
  ♢ = cases ξ ζ (𝟚-possibilities b)

to-cantor-cancels-to-cantor₀ : (α : Cantor) → to-cantor (to-cantor₀ α) ＝ α
to-cantor-cancels-to-cantor₀ α = dfunext fe †
 where
  † : (n : ℕ) → to-bool (embedding-𝟚-ℕ (α n)) (to-baire-gives-boolean-point α n) ＝ α n
  † n = cases †₁ †₂ (to-baire-gives-boolean-point α n)
   where
    †₁ : embedding-𝟚-ℕ (α n) ＝ 0
       → to-bool (embedding-𝟚-ℕ (α n)) (to-baire-gives-boolean-point α n) ＝ α n
    †₁ p =
     to-bool (embedding-𝟚-ℕ (α n)) (embedding-𝟚-ℕ-gives-boolean (α n)) ＝⟨ Ⅰ ⟩
     to-bool 0 (inl refl)                                            ＝⟨ Ⅱ ⟩
     α n                                                             ∎
      where
       Ⅰ = ap
            (λ - → to-bool (embedding-𝟚-ℕ -) (embedding-𝟚-ℕ-gives-boolean -))
            (embedding-𝟚-ℕ-0-implies-is-₀ (α n) p)
       Ⅱ = embedding-𝟚-ℕ-0-implies-is-₀ (α n) p ⁻¹

    †₂ : embedding-𝟚-ℕ (α n) ＝ 1
       → to-bool (embedding-𝟚-ℕ (α n)) (to-baire-gives-boolean-point α n) ＝ α n
    †₂ p =
     to-bool (embedding-𝟚-ℕ (α n)) (embedding-𝟚-ℕ-gives-boolean (α n)) ＝⟨ Ⅰ ⟩
     to-bool 1 (inr refl)                                            ＝⟨ Ⅱ ⟩
     α n                                                             ∎
      where
       Ⅰ = ap
            (λ - → to-bool (embedding-𝟚-ℕ -) (embedding-𝟚-ℕ-gives-boolean -))
            (embedding-𝟚-ℕ-1-implies-is-₁ (α n) p)
       Ⅱ = embedding-𝟚-ℕ-1-implies-is-₁ (α n) p ⁻¹

point-of-lemma : (α : Cantor)
               → point-of (to-cantor₀ α) ∼ embedding-𝟚-ℕ ∘ α
point-of-lemma α = λ _ → refl

＝⟦⟧-cantor₀-equivalence : (α β : Cantor) (t : BT ℕ)
                         → α ＝⟦ t ⟧ β
                         → point-of (to-cantor₀ α) ＝⟦ t ⟧ point-of (to-cantor₀ β)
＝⟦⟧-cantor₀-equivalence α β []      _       = []
＝⟦⟧-cantor₀-equivalence α β (n ∷ φ) (p ∷ ψ) = † ∷ γ
 where
  † : embedding-𝟚-ℕ (α n) ＝ embedding-𝟚-ℕ (β n)
  † = ap embedding-𝟚-ℕ p

  γ : (i : 𝟚) → point-of (to-cantor₀ α) ＝⟦ φ i ⟧ point-of (to-cantor₀ β)
  γ ₀ = ＝⟦⟧-cantor₀-equivalence α β (φ ₀) (ψ ₀)
  γ ₁ = ＝⟦⟧-cantor₀-equivalence α β (φ ₁) (ψ ₁)

to-bool-lemma₁ : (α : Baire) (bv : is-boolean-point α) (i : ℕ)
              → α i ＝ 0 → to-bool (α i) (bv i) ＝ ₀
to-bool-lemma₁ α bv i p = ap (to-bool (α i)) †
  where
   † : bv i ＝ inl p
   † = θ-lemma α i (bv i) (inl p)

to-bool-lemma₂ : (α : Baire) (bv : is-boolean-point α) (i : ℕ)
               → α i ＝ 1 → to-bool (α i) (bv i) ＝ ₁
to-bool-lemma₂ α bv i p = ap (to-bool (α i)) †
  where
   † : bv i ＝ inr p
   † = θ-lemma α i (bv i) (inr p)

to-cantor₀-cancels-to-cantor : to-cantor₀ ∘ to-cantor ∼ id
to-cantor₀-cancels-to-cantor (α , bv) = to-subtype-＝ being-boolean-point-is-prop †
  where
   ‡₁ : (i : ℕ) → α i ＝ 0 → embedding-C-B (to-cantor (α , bv)) i ＝ α i
   ‡₁ i p = embedding-𝟚-ℕ (to-bool (α i) (bv i)) ＝⟨ Ⅰ ⟩
            0                                    ＝⟨ p ⁻¹ ⟩
            α i                                  ∎
             where
              Ⅰ = ap embedding-𝟚-ℕ (to-bool-lemma₁ α bv i p)

   ‡₂ : (i : ℕ) → α i ＝ 1 → embedding-C-B (to-cantor (α , bv)) i ＝ α i
   ‡₂ i p = embedding-C-B (to-cantor (α , bv)) i ＝⟨ refl ⟩
            embedding-𝟚-ℕ (to-bool (α i) (bv i)) ＝⟨ Ⅰ ⟩
            embedding-𝟚-ℕ ₁                      ＝⟨ refl ⟩
            1                                    ＝⟨ p ⁻¹ ⟩
            α i                                  ∎
             where
              Ⅰ = ap embedding-𝟚-ℕ (to-bool-lemma₂ α bv i p)

   ‡ : embedding-C-B (to-cantor (α , bv)) ∼ α
   ‡ i = embedding-C-B (to-cantor (α , bv)) i ＝⟨ refl ⟩
         embedding-𝟚-ℕ (to-bool (α i) (bv i)) ＝⟨ Ⅰ    ⟩
         α i                                  ∎
          where
           Ⅰ : embedding-𝟚-ℕ (to-bool (α i) (bv i)) ＝ α i
           Ⅰ = cases (‡₁ i) (‡₂ i) (bv i)


   † : embedding-C-B (to-cantor (α , bv)) ＝ α
   † = dfunext fe ‡

cantor-equiv-cantor₀ : Cantor ≃ Cantor₀
cantor-equiv-cantor₀ = to-cantor₀ , ((to-cantor , φ) , to-cantor , ψ)
 where
  φ : to-cantor₀ ∘ to-cantor ∼ id
  φ = to-cantor₀-cancels-to-cantor

  ψ : to-cantor ∘ to-cantor₀ ∼ id
  ψ = to-cantor-cancels-to-cantor₀

\end{code}

\begin{code}

sequentialize : {X : 𝓤₀  ̇} → BT X → List X
sequentialize []      = []
sequentialize (x ∷ φ) = x ∷ sequentialize (φ ₀) ++ sequentialize (φ ₁)

maximumᵤ : BT ℕ → ℕ
maximumᵤ []      = 0
maximumᵤ (n ∷ φ) = max n (max (maximumᵤ (φ ₀)) (maximumᵤ (φ ₁)))

maximumᵤ′ : BT ℕ → ℕ
maximumᵤ′ = maximum ∘ sequentialize

maximum-maps-++-to-max-of-maximum
 : (ms ns : List ℕ)
 → maximum (ms ++ ns) ＝ max (maximum ms) (maximum ns)
maximum-maps-++-to-max-of-maximum []       ns = refl
maximum-maps-++-to-max-of-maximum (m ∷ ms) ns = †
 where
  IH : maximum (ms ++ ns) ＝ max (maximum ms) (maximum ns)
  IH = maximum-maps-++-to-max-of-maximum ms ns

  Ⅰ = ap (max m) IH
  Ⅱ = max-assoc m (maximum ms) (maximum ns) ⁻¹

  † : max m (maximum (ms ++ ns)) ＝ max (max m (maximum (ms))) (maximum ns)
  † = max m (maximum (ms ++ ns))              ＝⟨ Ⅰ ⟩
      max m (max (maximum ms) (maximum ns))   ＝⟨ Ⅱ ⟩
      max (max m (maximum ms)) (maximum ns)   ∎

maximumᵤ′-equivalent-to-maximumᵤ : (t : BT ℕ) → maximumᵤ t ＝ maximumᵤ′ t
maximumᵤ′-equivalent-to-maximumᵤ []      = refl
maximumᵤ′-equivalent-to-maximumᵤ (n ∷ φ) = †
 where
  IH₁ = maximumᵤ′-equivalent-to-maximumᵤ (φ ₀)
  IH₂ = maximumᵤ′-equivalent-to-maximumᵤ (φ ₁)

  Ⅰ = ap (λ - → max - (maximumᵤ (φ ₁))) IH₁
  Ⅱ = ap (max (maximumᵤ′ (φ ₀))) IH₂
  Ⅲ = maximum-maps-++-to-max-of-maximum
       (sequentialize (φ ₀))
       (sequentialize (φ ₁)) ⁻¹

  ‡ : max (maximumᵤ (φ ₀)) (maximumᵤ (φ ₁))
    ＝ maximum (sequentialize (φ ₀) ++ sequentialize (φ ₁))
  ‡ =
   max (maximumᵤ (φ ₀)) (maximumᵤ (φ ₁))                               ＝⟨ Ⅰ    ⟩
   max (maximumᵤ′ (φ ₀)) (maximumᵤ (φ ₁))                              ＝⟨ Ⅱ    ⟩
   max (maximumᵤ′ (φ ₀)) (maximumᵤ′ (φ ₁))                             ＝⟨ refl ⟩
   max (maximum (sequentialize (φ ₀))) (maximum (sequentialize (φ ₁))) ＝⟨ Ⅲ    ⟩
   maximum (sequentialize (φ ₀) ++ sequentialize (φ ₁))                ∎

  † : max n (max (maximumᵤ (φ ₀)) (maximumᵤ (φ ₁)))
    ＝ max n (maximum (sequentialize (φ ₀) ++ sequentialize (φ ₁)))
  † = ap (max n) ‡

\end{code}

\begin{code}

to-cantor₀-map : (Cantor → ℕ) → Cantor₀ → ℕ
to-cantor₀-map f = f ∘ to-cantor

to-cantor₀-map-equality : (f g :  Cantor → ℕ)
                        → f ∼ g → to-cantor₀-map f ∼ to-cantor₀-map g
to-cantor₀-map-equality f g ε = ε ∘ to-cantor

to-cantor₀-map-lemma : (f : Cantor → ℕ)
                     → (α β : Cantor)
                     → f α ＝ f β
                     → to-cantor₀-map f (to-cantor₀ α)
                       ＝ to-cantor₀-map f (to-cantor₀ β)
to-cantor₀-map-lemma f α β p =
 to-cantor₀-map f (to-cantor₀ α) ＝⟨ refl ⟩
 f (to-cantor (to-cantor₀ α))    ＝⟨ Ⅰ    ⟩
 f α                             ＝⟨ Ⅱ    ⟩
 f β                             ＝⟨ Ⅲ    ⟩
 f (to-cantor (to-cantor₀ β))    ＝⟨ refl ⟩
 to-cantor₀-map f (to-cantor₀ β) ∎
  where
   Ⅰ = ap f (to-cantor-cancels-to-cantor₀ α)
   Ⅱ = p
   Ⅲ = ap f (to-cantor-cancels-to-cantor₀ β) ⁻¹

to-cantor₀-map-lemma′ : (f : Cantor → ℕ)
                      → (α β : Cantor)
                      → to-cantor₀-map f (to-cantor₀ α) ＝ to-cantor₀-map f (to-cantor₀ β)
                      → f α ＝ f β
to-cantor₀-map-lemma′ f α β p = f α                          ＝⟨ Ⅰ ⟩
                                f (to-cantor (to-cantor₀ α)) ＝⟨ Ⅱ ⟩
                                f (to-cantor (to-cantor₀ β)) ＝⟨ Ⅲ ⟩
                                f β                          ∎
 where
  Ⅰ = ap f (to-cantor-cancels-to-cantor₀ α ⁻¹ )
  Ⅱ = p
  Ⅲ = ap f (to-cantor-cancels-to-cantor₀ β)

\end{code}

\begin{code}

is-uniformly-continuous₀ : (Cantor → ℕ) → 𝓤₀  ̇
is-uniformly-continuous₀ f =
 Σ n ꞉ ℕ , ((ξ₁@(α₁ , _) ξ₂@(α₂ , _) : Cantor₀) → α₁ ＝⦅ n ⦆ α₂ → f₀ ξ₁ ＝ f₀ ξ₂)
  where
   f₀ : Cantor₀ → ℕ
   f₀ = to-cantor₀-map f

\end{code}

\begin{code}

＝⟪⟫₀-implies-＝⟦⟧ : (α₁ α₂ : Baire) (t : BT ℕ)
                   → α₁ ＝⟪ sequentialize t ⟫₀ α₂ → α₁ ＝⟦ t ⟧ α₂
＝⟪⟫₀-implies-＝⟦⟧ α₁ α₂ []      p = []
＝⟪⟫₀-implies-＝⟦⟧ α₁ α₂ (x ∷ φ) p = p x in-head ∷ †
 where
  ϑ : α₁ ＝⟪ sequentialize (φ ₀) ++ sequentialize (φ ₁) ⟫₀ α₂
  ϑ = ＝⟪⟫₀-cons α₁ α₂ x (sequentialize (φ ₀) ++ sequentialize (φ ₁)) p

  ς₀ : α₁ ＝⟪ sequentialize (φ ₀) ⟫₀ α₂
  ς₀ = pr₁ (＝⟪⟫-++-lemma₁ α₁ α₂ (sequentialize (φ ₀)) (sequentialize (φ ₁)) ϑ)

  ς₁ : α₁ ＝⟪ sequentialize (φ ₁) ⟫₀ α₂
  ς₁ = pr₂ (＝⟪⟫-++-lemma₁ α₁ α₂ (sequentialize (φ ₀)) (sequentialize (φ ₁)) ϑ)

  † : (j : 𝟚) → α₁ ＝⟦ φ j ⟧ α₂
  † ₀ = ＝⟪⟫₀-implies-＝⟦⟧ α₁ α₂ (φ ₀) ς₀
  † ₁ = ＝⟪⟫₀-implies-＝⟦⟧ α₁ α₂ (φ ₁) ς₁

＝⟦⟧-implies-＝⟪⟫₀ : (α β : Baire) (t : BT ℕ)
                   → α ＝⟦ t ⟧ β → α ＝⟪ sequentialize t ⟫₀ β
＝⟦⟧-implies-＝⟪⟫₀ _ _ []      _       _ ()
＝⟦⟧-implies-＝⟪⟫₀ α β (n ∷ φ) (p ∷ _) _ in-head     = p
＝⟦⟧-implies-＝⟪⟫₀ α β (n ∷ φ) (p ∷ ψ) i (in-tail q) = † i q
 where
  ms = sequentialize (φ ₀)
  ns = sequentialize (φ ₁)

  IH₁ : α ＝⟪ ms ⟫₀ β
  IH₁ = ＝⟦⟧-implies-＝⟪⟫₀ α β (φ ₀) (ψ ₀)

  IH₂ : α ＝⟪ ns ⟫₀ β
  IH₂ = ＝⟦⟧-implies-＝⟪⟫₀ α β (φ ₁) (ψ ₁)

  † : α ＝⟪ ms ++ ns ⟫₀ β
  † = ＝⟪⟫-++-lemma₂ α β ms ns (IH₁ , IH₂)

to-bool-congruence : (m : ℕ)
                   → (n : ℕ)
                   → (𝒷₁ : is-boolean-valued m)
                   → (𝒷₂ : is-boolean-valued n)
                   → m ＝ n
                   → to-bool m 𝒷₁ ＝ to-bool n 𝒷₂
to-bool-congruence zero            zero            (inl refl) (inl refl) _ = refl
to-bool-congruence (succ zero)     (succ zero)     (inr refl) (inr refl) _ = refl
to-bool-congruence (succ (succ _)) (succ (succ _)) (inl ())   (inl _)    _
to-bool-congruence (succ (succ _)) (succ (succ _)) (inl ())   (inr _)    _
to-bool-congruence (succ (succ _)) (succ (succ _)) (inr ())   (inl _)    _
to-bool-congruence (succ (succ _)) (succ (succ _)) (inr ())   (inr _)    _

to-cantor-＝⟦⟧ : (α₁ α₂ : Baire)
              (ϑ₁ : is-boolean-point α₁) (ϑ₂ : is-boolean-point α₂)
              (t : BT ℕ)
            → α₁ ＝⟦ t ⟧ α₂
            → to-cantor (α₁ , ϑ₁) ＝⟦ t ⟧ to-cantor (α₂ , ϑ₂)
to-cantor-＝⟦⟧ α₁ α₂ ϑ₁ ϑ₂ []       _      = []
to-cantor-＝⟦⟧ α₁ α₂ ϑ₁ ϑ₂ (n ∷ φ) (p ∷ ψ) = β ∷ γ
 where
  β : to-bool (α₁ n) (ϑ₁ n) ＝ to-bool (α₂ n) (ϑ₂ n)
  β = to-bool-congruence (α₁ n) (α₂ n) (ϑ₁ n) (ϑ₂ n) p

  γ : (b : 𝟚) → to-cantor (α₁ , ϑ₁) ＝⟦ φ b ⟧ to-cantor (α₂ , ϑ₂)
  γ ₀ = to-cantor-＝⟦⟧ α₁ α₂ ϑ₁ ϑ₂ (φ ₀) (ψ ₀)
  γ ₁ = to-cantor-＝⟦⟧ α₁ α₂ ϑ₁ ϑ₂ (φ ₁) (ψ ₁)

uni-continuity-implies-uni-continuity₀ : (f : Cantor → ℕ)
                                       → is-uniformly-continuous  f
                                       → is-uniformly-continuous₀ f
uni-continuity-implies-uni-continuity₀ f 𝔠 = †
 where
  t : BT ℕ
  t = pr₁ 𝔠

  n : ℕ
  n = succ (maximumᵤ (pr₁ 𝔠))

  f₀ : Cantor₀ → ℕ
  f₀ = to-cantor₀-map f

  ‡ : (α₁ α₂ : Baire) (ϑ₁ : is-boolean-point α₁) (ϑ₂ : is-boolean-point α₂)
    → α₁ ＝⦅ n ⦆ α₂ → f₀ (α₁ , ϑ₁) ＝ f₀ (α₂ , ϑ₂)
  ‡ α₁ α₂ ϑ₁ ϑ₂ (p , q) = pr₂ 𝔠 (to-cantor (α₁ , ϑ₁)) (to-cantor (α₂ , ϑ₂)) Ͱ
   where
    ϝ : tl α₁ ＝⦅ maximumᵤ′ t ⦆ (tl α₂)
    ϝ = transport
         (λ - → tl α₁ ＝⦅ - ⦆ tl α₂)
         (maximumᵤ′-equivalent-to-maximumᵤ t)
         q

    ϟ : α₁ ＝⦅ succ (maximum (sequentialize t)) ⦆ α₂
    ϟ = p , ϝ

    ϡ : α₁ ＝⟪ sequentialize t ⟫ α₂
    ϡ = ＝⦅⦆-implies-＝⟪⟫-for-suitable-modulus α₁ α₂ (sequentialize t) ϟ

    ϸ : α₁ ＝⟪ sequentialize t ⟫₀ α₂
    ϸ = ＝⟪⟫-implies-＝⟪⟫₀ α₁ α₂ (sequentialize t) ϡ

    ϻ : α₁ ＝⟦ t ⟧ α₂
    ϻ = ＝⟪⟫₀-implies-＝⟦⟧ α₁ α₂ t ϸ

    Ͱ : to-cantor (α₁ , ϑ₁) ＝⟦ t ⟧ to-cantor (α₂ , ϑ₂)
    Ͱ = to-cantor-＝⟦⟧ α₁ α₂ ϑ₁ ϑ₂ t ϻ

  † : is-uniformly-continuous₀ f
  † = n , (λ (α₁ , ϑ₁) (α₂ , ϑ₂) → ‡ α₁ α₂ ϑ₁ ϑ₂)

\end{code}

To prove the converse direction, we define analogue of the range function.

\begin{code}

singleton : ℕ → BT ℕ
singleton n = n ∷ λ { ₀ → [] ; ₁ → [] }

pred : ℕ → ℕ
pred zero     = zero
pred (succ n) = n

rangeᵤ : (n : ℕ) → BT ℕ
rangeᵤ zero     = singleton 0
rangeᵤ (succ n) = succ n ∷ λ { ₀ → [] ; ₁ → rangeᵤ n }

＝⟦⟧-up-to-rangeᵤ-m-implies-＝⟪⟫-up-to-range-m : {X : 𝓤₀  ̇} (α α′ : ℕ → X) (m : ℕ)
                                               → α ＝⟦ rangeᵤ m ⟧ α′
                                               → α ＝⟪ range m ⟫ α′
＝⟦⟧-up-to-rangeᵤ-m-implies-＝⟪⟫-up-to-range-m α α′ zero (p ∷ _) = p ∷ []
＝⟦⟧-up-to-rangeᵤ-m-implies-＝⟪⟫-up-to-range-m α α′ (succ m) (p ∷ q) = p ∷ IH
 where
  IH : α ＝⟪ range m ⟫ α′
  IH = ＝⟦⟧-up-to-rangeᵤ-m-implies-＝⟪⟫-up-to-range-m α α′ m (q ₁)

＝⟦⟧-up-to-range-m-implies-＝⦅⦆-up-to-m : (α β : Baire) (m : ℕ)
                                        → α ＝⟦ rangeᵤ m ⟧ β
                                        → α ＝⦅ m ⦆ β
＝⟦⟧-up-to-range-m-implies-＝⦅⦆-up-to-m α β m = φ ∘ ψ
 where
  φ = ＝⟪⟫-range-implies-＝⦅⦆ α β m
  ψ = ＝⟦⟧-up-to-rangeᵤ-m-implies-＝⟪⟫-up-to-range-m α β m

＝⟦⟧-boolean-lemma : (α β : Cantor) (m : ℕ)
                   → α ＝⟦ rangeᵤ m ⟧ β
                   → embedding-C-B α ＝⟦ rangeᵤ m ⟧ embedding-C-B β
＝⟦⟧-boolean-lemma α β zero (p ∷ _) = ap embedding-𝟚-ℕ p ∷ (λ { ₀ → [] ; ₁ → [] })
＝⟦⟧-boolean-lemma α β (succ m) (p ∷ φ) =
 ap embedding-𝟚-ℕ p ∷ λ { ₀ → [] ; ₁ → ＝⟦⟧-boolean-lemma α β m (φ ₁) }

uni-continuity₀-implies-uni-continuity : (f : Cantor → ℕ)
                                       → is-uniformly-continuous₀ f
                                       → is-uniformly-continuous f
uni-continuity₀-implies-uni-continuity f ζ = rangeᵤ m , †
 where
  m : ℕ
  m = pr₁ ζ

  f₀ : Cantor₀ → ℕ
  f₀ = to-cantor₀-map f

  ‡ : (α β : Baire) (𝒷₁ : is-boolean-point α) (𝒷₂ : is-boolean-point β)
    → α ＝⟦ rangeᵤ m ⟧ β → f₀ (α , 𝒷₁) ＝ f₀ (β , 𝒷₂)
  ‡ α β 𝒷₁ 𝒷₂ ϑ =
   pr₂ ζ (α , 𝒷₁) (β , 𝒷₂) (＝⟦⟧-up-to-range-m-implies-＝⦅⦆-up-to-m α β m ϑ)

  † : (α β : Cantor) → α ＝⟦ rangeᵤ m ⟧ β → f α ＝ f β
  † α β p = to-cantor₀-map-lemma′ f α β (‡ α′ β′ 𝒷₁ 𝒷₂ p′)
   where
    α′ : Baire
    α′ = embedding-C-B α

    𝒷₁ : (n : ℕ) → is-boolean-valued (α′ n)
    𝒷₁ = to-baire-gives-boolean-point α

    β′ : Baire
    β′ = embedding-C-B β

    𝒷₂ : (n : ℕ) → is-boolean-valued (β′ n)
    𝒷₂ = to-baire-gives-boolean-point β

    p′ : α′ ＝⟦ rangeᵤ m ⟧ β′
    p′ = ＝⟦⟧-boolean-lemma α β m p

\end{code}

\begin{code}

uni-continuity-equivalent-to-uni-continuity : (f : Cantor → ℕ)
                                            → is-uniformly-continuous₀ f
                                              ⇔ is-uniformly-continuous f
uni-continuity-equivalent-to-uni-continuity f = ⦅⇒⦆ , ⦅⇐⦆
 where
  ⦅⇒⦆ = uni-continuity₀-implies-uni-continuity f
  ⦅⇐⦆ = uni-continuity-implies-uni-continuity₀ f

\end{code}
