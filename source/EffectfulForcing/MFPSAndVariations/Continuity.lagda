Martin Escardo 2012

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.MFPSAndVariations.Continuity where

open import MLTT.Spartan
open import MLTT.Athenian
open import Naturals.Order

Baire : 𝓤₀ ̇
Baire = ℕ → ℕ

data _＝⟪_⟫_ {X : 𝓤₀ ̇ } : (ℕ → X) → List ℕ → (ℕ → X) → 𝓤₀ ̇  where
 []  : {α α' : ℕ → X} → α ＝⟪ [] ⟫ α'
 _∷_ : {α α' : ℕ → X} {i : ℕ} {s : List ℕ}
     → α i ＝ α' i
     → α ＝⟪ s ⟫ α'
     → α ＝⟪ i ∷ s ⟫ α'

infix 0 _＝⟪_⟫_
infixr 3 _∷_

is-continuous : (Baire → ℕ) → 𝓤₀ ̇
is-continuous f = ∀ α → Σ s ꞉ List ℕ , (∀ α' → α ＝⟪ s ⟫ α' → f α ＝ f α')

continuity-extensional : (f g : Baire → ℕ)
                       → (f ∼ g)
                       → is-continuous f
                       → is-continuous g
continuity-extensional f g t c α = (pr₁ (c α) ,
                                    (λ α' r → g α  ＝⟨ (t α)⁻¹ ⟩
                                              f α  ＝⟨ pr₂(c α) α' r ⟩
                                              f α' ＝⟨ t α' ⟩
                                              g α' ∎))

Cantor : 𝓤₀ ̇
Cantor = ℕ → 𝟚

data BT (X : 𝓤₀ ̇ ) : 𝓤₀ ̇  where
  []   : BT X
  _∷_ : X → (𝟚 → BT X) → BT X

data _＝⟦_⟧_ {X : 𝓤₀ ̇ } : (ℕ → X) → BT ℕ → (ℕ → X) → 𝓤₀ ̇  where
  []  : {α α' : ℕ → X} → α ＝⟦ [] ⟧ α'
  _∷_ : {α α' : ℕ → X}{i : ℕ}{s : 𝟚 → BT ℕ}
      → α i ＝ α' i
      → ((j : 𝟚) → α ＝⟦ s j ⟧ α')
      → α ＝⟦ i ∷ s ⟧ α'

is-uniformly-continuous : (Cantor → ℕ) → 𝓤₀ ̇
is-uniformly-continuous f = Σ s ꞉ BT ℕ , (∀ α α' → α ＝⟦ s ⟧ α' → f α ＝ f α')

UC-extensional : (f g : Cantor → ℕ)
               → (f ∼ g)
               → is-uniformly-continuous f
               → is-uniformly-continuous g
UC-extensional f g t (u , c) = (u ,
                                (λ α α' r → g α  ＝⟨ (t α)⁻¹ ⟩
                                            f α  ＝⟨ c α α' r ⟩
                                            f α' ＝⟨ t α' ⟩
                                            g α' ∎))
embedding-𝟚-ℕ : 𝟚 → ℕ
embedding-𝟚-ℕ ₀ = 0
embedding-𝟚-ℕ ₁ = 1

embedding-C-B : Cantor → Baire
embedding-C-B = embedding-𝟚-ℕ ∘_

C-restriction : (Baire → ℕ) → (Cantor → ℕ)
C-restriction = _∘ embedding-C-B

\end{code}

TODO. Formulate the usual notions of (uniform) continuity and prove
that they are logically equivalent to the above.

TODO completed below by Ayberk Tosun on 13/06/2023.

We first formulate the `α ＝⦅ n ⦆ β` relation that expresses that two sequences
`α`, `β` of natural numbers are equal up to (not inclusive) some bound `n`.
These have been adapted from the `CantorSearch` module authored by Martín
Escardó (including the proofs `agreement→` and `agreement←`).

\begin{code}

hd : Baire → ℕ
hd α = α 0

tl : Baire → Baire
tl α = α ∘ succ

_＝⦅_⦆_ : Baire → ℕ → Baire → 𝓤₀  ̇
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

Using the `_＝⦅_⦆_` relation, we express the “usual” notion of continuity
mentioned in the TODO. We call this `is-continuous₀` and prove at the end of
the module that it is logically equivalent to `is-continuous`.

\begin{code}

is-continuous₀ : (Baire → ℕ) → 𝓤₀  ̇
is-continuous₀ f =
 (α : Baire) → Σ n ꞉ ℕ , ((α′ : Baire) → α ＝⦅ n ⦆ α′ → f α ＝ f α′)

\end{code}

We now formulate an alternative non-inductive version of the `_＝⟪_⟫_` relation
that we call `_＝⟪_⟫₀_` and prove its logical equivalence with `_＝⟪_⟫_`. The
motivation for the non-inductive formulation is that it simplifies the proof a
bit.

\begin{code}

_＝⟪_⟫₀_ : Baire → List ℕ → Baire → 𝓤₀  ̇
_＝⟪_⟫₀_ α s α′ = (i : ℕ) → member i s → α i ＝ α′ i

＝⟪⟫₀-cons : (α α′ : Baire) (i : ℕ) (is : List ℕ)
           → α ＝⟪ i ∷ is ⟫₀ α′ → α ＝⟪ is ⟫₀ α′
＝⟪⟫₀-cons α α′ i is t j p = t j (in-tail p)

\end{code}

\begin{code}

＝⟪⟫₀-implies-＝⟪⟫ : (α α′ : Baire) (s : List ℕ)
                   → α ＝⟪ s ⟫₀ α′
                   → α ＝⟪ s ⟫  α′
＝⟪⟫₀-implies-＝⟪⟫ α α′ []       t = []
＝⟪⟫₀-implies-＝⟪⟫ α α′ (i ∷ is) t =
 (t i in-head) ∷ (＝⟪⟫₀-implies-＝⟪⟫ α α′ is (＝⟪⟫₀-cons α α′ i is t))

＝⟪⟫-implies-＝⟪⟫₀ : (α α′ : Baire) (s : List ℕ) → α ＝⟪ s ⟫ α′ → α ＝⟪ s ⟫₀ α′
＝⟪⟫-implies-＝⟪⟫₀ α α′ []       []       i ()
＝⟪⟫-implies-＝⟪⟫₀ α α′ (i ∷ is) (p ∷ ps) i in-head     = p
＝⟪⟫-implies-＝⟪⟫₀ α α′ (_ ∷ is) (p ∷ ps) j (in-tail q) =
 ＝⟪⟫-implies-＝⟪⟫₀ α α′ is ps j q

\end{code}

We define the `maximum` function computing the maximum of a given list of
natural numbers.

\begin{code}

maximum : List ℕ → ℕ
maximum = foldr max 0

\end{code}

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

We now address the other direction.

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

We also define the following operation `modulus-at₀` that projects out the
modulus of continuity computed by a proof of `is-continuous₀`:

\begin{code}

modulus-at₀ : (f : Baire → ℕ) → is-continuous₀ f → Baire → ℕ
modulus-at₀ f c α = pr₁ (c α)

\end{code}
