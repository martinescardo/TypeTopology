Martin Escardo 2012

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module EffectfulForcing.MFPSAndVariations.Continuity where

open import MLTT.Spartan
open import MLTT.Athenian
open import Naturals.Order
open import UF.Retracts
open import UF.Equiv

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

\section{Uniform continuity}

We start by defining the notion of being Boolean: a point `α : Baire` of the
Baire space is called Boolean if its range is a subset of `{0, 1}`.

\begin{code}

is-boolean : ℕ → 𝓤₀  ̇
is-boolean n = (n ＝ 0) + (n ＝ 1)

to-nat : 𝟚 → ℕ
to-nat = 𝟚-cases 0 1

to-nat-gives-boolean : (b : 𝟚) → is-boolean (to-nat b)
to-nat-gives-boolean ₀ = inl refl
to-nat-gives-boolean ₁ = inr refl

to-bool : (n : ℕ) → is-boolean n → 𝟚
to-bool 0 (inl refl) = ₀
to-bool 1 (inr refl) = ₁

is-boolean-point : Baire → 𝓤₀  ̇
is-boolean-point α = (n : ℕ) → is-boolean (α n)

\end{code}

Using this, we could give an alternative definition of the Cantor space.

\begin{code}

Cantor₀ : 𝓤₀  ̇
Cantor₀ = Σ α ꞉ Baire , is-boolean-point α

\end{code}

Which is clearly equivalent to the previous definition.

\begin{code}

to-baire : Cantor → Baire
to-baire α = to-nat ∘ α

to-baire-gives-boolean-point : (α : Cantor) → is-boolean-point (to-baire α)
to-baire-gives-boolean-point α = to-nat-gives-boolean ∘ α

to-cantor₀ : Cantor → Cantor₀
to-cantor₀ α = to-baire α , to-baire-gives-boolean-point α

to-cantor : Cantor₀ → Cantor
to-cantor (α , p) = λ n → to-bool (α n) (p n)

to-nat-0-implies-is-₀ : (b : 𝟚) → to-nat b ＝ 0 → b ＝ ₀
to-nat-0-implies-is-₀ ₀ p = refl

to-nat-1-implies-is-₁ : (b : 𝟚) → to-nat b ＝ 1 → b ＝ ₁
to-nat-1-implies-is-₁ ₁ p = refl

to-cantor-cancels-to-cantor₀ : (α : Cantor) → to-cantor (to-cantor₀ α) ∼ α
to-cantor-cancels-to-cantor₀ α = †
 where
  † : (n : ℕ) → to-bool (to-nat (α n)) (to-baire-gives-boolean-point α n) ＝ α n
  † n = cases †₁ †₂ (to-baire-gives-boolean-point α n)
   where
    †₁ : to-nat (α n) ＝ 0
       → to-bool (to-nat (α n)) (to-baire-gives-boolean-point α n) ＝ α n
    †₁ p = to-bool (to-nat (α n)) (to-nat-gives-boolean (α n)) ＝⟨ Ⅰ ⟩
           to-bool 0 (inl refl)                                ＝⟨ Ⅱ ⟩
           α n                                                 ∎
            where
             Ⅰ = ap
                  (λ - → to-bool (to-nat -) (to-nat-gives-boolean -))
                  (to-nat-0-implies-is-₀ (α n) p)
             Ⅱ = to-nat-0-implies-is-₀ (α n) p ⁻¹

    †₂ : to-nat (α n) ＝ 1
       → to-bool (to-nat (α n)) (to-baire-gives-boolean-point α n) ＝ α n
    †₂ p = to-bool (to-nat (α n)) (to-nat-gives-boolean (α n)) ＝⟨ Ⅰ ⟩
           to-bool 1 (inr refl)                                ＝⟨ Ⅱ ⟩
           α n                                                 ∎
            where
             Ⅰ = ap
                  (λ - → to-bool (to-nat -) (to-nat-gives-boolean -))
                  (to-nat-1-implies-is-₁ (α n) p)
             Ⅱ = to-nat-1-implies-is-₁ (α n) p ⁻¹

\end{code}

\begin{code}

maximumᵤ : BT ℕ → ℕ
maximumᵤ []      = 0
maximumᵤ (n ∷ φ) = max n (max (maximumᵤ (φ ₀)) (maximumᵤ (φ ₁)))

\end{code}

\begin{code}

to-cantor₀-map : (Cantor → ℕ) → Cantor₀ → ℕ
to-cantor₀-map f = f ∘ to-cantor

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

  fb : (α : Baire) → is-boolean-point α → ℕ
  fb α ϑ = f₀ (α , ϑ)

  ‡ : (α₁ α₂ : Baire) (ϑ₁ : is-boolean-point α₁) (ϑ₂ : is-boolean-point α₂)
    → α₁ ＝⦅ n ⦆ α₂ → f₀ (α₁ , ϑ₁) ＝ f₀ (α₂ , ϑ₂)
  ‡ α₁ α₂ ϑ₁ ϑ₂ p = pr₂ 𝔠 α₁′ α₂′ {!!}
    where
     tmp : {!!}
     tmp = ＝⦅⦆-implies-＝⟪⟫-for-suitable-modulus α₁ α₂ {!t!} p

     α₁′ : Cantor
     α₁′ = to-cantor (α₁ , ϑ₁)

     α₂′ : Cantor
     α₂′ = to-cantor (α₂ , ϑ₂)

  † : is-uniformly-continuous₀ f
  † = n , λ (α₁ , ϑ₁) (α₂ , ϑ₂) → ‡ α₁ α₂ ϑ₁ ϑ₂

\end{code}
