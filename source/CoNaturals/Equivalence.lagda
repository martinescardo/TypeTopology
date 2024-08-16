Martin Escardo, November 2023.

We show that the two types ℕ∞ and ℕ∞' of conatural numbers are
equivalent.

For that purpose, we develop an automorphism of the Cantor type ℕ → 𝟚
that restricts restricts to an equivalence between ℕ∞ and the subtype

     ℕ∞ := Σ α ꞉ (ℕ → 𝟚) , is-prop (Σ n ꞉ ℕ , α n ＝ ₁)

of the Cantor type (of binary sequences with at most one ₁).

Notice that the condition on α can be expressed as "is-prop (fiber α ₁)".

\begin{code}

{-# OPTIONS --safe --without-K #-}

module CoNaturals.Equivalence where

open import CoNaturals.GenericConvergentSequence
open import CoNaturals.GenericConvergentSequence2
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Order
open import Naturals.Properties
open import Notation.CanonicalMap
open import Notation.Order
open import TypeTopology.Cantor
open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

private
 T = T-cantor

private
 instance
  Canonical-Map-ℕ-ℕ∞' : Canonical-Map ℕ ℕ∞'
  ι {{Canonical-Map-ℕ-ℕ∞'}} = ℕ-to-ℕ∞'

\end{code}

To show that ℕ∞' gives an equivalent copy of ℕ∞, we consider a
particular equivalence (ℕ → 𝟚) ≃ (ℕ → 𝟚).

\begin{code}

ϕ-cantor γ-cantor : (ℕ → 𝟚) → (ℕ → 𝟚)

ϕ-cantor α n = cons ₁ α n ⊕ α n

γ-cantor β 0        = complement (β 0)
γ-cantor β (succ n) = γ-cantor β n ⊕ β (succ n)

private
 ϕ γ : (ℕ → 𝟚) → (ℕ → 𝟚)
 ϕ = ϕ-cantor
 γ = γ-cantor

η-cantor : (β : ℕ → 𝟚) → ϕ (γ β) ∼ β
η-cantor β 0        = complement-involutive (β 0)
η-cantor β (succ n) = ⊕-involutive {γ β n} {β (succ n)}

ε-cantor : (α : ℕ → 𝟚) → γ (ϕ α) ∼ α
ε-cantor α 0        = complement-involutive (α 0)
ε-cantor α (succ n) = γ (ϕ α) (succ n)             ＝⟨ refl ⟩
                      γ (ϕ α) n ⊕ α n ⊕ α (succ n) ＝⟨ I ⟩
                      α n ⊕ α n ⊕ α (succ n)       ＝⟨ II ⟩
                      α (succ n)                   ∎
 where
  I  = ap (_⊕ α n ⊕ α (succ n)) (ε-cantor α n)
  II = ⊕-involutive {α n} {α (succ n)}

private
 η : (β : ℕ → 𝟚) → ϕ (γ β) ∼ β
 ε : (α : ℕ → 𝟚) → γ (ϕ α) ∼ α

 η = η-cantor
 ε = ε-cantor

\end{code}

We now discuss the restrictions of ϕ and γ mentioned above. Notice
that the following is by four cases without induction.

\begin{code}

ϕ-property : funext₀
           → (α : ℕ → 𝟚)
           → is-decreasing α
           → has-at-most-one-₁ (ϕ α)
ϕ-property fe α δ (0 , p) (0 ,      q) = to-T-＝ refl
ϕ-property fe α δ (0 , p) (succ m , q) = 𝟘-elim (Zero-not-Succ (II ⁻¹ ∙ IV))
 where
  u : ℕ∞
  u = (α , δ)

  I = α 0                           ＝⟨ (complement-involutive (α 0))⁻¹ ⟩
      complement (complement (α 0)) ＝⟨ ap complement p ⟩
      complement ₁                  ＝⟨ refl ⟩
      ₀                             ∎

  II : u ＝ Zero
  II = is-Zero-equal-Zero fe I

  III : (α m ＝ ₁) × (α (succ m) ＝ ₀)
  III = ⊕-property₁ {α m} {α (succ m)} (δ m) q

  IV : u ＝ Succ (ι m)
  IV = uncurry (Succ-criterion fe) III

ϕ-property fe α δ (succ n , p) (0 , q)= 𝟘-elim (Zero-not-Succ (II ⁻¹ ∙ IV))
 where
  u : ℕ∞
  u = (α , δ)

  I = α 0                           ＝⟨ (complement-involutive (α 0))⁻¹ ⟩
      complement (complement (α 0)) ＝⟨ ap complement q ⟩
      complement ₁                  ＝⟨ refl ⟩
      ₀                             ∎

  II : u ＝ Zero
  II = is-Zero-equal-Zero fe I

  III : (α n ＝ ₁) × (α (succ n) ＝ ₀)
  III = ⊕-property₁ {α n} {α (succ n)} (δ n) p

  IV : u ＝ Succ (ι n)
  IV = uncurry (Succ-criterion fe) III

ϕ-property fe α δ (succ n , p) (succ m , q) = VI
 where
  u : ℕ∞
  u = (α , δ)

  I : (α n ＝ ₁) × (α (succ n) ＝ ₀)
  I = ⊕-property₁ (δ n) p

  II : (α m ＝ ₁) × (α (succ m) ＝ ₀)
  II = ⊕-property₁ (δ m) q

  III : u ＝ Succ (ι n)
  III = uncurry (Succ-criterion fe) I

  IV : u ＝ Succ (ι m)
  IV = uncurry (Succ-criterion fe) II

  V : succ n ＝ succ m
  V = ℕ-to-ℕ∞-lc (III ⁻¹ ∙ IV)

  VI : (succ n , p) ＝ (succ m , q)
  VI = to-T-＝ V

\end{code}

The following two observations give an alternative understanding of
the definition of γ:

\begin{code}

γ-case₀ : {β : ℕ → 𝟚} {n : ℕ}
        → β (succ n) ＝ ₀ → γ β (succ n) ＝ γ β n
γ-case₀ = ⊕-₀-right-neutral'

γ-case₁ : {β : ℕ → 𝟚} {n : ℕ}
        → β (succ n) ＝ ₁ → γ β (succ n) ＝ complement (γ β n)
γ-case₁ = ⊕-left-complement

\end{code}

We need the following consequences of the sequence β having at most
one ₁.

\begin{code}

at-most-one-₁-Lemma₀ : (β : ℕ → 𝟚)
                     → has-at-most-one-₁ β
                     → {m n : ℕ} → (β m ＝ ₁) × (β n ＝ ₁) → m ＝ n
at-most-one-₁-Lemma₀ β π {m} {n} (p , q) = ap pr₁ (π (m , p) (n , q))

at-most-one-₁-Lemma₁ : (β : ℕ → 𝟚)
                     → has-at-most-one-₁ β
                     → {m n : ℕ} → m ≠ n → β m ＝ ₁ → β n ＝ ₀
at-most-one-₁-Lemma₁ β π {m} {n} ν p = II
 where
  I : β n ≠ ₁
  I q = ν (at-most-one-₁-Lemma₀ β π (p , q))

  II : β n ＝ ₀
  II = different-from-₁-equal-₀ I

\end{code}

The main lemma about γ is the following, where we are interested in
the choice k = n, but we need to prove the lemma for general k to get
a suitable induction hypothesis.

\begin{code}

γ-lemma : (β : ℕ → 𝟚)
        → has-at-most-one-₁ β
        → (n : ℕ) → β (succ n) ＝ ₁ → (k : ℕ) → k ≤ n → γ β k ＝ ₁
γ-lemma β π n p 0 l = w
 where
  w : complement (β 0) ＝ ₁
  w = complement-intro₀ (at-most-one-₁-Lemma₁ β π (positive-not-zero n) p)

γ-lemma β π 0 p (succ k) ()
γ-lemma β π (succ n) p (succ k) l = w
 where
  IH : γ β k ＝ ₁
  IH = γ-lemma β π (succ n) p k (≤-trans k n (succ n) l (≤-succ n))

  I : succ (succ n) ≠ succ k
  I m = not-less-than-itself n r
   where
    q : succ n ＝ k
    q = succ-lc m

    r : succ n ≤ n
    r = transport⁻¹ (_≤ n) q l

  II : β (succ k) ＝ ₀
  II = at-most-one-₁-Lemma₁ β π I p

  w : γ β k ⊕ β (succ k) ＝ ₁
  w =  ⊕-intro₁₀ IH II

\end{code}

With this it is almost immediate that γ produces a decreasing
sequence if it is given a sequence with at most one ₁:

\begin{code}

γ-property : (β : ℕ → 𝟚)
           → has-at-most-one-₁ β
           → is-decreasing (γ β)
γ-property β π n = IV
 where
  I : β (succ n) ＝ ₁ → γ β n ＝ ₁
  I p = γ-lemma β π n p n (≤-refl n)

  II : β (succ n) ≤ γ β n
  II = ≤₂-criterion I

  III : γ β n ⊕ β (succ n) ≤ γ β n
  III = ≤₂-add-left (γ β n) (β (succ n)) II

  IV : γ β (succ n) ≤ γ β n
  IV = III

module ℕ∞-equivalence (fe : funext₀) where

 ℕ∞-to-ℕ∞' : ℕ∞ → ℕ∞'
 ℕ∞-to-ℕ∞' (α , δ) = ϕ α , ϕ-property fe α δ

 ℕ∞'-to-ℕ∞ : ℕ∞' → ℕ∞
 ℕ∞'-to-ℕ∞ (β , π) = γ β , γ-property β π

 ℕ∞-η : ℕ∞'-to-ℕ∞ ∘ ℕ∞-to-ℕ∞' ∼ id
 ℕ∞-η (α , δ) = to-subtype-＝
                 (being-decreasing-is-prop fe)
                 (dfunext fe (ε α))

 ℕ∞-ε : ℕ∞-to-ℕ∞' ∘ ℕ∞'-to-ℕ∞ ∼ id
 ℕ∞-ε (β , π) = to-subtype-＝
                 (λ β → being-prop-is-prop fe)
                 (dfunext fe (η β))

\end{code}

And with this we get the promised equivalence.

\begin{code}

 ℕ∞-to-ℕ∞'-≃ : ℕ∞ ≃ ℕ∞'
 ℕ∞-to-ℕ∞'-≃ = qinveq ℕ∞-to-ℕ∞' (ℕ∞'-to-ℕ∞ , ℕ∞-η , ℕ∞-ε)

\end{code}
