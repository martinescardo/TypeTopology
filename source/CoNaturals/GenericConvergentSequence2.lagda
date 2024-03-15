Martin Escardo, 14th January 2022, with major additions in November
2023 and a few additions later.


We develop an automorphism of the Cantor type ℕ → 𝟚 which
induces an equivalent copy ℕ∞' of ℕ∞.

The function ϕ restricts to an equivalence between ℕ∞ and the subtype

     Σ α ꞉ (ℕ → 𝟚) , is-prop (Σ n ꞉ ℕ , α n ＝ ₁)

of the Cantor type (the sequences with at most one ₁).

Notice that the condition on α can be expressed as "is-prop (fiber α ₁)".

\begin{code}

{-# OPTIONS --safe --without-K #-}

module CoNaturals.GenericConvergentSequence2 where

open import CoNaturals.GenericConvergentSequence
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Order hiding (max)
open import Naturals.Properties
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.FunExt
open import UF.NotNotStablePropositions
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

T-cantor : (ℕ → 𝟚) → 𝓤₀ ̇
T-cantor α = Σ n ꞉ ℕ , α n ＝ ₁

private
 T = T-cantor

has-at-most-one-₁ : (ℕ → 𝟚) → 𝓤₀ ̇
has-at-most-one-₁ α = is-prop (T α)

has-at-most-one-₁-is-prop : funext₀ → (α : ℕ → 𝟚) → is-prop (has-at-most-one-₁ α)
has-at-most-one-₁-is-prop fe α = being-prop-is-prop fe

ℕ∞' : 𝓤₀ ̇
ℕ∞' = Σ α ꞉ (ℕ → 𝟚) , has-at-most-one-₁ α

ℕ∞'-to-ℕ→𝟚 : ℕ∞' → (ℕ → 𝟚)
ℕ∞'-to-ℕ→𝟚 = pr₁

ℕ∞'-to-ℕ→𝟚-lc : funext₀ → left-cancellable ℕ∞'-to-ℕ→𝟚
ℕ∞'-to-ℕ→𝟚-lc fe = pr₁-lc (being-prop-is-prop fe)

ℕ∞'-is-¬¬-separated : funext₀ → is-¬¬-separated ℕ∞'
ℕ∞'-is-¬¬-separated fe = subtype-is-¬¬-separated
                         pr₁
                         (ℕ∞'-to-ℕ→𝟚-lc fe)
                         (Cantor-is-¬¬-separated fe)

ℕ∞'-is-set : funext₀ → is-set ℕ∞'
ℕ∞'-is-set fe = ¬¬-separated-types-are-sets fe (ℕ∞'-is-¬¬-separated fe)

private
 ¬T : (ℕ → 𝟚) → 𝓤₀ ̇
 ¬T α = (n : ℕ) → α n ＝ ₀

not-T-gives-¬T : {α : ℕ → 𝟚} → ¬ (T α) → ¬T α
not-T-gives-¬T {α} ϕ n = different-from-₁-equal-₀ (λ (e : α n ＝ ₁) → ϕ (n , e))

¬T-gives-not-T : {α : ℕ → 𝟚} → ¬T α → ¬ (T α)
¬T-gives-not-T {α} ψ (n , e) = zero-is-not-one ((ψ n)⁻¹ ∙ e)

to-T-＝ : {α : ℕ → 𝟚}
          {n n' : ℕ}
        → n ＝ n'
        → {e : α n ＝ ₁} {e' : α n' ＝ ₁}
        → (n , e) ＝[ T α ] (n' , e')
to-T-＝ p = to-subtype-＝ (λ - → 𝟚-is-set) p

from-T-＝ : {α : ℕ → 𝟚}
          {n n' : ℕ}
        → {e : α n ＝ ₁} {e' : α n' ＝ ₁}
        → (n , e) ＝[ T α ] (n' , e')
        → n ＝ n'
from-T-＝ p = ap pr₁ p

index-uniqueness : (α : ℕ → 𝟚)
                 → is-prop (T α)
                 → {n n' : ℕ} → α n ＝ ₁ → α n' ＝ ₁ → n ＝ n'
index-uniqueness α i {n} {n'} e e' = from-T-＝ (i (n , e) (n' , e'))

index-uniqueness-converse : (α : ℕ → 𝟚)
                          → ({n n' : ℕ} → α n ＝ ₁ → α n' ＝ ₁ → n ＝ n')
                          → is-prop (T α)
index-uniqueness-converse α ϕ (n , e) (n' , e') = to-T-＝ (ϕ e e')

private
 instance
  canonical-map-ℕ∞'-ℕ→𝟚 : Canonical-Map ℕ∞' (ℕ → 𝟚)
  ι {{canonical-map-ℕ∞'-ℕ→𝟚}} = ℕ∞'-to-ℕ→𝟚

ℕ∞'-to-ℕ→𝟚-at-most-one-₁ : (u : ℕ∞') → is-prop (T (ℕ∞'-to-ℕ→𝟚 u))
ℕ∞'-to-ℕ→𝟚-at-most-one-₁ = pr₂

ℕ∞'-index-uniqueness : (u : ℕ∞')
                     → {n n' : ℕ} → ι u n ＝ ₁ → ι u n' ＝ ₁ → n ＝ n'
ℕ∞'-index-uniqueness (α , i) = index-uniqueness α i

Zero' : ℕ∞'
Zero' = α , h
 where
  α : ℕ → 𝟚
  α 0        = ₁
  α (succ n) = ₀

  i : is-prop (T α)
  i (0 , e) (0 , e') = to-T-＝ refl

  h : has-at-most-one-₁ α
  h (n , e) (n' , e') = to-T-＝ (index-uniqueness α i e e')

Succ' : ℕ∞' → ℕ∞'
Succ' (α , h) = cons ₀ α , h'
 where
  h' : has-at-most-one-₁ (cons ₀ α)
  h' (succ n , e) (succ n' , e') = to-T-＝ (ap succ (index-uniqueness α h e e'))

ℕ-to-ℕ∞' : ℕ → ℕ∞'
ℕ-to-ℕ∞' 0        = Zero'
ℕ-to-ℕ∞' (succ n) = Succ' (ℕ-to-ℕ∞' n)

private
 instance
  Canonical-Map-ℕ-ℕ∞' : Canonical-Map ℕ ℕ∞'
  ι {{Canonical-Map-ℕ-ℕ∞'}} = ℕ-to-ℕ∞'

is-finite' : ℕ∞' → 𝓤₀ ̇
is-finite' u@(α , a) = T α

being-finite'-is-prop : funext₀ → (u : ℕ∞') → is-prop (is-finite' u)
being-finite'-is-prop fe₀ u@(α , a) = a

size' : {u : ℕ∞'} → is-finite' u → ℕ
size' (n , e) = n

size'-property : {u : ℕ∞'} (φ : is-finite' u) → ℕ∞'-to-ℕ→𝟚 u (size' {u} φ) ＝ ₁
size'-property (n , e) = e

Zero'-is-finite : is-finite' Zero'
Zero'-is-finite = 0 , refl

is-finite'-up : (u : ℕ∞')
              → is-finite' u
              → is-finite' (Succ' u)
is-finite'-up _ (n , e) = succ n , e

is-finite'-down : (u : ℕ∞')
                → is-finite' (Succ' u)
                → is-finite' u
is-finite'-down _ (succ n , e) = n , e

ℕ-to-ℕ∞'-is-finite' : (n : ℕ) → is-finite' (ι n)
ℕ-to-ℕ∞'-is-finite' 0        = Zero'-is-finite
ℕ-to-ℕ∞'-is-finite' (succ n) = is-finite'-up (ι n)
                                (ℕ-to-ℕ∞'-is-finite' n)

∞' : ℕ∞'
∞' = (λ _ → ₀) , (λ (n , e) (n' , e') → 𝟘-elim (zero-is-not-one e))

not-finite'-is-∞' : funext₀ → (u : ℕ∞') → ¬ is-finite' u → u ＝ ∞'
not-finite'-is-∞' fe u ν = ℕ∞'-to-ℕ→𝟚-lc fe
                            (dfunext fe
                              (λ i → different-from-₁-equal-₀
                                      (λ (e : ℕ∞'-to-ℕ→𝟚 u i ＝ ₁) → ν (i , e))))

not-T-is-∞' : funext₀ → (u : ℕ∞') → ¬ T (ι u) → u ＝ ∞'
not-T-is-∞' fe u ν = ℕ∞'-to-ℕ→𝟚-lc fe (dfunext fe (not-T-gives-¬T ν))

is-infinite-∞' : ¬ is-finite' ∞'
is-infinite-∞' (n , e) = zero-is-not-one e

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

module _ (fe : funext₀) where

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

 private
  trivial-fact : (i : ℕ) → ϕ (ℕ∞-to-ℕ→𝟚 ∞) i ＝ ₀
  trivial-fact 0        = refl
  trivial-fact (succ i) = refl

 Zero-preservation : ℕ∞-to-ℕ∞' Zero ＝ Zero'
 Zero-preservation = to-subtype-＝ (has-at-most-one-₁-is-prop fe) (dfunext fe I)
  where
   I : ϕ (ι Zero) ∼ ι Zero'
   I 0        = refl
   I (succ i) = trivial-fact 0

 Succ-preservation : (u : ℕ∞) → ℕ∞-to-ℕ∞' (Succ u) ＝ Succ' (ℕ∞-to-ℕ∞' u)
 Succ-preservation u@(α , d) = to-subtype-＝ (has-at-most-one-₁-is-prop fe) II
  where
   I : ϕ (ℕ∞-to-ℕ→𝟚 (Succ u)) ∼ cons ₀ (ι (ℕ∞-to-ℕ∞' u))
   I 0        = refl
   I (succ _) = refl

   II : ϕ (ℕ∞-to-ℕ→𝟚 (Succ u)) ＝ cons ₀ (ι (ℕ∞-to-ℕ∞' u))
   II = dfunext fe I

 ∞-preservation : ℕ∞-to-ℕ∞' ∞ ＝ ∞'
 ∞-preservation = to-subtype-＝ (has-at-most-one-₁-is-prop fe)
                   (dfunext fe trivial-fact)

 ∞-gives-∞' : (u : ℕ∞') → ℕ∞'-to-ℕ∞ u ＝ ∞ → u ＝ ∞'
 ∞-gives-∞' u e =
  u                       ＝⟨ II₀ ⟩
  ℕ∞-to-ℕ∞' (ℕ∞'-to-ℕ∞ u) ＝⟨ II₁ ⟩
  ℕ∞-to-ℕ∞' ∞             ＝⟨ II₂ ⟩
  ∞'                      ∎
  where
   II₀ = (inverses-are-sections' ℕ∞-to-ℕ∞'-≃ u)⁻¹
   II₁ = ap ℕ∞-to-ℕ∞' e
   II₂ = ∞-preservation

 ∞'-gives-∞ : (u : ℕ∞) → ℕ∞-to-ℕ∞' u ＝ ∞' → u ＝ ∞
 ∞'-gives-∞ u e =
  u                       ＝⟨ (inverses-are-retractions' ℕ∞-to-ℕ∞'-≃ u)⁻¹ ⟩
  ℕ∞'-to-ℕ∞ (ℕ∞-to-ℕ∞' u) ＝⟨ ap ℕ∞'-to-ℕ∞ e ⟩
  ℕ∞'-to-ℕ∞ ∞'            ＝⟨ ap ℕ∞'-to-ℕ∞ (∞-preservation ⁻¹) ⟩
  ℕ∞'-to-ℕ∞ (ℕ∞-to-ℕ∞' ∞) ＝⟨ inverses-are-retractions' ℕ∞-to-ℕ∞'-≃ ∞ ⟩
  ∞                       ∎

 finite-preservation : (n : ℕ) → ℕ∞-to-ℕ∞' (ι n) ＝ ι n
 finite-preservation 0        = Zero-preservation
 finite-preservation (succ n) =
  ℕ∞-to-ℕ∞' (ι (succ n))  ＝⟨ refl ⟩
  ℕ∞-to-ℕ∞' (Succ (ι n))  ＝⟨ Succ-preservation (ι n) ⟩
  Succ' (ℕ∞-to-ℕ∞' (ι n)) ＝⟨ ap Succ' (finite-preservation n) ⟩
  Succ' (ι n)             ＝⟨ refl ⟩
  ι (succ n)              ∎

 finite-gives-finite' : (u : ℕ∞') → is-finite (ℕ∞'-to-ℕ∞ u) → is-finite' u
 finite-gives-finite' u (n , e) = III
  where
   I : is-finite' (ι n)
   I = ℕ-to-ℕ∞'-is-finite' n

   II = ι n                     ＝⟨ (finite-preservation n)⁻¹ ⟩
        ℕ∞-to-ℕ∞' (ι n)         ＝⟨ ap ℕ∞-to-ℕ∞' e ⟩
        ℕ∞-to-ℕ∞' (ℕ∞'-to-ℕ∞ u) ＝⟨ inverses-are-sections' ℕ∞-to-ℕ∞'-≃ u ⟩
        u                       ∎

   III : is-finite' u
   III = transport is-finite' II I

 finite'-preservation : (n : ℕ) → ℕ∞'-to-ℕ∞ (ι n) ＝ ι n
 finite'-preservation n =
  ℕ∞'-to-ℕ∞ (ι n)             ＝⟨ I ⟩
  ℕ∞'-to-ℕ∞ (ℕ∞-to-ℕ∞' (ι n)) ＝⟨ II ⟩
  ι n                         ∎
   where
    I  = (ap ℕ∞'-to-ℕ∞ (finite-preservation n))⁻¹
    II = inverses-are-retractions' ℕ∞-to-ℕ∞'-≃ (ι n)

 ℕ-to-ℕ∞'-lc : left-cancellable ℕ-to-ℕ∞'
 ℕ-to-ℕ∞'-lc {n} {n'} e =
  ℕ-to-ℕ∞-lc (
   ι n              ＝⟨ (finite'-preservation n)⁻¹ ⟩
   ℕ∞'-to-ℕ∞ (ι n)  ＝⟨ ap ℕ∞'-to-ℕ∞ e ⟩
   ℕ∞'-to-ℕ∞ (ι n') ＝⟨ finite'-preservation n' ⟩
   ι n'             ∎)

 ℕ-to-ℕ∞'-diagonal : (n : ℕ) → ℕ∞'-to-ℕ→𝟚 (ι n) n ＝ ₁
 ℕ-to-ℕ∞'-diagonal 0        = refl
 ℕ-to-ℕ∞'-diagonal (succ n) = ℕ-to-ℕ∞'-diagonal n

 diagonal-lemma : (n : ℕ) (u : ℕ∞') → ℕ∞'-to-ℕ→𝟚 u n ＝ ₁ → u ＝ ι n
 diagonal-lemma n u p = ℕ∞'-to-ℕ→𝟚-lc fe (dfunext fe f)
  where
   I : ℕ∞'-to-ℕ→𝟚 u n ＝ ℕ∞'-to-ℕ→𝟚 (ι n) n
   I = ℕ∞'-to-ℕ→𝟚 u n     ＝⟨ p ⟩
       ₁                  ＝⟨ (ℕ-to-ℕ∞'-diagonal n)⁻¹ ⟩
       ℕ∞'-to-ℕ→𝟚 (ι n) n ∎

   II : (i : ℕ) → n ≠ i → ℕ∞'-to-ℕ→𝟚 u i ＝ ℕ∞'-to-ℕ→𝟚 (ι n) i
   II i ν =
    ℕ∞'-to-ℕ→𝟚 u i      ＝⟨ II₀ ⟩
    ₀                   ＝⟨ II₁ ⁻¹ ⟩
    ℕ∞'-to-ℕ→𝟚 (ι n) i  ∎
     where
      II₀ = different-from-₁-equal-₀
             (λ (e : ℕ∞'-to-ℕ→𝟚 u i ＝ ₁)
                   → ν (ℕ∞'-index-uniqueness u p e))

      II₁ = different-from-₁-equal-₀
             (λ (e : ℕ∞'-to-ℕ→𝟚 (ι n) i ＝ ₁)
                   → ν (ℕ∞'-index-uniqueness (ι n) (ℕ-to-ℕ∞'-diagonal n) e))

   f : (i : ℕ) → ℕ∞'-to-ℕ→𝟚 u i ＝ ℕ∞'-to-ℕ→𝟚 (ι n) i
   f i = Cases (ℕ-is-discrete n i)
          (λ (q : n ＝ i)
                → transport (λ - → ℕ∞'-to-ℕ→𝟚 u - ＝ ℕ∞'-to-ℕ→𝟚 (ι n) -) q I)
          (λ (ν : n ≠ i)
                → II i ν)

 size'-property' : {u : ℕ∞'} (φ : is-finite' u) → ι (size' {u} φ) ＝ u
 size'-property' {u} φ = II ⁻¹
  where
   I : ℕ∞'-to-ℕ→𝟚 u (size' {u} φ) ＝ ₁
   I = size'-property {u} φ

   II : u ＝ ι (size' {u} φ)
   II = diagonal-lemma (size' {u} φ) u I

 finite'-is-natural : (u : ℕ∞') → is-finite' u → Σ n ꞉ ℕ , u ＝ ι n
 finite'-is-natural u (n , p) = (n , diagonal-lemma n u p)

 finite'-gives-finite : (u : ℕ∞) → is-finite' (ℕ∞-to-ℕ∞' u) → is-finite u
 finite'-gives-finite u (n , e) = III
  where
   I : is-finite (ι n)
   I = ℕ-to-ℕ∞-is-finite n

   II = ι n                     ＝⟨ II₀ ⟩
        ℕ∞'-to-ℕ∞ (ι n)         ＝⟨ II₁ ⟩
        ℕ∞'-to-ℕ∞ (ℕ∞-to-ℕ∞' u) ＝⟨ II₂ ⟩
        u                       ∎
         where
          II₀ = (finite'-preservation n)⁻¹
          II₁ = ap ℕ∞'-to-ℕ∞ ((diagonal-lemma n (ℕ∞-to-ℕ∞' u) e)⁻¹)
          II₂ = inverses-are-retractions' ℕ∞-to-ℕ∞'-≃ u

   III : is-finite u
   III = transport is-finite II I

 finite'-isolated : (n : ℕ) → is-isolated (ℕ-to-ℕ∞' n)
 finite'-isolated n u = I (finite-isolated fe n (ℕ∞'-to-ℕ∞ u))
  where
   I : is-decidable (ι n ＝ ℕ∞'-to-ℕ∞ u) → is-decidable (ι n ＝ u)
   I (inl e) = inl (ι n                     ＝⟨ (finite-preservation n)⁻¹ ⟩
                    ℕ∞-to-ℕ∞' (ι n)         ＝⟨ ap ℕ∞-to-ℕ∞' e ⟩
                    ℕ∞-to-ℕ∞' (ℕ∞'-to-ℕ∞ u) ＝⟨ ℕ∞-ε u ⟩
                    u                       ∎)
   I (inr ν) = inr (λ (e : ι n ＝ u)
                         → ν (ι n             ＝⟨ (finite'-preservation n)⁻¹ ⟩
                              ℕ∞'-to-ℕ∞ (ι n) ＝⟨ ap ℕ∞'-to-ℕ∞ e ⟩
                              ℕ∞'-to-ℕ∞ u     ∎))

 ℕ∞'-equality-criterion : (x y : ℕ∞')
                        → ((n : ℕ) → ι n ＝ x → ι n ＝ y)
                        → ((n : ℕ) → ι n ＝ y → ι n ＝ x)
                        → x ＝ y
 ℕ∞'-equality-criterion x y f g = ℕ∞'-to-ℕ→𝟚-lc fe V
  where
   I : (n : ℕ) (x y : ℕ∞')
     → (ι n ＝ x → ι n ＝ y)
     → ℕ∞'-to-ℕ→𝟚 x n ≤₂ ℕ∞'-to-ℕ→𝟚 y n
   I n x y h = ≤₂-criterion a
    where
     a : ℕ∞'-to-ℕ→𝟚 x n ＝ ₁ → ℕ∞'-to-ℕ→𝟚 y n ＝ ₁
     a e = ℕ∞'-to-ℕ→𝟚 y n     ＝⟨ (ap (λ - → - n) IV)⁻¹ ⟩
           ℕ∞'-to-ℕ→𝟚 (ι n) n ＝⟨ ℕ-to-ℕ∞'-diagonal n ⟩
           ₁                  ∎
      where
       II : ι n ＝ x
       II = (diagonal-lemma n x e)⁻¹

       III : ι n ＝ y
       III = h II

       IV : ℕ∞'-to-ℕ→𝟚 (ι n) ＝ ℕ∞'-to-ℕ→𝟚 y
       IV = ap ℕ∞'-to-ℕ→𝟚 III

   V : ℕ∞'-to-ℕ→𝟚 x ＝ ℕ∞'-to-ℕ→𝟚 y
   V = dfunext fe (λ n → ≤₂-anti (I n x y (f n)) (I n y x (g n)))

\end{code}
