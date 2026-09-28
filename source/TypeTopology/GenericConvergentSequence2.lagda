Martin Escardo, 14th January 2022.

An isomorphic copy of ℕ∞ defined in TypeTopology.GenericConvergentSequence.
The isomorphism is proved in CoNaturals.Equivalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TypeTopology.GenericConvergentSequence2 where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import Notation.CanonicalMap
open import TypeTopology.Cantor
open import UF.DiscreteAndSeparated
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
