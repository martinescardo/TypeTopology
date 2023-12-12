Martin Escardo 2012.

See my JSL paper "Infinite sets that satisfy the principle of
omniscience" for a discussion of the type ℕ∞ defined here.
Essentially, ℕ∞ is ℕ with an added point ∞.

Added December 2017. What we knew for a long time: The ℕ∞ is a retract
of the Cantor type ℕ → 𝟚. This required adding a number of
lemmas. More additions after that date.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module CoNaturals.GenericConvergentSequence where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Addition renaming (_+_ to _∔_)
open import Naturals.Order hiding (max)
open import Naturals.Properties
open import Notation.CanonicalMap
open import Notation.Order
open import TypeTopology.Density
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.FunExt
open import UF.NotNotStablePropositions
open import UF.Retracts
open import UF.Sets
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

Definition (The generic convergent sequence).  We use u,v,x to range
over ℕ∞ and α,β to range over (ℕ → 𝟚):

\begin{code}

is-decreasing : (ℕ → 𝟚) → 𝓤₀ ̇
is-decreasing α = (i : ℕ) → α i ≥ α (i ∔ 1)

being-decreasing-is-prop : funext₀ → (α : ℕ → 𝟚) → is-prop (is-decreasing α)
being-decreasing-is-prop fe α = Π-is-prop fe (λ _ → ≤₂-is-prop-valued)

ℕ∞ : 𝓤₀ ̇
ℕ∞ = Σ α ꞉ (ℕ → 𝟚) , is-decreasing α

ℕ∞-to-ℕ→𝟚 : ℕ∞ → (ℕ → 𝟚)
ℕ∞-to-ℕ→𝟚 = pr₁

instance
 canonical-map-ℕ∞-ℕ→𝟚 : Canonical-Map ℕ∞ (ℕ → 𝟚)
 ι {{canonical-map-ℕ∞-ℕ→𝟚}} = ℕ∞-to-ℕ→𝟚

ℕ∞-to-ℕ→𝟚-lc : funext₀ → left-cancellable ℕ∞-to-ℕ→𝟚
ℕ∞-to-ℕ→𝟚-lc fe = pr₁-lc (being-decreasing-is-prop fe _)

force-decreasing : (ℕ → 𝟚) → (ℕ → 𝟚)
force-decreasing β 0        = β 0
force-decreasing β (succ i) = min𝟚 (β (i ∔ 1)) (force-decreasing β i)

force-decreasing-is-decreasing : (β : ℕ → 𝟚) → is-decreasing (force-decreasing β)
force-decreasing-is-decreasing β 0        = Lemma[minab≤₂b]
force-decreasing-is-decreasing β (succ i) = Lemma[minab≤₂b] {β (i ∔ 2)}
                                                            {force-decreasing β (i ∔ 1)}

force-decreasing-unchanged : (α : ℕ → 𝟚) → is-decreasing α → force-decreasing α ∼ α
force-decreasing-unchanged α d 0        = refl
force-decreasing-unchanged α d (succ i) = g
  where
    IH : force-decreasing α i ＝ α i
    IH = force-decreasing-unchanged α d i

    p : α (i ∔ 1) ≤ α i
    p = d i

    h : min𝟚 (α (i ∔ 1)) (α i) ＝ α (i ∔ 1)
    h = Lemma[a≤₂b→min𝟚ab＝a] p

    g' : min𝟚 (α (i ∔ 1)) (force-decreasing α i) ＝ α (i ∔ 1)
    g' = transport (λ b → min𝟚 (α (i ∔ 1)) b ＝ α (i ∔ 1)) (IH ⁻¹) h

    g : force-decreasing α (i ∔ 1) ＝ α (i ∔ 1)
    g = g'

ℕ→𝟚-to-ℕ∞ : (ℕ → 𝟚) → ℕ∞
ℕ→𝟚-to-ℕ∞ β = force-decreasing β , force-decreasing-is-decreasing β

ℕ→𝟚-to-ℕ∞-is-retraction : funext₀ → (x : ℕ∞) → ℕ→𝟚-to-ℕ∞ (ι x) ＝ x
ℕ→𝟚-to-ℕ∞-is-retraction fe (α , d) =
 to-Σ-＝
  (dfunext fe (force-decreasing-unchanged α d) ,
   being-decreasing-is-prop fe α _ _)

ℕ∞-retract-of-Cantor : funext₀ → retract ℕ∞ of (ℕ → 𝟚)
ℕ∞-retract-of-Cantor fe = ℕ→𝟚-to-ℕ∞ , ι , ℕ→𝟚-to-ℕ∞-is-retraction fe

force-decreasing-is-smaller : (β : ℕ → 𝟚) (i : ℕ) → force-decreasing β i ≤ β i
force-decreasing-is-smaller β 0        = ≤₂-refl
force-decreasing-is-smaller β (succ i) = Lemma[minab≤₂a]

force-decreasing-is-not-much-smaller : (β : ℕ → 𝟚) (n : ℕ)
                                     → force-decreasing β n ＝ ₀
                                     → Σ m ꞉ ℕ , β m ＝ ₀
force-decreasing-is-not-much-smaller β 0  p       = 0 , p
force-decreasing-is-not-much-smaller β (succ n) p = f c
  where
    A = Σ m ꞉ ℕ , β m ＝ ₀

    c : (β (n ∔ 1) ＝ ₀) + (force-decreasing β n ＝ ₀)
    c = lemma[min𝟚ab＝₀] {β (n ∔ 1)} {force-decreasing β n} p

    f : (β (n ∔ 1) ＝ ₀) + (force-decreasing β n ＝ ₀) → A
    f (inl q) = n ∔ 1 , q
    f (inr r) = force-decreasing-is-not-much-smaller β n r

Cantor-is-¬¬-separated : funext₀ → is-¬¬-separated (ℕ → 𝟚)
Cantor-is-¬¬-separated fe = Π-is-¬¬-separated fe (λ _ → 𝟚-is-¬¬-separated)

ℕ∞-is-¬¬-separated : funext₀ → is-¬¬-separated ℕ∞
ℕ∞-is-¬¬-separated fe = subtype-is-¬¬-separated
                         pr₁
                         (ℕ∞-to-ℕ→𝟚-lc fe)
                         (Cantor-is-¬¬-separated fe)

ℕ∞-is-set : funext₀ → is-set ℕ∞
ℕ∞-is-set fe = ¬¬-separated-types-are-sets fe (ℕ∞-is-¬¬-separated fe)

open import TypeTopology.TotallySeparated

ℕ∞-is-totally-separated : funext₀ → is-totally-separated ℕ∞
ℕ∞-is-totally-separated fe = retract-of-totally-separated
                              (ℕ∞-retract-of-Cantor fe)
                              (Cantor-is-totally-separated fe)


Zero : ℕ∞
Zero = (λ i → ₀) , (λ i → ≤₂-refl {₀})

cons : 𝟚 → (ℕ → 𝟚) → (ℕ → 𝟚)
cons b α 0        = b
cons b α (succ n) = α n

Succ : ℕ∞ → ℕ∞
Succ (α , d) = (cons ₁ α , d')
 where
  d' : is-decreasing (cons ₁ α)
  d' 0        = ₁-top
  d' (succ i) = d i

instance
 Square-Order-ℕ∞-ℕ : Square-Order ℕ∞ ℕ
 _⊑_ {{Square-Order-ℕ∞-ℕ}} u n = ι u n ＝ ₀

 Strict-Square-Order-ℕ-ℕ∞ : Strict-Square-Order ℕ ℕ∞
 _⊏_ {{Strict-Square-Order-ℕ-ℕ∞}} n u = ι u n ＝ ₁

not-⊏-is-⊒ : {m : ℕ} {u : ℕ∞} → ¬ (m ⊏ u) → u ⊑ m
not-⊏-is-⊒ f = different-from-₁-equal-₀ f

not-⊑-is-⊐ : {m : ℕ} {u : ℕ∞} → ¬ (u ⊑ m) → m ⊏ u
not-⊑-is-⊐ f = different-from-₀-equal-₁ f

is-Zero : ℕ∞ → 𝓤₀ ̇
is-Zero u = u ⊑ 0

is-positive : ℕ∞ → 𝓤₀ ̇
is-positive u = 0 ⊏ u

positivity : ℕ∞ → 𝟚
positivity u = ι u 0

𝟚-retract-of-ℕ∞ : retract 𝟚 of ℕ∞
𝟚-retract-of-ℕ∞  = positivity , s , η
 where
  s : 𝟚 → ℕ∞
  s ₀ = Zero
  s ₁ = Succ Zero

  η : positivity ∘ s ∼ id
  η ₀ = refl
  η ₁ = refl

is-Zero-Zero : is-Zero Zero
is-Zero-Zero = refl

is-positive-Succ : (α : ℕ∞) → is-positive (Succ α)
is-positive-Succ α = refl

Zero-not-Succ : {u : ℕ∞} → Zero ≠ Succ u
Zero-not-Succ {u} r = zero-is-not-one (ap positivity r)

Succ-not-Zero : {u : ℕ∞} → Succ u ≠ Zero
Succ-not-Zero = ≠-sym Zero-not-Succ

∞ : ℕ∞
∞ = (λ i → ₁) , (λ i → ≤₂-refl {₁})

Succ-∞-is-∞ : funext₀ → Succ ∞ ＝ ∞
Succ-∞-is-∞ fe = ℕ∞-to-ℕ→𝟚-lc fe (dfunext fe lemma)
 where
   lemma : (i : ℕ) → ι (Succ ∞) i ＝ ι ∞ i
   lemma 0        = refl
   lemma (succ i) = refl

unique-fixed-point-of-Succ : funext₀ → (u : ℕ∞) → u ＝ Succ u → u ＝ ∞
unique-fixed-point-of-Succ fe u r = ℕ∞-to-ℕ→𝟚-lc fe claim
 where
  fact : (i : ℕ) → ι u i ＝ ι (Succ u) i
  fact i = ap (λ - → ι - i) r

  lemma : (i : ℕ) → ι u i ＝ ₁
  lemma 0        = fact 0
  lemma (succ i) = ι u (i ∔ 1)        ＝⟨ fact (i ∔ 1) ⟩
                   ι (Succ u) (i ∔ 1) ＝⟨ lemma i ⟩
                   ₁                  ∎

  claim : ι u ＝ ι ∞
  claim = dfunext fe lemma

Pred : ℕ∞ → ℕ∞
Pred (α , d) = (α ∘ succ , d ∘ succ)

Pred-Zero-is-Zero : Pred Zero ＝ Zero
Pred-Zero-is-Zero = refl

Pred-Zero-is-Zero' : (u : ℕ∞) → u ＝ Zero → Pred u ＝ u
Pred-Zero-is-Zero' u p = transport (λ - → Pred - ＝ -) (p ⁻¹) Pred-Zero-is-Zero

Pred-Succ : {u : ℕ∞} → Pred (Succ u) ＝ u
Pred-Succ {u} = refl

Pred-∞-is-∞ : Pred ∞ ＝ ∞
Pred-∞-is-∞ = refl

Succ-lc : left-cancellable Succ
Succ-lc = ap Pred

ℕ-to-ℕ∞ : ℕ → ℕ∞
ℕ-to-ℕ∞ 0        = Zero
ℕ-to-ℕ∞ (succ n) = Succ (ℕ-to-ℕ∞ n)

instance
 Canonical-Map-ℕ-ℕ∞ : Canonical-Map ℕ ℕ∞
 ι {{Canonical-Map-ℕ-ℕ∞}} = ℕ-to-ℕ∞

_≣_ : ℕ∞ → ℕ → 𝓤₀ ̇
u ≣ n = u ＝ ι n

ℕ-to-ℕ∞-lc : left-cancellable ι
ℕ-to-ℕ∞-lc {0}      {0}      r = refl
ℕ-to-ℕ∞-lc {0}      {succ n} r = 𝟘-elim (Zero-not-Succ r)
ℕ-to-ℕ∞-lc {succ m} {0}      r = 𝟘-elim (Zero-not-Succ (r ⁻¹))
ℕ-to-ℕ∞-lc {succ m} {succ n} r = ap succ (ℕ-to-ℕ∞-lc {m} {n} (Succ-lc r))

ℕ-to-ℕ∞-is-embedding : funext₀ → is-embedding ℕ-to-ℕ∞
ℕ-to-ℕ∞-is-embedding fe = lc-maps-into-sets-are-embeddings ℕ-to-ℕ∞ ℕ-to-ℕ∞-lc (ℕ∞-is-set fe)

embedding-ℕ-to-ℕ∞ : funext₀ → ℕ ↪ ℕ∞
embedding-ℕ-to-ℕ∞ fe = ℕ-to-ℕ∞ , ℕ-to-ℕ∞-is-embedding fe

ℕ-to-ℕ∞-lc-refl : (k : ℕ) → ℕ-to-ℕ∞-lc refl ＝ refl {_} {ℕ} {k}
ℕ-to-ℕ∞-lc-refl 0        = refl
ℕ-to-ℕ∞-lc-refl (succ k) = ap (ap succ) (ℕ-to-ℕ∞-lc-refl k)

ℕ-to-ℕ∞-diagonal₀ : (n : ℕ) → ι n ⊑ n
ℕ-to-ℕ∞-diagonal₀ 0        = refl
ℕ-to-ℕ∞-diagonal₀ (succ n) = ℕ-to-ℕ∞-diagonal₀ n

ℕ-to-ℕ∞-diagonal₁ : (n : ℕ) → n ⊏ ι (n ∔ 1)
ℕ-to-ℕ∞-diagonal₁ 0        = refl
ℕ-to-ℕ∞-diagonal₁ (succ n) = ℕ-to-ℕ∞-diagonal₁ n

is-Zero-equal-Zero : funext₀ → {u : ℕ∞} → is-Zero u → u ＝ Zero
is-Zero-equal-Zero fe {u} base = ℕ∞-to-ℕ→𝟚-lc fe (dfunext fe lemma)
 where
  lemma : (i : ℕ) → ι u i ＝ ι Zero i
  lemma 0        = base
  lemma (succ i) = [a＝₁→b＝₁]-gives-[b＝₀→a＝₀] (≤₂-criterion-converse (pr₂ u i)) (lemma i)

same-positivity : funext₀ → (u v : ℕ∞)
                → (u ＝ Zero → v ＝ Zero)
                → (v ＝ Zero → u ＝ Zero)
                → positivity u ＝ positivity v
same-positivity fe₀ u v f g = ≤₂-anti (≤₂'-gives-≤₂ a)
                                      (≤₂'-gives-≤₂ b)
 where
  a : is-Zero v → is-Zero u
  a p = transport⁻¹ is-Zero (g (is-Zero-equal-Zero fe₀ p)) refl

  b : is-Zero u → is-Zero v
  b p = transport⁻¹ is-Zero (f (is-Zero-equal-Zero fe₀ p)) refl

successors-same-positivity : {u u' v v' : ℕ∞}
                           → u ＝ Succ u'
                           → v ＝ Succ v'
                           → positivity u ＝ positivity v
successors-same-positivity refl refl = refl

not-Zero-is-Succ : funext₀ → {u : ℕ∞} → u ≠ Zero → u ＝ Succ (Pred u)
not-Zero-is-Succ fe {u} f = ℕ∞-to-ℕ→𝟚-lc fe (dfunext fe lemma)
 where
  lemma : (i : ℕ) → ι u i ＝ ι (Succ (Pred u)) i
  lemma 0        = different-from-₀-equal-₁ (f ∘ is-Zero-equal-Zero fe)
  lemma (succ i) = refl

positive-is-not-Zero : {u : ℕ∞} → is-positive u → u ≠ Zero
positive-is-not-Zero {u} r s = lemma r
 where
  lemma : ¬ (is-positive u)
  lemma = equal-₀-different-from-₁ (ap positivity s)

positive-equal-Succ : funext₀ → {u : ℕ∞} → is-positive u → u ＝ Succ (Pred u)
positive-equal-Succ fe r = not-Zero-is-Succ fe (positive-is-not-Zero r)

Zero-or-Succ : funext₀ → (u : ℕ∞) → (u ＝ Zero) + (u ＝ Succ (Pred u))
Zero-or-Succ fe₀ u = 𝟚-equality-cases
                      (λ (z : is-Zero u) → inl (is-Zero-equal-Zero fe₀ z))
                      (λ (p : is-positive u) → inr (positive-equal-Succ fe₀ p))

is-Succ : ℕ∞ → 𝓤₀ ̇
is-Succ u = Σ w ꞉ ℕ∞ , u ＝ Succ w

Zero+Succ : funext₀ → (u : ℕ∞) → (u ＝ Zero) + is-Succ u
Zero+Succ fe₀ u = Cases (Zero-or-Succ fe₀ u) inl (λ p → inr (Pred u , p))

Succ-criterion : funext₀ → {u : ℕ∞} {n : ℕ} → n ⊏ u → u ⊑ n ∔ 1 → u ＝ Succ (ι n)
Succ-criterion fe {u} {n} r s = ℕ∞-to-ℕ→𝟚-lc fe claim
 where
  lemma : (u : ℕ∞) (n : ℕ) → n ⊏ u → u ⊑ n ∔ 1
        → (i : ℕ) → ι u i ＝ ι (Succ (ι n)) i
  lemma u 0 r s 0        = r
  lemma u 0 r s (succ i) = lemma₀ i
     where
      lemma₀ : (i : ℕ) → u ⊑ i ∔ 1
      lemma₀ 0        = s
      lemma₀ (succ i) = [a＝₁→b＝₁]-gives-[b＝₀→a＝₀]
                         (≤₂-criterion-converse (pr₂ u (i ∔ 1))) (lemma₀ i)
  lemma u (succ n) r s 0 = lemma₁ (n ∔ 1) r
     where
      lemma₁ : (n : ℕ) → n ⊏ u → is-positive u
      lemma₁ 0        t = t
      lemma₁ (succ n) t = lemma₁ n (≤₂-criterion-converse (pr₂ u n) t)
  lemma u (succ n) r s (succ i) = lemma (Pred u) n r s i

  claim : ι u ＝ ι (Succ (ι n))
  claim = dfunext fe (lemma u n r s)

∞-is-not-finite : (n : ℕ) → ∞ ≠ ι n
∞-is-not-finite n s = one-is-not-zero (₁         ＝⟨ ap (λ - → ι - n) s ⟩
                                       ι (ι n) n ＝⟨ ℕ-to-ℕ∞-diagonal₀ n ⟩
                                       ₀         ∎)

not-finite-is-∞ : funext₀ → {u : ℕ∞} → ((n : ℕ) → u ≠ ι n) → u ＝ ∞
not-finite-is-∞ fe {u} f = ℕ∞-to-ℕ→𝟚-lc fe (dfunext fe lemma)
 where
  lemma : (n : ℕ) → n ⊏ u
  lemma 0        = different-from-₀-equal-₁ (λ r → f 0 (is-Zero-equal-Zero fe r))
  lemma (succ n) = different-from-₀-equal-₁ (λ r → f (n ∔ 1) (Succ-criterion fe (lemma n) r))

ℕ∞-ddensity : funext₀ → {Y : ℕ∞ → 𝓤 ̇ }
            → ({u : ℕ∞} → is-¬¬-separated (Y u))
            → {f g : Π Y}
            → ((n : ℕ) → f (ι n) ＝ g (ι n))
            → f ∞ ＝ g ∞
            → (u : ℕ∞) → f u ＝ g u
ℕ∞-ddensity fe {Y} s {f} {g} h h∞ u = s (f u) (g u) c
 where
  a : f u ≠ g u → (n : ℕ) → u ≠ ι n
  a t n = contrapositive (λ (r : u ＝ ι n) → transport⁻¹ (λ - → f - ＝ g -) r (h n)) t

  b : f u ≠ g u → u ≠ ∞
  b = contrapositive (λ (r : u ＝ ∞) → transport⁻¹ (λ - → f - ＝ g -) r h∞)

  c : ¬¬ (f u ＝ g u)
  c = λ t → b t (not-finite-is-∞ fe (a t))

ℕ∞-density : funext₀
           → {Y : 𝓤 ̇ }
           → is-¬¬-separated Y
           → {f g : ℕ∞ → Y}
           → ((n : ℕ) → f (ι n) ＝ g (ι n))
           → f ∞ ＝ g ∞
           → (u : ℕ∞) → f u ＝ g u
ℕ∞-density fe s = ℕ∞-ddensity fe (λ {_} → s)

ℕ∞-𝟚-density : funext₀
             → {p : ℕ∞ → 𝟚}
             → ((n : ℕ) → p (ι n) ＝ ₁)
             → p ∞ ＝ ₁
             → (u : ℕ∞) → p u ＝ ₁
ℕ∞-𝟚-density fe = ℕ∞-density fe 𝟚-is-¬¬-separated

ι𝟙 : ℕ + 𝟙 → ℕ∞
ι𝟙 = cases {𝓤₀} {𝓤₀} ι (λ _ → ∞)

ι𝟙-is-embedding : funext₀ → is-embedding ι𝟙
ι𝟙-is-embedding fe = disjoint-cases-embedding ι (λ _ → ∞) (ℕ-to-ℕ∞-is-embedding fe) g d
 where
  g : is-embedding (λ _ → ∞)
  g x (* , p) (⋆ , q) = ap (λ - → ⋆ , -) (ℕ∞-is-set fe p q)

  d : (n : ℕ) (y : 𝟙) → ι n ≠ ∞
  d n _ p = ∞-is-not-finite n (p ⁻¹)

ι𝟙-dense : funext₀ → is-dense ι𝟙
ι𝟙-dense fe (u , f) = g (not-finite-is-∞ fe h)
 where
  g : ¬ (u ＝ ∞)
  g p = f ((inr ⋆) , (p ⁻¹))

  h : (n : ℕ) → ¬ (u ＝ ι n)
  h n p = f (inl n , (p ⁻¹))

\end{code}

There should be a better proof of the following. The idea is simple:
by the above development, u = ι 0 if and only if ι u 0 ＝ 0, and
u ＝ ι (n+1) if and only if n ⊏ u ⊑ n+1.

\begin{code}

finite-isolated : funext₀ → (n : ℕ) → is-isolated (ι n)
finite-isolated fe n u = is-decidable-eq-sym u (ι n) (f u n)
 where
  f : (u : ℕ∞) (n : ℕ) → is-decidable (u ＝ ι n)
  f u 0 = 𝟚-equality-cases g₀ g₁
   where
    g₀ : is-Zero u → is-decidable (u ＝ Zero)
    g₀ r = inl (is-Zero-equal-Zero fe r)

    h : u ＝ Zero → is-Zero u
    h = ap (λ - → ι - 0)

    g₁ : is-positive u → is-decidable (u ＝ Zero)
    g₁ r = inr (contrapositive h (equal-₁-different-from-₀ r))

  f u (succ n) = 𝟚-equality-cases g₀ g₁
   where
    g : u ＝ ι (n ∔ 1) → n ⊏ u
    g r = ap (λ - → ι - n) r ∙ ℕ-to-ℕ∞-diagonal₁ n

    g₀ :  u ⊑ n → is-decidable (u ＝ ι (n ∔ 1))
    g₀ r = inr (contrapositive g (equal-₀-different-from-₁ r))

    h : u ＝ ι (n ∔ 1) → u ⊑ n ∔ 1
    h r = ap (λ - → ι - (n ∔ 1)) r ∙ ℕ-to-ℕ∞-diagonal₀ (n ∔ 1)

    g₁ :  n ⊏ u → is-decidable (u ＝ ι (n ∔ 1))
    g₁ r = 𝟚-equality-cases g₁₀ g₁₁
     where
      g₁₀ : u ⊑ n ∔ 1 → is-decidable (u ＝ ι (n ∔ 1))
      g₁₀ s = inl (Succ-criterion fe r s)

      g₁₁ : n ∔ 1 ⊏ u → is-decidable (u ＝ ι (n ∔ 1))
      g₁₁ s = inr (contrapositive h (equal-₁-different-from-₀ s))


is-finite : ℕ∞ → 𝓤₀ ̇
is-finite u = Σ n ꞉ ℕ , ι n ＝ u

size : {u : ℕ∞} → is-finite u → ℕ
size (n , r) = n

being-finite-is-prop : funext₀ → (u : ℕ∞) → is-prop (is-finite u)
being-finite-is-prop = ℕ-to-ℕ∞-is-embedding

ℕ-to-ℕ∞-is-finite : (n : ℕ) → is-finite (ι n)
ℕ-to-ℕ∞-is-finite n = (n , refl)

Zero-is-finite : is-finite Zero
Zero-is-finite = ℕ-to-ℕ∞-is-finite 0

Zero-is-finite' : funext₀ → (u : ℕ∞) → is-Zero u → is-finite u
Zero-is-finite' fe u z = transport⁻¹
                           is-finite
                           (is-Zero-equal-Zero fe z)
                           Zero-is-finite

is-finite-down : (u : ℕ∞) → is-finite (Succ u) → is-finite u
is-finite-down u (0 , r)      = 𝟘-elim (Zero-not-Succ r)
is-finite-down u (succ n , r) = n , Succ-lc r

is-finite-up : (u : ℕ∞) → is-finite u → is-finite (Succ u)
is-finite-up u (n , r) = (n ∔ 1 , ap Succ r)

is-finite-up' : funext₀ → (u : ℕ∞) → is-finite (Pred u) → is-finite u
is-finite-up' fe u i = 𝟚-equality-cases
                         (λ (z : is-Zero u)
                            → Zero-is-finite' fe u z)
                         (λ (p : is-positive u)
                            → transport⁻¹
                               is-finite
                               (positive-equal-Succ fe p)
                               (is-finite-up (Pred u) i))

is-infinite-∞ : ¬ is-finite ∞
is-infinite-∞ (n , r) = 𝟘-elim (∞-is-not-finite n (r ⁻¹))

\end{code}

Order on ℕ∞:

\begin{code}

_≼ℕ∞_ : ℕ∞ → ℕ∞ → 𝓤₀ ̇
u ≼ℕ∞ v = (n : ℕ) → n ⊏ u → n ⊏ v

instance
 Curly-Order-ℕ∞-ℕ∞ : Curly-Order ℕ∞ ℕ∞
 _≼_ {{Curly-Order-ℕ∞-ℕ∞}} = _≼ℕ∞_

≼-anti : funext₀ → (u v : ℕ∞) → u ≼ v → v ≼ u → u ＝ v
≼-anti fe u v l m = ℕ∞-to-ℕ→𝟚-lc fe γ
 where
  γ : ι u ＝ ι v
  γ = dfunext fe (λ i → ≤₂-anti (≤₂-criterion (l i)) (≤₂-criterion (m i)))

∞-largest : (u : ℕ∞) → u ≼ ∞
∞-largest u = λ n _ → refl

Zero-smallest : (u : ℕ∞) → Zero ≼ u
Zero-smallest u n = λ (p : ₀ ＝ ₁) → 𝟘-elim (zero-is-not-one p)

Succ-not-≼-Zero : (u : ℕ∞) → ¬ (Succ u ≼ Zero)
Succ-not-≼-Zero u l = zero-is-not-one (l zero refl)

Succ-monotone : (u v : ℕ∞) → u ≼ v → Succ u ≼ Succ v
Succ-monotone u v l 0        p = p
Succ-monotone u v l (succ n) p = l n p

Succ-loc : (u v : ℕ∞) → Succ u ≼ Succ v → u ≼ v
Succ-loc u v l n = l (n ∔ 1)

above-Succ-is-positive : (u v : ℕ∞) → Succ u ≼ v → is-positive v
above-Succ-is-positive u v l = l 0 refl

≼-unfold-Succ : funext₀ → (u v : ℕ∞) → Succ u ≼ v → Succ u ≼ Succ (Pred v)
≼-unfold-Succ fe u v l = transport (λ - → Succ u ≼ -)
                          (positive-equal-Succ fe {v}
                            (above-Succ-is-positive u v l)) l

≼-unfold : funext₀ → (u v : ℕ∞)
         → u ≼ v
         → (u ＝ Zero) + (Σ w ꞉ ℕ∞ , Σ t ꞉ ℕ∞ , (u ＝ Succ w) × (v ＝ Succ t) × (w ≼ t))
≼-unfold fe u v l = φ (Zero+Succ fe u) (Zero+Succ fe v)
 where
  φ : (u ＝ Zero) + is-Succ u → (v ＝ Zero) + is-Succ v → _
  φ (inl p)          _                = inl p
  φ (inr (w , refl)) (inl refl)       = 𝟘-elim (Succ-not-≼-Zero w l)
  φ (inr (w , refl)) (inr (t , refl)) = inr (w , t , refl , refl , Succ-loc w t l)

≼-fold : (u v : ℕ∞)
       → ((u ＝ Zero) + (Σ w ꞉ ℕ∞ , Σ t ꞉ ℕ∞ , (u ＝ Succ w) × (v ＝ Succ t) × (w ≼ t)))
       → u ≼ v
≼-fold Zero      v         (inl refl)                      = Zero-smallest v
≼-fold .(Succ w) .(Succ t) (inr (w , t , refl , refl , l)) = Succ-monotone w t l

max : ℕ∞ → ℕ∞ → ℕ∞
max (α , r) (β , s) = (λ i → max𝟚 (α i) (β i)) , t
 where
  t : is-decreasing (λ i → max𝟚 (α i) (β i))
  t i = max𝟚-preserves-≤ (r i) (s i)

min : ℕ∞ → ℕ∞ → ℕ∞
min (α , r) (β , s) = (λ i → min𝟚 (α i) (β i)) , t
 where
  t : is-decreasing (λ i → min𝟚 (α i) (β i))
  t i = min𝟚-preserves-≤ (r i) (s i)

\end{code}

More lemmas about order should be added, but I will do this on demand
as the need arises.

\begin{code}

∞-⊏-largest : (n : ℕ) → n ⊏ ∞
∞-⊏-largest n = refl

_≺ℕ∞_ : ℕ∞ → ℕ∞ → 𝓤₀ ̇
u ≺ℕ∞ v = Σ n ꞉ ℕ , (u ＝ ι n) × n ⊏ v

instance
 Strict-Curly-Order-ℕ∞-ℕ∞ : Strict-Curly-Order ℕ∞ ℕ∞
 _≺_ {{Strict-Curly-Order-ℕ∞-ℕ∞}} = _≺ℕ∞_

∞-top : (u : ℕ∞) → ¬ (∞ ≺ u)
∞-top u (n , r , l) = ∞-is-not-finite n r

below-isolated : funext₀ → (u v : ℕ∞) → u ≺ v → is-isolated u
below-isolated fe u v (n , r , l) = transport⁻¹ is-isolated r (finite-isolated fe n)

≺-prop-valued : funext₀ → (u v : ℕ∞) → is-prop (u ≺ v)
≺-prop-valued fe u v (n , r , a) (m , s , b) = to-Σ-＝ (ℕ-to-ℕ∞-lc (r ⁻¹ ∙ s) ,
                                                       to-Σ-＝ (ℕ∞-is-set fe _ _ ,
                                                               𝟚-is-set _ _))

⊏-gives-≺ : (n : ℕ) (u : ℕ∞) → n ⊏ u → ι n ≺ u
⊏-gives-≺ n u a = n , refl , a

≺-gives-⊏ : (n : ℕ) (u : ℕ∞) → ι n ≺ u → n ⊏ u
≺-gives-⊏ n u (m , r , a) = transport⁻¹ (λ k → k ⊏ u) (ℕ-to-ℕ∞-lc r) a

∞-≺-largest : (n : ℕ) → ι n ≺ ∞
∞-≺-largest n = n , refl , ∞-⊏-largest n

≺-implies-finite : (a b : ℕ∞) → a ≺ b → is-finite a
≺-implies-finite a b (n , p , _) = n , (p ⁻¹)

ℕ-to-ℕ∞-≺-diagonal : (n : ℕ) → ι n ≺ ι (n ∔ 1)
ℕ-to-ℕ∞-≺-diagonal n = n , refl , ℕ-to-ℕ∞-diagonal₁ n

finite-≺-Succ : (a : ℕ∞) → is-finite a → a ≺ Succ a
finite-≺-Succ a (n , p) = transport (_≺ Succ a) p
                            (transport (ι n ≺_) (ap Succ p)
                              (ℕ-to-ℕ∞-≺-diagonal n))

≺-Succ : (a b : ℕ∞) → a ≺ b → Succ a ≺ Succ b
≺-Succ a b (n , p , q) = n ∔ 1 , ap Succ p , q

open import Naturals.Order

<-gives-⊏ : (m n : ℕ) → m < n →  m ⊏ ι n
<-gives-⊏ 0        0        l = 𝟘-elim l
<-gives-⊏ 0        (succ n) l = refl
<-gives-⊏ (succ m) 0        l = 𝟘-elim l
<-gives-⊏ (succ m) (succ n) l = <-gives-⊏ m n l

⊏-gives-< : (m n : ℕ) →  m ⊏ ι n → m < n
⊏-gives-< 0        0        l = 𝟘-elim (zero-is-not-one l)
⊏-gives-< 0        (succ n) l = zero-least n
⊏-gives-< (succ m) 0        l = 𝟘-elim (zero-is-not-one l)
⊏-gives-< (succ m) (succ n) l = ⊏-gives-< m n l

⊏-back : (u : ℕ∞) (n : ℕ) → n ∔ 1 ⊏ u → n ⊏ u
⊏-back u n = ≤₂-criterion-converse (pr₂ u n)

⊏-trans'' : (u : ℕ∞) (n : ℕ) → (m : ℕ) → m ≤ n → n ⊏ u → m ⊏ u
⊏-trans'' u = regress (λ n → n ⊏ u) (⊏-back u)

⊏-trans' : (m : ℕ) (n : ℕ) (u : ℕ∞)  → m < n → n ⊏ u → m ⊏ u
⊏-trans' m n u l = ⊏-trans'' u n m (≤-trans m (m ∔ 1) n (≤-succ m) l)

⊏-trans : (m n : ℕ) (u : ℕ∞) → m ⊏ ι n → n ⊏ u → m ⊏ u
⊏-trans m n u a = ⊏-trans' m n u (⊏-gives-< m n a)

open import Ordinals.Notions

≺-trans : is-transitive _≺_
≺-trans u v w (m , r , a) (n , s , b) = m , r , c
 where
  c : m ⊏ w
  c = ⊏-trans m n w (transport (λ t → m ⊏ t) s a) b

≺-Succ-r : (a b : ℕ∞) → a ≺ b → a ≺ Succ b
≺-Succ-r a b l = ≺-trans a (Succ a) (Succ b)
                     (finite-≺-Succ a (≺-implies-finite a b l))
                     (≺-Succ a b l)

≺≼-gives-≺ : (x y z : ℕ∞) → x ≺ y → y ≼ z → x ≺ z
≺≼-gives-≺ x y z (n , p , q) le = n , p , le n q

finite-accessible : (n : ℕ) → is-accessible _≺_ (ι n)
finite-accessible = course-of-values-induction (λ n → is-accessible _≺_ (ι n)) φ
 where
  φ : (n : ℕ)
    → ((m : ℕ) → m < n → is-accessible _≺_ (ι m))
    → is-accessible _≺_ (ι n)
  φ n σ = acc τ
   where
    τ : (u : ℕ∞) → u ≺ ι n → is-accessible _≺_ u
    τ u (m , r , l) = transport⁻¹ (is-accessible _≺_) r (σ m (⊏-gives-< m n l))

≺-well-founded : is-well-founded _≺_
≺-well-founded v = acc σ
 where
  σ : (u : ℕ∞) → u ≺ v → is-accessible _≺_ u
  σ u (n , r , l) = transport⁻¹ (is-accessible _≺_) r (finite-accessible n)

≺-extensional : funext₀ → is-extensional _≺_
≺-extensional fe u v l m = γ
 where
  f : (i : ℕ) → i ⊏ u → i ⊏ v
  f i a = ≺-gives-⊏ i v (l (ι i) (⊏-gives-≺ i u a))

  g : (i : ℕ) → i ⊏ v → i ⊏ u
  g i a = ≺-gives-⊏ i u (m (ι i) (⊏-gives-≺ i v a))

  h : (i : ℕ) → ι u i ＝ ι v i
  h i = ≤₂-anti (≤₂-criterion (f i)) (≤₂-criterion (g i))

  γ : u ＝ v
  γ = ℕ∞-to-ℕ→𝟚-lc fe (dfunext fe h)

ℕ∞-ordinal : funext₀ → is-well-order _≺_
ℕ∞-ordinal fe = (≺-prop-valued fe) , ≺-well-founded , ≺-extensional fe , ≺-trans

\end{code}

The following is not needed anymore, as we have the stronger fact,
proved above, that ≺ is well founded:

\begin{code}

≺-well-founded₂ : funext₀ → is-well-founded₂ _≺_
≺-well-founded₂ fe p φ = ℕ∞-𝟚-density fe a b
 where
  γ : (n : ℕ) → ((m : ℕ) → m < n → p (ι m) ＝ ₁) → p (ι n) ＝ ₁
  γ n g = φ (ι n) h
   where
    h : (u : ℕ∞) → u ≺ ι n → p u ＝ ₁
    h u (m , r , l) = transport⁻¹ (λ v → p v ＝ ₁) r (g m (⊏-gives-< m n l))

  a : (n : ℕ) → p (ι n) ＝ ₁
  a = course-of-values-induction (λ n → p (ι n) ＝ ₁) γ

  f : (u : ℕ∞) → u ≺ ∞ → p u ＝ ₁
  f u (n , r , l) = transport⁻¹ (λ v → p v ＝ ₁) r (a n)

  b : p ∞ ＝ ₁
  b = φ ∞ f

ℕ∞-ordinal₂ : funext₀ → is-well-order₂ _≺_
ℕ∞-ordinal₂ fe = ≺-prop-valued fe ,
                 ≺-well-founded₂ fe ,
                 ≺-extensional fe ,
                 ≺-trans

ℕ-to-ℕ∞-lemma : funext₀ → (u : ℕ∞) (n : ℕ) → u ⊑ n → Σ m ꞉ ℕ , (m ≤ n) × (u ＝ ι m)
ℕ-to-ℕ∞-lemma fe u 0        p = 0 , ≤-refl 0 , is-Zero-equal-Zero fe p
ℕ-to-ℕ∞-lemma fe u (succ n) p = g (𝟚-is-discrete (ι u n) ₀)
 where
  IH : u ⊑ n → Σ m ꞉ ℕ , (m ≤ n) × (u ＝ ι m)
  IH = ℕ-to-ℕ∞-lemma fe u n

  g : is-decidable(u ⊑ n) → Σ m ꞉ ℕ , (m ≤ n ∔ 1) × (u ＝ ι m)
  g (inl q) = pr₁(IH q) , ≤-trans (pr₁ (IH q)) n (n ∔ 1)
                           (pr₁ (pr₂ (IH q)))
                           (≤-succ n) , pr₂ (pr₂ (IH q))
  g (inr φ) = n ∔ 1 , ≤-refl n , s
    where
     q : n ⊏ u
     q = different-from-₀-equal-₁ φ

     s : u ＝ Succ (ι n)
     s = Succ-criterion fe {u} {n} q p

≺-cotransitive : funext₀ → cotransitive _≺_
≺-cotransitive fe u v w (n , r , a) = g (𝟚-is-discrete (ι w n) ₁)
 where
  g : is-decidable (n ⊏ w) → (u ≺ w) + (w ≺ v)
  g (inl a) = inl (n , r , a)
  g (inr f) = inr (m , s , ⊏-trans'' v n m l a)
   where
    b : w ⊑ n
    b = not-⊏-is-⊒ {n} {w} f

    σ : Σ m ꞉ ℕ , (m ≤ n) × (w ＝ ι m)
    σ = ℕ-to-ℕ∞-lemma fe w n b

    m : ℕ
    m = pr₁ σ

    l : m ≤ n
    l = pr₁ (pr₂ σ)

    s : w ＝ ι m
    s = pr₂ (pr₂ σ)

ℕ∞-𝟚-order-separated : funext₀ → 𝟚-order-separated _≺_
ℕ∞-𝟚-order-separated fe x y (n , r , l) =  p , t , h
 where
  p : ℕ∞ → 𝟚
  p z = ι z n

  e : ι x n ＝ ₀
  e = transport⁻¹ (λ z → p z ＝ ₀) r (ℕ-to-ℕ∞-diagonal₀ n)

  t : ι x n <₂ ι y n
  t = <₂-criterion e l

  f : (u v : ℕ∞) → u ≺ v → p u ≤ p v
  f u v (n' , r' , l') = ≤₂-criterion ϕ
   where
    ϕ : ι u n ＝ ₁ → p v ＝ ₁
    ϕ s = ⊏-trans' n n' v b l'
     where
      a : p (ι n') ＝ ₁
      a = transport (λ z → p z ＝ ₁) r' s

      b : n < n'
      b = ⊏-gives-< n n' a

  g : (u v : ℕ∞) → p u <₂ p v → u ≺ v
  g u v l = γ (<₂-criterion-converse l)
   where
    γ : (p u ＝ ₀) × (p v ＝ ₁) → u ≺ v
    γ (a , b) = pr₁ c , pr₂ (pr₂ c) , (⊏-trans'' v n (pr₁ c) (pr₁ (pr₂ c)) b)
     where
      c : Σ m ꞉ ℕ , (m ≤ n) × (u ＝ ι m)
      c = ℕ-to-ℕ∞-lemma fe u n a

  h : (u v : ℕ∞) → (u ≺ v → p u ≤ p v) × (p u <₂ p v → u ≺ v)
  h u v = f u v , g u v

ℕ-to-ℕ∞-order-preserving : (m n : ℕ) → m < n → ι m ≺ ι n
ℕ-to-ℕ∞-order-preserving m n l = m , refl , <-gives-⊏ m n l

ℕ-to-ℕ∞-order-reflecting : (m n : ℕ) → ι m ≺ ι n → m < n
ℕ-to-ℕ∞-order-reflecting m n (m' , p , l') = ⊏-gives-< m n l
 where
  l : m ⊏ ι n
  l = transport⁻¹ (λ - → - ⊏ ι n) (ℕ-to-ℕ∞-lc p) l'

{- TODO

<-gives-≺ : (m n : ℕ) → ι m ≺ ι n → m < n
<-gives-≺ = ?

⊏-gives-≺ : (m : ℕ) (u : ℕ∞) → m ⊏ u → ι m ≺ u
⊏-gives-≺ = ?
-}

\end{code}

Added 25 June 2018. This may be placed somewhere else in the future.
Another version of N∞, to be investigated.

\begin{code}

Ν∞ : 𝓤₁ ̇
Ν∞ = Σ A ꞉ (ℕ → Ω 𝓤₀), ((n : ℕ) → A (n ∔ 1) holds → A n holds)

\end{code}

Needed 28 July 2018:

\begin{code}

≼-is-prop-valued : funext₀ → (u v : ℕ∞) → is-prop (u ≼ v)
≼-is-prop-valued fe u v = Π-is-prop fe (λ n → Π-is-prop fe (λ l → 𝟚-is-set))

≼-not-≺ : (u v : ℕ∞) → u ≼ v → ¬ (v ≺ u)
≼-not-≺ u v l (n , (p , m)) = zero-is-not-one (e ⁻¹ ∙ d)
 where
  a : v ≺ u
  a = transport (λ - → - ≺ u) (p ⁻¹) (⊏-gives-≺ n u m)

  k : ℕ
  k = pr₁ a

  b : v ＝ ι k
  b = pr₁ (pr₂ a)

  c : k ⊏ v
  c = l k (pr₂ (pr₂ a))

  d : ι (ι k) k ＝ ₁
  d = transport (λ - → k ⊏ -) b c

  e : ι (ι k) k ＝ ₀
  e = ℕ-to-ℕ∞-diagonal₀ k

not-≺-≼ : funext₀ → (u v : ℕ∞) → ¬ (v ≺ u) → u ≼ v
not-≺-≼ fe u v φ n l = 𝟚-equality-cases f g
 where
  f : v ⊑ n → n ⊏ v
  f m = 𝟘-elim (φ (k , (p , b)))
   where
    k : ℕ
    k = pr₁ (ℕ-to-ℕ∞-lemma fe v n m)

    a : k ≤ n
    a = pr₁ (pr₂ (ℕ-to-ℕ∞-lemma fe v n m))

    p : v ＝ ι k
    p = pr₂ (pr₂ (ℕ-to-ℕ∞-lemma fe v n m))

    b : k ⊏ u
    b = ⊏-trans'' u n k a l

  g : n ⊏ v → n ⊏ v
  g = id

\end{code}

Characterization of ⊏.

\begin{code}

⊏-positive : (n : ℕ) (u : ℕ∞) → n ⊏ u → is-positive u
⊏-positive n u = ⊏-trans'' u n 0 (zero-least n)

⊏-charac→ : funext₀
          → (n : ℕ) (u : ℕ∞)
          → n ⊏ u
          → Σ v ꞉ ℕ∞ , u ＝ (Succ ^ (n ∔ 1)) v
⊏-charac→ fe₀ 0        u l = Pred u , (positive-equal-Succ fe₀ l)
⊏-charac→ fe₀ (succ n) u l = γ
 where
  IH : Σ v ꞉ ℕ∞ , Pred u ＝ (Succ ^ (n ∔ 1)) v
  IH = ⊏-charac→ fe₀ n (Pred u) l

  v : ℕ∞
  v = pr₁ IH

  p : u ＝ (Succ ^ (n ∔ 2)) v
  p = u                   ＝⟨ positive-equal-Succ fe₀ (⊏-positive (n ∔ 1) u l) ⟩
      Succ (Pred u)       ＝⟨ ap Succ (pr₂ IH) ⟩
      (Succ ^ (n ∔ 2)) v  ∎

  γ : Σ v ꞉ ℕ∞ , u ＝ (Succ ^ (n ∔ 2)) v
  γ = v , p

⊏-charac← : funext₀ → (n : ℕ) (u : ℕ∞)
           → (Σ v ꞉ ℕ∞ , u ＝ (Succ ^ (n ∔ 1)) v) → n ⊏ u
⊏-charac← fe₀ 0        u (v , refl) = refl
⊏-charac← fe₀ (succ n) u (v , refl) = γ
 where
  IH : n ⊏ Pred u
  IH = ⊏-charac← fe₀ n (Pred u) (v , refl)

  γ : n ∔ 1 ⊏ u
  γ = IH

\end{code}

Added 19th April 2022.

\begin{code}

bounded-is-finite : funext₀
                  → (n : ℕ) (u : ℕ∞)
                  → u ⊑ n
                  → is-finite u
bounded-is-finite fe n u le = case ℕ-to-ℕ∞-lemma fe u n le of
                               (λ (m , _ , p) → m , (p ⁻¹))

⊑-succ-gives-≺ : funext₀
               → (n : ℕ) (u : ℕ∞)
               → u ⊑ n
               → u ≺ ι (succ n)
⊑-succ-gives-≺ fe n u les = f (ℕ-to-ℕ∞-lemma fe u n les)
 where
  f : (Σ m ꞉ ℕ , (m ≤ n) × (u ＝ ι m)) → u ≺ ι (succ n)
  f (m , le , p) = m , p , a
   where
    a : m ⊏ ι (succ n)
    a = <-gives-⊏ m (succ n) le

finite-trichotomous : funext₀
                    → (n : ℕ) (u : ℕ∞)
                    → (ι n ≺ u) + (ι n ＝ u) + (u ≺ ι n)
finite-trichotomous fe 0 u =
 𝟚-equality-cases
  (λ (l : is-Zero u) → inr (inl ((is-Zero-equal-Zero fe l)⁻¹)))
  (λ (m : is-positive u)
        → inl (⊏-gives-≺ 0 u m))
finite-trichotomous fe (succ n) u =
 𝟚-equality-cases
  (λ (l : u ⊑ succ n) →
        𝟚-equality-cases
         (λ (a : u ⊑ n) → inr (inr (⊑-succ-gives-≺ fe n u a)))
         (λ (b : n ⊏ u) → inr (inl ((Succ-criterion fe b l)⁻¹))))
  (λ (m : succ n ⊏ u) → inl (⊏-gives-≺ (succ n) u m))

\end{code}

TODO. Move the following to a sepatate file.

Added 14th January 2022, with various additions in November 2023.

We now develop an automorphism of the Cantor type ℕ → 𝟚 which
induces an equivalent copy of ℕ∞.

The function ϕ restricts to an equivalence between ℕ∞ and the subtype

     Σ α ꞉ (ℕ → 𝟚) , is-prop (Σ n ꞉ ℕ , α n ＝ ₁)

of the Cantor type (the sequences with at most one ₁).

Notice that the condition on α can be expressed as "is-prop (fiber α ₁)".

\begin{code}

T-cantor : (ℕ → 𝟚) → 𝓤₀ ̇
T-cantor α = Σ n ꞉ ℕ , α n ＝ ₁

private
 T : (ℕ → 𝟚) → 𝓤₀ ̇
 T = T-cantor

has-at-most-one-₁ : (ℕ → 𝟚) → 𝓤₀ ̇
has-at-most-one-₁ α = is-prop (T α)

has-at-most-one-₁-is-prop : funext₀ → (α : ℕ → 𝟚) → is-prop (has-at-most-one-₁ α)
has-at-most-one-₁-is-prop fe α = being-prop-is-prop fe

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

\end{code}

The following is the isomorphic copy of ℕ∞ alluded above.

\begin{code}

ℕ∞' : 𝓤₀ ̇
ℕ∞' = Σ α ꞉ (ℕ → 𝟚) , has-at-most-one-₁ α

ℕ∞'-to-ℕ→𝟚 : ℕ∞' → (ℕ → 𝟚)
ℕ∞'-to-ℕ→𝟚 = pr₁

private
 instance
  canonical-map-ℕ∞'-ℕ→𝟚 : Canonical-Map ℕ∞' (ℕ → 𝟚)
  ι {{canonical-map-ℕ∞'-ℕ→𝟚}} = ℕ∞'-to-ℕ→𝟚

ℕ∞'-to-ℕ→𝟚-prop : (u : ℕ∞') → is-prop (T (ℕ∞'-to-ℕ→𝟚 u))
ℕ∞'-to-ℕ→𝟚-prop = pr₂

Zero' : ℕ∞'
Zero' = α , h
 where
  α : ℕ → 𝟚
  α 0        = ₁
  α (succ n) = ₀

  i : is-prop (T α)
  i (0 , e) (0 , e') = to-T-＝ refl

  h : has-at-most-one-₁ α
  h (n , e) (n' , e') = to-subtype-＝ (λ - → 𝟚-is-set) (index-uniqueness α i e e')

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
is-finite' u = T (ℕ∞'-to-ℕ→𝟚 u)

Zero'-is-finite : is-finite' Zero'
Zero'-is-finite = 0 , refl

finiteness'-preservation : (u : ℕ∞')
                          → is-finite' u
                          → is-finite' (Succ' u)
finiteness'-preservation _ (n , e) = succ n , e

ℕ-to-ℕ∞'-is-finite' : (n : ℕ) → is-finite' (ι n)
ℕ-to-ℕ∞'-is-finite' 0        = Zero'-is-finite
ℕ-to-ℕ∞'-is-finite' (succ n) = finiteness'-preservation (ι n)
                                (ℕ-to-ℕ∞'-is-finite' n)

∞' : ℕ∞'
∞' = (λ _ → ₀) , (λ (n , e) (n' , e') → 𝟘-elim (zero-is-not-one e))

∞'-is-not-finite : ¬ is-finite' ∞'
∞'-is-not-finite (n , e) = zero-is-not-one e

\end{code}

To show that ℕ∞' gives an equivalent copy of ℕ∞, we consider a
particular equivalence (ℕ → 𝟚) ≃ (ℕ → 𝟚).

\begin{code}

ϕ-cantor γ-cantor : (ℕ → 𝟚) → (ℕ → 𝟚)

ϕ-cantor α n = cons ₁ α n ⊕ α n

γ-cantor β 0        = complement (β 0)
γ-cantor β (succ n) = γ-cantor β n ⊕ β (n ∔ 1)

private
 ϕ γ : (ℕ → 𝟚) → (ℕ → 𝟚)
 ϕ = ϕ-cantor
 γ = γ-cantor

η-cantor : (β : ℕ → 𝟚) → ϕ (γ β) ∼ β
η-cantor β 0        = complement-involutive (β 0)
η-cantor β (succ n) = ⊕-involutive {γ β n} {β (n ∔ 1)}

ε-cantor : (α : ℕ → 𝟚) → γ (ϕ α) ∼ α
ε-cantor α 0        = complement-involutive (α 0)
ε-cantor α (succ n) = γ (ϕ α) (n ∔ 1)             ＝⟨ refl ⟩
                      γ (ϕ α) n ⊕ α n ⊕ α (n ∔ 1) ＝⟨ I ⟩
                      α n ⊕ α n ⊕ α (n ∔ 1)       ＝⟨ II ⟩
                      α (n ∔ 1)                   ∎
 where
  I  = ap (_⊕ α n ⊕ α (succ n)) (ε-cantor α n)
  II = ⊕-involutive {α n} {α (n ∔ 1)}

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
ϕ-property fe α δ (0 , p) (0 ,      q) = to-subtype-＝ (λ _ → 𝟚-is-set) refl
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

  III : (α m ＝ ₁) × (α (m ∔ 1) ＝ ₀)
  III = ⊕-property₁ {α m} {α (m ∔ 1)} (δ m) q

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

  III : (α n ＝ ₁) × (α (n ∔ 1) ＝ ₀)
  III = ⊕-property₁ {α n} {α (n ∔ 1)} (δ n) p

  IV : u ＝ Succ (ι n)
  IV = uncurry (Succ-criterion fe) III

ϕ-property fe α δ (succ n , p) (succ m , q) = VI
 where
  u : ℕ∞
  u = (α , δ)

  I : (α n ＝ ₁) × (α (n ∔ 1) ＝ ₀)
  I = ⊕-property₁ (δ n) p

  II : (α m ＝ ₁) × (α (m ∔ 1) ＝ ₀)
  II = ⊕-property₁ (δ m) q

  III : u ＝ Succ (ι n)
  III = uncurry (Succ-criterion fe) I

  IV : u ＝ Succ (ι m)
  IV = uncurry (Succ-criterion fe) II

  V : n ∔ 1 ＝ m ∔ 1
  V = ℕ-to-ℕ∞-lc (III ⁻¹ ∙ IV)

  VI : (n ∔ 1 , p) ＝ (m ∔ 1 , q)
  VI = to-subtype-＝ (λ _ → 𝟚-is-set) V

\end{code}

The following two observations give an alternative understanding of
the definition of γ:

\begin{code}

γ-case₀ : {β : ℕ → 𝟚} {n : ℕ}
        → β (n ∔ 1) ＝ ₀ → γ β (n ∔ 1) ＝ γ β n
γ-case₀ = ⊕-₀-right-neutral'

γ-case₁ : {β : ℕ → 𝟚} {n : ℕ}
        → β (n ∔ 1) ＝ ₁ → γ β (n ∔ 1) ＝ complement (γ β n)
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
at-most-one-₁-Lemma₁ β π {m} {n} ν p = w
 where
  I : β n ≠ ₁
  I q = ν (at-most-one-₁-Lemma₀ β π (p , q))

  w : β n ＝ ₀
  w = different-from-₁-equal-₀ I

\end{code}

The main lemma about γ is the following, where we are interested in
the choice k = n, but we need to prove the lemma for general k to get
a suitable induction hypothesis.

\begin{code}

γ-lemma : (β : ℕ → 𝟚)
        → has-at-most-one-₁ β
        → (n : ℕ) → β (n ∔ 1) ＝ ₁ → (k : ℕ) → k ≤ n → γ β k ＝ ₁
γ-lemma β π n p 0 l = w
 where
  w : complement (β 0) ＝ ₁
  w = complement-intro₀ (at-most-one-₁-Lemma₁ β π (positive-not-zero n) p)

γ-lemma β π 0 p (succ k) ()
γ-lemma β π (succ n) p (succ k) l = w
 where
  IH : γ β k ＝ ₁
  IH = γ-lemma β π (n ∔ 1) p k (≤-trans k n (n ∔ 1) l (≤-succ n))

  I : n ∔ 2 ≠ succ k
  I m = not-less-than-itself n r
   where
    q : n ∔ 1 ＝ k
    q = succ-lc m

    r : n ∔ 1 ≤ n
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
  I : β (n ∔ 1) ＝ ₁ → γ β n ＝ ₁
  I p = γ-lemma β π n p n (≤-refl n)

  II : β (n ∔ 1) ≤ γ β n
  II = ≤₂-criterion I

  III : γ β n ⊕ β (n ∔ 1) ≤ γ β n
  III = ≤₂-add-left (γ β n) (β (n ∔ 1)) II

  IV : γ β (n ∔ 1) ≤ γ β n
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

 finite-preservation : (n : ℕ) → ℕ∞-to-ℕ∞' (ℕ-to-ℕ∞ n) ＝ ℕ-to-ℕ∞' n
 finite-preservation 0        = Zero-preservation
 finite-preservation (succ n) =
  ℕ∞-to-ℕ∞' (ℕ-to-ℕ∞ (succ n)) ＝⟨ refl ⟩
  ℕ∞-to-ℕ∞' (Succ (ℕ-to-ℕ∞ n)) ＝⟨ Succ-preservation (ℕ-to-ℕ∞ n) ⟩
  Succ' (ℕ∞-to-ℕ∞' (ι n))      ＝⟨ ap Succ' (finite-preservation n) ⟩
  Succ' (ℕ-to-ℕ∞' n)           ＝⟨ refl ⟩
  ℕ-to-ℕ∞' (succ n)            ∎

\end{code}
