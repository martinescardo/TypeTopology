Martin Escardo, 5-28 April 2026.

The set of decreasing sequences of natural numbers bounded by a
natural number k is compact, aka searchable, and also totally
separated. That is, it is a Stone type. This is because it is
isomorphic to another set we know to be compact. This doesn't require
univalence. Our only assumption is function extensionality. And total
separatedness follows directly from previous results.

This result was first announced at 7FWTop [1], before the formal proof in
Agda was completed, although the informal construction was already in
this file at that time in mathematical vernacular (see below).

[1] https://martinescardo.github.io/.talks/escardo-venice2026-stone-types.pdf

In any case, we don't obtain any new compact type here. Just a
different, perhaps more appealing, isomorphic copy.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_+_)
open import UF.FunExt

module TypeTopology.BoundedDecreasingSequences (fe : Fun-Ext) where

open import CoNaturals.Type
open import MLTT.Two-Properties
open import Naturals.Addition
open import Naturals.Order
open import Naturals.Subtraction
open import Notation.CanonicalMap
open import Notation.Order
open import TypeTopology.CompactTypes
open import TypeTopology.GenericConvergentSequenceCompactness
open import TypeTopology.MicroTychonoff
open import TypeTopology.SquashedCantor (λ 𝓤 𝓥 → fe {𝓤} {𝓥})
open import TypeTopology.SquashedSum
open import TypeTopology.TotallySeparated
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

We first define the type of decreasing sequences of natural numbers
bounded by a natural number k.

\begin{code}

is-bounded-by : ℕ → (ℕ → ℕ) → 𝓤₀ ̇
is-bounded-by k α = (n : ℕ) → α n ≤ k

\end{code}

In the following "decreasing" means non-strictly decreasing. We call
it `is-decreasing'` because `is-decreasing` is already taken and
needed here, for non-strictly decreasing binary sequences.

\begin{code}

is-decreasing' : (ℕ → ℕ) → 𝓤₀ ̇
is-decreasing' α = (n : ℕ) → α n ≥ α (succ n)

\end{code}

The following immediate consequence of the above condition is going to
be useful below.

\begin{code}

is-decreasing'' : (β : ℕ → ℕ)
                → is-decreasing' β
                → (n₀ n : ℕ)
                → β n₀ ≥ β (n₀ + n)
is-decreasing'' β δ n₀ 0        = ≤-refl (β n₀)
is-decreasing'' β δ n₀ (succ n) =
 ≤-trans (β (n₀ + succ n)) (β (n₀ + n)) (β n₀)
  (δ (n₀ + n))
  (is-decreasing'' β δ n₀ n)

\end{code}

We now combine the two notions to get the type 𝔹 k of sequences
bounded by k.

\begin{code}

is-bd : ℕ → (ℕ → ℕ) → 𝓤₀ ̇
is-bd k α = is-bounded-by k α × is-decreasing' α

being-bounded-by-is-prop : (k : ℕ) (α : ℕ → ℕ) → is-prop (is-bounded-by k α)
being-bounded-by-is-prop k α = Π-is-prop fe (λ n → ≤-is-prop-valued (α n) k)

being-decreasing'-is-prop : (α : ℕ → ℕ) → is-prop (is-decreasing' α)
being-decreasing'-is-prop α = Π-is-prop fe
                               (λ n → ≤-is-prop-valued (α (succ n)) (α n))

being-bd-is-prop : (k : ℕ) (α : ℕ → ℕ) → is-prop (is-bd k α)
being-bd-is-prop k α = ×-is-prop
                        (being-bounded-by-is-prop k α)
                        (being-decreasing'-is-prop α)

𝔹 : ℕ → 𝓤₀ ̇
𝔹 k = Σ α ꞉ (ℕ → ℕ) , is-bd k α

\end{code}

We now name some projections for the sake of clarity.

\begin{code}

𝔹-sequence : {k : ℕ} → 𝔹 k → (ℕ → ℕ)
𝔹-sequence (α , _ , _) = α

\end{code}

We use the overloaded canonical-map notation ι to denote the
underlying sequence of an element of 𝔹 k.

\begin{code}

module _ {k : ℕ} where
 instance
  canonical-map-𝔹-ℕ→ℕ : Canonical-Map (𝔹 k) (ℕ → ℕ)
  ι {{canonical-map-𝔹-ℕ→ℕ}} = 𝔹-sequence {k}

\end{code}

With this notation, we continue to name the projections.

\begin{code}

𝔹-is-bounded-by : {k : ℕ}
                  (𝕓 : 𝔹 k)
                → is-bounded-by k (ι 𝕓)
𝔹-is-bounded-by (_ , b , _) = b

\end{code}

We will let δ range over witnesses of `is-decreasing'`.

\begin{code}

𝔹-is-decreasing' : {k : ℕ}
                   (𝕓 : 𝔹 k)
                 → is-decreasing' (ι 𝕓)
𝔹-is-decreasing' (_ , _ , δ) = δ

\end{code}

The following equality criterion of elements of the type 𝔹 k amounts
to the pointwise injectivity of the inclusion map of 𝔹 k into the
Baire type (ℕ → ℕ).

\begin{code}

to-𝔹-＝ : {k : ℕ}
          (𝕓 𝕓' : 𝔹 k)
        → ι 𝕓 ∼ ι 𝕓'
        → 𝕓 ＝ 𝕓'
to-𝔹-＝ {k} (α , _) (β , _) h = to-subtype-＝ (being-bd-is-prop k) (dfunext fe h)

\end{code}

We now define 𝓑 k = 𝔻ᵏ 𝟙 by induction on k, where 𝔻 is the delay monad
defined in the module SquashedCantor. Our objective is to eventually
show that 𝔹 k ≃ 𝓑 k, in order to derive the claims made above as a
corollary.

\begin{code}

𝓑 : ℕ → 𝓤₀ ̇
𝓑 0        = 𝟙
𝓑 (succ k) = 𝔻 (𝓑 k )

𝔻-preserves-compactness∙ : (X : 𝓤 ̇ )
                         → is-compact∙ X
                         → is-compact∙ (𝔻 X)
𝔻-preserves-compactness∙ X κ =
 Σ-is-compact∙
  (ℕ∞-compact∙ fe)
  (λ u → micro-tychonoff fe (being-finite-is-prop fe u) (λ _ → κ))

𝔻-preserves-totally-separatedness : (X : 𝓤 ̇ )
                                  → is-totally-separated X
                                  → is-totally-separated (𝔻 X)
𝔻-preserves-totally-separatedness X τ =
 Σ¹-is-totally-separated (λ 𝓤 𝓥 → fe {𝓤} {𝓥}) (λ _ → X) (λ _ → τ)

𝓑-is-compact∙ : (k : ℕ) → is-compact∙ (𝓑 k)
𝓑-is-compact∙ zero     = 𝟙-is-compact∙
𝓑-is-compact∙ (succ k) = 𝔻-preserves-compactness∙ (𝓑 k) (𝓑-is-compact∙ k)

𝔻-preserves-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → 𝔻 X ≃ 𝔻 Y
𝔻-preserves-≃ e = Σ-cong (λ u → Π-cong fe fe (λ φ → e))

𝔹-base : 𝔹 0 ≃ 𝟙 {𝓤}
𝔹-base = singleton-≃-𝟙
          (((λ _ → 0) , unique-to-𝟙 , unique-to-𝟙) ,
          (λ (α , b , d) → to-𝔹-＝ _ _ (λ n → (zero-least'' (α n) (b n))⁻¹)))

\end{code}

The main result of this file is the following, where 𝔹-step, defined
later, is the main tool.

\begin{code}

𝔹-step : (k : ℕ) → 𝔹 (succ k) ≃ 𝔻 (𝔹 k)

𝔹-and-𝓑-are-equivalent : (k : ℕ) → 𝔹 k ≃ 𝓑 k
𝔹-and-𝓑-are-equivalent 0        = 𝔹-base
𝔹-and-𝓑-are-equivalent (succ k) =
 𝔹 (succ k) ≃⟨ 𝔹-step k ⟩
 𝔻 (𝔹 k)    ≃⟨ 𝔻-preserves-≃ (𝔹-and-𝓑-are-equivalent k) ⟩
 𝔻 (𝓑 k)    ≃⟨ ≃-refl _ ⟩
 𝓑 (succ k) ■

\end{code}

With this we conclude that 𝔹 k ≃ 𝓑 k and hence 𝔹 k is compact, which
is what we wanted to show in this file.

\begin{code}

𝔹-is-compact∙ : (k : ℕ) → is-compact∙ (𝔹 k)
𝔹-is-compact∙ k = compact∙-types-are-closed-under-equiv
                   (≃-sym (𝔹-and-𝓑-are-equivalent k))
                   (𝓑-is-compact∙ k)
\end{code}

We now construct the claimed isomorphism 𝔹-step : 𝔹 (succ k) ≃ 𝔻 (𝔹 k)
as follows.

 (→) Given a non-increasing sequence β : ℕ → ℕ, we define α : ℕ → 𝟚 by

      α n = ₁ iff β n = succ k

     This is decreasing, and hence gives an element x of ℕ∞.

     Now assume x is finite. This means that there is a minimal n₀ such
     that α n₀ = ₀.

     We define an element of 𝔹 k with underlying sequence γ : ℕ → ℕ defined by

      γ n = β (n + n₀),

     which is bounded by k and is non-increasing.

 (←) To undo this, given α : ℕ → 𝟚 decreasing for x : ℕ∞ and
     𝕓 : is-finite x → B k, we define

     β n = succ k if α n = ₁
           𝕓 (n₀ , e₀) (n - n₀) otherwise,

     where n₀ is the minimal number with n₀ ≤ n and e₀ : α n₀ = 0.

The formal construction in Agda is rather laborious but routine.

Minor remark. It would have been slightly better to instead define
γ n = β (n₀ + n). This would have saved us from applying commutativity of
addition twice. But it would also require slightly changing other
things. So we'll leave it at that.

We begin with the following transport lemma, which is a generalization
of `transport-finite` in the module SquashedCantor, will be crucial
for our purposes, but will be used much later.

\begin{code}

transport-is-finite
 : {k : ℕ}
   {u v : ℕ∞}
   (q : u ＝ v)
   (π : is-finite u → 𝔹 k)
   (φ : is-finite v)
 → transport (λ - → is-finite - → 𝔹 k) q π φ ＝ π (transport is-finite (q ⁻¹) φ)
transport-is-finite refl h φ = refl

\end{code}

We now proceed to the proof of 𝔹-step, which, in turn, requires many steps itself.

\begin{code}

𝔹-step k = qinveq f (g , gf , fg)
 where

\end{code}

We begin with auxiliary constructions and lemmas for the forward direction.

\begin{code}

  α-of : (ℕ → ℕ) → (ℕ → 𝟚)
  α-of β n = χ＝ (β n) (succ k)

  module _ (β : ℕ → ℕ) (n : ℕ) where

   α-of-₁ : β n ＝ succ k → α-of β n ＝ ₁
   α-of-₁ e = different-from-₀-equal-₁
               (λ s → pr₁ (χ＝-spec (β n) (succ k)) s e)

   α-of-₁-converse : α-of β n ＝ ₁ → β n ＝ succ k
   α-of-₁-converse p = pr₂ (χ＝-spec (β n) (succ k)) p

   α-of-₀ : α-of β n ＝ ₀ → β n ≠ succ k
   α-of-₀ p = pr₁ (χ＝-spec (β n) (succ k)) p

   α-of-₀-converse : β n ≠ succ k → α-of β n ＝ ₀
   α-of-₀-converse ne = different-from-₁-equal-₀
                         (λ p → ne (α-of-₁-converse p))

   α-equals-₀-gives-bounded : is-bounded-by (succ k) β
                            → α-of β n ＝ ₀
                            → β n ≤ k
   α-equals-₀-gives-bounded b p = ≤-down (β n) k (b n) (α-of-₀ p)

  α-of-decreasing : (β : ℕ → ℕ)
                  → is-bounded-by (succ k) β
                  → is-decreasing' β
                  → is-decreasing (α-of β)
  α-of-decreasing β b δ n = ≤₂-criterion IV
   where
    IV : α-of β (succ n) ＝ ₁ → α-of β n ＝ ₁
    IV p = α-of-₁ β n III
     where
      I : β (succ n) ＝ succ k
      I = α-of-₁-converse β (succ n) p

      II : succ k ≤ β n
      II = transport (_≤ β n) I (δ n)

      III : β n ＝ succ k
      III = ≤-anti (β n) (succ k) (b n) II

  u-of : 𝔹 (succ k) → ℕ∞
  u-of (β , b , δ) = α-of β , α-of-decreasing β b δ

  α-₀-criterion : (𝕓 : 𝔹 (succ k)) (φ : is-finite (u-of 𝕓))
                → α-of (ι 𝕓) (size φ) ＝ ₀
  α-₀-criterion (β , _ , _) (n₀ , e) =
   α-of β n₀    ＝⟨ ap (λ - → ι - n₀) (e ⁻¹) ⟩
   ι (ι n₀) n₀  ＝⟨ ℕ-to-ℕ∞-diagonal₀ n₀ ⟩
   ₀            ∎

  π-of : (𝕓 : 𝔹 (succ k)) → is-finite (u-of 𝕓) → 𝔹 k
  π-of 𝕓@(β , b , δ) φ = γ , II , III
    where
     n₀ : ℕ
     n₀ = size φ

     γ : ℕ → ℕ
     γ n = β (n₀ + n)

     I : β n₀ ≤ k
     I = α-equals-₀-gives-bounded β n₀ b (α-₀-criterion 𝕓 φ)

     II : is-bounded-by k γ
     II n = ≤-trans (β (n₀ + n)) (β n₀) k (is-decreasing'' β δ n₀ n) I

     III : is-decreasing' γ
     III n = δ (n₀ + n)

\end{code}

With this, we can complete the definition of the forward direction,
but also notice that the above constructions and lemmas will also be
useful to prove that it has a two-sided inverses.

\begin{code}

  f : 𝔹 (succ k) → 𝔻 (𝔹 k)
  f 𝕓 = u-of 𝕓 , π-of 𝕓

\end{code}

For the backward direction we again start with some auxiliary
constructions and lemmas.

\begin{code}

  module _ (n : ℕ) (u : ℕ∞) (e : ι u n ＝ ₀) where

   φ-of : is-finite u
   φ-of = case ℕ-to-ℕ∞-lemma fe u n e of
           λ (m , _ , p) → (m , (p ⁻¹))

   d-of : ℕ
   d-of = case ℕ-to-ℕ∞-lemma fe u n e of
           λ (m , le , _) → pr₁ (subtraction m n le)

   φd-property : d-of + size φ-of ＝ n
   φd-property = case ℕ-to-ℕ∞-lemma fe u n e of
                  λ (m , le , _) → pr₂ (subtraction m n le)

  module _ (u : ℕ∞) (π : is-finite u → 𝔹 k) (n : ℕ) where

   β-of : ℕ
   β-of = 𝟚-equality-cases
           (λ (e : ι u n ＝ ₀) → ι (π (φ-of n u e)) (d-of n u e))
           (λ (_ : ι u n ＝ ₁) → succ k)

   β-of-at-₀ : (e : ι u n ＝ ₀)
             → β-of ＝ ι (π (φ-of n u e)) (d-of n u e)
   β-of-at-₀ = 𝟚-equality-cases₀

   β-of-at-₁ : ι u n ＝ ₁
             → β-of ＝ succ k
   β-of-at-₁ = 𝟚-equality-cases₁

  β-of-at-finite : (u : ℕ∞)
                   (π : is-finite u → 𝔹 k)
                   (n : ℕ)
                   (φ@(n₀ , e₀) : is-finite u)
                   (e : ι u (n₀ + n) ＝ ₀)
                 → β-of u π (n₀ + n) ＝ ι (π φ) n
  β-of-at-finite u π n φ@(n₀ , e₀) e =
   β-of u π (n₀ + n) ＝⟨ β-of-at-₀ u π (n₀ + n) e ⟩
   ι (π φ') d        ＝⟨ ap (ι (π φ')) IV ⟩
   ι (π φ') n        ＝⟨ ap (λ - → ι (π -) n) I ⟩
   ι (π φ) n         ∎
    where
     φ' : is-finite u
     φ' = φ-of (n₀ + n) u e

     d : ℕ
     d = d-of (n₀ + n) u e

     I : φ' ＝ φ
     I = being-finite-is-prop fe u _ _

     II : size φ' ＝ n₀
     II = ap size I

     III = n₀ + d      ＝⟨ addition-commutativity n₀ d ⟩
           d + n₀      ＝⟨ ap (d +_) (II ⁻¹) ⟩
           d + size φ' ＝⟨ φd-property (n₀ + n) u e ⟩
           n₀ + n      ∎

     IV : d ＝ n
     IV = addition-left-cancellable d n n₀ III

  β-of-bd : (u : ℕ∞)
            (π : is-finite u → 𝔹 k)
          → is-bounded-by (succ k) (β-of u π)
  β-of-bd u π n = 𝟚-equality-cases bd₀ bd₁
   where
    bd₀ : ι u n ＝ ₀ → β-of u π n ≤ succ k
    bd₀ e = transport (_≤ succ k) (I ⁻¹) III
     where
      φ : is-finite u
      φ = φ-of n u e

      d : ℕ
      d = d-of n u e

      I : β-of u π n ＝ ι (π φ) d
      I = β-of-at-₀ u π n e

      II : ι (π φ) d ≤ k
      II = 𝔹-is-bounded-by (π φ) d

      III : ι (π φ) d ≤ succ k
      III = ≤-trans (ι (π φ) d) k (succ k) II (≤-succ k)

    bd₁ : ι u n ＝ ₁ → β-of u π n ≤ succ k
    bd₁ p = transport (_≤ succ k) ((β-of-at-₁ u π n p) ⁻¹) (≤-refl (succ k))

  β-of-decr : (u : ℕ∞) (π : is-finite u → 𝔹 k)
            → is-decreasing' (β-of u π)
  β-of-decr u π n = 𝟚-equality-cases I₀ I₁
   where
    I₀ : ι u (succ n) ＝ ₀ → β-of u π (succ n) ≤ β-of u π n
    I₀ z' = 𝟚-equality-cases
             (λ (z : ι u n ＝ ₀) → II₀ z' z)
             (λ (p : ι u n ＝ ₁) → II₁ z' p)
     where
      II₀ : ι u (succ n) ＝ ₀
          → ι u n ＝ ₀
          → β-of u π (succ n) ≤ β-of u π n
      II₀ e' e = transport₂ _≤_ (III' ⁻¹) (III ⁻¹) XIV
       where
        φ' : is-finite u
        φ' = φ-of (succ n) u z'

        d' : ℕ
        d' = d-of (succ n) u z'

        φ : is-finite u
        φ = φ-of n u e

        d : ℕ
        d = d-of n u e

        III' : β-of u π (succ n) ＝ ι (π φ') d'
        III' = β-of-at-₀ u π (succ n) z'

        III : β-of u π n ＝ ι (π φ) d
        III = β-of-at-₀ u π n e

        IV : φ' ＝ φ
        IV = being-finite-is-prop fe u φ' φ

        V : ι (π φ') ＝ ι (π φ)
        V = ap (λ - → ι (π -)) IV

        m  = size φ
        m' = size φ'

        VI : m' ＝ m
        VI = ap size IV

        VII : d + m ＝ n
        VII = φd-property n u e

        VIII : d' + m' ＝ succ n
        VIII = φd-property (succ n) u z'

        IX : d' + m ＝ succ n
        IX = transport (λ - → d' + - ＝ succ n) VI VIII

        X = d' + m       ＝⟨ IX ⟩
            succ n       ＝⟨ ap succ (VII ⁻¹) ⟩
            succ (d + m) ＝⟨ succ-left d m ⁻¹ ⟩
            succ d + m   ∎

        XI : d' ＝ succ d
        XI = addition-right-cancellable d' (succ d) m X

        XII : is-decreasing' (ι (π φ))
        XII = 𝔹-is-decreasing' (π φ)

        XIII = ι (π φ') d'       ＝⟨ ap (ι (π φ')) XI ⟩
               ι (π φ') (succ d) ＝⟨ ap (λ - → - (succ d)) V ⟩
               ι (π φ)  (succ d) ∎

        XIV : ι (π φ') d' ≤ ι (π φ) d
        XIV = transport (_≤ ι (π φ) d) (XIII ⁻¹) (XII d)

      II₁ : ι u (succ n) ＝ ₀ → ι u n ＝ ₁
          → β-of u π (succ n) ≤ β-of u π n
      II₁ z' p = transport (_≤ β-of u π n) (III ⁻¹) VI
       where
        φ' : is-finite u
        φ' = φ-of (succ n) u z'

        d' : ℕ
        d' = d-of (succ n) u z'

        III : β-of u π (succ n) ＝ ι (π φ') d'
        III = β-of-at-₀ u π (succ n) z'

        IV : ι (π φ') d' ≤ k
        IV = pr₁ (pr₂ (π φ')) d'

        V : β-of u π n ＝ succ k
        V = β-of-at-₁ u π n p

        VI : ι (π φ') d' ≤ β-of u π n
        VI = transport
              (ι (π φ') d' ≤_)
              (V ⁻¹)
              (≤-trans (ι (π φ') d') k (succ k) IV (≤-succ k))

    I₁ : ι u (succ n) ＝ ₁ → β-of u π (succ n) ≤ β-of u π n
    I₁ p' = 𝟚-equality-cases
             (λ (e : ι u n ＝ ₀)
                   → 𝟘-elim
                      (zero-is-not-one
                       (₀     ＝⟨ e ⁻¹ ⟩
                        ι u n ＝⟨ ≤₂-criterion-converse (pr₂ u n) p' ⟩
                        ₁     ∎)))
             (λ (p : ι u n ＝ ₁)
                   → transport₂ _≤_
                      ((β-of-at-₁ u π (succ n) p') ⁻¹)
                      ((β-of-at-₁ u π n p) ⁻¹)
                      (≤-refl (succ k)))

\end{code}

With this we can define an inver g of the function f defined above.

\begin{code}

  g : 𝔻 (𝔹 k) → 𝔹 (succ k)
  g (u , π) = β-of u π , β-of-bd u π , β-of-decr u π

\end{code}

We now show that f and g are mutually inverse.

\begin{code}

  gf : g ∘ f ∼ id
  gf 𝕓@(β , _ , _) = to-𝔹-＝ _ _ I
   where
    u : ℕ∞
    u = u-of 𝕓

    π : is-finite u → 𝔹 k
    π = π-of 𝕓

    I : (n : ℕ) → β-of u π n ＝ β n
    I n = 𝟚-equality-cases I₀ I₁
     where
      I₀ : ι u n ＝ ₀ → β-of u π n ＝ β n
      I₀ e =
       β-of u π n                      ＝⟨ β-of-at-₀ u π n e ⟩
       ι (π (φ-of n u e)) (d-of n u e) ＝⟨ refl ⟩
       β (m + d)                       ＝⟨ ap β II ⟩
       β n                             ∎
       where
        m : ℕ
        m = size (φ-of n u e)

        d : ℕ
        d = d-of n u e

        II = m + d ＝⟨ addition-commutativity m d ⟩
             d + m ＝⟨ φd-property n u e ⟩
             n     ∎

      I₁ : ι u n ＝ ₁ → β-of u π n ＝ β n
      I₁ p = β-of u π n ＝⟨ β-of-at-₁ u π n p ⟩
             succ k     ＝⟨ (α-of-₁-converse β n p) ⁻¹ ⟩
             β n        ∎

  fg : f ∘ g ∼ id
  fg 𝕕@(u , π) = to-Σ-＝ (IV , V)
   where
    β : ℕ → ℕ
    β = β-of u π

    I : is-bounded-by (succ k) β
    I = β-of-bd u π

    II : is-decreasing' β
    II = β-of-decr u π

    𝕕' : 𝔻 (𝔹 k)
    𝕕' = f (g 𝕕)

    u' : ℕ∞
    u' = 𝔻-time 𝕕'

    π' : is-finite u' → 𝔹 k
    π' = 𝔻-value 𝕕'

    III : (n : ℕ) → α-of β n ＝ ι u n
    III n = 𝟚-equality-cases III₀ III₁
     where
      III₀ : ι u n ＝ ₀ → α-of β n ＝ ι u n
      III₀ e = α-of β n  ＝⟨ α-of-₀-converse β n ⦅4⦆ ⟩
               ₀         ＝⟨ e ⁻¹ ⟩
               ι u n     ∎
       where
        φ : is-finite u
        φ = φ-of n u e

        d : ℕ
        d = d-of n u e

        ⦅1⦆ : β n ＝ ι (π φ) d
        ⦅1⦆ = β-of-at-₀ u π n e

        ⦅2⦆ : ι (π φ) d ≤ k
        ⦅2⦆ = pr₁ (pr₂ (π φ)) d

        ⦅3⦆ : β n ≤ k
        ⦅3⦆ = transport (_≤ k) (⦅1⦆ ⁻¹) ⦅2⦆

        ⦅4⦆ : β n ≠ succ k
        ⦅4⦆ r = not-less-than-itself k (transport (_≤ k) r ⦅3⦆)

      III₁ : ι u n ＝ ₁ → α-of β n ＝ ι u n
      III₁ p = α-of β n  ＝⟨ α-of-₁ β n (β-of-at-₁ u π n p) ⟩
               ₁         ＝⟨ p ⁻¹ ⟩
               ι u n     ∎

    IV : u' ＝ u
    IV = ℕ∞-to-ℕ→𝟚-lc fe (dfunext fe III)

    V : transport (λ - → is-finite - → 𝔹 k) IV π' ＝ π
    V = dfunext fe V₁
     where
      module _ (φ@(n₀ , e₀) : is-finite u) where

       φ' φ'' : is-finite u'
       φ'  = n₀ , (e₀ ∙ IV ⁻¹)
       φ'' = transport is-finite (IV ⁻¹) φ

       V₀ : (n : ℕ) → ι (π' φ') n ＝ ι (π φ) n
       V₀ n = ι (π' φ') n ＝⟨ refl ⟩
              β (n₀ + n)  ＝⟨ β-of-at-finite u π n φ (+-stays-zero u n₀ e₀ n) ⟩
              ι (π φ) n   ∎

       V₁ = transport (λ - → is-finite - → 𝔹 k) IV π' φ ＝⟨ ⦅1⦆ ⟩
            π' φ''                                      ＝⟨ ⦅2⦆ ⟩
            π' φ'                                       ＝⟨ ⦅3⦆ ⟩
            π φ                                         ∎
        where
         ⦅1⦆ = transport-is-finite IV π' φ
         ⦅2⦆ = ap π' (being-finite-is-prop fe u' φ'' φ')
         ⦅3⦆ = to-𝔹-＝ _ _ V₀

\end{code}
