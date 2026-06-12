Martin Escardo, 10-12th June 2026.

We show that a supremum of totally separated ordinals doesn't need to
be totally separated itself, even if the ordinals are further assumed
to be compact and the index set is assumed to be compact and totally
separated.

The motivation for this comes from the file Ordinals.NotationInterpretation0,
where we interpret Brouwer ordinal codes as ordinals in four ways.

Recall that Brouwer ordinal codes are countably branching trees
inductively defined by constructors

  Z : 𝔹,
  S : 𝔹,
  L : (ℕ → 𝔹) → 𝔹.

The four interpretations are as follows.

(0) The standard interpretation, where Z denotes zero,
    S denotes successor, and L denotes supremum (least upper bound).

(1) Like the standard interpretation, but replacing the interpretation
    of Z by one, and that of L by the following construction. Given
    α : ℕ → Ordinal, we extend it to α̅ : ℕ∞ → Ordinal, using the
    injectivity of the type of ordinals, and then take the ordinal sum
    of α̅.

    The ordinals we get in this way are compact (or searchable) and
    totally separated.

(2) Like (1), but instead of taking the sum of α̅ we take its sup.

    Here we get compact ordinals, but it was an open question whether
    they are also totally separated.

    (†) We show that they are *not* totally separated in general,
        unless a certain amount of classical logic is available.

(3) Like (0), but we replace supremum by ordinal sum.

    Here we get countable trichotomous ordinals.

The simplest example for (†) is obtained by taking the constant
sequence αₙ = 2.  The supremum of the corresponding α̅ is the ordinal
of semidecidable propositions, where a proposition is below another
iff the former fails and the latter holds. Notice that this is the
restriction of the ordinal Ωₒ of propositions, defined in the file
Ordinals.OrdinalOfTruthValues, to the semidecidable propositions.

Classically the supremum is 𝟚ₒ, and indeed S ≃ₒ 𝟚ₒ iff every
semidecidable proposition is decidable, but we don't formalize this
here.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc

module Ordinals.FailureOfTotalSeparatedness
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open import UF.FunExt
open import UF.Subsingletons
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

open PropositionalTruncation pt

open import CoNaturals.Type
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Order
open import Notation.CanonicalMap
open import Notation.Order
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.Injectivity
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Size
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties

module _ (sr : Set-Replacement pt) where

 open suprema pt sr

 private
  extension : (ℕ → Ordinal 𝓤₀) → (ℕ∞ → Ordinal 𝓤₀)
  extension α = α ↗ (embedding-ℕ-to-ℕ∞ fe')
   where
    open ordinals-injectivity fe

\end{code}

As explained above, we work with constantly 2 sequence, called α
below.

\begin{code}

 α : ℕ → Ordinal 𝓤₀
 α _ = 𝟚ₒ

 α̅ : ℕ∞ → Ordinal 𝓤₀
 α̅ = extension α

 α̅∞ : Ordinal 𝓤₀
 α̅∞ = sup α̅

 ⟨α̅∞⟩-is-set : is-set ⟨ α̅∞ ⟩
 ⟨α̅∞⟩-is-set = underlying-type-is-set fe α̅∞

\end{code}

We work with the following alternative formulation of
semidecidability.  We don't bother to pause to show it is equivalent
to the standard definition, because all we need is an example for (†)
above, which we provide below.

TODO. In the future, do establish this equivalence formally, and
probably move all code for the alternative definition to the file
NotionsOfDecidability.SemiDecidable.

\begin{code}

 is-semidecidable : (X : 𝓤 ̇ ) → 𝓤 ̇
 is-semidecidable X = ∃ u ꞉ ℕ∞ , (X ↔ is-finite u)

 being-semidecidable-is-prop : (X : 𝓤 ̇ )
                             → is-prop (is-semidecidable X)
 being-semidecidable-is-prop X = ∃-is-prop

 𝟘-is-semidecidable : is-semidecidable 𝟘
 𝟘-is-semidecidable = ∣ ∞ , 𝟘-elim , (λ (n , p) → ∞-is-not-finite n (p ⁻¹)) ∣

 𝟙-is-semidecidable : is-semidecidable (𝟙 {𝓤})
 𝟙-is-semidecidable = ∣ Zero , (λ _ → 0 , refl) , (λ _ → ⋆) ∣

 𝕊 : 𝓤₁ ̇
 𝕊 = Σ p ꞉ Ω 𝓤₀ , is-semidecidable (p holds)

 ⊥ₛ ⊤ₛ : 𝕊
 ⊥ₛ = ⊥ , 𝟘-is-semidecidable
 ⊤ₛ = ⊤ , 𝟙-is-semidecidable

\end{code}

We can think of this as a Sierpinski type. We define the domain of
definition of an element of 𝕊 as follows.

\begin{code}

 δ : 𝕊 → Ω 𝓤₀
 δ = pr₁

\end{code}

We order the Sierpinski type as follows:

\begin{code}

 _≺ₛ_ : 𝕊 → 𝕊 → 𝓤₁ ̇
 s ≺ₛ s' = (δ s holds → 𝟘 {𝓤₁}) × (δ s' holds)

\end{code}

NB. We are deliberately making the order to live in the universe 𝓤₁,
rather than 𝓤₀, because its carrier already lives in 𝓤₁, for
simplicitly. A conclusion of our development, recorded below, is that
both 𝕊 and its order have a copy in 𝓤₀.

The Sierpinski type 𝕊 is a set, its equality is characterized by
logical equivalence of domains of definition, and ≺ₛ is a well-order,
all of which are immediate, although a bit laborious.

\begin{code}

 𝕊-is-set : is-set 𝕊
 𝕊-is-set = Σ-is-set (Ω-is-set fe' pe)
             (λ p → props-are-sets
                     (being-semidecidable-is-prop (p holds)))

 to-𝕊-＝ : (t t' : 𝕊)
         → (δ t holds ↔ δ t' holds)
         → t ＝ t'
 to-𝕊-＝ t t' (f , g) = to-subtype-＝
                         (λ p → being-semidecidable-is-prop (p holds))
                         (Ω-extensionality pe fe' f g)

 ≺ₛ-prop-valued : is-prop-valued _≺ₛ_
 ≺ₛ-prop-valued t t' = ×-is-prop
                        (Π-is-prop fe' (λ _ → 𝟘-is-prop))
                        (holds-is-prop (δ t'))

 ≺ₛ-transitive : is-transitive _≺ₛ_
 ≺ₛ-transitive t t' t'' (ν , _) (_ , h') = ν , h'

 ≺ₛ-extensional : is-extensional _≺ₛ_
 ≺ₛ-extensional t t' f g = to-𝕊-＝ t t' (I , II)
  where
   I : δ t holds → δ t' holds
   I s = pr₂ (f ⊥ₛ (𝟘-elim , s))

   II : δ t' holds → δ t holds
   II s' = pr₂ (g ⊥ₛ (𝟘-elim , s'))

 ≺ₛ-well-founded : is-well-founded _≺ₛ_
 ≺ₛ-well-founded t = acc (λ z (ν , _) → acc (λ w (_ , h) → 𝟘-elim (ν h)))

 𝓢 : Ordinal 𝓤₁
 𝓢 = 𝕊 , _≺ₛ_ , ≺ₛ-prop-valued ,
     ≺ₛ-well-founded , ≺ₛ-extensional , ≺ₛ-transitive

\end{code}

We now develop auxiliary constructions and lemmas. By definition, we
have that ⟨ 𝟚ₒ {𝓤₀} ⟩ ＝ 𝟙 + 𝟙, but the type 𝟚 is defined by
constructors ₀ and ₁.

\begin{code}

 pattern 𝟎 = inl ⋆
 pattern 𝟏 = inr ⋆

 ⊥ξ ⊤ξ : {u : ℕ∞} → ⟨ α̅ u ⟩
 ⊥ξ _ = 𝟎
 ⊤ξ _ = 𝟏

 𝟚ₒ-to-𝟚 : ⟨ 𝟚ₒ {𝓤₀} ⟩ → 𝟚
 𝟚ₒ-to-𝟚 𝟎 = ₀
 𝟚ₒ-to-𝟚 𝟏 = ₁

\end{code}

We will denote the above map by ι.

\begin{code}

 instance
  canonical-map-𝟚ₒ-𝟚 : Canonical-Map ⟨ 𝟚ₒ {𝓤₀} ⟩ 𝟚
  ι {{canonical-map-𝟚ₒ-𝟚}} = 𝟚ₒ-to-𝟚

 ≺-left : (x y : ⟨ 𝟚ₒ ⟩) → x ≺⟨ 𝟚ₒ ⟩ y → ι x ＝ ₀
 ≺-left 𝟎 𝟎 l = 𝟘-elim l
 ≺-left 𝟎 𝟏 l = refl
 ≺-left 𝟏 𝟎 l = 𝟘-elim l
 ≺-left 𝟏 𝟏 l = 𝟘-elim l

 ≺-right : (x y : ⟨ 𝟚ₒ ⟩) → x ≺⟨ 𝟚ₒ ⟩ y → ι y ＝ ₁
 ≺-right 𝟎 𝟎 l = 𝟘-elim l
 ≺-right 𝟎 𝟏 l = refl
 ≺-right 𝟏 𝟎 l = 𝟘-elim l
 ≺-right 𝟏 𝟏 l = 𝟘-elim l

 ≺-left-right : (x y : ⟨ 𝟚ₒ ⟩) → ι x ＝ ₀ → ι y ＝ ₁ → x ≺⟨ 𝟚ₒ ⟩ y
 ≺-left-right 𝟎 𝟎 e₀ e₁ = 𝟘-elim (zero-is-not-one e₁)
 ≺-left-right 𝟎 𝟏 e₀ e₁ = ⋆
 ≺-left-right 𝟏 𝟎 e₀ e₁ = 𝟘-elim (one-is-not-zero e₀)
 ≺-left-right 𝟏 𝟏 e₀ e₁ = 𝟘-elim (one-is-not-zero e₀)

\end{code}

For u : ℕ∞, an element of α̅ u is a function ξ : is-finite u → 𝟙 + 𝟙.
We convert it to a function ρ ξ : is-finite u → 𝟚. We let φ range
over the type is-finite u.

\begin{code}

 ρ : {u : ℕ∞} → ⟨ α̅ u ⟩ → (is-finite u → 𝟚)
 ρ ξ φ = ι (ξ φ)

 𝓕 : {u : ℕ∞} → ⟨ α̅ u ⟩ → 𝓤₀ ̇
 𝓕 ξ = fiber (ρ ξ) ₁

 𝓕-is-prop : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩) → is-prop (𝓕 ξ)
 𝓕-is-prop {u} ξ = Σ-is-prop (being-finite-is-prop fe' u) (λ φ → 𝟚-is-set)

\end{code}

For the purposes of the development below, we need to show that the
type 𝓕 ξ is semidecidable. To this end, we construct a conatural
number extent ξ : ℕ∞ that is finite if and only if 𝓕 ξ holds, so that
we get a map 𝔽 : ⟨ α̅ u ⟩ → 𝕊 such that 𝔽 ξ is the Sierpinski value of
the fiber of ξ over ₁.

\begin{code}

 raw-extent : {u : ℕ∞} → ⟨ α̅ u ⟩ → (ℕ → 𝟚)
 raw-extent {u} ξ m =
  𝟚-equality-cases
   (λ (e : ι u m ＝ ₀) → complement (ρ ξ (bounded-is-finite fe' m u e)))
   (λ (_ : ι u m ＝ ₁) → ₁)

 raw-extent-is-decreasing : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩)
                          → is-decreasing (raw-extent ξ)
 raw-extent-is-decreasing {u} ξ m = ≤₂-criterion I
  where
   I : raw-extent ξ (succ m) ＝ ₁ → raw-extent ξ m ＝ ₁
   I e₁ = h (ι u m) refl
    where
     h : (c : 𝟚) → ι u m ＝ c → raw-extent ξ m ＝ ₁
     h ₁ e = 𝟚-equality-cases₁ e
     h ₀ e =
      raw-extent ξ m
        ＝⟨ 𝟚-equality-cases₀ e ⟩
      complement (ρ ξ (bounded-is-finite fe' m u e))
        ＝⟨ ap (λ - → complement (ρ ξ -))
             (being-finite-is-prop fe' u
               (bounded-is-finite fe' m u e)
               (bounded-is-finite fe' (succ m) u (stays-zero u e))) ⟩
      complement (ρ ξ (bounded-is-finite fe' (succ m) u (stays-zero u e)))
        ＝⟨ (𝟚-equality-cases₀ (stays-zero u e))⁻¹ ⟩
      raw-extent ξ (succ m)
        ＝⟨ e₁ ⟩
      ₁ ∎

\end{code}

NB. If we write the above chain of equations in the usual TypeTopology
style, e.g. using roman numbers for the equality proofs defined in a
`where` clause (as in some examples below), then we get a number of
unsolved constraints.

\begin{code}

 extent : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩) → ℕ∞
 extent ξ = raw-extent ξ , raw-extent-is-decreasing ξ

 finite-extent-gives-𝓕 : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩) → is-finite (extent ξ) → 𝓕 ξ
 finite-extent-gives-𝓕 {u} ξ (n , p) = h (ι u n) refl
  where
   I : raw-extent ξ n ＝ ₀
   I = raw-extent ξ n ＝⟨ (ap (λ - → ι - n) p) ⁻¹ ⟩
       ι (ι n) n      ＝⟨ ℕ-to-ℕ∞-diagonal₀ n ⟩
       ₀              ∎

   h : (c : 𝟚) → ι u n ＝ c → 𝓕 ξ
   h ₁ e = 𝟘-elim (zero-is-not-one
                    (₀              ＝⟨ I ⁻¹ ⟩
                     raw-extent ξ n ＝⟨ 𝟚-equality-cases₁ e ⟩
                     ₁              ∎))
   h ₀ e = φ , complement₀ q
    where
     φ : is-finite u
     φ = bounded-is-finite fe' n u e

     q : complement (ρ ξ φ) ＝ ₀
     q = complement (ρ ξ φ) ＝⟨ (𝟚-equality-cases₀ e)⁻¹ ⟩
         raw-extent ξ n     ＝⟨ I ⟩
         ₀                  ∎

 𝓕-gives-finite-extent : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩) → 𝓕 ξ → is-finite (extent ξ)
 𝓕-gives-finite-extent {u} ξ ((n , p) , geq) = n , ((IV n I III) ⁻¹)
  where
   I : (m : ℕ) → m < n → raw-extent ξ m ＝ ₁
   I m l = 𝟚-equality-cases₁ I₀
    where
     I₀ : ι u m ＝ ₁
     I₀ = ι u m     ＝⟨ (ap (λ w → ι w m) p) ⁻¹ ⟩
          ι (ι n) m ＝⟨ <-gives-⊏ m n l ⟩
          ₁         ∎

   II : ι u n ＝ ₀
   II = ι u n     ＝⟨ (ap (λ w → ι w n) p) ⁻¹ ⟩
        ι (ι n) n ＝⟨ ℕ-to-ℕ∞-diagonal₀ n ⟩
        ₀         ∎

   III : raw-extent ξ n ＝ ₀
   III = raw-extent ξ n
           ＝⟨ 𝟚-equality-cases₀ II ⟩
         complement (ρ ξ (bounded-is-finite fe' n u II))
           ＝⟨ ap (λ ψ → complement (ρ ξ ψ))
                 (being-finite-is-prop fe' u
                 (bounded-is-finite fe' n u II) (n , p)) ⟩
         complement (ρ ξ (n , p))
           ＝⟨ ap complement geq ⟩
          ₀ ∎

   IV : (n : ℕ)
      → ((m : ℕ) → m < n → raw-extent ξ m ＝ ₁)
      → raw-extent ξ n ＝ ₀
      → extent ξ ＝ ι n
   IV 0         lt a = is-Zero-equal-Zero fe' a
   IV (succ n') lt a = Succ-criterion fe' (lt n' (<-succ n')) a

 𝓕-is-semidecidable : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩) → is-semidecidable (𝓕 ξ)
 𝓕-is-semidecidable {u} ξ = ∣ extent ξ ,
                              𝓕-gives-finite-extent ξ ,
                              finite-extent-gives-𝓕 ξ ∣

 𝔽 : {u : ℕ∞} → ⟨ α̅ u ⟩ → 𝕊
 𝔽 ξ = (𝓕 ξ , 𝓕-is-prop ξ) , 𝓕-is-semidecidable ξ

\end{code}

We now show that 𝔽 preservers the strict order.

\begin{code}

 𝓕-is-empty : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩) (φ : is-finite u)
            → ρ ξ φ ＝ ₀
            → ¬ (𝓕 ξ)
 𝓕-is-empty {u} ξ φ e₀ (ψ , e₁) = one-is-not-zero I
  where
   I : ₁ ＝ ₀
   I = ₁     ＝⟨ e₁ ⁻¹ ⟩
       ρ ξ ψ ＝⟨ ap (ρ ξ) (being-finite-is-prop fe' u ψ φ) ⟩
       ρ ξ φ ＝⟨ e₀ ⟩
       ₀     ∎

 𝔽⊥ : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩) (φ : is-finite u)
    → ρ ξ φ ＝ ₀
    → 𝔽 ξ ＝ ⊥ₛ
 𝔽⊥ ξ φ e₀ = to-𝕊-＝ (𝔽 ξ) ⊥ₛ (𝓕-is-empty ξ φ e₀ , 𝟘-elim)

 𝔽⊤ : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩) (φ : is-finite u)
    → ρ ξ φ ＝ ₁
    → 𝔽 ξ ＝ ⊤ₛ
 𝔽⊤ ξ φ e₁ = to-𝕊-＝ (𝔽 ξ) ⊤ₛ ((λ _ → ⋆) , (λ _ → φ , e₁))

 𝔽-preserves-≺ : {u : ℕ∞} (ξ₁ ξ₂ : ⟨ α̅ u ⟩)
               → ξ₁ ≺⟨ α̅ u ⟩ ξ₂
               → 𝔽 ξ₁ ≺ₛ 𝔽 ξ₂
 𝔽-preserves-≺ ξ₁ ξ₂ (φ , l) =
  (λ s → 𝟘-elim (𝓕-is-empty ξ₁ φ (≺-left (ξ₁ φ) (ξ₂ φ) l) s)) ,
  (φ , ≺-right (ξ₁ φ) (ξ₂ φ) l)

\end{code}

If the lower sets of ξ and ξ' are equal, then so are 𝔽 ξ and 𝔽 ξ'.

\begin{code}

 ↓-to-𝔽-＝ : {u u' : ℕ∞} (ξ : ⟨ α̅ u ⟩) (ξ' : ⟨ α̅ u' ⟩)
          → α̅ u ↓ ξ ＝ α̅ u' ↓ ξ'
          → 𝔽 ξ ＝ 𝔽 ξ'
 ↓-to-𝔽-＝ {u} {u'} ξ ξ' E = to-𝕊-＝ (𝔽 ξ) (𝔽 ξ') (IV , V)
  where
   I : (Σ ζ ꞉ ⟨ α̅ u ⟩ , ζ ≺⟨ α̅ u ⟩ ξ) ＝ (Σ ζ' ꞉ ⟨ α̅ u' ⟩ , ζ' ≺⟨ α̅ u' ⟩ ξ')
   I = ap ⟨_⟩ E

   II : (w : ℕ∞) (ρ : ⟨ α̅ w ⟩) → 𝓕 ρ → Σ ζ ꞉ ⟨ α̅ w ⟩ , ζ ≺⟨ α̅ w ⟩ ρ
   II w ρ (φ , e₂) = ⊥ξ , φ , ≺-left-right (⊥ξ φ) (ρ φ) refl e₂

   III : (w w' : ℕ∞) (ρ : ⟨ α̅ w ⟩) (ρ' : ⟨ α̅ w' ⟩)
      → ((Σ ζ ꞉ ⟨ α̅ w ⟩ , ζ ≺⟨ α̅ w ⟩ ρ) → (Σ ζ' ꞉ ⟨ α̅ w' ⟩ , ζ' ≺⟨ α̅ w' ⟩ ρ'))
      → 𝓕 ρ
      → 𝓕 ρ'
   III w w' ρ ρ' h s = c (h (II w ρ s))
    where
     c : (Σ ζ' ꞉ ⟨ α̅ w' ⟩ , ζ' ≺⟨ α̅ w' ⟩ ρ') → 𝓕 ρ'
     c (ζ' , ψ , l) = ψ , ≺-right (ζ' ψ) (ρ' ψ) l

   IV : 𝓕 ξ → 𝓕 ξ'
   IV = III u u' ξ ξ' (Idtofun I)

   V : 𝓕 ξ' → 𝓕 ξ
   V = III u' u ξ' ξ (Idtofun (I ⁻¹))

\end{code}

We now define a simulation θ from from the ordinal α̅ u to the ordinal α̅∞.

\begin{code}

 θ : {u : ℕ∞} → ⟨ α̅ u ⟩ → ⟨ α̅∞ ⟩
 θ {u} = [ α̅ u , sup α̅ ]⟨ sup-is-upper-bound α̅ u ⟩

 θ-is-simulation : {u : ℕ∞} → is-simulation (α̅ u) α̅∞ θ
 θ-is-simulation {u} = pr₂ (sup-is-upper-bound α̅ u)

\end{code}

TODO. Find a sensible name for the above projection pr₂. We must have
a definition somewhere. If not, define it at an appropriate file.

We will use a number of times the fact that for every y : ⟨ α̅∞ ⟩ there
is u : ℕ∞ such that the fiber of y over θ {u} is inhabited.

\begin{code}

 θ-fiber-lemma : (y : ⟨ α̅∞ ⟩) → ∃ u ꞉ ℕ∞ , fiber (θ {u}) y
 θ-fiber-lemma = sup-is-upper-bound-jointly-surjective α̅

 θ-to-𝔽-＝ : {u u' : ℕ∞} (ξ : ⟨ α̅ u ⟩) (ξ' : ⟨ α̅ u' ⟩)
          → θ ξ ＝ θ ξ'
          → 𝔽 ξ ＝ 𝔽 ξ'
 θ-to-𝔽-＝ {u} {u'} ξ ξ' e = ↓-to-𝔽-＝ ξ ξ' I
  where
   I : α̅ u ↓ ξ ＝ α̅ u' ↓ ξ'
   I = α̅ u ↓ ξ   ＝⟨ (initial-segment-of-sup-at-component α̅ u ξ)⁻¹ ⟩
       α̅∞ ↓ θ ξ  ＝⟨ ap (α̅∞ ↓_) e ⟩
       α̅∞ ↓ θ ξ' ＝⟨ initial-segment-of-sup-at-component α̅ u' ξ' ⟩
       α̅ u' ↓ ξ'  ∎

\end{code}

We now define a map τ : ⟨ α̅∞ ⟩ → 𝕊 by first defining a type-valued
version τ' of it, which we first show to be single-valued.

\begin{code}

 τ' : ⟨ α̅∞ ⟩ → 𝓤₁ ̇
 τ' y = Σ t ꞉ 𝕊 , ((u : ℕ∞) (ξ : ⟨ α̅ u ⟩) → θ ξ ＝ y → 𝔽 ξ ＝ t)

 τ'-is-prop : (y : ⟨ α̅∞ ⟩) → is-prop (τ' y)
 τ'-is-prop y (t , h) (t' , h') =
  to-subtype-＝
   (λ - → Π₃-is-prop fe' (λ u ξ e → 𝕊-is-set))
   (∥∥-rec 𝕊-is-set (λ (u , ξ , e) → t   ＝⟨ (h u ξ e) ⁻¹ ⟩
                                     𝔽 ξ ＝⟨ h' u ξ e ⟩
                                     t'  ∎)
   (θ-fiber-lemma y))

 τ'-pointed : (y : ⟨ α̅∞ ⟩) → τ' y
 τ'-pointed y = ∥∥-rec (τ'-is-prop y) I (θ-fiber-lemma y)
  where
   I : (Σ u ꞉ ℕ∞ , Σ ξ ꞉ ⟨ α̅ u ⟩ , θ ξ ＝ y) → τ' y
   I (u , ξ , e) = 𝔽 ξ , (λ u' ξ' e' → θ-to-𝔽-＝ ξ' ξ (I₀ ξ' e'))
    where
     I₀ : {u' : ℕ∞} (ξ' : ⟨ α̅ u' ⟩) → θ ξ' ＝ y → θ ξ' ＝ θ ξ
     I₀ ξ' e' = θ ξ' ＝⟨ e' ⟩
                y    ＝⟨ e ⁻¹ ⟩
                θ ξ  ∎

 τ : ⟨ α̅∞ ⟩ → 𝕊
 τ y = pr₁ (τ'-pointed y)

\end{code}

The following is the property we want τ to satisfy, as a lemma for the
main result of this file.

\begin{code}

 τ-property : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩) (y : ⟨ α̅∞ ⟩)
            → θ ξ ＝ y
            → τ y ＝ 𝔽 ξ
 τ-property {u} ξ y e = (pr₂ (τ'-pointed y) u ξ e) ⁻¹

\end{code}

The following casts are to both make proofs easier to understand and
to improve type checking performance by avoiding transports (at the
time of writing).

\begin{code}

 ≺-cast-left : (x x' y : ⟨ α̅∞ ⟩) → x ＝ x' → x ≺⟨ α̅∞ ⟩ y → x' ≺⟨ α̅∞ ⟩ y
 ≺-cast-left x x' y refl l = l

 ≺-cast-right : (x y y' : ⟨ α̅∞ ⟩) → y ＝ y' → x ≺⟨ α̅∞ ⟩ y → x ≺⟨ α̅∞ ⟩ y'
 ≺-cast-right x y y' refl l = l

 θ-preserves-≺ : (u : ℕ∞) (ξ ξ' : ⟨ α̅ u ⟩)
               → ξ ≺⟨ α̅ u ⟩ ξ'
               → θ ξ ≺⟨ α̅∞ ⟩ θ ξ'
 θ-preserves-≺ u = simulations-are-order-preserving (α̅ u) α̅∞ θ θ-is-simulation

 θ-is-initial-segment : (u : ℕ∞) (ξ : ⟨ α̅ u ⟩) (z : ⟨ α̅∞ ⟩)
                      → z ≺⟨ α̅∞ ⟩ θ ξ
                      → Σ ξ₀ ꞉ ⟨ α̅ u ⟩ , (ξ₀ ≺⟨ α̅ u ⟩ ξ) × (θ ξ₀ ＝ z)
 θ-is-initial-segment u ξ z = simulations-are-initial-segments (α̅ u) α̅∞ θ
                               θ-is-simulation ξ z

 ≺ₛ-cast-left : (t t' r : 𝕊) → t ＝ t' → t ≺ₛ r → t' ≺ₛ r
 ≺ₛ-cast-left t t' r refl l = l

 ≺ₛ-cast-right : (t r r' : 𝕊) → r ＝ r' → t ≺ₛ r → t ≺ₛ r'
 ≺ₛ-cast-right t r r' refl l = l

 τ-fiber-cast : (y : ⟨ α̅∞ ⟩) (t t' : 𝕊)
              → t ＝ t'
              → (Σ y₀ ꞉ ⟨ α̅∞ ⟩ , (y₀ ≺⟨ α̅∞ ⟩ y) × (τ y₀ ＝ t))
              → (Σ y₀ ꞉ ⟨ α̅∞ ⟩ , (y₀ ≺⟨ α̅∞ ⟩ y) × (τ y₀ ＝ t'))
 τ-fiber-cast y t t' refl σ = σ

 τ-⊥-no-preds : (u : ℕ∞) (ξ : ⟨ α̅ u ⟩) (y z : ⟨ α̅∞ ⟩)
              → θ ξ ＝ y
              → τ y ＝ ⊥ₛ
              → ¬ (z ≺⟨ α̅∞ ⟩ y)
 τ-⊥-no-preds u ξ y z e c l = II (θ-is-initial-segment u ξ z l')
  where
   l' : z ≺⟨ α̅∞ ⟩ θ ξ
   l' = ≺-cast-right z y (θ ξ) (e ⁻¹) l

   I : 𝔽 ξ ＝ ⊥ₛ
   I = 𝔽 ξ ＝⟨ (τ-property ξ y e) ⁻¹ ⟩
       τ y     ＝⟨ c ⟩
       ⊥ₛ      ∎

   II : (Σ ξ₀ ꞉ ⟨ α̅ u ⟩ , (ξ₀ ≺⟨ α̅ u ⟩ ξ) × (θ ξ₀ ＝ z)) → 𝟘 {𝓤₀}
   II (ξ₀ , m , p) = transport (λ - → δ - holds) I
                      (pr₂ (𝔽-preserves-≺ ξ₀ ξ m))

 τ-⊥-uniqueness : (y y' : ⟨ α̅∞ ⟩) → τ y ＝ ⊥ₛ → τ y' ＝ ⊥ₛ → y ＝ y'
 τ-⊥-uniqueness y y' c c' =
  ∥∥-rec ⟨α̅∞⟩-is-set
   (λ ρ → ∥∥-rec ⟨α̅∞⟩-is-set (I ρ) (θ-fiber-lemma y'))
   (θ-fiber-lemma y)
  where
   I : (Σ u ꞉ ℕ∞ , Σ ξ ꞉ ⟨ α̅ u ⟩ , θ ξ ＝ y)
     → (Σ u' ꞉ ℕ∞ , Σ ξ' ꞉ ⟨ α̅ u' ⟩ , θ ξ' ＝ y')
     → y ＝ y'
   I (u , ξ , e) (u' , ξ' , e') = Extensionality α̅∞ y y' f g
    where
     f : (z : ⟨ α̅∞ ⟩) → z ≺⟨ α̅∞ ⟩ y → z ≺⟨ α̅∞ ⟩ y'
     f z l = 𝟘-elim (τ-⊥-no-preds u ξ y z e c l)

     g : (z : ⟨ α̅∞ ⟩) → z ≺⟨ α̅∞ ⟩ y' → z ≺⟨ α̅∞ ⟩ y
     g z l = 𝟘-elim (τ-⊥-no-preds u' ξ' y' z e' c' l)

 τ-⊤-lemma
  : {u₁ u₂ : ℕ∞} (ξ₁ : ⟨ α̅ u₁ ⟩) (ξ₂ : ⟨ α̅ u₂ ⟩)
  → 𝔽 ξ₁ ＝ ⊤ₛ
  → 𝔽 ξ₂ ＝ ⊤ₛ
  → (z : ⟨ α̅∞ ⟩)
  → z ≺⟨ α̅∞ ⟩ θ ξ₁
  → z ≺⟨ α̅∞ ⟩ θ ξ₂
 τ-⊤-lemma {u₁} {u₂} ξ₁ ξ₂ c₁ c₂ z l₀ = III (θ-is-initial-segment u₁ ξ₁ z l₀)
  where
   s₂ : 𝓕 ξ₂
   s₂ = transport (λ - → δ - holds) (c₂ ⁻¹) ⋆

   φ₂ : is-finite u₂
   φ₂ = pr₁ s₂

   I : ⊥ξ ≺⟨ α̅ u₂ ⟩ ξ₂
   I = φ₂ , ≺-left-right (⊥ξ φ₂) (ξ₂ φ₂) refl (pr₂ s₂)

   II : τ (θ ⊥ξ) ＝ ⊥ₛ
   II = τ (θ ⊥ξ) ＝⟨ τ-property ⊥ξ (θ ⊥ξ) refl ⟩
        𝔽 ⊥ξ     ＝⟨ 𝔽⊥ ⊥ξ φ₂ refl ⟩
        ⊥ₛ       ∎

   III : (Σ ξ₀ ꞉ ⟨ α̅ u₁ ⟩ , (ξ₀ ≺⟨ α̅ u₁ ⟩ ξ₁) × (θ ξ₀ ＝ z))
       → z ≺⟨ α̅∞ ⟩ θ ξ₂
   III (ξ₀ , (φ₁ , l₁) , p) = ≺-cast-left (θ ⊥ξ) z (θ ξ₂) (zz ⁻¹)
                             (θ-preserves-≺ u₂ ⊥ξ ξ₂ I)
    where
     cz : τ z ＝ ⊥ₛ
     cz = τ z       ＝⟨ τ-property ξ₀ z p ⟩
          𝔽 ξ₀ ＝⟨ 𝔽⊥ ξ₀ φ₁ (≺-left (ξ₀ φ₁) (ξ₁ φ₁) l₁) ⟩
          ⊥ₛ        ∎

     zz : z ＝ θ ⊥ξ
     zz = τ-⊥-uniqueness z (θ ⊥ξ) cz II

 τ-lemma₁ : (y y' : ⟨ α̅∞ ⟩) → τ y ＝ ⊤ₛ → τ y' ＝ ⊤ₛ → y ＝ y'
 τ-lemma₁ y y' a a' =
  ∥∥-rec ⟨α̅∞⟩-is-set
   (λ ρ → ∥∥-rec ⟨α̅∞⟩-is-set (I ρ) (θ-fiber-lemma y'))
   (θ-fiber-lemma y)
  where
   I : (Σ u ꞉ ℕ∞ , Σ ξ ꞉ ⟨ α̅ u ⟩ , θ ξ ＝ y)
     → (Σ u' ꞉ ℕ∞ , Σ ξ' ꞉ ⟨ α̅ u' ⟩ , θ ξ' ＝ y')
     → y ＝ y'
   I (u , ξ , e) (u' , ξ' , e') = Extensionality α̅∞ y y' III III'
    where
     II : 𝔽 ξ ＝ ⊤ₛ
     II = 𝔽 ξ ＝⟨ (τ-property ξ y e) ⁻¹ ⟩
          τ y     ＝⟨ a ⟩
          ⊤ₛ      ∎

     II' : 𝔽 ξ' ＝ ⊤ₛ
     II' = 𝔽 ξ' ＝⟨ (τ-property ξ' y' e') ⁻¹ ⟩
           τ y' ＝⟨ a' ⟩
           ⊤ₛ   ∎

     III : (z : ⟨ α̅∞ ⟩) → z ≺⟨ α̅∞ ⟩ y → z ≺⟨ α̅∞ ⟩ y'
     III z l = ≺-cast-right z (θ ξ') y' e'
                (τ-⊤-lemma ξ ξ' II II' z
                  (≺-cast-right z y (θ ξ) (e ⁻¹) l))

     III' : (z : ⟨ α̅∞ ⟩) → z ≺⟨ α̅∞ ⟩ y' → z ≺⟨ α̅∞ ⟩ y
     III' z l = ≺-cast-right z (θ ξ) y e
                 (τ-⊤-lemma ξ' ξ II' II z
                   (≺-cast-right z y' (θ ξ') (e' ⁻¹) l))

\end{code}

We now show that the map τ is a simulation. For the initial-segment
property, the crucial point is that the only ≺ₛ-predecessor of
anything is ⊥ₛ, whose τ-preimages are unique by the previous lemma, so
that the required Σ-type is a proposition.

\begin{code}

 τ-lemma₂ : (y y' : ⟨ α̅∞ ⟩) (u : ℕ∞) (ξ : ⟨ α̅ u ⟩)
          → θ ξ ＝ y
          → (u' : ℕ∞) (ξ' : ⟨ α̅ u' ⟩)
          → θ ξ' ＝ y'
          → y ≺⟨ α̅∞ ⟩ y'
          → τ y ≺ₛ τ y'
 τ-lemma₂ y y' u ξ e u' ξ' e' l = I (θ-is-initial-segment u' ξ' (θ ξ) l')
  where
   l₁ : θ ξ ≺⟨ α̅∞ ⟩ y'
   l₁ = ≺-cast-left y (θ ξ) y' (e ⁻¹) l

   l' : θ ξ ≺⟨ α̅∞ ⟩ θ ξ'
   l' = ≺-cast-right (θ ξ) y' (θ ξ') (e' ⁻¹) l₁

   I : (Σ ξ₀ ꞉ ⟨ α̅ u' ⟩ , (ξ₀ ≺⟨ α̅ u' ⟩ ξ') × (θ ξ₀ ＝ θ ξ))
     → τ y ≺ₛ τ y'
   I (ξ₀ , m , p) = ≺ₛ-cast-left (𝔽 ξ₀) (τ y) (τ y') I₃ I₄
    where
     I₀ : 𝔽 ξ₀ ≺ₛ 𝔽 ξ'
     I₀ = 𝔽-preserves-≺ ξ₀ ξ' m

     I₁ : 𝔽 ξ' ＝ τ y'
     I₁ = (τ-property ξ' y' e') ⁻¹

     I₂ : θ ξ₀ ＝ y
     I₂ = θ ξ₀ ＝⟨ p ⟩
          θ ξ  ＝⟨ e ⟩
          y    ∎

     I₃ : 𝔽 ξ₀ ＝ τ y
     I₃ = (τ-property ξ₀ y I₂) ⁻¹

     I₄ : 𝔽 ξ₀ ≺ₛ τ y'
     I₄ = ≺ₛ-cast-right (𝔽 ξ₀) (𝔽 ξ') (τ y') I₁ I₀

 τ-lemma₃ : is-order-preserving α̅∞ 𝓢 τ
 τ-lemma₃ y y' l =
  ∥∥-rec (≺ₛ-prop-valued (τ y) (τ y'))
   (λ (u , ξ , e) → ∥∥-rec (≺ₛ-prop-valued (τ y) (τ y'))
     (λ (u' , ξ' , e') → τ-lemma₂ y y' u ξ e u' ξ' e' l)
     (θ-fiber-lemma y'))
   (θ-fiber-lemma y)

 τ-lemma₄ : (y : ⟨ α̅∞ ⟩) (u : ℕ∞) (ξ : ⟨ α̅ u ⟩)
          → θ ξ ＝ y
          → 𝓕 ξ
          → Σ y₀ ꞉ ⟨ α̅∞ ⟩ , (y₀ ≺⟨ α̅∞ ⟩ y) × (τ y₀ ＝ ⊥ₛ)
 τ-lemma₄ y u ξ eᵧ (φ , e₂) = θ ⊥ξ , I₁ , I₂
  where
   I₀ : θ ⊥ξ ≺⟨ α̅∞ ⟩ θ ξ
   I₀ = θ-preserves-≺ u ⊥ξ ξ
         (φ , ≺-left-right (⊥ξ φ) (ξ φ) refl e₂)

   I₁ : θ ⊥ξ ≺⟨ α̅∞ ⟩ y
   I₁ = ≺-cast-right (θ ⊥ξ) (θ ξ) y eᵧ I₀

   I₂ : τ (θ ⊥ξ) ＝ ⊥ₛ
   I₂ = τ (θ ⊥ξ) ＝⟨ τ-property ⊥ξ (θ ⊥ξ) refl ⟩
        𝔽 ⊥ξ    ＝⟨ 𝔽⊥ ⊥ξ φ refl ⟩
        ⊥ₛ              ∎

 τ-lemma₅ : (y : ⟨ α̅∞ ⟩) (t : 𝕊)
          → t ≺ₛ τ y
          → Σ y₀ ꞉ ⟨ α̅∞ ⟩ , (y₀ ≺⟨ α̅∞ ⟩ y) × (τ y₀ ＝ t)
 τ-lemma₅ y t (ν , h) = τ-fiber-cast y ⊥ₛ t (I ⁻¹) IV
  where
   I : t ＝ ⊥ₛ
   I = to-𝕊-＝ t ⊥ₛ ((λ s → 𝟘-elim (ν s)) , 𝟘-elim)

   II : is-prop (Σ y₀ ꞉ ⟨ α̅∞ ⟩ , (y₀ ≺⟨ α̅∞ ⟩ y) × (τ y₀ ＝ ⊥ₛ))
   II (y₀ , m , c) (y₀' , m' , c') =
    to-subtype-＝
     (λ y₁ → ×-is-prop (Prop-valuedness α̅∞ y₁ y) 𝕊-is-set)
     (τ-⊥-uniqueness y₀ y₀' c c')

   III : (Σ u ꞉ ℕ∞ , Σ ξ ꞉ ⟨ α̅ u ⟩ , θ ξ ＝ y)
       → Σ y₀ ꞉ ⟨ α̅∞ ⟩ , (y₀ ≺⟨ α̅∞ ⟩ y) × (τ y₀ ＝ ⊥ₛ)
   III (u , ξ , eᵧ) = τ-lemma₄ y u ξ eᵧ s
    where
     s : 𝓕 ξ
     s = transport (λ - → δ - holds) (τ-property ξ y eᵧ) h

   IV : Σ y₀ ꞉ ⟨ α̅∞ ⟩ , (y₀ ≺⟨ α̅∞ ⟩ y) × (τ y₀ ＝ ⊥ₛ)
   IV = ∥∥-rec II III (θ-fiber-lemma y)

\end{code}

Which give the desired conclusion.

\begin{code}

 τ-is-simulation : is-simulation α̅∞ 𝓢 τ
 τ-is-simulation = τ-lemma₅ , τ-lemma₃

\end{code}

We continue with more lemmas about τ.

\begin{code}

 τ-lemma₆ : (p : Ω 𝓤₀) {u : ℕ∞}
          → (p holds ↔ is-finite u)
          → (σ : is-semidecidable (p holds))
          → fiber τ (p , σ)
 τ-lemma₆ p {u} 𝕖 σ = y , II
  where
   y : ⟨ α̅∞ ⟩
   y = θ ⊤ξ

   I : 𝔽 ⊤ξ ＝ (p , σ)
   I = to-𝕊-＝ (𝔽 ⊤ξ) (p , σ) (I₀ , I₁)
    where
     I₀ : 𝓕 ⊤ξ → p holds
     I₀ (φ , _) = rl-implication 𝕖 φ

     I₁ : p holds → 𝓕 ⊤ξ
     I₁ s = lr-implication 𝕖 s , refl

   II : τ y ＝ (p , σ)
   II = τ y      ＝⟨ τ-property ⊤ξ y refl ⟩
        𝔽 ⊤ξ     ＝⟨ I ⟩
        (p , σ)  ∎

 τ-is-surjection : is-surjection τ
 τ-is-surjection (p , σ) = ∥∥-rec ∃-is-prop (λ (u₀ , 𝕖) → ∣ τ-lemma₆ p 𝕖 σ ∣) σ

\end{code}

A surjective simulation is an order equivalence, and so we get the
promised description of the supremum.

\begin{code}

 τ-lc : left-cancellable τ
 τ-lc = simulations-are-lc α̅∞ 𝓢 τ τ-is-simulation

 τ-is-embedding : is-embedding τ
 τ-is-embedding = lc-maps-into-sets-are-embeddings τ τ-lc 𝕊-is-set

 τ-is-equiv : is-equiv τ
 τ-is-equiv = surjective-embeddings-are-equivs τ τ-is-embedding τ-is-surjection

 τ-reflects-≺ : (y y' : ⟨ α̅∞ ⟩) → τ y ≺ₛ τ y' → y ≺⟨ α̅∞ ⟩ y'
 τ-reflects-≺ y y' l = I (τ-lemma₅ y' (τ y) l)
  where
   I : (Σ y₀ ꞉ ⟨ α̅∞ ⟩ , (y₀ ≺⟨ α̅∞ ⟩ y') × (τ y₀ ＝ τ y)) → y ≺⟨ α̅∞ ⟩ y'
   I (y₀ , m , c) = ≺-cast-left y₀ y y' (τ-lc c) m

 τ⁻¹ : 𝕊 → ⟨ α̅∞ ⟩
 τ⁻¹ = inverse τ τ-is-equiv

 τ⁻¹-is-order-preserving : is-order-preserving 𝓢 α̅∞ τ⁻¹
 τ⁻¹-is-order-preserving t t' l = τ-reflects-≺
                                   (inverse τ τ-is-equiv t)
                                   (inverse τ τ-is-equiv t')
                                   III
  where
   I : t ＝ τ (inverse τ τ-is-equiv t)
   I = (inverses-are-sections τ τ-is-equiv t) ⁻¹

   I' : t' ＝ τ (inverse τ τ-is-equiv t')
   I' = (inverses-are-sections τ τ-is-equiv t') ⁻¹

   II : t ≺ₛ τ (inverse τ τ-is-equiv t')
   II = ≺ₛ-cast-right t t' (τ (inverse τ τ-is-equiv t')) I' l

   III : τ (inverse τ τ-is-equiv t) ≺ₛ τ (inverse τ τ-is-equiv t')
   III = ≺ₛ-cast-left t (τ (inverse τ τ-is-equiv t))
          (τ (inverse τ τ-is-equiv t')) I II

\end{code}

As promised, the sup of α̅ is S:

\begin{code}

 α̅∞-is-𝓢 : α̅∞ ≃ₒ 𝓢
 α̅∞-is-𝓢 = τ , τ-lemma₃ , τ-is-equiv , τ⁻¹-is-order-preserving

 characterization-of-α̅∞ : ⟨ α̅∞ ⟩ ≃ 𝕊
 characterization-of-α̅∞ = ≃ₒ-gives-≃ α̅∞ 𝓢 α̅∞-is-𝓢

\end{code}

As a corollary, we conclude that, although 𝕊 lives in 𝓤₁ by
construction, it has a copy in 𝓤₀:

\begin{code}

 𝕊-is-small : is-small 𝕊
 𝕊-is-small = ⟨ α̅∞ ⟩ , characterization-of-α̅∞

\end{code}

The ordinal α̅∞, or equivalently the type 𝕊, fails to be totally
separated in general in the following sense: its total separatedness
implies the constructive taboo ¬¬ WLPO, which is a principle that
fails in both Johnstone's Topological Topos and Hylands Effective
Topos, for instance.

\begin{code}

 open import TypeTopology.TotallySeparated
 open import Taboos.WLPO
 open import Taboos.BasicDiscontinuity fe'

 is-fin : ℕ∞ → 𝕊
 is-fin u = (is-finite u , being-finite-is-prop fe' u) , ∣ u , ↔-refl ∣

 naturals-are-fin : (n : ℕ) → is-fin (ι n) ＝ ⊤ₛ
 naturals-are-fin n = to-𝕊-＝ (is-fin (ι n)) ⊤ₛ ((λ _ → ⋆) , (λ _ → n , refl))

 ∞-is-not-fin : is-fin ∞ ＝ ⊥ₛ
 ∞-is-not-fin = to-𝕊-＝ (is-fin ∞) ⊥ₛ (ν , 𝟘-elim)
  where
   ν : ¬ is-finite ∞
   ν (n , r) = ∞-is-not-finite n (r ⁻¹)

 ⊥ₛ-is-not-⊤ₛ : ⊥ₛ ≠ ⊤ₛ
 ⊥ₛ-is-not-⊤ₛ e = transport (λ - → δ - holds) (e ⁻¹) ⋆

 𝕊-separating-map-gives-WLPO : (p : 𝕊 → 𝟚) → p ⊥ₛ ≠ p ⊤ₛ → WLPO
 𝕊-separating-map-gives-WLPO p ν = h (p ⊥ₛ) (p ⊤ₛ) refl refl
  where
   q : ℕ∞ → 𝟚
   q u = p (is-fin u)

   q₀ : (n : ℕ) → q (ι n) ＝ p ⊤ₛ
   q₀ n = ap p (naturals-are-fin n)

   q∞ : q ∞ ＝ p ⊥ₛ
   q∞ = ap p ∞-is-not-fin

   h : (b c : 𝟚) → p ⊥ₛ ＝ b → p ⊤ₛ ＝ c → WLPO
   h ₀ ₀ e e' = 𝟘-elim (ν (p ⊥ₛ ＝⟨ e ⟩
                           ₀    ＝⟨ e' ⁻¹ ⟩
                           p ⊤ₛ ∎))
   h ₁ ₁ e e' = 𝟘-elim (ν (p ⊥ₛ ＝⟨ e ⟩
                           ₁    ＝⟨ e' ⁻¹ ⟩
                           p ⊤ₛ ∎))
   h ₁ ₀ e e' = basic-discontinuity-taboo q (I₀ , I∞)
    where
     I₀ : (n : ℕ) → q (ι n) ＝ ₀
     I₀ n = q (ι n) ＝⟨ q₀ n ⟩
            p ⊤ₛ    ＝⟨ e' ⟩
            ₀       ∎

     I∞ : q ∞ ＝ ₁
     I∞ = q ∞  ＝⟨ q∞ ⟩
          p ⊥ₛ ＝⟨ e ⟩
          ₁    ∎
   h ₀ ₁ e e' = basic-discontinuity-taboo (λ u → complement (q u)) (I₀ , I∞)
    where
     I₀ : (n : ℕ) → complement (q (ι n)) ＝ ₀
     I₀ n = complement (q (ι n)) ＝⟨ ap complement (q₀ n) ⟩
            complement (p ⊤ₛ)    ＝⟨ ap complement e' ⟩
            ₀                    ∎

     I∞ : complement (q ∞) ＝ ₁
     I∞ = complement (q ∞)  ＝⟨ ap complement q∞ ⟩
          complement (p ⊥ₛ) ＝⟨ ap complement e ⟩
          ₁                 ∎

 𝕊-totally-separated-gives-¬¬WLPO : is-totally-separated 𝕊 → ¬¬ WLPO
 𝕊-totally-separated-gives-¬¬WLPO ts w = ⊥ₛ-is-not-⊤ₛ (ts {⊥ₛ} {⊤ₛ} a)
  where
   a : (p : 𝕊 → 𝟚) → p ⊥ₛ ＝ p ⊤ₛ
   a p = h (p ⊥ₛ) (p ⊤ₛ) refl refl
    where
     h : (b c : 𝟚) → p ⊥ₛ ＝ b → p ⊤ₛ ＝ c → p ⊥ₛ ＝ p ⊤ₛ
     h ₀ ₀ e e' = p ⊥ₛ ＝⟨ e ⟩
                  ₀    ＝⟨ e' ⁻¹ ⟩
                  p ⊤ₛ ∎
     h ₁ ₁ e e' = p ⊥ₛ ＝⟨ e ⟩
                  ₁    ＝⟨ e' ⁻¹ ⟩
                  p ⊤ₛ ∎
     h ₀ ₁ e e' = 𝟘-elim (w (𝕊-separating-map-gives-WLPO p ν))
      where
       ν : p ⊥ₛ ≠ p ⊤ₛ
       ν d = zero-is-not-one (₀    ＝⟨ e ⁻¹ ⟩
                              p ⊥ₛ ＝⟨ d ⟩
                              p ⊤ₛ ＝⟨ e' ⟩
                              ₁    ∎)
     h ₁ ₀ e e' = 𝟘-elim (w (𝕊-separating-map-gives-WLPO p ν))
      where
       ν : p ⊥ₛ ≠ p ⊤ₛ
       ν d = one-is-not-zero (₁    ＝⟨ e ⁻¹ ⟩
                              p ⊥ₛ ＝⟨ d ⟩
                              p ⊤ₛ ＝⟨ e' ⟩
                              ₀    ∎)

 ⟨α̅∞⟩-totally-separated-gives-¬¬WLPO : is-totally-separated ⟨ α̅∞ ⟩ → ¬¬ WLPO
 ⟨α̅∞⟩-totally-separated-gives-¬¬WLPO ts =
  𝕊-totally-separated-gives-¬¬WLPO
   (equiv-to-totally-separated characterization-of-α̅∞ ts)

\end{code}

Which proves (†) above.

TODO. Write down this conclusion formally.
