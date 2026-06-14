Martin Escardo, 10-12th June 2026.

This is a companion to Ordinals.BrouwerCodesInterpretations.

Recall that Brouwer ordinal codes are countably branching trees,
inductively defined by the constructors

  Z : B,
  S : B → B,
  L : (ℕ → B) → B.

The standard interpretation ⟦_⟧₀, given in Ordinals.BrouwerCodesInterpretations,
interprets Z as zero, S as successor, and L as supremum (least upper bound).
See also Ordinals.FailureOfTrichotomy.

The alternative sup-of-extension interpretation ⟦_⟧₂, given in the
same file, interprets Z as one (rather than zero), S again as
successor, but L as the supremum of the extension ℕ∞ → Ordinal of a
family ℕ → Ordinal, given by the algebraic injectivity of the type of
ordinals as constructed in the file Ordinals.Injectivity.

This non-standard interpretation gives compact (aka searchable)
ordinals. A question we had for some time was whether the resulting
ordinals are also totally separated. Here we answer this in the
negative. More precisely, from the assumption that the resulting
ordinals are totally separated, we conclude that ¬¬ WLPO holds.

More generally, and this is what we start with in this file, we show
that a supremum of totally separated ordinals doesn't need to be
totally separated itself, even if the ordinals are further assumed to
be compact and the index set is assumed to be compact and totally
separated.

To prove this, we show that the supremum of the extension of the
constantly 2 sequence of ordinals is a Sierpinski-like type.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.FailureOfTotalSeparatedness
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
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
open import Ordinals.Equivalence
open import Ordinals.Injectivity
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Two
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties

open suprema pt sr

private
 extension : (ℕ → Ordinal 𝓤₀) → (ℕ∞ → Ordinal 𝓤₀)
 extension α = α ↗ (embedding-ℕ-to-ℕ∞ fe')
  where
   open ordinals-injectivity fe

\end{code}

To achieve the above goal, we work with the constantly 2 sequence of
ordinals, abbreviated α here.

\begin{code}

α : ℕ → Ordinal 𝓤₀
α _ = 𝟚ₒ

α̅ : ℕ∞ → Ordinal 𝓤₀
α̅ = extension α

\end{code}

For u : ℕ∞, an element of ⟨ α̅ u ⟩ is a function ξ : is-finite u → 𝟚,
that is, a partial element of 𝟚 with domain of definition is-finite u.
We let φ range over the type is-finite u.

\begin{code}

_ : (u : ℕ∞) → ⟨ α̅ u ⟩ ＝ (is-finite u → 𝟚)
_ = λ u → refl

𝓼 : Ordinal 𝓤₀
𝓼 = sup α̅

𝓼-is-set : is-set ⟨ 𝓼 ⟩
𝓼-is-set = underlying-type-is-set fe 𝓼

\end{code}

The following are all the properties of the supremum that we need for
our purposes, all labelled by θ.

\begin{code}

θ : {u : ℕ∞} → ⟨ α̅ u ⟩ → ⟨ 𝓼 ⟩
θ {u} = [ α̅ u , 𝓼 ]⟨ sup-is-upper-bound α̅ u ⟩

θ-is-simulation : {u : ℕ∞} → is-simulation (α̅ u) 𝓼 θ
θ-is-simulation {u} = [ α̅ u , 𝓼 ]⟨ sup-is-upper-bound α̅ u ⟩-is-simulation

θ-is-order-preserving : {u : ℕ∞} → is-order-preserving (α̅ u) 𝓼 θ
θ-is-order-preserving {u} = simulations-are-order-preserving (α̅ u) 𝓼 θ
                             θ-is-simulation

θ-is-initial-segment : {u : ℕ∞} → is-initial-segment (α̅ u) 𝓼 θ
θ-is-initial-segment {u} ξ z = simulations-are-initial-segments (α̅ u) 𝓼 θ
                                θ-is-simulation ξ z

θ-is-jointly-surjective : (y : ⟨ 𝓼 ⟩) → ∃ u ꞉ ℕ∞ , fiber (θ {u}) y
θ-is-jointly-surjective = sup-is-upper-bound-jointly-surjective α̅

θ-downset : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩) → 𝓼 ↓ θ ξ ＝ α̅ u ↓ ξ
θ-downset {u} = initial-segment-of-sup-at-component α̅ u

\end{code}

We work with the following alternative formulation of semidecidability.

TODO. In the future, establish this equivalence formally, and probably
move all code for the alternative definition to the file
NotionsOfDecidability.SemiDecidable. But notice that we don't need to
establish this equivalence to get our desired conclusions discussed
above.

\begin{code}

is-semidecidable : (X : 𝓤 ̇ ) → 𝓤 ̇
is-semidecidable X = ∃ u ꞉ ℕ∞ , (X ≃ is-finite u)

being-semidecidable-is-prop : (X : 𝓤 ̇ )
                            → is-prop (is-semidecidable X)
being-semidecidable-is-prop X = ∃-is-prop

𝟘-is-semidecidable : is-semidecidable 𝟘
𝟘-is-semidecidable = ∣ ∞ , qinveq
                            𝟘-elim
                            ((λ (n , e) → ∞-is-not-finite n (e ⁻¹)) ,
                             (λ z → 𝟘-elim z) ,
                             (λ (n , e) → 𝟘-elim (∞-is-not-finite n (e ⁻¹)))) ∣

𝟙-is-semidecidable : is-semidecidable (𝟙 {𝓤})
𝟙-is-semidecidable = ∣ Zero , qinveq
                              (λ _ → 0 , refl)
                              (unique-to-𝟙 ,
                               (λ _ → refl) ,
                               (λ φ → ℕ-to-ℕ∞-is-embedding fe' Zero
                                       (to-fiber ℕ-to-ℕ∞ 0) φ)) ∣

𝕊 : 𝓤₁ ̇
𝕊 = Σ p ꞉ Ω 𝓤₀ , is-semidecidable (p holds)

⊥ₛ ⊤ₛ : 𝕊
⊥ₛ = ⊥ , 𝟘-is-semidecidable
⊤ₛ = ⊤ , 𝟙-is-semidecidable

\end{code}

We can think of 𝕊 as a Sierpinski type. We define the domain of
definition of an element of 𝕊 as follows.

\begin{code}

δ : 𝕊 → Ω 𝓤₀
δ = pr₁

\end{code}

As discussed above, we order the Sierpinski type as follows.

\begin{code}

_≺ₛ_ : 𝕊 → 𝕊 → 𝓤₁ ̇
t ≺ₛ t' = (δ t holds → 𝟘 {𝓤₁}) × (δ t' holds)

\end{code}

NB. For simplicity, we are deliberately making the order live in the
universe 𝓤₁, rather than 𝓤₀, because its carrier already lives in 𝓤₁.
A conclusion of our development, recorded below, is that both 𝕊 and
its order have a copy in 𝓤₀ under our assumptions above.

The Sierpinski type 𝕊 is a set, its equality is characterized by
logical equivalence of domains of definition, and ≺ₛ is a well-order,
all of which are immediate.

\begin{code}

𝕊-is-set : is-set 𝕊
𝕊-is-set = Σ-is-set (Ω-is-set fe' pe)
            (λ p → props-are-sets
                    (being-semidecidable-is-prop (p holds)))

to-𝕊-＝ : {t t' : 𝕊}
        → (δ t holds ↔ δ t' holds)
        → t ＝ t'
to-𝕊-＝ (f , g) = to-subtype-＝
                   (λ p → being-semidecidable-is-prop (p holds))
                   (Ω-extensionality pe fe' f g)

≺ₛ-prop-valued : is-prop-valued _≺ₛ_
≺ₛ-prop-valued t t' = ×-is-prop
                       (Π-is-prop fe' (λ _ → 𝟘-is-prop))
                       (holds-is-prop (δ t'))

≺ₛ-transitive : is-transitive _≺ₛ_
≺ₛ-transitive t t' t'' (ν , _) (_ , h') = ν , h'

≺ₛ-extensional : is-extensional _≺ₛ_
≺ₛ-extensional t t' f g = to-𝕊-＝ (I , II)
 where
  I : δ t holds → δ t' holds
  I s = pr₂ (f ⊥ₛ (𝟘-elim , s))

  II : δ t' holds → δ t holds
  II s' = pr₂ (g ⊥ₛ (𝟘-elim , s'))

\end{code}

TODO. Find a sensible name for the above projection pr₂. We must have
a definition somewhere. If not, define it at an appropriate file.

\begin{code}

≺ₛ-well-founded : is-well-founded _≺ₛ_
≺ₛ-well-founded t = acc (λ _ (ν , _) → acc (λ _ (_ , h) → 𝟘-elim (ν h)))

𝓢 : Ordinal 𝓤₁
𝓢 = 𝕊 , _≺ₛ_ , ≺ₛ-prop-valued ,
    ≺ₛ-well-founded , ≺ₛ-extensional , ≺ₛ-transitive

\end{code}

Eventually we will show that 𝓼 ≃ₒ 𝓢. Notice that the former lives in
the first universe 𝓤₀ and the latter in next universe 𝓤₁, which is one
way of interpreting the choice of capitalization.

\begin{code}

𝟎 𝟏 : {u : ℕ∞} → ⟨ α̅ u ⟩
𝟎 φ = ₀
𝟏 φ = ₁

\end{code}

The following specialized transports are to make the type checking
performance feasible. We struggled to make the draft versions of this
file to type check, where we used the general transport construction,
with Agda spinning "for ever". We use similar tricks in a number of
places below, for the same reason.

\begin{code}

≺-transportₗ : {x x' y : ⟨ 𝓼 ⟩} → x ＝ x' → x ≺⟨ 𝓼 ⟩ y → x' ≺⟨ 𝓼 ⟩ y
≺-transportₗ refl l = l

≺-transportᵣ : {x y y' : ⟨ 𝓼 ⟩} → y ＝ y' → x ≺⟨ 𝓼 ⟩ y → x ≺⟨ 𝓼 ⟩ y'
≺-transportᵣ refl l = l

≺ₛ-transportₗ : {t t' r : 𝕊} → t ＝ t' → t ≺ₛ r → t' ≺ₛ r
≺ₛ-transportₗ refl l = l

≺ₛ-transportᵣ : {t r r' : 𝕊} → r ＝ r' → t ≺ₛ r → t ≺ₛ r'
≺ₛ-transportᵣ refl l = l

\end{code}

We have that, for any u : ℕ∞ and ξ : ⟨ α̅ u ⟩, the type

  fiber ξ ₁ := (Σ φ : is-finite , ξ φ ＝ ₁)

is a proposition. We need to show that it is semidecidable.

\begin{code}

𝓕 : {u : ℕ∞} → ⟨ α̅ u ⟩ → 𝓤₀ ̇
𝓕 ξ = fiber ξ ₁

𝓕-is-prop : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩) → is-prop (𝓕 ξ)
𝓕-is-prop {u} ξ = Σ-is-prop (being-finite-is-prop fe' u) (λ φ → 𝟚-is-set)

\end{code}

To show that the proposition 𝓕 ξ is semidecidable, we construct a
conatural number

 semidecider ξ : ℕ∞

that is finite if and only if 𝓕 ξ holds.

\begin{code}

ϕ : {n : ℕ} {u : ℕ∞} → ι u n ＝ ₀ → is-finite u
ϕ {n} {u} = bounded-is-finite fe' n u

finiteness-is-prop : {u : ℕ∞} → is-prop (is-finite u)
finiteness-is-prop {u} = being-finite-is-prop fe' u

raw-semidecider : {u : ℕ∞} → ⟨ α̅ u ⟩ → (ℕ → 𝟚)
raw-semidecider {u} ξ m =
 𝟚-equality-cases
  (λ (e : ι u m ＝ ₀) → complement (ξ (ϕ e)))
  (λ (_ : ι u m ＝ ₁) → ₁)

raw-semidecider-is-decreasing : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩)
                              → is-decreasing (raw-semidecider ξ)
raw-semidecider-is-decreasing {u} ξ m = ≤₂-criterion I
 where
  I : raw-semidecider ξ (succ m) ＝ ₁ → raw-semidecider ξ m ＝ ₁
  I e₁ = h (ι u m) refl
   where
    h : (c : 𝟚) → ι u m ＝ c → raw-semidecider ξ m ＝ ₁
    h ₁ e = 𝟚-equality-cases₁ e
    h ₀ e =
     raw-semidecider ξ m                 ＝⟨ 𝟚-equality-cases₀ e ⟩
     complement (ξ (ϕ e))                ＝⟨ ap (λ - → complement (ξ -))
                                                (finiteness-is-prop (ϕ e)
                                                  (ϕ (stays-zero u e))) ⟩
     complement (ξ (ϕ (stays-zero u e))) ＝⟨ (𝟚-equality-cases₀
                                               (stays-zero u e))⁻¹ ⟩
     raw-semidecider ξ (succ m)          ＝⟨ e₁ ⟩
     ₁                                   ∎

\end{code}

NB. If we write the above chain of equations in the usual TypeTopology
style, e.g. using roman numbers for the equality proofs defined in a
`where` clause (as in some examples below), we get a number of
unsolved constraints.

\begin{code}

semidecider : {u : ℕ∞} → ⟨ α̅ u ⟩ → ℕ∞
semidecider ξ = raw-semidecider ξ , raw-semidecider-is-decreasing ξ

finite-semidecider-gives-𝓕 : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩)
                           → is-finite (semidecider ξ)
                           → 𝓕 ξ
finite-semidecider-gives-𝓕 {u} ξ (n , p) = h (ι u n) refl
 where
  I : raw-semidecider ξ n ＝ ₀
  I = raw-semidecider ξ n ＝⟨ (ap (λ - → ι - n) p)⁻¹ ⟩
      ι (ι n) n           ＝⟨ ℕ-to-ℕ∞-diagonal₀ n ⟩
      ₀                   ∎

  h : (c : 𝟚) → ι u n ＝ c → 𝓕 ξ
  h ₁ e = 𝟘-elim (zero-is-not-one
                   (₀                   ＝⟨ I ⁻¹ ⟩
                    raw-semidecider ξ n ＝⟨ 𝟚-equality-cases₁ e ⟩
                    ₁                   ∎))
  h ₀ e = φ , complement₀ q
   where
    φ : is-finite u
    φ = ϕ e

    q : complement (ξ φ) ＝ ₀
    q = complement (ξ φ)    ＝⟨ (𝟚-equality-cases₀ e)⁻¹ ⟩
        raw-semidecider ξ n ＝⟨ I ⟩
        ₀                   ∎

𝓕-gives-finite-semidecider : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩)
                           → 𝓕 ξ
                           → is-finite (semidecider ξ)
𝓕-gives-finite-semidecider {u} ξ ((n , p) , geq) = n , ((IV n I III)⁻¹)
 where
  I : (m : ℕ) → m < n → raw-semidecider ξ m ＝ ₁
  I m l = 𝟚-equality-cases₁ I₀
   where
    I₀ : ι u m ＝ ₁
    I₀ = ι u m     ＝⟨ (ap (λ w → ι w m) p)⁻¹ ⟩
         ι (ι n) m ＝⟨ <-gives-⊏ m n l ⟩
         ₁         ∎

  II : ι u n ＝ ₀
  II = ι u n     ＝⟨ (ap (λ w → ι w n) p)⁻¹ ⟩
       ι (ι n) n ＝⟨ ℕ-to-ℕ∞-diagonal₀ n ⟩
       ₀         ∎

  III : raw-semidecider ξ n ＝ ₀
  III = raw-semidecider ξ n    ＝⟨ 𝟚-equality-cases₀ II ⟩
        complement (ξ (ϕ II))  ＝⟨ ap (λ - → complement (ξ -))
                                      (finiteness-is-prop (ϕ II) (n , p)) ⟩
        complement (ξ (n , p)) ＝⟨ ap complement geq ⟩
        ₀                      ∎

  IV : (n : ℕ)
     → ((m : ℕ) → m < n → raw-semidecider ξ m ＝ ₁)
     → raw-semidecider ξ n ＝ ₀
     → semidecider ξ ＝ ι n
  IV 0         lt a = is-Zero-equal-Zero fe' a
  IV (succ n') lt a = Succ-criterion fe' (lt n' (<-succ n')) a

𝓕-≃-finite-semidecider : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩)
                       → 𝓕 ξ ≃ is-finite (semidecider ξ)
𝓕-≃-finite-semidecider ξ = logically-equivalent-props-are-equivalent
                            (𝓕-is-prop ξ)
                            finiteness-is-prop
                            (𝓕-gives-finite-semidecider ξ)
                            (finite-semidecider-gives-𝓕 ξ)

𝓕-is-semidecidable : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩) → is-semidecidable (𝓕 ξ)
𝓕-is-semidecidable ξ = ∣ semidecider ξ , 𝓕-≃-finite-semidecider ξ ∣

𝔽 : {u : ℕ∞} → ⟨ α̅ u ⟩ → 𝕊
𝔽 ξ = (𝓕 ξ , 𝓕-is-prop ξ) , 𝓕-is-semidecidable ξ

\end{code}

We now show that 𝔽 is order preserving.

\begin{code}

disjoint-fibers : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩) → fiber ξ ₀ → fiber ξ ₁ → 𝟘
disjoint-fibers ξ (φ₀ , e₀) (φ₁ , e₁) = one-is-not-zero I
 where
  I : ₁ ＝ ₀
  I = ₁    ＝⟨ e₁ ⁻¹ ⟩
      ξ φ₁ ＝⟨ ap ξ (finiteness-is-prop φ₁ φ₀) ⟩
      ξ φ₀ ＝⟨ e₀ ⟩
      ₀    ∎

𝔽-is-order-preserving : {u : ℕ∞} → is-order-preserving (α̅ u) 𝓢 𝔽
𝔽-is-order-preserving ξ₁ ξ₂ (φ , l) =
 (λ s → 𝟘-elim (disjoint-fibers ξ₁ (φ , ≺₂-left l) s)) ,
 (φ , ≺₂-right l)

\end{code}

If the lower sets of ξ and ξ' in the ordinals α̅ u and α̅ u' are equal,
then so are 𝔽 ξ and 𝔽 ξ'.

\begin{code}

↓-to-𝔽-＝ : {u u' : ℕ∞} (ξ : ⟨ α̅ u ⟩) (ξ' : ⟨ α̅ u' ⟩)
         → α̅ u ↓ ξ ＝ α̅ u' ↓ ξ'
         → 𝔽 ξ ＝ 𝔽 ξ'
↓-to-𝔽-＝ {u} {u'} ξ ξ' e = to-𝕊-＝ (IV , V)
 where
  I : (Σ ζ ꞉ ⟨ α̅ u ⟩ , ζ ≺⟨ α̅ u ⟩ ξ) ＝ (Σ ζ' ꞉ ⟨ α̅ u' ⟩ , ζ' ≺⟨ α̅ u' ⟩ ξ')
  I = ap ⟨_⟩ e

  II : {w : ℕ∞} (ρ : ⟨ α̅ w ⟩) → 𝓕 ρ → Σ ζ ꞉ ⟨ α̅ w ⟩ , ζ ≺⟨ α̅ w ⟩ ρ
  II ρ (φ , e₂) = 𝟎 , φ , ≺₂-left-right refl e₂

  III : {w w' : ℕ∞} (ξ : ⟨ α̅ w ⟩) (ξ' : ⟨ α̅ w' ⟩)
      → ((Σ ζ ꞉ ⟨ α̅ w ⟩ , ζ ≺⟨ α̅ w ⟩ ξ) → (Σ ζ' ꞉ ⟨ α̅ w' ⟩ , ζ' ≺⟨ α̅ w' ⟩ ξ'))
      → 𝓕 ξ
      → 𝓕 ξ'
  III {w} {w'} ξ ξ' h s = III₀ (h (II ξ s))
   where
    III₀ : (Σ ζ' ꞉ ⟨ α̅ w' ⟩ , ζ' ≺⟨ α̅ w' ⟩ ξ') → 𝓕 ξ'
    III₀ (ζ' , ψ , l) = ψ , ≺₂-right l

  IV : 𝓕 ξ → 𝓕 ξ'
  IV = III ξ ξ' (Idtofun I)

  V : 𝓕 ξ' → 𝓕 ξ
  V = III ξ' ξ (Idtofun (I ⁻¹))

θ-to-𝔽-＝ : {u u' : ℕ∞} {ξ : ⟨ α̅ u ⟩} {ξ' : ⟨ α̅ u' ⟩}
         → θ ξ ＝ θ ξ'
         → 𝔽 ξ ＝ 𝔽 ξ'
θ-to-𝔽-＝ {u} {u'} {ξ} {ξ'} e = ↓-to-𝔽-＝ ξ ξ' I
 where
  I : α̅ u ↓ ξ ＝ α̅ u' ↓ ξ'
  I = α̅ u ↓ ξ   ＝⟨ (θ-downset ξ)⁻¹ ⟩
      𝓼 ↓ θ ξ   ＝⟨ ap (𝓼 ↓_) e ⟩
      𝓼 ↓ θ ξ'  ＝⟨ θ-downset ξ' ⟩
      α̅ u' ↓ ξ' ∎

\end{code}

We now define a map τ : ⟨ 𝓼 ⟩ → 𝕊 by first defining a type-valued
version T of it, after showing that it is singleton-valued. Although
T-point gives data, it is defined by propositional-truncation
induction, and, for that purpose, we first need to show that T is
proposition valued. Getting the construction of τ using something such
as T was the biggest headache of this file, luckily with a
simple-looking solution.

\begin{code}

T : ⟨ 𝓼 ⟩ → 𝓤₁ ̇
T y = Σ t ꞉ 𝕊 , ((u : ℕ∞) (ξ : ⟨ α̅ u ⟩) → θ ξ ＝ y → 𝔽 ξ ＝ t)

T-is-prop-valued : (y : ⟨ 𝓼 ⟩) → is-prop (T y)
T-is-prop-valued y (t , h) (t' , h') =
 to-subtype-＝
  (λ - → Π₃-is-prop fe' (λ u ξ e → 𝕊-is-set))
  (∥∥-rec 𝕊-is-set (λ (u , ξ , e) → t   ＝⟨ (h u ξ e)⁻¹ ⟩
                                    𝔽 ξ ＝⟨ h' u ξ e ⟩
                                    t'  ∎)
  (θ-is-jointly-surjective y))

T-point : (y : ⟨ 𝓼 ⟩) → T y
T-point y = ∥∥-rec (T-is-prop-valued y) I (θ-is-jointly-surjective y)
 where
  I : (Σ u ꞉ ℕ∞ , Σ ξ ꞉ ⟨ α̅ u ⟩ , θ ξ ＝ y) → T y
  I (u , ξ , e) = 𝔽 ξ , (λ u' ξ' e' → θ-to-𝔽-＝ (I₀ ξ' e'))
   where
    I₀ : {u' : ℕ∞} (ξ' : ⟨ α̅ u' ⟩) → θ ξ' ＝ y → θ ξ' ＝ θ ξ
    I₀ ξ' e' = θ ξ' ＝⟨ e' ⟩
               y    ＝⟨ e ⁻¹ ⟩
               θ ξ  ∎

τ : ⟨ 𝓼 ⟩ → 𝕊
τ y = pr₁ (T-point y)

\end{code}

We have that τ ∘ θ ∼ 𝔽. For future use, it is convenient to formulate
this in the following equivalent form, and in any case this is what
the definition of T gives directly.

\begin{code}

by-construction-of-τ : {u : ℕ∞} (ξ : ⟨ α̅ u ⟩) (y : ⟨ 𝓼 ⟩)
                     → θ ξ ＝ y
                     → τ y ＝ 𝔽 ξ
by-construction-of-τ {u} ξ y e = (pr₂ (T-point y) u ξ e)⁻¹

τ-fiber-transport : {y : ⟨ 𝓼 ⟩} {t t' : 𝕊}
                  → t ＝ t'
                  → (Σ y₀ ꞉ ⟨ 𝓼 ⟩ , (y₀ ≺⟨ 𝓼 ⟩ y) × (τ y₀ ＝ t))
                  → (Σ y₀ ꞉ ⟨ 𝓼 ⟩ , (y₀ ≺⟨ 𝓼 ⟩ y) × (τ y₀ ＝ t'))
τ-fiber-transport refl σ = σ

τ-⊥-no-preds : (u : ℕ∞) (ξ : ⟨ α̅ u ⟩) (y z : ⟨ 𝓼 ⟩)
             → θ ξ ＝ y
             → τ y ＝ ⊥ₛ
             → ¬ (z ≺⟨ 𝓼 ⟩ y)
τ-⊥-no-preds u ξ y z e c l = II (θ-is-initial-segment ξ z l')
 where
  l' : z ≺⟨ 𝓼 ⟩ θ ξ
  l' = ≺-transportᵣ (e ⁻¹) l

  I : 𝔽 ξ ＝ ⊥ₛ
  I = 𝔽 ξ ＝⟨ (by-construction-of-τ ξ y e)⁻¹ ⟩
      τ y ＝⟨ c ⟩
      ⊥ₛ  ∎

  II : (Σ ξ₀ ꞉ ⟨ α̅ u ⟩ , (ξ₀ ≺⟨ α̅ u ⟩ ξ) × (θ ξ₀ ＝ z)) → 𝟘 {𝓤₀}
  II (ξ₀ , m , p) = transport (λ - → δ - holds) I
                     (pr₂ (𝔽-is-order-preserving ξ₀ ξ m))

τ-lc-at-⊥ : (y y' : ⟨ 𝓼 ⟩) → τ y ＝ ⊥ₛ → τ y' ＝ ⊥ₛ → y ＝ y'
τ-lc-at-⊥ y y' c c' =
 ∥∥-rec₂ 𝓼-is-set I (θ-is-jointly-surjective y) (θ-is-jointly-surjective y')
 where
  I : (Σ u  ꞉ ℕ∞ , Σ ξ  ꞉ ⟨ α̅ u  ⟩ , θ ξ  ＝ y)
    → (Σ u' ꞉ ℕ∞ , Σ ξ' ꞉ ⟨ α̅ u' ⟩ , θ ξ' ＝ y')
    → y ＝ y'
  I (u , ξ , e) (u' , ξ' , e') = Extensionality 𝓼 y y' f g
   where
    f : (z : ⟨ 𝓼 ⟩) → z ≺⟨ 𝓼 ⟩ y → z ≺⟨ 𝓼 ⟩ y'
    f z l = 𝟘-elim (τ-⊥-no-preds u ξ y z e c l)

    g : (z : ⟨ 𝓼 ⟩) → z ≺⟨ 𝓼 ⟩ y' → z ≺⟨ 𝓼 ⟩ y
    g z l = 𝟘-elim (τ-⊥-no-preds u' ξ' y' z e' c' l)

\end{code}

We now show that the map τ is a simulation. For the initial-segment
property, the crucial point is that the only ≺ₛ-predecessor of
anything is ⊥ₛ, whose τ-preimages are unique by the previous lemma, so
that the required Σ-type is a proposition.

\begin{code}

τ-lemma₁ : (y y' : ⟨ 𝓼 ⟩)
         → {u  : ℕ∞} (ξ  : ⟨ α̅ u ⟩)
           {u' : ℕ∞} (ξ' : ⟨ α̅ u' ⟩)
         → θ ξ  ＝ y
         → θ ξ' ＝ y'
         → y ≺⟨ 𝓼 ⟩ y'
         → τ y ≺ₛ τ y'
τ-lemma₁ y y' ξ {u'} ξ' e e' l = III (θ-is-initial-segment ξ' (θ ξ) II)
 where
  I : θ ξ ≺⟨ 𝓼 ⟩ y'
  I = ≺-transportₗ (e ⁻¹) l

  II : θ ξ ≺⟨ 𝓼 ⟩ θ ξ'
  II = ≺-transportᵣ (e' ⁻¹) I

  III : (Σ ξ₀ ꞉ ⟨ α̅ u' ⟩ , (ξ₀ ≺⟨ α̅ u' ⟩ ξ') × (θ ξ₀ ＝ θ ξ))
      → τ y ≺ₛ τ y'
  III (ξ₀ , m , p) = III₅
   where
    III₀ : 𝔽 ξ₀ ≺ₛ 𝔽 ξ'
    III₀ = 𝔽-is-order-preserving ξ₀ ξ' m

    III₁ : 𝔽 ξ' ＝ τ y'
    III₁ = (by-construction-of-τ ξ' y' e') ⁻¹

    III₂ : θ ξ₀ ＝ y
    III₂ = θ ξ₀ ＝⟨ p ⟩
           θ ξ  ＝⟨ e ⟩
           y    ∎

    III₃ : 𝔽 ξ₀ ＝ τ y
    III₃ = (by-construction-of-τ ξ₀ y III₂) ⁻¹

    III₄ : 𝔽 ξ₀ ≺ₛ τ y'
    III₄ = ≺ₛ-transportᵣ {𝔽 ξ₀} {𝔽 ξ'} {τ y'} III₁ III₀

    III₅ : τ y ≺ₛ τ y'
    III₅ = ≺ₛ-transportₗ {𝔽 ξ₀} {τ y} {τ y'} III₃ III₄

τ-is-order-preserving : is-order-preserving 𝓼 𝓢 τ
τ-is-order-preserving y y' l =
 ∥∥-rec (≺ₛ-prop-valued (τ y) (τ y'))
  (λ (u , ξ , e) → ∥∥-rec
                     (≺ₛ-prop-valued (τ y) (τ y'))
                     (λ (u' , ξ' , e') → τ-lemma₁ y y' ξ ξ' e e' l)
                     (θ-is-jointly-surjective y'))
  (θ-is-jointly-surjective y)

τ-lemma₂ : (y : ⟨ 𝓼 ⟩) {u : ℕ∞} (ξ : ⟨ α̅ u ⟩)
         → θ ξ ＝ y
         → 𝓕 ξ
         → Σ y₀ ꞉ ⟨ 𝓼 ⟩ , (y₀ ≺⟨ 𝓼 ⟩ y) × (τ y₀ ＝ ⊥ₛ)
τ-lemma₂ y ξ e (φ , e') = θ 𝟎 , II , III
 where
  I : θ 𝟎 ≺⟨ 𝓼 ⟩ θ ξ
  I = θ-is-order-preserving 𝟎 ξ (φ , ≺₂-left-right refl e')

  II : θ 𝟎 ≺⟨ 𝓼 ⟩ y
  II = ≺-transportᵣ e I

  III : τ (θ 𝟎) ＝ ⊥ₛ
  III = τ (θ 𝟎) ＝⟨ by-construction-of-τ 𝟎 (θ 𝟎) refl ⟩
        𝔽 𝟎     ＝⟨ to-𝕊-＝ ((disjoint-fibers 𝟎 (φ , refl)) , 𝟘-elim) ⟩
        ⊥ₛ       ∎

τ-is-initial-segment : is-initial-segment 𝓼 𝓢 τ
τ-is-initial-segment y t (ν , h) = V
 where
  I : ⊥ₛ ＝ t
  I = to-𝕊-＝ (𝟘-elim , (λ s → 𝟘-elim (ν s)))

  II : is-prop (Σ y₀ ꞉ ⟨ 𝓼 ⟩ , (y₀ ≺⟨ 𝓼 ⟩ y) × (τ y₀ ＝ ⊥ₛ))
  II (y₀ , m , c) (y₀' , m' , c') =
   to-subtype-＝
    (λ y₁ → ×-is-prop (Prop-valuedness 𝓼 y₁ y) 𝕊-is-set)
    (τ-lc-at-⊥ y₀ y₀' c c')

  III : (Σ u ꞉ ℕ∞ , Σ ξ ꞉ ⟨ α̅ u ⟩ , θ ξ ＝ y)
      → Σ y₀ ꞉ ⟨ 𝓼 ⟩ , (y₀ ≺⟨ 𝓼 ⟩ y) × (τ y₀ ＝ ⊥ₛ)
  III (u , ξ , e) = τ-lemma₂ y ξ e s
   where
    s : 𝓕 ξ
    s = transport (λ - → δ - holds) (by-construction-of-τ ξ y e) h

  IV : Σ y₀ ꞉ ⟨ 𝓼 ⟩ , (y₀ ≺⟨ 𝓼 ⟩ y) × (τ y₀ ＝ ⊥ₛ)
  IV = ∥∥-rec II III (θ-is-jointly-surjective y)

  V : Σ y₀ ꞉ ⟨ 𝓼 ⟩ , (y₀ ≺⟨ 𝓼 ⟩ y) × (τ y₀ ＝ t)
  V = τ-fiber-transport I IV

\end{code}

Which gives the desired conclusion.

\begin{code}

τ-is-simulation : is-simulation 𝓼 𝓢 τ
τ-is-simulation = τ-is-initial-segment , τ-is-order-preserving

\end{code}

We continue with more lemmas about τ.

\begin{code}

τ-is-surjection : is-surjection τ
τ-is-surjection (p , σ) = IV
 where
  I : (Σ u ꞉ ℕ∞ , (p holds ≃ is-finite u))
    → fiber τ (p , σ)
  I (u , 𝕗) = θ 𝟏 , III
   where
    II : 𝔽 𝟏 ＝ (p , σ)
    II = to-𝕊-＝ (II₀ , II₁)
     where
      II₀ : 𝓕 𝟏 → p holds
      II₀ (φ , _) = ⌜ 𝕗 ⌝⁻¹ φ

      II₁ : p holds → 𝓕 𝟏
      II₁ s = ⌜ 𝕗 ⌝ s , refl

    III : τ (θ 𝟏) ＝ (p , σ)
    III = τ (θ 𝟏) ＝⟨ by-construction-of-τ 𝟏 (θ 𝟏) refl ⟩
          𝔽 𝟏     ＝⟨ II ⟩
          (p , σ)  ∎

  IV : ∥ fiber τ (p , σ) ∥
  IV = ∥∥-functor I σ

\end{code}

A surjective simulation is an order equivalence, and so we get the
promised description of the supremum.

\begin{code}

τ-lc : left-cancellable τ
τ-lc = simulations-are-lc 𝓼 𝓢 τ τ-is-simulation

τ-is-embedding : is-embedding τ
τ-is-embedding = lc-maps-into-sets-are-embeddings τ τ-lc 𝕊-is-set

τ-is-equiv : is-equiv τ
τ-is-equiv = surjective-embeddings-are-equivs τ τ-is-embedding τ-is-surjection

τ-is-order-reflecting : is-order-reflecting 𝓼 𝓢 τ
τ-is-order-reflecting y y' l = I (τ-is-initial-segment y' (τ y) l)
 where
  I : (Σ y₀ ꞉ ⟨ 𝓼 ⟩ , (y₀ ≺⟨ 𝓼 ⟩ y') × (τ y₀ ＝ τ y)) → y ≺⟨ 𝓼 ⟩ y'
  I (y₀ , m , c) = ≺-transportₗ (τ-lc c) m

τ⁻¹ : 𝕊 → ⟨ 𝓼 ⟩
τ⁻¹ = inverse τ τ-is-equiv

τ⁻¹-is-order-preserving : is-order-preserving 𝓢 𝓼 τ⁻¹
τ⁻¹-is-order-preserving =
 order-reflecting-gives-inverse-order-preserving 𝓼 𝓢 τ τ-is-equiv
  τ-is-order-reflecting

\end{code}

Therefore, as promised, the sup of α̅ is 𝓢:

\begin{code}

𝓼-is-𝓢 : 𝓼 ≃ₒ 𝓢
𝓼-is-𝓢 = τ , τ-is-order-preserving , τ-is-equiv , τ⁻¹-is-order-preserving

⟨𝓼⟩-is-𝕊 : ⟨ 𝓼 ⟩ ≃ 𝕊
⟨𝓼⟩-is-𝕊 = ≃ₒ-gives-≃ 𝓼 𝓢 𝓼-is-𝓢

\end{code}

As a corollary, we conclude that, although 𝕊 lives in 𝓤₁ by
construction, it has a copy in 𝓤₀, as mentioned above.

\begin{code}

𝕊-is-small : is-small 𝕊
𝕊-is-small = ⟨ 𝓼 ⟩ , ⟨𝓼⟩-is-𝕊

\end{code}

The underlying type of the ordinal 𝓼, or equivalently the type 𝕊,
fails to be totally separated in general in the following sense: its
total separatedness implies the constructive taboo ¬¬ WLPO, which is a
principle that fails in both Johnstone's Topological Topos and Hylands
Effective Topos, for instance.

\begin{code}

open import TypeTopology.TotallySeparated
open import Taboos.WLPO
open import Taboos.BasicDiscontinuity fe'

being-finite-is-semidecidable : (u : ℕ∞) → is-semidecidable (is-finite u)
being-finite-is-semidecidable u = ∣ u , ≃-refl (is-finite u) ∣

is-fin : ℕ∞ → 𝕊
is-fin u = (is-finite u , being-finite-is-prop fe' u) ,
           being-finite-is-semidecidable u

naturals-are-fin : (n : ℕ) → is-fin (ι n) ＝ ⊤ₛ
naturals-are-fin n = to-𝕊-＝ ((λ _ → ⋆) , (λ _ → n , refl))

∞-is-not-fin : is-fin ∞ ＝ ⊥ₛ
∞-is-not-fin = to-𝕊-＝ (is-infinite-∞ , 𝟘-elim)

⊥ₛ-is-not-⊤ₛ : ⊥ₛ ≠ ⊤ₛ
⊥ₛ-is-not-⊤ₛ e = transport (λ - → δ - holds) (e ⁻¹) ⋆

𝕊-separation-gives-WLPO : (p : 𝕊 → 𝟚) → p ⊥ₛ ≠ p ⊤ₛ → WLPO
𝕊-separation-gives-WLPO p ν = h (p ⊥ₛ) (p ⊤ₛ) refl refl
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
  h ₁ ₁ e e' = 𝟘-elim (ν (p ⊥ₛ ＝⟨ e ⟩
                          ₁    ＝⟨ e' ⁻¹ ⟩
                          p ⊤ₛ ∎))

𝕊-totally-separated-gives-¬¬WLPO : is-totally-separated 𝕊 → ¬¬ WLPO
𝕊-totally-separated-gives-¬¬WLPO ts nwlpo = ⊥ₛ-is-not-⊤ₛ (ts I)
 where
  I : (p : 𝕊 → 𝟚) → p ⊥ₛ ＝ p ⊤ₛ
  I p = h (p ⊥ₛ) (p ⊤ₛ) refl refl
   where
    h : (b c : 𝟚) → p ⊥ₛ ＝ b → p ⊤ₛ ＝ c → p ⊥ₛ ＝ p ⊤ₛ
    h ₀ ₀ e e' = p ⊥ₛ ＝⟨ e ⟩
                 ₀    ＝⟨ e' ⁻¹ ⟩
                 p ⊤ₛ ∎
    h ₀ ₁ e e' = 𝟘-elim (nwlpo (𝕊-separation-gives-WLPO p ν))
     where
      ν : p ⊥ₛ ≠ p ⊤ₛ
      ν d = zero-is-not-one (₀    ＝⟨ e ⁻¹ ⟩
                             p ⊥ₛ ＝⟨ d ⟩
                             p ⊤ₛ ＝⟨ e' ⟩
                             ₁    ∎)
    h ₁ ₀ e e' = 𝟘-elim (nwlpo (𝕊-separation-gives-WLPO p ν))
     where
      ν : p ⊥ₛ ≠ p ⊤ₛ
      ν d = one-is-not-zero (₁    ＝⟨ e ⁻¹ ⟩
                             p ⊥ₛ ＝⟨ d ⟩
                             p ⊤ₛ ＝⟨ e' ⟩
                             ₀    ∎)
    h ₁ ₁ e e' = p ⊥ₛ ＝⟨ e ⟩
                 ₁    ＝⟨ e' ⁻¹ ⟩
                 p ⊤ₛ ∎

𝓼-totally-separated-gives-¬¬WLPO : is-totally-separated ⟨ 𝓼 ⟩ → ¬¬ WLPO
𝓼-totally-separated-gives-¬¬WLPO ts =
 𝕊-totally-separated-gives-¬¬WLPO (equiv-to-totally-separated ⟨𝓼⟩-is-𝕊 ts)

\end{code}

Putting the above together, we get the desired counter-example
discussed in the introduction to this file.

\begin{code}

open import TypeTopology.CompactTypes
open import TypeTopology.GenericConvergentSequenceCompactness fe'
open import TypeTopology.MicroTychonoff

counterexample-to-total-separatedess
 : Σ I ꞉ (𝓤₀ ̇ ) ,
   Σ α ꞉ (I → Ordinal 𝓤₀) , ((is-compact∙ I)
                          × (is-totally-separated I)
                          × ((i : I) → is-compact∙ ⟨ α i ⟩)
                          × ((i : I) → is-totally-separated ⟨ α i ⟩)
                          × (is-totally-separated ⟨ sup α ⟩ → ¬¬ WLPO))
counterexample-to-total-separatedess =
 ℕ∞ ,
 α̅ ,
 ℕ∞-compact∙ ,
 ℕ∞-is-totally-separated fe' ,
 (λ i → micro-tychonoff fe' (ℕ-to-ℕ∞-is-embedding fe' i) (λ _ → 𝟚-is-compact∙)) ,
 (λ i → Π-is-totally-separated fe' (λ _ → 𝟚-is-totally-separated)) ,
 𝓼-totally-separated-gives-¬¬WLPO

\end{code}

We now get back to our main concern, the sup-of-extension
interpretation ⟦_⟧₂ discussed in the introduction to this file. In
order to make sense of the proof below, remember our remark that this
non-standard interpretation maps Z to one rather than zero.

\begin{code}

open import Ordinals.BrouwerCodes
open import Ordinals.BrouwerCodesInterpretations ua pt sr using (⟦_⟧₂)
open import Ordinals.Arithmetic fe renaming (𝟚ₒ to 𝟚ₒ-standard)

total-separatedness-of-the-sup-of-extension-interpretation-gives-¬¬WLPO
 : ((b : B) → is-totally-separated ⟨ ⟦ b ⟧₂ ⟩) → ¬¬ WLPO
total-separatedness-of-the-sup-of-extension-interpretation-gives-¬¬WLPO ts
 = V
 where
  _ : ⟦ Z ⟧₂ ＝ 𝟙ₒ
  _ = refl

  _ : ⟦ S Z ⟧₂ ＝ 𝟚ₒ-standard
  _ = refl

  I : 𝟚ₒ ＝ ⟦ S Z ⟧₂
  I = eqtoidₒ (ua 𝓤₀) fe' 𝟚ₒ ⟦ S Z ⟧₂ (𝟚₀-agrees-with-𝟚₀-standard fe)

  b : B
  b = L (λ _ → S Z)

  II : ⟦ b ⟧₂ ＝ 𝓼
  II = ap (sup ∘ extension) (dfunext fe' (λ _ → I ⁻¹))

  III : is-totally-separated ⟨ ⟦ b ⟧₂ ⟩
  III = ts b

  IV : is-totally-separated ⟨ 𝓼 ⟩
  IV = transport (λ - → is-totally-separated ⟨ - ⟩) II III

  V : ¬¬ WLPO
  V = 𝓼-totally-separated-gives-¬¬WLPO IV

\end{code}
