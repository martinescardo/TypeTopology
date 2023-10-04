Tom de Jong, early January 2022.

We define small (compact) basis for dcpos. Our notion of a small basis is almost
like in classical domain theory [1,2], but includes an additional smallness
condition, that is similar but different to Aczel's [3] notion of a
set-generated dcpo. A similar smallness criterion in the context of category
theory also appears in [Proposition 2.16, 4].

A notable feature of dcpos with small bases is that they and their exponentials
are locally small.

In IdealCompletion-Properties, we show that having a small basis is equivalent
to being presented by ideals.

If a dcpo has a small basis, then it continuous. In fact, all our examples of
continuous and algebraic dcpos are actually examples of dcpos with small
(compact) bases.

[1] Definition III-4.1 in "Continuous lattices and domains" by Gierz. et al.
[2] Section 2.2.2 of "Domain Theory" by Abramsky and Jung
[3] "Aspects of general topology in constructive set theory" by Aczel
[4] "Continuous categories and exponentiable toposes" by Johnstone and Joyal

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan hiding (J)
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.BasesAndContinuity.Bases
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Size hiding (is-small ; is-locally-small)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.WayBelow pt fe 𝓥

open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓥

\end{code}

The idea of a small basis is that we have a small-indexed family β : B → D into
a dcpo such that for every x : D, the collection of b : B such that β b ≪ x is
small, directed and has supremum x. Thus, if we wish to approximate an element
of D, we only need the elements of B to do so.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇ }
        (β : B → ⟨ 𝓓 ⟩)
       where

 ↡ᴮ : ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 ↡ᴮ x = Σ b ꞉ B , β b ≪⟨ 𝓓 ⟩ x

 ↡-inclusion : (x : ⟨ 𝓓 ⟩) → ↡ᴮ x → ⟨ 𝓓 ⟩
 ↡-inclusion x = β ∘ pr₁

 record is-small-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
  field
   ≪ᴮ-is-small : (x : ⟨ 𝓓 ⟩) (b : B) → is-small (β b ≪⟨ 𝓓 ⟩ x)
   ↡ᴮ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↡-inclusion x)
   ↡ᴮ-is-sup : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x (↡-inclusion x)

\end{code}

Notice how we required β b ≪ x to be a small type for every b : B and x : D. We
write some boiler plate around that.

\begin{code}

  _≪ᴮₛ_ : (b : B) (x : ⟨ 𝓓 ⟩) → 𝓥 ̇
  b ≪ᴮₛ x = pr₁ (≪ᴮ-is-small x b)

  ≪ᴮₛ-≃-≪ᴮ : {b : B} {x : ⟨ 𝓓 ⟩} → (b ≪ᴮₛ x) ≃ (β b ≪⟨ 𝓓 ⟩ x)
  ≪ᴮₛ-≃-≪ᴮ {b} {x} = pr₂ (≪ᴮ-is-small x b)

  ≪ᴮₛ-to-≪ᴮ : {b : B} {x : ⟨ 𝓓 ⟩} → (b ≪ᴮₛ x) → (β b ≪⟨ 𝓓 ⟩ x)
  ≪ᴮₛ-to-≪ᴮ = ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝

  ≪ᴮ-to-≪ᴮₛ : {b : B} {x : ⟨ 𝓓 ⟩} → (β b ≪⟨ 𝓓 ⟩ x) → (b ≪ᴮₛ x)
  ≪ᴮ-to-≪ᴮₛ = ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹

  ≪ᴮₛ-is-prop-valued : {b : B} {x : ⟨ 𝓓 ⟩} → is-prop (b ≪ᴮₛ x)
  ≪ᴮₛ-is-prop-valued = equiv-to-prop ≪ᴮₛ-≃-≪ᴮ (≪-is-prop-valued 𝓓)

  ↡ᴮₛ : ⟨ 𝓓 ⟩ → 𝓥 ̇
  ↡ᴮₛ x = Σ b ꞉ B , (b ≪ᴮₛ x)

  ↡-inclusionₛ : (x : ⟨ 𝓓 ⟩) → ↡ᴮₛ x → ⟨ 𝓓 ⟩
  ↡-inclusionₛ x = β ∘ pr₁

  ↡ᴮₛ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↡-inclusionₛ x)
  ↡ᴮₛ-is-directed x = reindexed-family-is-directed 𝓓
                       (Σ-cong (λ b → ≃-sym ≪ᴮₛ-≃-≪ᴮ))
                       (↡-inclusion x) (↡ᴮ-is-directed x)

  ↡ᴮₛ-∐-＝ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (↡ᴮₛ-is-directed x) ＝ x
  ↡ᴮₛ-∐-＝ x = antisymmetry 𝓓 (∐ 𝓓 (↡ᴮₛ-is-directed x)) x ⦅1⦆ ⦅2⦆
   where
    ⦅1⦆ : ∐ 𝓓 (↡ᴮₛ-is-directed x) ⊑⟨ 𝓓 ⟩ x
    ⦅1⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 (↡ᴮₛ-is-directed x) x
          (λ (b , u) → sup-is-upperbound (underlying-order 𝓓) (↡ᴮ-is-sup x)
                        (b , ≪ᴮₛ-to-≪ᴮ u))
    ⦅2⦆ : x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↡ᴮₛ-is-directed x)
    ⦅2⦆ = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓) (↡ᴮ-is-sup x)
          (∐ 𝓓 (↡ᴮₛ-is-directed x))
          (λ (b , v) → ∐-is-upperbound 𝓓 (↡ᴮₛ-is-directed x)
                        (b , ≪ᴮ-to-≪ᴮₛ v))

  ↡ᴮₛ-∐-⊑ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (↡ᴮₛ-is-directed x) ⊑⟨ 𝓓 ⟩ x
  ↡ᴮₛ-∐-⊑ x = ＝-to-⊑ 𝓓 (↡ᴮₛ-∐-＝ x)

  ↡ᴮₛ-∐-⊒ : (x : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↡ᴮₛ-is-directed x)
  ↡ᴮₛ-∐-⊒ x = ＝-to-⊒ 𝓓 (↡ᴮₛ-∐-＝ x)

  ↡ᴮₛ-is-way-below : (x : ⟨ 𝓓 ⟩) (b : ↡ᴮₛ x) → ↡-inclusionₛ x b ≪⟨ 𝓓 ⟩ x
  ↡ᴮₛ-is-way-below x (b , u) = ≪ᴮₛ-to-≪ᴮ u

\end{code}

We prove that being a small basis is a property, for which we first show that
our record-based definition is equivalent to one using Σ-types.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇ }
        (β : B → ⟨ 𝓓 ⟩)
       where

 is-small-basis-Σ : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 is-small-basis-Σ = (x : ⟨ 𝓓 ⟩) → ((b : B) → is-small (β b ≪⟨ 𝓓 ⟩ x))
                                × is-Directed 𝓓 (↡-inclusion 𝓓 β x)
                                × is-sup (underlying-order 𝓓) x
                                         (↡-inclusion 𝓓 β x)

 being-small-basis-Σ-is-prop : Prop-Ext → is-prop is-small-basis-Σ
 being-small-basis-Σ-is-prop pe =
  Π-is-prop fe (λ x →
   ×₃-is-prop (Π-is-prop fe
               (λ b → prop-being-small-is-prop (λ _ → pe) (λ _ _ → fe)
                       (β b ≪⟨ 𝓓 ⟩ x) (≪-is-prop-valued 𝓓)))
              (being-directed-is-prop (underlying-order 𝓓) (↡-inclusion 𝓓 β x))
              (is-sup-is-prop (underlying-order 𝓓) (pr₁ (axioms-of-dcpo 𝓓))
                              x (↡-inclusion 𝓓 β x)))

 is-small-basis-≃ : is-small-basis 𝓓 β ≃ is-small-basis-Σ
 is-small-basis-≃ = qinveq f (g , (λ _ → refl) , (λ _ → refl))
  where
   f : is-small-basis 𝓓 β → is-small-basis-Σ
   f sb x = (≪ᴮ-is-small x , ↡ᴮ-is-directed x , ↡ᴮ-is-sup x)
    where
     open is-small-basis sb
   g : is-small-basis-Σ → is-small-basis 𝓓 β
   g sb =
    record
     { ≪ᴮ-is-small = λ x → pr₁ (sb x)
     ; ↡ᴮ-is-directed = λ x → pr₁ (pr₂ (sb x))
     ; ↡ᴮ-is-sup  = λ x → pr₂ (pr₂ (sb x))
     }

 being-small-basis-is-prop : Prop-Ext → is-prop (is-small-basis 𝓓 β)
 being-small-basis-is-prop pe = equiv-to-prop is-small-basis-≃
                                 (being-small-basis-Σ-is-prop pe)

\end{code}

It follows almost immediately that a dcpo that comes equipped with a small basis
is structurally continuous and this in turn implies that a dcpo with some
unspecified small basis must be continuous.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 has-specified-small-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-specified-small-basis = Σ B ꞉ 𝓥 ̇  , Σ β ꞉ (B → ⟨ 𝓓 ⟩) , is-small-basis 𝓓 β

 has-unspecified-small-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-unspecified-small-basis = ∥ has-specified-small-basis ∥

 structurally-continuous-if-specified-small-basis : has-specified-small-basis
                                                  → structurally-continuous 𝓓
 structurally-continuous-if-specified-small-basis (B , β , sb) =
  record
   { index-of-approximating-family     = ↡ᴮₛ
   ; approximating-family              = ↡-inclusionₛ
   ; approximating-family-is-directed  = ↡ᴮₛ-is-directed
   ; approximating-family-is-way-below = ↡ᴮₛ-is-way-below
   ; approximating-family-∐-＝          = ↡ᴮₛ-∐-＝
   }
    where
     open is-small-basis sb

 is-continuous-dcpo-if-unspecified-small-basis : has-unspecified-small-basis
                                               → is-continuous-dcpo 𝓓
 is-continuous-dcpo-if-unspecified-small-basis =
  ∥∥-functor structurally-continuous-if-specified-small-basis

\end{code}

A useful consequence of having a small basis is that the dcpo in question must
be locally small, as we show now.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇ }
        (β : B → ⟨ 𝓓 ⟩)
        (sb : is-small-basis 𝓓 β)
       where

 open is-small-basis sb

 ⊑-in-terms-of-≪ᴮ : {x y : ⟨ 𝓓 ⟩}
                  → (x ⊑⟨ 𝓓 ⟩ y) ≃ (∀ (b : B) → β b ≪⟨ 𝓓 ⟩ x → β b ≪⟨ 𝓓 ⟩ y)
 ⊑-in-terms-of-≪ᴮ {x} {y} =
  logically-equivalent-props-are-equivalent
   (prop-valuedness 𝓓 x y)
   (Π₂-is-prop fe (λ b u → ≪-is-prop-valued 𝓓)) ⦅⇒⦆ ⦅⇐⦆
    where
     ⦅⇒⦆ : x ⊑⟨ 𝓓 ⟩ y → (∀ (b : B) → β b ≪⟨ 𝓓 ⟩ x → β b ≪⟨ 𝓓 ⟩ y)
     ⦅⇒⦆ x-below-y b b-way-below-x = ≪-⊑-to-≪ 𝓓 b-way-below-x x-below-y
     ⦅⇐⦆ : (∀ (b : B) → β b ≪⟨ 𝓓 ⟩ x → β b ≪⟨ 𝓓 ⟩ y) → x ⊑⟨ 𝓓 ⟩ y
     ⦅⇐⦆ h = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓)
             (↡ᴮ-is-sup x) y
             (λ (b , b-way-below-x) → ≪-to-⊑ 𝓓 (h b b-way-below-x))

 locally-small-if-small-basis : is-locally-small 𝓓
 locally-small-if-small-basis =
  ⌜ local-smallness-equivalent-definitions 𝓓 ⌝⁻¹ γ
   where
    γ : is-locally-small' 𝓓
    γ x y = (∀ (b : B) → b ≪ᴮₛ x → b ≪ᴮₛ y) , e
     where
      e = (∀ (b : B) → b ≪ᴮₛ x → b ≪ᴮₛ y)           ≃⟨ I   ⟩
          (∀ (b : B) → b ≪ᴮₛ x → β b ≪⟨ 𝓓 ⟩ y)      ≃⟨ II  ⟩
          (∀ (b : B) → β b ≪⟨ 𝓓 ⟩ x → β b ≪⟨ 𝓓 ⟩ y) ≃⟨ III ⟩
          x ⊑⟨ 𝓓 ⟩ y                                ■
       where
        I   = Π-cong fe fe (λ b → →cong fe fe (≃-refl (b ≪ᴮₛ x)) ≪ᴮₛ-≃-≪ᴮ)
        II  = Π-cong fe fe (λ b → →cong fe fe ≪ᴮₛ-≃-≪ᴮ (≃-refl (β b ≪⟨ 𝓓 ⟩ y)))
        III = ≃-sym (⊑-in-terms-of-≪ᴮ)

\end{code}

If a dcpo comes equipped with a small basis B, then the interpolants for the
way-below relation can be found in B.

\begin{code}

 ≪-nullary-interpolation-basis : (x : ⟨ 𝓓 ⟩) → ∃ b ꞉ B , β b ≪⟨ 𝓓 ⟩ x
 ≪-nullary-interpolation-basis x =
  ∥∥-functor id (inhabited-if-Directed 𝓓 (↡-inclusion 𝓓 β x) (↡ᴮ-is-directed x))

 ≪-unary-interpolation-basis : {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y
                             → ∃ b ꞉ B , (x ≪⟨ 𝓓 ⟩ β b) × (β b ≪⟨ 𝓓 ⟩ y)
 ≪-unary-interpolation-basis {x} {y} x-way-below-y =
  ∥∥-rec ∃-is-prop γ (≪-unary-interpolation-str 𝓓 C x-way-below-y)
   where
    C : structurally-continuous 𝓓
    C = structurally-continuous-if-specified-small-basis 𝓓 (B , β , sb)
    open structurally-continuous C
    γ : (Σ d ꞉ ⟨ 𝓓 ⟩ , x ≪⟨ 𝓓 ⟩ d × d ≪⟨ 𝓓 ⟩ y)
      → ∃ b ꞉ B , x ≪⟨ 𝓓 ⟩ (β b) × β b ≪⟨ 𝓓 ⟩ y
    γ (d , x-wb-d , d-wb-y) =
     ∥∥-functor σ (d-wb-y (↡ᴮₛ y) (↡-inclusionₛ y)
                          (↡ᴮₛ-is-directed y) (↡ᴮₛ-∐-⊒ y))
      where
       σ : (Σ b ꞉ ↡ᴮₛ y , d ⊑⟨ 𝓓 ⟩ ↡-inclusionₛ y b)
         → Σ b ꞉ B , x ≪⟨ 𝓓 ⟩ (β b) × β b ≪⟨ 𝓓 ⟩ y
       σ ((b , b-wb-y) , d-below-b) = b , ≪-⊑-to-≪ 𝓓 x-wb-d d-below-b
                                        , ≪ᴮₛ-to-≪ᴮ b-wb-y

 ≪-binary-interpolation-basis : {x y z : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ z → y ≪⟨ 𝓓 ⟩ z
                              → ∃ b ꞉ B , (x   ≪⟨ 𝓓 ⟩ β b)
                                        × (y   ≪⟨ 𝓓 ⟩ β b)
                                        × (β b ≪⟨ 𝓓 ⟩ z  )
 ≪-binary-interpolation-basis {x} {y} {z} x-wb-z y-wb-z =
  ∥∥-rec ∃-is-prop γ (≪-binary-interpolation-str 𝓓 C x-wb-z y-wb-z)
   where
    C : structurally-continuous 𝓓
    C = structurally-continuous-if-specified-small-basis 𝓓 (B , β , sb)
    open structurally-continuous C
    γ : (Σ d ꞉ ⟨ 𝓓 ⟩ , x ≪⟨ 𝓓 ⟩ d × y ≪⟨ 𝓓 ⟩ d × d ≪⟨ 𝓓 ⟩ z)
      → ∃ b ꞉ B , x ≪⟨ 𝓓 ⟩ β b × y ≪⟨ 𝓓 ⟩ β b × β b ≪⟨ 𝓓 ⟩ z
    γ (d , x-wb-d , y-wb-d , d-wb-z) =
     ∥∥-functor σ (d-wb-z (↡ᴮₛ z) (↡-inclusionₛ z)
                          (↡ᴮₛ-is-directed z) (↡ᴮₛ-∐-⊒ z))
      where
       σ : (Σ b ꞉ ↡ᴮₛ z , d ⊑⟨ 𝓓 ⟩ ↡-inclusionₛ z b)
         → Σ b ꞉ B , x ≪⟨ 𝓓 ⟩ β b × y ≪⟨ 𝓓 ⟩ β b × β b ≪⟨ 𝓓 ⟩ z
       σ ((b , b-wb-z) , d-below-b) = b , ≪-⊑-to-≪ 𝓓 x-wb-d d-below-b
                                        , ≪-⊑-to-≪ 𝓓 y-wb-d d-below-b
                                        , ≪ᴮₛ-to-≪ᴮ b-wb-z


\end{code}

Now that we have established the basics of small bases, we introduce and study
small compact basis. The idea of a small compact basis is that we have a
small-indexed family β : B → D into a dcpo such that for β b is compact for
every b : B, and for every x : D, the collection of b : B such that β b ⊑ x is
small, directed and has supremum x. Thus, if we wish to approximate an element
of D, we can do so using compact elements from B.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇ }
        (β : B → ⟨ 𝓓 ⟩)
       where

 ↓ᴮ : ⟨ 𝓓 ⟩ → 𝓥 ⊔ 𝓣 ̇
 ↓ᴮ x = Σ b ꞉ B , β b ⊑⟨ 𝓓 ⟩ x

 ↓-inclusion : (x : ⟨ 𝓓 ⟩) → ↓ᴮ x → ⟨ 𝓓 ⟩
 ↓-inclusion x = β ∘ pr₁

 record is-small-compact-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
  field
   basis-is-compact : (b : B) → is-compact 𝓓 (β b)
   ⊑ᴮ-is-small : (x : ⟨ 𝓓 ⟩) (b : B) → is-small (β b ⊑⟨ 𝓓 ⟩ x)
   ↓ᴮ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↓-inclusion x)
   ↓ᴮ-is-sup : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x (↓-inclusion x)

  _⊑ᴮₛ_ : (b : B) (x : ⟨ 𝓓 ⟩) → 𝓥 ̇
  b ⊑ᴮₛ x = pr₁ (⊑ᴮ-is-small x b)

  ⊑ᴮₛ-≃-⊑ᴮ : {b : B} {x : ⟨ 𝓓 ⟩} → (b ⊑ᴮₛ x) ≃ (β b ⊑⟨ 𝓓 ⟩ x)
  ⊑ᴮₛ-≃-⊑ᴮ {b} {x} = pr₂ (⊑ᴮ-is-small x b)

  ⊑ᴮₛ-to-⊑ᴮ : {b : B} {x : ⟨ 𝓓 ⟩} → (b ⊑ᴮₛ x) → (β b ⊑⟨ 𝓓 ⟩ x)
  ⊑ᴮₛ-to-⊑ᴮ {b} {x} = ⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝

  ⊑ᴮ-to-⊑ᴮₛ : {b : B} {x : ⟨ 𝓓 ⟩} → (β b ⊑⟨ 𝓓 ⟩ x) → (b ⊑ᴮₛ x)
  ⊑ᴮ-to-⊑ᴮₛ {b} {x} = ⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝⁻¹

  ↓ᴮₛ : ⟨ 𝓓 ⟩ → 𝓥 ̇
  ↓ᴮₛ x = Σ b ꞉ B , (b ⊑ᴮₛ x)

  ↓-inclusionₛ : (x : ⟨ 𝓓 ⟩) → ↓ᴮₛ x → ⟨ 𝓓 ⟩
  ↓-inclusionₛ x = β ∘ pr₁

  ↓ᴮₛ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↓-inclusionₛ x)
  ↓ᴮₛ-is-directed x = reindexed-family-is-directed 𝓓
                       (Σ-cong (λ b → ≃-sym ⊑ᴮₛ-≃-⊑ᴮ))
                       (↓-inclusion x) (↓ᴮ-is-directed x)

  ↓ᴮₛ-∐-＝ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (↓ᴮₛ-is-directed x) ＝ x
  ↓ᴮₛ-∐-＝ x = antisymmetry 𝓓 (∐ 𝓓 (↓ᴮₛ-is-directed x)) x ⦅1⦆ ⦅2⦆
   where
    ⦅1⦆ : ∐ 𝓓 (↓ᴮₛ-is-directed x) ⊑⟨ 𝓓 ⟩ x
    ⦅1⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 (↓ᴮₛ-is-directed x) x
          (λ (b , u) → sup-is-upperbound (underlying-order 𝓓) (↓ᴮ-is-sup x)
                        (b , ⊑ᴮₛ-to-⊑ᴮ u))
    ⦅2⦆ : x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↓ᴮₛ-is-directed x)
    ⦅2⦆ = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓) (↓ᴮ-is-sup x)
          (∐ 𝓓 (↓ᴮₛ-is-directed x))
          (λ (b , v) → ∐-is-upperbound 𝓓 (↓ᴮₛ-is-directed x)
                        (b , ⊑ᴮ-to-⊑ᴮₛ v))

  ↓ᴮₛ-∐-⊑ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (↓ᴮₛ-is-directed x) ⊑⟨ 𝓓 ⟩ x
  ↓ᴮₛ-∐-⊑ x = ＝-to-⊑ 𝓓 (↓ᴮₛ-∐-＝ x)

  ↓ᴮₛ-∐-⊒ : (x : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↓ᴮₛ-is-directed x)
  ↓ᴮₛ-∐-⊒ x = ＝-to-⊒ 𝓓 (↓ᴮₛ-∐-＝ x)

  ↓ᴮₛ-compact : (x : ⟨ 𝓓 ⟩) (b : ↓ᴮₛ x) → is-compact 𝓓 (↓-inclusionₛ x b)
  ↓ᴮₛ-compact x (b , u) = basis-is-compact b

\end{code}

Of course, every small compact basis is a small basis, and alternatively, we
could have defined a small compact basis as a small basis such that every basis
element is compact.

\begin{code}

 compact-basis-is-basis : is-small-compact-basis
                        → is-small-basis 𝓓 β
 compact-basis-is-basis scb =
  record
   { ≪ᴮ-is-small    = λ x b → ( b ⊑ᴮₛ x
                            , ((b ⊑ᴮₛ x)      ≃⟨ ⊑ᴮₛ-≃-⊑ᴮ ⟩
                               (β b ⊑⟨ 𝓓 ⟩ x) ≃⟨ lemma b  ⟩
                               (β b ≪⟨ 𝓓 ⟩ x) ■))
   ; ↡ᴮ-is-directed = λ x → reindexed-family-is-directed 𝓓
                             (↓ᴮ-≃-↡ᴮ x) (↓-inclusion x) (↓ᴮ-is-directed x)
   ; ↡ᴮ-is-sup      = λ x → reindexed-family-sup 𝓓 (↓ᴮ-≃-↡ᴮ x) (↓-inclusion x)
                             x (↓ᴮ-is-sup x)
   }
   where
    open is-small-compact-basis scb
    lemma : (b : B) {x : ⟨ 𝓓 ⟩} → (β b ⊑⟨ 𝓓 ⟩ x) ≃ (β b ≪⟨ 𝓓 ⟩ x)
    lemma b = compact-⊑-≃-≪ 𝓓 (basis-is-compact b)
    ↓ᴮ-≃-↡ᴮ : (x : ⟨ 𝓓 ⟩) → ↓ᴮ x ≃ ↡ᴮ 𝓓 β x
    ↓ᴮ-≃-↡ᴮ x = Σ-cong (λ b → lemma b)

 locally-small-if-small-compact-basis : is-small-compact-basis
                                      → is-locally-small 𝓓
 locally-small-if-small-compact-basis scb =
  locally-small-if-small-basis 𝓓 β (compact-basis-is-basis scb)

 small-and-compact-basis : is-small-basis 𝓓 β
                         → ((b : B) → is-compact 𝓓 (β b))
                         → is-small-compact-basis
 small-and-compact-basis β-is-small-basis κ =
  record
   { basis-is-compact = κ
   ; ⊑ᴮ-is-small      = λ x b → ( b ≪ᴮₛ x
                              , ((b ≪ᴮₛ x)    ≃⟨ ≪ᴮₛ-≃-≪ᴮ ⟩
                                 β b ≪⟨ 𝓓 ⟩ x ≃⟨ lemma b ⟩
                                 β b ⊑⟨ 𝓓 ⟩ x ■))
   ; ↓ᴮ-is-directed   = λ x → reindexed-family-is-directed 𝓓
                               (↡ᴮ-≃-↓ᴮ x) (↡-inclusion 𝓓 β x) (↡ᴮ-is-directed x)
   ; ↓ᴮ-is-sup        = λ x → reindexed-family-sup 𝓓
                               (↡ᴮ-≃-↓ᴮ x) (↡-inclusion 𝓓 β x) x (↡ᴮ-is-sup x)
   }
   where
    open is-small-basis β-is-small-basis
    lemma : (b : B) {x : ⟨ 𝓓 ⟩} → (β b ≪⟨ 𝓓 ⟩ x) ≃ (β b ⊑⟨ 𝓓 ⟩ x)
    lemma b = ≃-sym (compact-⊑-≃-≪ 𝓓 (κ b))
    ↡ᴮ-≃-↓ᴮ : (x : ⟨ 𝓓 ⟩) → ↡ᴮ 𝓓 β x ≃ ↓ᴮ x
    ↡ᴮ-≃-↓ᴮ x = Σ-cong (λ b → lemma b)

\end{code}

In fact, a small compact basis must contain every compact element.

\begin{code}

 small-compact-basis-contains-all-compact-elements : is-small-compact-basis
                                                   → (x : ⟨ 𝓓 ⟩)
                                                   → is-compact 𝓓 x
                                                   → ∃ b ꞉ B , β b ＝ x
 small-compact-basis-contains-all-compact-elements scb x x-is-compact =
  ∥∥-functor γ (x-is-compact (↓ᴮₛ x) (↓-inclusionₛ x)
                             (↓ᴮₛ-is-directed x) (↓ᴮₛ-∐-⊒ x))
   where
    open is-small-compact-basis scb
    γ : (Σ (b , b-below-x) ꞉ ↓ᴮₛ x , x ⊑⟨ 𝓓 ⟩ β b)
      → (Σ b ꞉ B , β b ＝ x)
    γ ((b , b-below-x) , x-below-b) = (b , e)
     where
      e : β b ＝ x
      e = antisymmetry 𝓓 (β b) x (⊑ᴮₛ-to-⊑ᴮ b-below-x) x-below-b

\end{code}

As one may expect, a dcpo that comes equipped with a small compact basis is
structurally algebraic and this in turn implies that a dcpo with some
unspecified small compact basis must be algebraic.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 has-specified-small-compact-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-specified-small-compact-basis =
  Σ B ꞉ 𝓥 ̇ , Σ β ꞉ (B → ⟨ 𝓓 ⟩) , is-small-compact-basis 𝓓 β

 has-unspecified-small-compact-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-unspecified-small-compact-basis = ∥ has-specified-small-compact-basis ∥

 structurally-algebraic-if-specified-small-compact-basis :
    has-specified-small-compact-basis
  → structurally-algebraic 𝓓
 structurally-algebraic-if-specified-small-compact-basis (B , β , scb) =
  record
   { index-of-compact-family    = ↓ᴮₛ
   ; compact-family             = ↓-inclusionₛ
   ; compact-family-is-directed = ↓ᴮₛ-is-directed
   ; compact-family-is-compact  = ↓ᴮₛ-compact
   ; compact-family-∐-＝         = ↓ᴮₛ-∐-＝
   }
   where
    open is-small-compact-basis scb

 is-algebraic-dcpo-if-unspecified-small-compact-basis :
    has-unspecified-small-compact-basis
  → is-algebraic-dcpo 𝓓
 is-algebraic-dcpo-if-unspecified-small-compact-basis =
  ∥∥-functor structurally-algebraic-if-specified-small-compact-basis

\end{code}

TODO

\end{code}

The following technical lemmas give us criteria for directedness and calculating
suprema of the collection Σ b : B , β b ≪⟨ 𝓓 ⟩ x.

Essentially they say that it is sufficient for a subset of ↡ᴮ x to be directed
and have suprema x. So the results are type-theoretic versions of Proposition
2.2.4 of "Domain Theory" by Abramsky and Jung, and Proposition III-4.2 of
"Continuous lattices and domains" by Gierz et al.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇ }
        (β : B → ⟨ 𝓓 ⟩)
        (x : ⟨ 𝓓 ⟩)
        {I : 𝓥 ̇ }
        (σ : I → ↡ᴮ 𝓓 β x)
       where

 ↡ᴮ-sup-criterion : is-sup (underlying-order 𝓓) x (↡-inclusion 𝓓 β x ∘ σ)
                  → is-sup (underlying-order 𝓓) x (↡-inclusion 𝓓 β x)
 ↡ᴮ-sup-criterion x-is-sup = (ub , lb-of-ubs)
  where
   ub : is-upperbound (underlying-order 𝓓) x (↡-inclusion 𝓓 β x)
   ub (b , b-way-below-x) = ≪-to-⊑ 𝓓 b-way-below-x
   lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order 𝓓)
                                            x (↡-inclusion 𝓓 β x)
   lb-of-ubs y y-is-ub =
    sup-is-lowerbound-of-upperbounds (underlying-order 𝓓) x-is-sup y y-is-ub'
     where
      y-is-ub' : is-upperbound (underlying-order 𝓓) y (↡-inclusion 𝓓 β x ∘ σ)
      y-is-ub' i = y-is-ub (σ i)

 ↡ᴮ-directedness-criterion : (δ : is-Directed 𝓓 (↡-inclusion 𝓓 β x ∘ σ))
                           → (x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ)
                           → is-Directed 𝓓 (↡-inclusion 𝓓 β x)
 ↡ᴮ-directedness-criterion δ@(inh , semidir) x-below-∐ = (inh' , semidir')
  where
   inh' : ∥ ↡ᴮ 𝓓 β x ∥
   inh' = ∥∥-functor σ inh
   semidir' : is-semidirected (underlying-order 𝓓) (↡-inclusion 𝓓 β x)
   semidir' (b₁ , b₁-way-below-x) (b₂ , b₂-way-below-x) =
    ∥∥-rec₂ ∃-is-prop f (b₁-way-below-x I (↡-inclusion 𝓓 β x ∘ σ) δ x-below-∐)
                        (b₂-way-below-x I (↡-inclusion 𝓓 β x ∘ σ) δ x-below-∐)
     where
      f : (Σ i ꞉ I , β b₁ ⊑⟨ 𝓓 ⟩ ↡-inclusion 𝓓 β x (σ i))
        → (Σ i ꞉ I , β b₂ ⊑⟨ 𝓓 ⟩ ↡-inclusion 𝓓 β x (σ i))
        → (∃ b ꞉ ↡ᴮ 𝓓 β x , (β b₁ ⊑⟨ 𝓓 ⟩ ↡-inclusion 𝓓 β x b)
                          × (β b₂ ⊑⟨ 𝓓 ⟩ ↡-inclusion 𝓓 β x b))
      f (i₁ , u₁) (i₂ , u₂) = ∥∥-functor g (semidir i₁ i₂)
       where
        g : (Σ i ꞉ I , (↡-inclusion 𝓓 β x (σ i₁) ⊑⟨ 𝓓 ⟩ ↡-inclusion 𝓓 β x (σ i))
                     × (↡-inclusion 𝓓 β x (σ i₂) ⊑⟨ 𝓓 ⟩ ↡-inclusion 𝓓 β x (σ i)))
          → (Σ b ꞉ ↡ᴮ 𝓓 β x , (β b₁ ⊑⟨ 𝓓 ⟩ ↡-inclusion 𝓓 β x b)
                            × (β b₂ ⊑⟨ 𝓓 ⟩ ↡-inclusion 𝓓 β x b))
        g (i , v₁ , v₂) = (σ i
                        , (β b₁                     ⊑⟨ 𝓓 ⟩[ u₁ ]
                           ↡-inclusion 𝓓 β x (σ i₁) ⊑⟨ 𝓓 ⟩[ v₁ ]
                           ↡-inclusion 𝓓 β x (σ i)  ∎⟨ 𝓓 ⟩)
                        , (β b₂                     ⊑⟨ 𝓓 ⟩[ u₂ ]
                           ↡-inclusion 𝓓 β x (σ i₂) ⊑⟨ 𝓓 ⟩[ v₂ ]
                           ↡-inclusion 𝓓 β x (σ i)  ∎⟨ 𝓓 ⟩))

\end{code}

The above criteria comes in useful when proving that if we have a continuous
retraction r : 𝓔 → 𝓓 and a small basis β : B → 𝓔 for 𝓔, then r ∘ β is a small
basis for 𝓓.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'})
        (ρ : 𝓓 continuous-retract-of 𝓔)
       where

 open _continuous-retract-of_ ρ

 small-basis-from-continuous-retract : Prop-Ext → {B : 𝓥 ̇ } (β : B → ⟨ 𝓔 ⟩)
                                     → is-small-basis 𝓔 β
                                     → is-small-basis 𝓓 (r ∘ β)
 small-basis-from-continuous-retract pe {B} β sb =
  record
   { ≪ᴮ-is-small    = ≪ʳᴮ-is-small
   ; ↡ᴮ-is-directed = ≪ʳᴮ-is-directed
   ; ↡ᴮ-is-sup      = ↡ʳᴮ-is-sup
   }
   where
    open is-small-basis sb

    ≪ʳᴮ-is-small : (x : ⟨ 𝓓 ⟩) (b : B) → is-small (r (β b) ≪⟨ 𝓓 ⟩ x)
    ≪ʳᴮ-is-small x b = ≪-is-small-valued pe 𝓓 𝓓-cont 𝓓-loc-small (r (β b)) x
     where
      𝓓-loc-small : is-locally-small 𝓓
      𝓓-loc-small = (local-smallness-preserved-by-continuous-retract
                      𝓓 𝓔 ρ (locally-small-if-small-basis 𝓔 β sb))
      𝓓-cont : is-continuous-dcpo 𝓓
      𝓓-cont = continuity-of-dcpo-preserved-by-continuous-retract 𝓓 𝓔 ρ
                ∣ structurally-continuous-if-specified-small-basis
                   𝓔 (B , (β , sb)) ∣

    σ : (x : ⟨ 𝓓 ⟩) → ↡ᴮₛ (s x) → ↡ᴮ 𝓓 (r ∘ β) x
    σ x (b , b-way-below-sx) =
     (b , continuous-retraction-≪-criterion 𝓓 𝓔 ρ (β b) x
           (≪ᴮₛ-to-≪ᴮ b-way-below-sx))

    ε : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓔 (↡-inclusionₛ (s x))
    ε x = ↡ᴮₛ-is-directed (s x)

    ∐-section-of-r : (x : ⟨ 𝓓 ⟩) → r (∐ 𝓔 (ε x)) ＝ x
    ∐-section-of-r x = r (∐ 𝓔 (ε x)) ＝⟨ ap r (↡ᴮₛ-∐-＝ (s x)) ⟩
                       r (s x)       ＝⟨ s-section-of-r x     ⟩
                       x             ∎

    ≪ʳᴮ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↡-inclusion 𝓓 (r ∘ β) x)
    ≪ʳᴮ-is-directed x = ↡ᴮ-directedness-criterion 𝓓 (r ∘ β) x (σ x) ε' h
     where
      ε' : is-Directed 𝓓 (r ∘ ↡-inclusionₛ (s x))
      ε' = image-is-directed' 𝓔 𝓓 𝕣 (ε x)
      h : x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε'
      h = transport (λ - → - ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε') (∐-section-of-r x) l
       where
        l : r (∐ 𝓔 (ε x)) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε'
        l = continuous-∐-⊑ 𝓔 𝓓 𝕣 (ε x)

    ↡ʳᴮ-is-sup : (x : ⟨ 𝓓 ⟩)
               → is-sup (underlying-order 𝓓) x (↡-inclusion 𝓓 (r ∘ β) x)
    ↡ʳᴮ-is-sup x = ↡ᴮ-sup-criterion 𝓓 (r ∘ β) x (σ x) h
     where
      h : is-sup (underlying-order 𝓓) x (r ∘ ↡-inclusionₛ (s x))
      h = transport
           (λ - → is-sup (underlying-order 𝓓) - (r ∘ ↡-inclusionₛ (s x)))
           (∐-section-of-r x) issup
       where
        issup : is-sup (underlying-order 𝓓) (r (∐ 𝓔 (ε x)))
                                            (r ∘ ↡-inclusionₛ (s x))
        issup = r-is-continuous (↡ᴮₛ (s x)) (↡-inclusionₛ (s x)) (ε x)

\end{code}

Finally, a nice use of dcpos with small bases is that they yield locally small
exponentials. More precisely, if 𝓔 is locally small and 𝓓 has an unspecified
small basis, then the exponential 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 is locally small, because when
ordering the exponential we can quantify just over the basis elements, rather
than over all elements of 𝓓.

\begin{code}

open import DomainTheory.Basics.Exponential pt fe 𝓥

locally-small-exponential-criterion : Prop-Ext
                                    → (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                                    → has-unspecified-small-basis 𝓓
                                    → is-locally-small 𝓔
                                    → is-locally-small (𝓓 ⟹ᵈᶜᵖᵒ 𝓔)
locally-small-exponential-criterion {𝓤} {𝓣} {𝓤'} {𝓣'} pe 𝓓 𝓔 𝓓-sb ls =
 ∥∥-rec (being-locally-small-is-prop (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) (λ _ → pe)) lemma 𝓓-sb
  where
   open is-locally-small ls
   lemma : has-specified-small-basis 𝓓 → is-locally-small (𝓓 ⟹ᵈᶜᵖᵒ 𝓔)
   lemma (B , β , β-is-small-basis) =
    ⌜ local-smallness-equivalent-definitions (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ⌝⁻¹ γ
     where
      open is-small-basis β-is-small-basis
      γ : is-locally-small' (𝓓 ⟹ᵈᶜᵖᵒ 𝓔)
      γ 𝕗@(f , f-cont) 𝕘@(g , g-cont) = (order-using-basis , order-lemma)
       where
        order-using-basis : 𝓥 ̇
        order-using-basis = (b : B) → f (β b) ⊑ₛ g (β b)
        ptwise-order : 𝓤 ⊔ 𝓣' ̇
        ptwise-order = ((x : ⟨ 𝓓 ⟩) → f x ⊑⟨ 𝓔 ⟩ g x)

        order-lemma : order-using-basis ≃ ptwise-order
        order-lemma =
         logically-equivalent-props-are-equivalent
          (Π-is-prop fe (λ b → equiv-to-prop ⊑ₛ-≃-⊑
                                (prop-valuedness 𝓔 (f (β b)) (g (β b)))))
          (Π-is-prop fe (λ x → prop-valuedness 𝓔 (f x) (g x)))
          ⦅⇒⦆ ⦅⇐⦆
          where
           ⦅⇐⦆ : ptwise-order → order-using-basis
           ⦅⇐⦆ f-below-g b = ⊑-to-⊑ₛ (f-below-g (β b))
           ⦅⇒⦆ : order-using-basis → ptwise-order
           ⦅⇒⦆ f-below-g x = transport (λ - → f - ⊑⟨ 𝓔 ⟩ g -)
                              (↡ᴮₛ-∐-＝ x) f-below-g'
            where
             f-below-g' = f (∐ 𝓓 (↡ᴮₛ-is-directed x)) ⊑⟨ 𝓔 ⟩[ ⦅1⦆ ]
                          ∐ 𝓔 εᶠ                      ⊑⟨ 𝓔 ⟩[ ⦅2⦆ ]
                          ∐ 𝓔 εᵍ                      ⊑⟨ 𝓔 ⟩[ ⦅3⦆ ]
                          g (∐ 𝓓 (↡ᴮₛ-is-directed x)) ∎⟨ 𝓔 ⟩
              where
               εᶠ : is-Directed 𝓔 (f ∘ ↡-inclusionₛ x)
               εᶠ = image-is-directed' 𝓓 𝓔 𝕗 (↡ᴮₛ-is-directed x)
               εᵍ : is-Directed 𝓔 (g ∘ ↡-inclusionₛ x)
               εᵍ = image-is-directed' 𝓓 𝓔 𝕘 (↡ᴮₛ-is-directed x)
               ⦅1⦆ = continuous-∐-⊑ 𝓓 𝓔 𝕗 (↡ᴮₛ-is-directed x)
               ⦅3⦆ = continuous-∐-⊒ 𝓓 𝓔 𝕘 (↡ᴮₛ-is-directed x)
               ⦅2⦆ = ∐-is-lowerbound-of-upperbounds 𝓔 εᶠ (∐ 𝓔 εᵍ) ub
                where
                 ub : (i : ↡ᴮₛ x) → f (↡-inclusionₛ x i) ⊑⟨ 𝓔 ⟩ ∐ 𝓔 εᵍ
                 ub (b , i) = f (β b) ⊑⟨ 𝓔 ⟩[ ⦅†⦆ ]
                              g (β b) ⊑⟨ 𝓔 ⟩[ ⦅‡⦆ ]
                              ∐ 𝓔 εᵍ  ∎⟨ 𝓔 ⟩
                  where
                   ⦅†⦆ = ⊑ₛ-to-⊑ (f-below-g b)
                   ⦅‡⦆ = ∐-is-upperbound 𝓔 εᵍ (b , i)

\end{code}

TODO.
Actually, we can improve the above results: a dcpo 𝓓 is already structurally
algebraic if it has an unspecified small compact basis.

The proof is roughly that the type of all compact elements is essentially small
if we have an unspecified small compact basis. However, this does require
univalence and set replacement. (The latter is equivalent to having small set
quotients, see Quotient.index.)

This result is due to Ayberk Tosun (19 September 2023) and was formalised here
on 4 October 2023 by Tom de Jong.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (uscb : has-unspecified-small-compact-basis 𝓓)
       where

 private
  K : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  K = Σ x ꞉ ⟨ 𝓓 ⟩ , is-compact 𝓓 x

  ι : K → ⟨ 𝓓 ⟩
  ι = pr₁

  ↓ᴷ : ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  ↓ᴷ x = Σ k ꞉ K , ι k ⊑⟨ 𝓓 ⟩ x

  ↓ᴷ-inclusion : (x : ⟨ 𝓓 ⟩) → ↓ᴷ x → ⟨ 𝓓 ⟩
  ↓ᴷ-inclusion x = ι ∘ pr₁

  ↓ᴷ-is-inhabited : (x : ⟨ 𝓓 ⟩) → ∥ ↓ᴷ x ∥
  ↓ᴷ-is-inhabited x = ∥∥-rec ∥∥-is-prop γ uscb
   where
    γ : has-specified-small-compact-basis 𝓓
      → ∥ ↓ᴷ x ∥
    γ (B , β , scb) = ∥∥-functor (λ (b , l) → (β b , basis-is-compact b) , l) inh
     where
      open is-small-compact-basis scb
      inh : ∥ ↓ᴮ 𝓓 β x ∥
      inh = inhabited-if-Directed 𝓓 (↓-inclusion 𝓓 β x) (↓ᴮ-is-directed x)

  ↓ᴷ-is-semidirected : (x : ⟨ 𝓓 ⟩) → is-Semidirected 𝓓 (↓ᴷ-inclusion x)
  ↓ᴷ-is-semidirected x =
   ∥∥-rec (being-semidirected-is-prop (underlying-order 𝓓) (↓ᴷ-inclusion x))
          γ uscb
    where
     γ : has-specified-small-compact-basis 𝓓
       → is-Semidirected 𝓓 (↓ᴷ-inclusion x)
     γ (B , β , scb) ((c₁ , c₁-compact) , c₁-below-x)
                     ((c₂ , c₂-compact) , c₂-below-x) =
      ∥∥-rec₂ ∃-is-prop sd ⦅1⦆ ⦅2⦆
       where
        open is-small-compact-basis scb
        sd : (Σ b₁ ꞉ B , β b₁ ＝ c₁)
           → (Σ b₂ ꞉ B , β b₂ ＝ c₂)
           → ∃ c ꞉ ↓ᴷ x , (c₁ ⊑⟨ 𝓓 ⟩ ↓ᴷ-inclusion x c)
                        × (c₂ ⊑⟨ 𝓓 ⟩ ↓ᴷ-inclusion x c)
        sd (b₁ , refl) (b₂ , refl) = ∥∥-functor β' semidir
         where
          β' : (Σ b ꞉ ↓ᴮ 𝓓 β x , (β b₁ ⊑⟨ 𝓓 ⟩ ↓-inclusion 𝓓 β x b)
                               × (β b₂ ⊑⟨ 𝓓 ⟩ ↓-inclusion 𝓓 β x b))
             → (Σ k ꞉ ↓ᴷ x , (β b₁ ⊑⟨ 𝓓 ⟩ ↓ᴷ-inclusion x k)
                           × (β b₂ ⊑⟨ 𝓓 ⟩ ↓ᴷ-inclusion x k))
          β' ((b , b-below-x) , l₁ , l₂) = ((β b , basis-is-compact b)
                                           , b-below-x) , l₁ , l₂
          semidir : ∃ b ꞉ ↓ᴮ 𝓓 β x , (β b₁ ⊑⟨ 𝓓 ⟩ ↓-inclusion 𝓓 β x b)
                                   × (β b₂ ⊑⟨ 𝓓 ⟩ ↓-inclusion 𝓓 β x b)
          semidir = semidirected-if-Directed 𝓓
                     (↓-inclusion 𝓓 β x) (↓ᴮ-is-directed x)
                     (b₁ , c₁-below-x) (b₂ , c₂-below-x)
        ⦅1⦆ : ∃ b₁ ꞉ B , β b₁ ＝ c₁
        ⦅1⦆ = small-compact-basis-contains-all-compact-elements
               𝓓 β scb c₁ c₁-compact
        ⦅2⦆ : ∃ b₂ ꞉ B , β b₂ ＝ c₂
        ⦅2⦆ = small-compact-basis-contains-all-compact-elements
               𝓓 β scb c₂ c₂-compact

  ↓ᴷ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↓ᴷ-inclusion x)
  ↓ᴷ-is-directed x = ↓ᴷ-is-inhabited x , ↓ᴷ-is-semidirected x



{-
 open import UF.KrausLemma
 open split-support-and-collapsibility pt
 open import UF.ImageAndSurjection pt
 open import UF.Univalence
 open import UF.Sets
 open import UF.Sets-Properties
 open import UF.Size

 module _
         (ua : Univalence)
         (sr : Set-Replacement pt)
  where

  has-specified-small-compact-basis-has-split-support :
   has-split-support (has-specified-small-compact-basis 𝓓)
  has-specified-small-compact-basis-has-split-support uscb = Kₛ , ιₛ , (record
                                                                              { basis-is-compact = {!!}
                                                                              ; ⊑ᴮ-is-small = {!!}
                                                                              ; ↓ᴮ-is-directed = {!!}
                                                                              ; ↓ᴮ-is-sup = {!!}
                                                                              })
   where
    K : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
    K = Σ x ꞉ ⟨ 𝓓 ⟩ , is-compact 𝓓 x

    ι : K → ⟨ 𝓓 ⟩
    ι = pr₁

    K-is-small : K is 𝓥 small
    K-is-small = ∥∥-rec (being-small-is-prop ua K 𝓥) γ uscb
     where
      γ : has-specified-small-compact-basis 𝓓
        → K is 𝓥 small
      γ (B , β , scb) = ≃-size-contravariance K-is-image image-is-small
       where
        open is-small-compact-basis scb
        open is-locally-small (locally-small-if-small-compact-basis 𝓓 β scb)
        β' : B → K
        β' b = β b , basis-is-compact b
        β'-is-surjection : is-surjection β'
        β'-is-surjection (x , x-compact) =
         ∥∥-functor
          (λ {(b , refl) → b , to-subtype-＝ (being-compact-is-prop 𝓓) refl})
          (small-compact-basis-contains-all-compact-elements
           𝓓 β scb x x-compact)
        K-is-image : K ≃ image β'
        K-is-image = ≃-sym (surjection-≃-image β' β'-is-surjection)
        K-is-set : is-set K
        K-is-set = subtypes-of-sets-are-sets' ι
                    (pr₁-lc (λ {x} → being-compact-is-prop 𝓓 x)) (sethood 𝓓)
        K-is-locally-small : K is-locally 𝓥 small
        K-is-locally-small (x , x-compact) (y , y-compact) =
           ((x ⊑ₛ y) × (y ⊑ₛ x))
         , logically-equivalent-props-are-equivalent
            (×-is-prop (⊑ₛ-is-prop-valued x y) (⊑ₛ-is-prop-valued y x))
            K-is-set
            (λ (l , k) → to-subtype-＝ (being-compact-is-prop 𝓓)
                                       (antisymmetry 𝓓 x y (⊑ₛ-to-⊑ l)
                                                           (⊑ₛ-to-⊑ k)))
            λ {refl → reflexivityₛ x , reflexivityₛ x}
        image-is-small : image β' is 𝓥 small
        image-is-small = sr β' (B , ≃-refl B) K-is-locally-small K-is-set

    Kₛ : 𝓥 ̇
    Kₛ = resized K K-is-small
    ιₛ : Kₛ → ⟨ 𝓓 ⟩
    ιₛ = ι ∘ ⌜ resizing-condition K-is-small ⌝

-}


{-
  structurally-algebraic-if-unspecified-small-compact-basis :
     has-unspecified-small-compact-basis 𝓓
   → structurally-algebraic 𝓓
  structurally-algebraic-if-unspecified-small-compact-basis uscb =
   record
    { index-of-compact-family = Cₛ
    ; compact-family = ιₛ
    ; compact-family-is-directed = ιₛ-is-directed
    ; compact-family-is-compact = ιₛ-is-compact
    ; compact-family-∐-＝ = ιₛ-∐-＝
    }
    where
     C : (x : ⟨ 𝓓 ⟩) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
     C x = Σ y ꞉ ⟨ 𝓓 ⟩ , is-compact 𝓓 y × (y ⊑⟨ 𝓓 ⟩ x)
     ι : (x : ⟨ 𝓓 ⟩) → C x → ⟨ 𝓓 ⟩
     ι x = pr₁
     ι-is-compact : (x : ⟨ 𝓓 ⟩) (c : C x) → is-compact 𝓓 (ι x c)
     ι-is-compact _ c = pr₁ (pr₂ c)
     ι-is-upperbound : (x : ⟨ 𝓓 ⟩) (c : C x) → ι x c ⊑⟨ 𝓓 ⟩ x
     ι-is-upperbound _ c = pr₂ (pr₂ c)
     ι-is-sup : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x (ι x)
     ι-is-sup x = ∥∥-rec (is-sup-is-prop (underlying-order 𝓓)
                                         (pr₁ (axioms-of-dcpo 𝓓))
                                         x (ι x))
                         γ
                         uscb
      where
       γ : has-specified-small-compact-basis 𝓓
         → is-sup (underlying-order 𝓓) x (ι x)
       γ (B , β , scb) = ι-is-upperbound x , lb-of-ubs
        where
         open is-small-compact-basis scb
         lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order 𝓓) x (ι x)
         lb-of-ubs y y-is-ub =
          transport (λ - → - ⊑⟨ 𝓓 ⟩ y)
                    (↓ᴮₛ-∐-＝ x)
                    (∐-is-lowerbound-of-upperbounds 𝓓
                     (↓ᴮₛ-is-directed x) y lb-of-ubs')
           where
            lb-of-ubs' : (b : ↓ᴮₛ x) → ↓-inclusionₛ x b ⊑⟨ 𝓓 ⟩ y
            lb-of-ubs' (b , l) = y-is-ub (β b , basis-is-compact b , ⊑ᴮₛ-to-⊑ᴮ l)

     ι-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (ι x)
     ι-is-directed x =
      ∥∥-rec (being-directed-is-prop (underlying-order 𝓓) (ι x)) γ uscb
       where
        γ : has-specified-small-compact-basis 𝓓
          → is-directed (underlying-order 𝓓) (ι x)
        γ (B , β , scb) = inh , semidir
         where
          open is-small-compact-basis scb
          inh' : ∥ ↓ᴮ 𝓓 β x ∥
          inh' = inhabited-if-Directed 𝓓 (↓-inclusion 𝓓 β x) (↓ᴮ-is-directed x)
          inh : ∥ C x ∥
          inh = ∥∥-functor (λ (b , l) → (β b) , basis-is-compact b , l) inh'

          semidir' : is-Semidirected 𝓓 (↓-inclusion 𝓓 β x)
          semidir' = semidirected-if-Directed 𝓓
                      (↓-inclusion 𝓓 β x) (↓ᴮ-is-directed x)
          semidir : is-semidirected (underlying-order 𝓓) (ι x)
          semidir (c₁ , c₁-compact , c₁-below-x)
                  (c₂ , c₂-compact , c₂-below-x) =
           ∥∥-rec₂ ∃-is-prop sd
                   (small-compact-basis-contains-all-compact-elements
                     𝓓 β scb c₁ c₁-compact)
                   (small-compact-basis-contains-all-compact-elements
                     𝓓 β scb c₂ c₂-compact)
             where
              sd : (Σ b₁ ꞉ B , β b₁ ＝ c₁)
                 → (Σ b₂ ꞉ B , β b₂ ＝ c₂)
                 → ∃ c ꞉ C x , (c₁ ⊑⟨ 𝓓 ⟩ ι x c) × (c₂ ⊑⟨ 𝓓 ⟩ ι x c)
              sd (b₁ , refl) (b₂ , refl) =
               ∥∥-functor
                (λ ((b , l) , (l₁ , l₂)) → (β b , basis-is-compact b , l)
                                                , l₁ , l₂)
                (semidir' (b₁ , c₁-below-x) (b₂ , c₂-below-x))

     C-is-small : (x : ⟨ 𝓓 ⟩) → (C x) is 𝓥 small
     C-is-small x = ∥∥-rec (being-small-is-prop ua (C x) 𝓥) γ uscb
      where
       γ : has-specified-small-compact-basis 𝓓
         → C x is 𝓥 small
       γ (B , β , scb) = ≃-size-contravariance C-is-image image-is-small
        where
         open import UF.ImageAndSurjection pt
         open import UF.Sets
         open import UF.Sets-Properties

         open is-small-compact-basis scb
         open is-locally-small (locally-small-if-small-compact-basis 𝓓 β scb)

         C-is-subtype : (y : ⟨ 𝓓 ⟩)
                      → is-prop (is-compact 𝓓 y × (y ⊑⟨ 𝓓 ⟩ x))
         C-is-subtype y = ×-is-prop (being-compact-is-prop 𝓓 y)
                                    (prop-valuedness 𝓓 y x)

         C-is-set : is-set (C x)
         C-is-set =
          subtypes-of-sets-are-sets'
           (ι x) (pr₁-lc (λ {y} → C-is-subtype y)) (sethood 𝓓)

         C-is-locally-small : C x is-locally 𝓥 small
         C-is-locally-small (c₁ , κ₁ , l₁) (c₂ , κ₂ , l₂) =
          ((c₁ ⊑ₛ c₂) × (c₂ ⊑ₛ c₁))
          , logically-equivalent-props-are-equivalent
             (×-is-prop (⊑ₛ-is-prop-valued c₁ c₂)
                        (⊑ₛ-is-prop-valued c₂ c₁))
             C-is-set
             (λ (l , k) → to-subtype-＝ C-is-subtype
                                       (antisymmetry 𝓓 c₁ c₂
                                         (⊑ₛ-to-⊑ l) (⊑ₛ-to-⊑ k)))
             (λ {refl  → reflexivityₛ c₁ , reflexivityₛ c₁})

         ρ : ↓ᴮₛ x → C x
         ρ (b , l) = β b , basis-is-compact b , ⊑ᴮₛ-to-⊑ᴮ l
         ρ-is-surjection : is-surjection ρ
         ρ-is-surjection (c , c-compact , c-below-x) =
          ∥∥-functor
           (λ {(b , refl) → (b , ⊑ᴮ-to-⊑ᴮₛ c-below-x)
                          , to-subtype-＝ C-is-subtype refl})
           (small-compact-basis-contains-all-compact-elements
             𝓓 β scb c c-compact)
         C-is-image : C x ≃ image ρ
         C-is-image = ≃-sym (surjection-≃-image ρ ρ-is-surjection)

         image-is-small : image ρ is 𝓥 small
         image-is-small =
          sr ρ
             (↓ᴮₛ x , ≃-refl (↓ᴮₛ x))
             C-is-locally-small
             C-is-set

     Cₛ : (x : ⟨ 𝓓 ⟩) → 𝓥 ̇
     Cₛ x = resized (C x) (C-is-small x)
     ιₛ : (x : ⟨ 𝓓 ⟩) → Cₛ x → ⟨ 𝓓 ⟩
     ιₛ x = ι x ∘ ⌜ resizing-condition (C-is-small x) ⌝
     ιₛ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (ιₛ x)
     ιₛ-is-directed x =
      reindexed-family-is-directed 𝓓
       (≃-sym (resizing-condition (C-is-small x)))
       (ι x) (ι-is-directed x)
     ιₛ-is-compact : (x : ⟨ 𝓓 ⟩) (c : Cₛ x) → is-compact 𝓓 (ιₛ x c)
     ιₛ-is-compact x c =
      ι-is-compact x (⌜ resizing-condition (C-is-small x) ⌝ c)
     ιₛ-is-sup : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x (ιₛ x)
     ιₛ-is-sup x = reindexed-family-sup 𝓓
                    (≃-sym (resizing-condition (C-is-small x)))
                    (ι x) x (ι-is-sup x)
     ιₛ-∐-＝  : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (ιₛ-is-directed x) ＝ x
     ιₛ-∐-＝  x = sups-are-unique
                   (underlying-order 𝓓)
                   (pr₁ (axioms-of-dcpo 𝓓))
                   (ιₛ x)
                   (∐-is-sup 𝓓 (ιₛ-is-directed x)) (ιₛ-is-sup x)
-}

\end{code}
