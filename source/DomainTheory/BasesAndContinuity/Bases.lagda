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

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.BasesAndContinuity.Bases
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

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

 record is-small-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇ where
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

  ↡ᴮₛ-is-sup : (x : ⟨ 𝓓 ⟩)
             → is-sup (underlying-order 𝓓) x (↡-inclusionₛ x)
  ↡ᴮₛ-is-sup x =
   transport (λ - → is-sup (underlying-order 𝓓) - (↡-inclusionₛ x))
             (↡ᴮₛ-∐-＝ x)
             (∐-is-sup 𝓓 (↡ᴮₛ-is-directed x))

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
 has-specified-small-basis = Σ B ꞉ 𝓥 ̇ , Σ β ꞉ (B → ⟨ 𝓓 ⟩) , is-small-basis 𝓓 β

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

 ≪-is-small-valued-if-small-basis : (x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y)
 ≪-is-small-valued-if-small-basis =
  ≪-is-small-valued-str 𝓓
   (structurally-continuous-if-specified-small-basis 𝓓 (B , β , sb))
   locally-small-if-small-basis

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

 record is-small-compact-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇ where
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

  ⊑ᴮₛ-is-prop-valued : {b : B} {x : ⟨ 𝓓 ⟩} → is-prop (b ⊑ᴮₛ x)
  ⊑ᴮₛ-is-prop-valued {b} {x} = equiv-to-prop ⊑ᴮₛ-≃-⊑ᴮ (prop-valuedness 𝓓 (β b) x)

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

 index-of-compact-basis : has-specified-small-compact-basis → 𝓥 ̇
 index-of-compact-basis (B , _) = B

 family-of-compact-elements : (𝒷 : has-specified-small-compact-basis)
                            → index-of-compact-basis 𝒷 → ⟨ 𝓓 ⟩
 family-of-compact-elements (_ , β , _) = β

 small-compact-basis : (𝒷 : has-specified-small-compact-basis)
                     → is-small-compact-basis 𝓓 (family-of-compact-elements 𝒷)
 small-compact-basis (_ , _ , scb) = scb

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

We can improve on the above in the presence of univalence and set replacement,
in which case we can derive structural-algebraicity from an unspecified small
compact basis. This is explained and formalised in CompactBasis.

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
        (pe : Prop-Ext)
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'})
        (ρ : 𝓓 continuous-retract-of 𝓔)
       where

 open _continuous-retract-of_ ρ

 small-basis-from-continuous-retract : {B : 𝓥 ̇ } (β : B → ⟨ 𝓔 ⟩)
                                     → is-small-basis 𝓔 β
                                     → is-small-basis 𝓓 (r ∘ β)
 small-basis-from-continuous-retract {B} β sb =
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

Added 5 June 2024.

We transfer small (compact) bases along isomorphisms of dcpos.

\begin{code}

module _
        (pe : Prop-Ext)
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'})
       where

 small-basis-from-≃ᵈᶜᵖᵒ : 𝓓 ≃ᵈᶜᵖᵒ 𝓔
                        → has-specified-small-basis 𝓓
                        → has-specified-small-basis 𝓔
 small-basis-from-≃ᵈᶜᵖᵒ 𝕗@(f , g , s , r , cf , cg) (B , β , sb) =
  B , f ∘ β ,
  small-basis-from-continuous-retract pe 𝓔 𝓓
   (≃ᵈᶜᵖᵒ-to-continuous-retract 𝓔 𝓓 (≃ᵈᶜᵖᵒ-inv 𝓓 𝓔 𝕗)) β sb

 small-compact-basis-from-≃ᵈᶜᵖᵒ : 𝓓 ≃ᵈᶜᵖᵒ 𝓔
                                → has-specified-small-compact-basis 𝓓
                                → has-specified-small-compact-basis 𝓔
 small-compact-basis-from-≃ᵈᶜᵖᵒ 𝕗@(f , g , s , r , cf , cg) (B , β , scb) =
  B , f ∘ β ,
  small-and-compact-basis 𝓔 (f ∘ β)
   (pr₂ (pr₂ (small-basis-from-≃ᵈᶜᵖᵒ
               𝕗 (B , β , compact-basis-is-basis 𝓓 β scb))))
   (λ b → embeddings-preserve-compactness
           𝓓 𝓔 f cf g cg s (λ y → ＝-to-⊑ 𝓔 (r y)) (β b) (basis-is-compact b))
    where
     open is-small-compact-basis scb

\end{code}

End of addition.

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
          (Π-is-prop fe (λ b → ⊑ₛ-is-prop-valued (f (β b)) (g (β b))))
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

Added 2 June 2024.

Any sup-complete dcpo with a small basis has a greatest element.
(In fact, it is inf-complete, but we don't formalise this here, see
Locales.AdjointFunctorTheoremForFrames though.)

\begin{code}

open import DomainTheory.Basics.SupComplete pt fe 𝓥

greatest-element-if-sup-complete-with-small-basis :
   (𝓓 : DCPO {𝓤} {𝓣})
 → is-sup-complete 𝓓
 → has-unspecified-small-basis 𝓓
 → Σ ⊤ ꞉ ⟨ 𝓓 ⟩ , ((x : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ ⊤)
greatest-element-if-sup-complete-with-small-basis 𝓓 sc = ∥∥-rec I II
 where
  I : is-prop (Σ ⊤ ꞉ ⟨ 𝓓 ⟩ , ((x : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ ⊤))
  I (t , l) (s , k) = to-subtype-＝
                       (λ y → Π-is-prop fe (λ x → prop-valuedness 𝓓 x y))
                       (antisymmetry 𝓓 t s (k t) (l s))
  II : has-specified-small-basis 𝓓
     → Σ ⊤ ꞉ ⟨ 𝓓 ⟩ , ((x : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ ⊤)
  II (B , β , β-is-small-basis) = ⊤ , ⊤-is-greatest
   where
    open is-small-basis β-is-small-basis
    open is-sup-complete sc
    ⊤ : ⟨ 𝓓 ⟩
    ⊤ = ⋁ β
    ⊤-is-greatest : (x : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ ⊤
    ⊤-is-greatest x =
     sup-is-lowerbound-of-upperbounds
      (underlying-order 𝓓) (↡ᴮ-is-sup x) ⊤ (λ (b , _) → ⋁-is-upperbound β b)

\end{code}

Added 26 June 2024.
We can refine a small basis to be closed under finite joins.

\begin{code}

module _
        (𝓓 : DCPO{𝓤} {𝓣})
        {B : 𝓥 ̇ }
        (β : B → ⟨ 𝓓 ⟩)
        (β-is-basis : is-small-basis 𝓓 β)
        (𝓓-has-finite-joins : has-finite-joins 𝓓)
       where

 open has-finite-joins 𝓓-has-finite-joins

 record basis-has-finite-joins : 𝓥 ⊔ 𝓤 ̇ where
  field
   ⊥ᴮ : B
   _∨ᴮ_ : B → B → B
   ⊥ᴮ-is-⊥ : β ⊥ᴮ ＝ ⊥
   ∨ᴮ-is-∨ : (a b : B) → β (a ∨ᴮ b) ＝ β a ∨ β b

  infix 100 _∨ᴮ_

  ⊥ᴮ-is-least : (b : B) → β ⊥ᴮ ⊑⟨ 𝓓 ⟩ β b
  ⊥ᴮ-is-least b = transport⁻¹ (λ - → - ⊑⟨ 𝓓 ⟩ β b) ⊥ᴮ-is-⊥ (⊥-is-least (β b))

  ∨ᴮ-is-upperbound₁ : {a b : B} → β a ⊑⟨ 𝓓 ⟩ β (a ∨ᴮ b)
  ∨ᴮ-is-upperbound₁ {a} {b} =
   transport⁻¹ (λ - → β a ⊑⟨ 𝓓 ⟩ -) (∨ᴮ-is-∨ a b) ∨-is-upperbound₁

  ∨ᴮ-is-upperbound₂ : {a b : B} → β b ⊑⟨ 𝓓 ⟩ β (a ∨ᴮ b)
  ∨ᴮ-is-upperbound₂ {a} {b} =
   transport⁻¹ (λ - → β b ⊑⟨ 𝓓 ⟩ -) (∨ᴮ-is-∨ a b) ∨-is-upperbound₂

  ∨ᴮ-is-lowerbound-of-upperbounds : {a b c : B}
                                  → β a ⊑⟨ 𝓓 ⟩ β c → β b ⊑⟨ 𝓓 ⟩ β c
                                  → β (a ∨ᴮ b) ⊑⟨ 𝓓 ⟩ β c
  ∨ᴮ-is-lowerbound-of-upperbounds {a} {b} {c} u v =
   transport⁻¹ (λ - → - ⊑⟨ 𝓓 ⟩ β c) (∨ᴮ-is-∨ a b)
               (∨-is-lowerbound-of-upperbounds u v)

module _
        (𝓓 : DCPO{𝓤} {𝓣})
        {B : 𝓥 ̇ }
        (β : B → ⟨ 𝓓 ⟩)
        (β-is-basis : is-small-basis 𝓓 β)
        (𝓓-has-finite-joins : has-finite-joins 𝓓)
       where

 open import MLTT.List
 open make-family-directed 𝓓 𝓓-has-finite-joins
 open has-finite-joins 𝓓-has-finite-joins

 refine-basis-to-have-finite-joins :
  Σ B' ꞉ 𝓥 ̇ , Σ β' ꞉ (B' → ⟨ 𝓓 ⟩) ,
  Σ p ꞉ is-small-basis 𝓓 β' , basis-has-finite-joins 𝓓 β' p 𝓓-has-finite-joins
 refine-basis-to-have-finite-joins = B' , β' , p , j
  where
   B' : 𝓥 ̇
   B' = List B
   β' : List B → ⟨ 𝓓 ⟩
   β' = directify β

   p : is-small-basis 𝓓 β'
   p = record
        { ≪ᴮ-is-small =
           λ x l → ≪-is-small-valued-if-small-basis 𝓓 β β-is-basis (β' l) x;
          ↡ᴮ-is-directed =
           λ x → ↡ᴮ-directedness-criterion 𝓓 β' x (ι x) (δ x) (ub x);
          ↡ᴮ-is-sup = λ x → ↡ᴮ-sup-criterion 𝓓 β' x (ι x) (sup x)
       }
    where
     open is-small-basis β-is-basis
     I : β' ∘ [_] ∼ β
     I b = antisymmetry 𝓓 (β' [ b ]) (β b)
            (∨-is-lowerbound-of-upperbounds
              (reflexivity 𝓓 (β b)) (⊥-is-least (β b)))
            ∨-is-upperbound₁
     ι : (x : ⟨ 𝓓 ⟩)
       → ↡ᴮₛ x → Σ l ꞉ List B , β' l ≪⟨ 𝓓 ⟩ x
     ι x (b , w) = [ b ] , transport⁻¹ (λ - → - ≪⟨ 𝓓 ⟩ x) (I b) (≪ᴮₛ-to-≪ᴮ w)
     II : (x : ⟨ 𝓓 ⟩) → ↡-inclusion 𝓓 β' x ∘ ι x ∼ ↡-inclusionₛ x
     II x (b , w) = I b
     δ : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↡-inclusion 𝓓 β' x ∘ ι x)
     δ x = transport⁻¹ (is-Directed 𝓓) (dfunext fe (II x)) (↡ᴮₛ-is-directed x)
     ub : (x : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (δ x)
     ub x = transport⁻¹ (λ - → x ⊑⟨ 𝓓 ⟩ -)
                        (∐-family-＝' 𝓓 (II x) (δ x) (↡ᴮₛ-is-directed x))
                        (↡ᴮₛ-∐-⊒ x)
     sup : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x (↡-inclusion 𝓓 β' x ∘ ι x)
     sup x = transport⁻¹ (is-sup (underlying-order 𝓓) x)
                         (dfunext fe (II x))
                         (↡ᴮₛ-is-sup x)

   j : basis-has-finite-joins 𝓓 β' p 𝓓-has-finite-joins
   j = record
        { ⊥ᴮ = [] ;
          _∨ᴮ_ = _++_ ;
          ⊥ᴮ-is-⊥ = refl ;
          ∨ᴮ-is-∨ = finite-join-eq
       }
    where
     finite-join-eq : (l k : List B) → directify β (l ++ k) ＝ β' l ∨ β' k
     finite-join-eq l k =
      sups-are-unique (underlying-order 𝓓) (poset-axioms-of-dcpo 𝓓)
                      (∨-family 𝓓 (β' l) (β' k))
                      (++-is-binary-sup β l k)
                      (∨-is-sup (β' l) (β' k))

\end{code}
