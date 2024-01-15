Tom de Jong, 31 January - 4 February 2022.
Material moved to separate file on 11 June 2022.

Suppose we are given a continuous dcpo D with small basis β : B → D. We show
that D is a continuous retract of the ideal completion Idl(B,⊑) which is an
algebraic dpco with a small compact basis. In fact, we even have an
embedding-projection pair.

We can also consider Idl(B,≪) and we get a continuous dcpo that is isomorphic to
D, but notice that Idl(B,≪) : 𝓥-DCPO {𝓥 ⁺} {𝓥}, while D : 𝓥-DCPO {𝓤} {𝓣}. Thus,
a dcpo with a small basis can essentially be parameterized by a single universe
with a large carrier. Moreover, every dcpo with a small basis can be presented
using ideals.(†)

Similarly, an algebraic dcpo with small compact basis β : B → D is isomorphic to
Idl(B,⊑) and analogous remarks apply in this case.

(†) Here, and similarly elsewhere, we really consider Idl(B,≪ₛ), where ≪ₛ is
    equivalent to ≪ on B, but takes values in 𝓥.

    The size conditions on B and the order are similar to those in Corollary
    2.17 of "Continuous categories and exponentiable toposes" by Johnstone and
    Joyal.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (J)

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.IdealCompletion.Retracts
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (𝓥 : Universe) -- universe where the index types for directedness
                       -- completeness live
       where

open import UF.Equiv
open import UF.Retracts
open import UF.Powerset

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.WayBelow pt fe 𝓥

open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓥
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓥

open import DomainTheory.IdealCompletion.IdealCompletion pt fe pe 𝓥
open import DomainTheory.IdealCompletion.Properties pt fe pe 𝓥

open PropositionalTruncation pt

\end{code}

We will consider ideal completions of:
(1) a small basis ordered by ⊑;
(2) a small basis ordered by ≪;
(3) a small compact basis order by ⊑.

All of these share some common ingredients, which we capture in the following
module so that we can conveniently reuse them.

\begin{code}

module Idl-retract-common
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇ }
        (β : B → ⟨ 𝓓 ⟩)
        (β-is-small-basis : is-small-basis 𝓓 β)
       where

 open is-small-basis β-is-small-basis

\end{code}

However we choose to order the basis, the map that takes an element x : D to the
subset {b : B ∣ b ≪ x} is instrumental. We show that this assignment is
Scott continuous here.

\begin{code}

 ↡ᴮ-subset : (x : ⟨ 𝓓 ⟩) → 𝓟 B
 ↡ᴮ-subset x = (λ b → (b ≪ᴮₛ x , ≪ᴮₛ-is-prop-valued))

 ↡ᴮ-subset-is-inhabited : (x : ⟨ 𝓓 ⟩) → ∥ 𝕋 (↡ᴮ-subset x) ∥
 ↡ᴮ-subset-is-inhabited x = inhabited-if-Directed 𝓓 (↡-inclusionₛ x) (↡ᴮₛ-is-directed x)

 ↡ᴮ-is-monotone : (x y : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ y → ↡ᴮ-subset x ⊆ ↡ᴮ-subset y
 ↡ᴮ-is-monotone x y x-below-y b b-way-below-x =
  ≪ᴮ-to-≪ᴮₛ (≪-⊑-to-≪ 𝓓 (≪ᴮₛ-to-≪ᴮ b-way-below-x) x-below-y)

 ↡ᴮ-is-continuous : {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
                  → is-sup _⊆_ (↡ᴮ-subset (∐ 𝓓 δ)) (↡ᴮ-subset ∘ α)
 ↡ᴮ-is-continuous {I} {α} δ = (ub , lb-of-ubs)
  where
   ub : is-upperbound _⊆_ (↡ᴮ-subset (∐ 𝓓 δ)) (↡ᴮ-subset ∘ α)
   ub i b b-way-below-αᵢ =
    ≪ᴮ-to-≪ᴮₛ (≪-⊑-to-≪ 𝓓 (≪ᴮₛ-to-≪ᴮ b-way-below-αᵢ) (∐-is-upperbound 𝓓 δ i))
   lb-of-ubs : is-lowerbound-of-upperbounds _⊆_
                (↡ᴮ-subset (∐ 𝓓 δ)) (↡ᴮ-subset ∘ α)
   lb-of-ubs S S-is-ub b b-way-below-∐α =
    ∥∥-rec (∈-is-prop S b) lemma₁ interpolant
     where
      interpolant : ∃ c ꞉ B , (β b ≪⟨ 𝓓 ⟩ β c) × (β c ≪⟨ 𝓓 ⟩ (∐ 𝓓 δ))
      interpolant = ≪-unary-interpolation-basis 𝓓 β β-is-small-basis
                     (≪ᴮₛ-to-≪ᴮ b-way-below-∐α)
      lemma₁ : (Σ c ꞉ B , (β b ≪⟨ 𝓓 ⟩ β c) × (β c ≪⟨ 𝓓 ⟩ (∐ 𝓓 δ)))
             → b ∈ S
      lemma₁ (c , b-way-below-c , c-way-below-∐α) =
       ∥∥-rec (∈-is-prop S b) lemma₂ wb-consequence
        where
         wb-consequence : ∃ i ꞉ I , β c ⊑⟨ 𝓓 ⟩ α i
         wb-consequence = c-way-below-∐α I α δ (reflexivity 𝓓 (∐ 𝓓 δ))
         lemma₂ : (Σ i ꞉ I , β c ⊑⟨ 𝓓 ⟩ α i) → b ∈ S
         lemma₂ (i , c-below-αᵢ) =
          S-is-ub i b (≪ᴮ-to-≪ᴮₛ (≪-⊑-to-≪ 𝓓 b-way-below-c c-below-αᵢ))

\end{code}

We show that the supremum of {b : B ∣ b ≪ x} equals x.

\begin{code}

 ∐-of-directed-subset : (I : 𝓟 B)
                      → is-Directed 𝓓 (β ∘ 𝕋-to-carrier I)
                      → ⟨ 𝓓 ⟩
 ∐-of-directed-subset I δ = ∐ 𝓓 δ

 ↡ᴮ-section-of-∐ : (x : ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 (↡-inclusionₛ x))
                 → ∐-of-directed-subset (↡ᴮ-subset x) δ ＝ x
 ↡ᴮ-section-of-∐ x δ = ∐ 𝓓 δ ＝⟨ ⦅1⦆ ⟩
                       ∐ 𝓓 ε ＝⟨ ⦅2⦆ ⟩
                       x     ∎
  where
   ε : is-Directed 𝓓 (↡-inclusionₛ x)
   ε = ↡ᴮₛ-is-directed x
   ⦅1⦆ = ∐-independent-of-directedness-witness 𝓓 δ ε
   ⦅2⦆ = ↡ᴮₛ-∐-＝ x

\end{code}

We present some criteria (which will find application later) for the composition
of ↡ᴮ-subset and ∐ to be a deflation, inflation and retraction-section.

\begin{code}

 ↡ᴮ-∐-deflation : (I : 𝓟 B) {δ : is-Directed 𝓓 (β ∘ 𝕋-to-carrier I)}
                → ((b c : B) → β b ⊑⟨ 𝓓 ⟩ β c → c ∈ I → b ∈ I)
                → ↡ᴮ-subset (∐-of-directed-subset I δ) ⊆ I
 ↡ᴮ-∐-deflation I {δ} I-lowerset b b-way-below-sup =
  ∥∥-rec (∈-is-prop I b) lemma claim
   where
    claim : ∃ i ꞉ 𝕋 I , β b ⊑⟨ 𝓓 ⟩ β ((𝕋-to-carrier I) i)
    claim = ≪ᴮₛ-to-≪ᴮ b-way-below-sup (𝕋 I) (β ∘ 𝕋-to-carrier I) δ
             (reflexivity 𝓓 (∐ 𝓓 δ))
    lemma : (Σ i ꞉ 𝕋 I , β b ⊑⟨ 𝓓 ⟩ β ((𝕋-to-carrier I) i))
          → b ∈ I
    lemma ((c , c-in-I) , b-below-c) = I-lowerset b c b-below-c c-in-I

 ↡ᴮ-∐-inflation : (I : 𝓟 B) {δ : is-Directed 𝓓 (β ∘ 𝕋-to-carrier I)}
                → ((b : B) → b ∈ I → ∃ c ꞉ B , (c ∈ I) × (β b ≪⟨ 𝓓 ⟩ β c))
                → I ⊆ ↡ᴮ-subset (∐-of-directed-subset I δ)
 ↡ᴮ-∐-inflation I {δ} I-rounded b b-in-I = ∥∥-rec ≪ᴮₛ-is-prop-valued lemma claim
  where
   claim : ∃ c ꞉ B , (c ∈ I) × (β b ≪⟨ 𝓓 ⟩ β c)
   claim = I-rounded b b-in-I
   lemma : (Σ c ꞉ B , (c ∈ I) × (β b ≪⟨ 𝓓 ⟩ β c))
         → b ≪ᴮₛ ∐-of-directed-subset I δ
   lemma (c , c-in-I , b-way-below-c) =
    ≪ᴮ-to-≪ᴮₛ (≪-⊑-to-≪ 𝓓 b-way-below-c (∐-is-upperbound 𝓓 δ (c , c-in-I)))

 ∐-↡ᴮ-retract : (I : 𝓟 B) {δ : is-Directed 𝓓 (β ∘ 𝕋-to-carrier I)}
              → ((b c : B) → β b ⊑⟨ 𝓓 ⟩ β c → c ∈ I → b ∈ I)
              → ((b : B) → b ∈ I → ∃ c ꞉ B , (c ∈ I) × (β b ≪⟨ 𝓓 ⟩ β c))
              → ↡ᴮ-subset (∐-of-directed-subset I δ) ＝ I
 ∐-↡ᴮ-retract I {δ} cond₁ cond₂ =
  subset-extensionality pe fe (↡ᴮ-∐-deflation I cond₁) (↡ᴮ-∐-inflation I cond₂)

\end{code}

If we assume the existence of some binary relation (which we think of as an
order) on B, then we can give some convenient criteria for ↡ᴮ being a
semidirected and lower-closed.

\begin{code}

 module _
         (_≺_ : B → B → 𝓥 ̇ )
        where

  ↡ᴮ-lowerset-criterion : (x : ⟨ 𝓓 ⟩)
                        → ((b c : B) → b ≺ c → β b ⊑⟨ 𝓓 ⟩ β c)
                        → (b c : B) → b ≺ c → c ∈ ↡ᴮ-subset x → b ∈ ↡ᴮ-subset x
  ↡ᴮ-lowerset-criterion x β-mon b c b-below-c c-way-below-x =
   ≪ᴮ-to-≪ᴮₛ (⊑-≪-to-≪ 𝓓 (β-mon b c b-below-c) (≪ᴮₛ-to-≪ᴮ c-way-below-x))

  ↡ᴮ-semidirected-set-criterion : (x : ⟨ 𝓓 ⟩)
                                → ((b c : B) → β b ≪⟨ 𝓓 ⟩ β c → b ≺ c)
                                → (a b : B) → a ∈ ↡ᴮ-subset x → b ∈ ↡ᴮ-subset x
                                → ∃ c ꞉ B , c ∈ ↡ᴮ-subset x × (a ≺ c) × (b ≺ c)
  ↡ᴮ-semidirected-set-criterion x β-mon a b a-way-below-x b-way-below-x =
   ∥∥-functor h (≪-binary-interpolation-basis 𝓓 β β-is-small-basis
                 (≪ᴮₛ-to-≪ᴮ a-way-below-x)
                 (≪ᴮₛ-to-≪ᴮ b-way-below-x))
    where
     h : (Σ c ꞉ B , (β a ≪⟨ 𝓓 ⟩ β c) × (β b ≪⟨ 𝓓 ⟩ β c) × (β c ≪⟨ 𝓓 ⟩ x))
       → (Σ c ꞉ B , c ∈ ↡ᴮ-subset x × (a ≺ c) × (b ≺ c))
     h (c , a-way-below-c , b-way-below-c , c-way-below-x) =
      (c , ≪ᴮ-to-≪ᴮₛ c-way-below-x , β-mon a c a-way-below-c
                                   , β-mon b c b-way-below-c)

\end{code}

A major application of the theory of rounded ideals is the following: a
continuous dcpo D with a small basis β : B → D is a continous retract (in fact,
we have an embedding-projection pair) of an algebraic dcpo, namely of Idl(B,⊑).

\begin{code}

module Idl-continuous-retract-of-algebraic
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇ }
        (β : B → ⟨ 𝓓 ⟩)
        (β-is-small-basis : is-small-basis 𝓓 β)
       where

 open is-small-basis β-is-small-basis
 open is-locally-small (locally-small-if-small-basis 𝓓 β β-is-small-basis)

 _⊑ᴮ_ : B → B → 𝓥 ̇
 b ⊑ᴮ b' = β b ⊑ₛ β b'

 ⊑ᴮ-≃-⊑ : {b b' : B} → (b ⊑ᴮ b') ≃ (β b ⊑⟨ 𝓓 ⟩ β b')
 ⊑ᴮ-≃-⊑ {b} {b'} = ⊑ₛ-≃-⊑

 ⊑ᴮ-is-prop-valued : {b b' : B} → is-prop (b ⊑ᴮ b')
 ⊑ᴮ-is-prop-valued = equiv-to-prop ⊑ᴮ-≃-⊑ (prop-valuedness 𝓓 _ _)

 ⊑ᴮ-is-reflexive : {b : B} → b ⊑ᴮ b
 ⊑ᴮ-is-reflexive = ⌜ ⊑ᴮ-≃-⊑ ⌝⁻¹ (reflexivity 𝓓 _)

 ⊑ᴮ-is-transitive : {b b' b'' : B} → b ⊑ᴮ b' → b' ⊑ᴮ b'' → b ⊑ᴮ b''
 ⊑ᴮ-is-transitive u v = ⌜ ⊑ᴮ-≃-⊑ ⌝⁻¹
                         (transitivity 𝓓 _ _ _ (⌜ ⊑ᴮ-≃-⊑ ⌝ u) (⌜ ⊑ᴮ-≃-⊑ ⌝ v))

 open Ideals-of-small-abstract-basis {B} _⊑ᴮ_
        ⊑ᴮ-is-prop-valued
        (reflexivity-implies-INT₂ _⊑ᴮ_ ⊑ᴮ-is-reflexive)
        (reflexivity-implies-INT₀ _⊑ᴮ_ ⊑ᴮ-is-reflexive)
        ⊑ᴮ-is-transitive
      public
 open Idl-retract-common 𝓓 β β-is-small-basis public
 open Idl-mediating 𝓓 β ⌜ ⊑ᴮ-≃-⊑ ⌝ public

 to-Idl : ⟨ 𝓓 ⟩ → Idl
 to-Idl x = (Bₓ , Bₓ-is-lowerset , Bₓ-is-directed-set)
  where
   Bₓ : 𝓟 B
   Bₓ = ↡ᴮ-subset x
   Bₓ-is-lowerset : is-lowerset Bₓ
   Bₓ-is-lowerset = ↡ᴮ-lowerset-criterion _⊑ᴮ_ x (λ b c → ⌜ ⊑ᴮ-≃-⊑ ⌝)
   Bₓ-is-semidirected-set : is-semidirected-set Bₓ
   Bₓ-is-semidirected-set =
    ↡ᴮ-semidirected-set-criterion _⊑ᴮ_ x
     (λ b c b-way-below-c → ⌜ ⊑ᴮ-≃-⊑ ⌝⁻¹ (≪-to-⊑ 𝓓 b-way-below-c))
   Bₓ-is-directed-set : is-directed-set Bₓ
   Bₓ-is-directed-set = (↡ᴮ-subset-is-inhabited x , Bₓ-is-semidirected-set)

 from-Idl : Idl → ⟨ 𝓓 ⟩
 from-Idl I = Idl-mediating-map I

 Idl-retract : retract ⟨ 𝓓 ⟩ of Idl
 Idl-retract = (r , s , γ)
  where
   s : ⟨ 𝓓 ⟩ → Idl
   s = to-Idl
   r : Idl → ⟨ 𝓓 ⟩
   r = from-Idl
   γ : (x : ⟨ 𝓓 ⟩) → r (s x) ＝ x
   γ x = ↡ᴮ-section-of-∐ x (Idl-mediating-directed (s x))

 Idl-deflation : (I : Idl) → to-Idl (from-Idl I) ⊑⟨ Idl-DCPO ⟩ I
 Idl-deflation 𝕀@(I , I-is-ideal) = ↡ᴮ-∐-deflation I γ
  where
   γ : (b c : B) → β b ⊑⟨ 𝓓 ⟩ β c → c ∈ I → b ∈ I
   γ b c b-below-c c-in-I = ideals-are-lowersets I I-is-ideal b c claim c-in-I
    where
     claim : b ⊑ᴮ c
     claim = ⌜ ⊑ᴮ-≃-⊑ ⌝⁻¹ b-below-c

 to-Idl-is-continuous : is-continuous 𝓓 Idl-DCPO to-Idl
 to-Idl-is-continuous I α δ =
  Idl-sups-from-powerset (to-Idl ∘ α) (to-Idl (∐ 𝓓 δ)) (↡ᴮ-is-continuous δ)

 from-Idl-is-continuous : is-continuous Idl-DCPO 𝓓 from-Idl
 from-Idl-is-continuous = Idl-mediating-map-is-continuous

 Idl-continuous-retract : 𝓓 continuous-retract-of Idl-DCPO
 Idl-continuous-retract =
  record
   { s               = to-Idl
   ; r               = from-Idl
   ; s-section-of-r  = retract-condition Idl-retract
   ; s-is-continuous = to-Idl-is-continuous
   ; r-is-continuous = from-Idl-is-continuous
   }

 Idl-embedding-projection-pair : embedding-projection-pair-between 𝓓 Idl-DCPO
 Idl-embedding-projection-pair =
  record
    { e               = to-Idl
    ; p               = from-Idl
    ; e-section-of-p  = retract-condition Idl-retract
    ; e-p-deflation   = Idl-deflation
    ; e-is-continuous = to-Idl-is-continuous
    ; p-is-continuous = from-Idl-is-continuous
    }

 Idl-is-algebraic : is-algebraic-dcpo Idl-DCPO
 Idl-is-algebraic = Idl-is-algebraic-dcpo (λ b → ⊑ᴮ-is-reflexive)

\end{code}

Of course, given a continuous dcpo D with small basis β : B → D, we can also
consider Idl(B,≪) which is isomorphic to D.

\begin{code}

module Idl-continuous
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇ }
        (β : B → ⟨ 𝓓 ⟩)
        (β-is-small-basis : is-small-basis 𝓓 β)
       where

 open is-small-basis β-is-small-basis

 _≺_ : B → B → 𝓥 ̇
 b ≺ b' = b ≪ᴮₛ β b'

 ≺-≃-≪ : {b b' : B} → (b ≺ b') ≃ (β b ≪⟨ 𝓓 ⟩ β b')
 ≺-≃-≪ {b} {b'} = ≪ᴮₛ-≃-≪ᴮ

 ≺-is-prop-valued : {b b' : B} → is-prop (b ≺ b')
 ≺-is-prop-valued = equiv-to-prop ≺-≃-≪ (≪-is-prop-valued 𝓓)

 ≺-is-transitive : {b b' b'' : B} → b ≺ b' → b' ≺ b'' → b ≺ b''
 ≺-is-transitive u v =
  ⌜ ≺-≃-≪ ⌝⁻¹ (≪-is-transitive 𝓓 (⌜ ≺-≃-≪ ⌝ u) (⌜ ≺-≃-≪ ⌝ v))

 ≺-INT₀ : (b : B) → ∃ c ꞉ B , c ≺ b
 ≺-INT₀ b = ∥∥-functor h
             (≪-nullary-interpolation-basis 𝓓 β β-is-small-basis (β b))
  where
   h : (Σ c ꞉ B , β c ≪⟨ 𝓓 ⟩ β b) → (Σ c ꞉ B , c ≺ b)
   h (c , c-way-below-b) = (c , ⌜ ≺-≃-≪ ⌝⁻¹ c-way-below-b)

 ≺-INT₂ : {b₁ b₂ b : B} → b₁ ≺ b → b₂ ≺ b
        → ∃ c ꞉ B , (b₁ ≺ c) × (b₂ ≺ c) × (c ≺ b)
 ≺-INT₂ {b₁} {b₂} {b} b₁-below-b b₂-below-b =
  ∥∥-functor h (≪-binary-interpolation-basis 𝓓 β β-is-small-basis
                (⌜ ≺-≃-≪ ⌝ b₁-below-b) (⌜ ≺-≃-≪ ⌝ b₂-below-b))
   where
    h : (Σ c ꞉ B , (β b₁ ≪⟨ 𝓓 ⟩ β c)
                 × (β b₂ ≪⟨ 𝓓 ⟩ β c)
                 × (β c ≪⟨ 𝓓 ⟩ β b))
      → (Σ c ꞉ B , (b₁ ≺ c) × (b₂ ≺ c) × (c ≺ b))
    h (c , u , v , w) = (c , ⌜ ≺-≃-≪ ⌝⁻¹ u , ⌜ ≺-≃-≪ ⌝⁻¹ v , ⌜ ≺-≃-≪ ⌝⁻¹ w)

 open Ideals-of-small-abstract-basis {B}  _≺_
                                     ≺-is-prop-valued
                                     ≺-INT₂
                                     ≺-INT₀
                                     ≺-is-transitive

 open Idl-retract-common 𝓓 β β-is-small-basis
 open Idl-mediating 𝓓 β (≪-to-⊑ 𝓓 ∘ ⌜ ≺-≃-≪ ⌝)

 to-Idl : ⟨ 𝓓 ⟩ → Idl
 to-Idl x = (Bₓ , Bₓ-is-lowerset , Bₓ-is-directed-set)
  where
   Bₓ : 𝓟 B
   Bₓ = ↡ᴮ-subset x
   Bₓ-is-lowerset : is-lowerset Bₓ
   Bₓ-is-lowerset = ↡ᴮ-lowerset-criterion _≺_ x
                     (λ b c b-below-c → ≪-to-⊑ 𝓓 (⌜ ≺-≃-≪ ⌝ b-below-c))
   Bₓ-is-semidirected-set : is-semidirected-set Bₓ
   Bₓ-is-semidirected-set = ↡ᴮ-semidirected-set-criterion _≺_ x
                             (λ b c → ⌜ ≺-≃-≪ ⌝⁻¹)
   Bₓ-is-directed-set : is-directed-set Bₓ
   Bₓ-is-directed-set = (↡ᴮ-subset-is-inhabited x , Bₓ-is-semidirected-set)

 from-Idl : Idl → ⟨ 𝓓 ⟩
 from-Idl I = Idl-mediating-map I

 to-Idl-is-continuous : is-continuous 𝓓 Idl-DCPO to-Idl
 to-Idl-is-continuous I α δ =
  Idl-sups-from-powerset (to-Idl ∘ α) (to-Idl (∐ 𝓓 δ)) (↡ᴮ-is-continuous δ)

 from-Idl-is-continuous : is-continuous Idl-DCPO 𝓓 from-Idl
 from-Idl-is-continuous = Idl-mediating-map-is-continuous

 to-Idl-section-of-from-Idl : from-Idl ∘ to-Idl ∼ id
 to-Idl-section-of-from-Idl x =
  ↡ᴮ-section-of-∐ x (Idl-mediating-directed (to-Idl x))

 from-Idl-section-of-to-Idl : to-Idl ∘ from-Idl ∼ id
 from-Idl-section-of-to-Idl 𝕀@(I , I-is-ideal) =
  to-subtype-＝ (λ J → being-ideal-is-prop J) (∐-↡ᴮ-retract I claim₁ claim₂)
   where
    claim₁ : (b c : B) → β b ⊑⟨ 𝓓 ⟩ β c → c ∈ I → b ∈ I
    claim₁ b c b-below-c c-in-I = ∥∥-rec (∈-is-prop I b) h (roundedness 𝕀 c-in-I)
     where
      h : (Σ c' ꞉ B , c' ∈ I × (c ≺ c')) → b ∈ I
      h (c' , c'-in-I , c-way-below-c') =
       ideals-are-lowersets I I-is-ideal b c' l c'-in-I
        where
         l : b ≺ c'
         l = (≪ᴮ-to-≪ᴮₛ (⊑-≪-to-≪ 𝓓 b-below-c (≪ᴮₛ-to-≪ᴮ c-way-below-c')))
    claim₂ : (b : B) → b ∈ I → ∃ c ꞉ B , c ∈ I × β b ≪⟨ 𝓓 ⟩ β c
    claim₂ b b-in-I = ∥∥-functor h (roundedness 𝕀 b-in-I)
     where
      h : (Σ c ꞉ B , c ∈ I × b ≺ c)
        → (Σ c ꞉ B , c ∈ I × β b ≪⟨ 𝓓 ⟩ β c)
      h (c , c-in-I , b-below-c) = (c , c-in-I , ⌜ ≺-≃-≪ ⌝ b-below-c)

 Idl-≃ : 𝓓 ≃ᵈᶜᵖᵒ Idl-DCPO
 Idl-≃ = (to-Idl , from-Idl , to-Idl-section-of-from-Idl
                            , from-Idl-section-of-to-Idl ,
          to-Idl-is-continuous , from-Idl-is-continuous)

\end{code}

Finally, if D is an algebraic dpco with small compact basis β : B → D, then
Idl(B,⊑) is isomorphic to D.

\begin{code}

module Idl-algebraic
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇ }
        (β : B → ⟨ 𝓓 ⟩)
        (β-is-small-compact-basis : is-small-compact-basis 𝓓 β)
       where

 open is-small-compact-basis β-is-small-compact-basis
 open Idl-continuous-retract-of-algebraic 𝓓 β
       (compact-basis-is-basis 𝓓 β β-is-small-compact-basis)

 Idl-≃ : 𝓓 ≃ᵈᶜᵖᵒ Idl-DCPO
 Idl-≃ = (to-Idl , from-Idl , retract-condition Idl-retract
                            , from-Idl-section-of-to-Idl ,
          to-Idl-is-continuous , from-Idl-is-continuous)
  where
   -- This is where we use --lossy-unification
   from-Idl-section-of-to-Idl : (I : ⟨ Idl-DCPO ⟩) → to-Idl (from-Idl I) ＝ I
   from-Idl-section-of-to-Idl I =
    antisymmetry Idl-DCPO (to-Idl (from-Idl I)) I (Idl-deflation I) inflationary
     where
      inflationary : I ⊑⟨ Idl-DCPO ⟩ to-Idl (from-Idl I)
      inflationary = ↡ᴮ-∐-inflation (carrier I) condition
       where
        condition : (b : B) → b ∈ᵢ I → ∃ c ꞉ B , c ∈ᵢ I × (β b ≪⟨ 𝓓 ⟩ β c)
        condition b b-in-I = ∣ b , b-in-I , basis-is-compact b ∣

\end{code}
