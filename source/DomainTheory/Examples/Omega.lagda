Tom de Jong, 28 February 2022

We show that the type Ω 𝓤 of propositions in a universe 𝓤 form an algebraic
pointed 𝓤-dcpo.

In fact, we show that the Booleans give a small compact basis for Ω 𝓤 and
characterize the compact elements of Ω 𝓤 as the decidable propositions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.Examples.Omega
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (𝓤 : Universe)
       where

open PropositionalTruncation pt

open import MLTT.Plus-Properties
open import NotionsOfDecidability.Decidable

open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ImageAndSurjection pt
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier renaming (⊥ to ⊥Ω ; ⊤ to ⊤Ω)
open import UF.SubtypeClassifier-Properties
open import UF.Sets
open import OrderedTypes.Poset fe

open import DomainTheory.Basics.Dcpo pt fe 𝓤
open import DomainTheory.Basics.Miscelanea pt fe 𝓤
open import DomainTheory.Basics.Pointed pt fe 𝓤
open import DomainTheory.Basics.WayBelow pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤

_⊑_ : Ω 𝓤 → Ω 𝓤 → 𝓤 ̇
P ⊑ Q = P holds → Q holds

⊑-is-reflexive : (P : Ω 𝓤) → P ⊑ P
⊑-is-reflexive _ = id

⊑-is-prop-valued : (P Q : Ω 𝓤) → is-prop (P ⊑ Q)
⊑-is-prop-valued P Q = Π-is-prop fe (λ _ → holds-is-prop Q)

⊑-is-transitive : (P Q R : Ω 𝓤) → P ⊑ Q → Q ⊑ R → P ⊑ R
⊑-is-transitive P Q R f g p = g (f p)

⊑-is-antisymmetric : (P Q : Ω 𝓤) → P ⊑ Q → Q ⊑ P → P ＝ Q
⊑-is-antisymmetric P Q f g =
 to-subtype-＝ (λ _ → being-prop-is-prop fe)
              (pe (holds-is-prop P) (holds-is-prop Q) f g)

Ω-DCPO : DCPO {𝓤 ⁺} {𝓤}
Ω-DCPO = (Ω 𝓤 , _⊑_
       , (Ω-is-set fe pe
       , ⊑-is-prop-valued
       , ⊑-is-reflexive
       , ⊑-is-transitive
       , ⊑-is-antisymmetric)
       , γ)
 where
  γ : is-directed-complete _⊑_
  γ I α δ = (sup , ub , lb-of-ubs)
   where
    sup : Ω 𝓤
    sup = ((∃ i ꞉ I , α i holds) , ∃-is-prop)
    ub : is-upperbound _⊑_ sup α
    ub i p = ∣ i , p ∣
    lb-of-ubs : is-lowerbound-of-upperbounds _⊑_ sup α
    lb-of-ubs Q Q-is-ub = ∥∥-rec (holds-is-prop Q) h
     where
      h : (Σ i ꞉ I , α i holds) → Q holds
      h (i , p) = Q-is-ub i p

Ω-DCPO⊥ : DCPO⊥ {𝓤 ⁺} {𝓤}
Ω-DCPO⊥ = Ω-DCPO , ((𝟘 , 𝟘-is-prop) , (λ _ → 𝟘-elim))

\end{code}

We proceed by showing that the Booleans give a small compact basis for Ω 𝓤.

\begin{code}

⊤Ω-is-greatest : (P : Ω 𝓤) → P ⊑ ⊤Ω
⊤Ω-is-greatest P _ = ⋆

Bool : 𝓤 ̇
Bool = 𝟙{𝓤} + 𝟙{𝓤}

κ : Bool → Ω 𝓤
κ (inl _) = ⊥Ω
κ (inr _) = ⊤Ω

κ⁺ : (P : Ω 𝓤) → (Σ b ꞉ Bool , κ b ⊑ P) → Ω 𝓤
κ⁺ P = κ ∘ pr₁

κ⁺-is-directed : (P : Ω 𝓤) → is-Directed Ω-DCPO (κ⁺ P)
κ⁺-is-directed P = inh , semidir
 where
  inh : ∥ domain (κ⁺ P) ∥
  inh = ∣ inl ⋆ , ⊥-is-least Ω-DCPO⊥ P ∣
  semidir : is-semidirected _⊑_ (κ⁺ P)
  semidir (inl ⋆ , _) i = ∣ i , ⊥-is-least Ω-DCPO⊥ (κ⁺ P i)
                              , ⊑-is-reflexive (κ⁺ P i) ∣
  semidir (inr ⋆ , u) j = ∣ (inr ⋆ , u) , ⊑-is-reflexive ⊤Ω
                                        , ⊤Ω-is-greatest (κ⁺ P j) ∣

κ⁺-sup : (P : Ω 𝓤) → is-sup _⊑_ P (κ⁺ P)
κ⁺-sup P = ub , lb-of-ubs
 where
  ub : is-upperbound _⊑_ P (κ⁺ P)
  ub (i , u) = u
  lb-of-ubs : is-lowerbound-of-upperbounds _⊑_ P (κ⁺ P)
  lb-of-ubs Q Q-is-ub p = Q-is-ub (inr ⋆ , (λ _ → p)) ⋆

𝟙-is-compact : is-compact Ω-DCPO ⊤Ω
𝟙-is-compact I α δ ⊤Ω-below-∐α = ∥∥-functor γ (⊤Ω-below-∐α ⋆)
 where
  γ : (Σ i ꞉ I , α i holds) → (Σ i ꞉ I , ⊤Ω ⊑ α i)
  γ (i , p) = (i , (λ _ → p))

compact-if-in-image-of-κ : (P : Ω 𝓤) → P ∈image κ → is-compact Ω-DCPO P
compact-if-in-image-of-κ P P-in-image-of-κ =
 ∥∥-rec (being-compact-is-prop Ω-DCPO P) γ P-in-image-of-κ
  where
   γ : (Σ b ꞉ Bool , κ b ＝ P) → is-compact Ω-DCPO P
   γ (inl ⋆ , refl) = ⊥-is-compact Ω-DCPO⊥
   γ (inr ⋆ , refl) = 𝟙-is-compact

in-image-of-κ-if-compact : (P : Ω 𝓤) → is-compact Ω-DCPO P → P ∈image κ
in-image-of-κ-if-compact P P-cpt = ∥∥-functor goal claim
 where
  I : 𝓤 ̇
  I = 𝟙{𝓤} + (P holds)
  α : I → Ω 𝓤
  α = add-⊥ Ω-DCPO⊥ (λ _ → ⊤Ω)
  δ : is-Directed Ω-DCPO α
  δ = add-⊥-is-directed Ω-DCPO⊥
       (subsingleton-indexed-is-semidirected Ω-DCPO (λ _ → ⊤Ω) (holds-is-prop P))
  P-below-∐α : P ⊑ ∐ Ω-DCPO {I} {α} δ
  P-below-∐α p = ∣ inr p , ⋆ ∣
  claim : ∃ i ꞉ I , P ⊑ α i
  claim = P-cpt I α δ P-below-∐α
  goal : (Σ i ꞉ I , P ⊑ α i) → Σ b ꞉ Bool , κ b ＝ P
  goal (inl ⋆ , u) = (inl ⋆ , ⊑-is-antisymmetric ⊥Ω P
                               (⊥-is-least Ω-DCPO⊥ P) u)
  goal (inr p , u) = (inr ⋆ , ⊑-is-antisymmetric ⊤Ω P (λ _ → p) u)

κ-is-small-compact-basis : is-small-compact-basis Ω-DCPO κ
κ-is-small-compact-basis =
 record
  { basis-is-compact = λ b → compact-if-in-image-of-κ (κ b) ∣ b , refl ∣
  ; ⊑ᴮ-is-small      = λ P b → (κ b ⊑ P , ≃-refl (κ b ⊑ P))
  ; ↓ᴮ-is-directed   = κ⁺-is-directed
  ; ↓ᴮ-is-sup        = κ⁺-sup
  }

Ω-has-specified-small-compact-basis : has-specified-small-compact-basis Ω-DCPO
Ω-has-specified-small-compact-basis = (Bool , κ , κ-is-small-compact-basis)

\end{code}

Hence, Ω 𝓤 is algebraic.

\begin{code}

Ω-structurally-algebraic : structurally-algebraic Ω-DCPO
Ω-structurally-algebraic =
 structurally-algebraic-if-specified-small-compact-basis Ω-DCPO
  Ω-has-specified-small-compact-basis

Ω-is-algebraic-dcpo : is-algebraic-dcpo Ω-DCPO
Ω-is-algebraic-dcpo = ∣ Ω-structurally-algebraic ∣

\end{code}

Finally, we show that the compact elements of Ω 𝓤 are exactly the decidable
propositions.

\begin{code}

compact-iff-empty-or-unit : (P : Ω 𝓤)
                          → is-compact Ω-DCPO P ↔ (P ＝ ⊥Ω) + (P ＝ ⊤Ω)
compact-iff-empty-or-unit P = I , II
 where
  I : is-compact Ω-DCPO P → (P ＝ ⊥Ω) + (P ＝ ⊤Ω)
  I c = ∥∥-rec (+-is-prop (Ω-is-set fe pe) (Ω-is-set fe pe) I₁)
                  I₂
                  (in-image-of-κ-if-compact P c)
   where
    I₁ : P ＝ ⊥Ω → ¬ (P ＝ ⊤Ω)
    I₁ refl e = 𝟘-is-not-𝟙 (ap (_holds) e)
    I₂ : (Σ b ꞉ domain κ , κ b ＝ P) → (P ＝ ⊥Ω) + (P ＝ ⊤Ω)
    I₂ (inl ⋆ , refl) = inl refl
    I₂ (inr ⋆ , refl) = inr refl
  II : (P ＝ ⊥Ω) + (P ＝ ⊤Ω) → is-compact Ω-DCPO P
  II (inl refl) = ⊥-is-compact Ω-DCPO⊥
  II (inr refl) = 𝟙-is-compact

compact-iff-decidable : (P : Ω 𝓤) → is-compact Ω-DCPO P ↔ is-decidable (P holds)
compact-iff-decidable P = I , II
 where
  I : is-compact Ω-DCPO P → is-decidable (P holds)
  I c = h (lr-implication (compact-iff-empty-or-unit P) c)
   where
    h : (P ＝ ⊥Ω) + (P ＝ ⊤Ω) → is-decidable (P holds)
    h (inl refl) = inr 𝟘-elim
    h (inr refl) = inl ⋆
  II : is-decidable (P holds) → is-compact Ω-DCPO P
  II d = rl-implication (compact-iff-empty-or-unit P)
                        (h (decidable-truth-values-are-⊥-or-⊤' pe fe P d))
   where
    h : (P ＝ ⊤Ω) + (P ＝ ⊥Ω) → (P ＝ ⊥Ω) + (P ＝ ⊤Ω)
    h (inl x) = inr x
    h (inr x) = inl x

\end{code}

Added 8 July 2024.

We can use the above to give an explicit counterexample to the claim that a
structural continuity of a dcpo expresses a property.

The idea is simply that if α : I → 𝓓 approximates an element x of a dcpo 𝓓, then
so does [α,α] : I + I → 𝓓, but the index types of these families are not equal
in general. Indeed they fail to be equal for the approximating family of ⊥Ω that
we constructed above.

\begin{code}

structural-continuity-is-not-prop : ¬ is-prop (structurally-continuous Ω-DCPO)
structural-continuity-is-not-prop ν =
 I+I-is-not-prop (equiv-to-prop (≃-sym equivalent-index-types) I-is-prop)
  where
   open structurally-continuous
   open is-small-compact-basis κ-is-small-compact-basis
   s₁ : structurally-continuous Ω-DCPO
   s₁ = structurally-continuous-if-structurally-algebraic
         Ω-DCPO
         Ω-structurally-algebraic

   I = index-of-approximating-family s₁ ⊥Ω
   i₀ : I
   i₀ = inl ⋆ , 𝟘-elim
   I-is-prop : is-prop I
   I-is-prop (inl ⋆ , _) (inl ⋆ , _) =
    to-subtype-＝ (λ b → ⊑ᴮₛ-is-prop-valued {b} {⊥Ω})
                  refl
   I-is-prop (inl ⋆ , _) (inr ⋆ , b) = 𝟘-elim (b ⋆)
   I-is-prop (inr ⋆ , b) _           = 𝟘-elim (b ⋆)

   s₂ : structurally-continuous Ω-DCPO
   s₂ = structurally-continuous-+-construction Ω-DCPO s₁

   equivalent-index-types : I ≃ I + I
   equivalent-index-types = idtoeq I (I + I)
                                   (ap (λ - → index-of-approximating-family - ⊥Ω)
                                       (ν s₁ s₂))

   I+I-is-not-prop : ¬ is-prop (I + I)
   I+I-is-not-prop ρ = +disjoint (ρ (inl i₀) (inr i₀))

\end{code}