Tom de Jong, 31 May 2024.
(Following a suggestion by Martín Escardó.)

We consider the large ordinal of small ordinals as a locally small algebraic
dcpo which does not have a small basis (even impredicatively).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.PropTrunc
open import UF.Size
open import UF.Univalence

module DomainTheory.Examples.Ordinals
        (pt : propositional-truncations-exist)
        (ua : Univalence)
        (sr : Set-Replacement pt)
        (𝓤 : Universe)
       where

open PropositionalTruncation pt

open import MLTT.List

open import UF.Base
open import UF.FunExt
open import UF.Subsingletons
open import UF.UA-FunExt

private
 fe' : FunExt
 fe' = Univalence-gives-FunExt ua

 fe : Fun-Ext
 fe {𝓤} {𝓥} = fe' 𝓤 𝓥

 pe' : PropExt
 pe' = Univalence-gives-PropExt ua

 pe : Prop-Ext
 pe {𝓤} = pe' 𝓤

open import DomainTheory.Basics.Dcpo pt fe 𝓤 hiding (⟨_⟩)
open import DomainTheory.Basics.SupComplete pt fe 𝓤
open import DomainTheory.Basics.WayBelow pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤

open import Ordinals.Arithmetic fe'
open import Ordinals.ArithmeticProperties ua
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Type
open import Ordinals.Underlying

open suprema pt sr

\end{code}

The ordinals in a given universe 𝓤 form a dcpo whose carrier lives in the
successor universe 𝓤 ⁺. The ordinal relation lives in 𝓤, and so the dcpo of
ordinals is large, but locally small. It has suprema for all families of
ordinals indexed by types in 𝓤.

\begin{code}

Ordinals-DCPO : DCPO {𝓤 ⁺} {𝓤}
Ordinals-DCPO = Ordinal 𝓤 , _⊴_ ,
                (underlying-type-is-set fe' (OO 𝓤) ,
                 ⊴-is-prop-valued , (⊴-refl , ⊴-trans , ⊴-antisym)) ,
                (λ I α δ → (sup α) , sup-is-least-upper-bound α)

Ordinals-DCPO-is-sup-complete : is-sup-complete Ordinals-DCPO
Ordinals-DCPO-is-sup-complete =
 record
  { ⋁ = sup ;
    ⋁-is-sup = sup-is-least-upper-bound
  }

open sup-complete-dcpo Ordinals-DCPO Ordinals-DCPO-is-sup-complete

\end{code}

The dcpo of ordinals is algebraic. This follows from three facts:
(1) Every ordinal α is equal to the supremum of the successors of its initial
    segments, i.e. α = sup (λ a → (α ↓ a) +ₒ 𝟙ₒ)
(2) Every successor ordinal, i.e. every ordinal of the form β +ₒ 𝟙ₒ is compact.
(3) The family in (1) can be "directified" by taking finite joins which
    preserves compactness.

\begin{code}

successor-ordinals-are-compact : (α : Ordinal 𝓤)
                               → is-compact Ordinals-DCPO (α +ₒ 𝟙ₒ)
successor-ordinals-are-compact α I β δ l =
 ∥∥-functor (λ (i , b , eq₂) → ⦅3⦆ (i , b , (eq₁ ∙ eq₂))) ⦅2⦆
  where
   ⦅1⦆ : Σ s ꞉ ⟨ sup β ⟩ , α ＝ sup β ↓ s
   ⦅1⦆ = ⊴-gives-≼ (α +ₒ 𝟙ₒ) (sup β) l α (successor-increasing α)
   s : ⟨ sup β ⟩
   s = pr₁ ⦅1⦆
   eq₁ : α ＝ sup β ↓ s
   eq₁ = pr₂ ⦅1⦆
   ⦅2⦆ : ∥ Σ i ꞉ I , Σ b ꞉ ⟨ β i ⟩ , sup β ↓ s ＝ β i ↓ b ∥
   ⦅2⦆ = initial-segment-of-sup-is-initial-segment-of-some-component β s
   ⦅3⦆ : (Σ i ꞉ I , Σ b ꞉ ⟨ β i ⟩ , α ＝ β i ↓ b)
       → Σ i ꞉ I , (α +ₒ 𝟙ₒ) ⊴ β i
   ⦅3⦆ (i , b , refl) = i , upper-bound-of-successors-of-initial-segments (β i) b

private
 module _ (α : Ordinal 𝓤) where
  family : ⟨ α ⟩ → Ordinal 𝓤
  family a = (α ↓ a) +ₒ 𝟙ₒ

Ordinals-DCPO-is-algebraic' : structurally-algebraic Ordinals-DCPO
Ordinals-DCPO-is-algebraic' =
 record
  { index-of-compact-family = λ α → List ⟨ α ⟩
  ; compact-family = λ α → directify (family α)
  ; compact-family-is-directed = λ α → directify-is-directed (family α)
  ; compact-family-is-compact = λ α → directify-is-compact
                                       (family α)
                                       (λ a → successor-ordinals-are-compact (α ↓ a))
  ; compact-family-∐-＝ = eq
  }
   where
    eq : (α : Ordinal 𝓤)
       → ∐ Ordinals-DCPO (directify-is-directed (family α)) ＝ α
    eq α = ∐ Ordinals-DCPO (directify-is-directed (family α)) ＝⟨ I ⟩
           sup (family α)                                     ＝⟨ II ⟩
           α                                                  ∎
     where
      II = (supremum-of-successors-of-initial-segments pt sr α) ⁻¹
      I = sups-are-unique _⊴_
           (poset-axioms-of-dcpo Ordinals-DCPO) (family α)
           (directify-sup' (family α)
             (∐ Ordinals-DCPO δ) (∐-is-sup Ordinals-DCPO δ))
           (sup-is-least-upper-bound (family α))
       where
        δ : is-Directed Ordinals-DCPO (directify (family α))
        δ = directify-is-directed (family α)

Ordinals-DCPO-is-algebraic : is-algebraic-dcpo Ordinals-DCPO
Ordinals-DCPO-is-algebraic = ∣ Ordinals-DCPO-is-algebraic' ∣

\end{code}

Unlike many other examples, such as the dpcos in the Scott model of PCF, or
Scott's D∞, the dpco of ordinals, while algebraic, does not have a small
(compact) basis. If it did, we could take the join of all the basis elements to
obtain a greatest ordinal, which does not exist.

\begin{code}

Ordinals-DCPO-has-no-small-basis : ¬ (has-unspecified-small-basis Ordinals-DCPO)
Ordinals-DCPO-has-no-small-basis h =
 no-greatest-ordinal
  (greatest-element-if-sup-complete-with-small-basis
    Ordinals-DCPO
    Ordinals-DCPO-is-sup-complete
    h)

Ordinals-DCPO-has-no-small-compact-basis :
 ¬ (has-unspecified-small-compact-basis Ordinals-DCPO)
Ordinals-DCPO-has-no-small-compact-basis h =
 Ordinals-DCPO-has-no-small-basis
  (∥∥-functor (λ (B , β , scb) → B , β , compact-basis-is-basis _ β scb) h)

\end{code}
