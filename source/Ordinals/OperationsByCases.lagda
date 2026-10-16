Tom de Jong, 16 October 2026.

We introduce a general scheme (cf. the BoundedOperations file) that captures
addition, multiplication and exponentiation by a fixed ordinal α.
This scheme used to be part of ArithmeticReflection, but was factored out to be
hosted in this separate file.

We consider an operation F : Ordinal 𝓤 → Ordinal 𝓤 together with
  - an ordinal Z : Ordinal 𝓤 (for the zero case)
  - an operation S : Ordinal 𝓤 → Ordinal 𝓤 (for the successor case)
such that
  - F (β +ₒ 𝟙ₒ) ＝ S (F β)         for all β : Ordinal 𝓤,
  - F (sup L)   ＝ Z ∨ sup (F ∘ L) for all L : I → Ordinal 𝓤 with I : 𝓤.

Note that if we take L to be the empty family, then we get
F 𝟘ₒ ＝ Z ∨ 𝟘ₒ ＝ Z, which is why Z is the zero case.

Such an operation F is unique, because it must satisfy the recursive equation
  F β = Z ∨ sup (λ b → S (F (β ↓ b))),
since every ordinal is the supremum of the successors of its initial segments.

As mentioned, examples are addition, multiplication and exponentiation
by a fixed ordinal α. Specifically,
- for F := (-) +ₒ α, we take Z = α  and S β := β +ₒ 𝟙ₒ;
- for F := (-) ×ₒ α, we take Z = 𝟘ₒ and S β := β +ₒ α;
- for F := α ^ₒ (-), we take Z = 𝟙ₒ and S β := β ×ₒ α (given 𝟙ₒ ⊴ α).

In particular, these operations are uniquely specified.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.OperationsByCases
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import MLTT.Spartan hiding (J)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.SupremaPreservation ua pt sr
open import Ordinals.Type
open import Ordinals.Underlying

open PropositionalTruncation pt
open suprema pt sr

\end{code}

We find it convenient to present Z ∨ sup (F ∘ L) via a single supremum.

\begin{code}

extended-sup : {I : 𝓤 ̇ } (L : I → Ordinal 𝓤) (Z : Ordinal 𝓤) → Ordinal 𝓤
extended-sup {𝓤} {I} L Z = sup {I = 𝟙 + I} (cases (λ (_ : 𝟙{𝓤}) → Z) L)

\end{code}

As shown below, Z and S determine F uniquely, because any F which
satisfies the above equations will be equal to the function G defined
by transfinite recursion as
  G β := Z ∨ sup (λ (b : ⟨ β ⟩) → S (G (β ↓ b))).
This map G is called canonical-spec-by-cases below.

\begin{code}

canonical-spec-by-cases : (S : Ordinal 𝓤 → Ordinal 𝓤) (Z : Ordinal 𝓤)
                        → Ordinal 𝓤 → Ordinal 𝓤
canonical-spec-by-cases {𝓤} S Z =
 transfinite-recursion-on-OO (Ordinal 𝓤)
                             (λ β ih → extended-sup (λ b → S (ih b)) Z)

module operation-by-cases-framework
        (F : Ordinal 𝓤 → Ordinal 𝓤)
        (S : Ordinal 𝓤 → Ordinal 𝓤)
        (Z : Ordinal 𝓤)
        (F-succ : (β : Ordinal 𝓤) → F (β +ₒ 𝟙ₒ) ＝ S (F β))
        (F-sup : preserves-suprema-up-to-join F Z)
       where

 recursive-equation : (β : Ordinal 𝓤)
                    → F β ＝ extended-sup (λ (b : ⟨ β ⟩) → S (F (β ↓ b))) Z
 recursive-equation β = F β                                        ＝⟨ I ⟩
                        F (sup λ b → (β ↓ b) +ₒ 𝟙ₒ)                ＝⟨ II ⟩
                        extended-sup (F ∘ (λ b → (β ↓ b) +ₒ 𝟙ₒ)) Z ＝⟨ III ⟩
                        extended-sup (λ b → S (F (β ↓ b))) Z       ∎
  where
   I   = ap F (supremum-of-successors-of-initial-segments pt sr β)
   II  = F-sup {⟨ β ⟩} (λ b → (β ↓ b) +ₒ 𝟙ₒ)
   III = ap (λ - → extended-sup - Z) (dfunext fe' (λ b → F-succ (β ↓ b)))

 presentation-by-transfinite-recursion
  : (β : Ordinal 𝓤) → F β ＝ canonical-spec-by-cases S Z β
 presentation-by-transfinite-recursion =
  transfinite-induction-on-OO (λ β → F β ＝ G β) I
   where
    G = canonical-spec-by-cases S Z

    I : (β : Ordinal 𝓤) → ((b : ⟨ β ⟩) → F (β ↓ b) ＝ G (β ↓ b)) → F β ＝ G β
    I β ih = F β                                            ＝⟨ I₁ ⟩
             extended-sup (λ (b : ⟨ β ⟩) → S (F (β ↓ b))) Z ＝⟨ I₂ ⟩
             extended-sup (λ (b : ⟨ β ⟩) → S (G (β ↓ b))) Z ＝⟨ I₃ ⟩
             G β                                            ∎
     where
      I₁ = recursive-equation β
      I₂ = ap (λ - → extended-sup - Z) (dfunext fe' (λ b → ap S (ih b)))
      I₃ = (transfinite-recursion-on-OO-behaviour
             (Ordinal 𝓤)
             (λ β ih → extended-sup (λ b → S (ih b)) Z) β) ⁻¹

uniquely-specified
 : (S : Ordinal 𝓤 → Ordinal 𝓤) (Z : Ordinal 𝓤)
 → is-prop
    (Σ G ꞉ (Ordinal 𝓤 → Ordinal 𝓤) , ((β : Ordinal 𝓤) → G (β +ₒ 𝟙ₒ) ＝ S (G β))
                                   × preserves-suprema-up-to-join G Z)
uniquely-specified {𝓤} S Z (F , F-succ , F-sup) (G , G-succ , G-sup) =
 to-subtype-＝
  (λ H → ×-is-prop
          (Π-is-prop fe' (λ β → the-type-of-ordinals-is-a-set (ua 𝓤) fe'))
          (preserves-suprema-up-to-join-is-prop H Z))
  (dfunext fe' I)
   where
    I : F ∼ G
    I β = F β                           ＝⟨ I₁  ⟩
          canonical-spec-by-cases S Z β ＝⟨ I₂ ⁻¹ ⟩
          G β                           ∎
     where
      open operation-by-cases-framework
      I₁ = presentation-by-transfinite-recursion F S Z F-succ F-sup β
      I₂ = presentation-by-transfinite-recursion G S Z G-succ G-sup β

\end{code}

In case we have a continuous function, we need not consider binary joins with
some ordinal Z since we can take Z ＝ 𝟘ₒ. The following code handles that
special case.

\begin{code}

module operation-by-cases-framework-continuous
        (F : Ordinal 𝓤 → Ordinal 𝓤)
        (S : Ordinal 𝓤 → Ordinal 𝓤)
        (F-succ : (β : Ordinal 𝓤) → F (β +ₒ 𝟙ₒ) ＝ S (F β))
        (F-cont : is-continuous F)
       where

 recursive-equation : (β : Ordinal 𝓤)
                    → F β ＝ sup (λ (b : ⟨ β ⟩) → S (F (β ↓ b)))
 recursive-equation β = F β                             ＝⟨ I ⟩
                        F (sup λ b → (β ↓ b) +ₒ 𝟙ₒ)     ＝⟨ II ⟩
                        sup (F ∘ (λ b → (β ↓ b) +ₒ 𝟙ₒ)) ＝⟨ III ⟩
                        sup (λ b → S (F (β ↓ b)))       ∎
  where
   I   = ap F (supremum-of-successors-of-initial-segments pt sr β)
   II  = F-cont {⟨ β ⟩} (λ b → (β ↓ b) +ₒ 𝟙ₒ)
   III = ap sup (dfunext fe' (λ b → F-succ (β ↓ b)))

uniquely-specified'
 : (S : Ordinal 𝓤 → Ordinal 𝓤)
 → is-prop
    (Σ G ꞉ (Ordinal 𝓤 → Ordinal 𝓤) , ((β : Ordinal 𝓤) → G (β +ₒ 𝟙ₒ) ＝ S (G β))
                                   × is-continuous G)
uniquely-specified' {𝓤} S =
 equiv-to-prop (Σ-cong (λ G → ×-cong (≃-refl _) (I G))) (uniquely-specified S 𝟘ₒ)
  where
   I : (G : Ordinal 𝓤 → Ordinal 𝓤)
     → is-continuous G ≃ preserves-suprema-up-to-join G 𝟘ₒ
   I G = logically-equivalent-props-are-equivalent
          (being-continuous-is-prop G)
          (preserves-suprema-up-to-join-is-prop G 𝟘ₒ)
          (rl-implication (preservation-of-suprema-continuity-equivalence G))
          (lr-implication (preservation-of-suprema-continuity-equivalence G))

\end{code}

We now instantiate the above with addition.
This used to be part of AdditionProperties (since 22 July 2025).

\begin{code}

module addition-by-fixed-ordinal
        (α : Ordinal 𝓤)
       where

 succ-equation : (Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
 succ-equation α⊕_ =
  (β : Ordinal 𝓤) → α⊕ (β +ₒ 𝟙ₒ) ＝ (α⊕ β) +ₒ 𝟙ₒ

 +ₒ-preserves-suprema-up-to-join : preserves-suprema-up-to-join (α +ₒ_) α
 +ₒ-preserves-suprema-up-to-join =
  preserves-suprema-up-to-join-criterion (α +ₒ_) α
   (+ₒ-preserves-inhabited-suprema pt sr α , 𝟘ₒ-right-neutral α)

 +ₒ-is-uniquely-specified'
  : ∃! α⊕_ ꞉ (Ordinal 𝓤 → Ordinal 𝓤) ,
     (succ-equation α⊕_) × (preserves-suprema-up-to-join α⊕_ α)
 +ₒ-is-uniquely-specified' =
  pointed-props-are-singletons
   (α +ₒ_ ,
    +ₒ-commutes-with-successor α ,
    (λ {I} → +ₒ-preserves-suprema-up-to-join))
   (uniquely-specified (_+ₒ 𝟙ₒ) α)

module addition where
 private

  successor-equation : (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
  successor-equation {𝓤} _⊕_ =
   (α : Ordinal 𝓤) → succ-equation α (α ⊕_)
    where
     open addition-by-fixed-ordinal

  suprema-equation : (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
  suprema-equation {𝓤} _⊕_ =
   (α : Ordinal 𝓤) → preserves-suprema-up-to-join (α ⊕_) α

 +ₒ-is-uniquely-specified
  : ∃! _⊕_ ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) ,
     (successor-equation _⊕_) × (suprema-equation _⊕_)
 +ₒ-is-uniquely-specified {𝓤} =
  equiv-to-singleton e (Π-is-singleton fe' +ₒ-is-uniquely-specified')
   where
    open addition-by-fixed-ordinal
    bin-op = Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤
    un-op = Ordinal 𝓤 → Ordinal 𝓤
    e =
     (Σ F ꞉ bin-op , (successor-equation F) × (suprema-equation F)) ≃⟨ I ⟩
     (Σ F ꞉ bin-op ,
       ((α : Ordinal 𝓤) → succ-equation α (F α)
                        × preserves-suprema-up-to-join (F α) α))    ≃⟨ II ⟩
     (Π α ꞉ Ordinal 𝓤 ,
       Σ G ꞉ un-op , succ-equation α G
                        × preserves-suprema-up-to-join G α)         ■
       where
        I  = Σ-cong (λ F → ≃-sym Π×-distr)
        II = ≃-sym ΠΣ-distr-≃

 +ₒ-recursive-equation : (α β : Ordinal 𝓤)
                       → α +ₒ β ＝ extended-sup (λ b → α +ₒ (β ↓ b) +ₒ 𝟙ₒ) α
 +ₒ-recursive-equation α = recursive-equation
  where
   open addition-by-fixed-ordinal
   open operation-by-cases-framework (α +ₒ_) (_+ₒ 𝟙ₒ) α
         (+ₒ-commutes-with-successor α)
         (+ₒ-preserves-suprema-up-to-join α)

\end{code}

We now instantiate the above with multiplication.
This used to be part of MultiplicationProperties (since 11 September 2024,
following a question by Martin Escardo).

\begin{code}

open import Ordinals.MultiplicationProperties ua

module multiplication-by-fixed-ordinal
        (α : Ordinal 𝓤)
       where

 succ-equation : (Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
 succ-equation α⊗_ =
  (β : Ordinal 𝓤) → α⊗ (β +ₒ 𝟙ₒ) ＝ (α⊗ β) +ₒ α

 ×ₒ-is-uniquely-specified'
  : ∃! α⊗_ ꞉ (Ordinal 𝓤 → Ordinal 𝓤) , (succ-equation α⊗_) × (is-continuous α⊗_)
 ×ₒ-is-uniquely-specified' =
  pointed-props-are-singletons
   (α ×ₒ_ , ×ₒ-successor α , (λ {I} → ×ₒ-is-continuous pt sr α))
   (uniquely-specified' (_+ₒ α))

module multiplication where
 private

  successor-equation : (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
  successor-equation {𝓤} _⊗_ =
   (α : Ordinal 𝓤) → succ-equation α (α ⊗_)
    where
     open multiplication-by-fixed-ordinal

  suprema-equation : (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
  suprema-equation {𝓤} _⊗_ = (α : Ordinal 𝓤) → is-continuous (α ⊗_)

 ×ₒ-is-uniquely-specified
  : ∃! _⊗_ ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) ,
     (successor-equation _⊗_) × (suprema-equation _⊗_)
 ×ₒ-is-uniquely-specified {𝓤} =
  equiv-to-singleton e (Π-is-singleton fe' ×ₒ-is-uniquely-specified')
   where
    open multiplication-by-fixed-ordinal
    bin-op = Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤
    un-op = Ordinal 𝓤 → Ordinal 𝓤
    e =
     (Σ F ꞉ bin-op , successor-equation F × suprema-equation F)         ≃⟨ I ⟩
     (Σ F ꞉ bin-op ,
       ((α : Ordinal 𝓤) → succ-equation α (F α) × is-continuous (F α))) ≃⟨ II ⟩
     (Π α ꞉ Ordinal 𝓤 , Σ G ꞉ un-op , succ-equation α G
                                    × is-continuous G)                  ■
       where
        I  = Σ-cong λ F → ≃-sym Π×-distr
        II = ≃-sym ΠΣ-distr-≃

 ×ₒ-recursive-equation : (α β : Ordinal 𝓤)
                       → α ×ₒ β ＝ sup (λ b → α ×ₒ (β ↓ b) +ₒ α)
 ×ₒ-recursive-equation α = recursive-equation
  where
   open operation-by-cases-framework-continuous (α ×ₒ_) (_+ₒ α)
         (×ₒ-successor α)
         (×ₒ-is-continuous pt sr α)

\end{code}

Finally, we apply the above to exponentiation by a fixed (positive) ordinal.
This replaces a previous development as part of the file
Exponentiation.Specification.

\begin{code}

open import Ordinals.Exponentiation.Specification ua pt sr
open import Ordinals.Exponentiation.Supremum ua pt sr

exponentiation-is-uniquely-specified
 : (α : Ordinal 𝓤)
 → is-prop
    (Σ exp ꞉ (Ordinal 𝓤 → Ordinal 𝓤) ,
        (exp-specification-succ α exp)
      × (exp-specification-zero-sup-combined α exp))
exponentiation-is-uniquely-specified α =
 uniquely-specified (_×ₒ α) 𝟙ₒ

^ₒ-is-uniquely-specified
 : (α : Ordinal 𝓤) → 𝟙ₒ ⊴ α
 → ∃! exp ꞉ (Ordinal 𝓤 → Ordinal 𝓤) ,
      (exp-specification-succ α exp)
    × (exp-specification-zero-sup-combined α exp)
^ₒ-is-uniquely-specified α α-nonzero =
 pointed-props-are-singletons
  (α ^ₒ_ ,
   ^ₒ-satisfies-succ-specification α α-nonzero ,
   (λ {I} → ^ₒ-satisfies-zero-sup-combined-specification α))
  (exponentiation-is-uniquely-specified α)

\end{code}