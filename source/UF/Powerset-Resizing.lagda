Martin Escardo, 2019

Powersets under resizing. More things are available at MGS.Size.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.Size

module UF.Powerset-Resizing
        (fe : Fun-Ext)
        (ρ : Propositional-Resizing)
       where

open import MLTT.Spartan
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.Lower-FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Univalence
open import UF.Powerset
open import UF.PropTrunc
open import UF.SubtypeClassifier

\end{code}

The powerset is closed under unions and intersections under the
assumption of propositional resizing and function extensionality:

\begin{code}

private
 pt : propositional-truncations-exist
 pt = resizing-truncation (λ _ _ → fe) ρ

open PropositionalTruncation pt

closure-under-unions : {X : 𝓤 ̇ } (𝓐 : (X → Ω 𝓥) → Ω 𝓦)
                     → Σ B ꞉ (X → Ω 𝓥)
                           , ((x : X) → (x ∈ B)
                                      ↔ (∃ A ꞉ (X → Ω 𝓥) , (A ∈ 𝓐) × (x ∈ A)))
closure-under-unions {𝓤} {𝓥} {𝓦} {X} 𝓐 = B , (λ x → lr x , rl x)
 where
  β : X → 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦 ̇
  β x = ∃ A ꞉ (X → Ω 𝓥) , (A ∈ 𝓐) × (x ∈ A)

  i : (x : X) → is-prop (β x)
  i x = ∃-is-prop

  B : X → Ω 𝓥
  B x = resize ρ (β x) (i x) ,
        resize-is-prop ρ (β x) (i x)

  lr : (x : X) → x ∈ B → ∃ A ꞉ (X → Ω 𝓥) , (A ∈ 𝓐) × (x ∈ A)
  lr x = from-resize ρ (β x) (i x)

  rl : (x : X) → (∃ A ꞉ (X → Ω 𝓥) , (A ∈ 𝓐) × (x ∈ A)) → x ∈ B
  rl x = to-resize ρ (β x) (i x)


⋃ : {X : 𝓤 ̇ } → ((X → Ω 𝓥) → Ω 𝓦) → (X → Ω 𝓥)
⋃ 𝓐 = pr₁ (closure-under-unions 𝓐)

from-⋃ : {X : 𝓤 ̇ } (𝓐 : ((X → Ω 𝓥) → Ω 𝓦)) (x : X)
       → x ∈ ⋃ 𝓐 → ∃ A ꞉ (X → Ω 𝓥) , (A ∈ 𝓐) × (x ∈ A)
from-⋃ 𝓐 x = lr-implication (pr₂ (closure-under-unions 𝓐) x)

to-⋃ : {X : 𝓤 ̇ } (𝓐 : ((X → Ω 𝓥) → Ω 𝓦)) (x : X)
     → (∃ A ꞉ (X → Ω 𝓥) , (A ∈ 𝓐) × (x ∈ A)) → x ∈ ⋃ 𝓐
to-⋃ 𝓐 x = rl-implication (pr₂ (closure-under-unions 𝓐) x)

closure-under-intersections : {X : 𝓤 ̇ } (𝓐 : (X → Ω 𝓥) → Ω 𝓦)
                            → Σ B ꞉ (X → Ω 𝓥)
                                  , ((x : X) → x ∈ B
                                             ↔ ((A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A))
closure-under-intersections {𝓤} {𝓥} {𝓦} {X} 𝓐 = B , (λ x → lr x , rl x)
 where
  β : X → 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦 ̇
  β x = (A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A

  i : (x : X) → is-prop (β x)
  i x = Π₂-is-prop fe (λ A _ → ∈-is-prop A x)

  B : X → Ω 𝓥
  B x = resize ρ (β x) (i x) ,
        resize-is-prop ρ (β x) (i x)

  lr : (x : X) → x ∈ B → (A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A
  lr x = from-resize ρ (β x) (i x)

  rl : (x : X) → ((A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A) → x ∈ B
  rl x = to-resize ρ (β x) (i x)

⋂ : {X : 𝓤 ̇ } → ((X → Ω 𝓥) → Ω 𝓦) → (X → Ω 𝓥)
⋂ 𝓐 = pr₁ (closure-under-intersections 𝓐)

from-⋂ : {X : 𝓤 ̇ } (𝓐 : ((X → Ω 𝓥) → Ω 𝓦)) (x : X)
       → x ∈ ⋂ 𝓐 → (A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A
from-⋂ 𝓐 x = lr-implication (pr₂ (closure-under-intersections 𝓐) x)

to-⋂ : {X : 𝓤 ̇ } (𝓐 : ((X → Ω 𝓥) → Ω 𝓦)) (x : X)
     → ((A : X → Ω 𝓥) → A ∈ 𝓐 → x ∈ A) → x ∈ ⋂ 𝓐
to-⋂ 𝓐 x = rl-implication (pr₂ (closure-under-intersections 𝓐) x)

\end{code}
