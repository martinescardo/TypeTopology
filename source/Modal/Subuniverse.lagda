Jon Sterling, started 27th Sep 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Modal.Subuniverse where

open import MLTT.Spartan
open import UF.Subsingletons
open import UF.Equiv

subuniverse
  : (𝓤 𝓥 : Universe)
  → (𝓤 ⊔ 𝓥)⁺ ̇
subuniverse 𝓤 𝓥 =
  Σ P ꞉ (𝓤 ̇ → 𝓥 ̇) ,
  Π A ꞉ 𝓤 ̇ ,
  is-prop (P A)

subuniverse-contains
  : subuniverse 𝓤 𝓥
  → 𝓤 ̇
  → 𝓥 ̇
subuniverse-contains P A =
  pr₁ P A

subuniverse-member
  : subuniverse 𝓤 𝓥
  → 𝓤 ⁺ ⊔ 𝓥  ̇
subuniverse-member P =
  Σ (subuniverse-contains P)

reflection-candidate
  : subuniverse 𝓤 𝓥
  → 𝓤 ̇
  → 𝓤 ⁺ ⊔ 𝓥  ̇
reflection-candidate P A =
  Σ A' ꞉ subuniverse-member P ,
  (A → pr₁ A')

is-reflection
  : (P : subuniverse 𝓤 𝓥)
  → (A : 𝓤 ̇)
  → reflection-candidate P A
  → 𝓤 ⁺ ⊔ 𝓥  ̇
is-reflection P A (A' , η) =
  Π B ꞉ subuniverse-member P ,
  is-equiv λ (f : pr₁ A' → pr₁ B) → f ∘ η

subuniverse-reflects
  : subuniverse 𝓤 𝓥
  → 𝓤 ̇
  → 𝓤 ⁺ ⊔ 𝓥  ̇
subuniverse-reflects {𝓤 = 𝓤} P A =
  Σ A' ꞉ reflection-candidate P A ,
  is-reflection P A A'

subuniverse-is-reflective
  : subuniverse 𝓤 𝓥
  → 𝓤 ⁺ ⊔ 𝓥  ̇
subuniverse-is-reflective P =
  Π (subuniverse-reflects P)



module ReflectiveSubuniverse (P : subuniverse 𝓤 𝓥) (P-is-reflective : subuniverse-is-reflective P) where
  Type○ = subuniverse-member P

  ○ : 𝓤 ̇ → 𝓤 ̇
  ○ A = pr₁ (pr₁ (pr₁ (P-is-reflective A)))

  ○-in-subuniverse : (A : 𝓤 ̇) → subuniverse-contains P (○ A)
  ○-in-subuniverse A = pr₂ (pr₁ (pr₁ (P-is-reflective A)))

  η : {A : 𝓤 ̇} → A → ○ A
  η {A = A} = pr₂ (pr₁ (P-is-reflective A))

  reflective-subuniverse-closed-under-products
    : (A : 𝓤 ̇)
    → (B : A → 𝓤 ̇)
    → (B-in-P : Π x ꞉ A , subuniverse-contains P (B x))
    → subuniverse-contains P (Π B)
  reflective-subuniverse-closed-under-products A B B-in-P =
    {!!}
    where
      h : ○ (Π B) → Π B
      h = {!!}

\end{code}
