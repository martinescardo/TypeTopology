Martin Escardo 25 May 2013

This is a variation of the MFPS paper
https://doi.org/10.1016/j.entcs.2013.09.010 in which dialogue trees
are Church encoded.

\begin{code}

{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.MFPSAndVariations.Church where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import MLTT.Fin
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Continuity
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.SystemT

\end{code}

We first discuss Church encoding of dialogue trees, denoted by D⋆.
This is motivated by the recursion (or iteration, actually) principle
for D.

\begin{code}

D-rec : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {A : 𝓣 ̇ }
      → (Z → A) → ((Y → A) → X → A) → D X Y Z → A
D-rec η' β' (η z)   = η' z
D-rec η' β' (β φ x) = β' (λ y → D-rec η' β' (φ y)) x

D⋆ : 𝓤 ̇ → 𝓥 ̇ → 𝓦 ̇ → 𝓣 ̇ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
D⋆ X Y Z A = (Z → A) → ((Y → A) → X → A) → A

D⋆-rec : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {A : 𝓣 ̇ }
       → (Z → A) → ((Y → A) → X → A) → D⋆ X Y Z A → A
D⋆-rec η' β' d = d η' β'

η⋆ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {A : 𝓣 ̇ }
   → Z → D⋆ X Y Z A
η⋆ z η' β' = η' z

β⋆ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {A : 𝓣 ̇ }
   → (Y → D⋆ X Y Z A) → X → D⋆ X Y Z A
β⋆ Φ x η' β' = β' (λ y → Φ y η' β') x

church-encode : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {A : 𝓣 ̇ }
              → D X Y Z → D⋆ X Y Z A
church-encode = D-rec η⋆ β⋆

\end{code}

To go back, we need to take A = D X Y Z:

\begin{code}

church-decode : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
              → D⋆ X Y Z (D X Y Z) → D X Y Z
church-decode = D⋆-rec η β

\end{code}

Hereditarily extensional equality on dialogue trees, to avoid the
axiom of function extensionality:

\begin{code}

data _≣_ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } : D X Y Z → D X Y Z → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ where

 ap-η : {z z' : Z}
      → z ＝ z'
      → η z ≣ η z'

 ap-β : {φ φ' : Y → D X Y Z}
        {x x' : X}
      → ((y : Y) → φ y ≣ φ' y)
      → x ＝ x'
      → β φ x ≣ β φ' x'

church-correctness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                     (d : D X Y Z)
                   → church-decode (church-encode d) ≣ d
church-correctness (η z)   = ap-η refl
church-correctness (β φ x) = ap-β (λ y → church-correctness (φ y)) refl

\end{code}

In the following definition we take A = ((X → Y) → Z).

\begin{code}

dialogue⋆ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
          → D⋆ X Y Z ((X → Y) → Z)
          → (X → Y) → Z
dialogue⋆ = D⋆-rec (λ z α → z) (λ φ x α → φ (α x) α)

B⋆ : 𝓦 ̇ → 𝓣 ̇ → 𝓦 ⊔ 𝓣 ̇
B⋆ = D⋆ ℕ ℕ

B↦B⋆ : {X A : Type} → B X → B⋆ X A
B↦B⋆ = church-encode

church-encode-B : {X : 𝓦 ̇ } {A : 𝓣  ̇ }
                → B X → B⋆ X A
church-encode-B = church-encode

dialogues-agreement : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                      (d : D X Y Z)
                      (α : X → Y)
                    → dialogue d α ＝ dialogue⋆ (church-encode d) α
dialogues-agreement (η z)   α = refl
dialogues-agreement (β φ x) α = dialogues-agreement (φ (α x)) α

decode⋆ : {X : 𝓦 ̇ } → Baire → B⋆ X (Baire → X) → X
decode⋆ α d = dialogue⋆ d α

kleisli-extension⋆ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓣 ̇ }
                   → (X → B⋆ Y A)
                   → B⋆ X A
                   → B⋆ Y A
kleisli-extension⋆ f d η' β' = d (λ x → f x η' β') β'

B⋆-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓣 ̇ } → (X → Y) → B⋆ X A → B⋆ Y A
B⋆-functor f = kleisli-extension⋆ (λ x → η⋆ (f x))

B⋆〖_〗 : type → Type → Type
B⋆〖 ι 〗     A = B⋆(〖 ι 〗) A
B⋆〖 σ ⇒ τ 〗 A = B⋆〖 σ 〗 A → B⋆〖 τ 〗 A

Kleisli-extension⋆ : {X A : Type}
                     {σ : type}
                   → (X → B⋆〖 σ 〗 A)
                   → (B⋆ X A → B⋆〖 σ 〗 A)
Kleisli-extension⋆ {X} {A} {ι}     = kleisli-extension⋆
Kleisli-extension⋆ {X} {A} {σ ⇒ τ} =
  λ g d s → Kleisli-extension⋆ {X} {A} {τ} (λ x → g x s) d

generic⋆ : {A : Type} → B⋆ ℕ A → B⋆ ℕ A
generic⋆ = kleisli-extension⋆ (β⋆ η⋆)

zero⋆ : {A : Type} → B⋆ ℕ A
zero⋆ = η⋆ 0

succ⋆ : {A : Type} → B⋆ ℕ A → B⋆ ℕ A
succ⋆ = B⋆-functor succ

rec⋆ : {σ : type}
       {A : Type}
     → (B⋆ ℕ A → B⋆〖 σ 〗 A → B⋆〖 σ 〗 A)
     → B⋆〖 σ 〗 A
     → B⋆ ℕ A → B⋆〖 σ 〗 A
rec⋆ {σ} {A} f x = Kleisli-extension⋆ {ℕ} {A} {σ} (rec (f ∘ η⋆) x)

B⋆【_】 : {n : ℕ} (Γ : Cxt n) (A : Type) → Type
B⋆【 Γ 】 A = (i : Fin _) → B⋆〖 Γ [ i ] 〗 A

⟪⟫⋆ : {A : Type} → B⋆【 〈〉 】 A
⟪⟫⋆ ()

_‚‚⋆_ : {n : ℕ} {Γ : Cxt n} {A : Type} {σ : type}
      → B⋆【 Γ 】 A
      → B⋆〖 σ 〗 A
      → B⋆【 Γ , σ 】 A
(xs ‚‚⋆ x) 𝟎       = x
(xs ‚‚⋆ x) (suc i) = xs i

B⋆⟦_⟧ : {n : ℕ} {Γ : Cxt n} {σ : type} {A : Type}
      → T' Γ σ
      → B⋆【 Γ 】 A
      → B⋆〖 σ 〗 A
B⋆⟦ Ω               ⟧  _ = generic⋆
B⋆⟦ Zero            ⟧  _ = zero⋆
B⋆⟦ Succ            ⟧  _ = succ⋆
B⋆⟦ Rec {_} {_} {σ} ⟧  _ = rec⋆ {σ}
B⋆⟦ ν i             ⟧ xs = xs i
B⋆⟦ ƛ t             ⟧ xs = λ x → B⋆⟦ t ⟧ (xs ‚‚⋆ x)
B⋆⟦ t · u           ⟧ xs = (B⋆⟦ t ⟧ xs) (B⋆⟦ u ⟧ xs)

dialogue-tree⋆ : {A : Type} → T₀ ((ι ⇒ ι) ⇒ ι) → B⋆ ℕ A
dialogue-tree⋆ t = B⋆⟦ (embed t) · Ω ⟧ ⟪⟫⋆

\end{code}
