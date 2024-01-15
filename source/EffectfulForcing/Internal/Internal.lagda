Martin Escardo, Bruno da Rocha Paiva, Ayberk Tosun, and Vincent Rahli, June 2023

This ports EffectfulForcing.MFPSAndVariations.Internal to a new version of system T.

We define a translation of system T into itself that assigns dialogue
trees, with Church encoding, to functions of type (ι → ι) → ι.


\begin{code}

{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.Internal.Internal where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.SystemT using (type ; ι ; _⇒_ ; 〖_〗)
open import EffectfulForcing.MFPSAndVariations.Church hiding (B⋆【_】 ; ⟪⟫⋆ ; _‚‚⋆_ ; B⋆⟦_⟧ ; dialogue-tree⋆)
open import EffectfulForcing.Internal.SystemT

\end{code}

\begin{code}

B⋆【_】 : (Γ : Cxt) (A : Type) → Type
B⋆【 Γ 】 A = {σ : type} (i : ∈Cxt σ Γ) → B⋆〖 σ 〗 A

⟪⟫⋆ : {A : Type} → B⋆【 〈〉 】 A
⟪⟫⋆ ()

_‚‚⋆_ : {Γ : Cxt} {A : Type} {σ : type}
      → B⋆【 Γ 】 A
      → B⋆〖 σ 〗 A
      → B⋆【 Γ ,, σ 】 A
(xs ‚‚⋆ x) {σ} (∈Cxt0 _) = x
(xs ‚‚⋆ x) {σ} (∈CxtS _ i) = xs i

B⋆⟦_⟧ : {Γ : Cxt} {σ : type} {A : Type}
      → T' Γ σ
      → B⋆【 Γ 】 A
      → B⋆〖 σ 〗 A
B⋆⟦ Ω         ⟧  _ = generic⋆
B⋆⟦ Zero      ⟧  _ = zero⋆
B⋆⟦ Succ t    ⟧ xs = succ⋆ (B⋆⟦ t ⟧ xs)
B⋆⟦ Rec f g t ⟧ xs = rec⋆ (B⋆⟦ f ⟧ xs) (B⋆⟦ g ⟧ xs) (B⋆⟦ t ⟧ xs)
B⋆⟦ ν i       ⟧ xs = xs i
B⋆⟦ ƛ t       ⟧ xs = λ x → B⋆⟦ t ⟧ (xs ‚‚⋆ x)
B⋆⟦ t · u     ⟧ xs = (B⋆⟦ t ⟧ xs) (B⋆⟦ u ⟧ xs)

dialogue-tree⋆ : {A : Type} → T₀ ((ι ⇒ ι) ⇒ ι) → B⋆ ℕ A
dialogue-tree⋆ t = B⋆⟦ (embed t) · Ω ⟧ ⟪⟫⋆

\end{code}

We know internalize the above to system T.

\begin{code}

⌜D⋆⌝ : type → type → type → type → type
⌜D⋆⌝ X Y Z A = (Z ⇒ A) ⇒ ((Y ⇒ A) ⇒ X ⇒ A) ⇒ A

⌜η⌝ : {X Y Z A : type} {Γ : Cxt}
    → T Γ (Z ⇒ ⌜D⋆⌝ X Y Z A)
⌜η⌝ = ƛ (ƛ (ƛ (ν₁ · ν₂)))

η-meaning : {X Y Z A : type} → ⟦ ⌜η⌝ {X} {Y} {Z} {A} ⟧₀ ＝ η⋆
η-meaning = refl

⌜β⌝ : {X Y Z A : type} {Γ : Cxt}
    → T Γ (((Y ⇒ ⌜D⋆⌝ X Y Z A) ⇒ X ⇒ ⌜D⋆⌝ X Y Z A))
⌜β⌝ = ƛ (ƛ (ƛ (ƛ (ν₀ · ƛ (ν₄ · ν₀ · ν₂ · ν₁) · ν₂))))

β-meaning : {X Y Z A : type} → ⟦ ⌜β⌝ {X} {Y} {Z} {A} ⟧₀ ＝ β⋆
β-meaning = refl

⌜B⌝ : type → type → type
⌜B⌝ = ⌜D⋆⌝ ι ι

⌜kleisli-extension⌝ : {X Y A : type} {Γ : Cxt}
                    → T Γ ((X ⇒ ⌜B⌝ Y A) ⇒ ⌜B⌝ X A ⇒ ⌜B⌝ Y A)
⌜kleisli-extension⌝ = ƛ (ƛ (ƛ (ƛ (ν₂ · ƛ (ν₄ · ν₀ · ν₂ · ν₁) · ν₀))))

kleisli-extension-meaning : {X Y A : type}
                          → ⟦ ⌜kleisli-extension⌝ {X} {Y} {A} ⟧₀
                          ＝ kleisli-extension⋆
kleisli-extension-meaning = refl

⌜B-functor⌝ : {X Y A : type} {Γ : Cxt}
            → T Γ ((X ⇒ Y) ⇒ ⌜B⌝ X A ⇒ ⌜B⌝ Y A)
⌜B-functor⌝ = ƛ (⌜kleisli-extension⌝ · ƛ (⌜η⌝ · (ν₁ · ν₀)))

B-functor-meaning : {X Y A : type}
                  → ⟦ ⌜B-functor⌝ {X} {Y} {A} ⟧₀
                  ＝ B⋆-functor
B-functor-meaning = refl

⌜star⌝ : {X Y A : type} {Γ : Cxt}
       → T Γ ((⌜B⌝ (X ⇒ Y) A) ⇒ ⌜B⌝ X A ⇒ ⌜B⌝ Y A)
⌜star⌝ =
 ƛ (ƛ (⌜kleisli-extension⌝
       · ƛ (⌜B-functor⌝
            · ƛ (ν₀ · ν₁)
            · ν₂)
       · ν₀))

-- λη.λβ.t (λs.f (λg.η(g s)) β) β
⌜app⌝ : {A : type} {σ τ : type} {Γ : Cxt}
       (f : T Γ (⌜B⌝ (σ ⇒ τ) A)) (t : T Γ (⌜B⌝ σ A)) → T Γ (⌜B⌝ τ A)
⌜app⌝ {A} {σ} {τ} {Γ} f t = ⌜star⌝ · f · t

B-type〖_〗 : type → type → type
B-type〖 ι 〗 A     = ⌜B⌝ ι A
B-type〖 σ ⇒ τ 〗 A = B-type〖 σ 〗 A ⇒ B-type〖 τ 〗 A

⌜Kleisli-extension⌝ : {X A : type} {σ : type} {Γ : Cxt}
                    → T Γ ((X ⇒ B-type〖 σ 〗 A) ⇒ ⌜B⌝ X A ⇒ B-type〖 σ 〗 A)
⌜Kleisli-extension⌝ {X} {A} {ι}     = ⌜kleisli-extension⌝
⌜Kleisli-extension⌝ {X} {A} {σ ⇒ τ} =
  ƛ (ƛ (ƛ (⌜Kleisli-extension⌝ {X} {A} {τ} · ƛ (ν₃ · ν₀ · ν₁) · ν₁)))

Kleisli-extension-meaning : {X A : type} {σ τ : type}
                          → ⟦ ⌜Kleisli-extension⌝ {X} {A} {σ ⇒ τ}⟧₀
                          ＝ λ g d s → ⟦ ⌜Kleisli-extension⌝ {X} {A} {τ} ⟧
                                       (⟨⟩ ‚ g ‚ d ‚ s)
                                       (λ x → g x s)
                                       d
Kleisli-extension-meaning = refl

⌜zero⌝ : {A : type} {Γ : Cxt} → T Γ (⌜B⌝ ι A)
⌜zero⌝ = ⌜η⌝ · Zero

⌜succ⌝ : {A : type} {Γ : Cxt} → T Γ (⌜B⌝ ι A ⇒ ⌜B⌝ ι A)
⌜succ⌝ =  ⌜B-functor⌝ · Succ'

⌜rec⌝ : {σ A : type} {Γ : Cxt}
      → T Γ ((⌜B⌝ ι A
               ⇒ B-type〖 σ 〗 A
               ⇒ B-type〖 σ 〗 A)
            ⇒ B-type〖 σ 〗 A
            ⇒ ⌜B⌝ ι A
            ⇒ B-type〖 σ 〗 A)
⌜rec⌝ {σ} {A} = ƛ (ƛ (⌜Kleisli-extension⌝ {ι} {A} {σ}
                        · (Rec' · (ƛ (ν₂ · (⌜η⌝ · ν₀))) · ν₀)))

rec-meaning : {σ A : type}
            → ⟦ ⌜rec⌝ {σ} {A} ⟧₀
            ＝ λ f x → ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ} ⟧
                        (⟨⟩ ‚ f ‚ x)
                        (rec (f ∘ ⟦ ⌜η⌝ {ι} {ι} {ι} {A} ⟧₀) x)
rec-meaning = refl

B-context【_】 : Cxt → type → Cxt
B-context【_】 〈〉       A = 〈〉
B-context【_】 (Γ ,, σ) A = B-context【_】 Γ A ,, B-type〖 σ 〗 A

infix 10 B-context【_】

∈Cxt-B-type : {Γ : Cxt} {A : type} {σ : type} (i : ∈Cxt σ Γ) → ∈Cxt (B-type〖 σ 〗 A) (B-context【 Γ 】 A)
∈Cxt-B-type {Γ ,, σ} {A} {σ} (∈Cxt0 Γ) = ∈Cxt0 (B-context【 Γ 】 A)
∈Cxt-B-type {Γ ,, τ} {A} {σ} (∈CxtS τ i) = ∈CxtS (B-type〖 τ 〗 A) (∈Cxt-B-type i)

⌜ν⌝ : {Γ : Cxt} {A : type} {σ : type} (i : ∈Cxt σ Γ)
    → T (B-context【 Γ 】 A) (B-type〖 σ 〗 A)
⌜ν⌝ {Γ} {A} {σ} i = ν (∈Cxt-B-type i)

\end{code}

(Compositional) translation of terms:

\begin{code}

⌜_⌝ : {Γ : Cxt} {σ : type} {A : type}
    → T Γ σ
    → T (B-context【 Γ 】 A) (B-type〖 σ 〗 A)
⌜ Zero ⌝      = ⌜zero⌝
⌜ Succ t ⌝    = ⌜succ⌝ · ⌜ t ⌝
⌜ Rec f g t ⌝ = ⌜rec⌝ · ⌜ f ⌝ · ⌜ g ⌝ · ⌜ t ⌝
⌜ ν i ⌝       = ⌜ν⌝ i
⌜ ƛ t ⌝       = ƛ ⌜ t ⌝
⌜ t · u ⌝     = ⌜ t ⌝ · ⌜ u ⌝

\end{code}

Given a term of type (ι ⇒ ι) ⇒ ι, we calculate a term defining its dialogue tree.

\begin{code}

⌜generic⌝ : {A : type} {Γ : Cxt}
          → T Γ (⌜B⌝ ι A ⇒ ⌜B⌝ ι A)
⌜generic⌝ = ⌜kleisli-extension⌝ · (⌜β⌝ · ⌜η⌝)

⌜dialogue-tree⌝ : {A : type} {Γ : Cxt}
                → T Γ ((ι ⇒ ι) ⇒ ι)
                → T (B-context【 Γ 】 A) (⌜B⌝ ι A)
⌜dialogue-tree⌝ t = ⌜ t ⌝ · ⌜generic⌝

\end{code}
