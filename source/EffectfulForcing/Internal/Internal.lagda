Martin Escardo 25 May 2013

This is an extension of The MFPS paper
https://doi.org/10.1016/j.entcs.2013.09.010 in which dialogue trees
are constructed internally in system T, rather than externally in
Agda, using Church encoding of trees (as system T doesn't directly
support trees). We work with the lambda-calculus version of the MFPS
paper.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.Internal.Internal where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import MLTT.Athenian using (Fin)
open import UF.Base
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Continuity
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.SystemT using (type ; ι ; _⇒_ ; 〖_〗)
open import EffectfulForcing.MFPSAndVariations.Church hiding (B⋆【_】 ; ⟪⟫⋆ ; _‚‚⋆_ ; B⋆⟦_⟧ ; dialogue-tree⋆)
open import EffectfulForcing.Internal.SystemT

open Fin

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

TODO. Formulate and prove the correctness of ⌜dialogue-tree⌝. We'll do this in another file.

Given a term t of type (ι ⇒ ι) ⇒ ι, we calculate a term defining a
modulus of continuity for t.

\begin{code}

max' : ℕ → ℕ → ℕ
max' 0        n        = n
max' (succ m) 0        = succ m
max' (succ m) (succ n) = succ (max' m n)

max : ℕ → ℕ → ℕ
max = rec (λ (m : ℕ) (f : ℕ → ℕ) → rec (λ (n : ℕ) _ → succ (f n)) (succ m)) (λ n → n)

max-agreement : (m n : ℕ) → max m n ＝ max' m n
max-agreement 0        n        = refl
max-agreement (succ m) 0        = refl
max-agreement (succ m) (succ n) = ap succ (max-agreement m n)

maxᵀ : {Γ : Cxt} → T Γ (ι ⇒ ι ⇒ ι)
maxᵀ = Rec' · ƛ (ƛ (Rec' · ƛ (ƛ (Succ (ν₂ · ν₁))) · (Succ ν₁))) · ƛ ν₀

maxᵀ-meaning : ⟦ maxᵀ ⟧₀ ＝ max
maxᵀ-meaning = refl

\end{code}

A modulus of continuity can be calculated from a dialogue tree.

\begin{code}

max-question-in-path : {Γ : Cxt}
                     → T (B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι))
                         ((⌜B⌝ ι ((ι ⇒ ι) ⇒ ι)) ⇒ (ι ⇒ ι) ⇒ ι)
max-question-in-path =
 ƛ (ν₀ · ƛ (ƛ Zero) · ƛ (ƛ (ƛ (maxᵀ · (Succ ν₁) · (ν₂ · (ν₀ · ν₁) · ν₀)))))

max-question-in-path-meaning-η :

 ∀ n α → ⟦ max-question-in-path ⟧₀ (⟦ ⌜η⌝ ⟧₀ n) α ＝ 0

max-question-in-path-meaning-η n α = refl

max-question-in-path-meaning-β :

 ∀ φ n α → ⟦ max-question-in-path ⟧₀ (⟦ ⌜β⌝ ⟧₀ φ n) α
        ＝ max (succ n) (⟦ max-question-in-path ⟧₀ (φ (α n)) α)

max-question-in-path-meaning-β φ n α = refl

internal-mod-cont : {Γ : Cxt}
                  → T Γ ((ι ⇒ ι) ⇒ ι)
                  → T (B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι)) ((ι ⇒ ι) ⇒ ι)
internal-mod-cont t = max-question-in-path · (⌜dialogue-tree⌝ {(ι ⇒ ι) ⇒ ι} t)

internal-mod-cont₀ : T₀ ((ι ⇒ ι) ⇒ ι) → T₀ ((ι ⇒ ι) ⇒ ι)
internal-mod-cont₀ = internal-mod-cont

external-mod-cont : T₀ ((ι ⇒ ι) ⇒ ι) → (ℕ → ℕ) → ℕ
external-mod-cont t = ⟦ internal-mod-cont₀ t ⟧₀

\end{code}

TODO. Prove the correctness of the internal modulus of continuity.

Examples to be compared with those of the lambda-calculus version of
the MFPS paper file.

\begin{code}

module examples2 where

 m₁ : (ℕ → ℕ) → ℕ
 m₁ = external-mod-cont (ƛ (ν₀ · numeral 17))

 m₁-explicitly : m₁ ＝ λ α → 18
 m₁-explicitly = refl

 example₁ : m₁ id ＝ 18
 example₁ = refl

 example₁' : m₁ (λ i → 0) ＝ 18
 example₁' = refl

 f₂ : T₀ ((ι ⇒ ι) ⇒ ι)
 f₂ = ƛ (ν₀ · (ν₀ · numeral 17))

 f₂-meaning : ⟦ f₂ ⟧₀ ＝ λ α → α (α 17)
 f₂-meaning = refl

 m₂ : (ℕ → ℕ) → ℕ
 m₂ = external-mod-cont (ƛ (ν₀ · (ν₀ · numeral 17)))

 m₂-explicitly : m₂ ＝ λ α → succ (max 17 (α 17))
 m₂-explicitly = refl

\end{code}

This is what m₂ evaluates to with Agda normalization:

\begin{code}

 m₂-explicitly' : m₂ ＝
   λ α → succ (rec (λ x₁ x₂ → succ (rec (λ x₃ x₄ → succ (rec (λ x₅ x₆
  → succ (rec (λ x₇ x₈ → succ (rec (λ x₉ x₁₀ → succ (rec (λ x₁₁ x₁₂ →
  succ (rec (λ x₁₃ x₁₄ → succ (rec (λ x₁₅ x₁₆ → succ (rec (λ x₁₇ x₁₈ →
  succ (rec (λ x₁₉ x₂₀ → succ (rec (λ x₂₁ x₂₂ → succ (rec (λ x₂₃ x₂₄ →
  succ (rec (λ x₂₅ x₂₆ → succ (rec (λ x₂₇ x₂₈ → succ (rec (λ x₂₉ x₃₀ →
  succ (rec (λ x₃₁ x₃₂ → succ (rec (λ x₃₃ x₃₄ → succ x₃₃) 1 x₃₁)) 2
  x₂₉)) 3 x₂₇)) 4 x₂₅)) 5 x₂₃)) 6 x₂₁)) 7 x₁₉)) 8 x₁₇)) 9 x₁₅)) 10
  x₁₃)) 11 x₁₁)) 12 x₉)) 13 x₇)) 14 x₅)) 15 x₃)) 16 x₁)) 17 (α 17))
 m₂-explicitly' = refl

 example₂ : m₂ succ ＝ 19
 example₂ = refl

 example₂' : m₂ (λ i → 0) ＝ 18
 example₂' = refl

 example₂'''' : m₂ (λ i → 1000) ＝ 1001
 example₂'''' = refl

 example₂'' : m₂ id ＝ 18
 example₂'' = refl

 example₂''' : m₂ (succ ∘ succ) ＝ 20
 example₂''' = refl

 Add : {Γ : Cxt} → T Γ (ι ⇒ ι ⇒ ι)
 Add = Rec' · ƛ Succ'

 t₃ : T₀ ((ι ⇒ ι) ⇒ ι)
 t₃ = ƛ (ν₀ · (ν₀ · (Add · (ν₀ · numeral 17) · (ν₀ · numeral 34))))

 add : ℕ → ℕ → ℕ
 add = rec (λ _ → succ)

 t₃-meaning : ⟦ t₃ ⟧₀ ＝ λ α → α (α (add (α 17) (α 34)))
 t₃-meaning = refl

 m₃ : (ℕ → ℕ) → ℕ
 m₃ = external-mod-cont t₃

{- This takes a long time to type check:
 m₃-explicitly : m₃ ＝ λ α →
   rec (λ x x₁ → succ (rec (λ x₂ x₃ → succ (rec (λ x₄ x₅ → succ (rec (λ x₆
   x₇ → succ (rec (λ x₈ x₉ → succ (rec (λ x₁₀ x₁₁ → succ (rec (λ
   x₁₂ x₁₃ → succ (rec (λ x₁₄ x₁₅ → succ (rec (λ x₁₆ x₁₇ → succ
   (rec (λ x₁₈ x₁₉ → succ (rec (λ x₂₀ x₂₁ → succ (rec (λ x₂₂ x₂₃ →
   succ (rec (λ x₂₄ x₂₅ → succ (rec (λ x₂₆ x₂₇ → succ (rec (λ x₂₈
   x₂₉ → succ (rec (λ x₃₀ x₃₁ → succ (rec (λ x₃₂ x₃₃ → succ (rec (λ
   x₃₄ x₃₅ → succ (rec (λ x₃₆ x₃₇ → succ (rec (λ x₃₈ x₃₉ → succ
   (rec (λ x₄₀ x₄₁ → succ (rec (λ x₄₂ x₄₃ → succ (rec (λ x₄₄ x₄₅ →
   succ (rec (λ x₄₆ x₄₇ → succ (rec (λ x₄₈ x₄₉ → succ (rec (λ x₅₀
   x₅₁ → succ (rec (λ x₅₂ x₅₃ → succ (rec (λ x₅₄ x₅₅ → succ (rec (λ
   x₅₆ x₅₇ → succ (rec (λ x₅₈ x₅₉ → succ (rec (λ x₆₀ x₆₁ → succ
   (rec (λ x₆₂ x₆₃ → succ (rec (λ x₆₄ x₆₅ → succ (rec (λ x₆₆ x₆₇ →
   succ x₆₆) 1 x₆₄)) 2 x₆₂)) 3 x₆₀)) 4 x₅₈)) 5 x₅₆)) 6 x₅₄)) 7
   x₅₂)) 8 x₅₀)) 9 x₄₈)) 10 x₄₆)) 11 x₄₄)) 12 x₄₂)) 13 x₄₀)) 14
   x₃₈)) 15 x₃₆)) 16 x₃₄)) 17 x₃₂)) 18 x₃₀)) 19 x₂₈)) 20 x₂₆)) 21
   x₂₄)) 22 x₂₂)) 23 x₂₀)) 24 x₁₈)) 25 x₁₆)) 26 x₁₄)) 27 x₁₂)) 28
   x₁₀)) 29 x₈)) 30 x₆)) 31 x₄)) 32 x₂)) 33 x)) 34 (rec (λ x x₁ x₂
   x₃ → x₁ (λ x₄ → x₂ (succ x₄)) x₃) (λ x x₁ → x₁ (λ x₂ → x x₂) 17)
   (α 34) (λ x x₁ → rec (λ x₂ x₃ → rec (λ x₄ x₅ → succ (x₃ x₄))
   (succ x₂)) (λ x₂ → x₂) x (rec (λ x₂ x₃ → rec (λ x₄ x₅ → succ (x₃
   x₄)) (succ x₂)) (λ x₂ → x₂) (x₁ x) 0)) (λ x x₁ x₂ → rec (λ x₃ x₄
   → rec (λ x₅ x₆ → succ (x₄ x₅)) (succ x₃)) (λ x₃ → x₃) x₁ (x (x₂
   x₁) x₂)) α)
 m₃-explicitly = refl
-}

 example₃ : m₃ succ ＝ 55
 example₃ = refl

 example₃' : m₃ id ＝ 52
 example₃' = refl

 example₃'' : m₃ (λ i → 0) ＝ 35
 example₃'' = refl

 example₃''' : m₃ (λ i → 300) ＝ 601
 example₃''' = refl

 example₃'''' : m₃ (λ i → add i i) ＝ 205
 example₃'''' = refl

 f : T₀ ((ι ⇒ ι) ⇒ ι)
 f = ƛ (ν₀ · (ν₀ · (ν₀ · numeral 17)))

 m₄ : (ℕ → ℕ) → ℕ
 m₄ = external-mod-cont f

 example₄ : m₄ id ＝ 18
 example₄ = refl

 example₄' : m₄ (λ i → 0) ＝ 18
 example₄' = refl

 example₄'' : m₄ succ ＝ 20
 example₄'' = refl

 example₄''' : m₄ (λ i → add i i) ＝ 69
 example₄''' = refl

 example₄'''' : ⟦ f ⟧₀ (λ i → add i i) ＝ 136
 example₄'''' = refl

\end{code}
