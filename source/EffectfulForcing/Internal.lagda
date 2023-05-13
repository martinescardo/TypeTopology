Martin Escardo 25 May 2013

This is an extension of The MFPS paper
https://doi.org/10.1016/j.entcs.2013.09.010 in which dialogue trees
are constructed internally in system T, rather than externally in
Agda, using Church encoding of trees (as system T doesn't directly
support trees). We work with the lambda-calculus version of the MFPS
paper.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.Internal where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import MLTT.Athenian using (Fin)
open import UF.Base
open import EffectfulForcing.Combinators
open import EffectfulForcing.Continuity
open import EffectfulForcing.Dialogue
open import EffectfulForcing.SystemT
open import EffectfulForcing.LambdaCalculusVersionOfMFPS

open Fin

\end{code}

We now internalize this to system T, using Church encoding of dialogue
trees in system T.  (Of course, we need some encoding of dialogue
trees, because T cannot directly define dialogue trees in its
impoverished type system.)

We first briefly discuss Church encoding of dialogue trees, denoted by
D⋆. This is motivated by the recursion (or iteration, actually)
principle for D:

\begin{code}

D-rec : {X Y Z A : Type} → (Z → A) → ((Y → A) → X → A) → D X Y Z → A
D-rec |η| |β| (η z) = |η| z
D-rec |η| |β| (β φ x) = |β| (λ y → D-rec |η| |β| (φ y)) x

D⋆ : Type → Type → Type → Type → Type
D⋆ X Y Z A = (Z → A) → ((Y → A) → X → A) → A

D⋆-rec : {X Y Z A : Type} → (Z → A) → ((Y → A) → X → A) → D⋆ X Y Z A → A
D⋆-rec |η| |β| d = d |η| |β|

η⋆ : {X Y Z A : Type} → Z → D⋆ X Y Z A
η⋆ z |η| |β| = |η| z

β⋆ : {X Y Z A : Type} → (Y → D⋆ X Y Z A) → X → D⋆ X Y Z A
β⋆ Φ x |η| |β| = |β| (λ y → Φ y |η| |β|) x

church-encode : {X Y Z A : Type} → D X Y Z → D⋆ X Y Z A
church-encode = D-rec η⋆ β⋆

church-encode-bis : {X Y Z A : Type} → D X Y Z → D⋆ X Y Z A
church-encode-bis (η z) = η⋆ z
church-encode-bis (β φ x) = β⋆ (λ i → church-encode-bis(φ i)) x

\end{code}

To go back, we need A = D X Y Z:

\begin{code}

church-decode : {X Y Z : Type} → D⋆ X Y Z (D X Y Z) → D X Y Z
church-decode = D⋆-rec η β

\end{code}

Extensional equality on dialogue trees (to avoid the axiom of function
extensionality):

\begin{code}

data _≣_ {X Y Z : Type} : D X Y Z → D X Y Z → Type where

 congη : {z z' : Z}
       → z ＝ z'
       → η z ≣ η z'

 congβ : {φ φ' : Y → D X Y Z}
         {x x' : X}
       → ((y : Y) → φ y ≣ φ' y)
       → x ＝ x'
       → β φ x ≣ β φ' x'

church-correctness : {X Y Z : Type}
                     (d : D X Y Z)
                   → church-decode (church-encode d) ≣ d
church-correctness (η z)   = congη refl
church-correctness (β φ x) = congβ (λ y → church-correctness (φ y)) refl

\end{code}

Using relational parametricity, we have the meta-theorem that
church-encode(church-decode d⋆) is provable for each closed term
d⋆. But we will be able to do better than that in our situation.

\begin{code}

dialogue⋆ : {X Y Z : Type} → D⋆ X Y Z ((X → Y) → Z) → (X → Y) → Z
dialogue⋆ = D⋆-rec (λ z α → z) (λ φ x α → φ (α x) α)

B⋆ : Type → Type → Type
B⋆ = D⋆ ℕ ℕ

church-encode-B : {A X : Type} → B X → B⋆ X A
church-encode-B = church-encode

dialogues-agreement : {X Y Z : Type}
                      (d : D X Y Z)
                      (α : X → Y)
                    → dialogue d α ＝ dialogue⋆ (church-encode d) α
dialogues-agreement (η z)   α = refl
dialogues-agreement (β φ x) α = dialogues-agreement (φ (α x)) α

decode⋆ : {X : Type} → Baire → B⋆ X (Baire → X) → X
decode⋆ α d = dialogue⋆ d α

kleisli-extension⋆ : {X Y A : Type} → (X → B⋆ Y A) → B⋆ X A → B⋆ Y A
kleisli-extension⋆ f d η⋆ β⋆ = d (λ x → f x η⋆ β⋆) β⋆

B⋆-functor : {X Y A : Type} → (X → Y) → B⋆ X A → B⋆ Y A
B⋆-functor f = kleisli-extension⋆(λ x → η⋆(f x))

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

B↦B⋆ : {X A : Type} → B X → B⋆ X A
B↦B⋆ = church-encode

\end{code}

Some shorthands to simplify the following definitions:

\begin{code}

ν₀ : {n : ℕ} {Γ : Cxt(succ n)} → T Γ (Γ [ 𝟎 ])
ν₀ = ν 𝟎

ν₁ : {n : ℕ} {Γ : Cxt(succ (succ n))} → T Γ (Γ [ suc 𝟎 ])
ν₁ = ν (suc 𝟎)

ν₂ : {n : ℕ} {Γ : Cxt(succ (succ (succ n)))}
   → T Γ (Γ [ suc (suc 𝟎) ])
ν₂ = ν (suc (suc 𝟎))

ν₃ : {n : ℕ} {Γ : Cxt(succ (succ (succ (succ n))))}
   → T Γ (Γ [ suc (suc (suc 𝟎)) ])
ν₃ = ν (suc (suc (suc 𝟎)))

ν₄ : {n : ℕ} {Γ : Cxt(succ (succ (succ (succ (succ n)))))}
   → T Γ (Γ [ suc (suc (suc (suc 𝟎))) ])
ν₄ = ν (suc (suc (suc (suc 𝟎))))

⌜D⋆⌝ : type → type → type → type → type
⌜D⋆⌝ X Y Z A = (Z ⇒ A) ⇒ ((Y ⇒ A) ⇒ X ⇒ A) ⇒ A

⌜η⌝ : {X Y Z A : type} {n : ℕ} {Γ : Cxt n}
    → T Γ (Z ⇒ ⌜D⋆⌝ X Y Z A)
⌜η⌝ = ƛ (ƛ (ƛ (ν₁ · ν₂)))

η-behaviour : {X Y Z A : type} → ⟦ ⌜η⌝ {X} {Y} {Z} {A} ⟧₀ ＝ η⋆
η-behaviour = refl

⌜β⌝ : {X Y Z A : type} {n : ℕ} {Γ : Cxt n}
    → T Γ (((Y ⇒ ⌜D⋆⌝ X Y Z A) ⇒ X ⇒ ⌜D⋆⌝ X Y Z A))
⌜β⌝ = ƛ (ƛ (ƛ (ƛ (ν₀ · ƛ(ν₄ · ν₀ · ν₂ · ν₁) · ν₂))))

β-behaviour : {X Y Z A : type} → ⟦ ⌜β⌝ {X} {Y} {Z} {A} ⟧₀ ＝ β⋆
β-behaviour = refl

⌜B⌝ : type → type → type
⌜B⌝ = ⌜D⋆⌝ ι ι

⌜kleisli-extension⌝ : {X Y A : type} {n : ℕ} {Γ : Cxt n}
                    → T Γ ((X ⇒ ⌜B⌝ Y A) ⇒ ⌜B⌝ X A ⇒ ⌜B⌝ Y A)
⌜kleisli-extension⌝ = ƛ (ƛ (ƛ (ƛ (ν₂ · ƛ(ν₄ · ν₀ · ν₂ · ν₁) · ν₀))))

kleisli-extension-behaviour : {X Y A : type}
                            → ⟦ ⌜kleisli-extension⌝ {X} {Y} {A} ⟧₀
                            ＝ λ f d η⋆ β⋆ → d (λ x → f x η⋆ β⋆) β⋆
kleisli-extension-behaviour = refl

⌜B-functor⌝ : {X Y A : type} {n : ℕ} {Γ : Cxt n}
            → T Γ ((X ⇒ Y) ⇒ ⌜B⌝ X A ⇒ ⌜B⌝ Y A)
⌜B-functor⌝ = ƛ(⌜kleisli-extension⌝ · ƛ(⌜η⌝ · (ν₁ · ν₀)))

B-functor-behaviour : {X Y A : type}
                    → ⟦ ⌜B-functor⌝ {X} {Y} {A} ⟧₀
                    ＝ λ f → ⟦ ⌜kleisli-extension⌝ ⟧₀ (λ x → ⟦ ⌜η⌝ ⟧₀ (f x))
B-functor-behaviour = refl

B-type〖_〗 : type → type → type
B-type〖 ι 〗 A     = ⌜B⌝ ι A
B-type〖 σ ⇒ τ 〗 A = B-type〖 σ 〗 A ⇒ B-type〖 τ 〗 A

⌜Kleisli-extension⌝ : {X A : type} {σ : type} {n : ℕ} {Γ : Cxt n}
                    → T Γ ((X ⇒ B-type〖 σ 〗 A) ⇒ ⌜B⌝ X A ⇒ B-type〖 σ 〗 A)
⌜Kleisli-extension⌝ {X} {A} {ι}     = ⌜kleisli-extension⌝
⌜Kleisli-extension⌝ {X} {A} {σ ⇒ τ} =
  ƛ (ƛ (ƛ (⌜Kleisli-extension⌝ {X} {A} {τ} · ƛ (ν₃ · ν₀ · ν₁) · ν₁)))

Kleisli-extension-behaviour : {X A : type} {σ τ : type}
                            → ⟦ ⌜Kleisli-extension⌝ {X} {A} {σ ⇒ τ}⟧₀
                            ＝ λ g d s → ⟦ ⌜Kleisli-extension⌝ {X} {A} {τ} ⟧
                                         (⟨⟩ ‚ g ‚ d ‚ s)
                                         (λ x → g x s)
                                         d
Kleisli-extension-behaviour = refl

⌜zero⌝ : {A : type} {n : ℕ} {Γ : Cxt n} → T Γ (⌜B⌝ ι A)
⌜zero⌝ = ⌜η⌝ · Zero

⌜succ⌝ : {A : type} {n : ℕ} {Γ : Cxt n} → T Γ (⌜B⌝ ι A ⇒ ⌜B⌝ ι A)
⌜succ⌝ =  ⌜B-functor⌝ · Succ

⌜rec⌝ : {σ A : type} {n : ℕ} {Γ : Cxt n}
      → T Γ ((⌜B⌝ ι A
               ⇒ B-type〖 σ 〗 A
               ⇒ B-type〖 σ 〗 A)
               ⇒ B-type〖 σ 〗 A
            ⇒ ⌜B⌝ ι A
            ⇒ B-type〖 σ 〗 A)
⌜rec⌝ {σ} {A} = ƛ (ƛ (⌜Kleisli-extension⌝ {ι} {A} {σ}
                        · (Rec · (ƛ (ν₂ · (⌜η⌝ · ν₀))) · ν₀)))

rec-behaviour : {σ A : type}
              → ⟦ ⌜rec⌝ {σ} {A} ⟧₀
              ＝ λ f x → ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ} ⟧
                          (⟨⟩ ‚ f ‚ x)
                          (rec (f ∘ ⟦ ⌜η⌝ {ι} {ι} {ι} {A} ⟧₀) x)
rec-behaviour = refl

B-context【_】 : {n : ℕ} → Cxt n → type → Cxt n
B-context【_】 {0}      〈〉       A = 〈〉
B-context【_】 {succ n} (Γ , σ) A = (B-context【_】 {n} Γ A , B-type〖 σ 〗 A)

infix 10 B-context【_】

⌜ν⌝ : {n : ℕ} {Γ : Cxt n} {A : type} (i : Fin n)
    → T (B-context【 Γ 】 A) (B-type〖 Γ [ i ] 〗 A)
⌜ν⌝ i = transport (T (B-context【 _ 】 _)) (p i) (ν i)
 where
  p : {n : ℕ} {Γ : Cxt n} {A : type} (i : Fin n)
    → B-context【 Γ 】 A [ i ] ＝ B-type〖 Γ [ i ] 〗 A
  p {0}      {〈〉}     ()
  p {succ n} {Γ , x} 𝟎       = refl
  p {succ n} {Γ , x} (suc i) = p i

\end{code}

(Compositional) translation of terms:

\begin{code}

⌜_⌝ : {n : ℕ} {Γ : Cxt n} {σ : type} {A : type}
    → T Γ σ
    → T (B-context【 Γ 】 A) (B-type〖 σ 〗 A)
⌜ Zero ⌝             = ⌜zero⌝
⌜ Succ ⌝             = ⌜succ⌝
⌜ Rec {_} {_} {σ} ⌝  = ⌜rec⌝ {σ}
⌜ ν i ⌝              = ⌜ν⌝ i
⌜ ƛ t ⌝              = ƛ ⌜ t ⌝
⌜ t · u ⌝            = ⌜ t ⌝ · ⌜ u ⌝

\end{code}

 Given a term of type (ι ⇒ ι) ⇒ ι, we calculate a term defining its dialogue tree:

\begin{code}

⌜generic⌝ : {A : type} {n : ℕ} {Γ : Cxt n}
          → T Γ (⌜B⌝ ι A ⇒ ⌜B⌝ ι A)
⌜generic⌝ = ⌜kleisli-extension⌝ · (⌜β⌝ · ⌜η⌝)

⌜dialogue-tree⌝ : {A : type} {n : ℕ} {Γ : Cxt n}
                → T Γ ((ι ⇒ ι) ⇒ ι)
                → T (B-context【 Γ 】 A) (⌜B⌝ ι A)
⌜dialogue-tree⌝ t = ⌜ t ⌝ · ⌜generic⌝

\end{code}

TODO. Formulate and prove the correctness of

Internal modulus of continuity:

\begin{code}

max : ℕ → ℕ → ℕ
max 0        n        = n
max (succ m) 0        = succ m
max (succ m) (succ n) = succ (max m n)

max' : ℕ → ℕ → ℕ
max' = rec {ℕ → ℕ} (λ m f → rec {ℕ} (λ n _ → succ (f n)) (succ m)) (λ n → n)

max-is-max' : (m n : ℕ) → max m n ＝ max' m n
max-is-max' 0        n        = refl
max-is-max' (succ m) 0        = refl
max-is-max' (succ m) (succ n) = ap succ (max-is-max' m n)

Max :  {n : ℕ} {Γ : Cxt n} → T Γ (ι ⇒ ι ⇒ ι)
Max = Rec · ƛ (ƛ (Rec · ƛ (ƛ (Succ · (ν₂ · ν₁))) · (Succ · ν₁))) · ƛ ν₀

\end{code}

A modulus of continuity can be calculated from a dialogue tree.

\begin{code}

max-question-in-path : {n : ℕ} {Γ : Cxt n}
                     → T (B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι))
                         ((⌜B⌝ ι ((ι ⇒ ι) ⇒ ι)) ⇒ (ι ⇒ ι) ⇒ ι)
max-question-in-path = ƛ(ν₀ · (ƛ(ƛ(Zero))) · (ƛ(ƛ(ƛ(Max · (Succ · ν₁) · (ν₂ · (ν₀ · ν₁) · ν₀))))))

max-question-in-path-behaviour₀ : ∀ n α → ⟦ max-question-in-path ⟧₀ (⟦ ⌜η⌝ ⟧₀ n) α ＝ 0
max-question-in-path-behaviour₀ n α = refl


max-question-in-path-behaviour₁ :

 ∀ φ n α → ⟦ max-question-in-path ⟧₀ (⟦ ⌜β⌝ ⟧₀ φ n) α
        ＝ ⟦ Max ⟧₀ (succ n) (⟦ max-question-in-path ⟧₀ (φ(α n)) α)

max-question-in-path-behaviour₁ φ n α = refl

internal-mod-cont : {n : ℕ} {Γ : Cxt n}
                  → T Γ ((ι ⇒ ι) ⇒ ι)
                  → T (B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι)) ((ι ⇒ ι) ⇒ ι)
internal-mod-cont t = max-question-in-path · (⌜dialogue-tree⌝ {(ι ⇒ ι) ⇒ ι} t)

internal-mod-cont₀ : T₀ ((ι ⇒ ι) ⇒ ι) → T₀ ((ι ⇒ ι) ⇒ ι)
internal-mod-cont₀ = internal-mod-cont

external-mod-cont : T₀ ((ι ⇒ ι) ⇒ ι) → (ℕ → ℕ) → ℕ
external-mod-cont t = ⟦ internal-mod-cont₀ t ⟧₀

\end{code}

TODO. Prove the correctness of the internal modulus of continuity.

Examples:

\begin{code}

module example where

 numeral : {n : ℕ} {Γ : Cxt n} → ℕ → T Γ ι
 numeral 0        = Zero
 numeral (succ n) = Succ · (numeral n)

 example₁ : (ℕ → ℕ) → ℕ
 example₁ = external-mod-cont(ƛ(ν₀ · (numeral 17)))

 m₁ : ℕ
 m₁ = example₁ (λ i → i)

 example₂ : (ℕ → ℕ) → ℕ
 example₂ = external-mod-cont(ƛ(ν₀ · (ν₀ · (numeral 17))))

 m₂ : ℕ
 m₂ = example₂ succ

 Add : {n : ℕ} {Γ : Cxt n} → T Γ (ι ⇒ ι ⇒ ι)
 Add = Rec · ƛ (ƛ (Succ · ν₀))

 example₃ : (ℕ → ℕ) → ℕ
 example₃ = external-mod-cont
             (ƛ (ν₀ · (ν₀ · (Add · (ν₀ · (numeral 17)) · (ν₀ · (numeral 34))))))

 m₃ : ℕ
 m₃ = example₃ succ

\end{code}
