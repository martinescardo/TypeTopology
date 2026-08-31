Martin Escardo 22-23 May 2013

Gödel's system T and its standard set-theoretical semantics.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.MFPSAndVariations.SystemT where

open import MLTT.Spartan  hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import MLTT.Fin
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Continuity
open import UF.Base

data type : 𝓤₀ ̇ where
 ι   : type
 _⇒_ : type → type → type

infixr 6 _⇒_

\end{code}

We work with vector types which notational grow at the end rather than
the head.  This is because we use vector types to represent contexts,
which traditionally grow at the end:

\begin{code}

_^_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X ^ 0        = 𝟙
X ^ (succ n) = X ^ n × X

infixr 3 _^_

_[_] : {X : Set} {n : ℕ} → X ^ n → Fin n → X
_[_] {X} {succ n} (xs , x) 𝟎       = x
_[_] {X} {succ n} (xs , x) (suc i) = xs [ i ]

Cxt : ℕ → 𝓤₀ ̇
Cxt n = type ^ n

data T : {n : ℕ} (Γ : Cxt n) (σ : type) → 𝓤₀ ̇  where
 Zero : {n : ℕ} {Γ : Cxt n} → T Γ ι
 Succ : {n : ℕ} {Γ : Cxt n} → T Γ (ι ⇒ ι)
 Rec  : {n : ℕ} {Γ : Cxt n} {σ : type}   → T Γ ((ι ⇒ σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
 ν    : {n : ℕ} {Γ : Cxt n} (i : Fin n)  → T Γ (Γ [ i ])
 ƛ    : {n : ℕ} {Γ : Cxt n} {σ τ : type} → T (Γ , σ) τ → T Γ (σ ⇒ τ)
 _·_  : {n : ℕ} {Γ : Cxt n} {σ τ : type} → T Γ (σ ⇒ τ) → T Γ σ → T Γ τ

infixl 6 _·_

\end{code}

The standard interpretation of system T:

\begin{code}

〖_〗 : type → 𝓤₀ ̇
〖 ι 〗     = ℕ
〖 σ ⇒ τ 〗 = 〖 σ 〗 → 〖 τ 〗

【_】 : {n : ℕ} (Γ : Cxt n) → 𝓤₀ ̇
【 Γ 】 = (i : Fin _) → 〖 Γ [ i ] 〗

⟨⟩ : 【 〈〉 】
⟨⟩ ()

_‚_ : {n : ℕ} {Γ : Cxt n} {σ : type} → 【 Γ 】 → 〖 σ 〗 → 【 Γ , σ 】
(xs ‚ x)  𝟎      = x
(xs ‚ x) (suc i) = xs i

infixl 6 _‚_

⟦_⟧ : {n : ℕ} {Γ : Cxt n} {σ : type} → T Γ σ → 【 Γ 】 → 〖 σ 〗
⟦ Zero  ⟧  _ = 0
⟦ Succ  ⟧  _ = succ
⟦ Rec   ⟧  _ = rec
⟦ ν i   ⟧ xs = xs i
⟦ ƛ t   ⟧ xs = λ x → ⟦ t ⟧ (xs ‚ x)
⟦ t · u ⟧ xs = (⟦ t ⟧ xs) (⟦ u ⟧ xs)

\end{code}

Closed terms can be interpreted in a special way:

\begin{code}

T₀ : type → 𝓤₀ ̇
T₀ = T 〈〉

⟦_⟧₀  : {σ : type} → T₀ σ → 〖 σ 〗
⟦ t ⟧₀ = ⟦ t ⟧ ⟨⟩

T-definable : {σ : type} → 〖 σ 〗 → 𝓤₀ ̇
T-definable {σ} x = Σ t ꞉ T₀ σ , ⟦ t ⟧₀ ＝ x

\end{code}

System T extended with a formal oracle Ω, called T' (rather than TΩ as previously):

\begin{code}

data T' : {n : ℕ} (Γ : Cxt n) (σ : type) → 𝓤₀ ̇  where
 Ω    : {n : ℕ} {Γ : Cxt n} → T' Γ (ι ⇒ ι)
 Zero : {n : ℕ} {Γ : Cxt n} → T' Γ ι
 Succ : {n : ℕ} {Γ : Cxt n} → T' Γ (ι ⇒ ι)
 Rec  : {n : ℕ} {Γ : Cxt n} → {σ : type}   → T' Γ ((ι ⇒ σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
 ν    : {n : ℕ} {Γ : Cxt n} → (i : Fin n)  → T' Γ (Γ [ i ])
 ƛ    : {n : ℕ} {Γ : Cxt n} → {σ τ : type} → T' (Γ , σ) τ → T' Γ (σ ⇒ τ)
 _·_  : {n : ℕ} {Γ : Cxt n} → {σ τ : type} → T' Γ (σ ⇒ τ) → T' Γ σ → T' Γ τ


⟦_⟧' : {n : ℕ} {Γ : Cxt n} {σ : type} → T' Γ σ → Baire → 【 Γ 】 → 〖 σ 〗
⟦ Ω     ⟧' α  _ = α
⟦ Zero  ⟧' _  _ = 0
⟦ Succ  ⟧' _  _ = succ
⟦ Rec   ⟧' _  _ = rec
⟦ ν i   ⟧' _ xs = xs i
⟦ ƛ t   ⟧' α xs = λ x → ⟦ t ⟧' α (xs ‚ x)
⟦ t · u ⟧' α xs = (⟦ t ⟧' α xs) (⟦ u ⟧' α xs)

\end{code}

To regard system T as a sublanguage of T', we need to work with an
explicit embedding:

\begin{code}

embed : {n : ℕ} {Γ : Cxt n} {σ : type} → T Γ σ → T' Γ σ
embed Zero    = Zero
embed Succ    = Succ
embed Rec     = Rec
embed (ν i)   = ν i
embed (ƛ t)   = ƛ (embed t)
embed (t · u) = (embed t) · (embed u)

preservation : {n : ℕ}
               {Γ : Cxt n}
               {σ : type}
               (t : T Γ σ)
               (α : Baire)
             → ⟦ t ⟧ ＝ ⟦ embed t ⟧' α
preservation Zero    α = refl
preservation Succ    α = refl
preservation Rec     α = refl
preservation (ν i)   α = refl
preservation (ƛ t)   α = ap (λ f xs x → f (xs ‚ x)) (preservation t α)
preservation (t · u) α = ap₂ (λ f g x → f x (g x))
                             (preservation t α)
                             (preservation u α)
\end{code}

Some shorthands to simplify examples of system T terms.

\begin{code}

numeral : {n : ℕ} {Γ : Cxt n} → ℕ → T Γ ι
numeral 0        = Zero
numeral (succ n) = Succ · (numeral n)

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

\end{code}
