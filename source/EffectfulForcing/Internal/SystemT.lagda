Martin Escardo, Bruno da Rocha Paiva, Ayberk Tosun, and Vincent Rahli, June 2023

Gödel's system T and its standard set-theoretical semantics. This is a
modification of EffectfulForcing.MFPSAndVariations.SystemT, based on
PLFA (https://plfa.github.io/), which avoids lots of transport in the
file EffectfulForcing.Internal.Subst.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline #-}

module EffectfulForcing.Internal.SystemT where

open import MLTT.Spartan  hiding (rec ; _^_)
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Continuity
open import EffectfulForcing.MFPSAndVariations.SystemT using (type ; ι ; _⇒_ ; 〖_〗)
open import UF.Base using (ap₂ ; ap₃)

\end{code}

We work with vector types which notational grow at the end rather than
the head.  This is because we use vector types to represent contexts,
which traditionally grow at the end:

\begin{code}

_^_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X ^ 0        = 𝟙
X ^ (succ n) = X ^ n × X

infixr 3 _^_

data Cxt : 𝓤₀ ̇ where
 〈〉 : Cxt
 _,,_ : Cxt → type → Cxt

infixl 6 _,,_

data ∈Cxt (σ : type) : Cxt → 𝓤₀ ̇ where
 ∈Cxt0 : (Γ : Cxt) → ∈Cxt σ (Γ ,, σ)
 ∈CxtS : {Γ : Cxt} (τ : type) → ∈Cxt σ Γ → ∈Cxt σ (Γ ,, τ)

data T : (Γ : Cxt) (σ : type) → 𝓤₀ ̇ where
 Zero : {Γ : Cxt} → T Γ ι
 Succ : {Γ : Cxt} → T Γ ι → T Γ ι
 Rec  : {Γ : Cxt} {σ : type} → T Γ (ι ⇒ σ ⇒ σ) → T Γ σ → T Γ ι → T Γ σ
 ν    : {Γ : Cxt} {σ : type} (i : ∈Cxt σ Γ)  → T Γ σ
 ƛ    : {Γ : Cxt} {σ τ : type} → T (Γ ,, σ) τ → T Γ (σ ⇒ τ)
 _·_  : {Γ : Cxt} {σ τ : type} → T Γ (σ ⇒ τ) → T Γ σ → T Γ τ

infixl 6 _·_

\end{code}

The standard interpretation of system T:

\begin{code}

【_】 : (Γ : Cxt) → 𝓤₀ ̇
【 Γ 】 = {σ : type} (i : ∈Cxt σ Γ) → 〖 σ 〗

⟨⟩ : 【 〈〉 】
⟨⟩ ()

_‚_ : {Γ : Cxt} {σ : type} → 【 Γ 】 → 〖 σ 〗 → 【 Γ ,, σ 】
(xs ‚ x) {σ} (∈Cxt0 _) = x
(xs ‚ x) {σ} (∈CxtS _ i) = xs i

infixl 6 _‚_

⟦_⟧ : {Γ : Cxt} {σ : type} → T Γ σ → 【 Γ 】 → 〖 σ 〗
⟦ Zero      ⟧  _ = 0
⟦ Succ t    ⟧ xs = succ (⟦ t ⟧ xs)
⟦ Rec f g t ⟧ xs = rec (⟦ f ⟧ xs) (⟦ g ⟧ xs) (⟦ t ⟧ xs)
⟦ ν i       ⟧ xs = xs i
⟦ ƛ t       ⟧ xs = λ x → ⟦ t ⟧ (xs ‚ x)
⟦ t · u     ⟧ xs = (⟦ t ⟧ xs) (⟦ u ⟧ xs)

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

data T' : (Γ : Cxt) (σ : type) → 𝓤₀ ̇  where
 Ω    : {Γ : Cxt} → T' Γ (ι ⇒ ι)
 Zero : {Γ : Cxt} → T' Γ ι
 Succ : {Γ : Cxt} → T' Γ ι → T' Γ ι
 Rec  : {Γ : Cxt} → {σ : type} → T' Γ (ι ⇒ σ ⇒ σ) → T' Γ σ → T' Γ ι → T' Γ σ
 ν    : {Γ : Cxt} {σ : type} (a : ∈Cxt σ Γ)  → T' Γ σ
 ƛ    : {Γ : Cxt} → {σ τ : type} → T' (Γ ,, σ) τ → T' Γ (σ ⇒ τ)
 _·_  : {Γ : Cxt} → {σ τ : type} → T' Γ (σ ⇒ τ) → T' Γ σ → T' Γ τ


⟦_⟧' : {Γ : Cxt} {σ : type} → T' Γ σ → Baire → 【 Γ 】 → 〖 σ 〗
⟦ Ω         ⟧' α  _ = α
⟦ Zero      ⟧' _  _ = 0
⟦ Succ t    ⟧' α xs = succ (⟦ t ⟧' α xs)
⟦ Rec f g t ⟧' α xs = rec (⟦ f ⟧' α xs) (⟦ g ⟧' α xs) (⟦ t ⟧' α xs)
⟦ ν i       ⟧' _ xs = xs i
⟦ ƛ t       ⟧' α xs = λ x → ⟦ t ⟧' α (xs ‚ x)
⟦ t · u     ⟧' α xs = (⟦ t ⟧' α xs) (⟦ u ⟧' α xs)

\end{code}

To regard system T as a sublanguage of T', we need to work with an
explicit embedding:

\begin{code}

embed : {Γ : Cxt} {σ : type} → T Γ σ → T' Γ σ
embed Zero        = Zero
embed (Succ t)    = Succ (embed t)
embed (Rec f g t) = Rec (embed f) (embed g) (embed t)
embed (ν i)       = ν i
embed (ƛ t)       = ƛ (embed t)
embed (t · u)     = (embed t) · (embed u)

preservation : {Γ : Cxt}
               {σ : type}
               (t : T Γ σ)
               (α : Baire)
             → ⟦ t ⟧ ＝ ⟦ embed t ⟧' α
preservation Zero        α = refl
preservation (Succ t)    α = ap (λ f xs → succ (f xs)) (preservation t α)
preservation (Rec f g t) α = ap₃ (λ f g t xs → rec (f xs) (g xs) (t xs))
                             (preservation f α)
                             (preservation g α)
                             (preservation t α)
preservation (ν i)       α = refl
preservation (ƛ t)       α = ap (λ f xs x → f (xs ‚ x)) (preservation t α)
preservation (t · u)     α = ap₂ (λ f g x → f x (g x))
                             (preservation t α)
                             (preservation u α)
\end{code}

Some shorthands to simplify examples of system T terms.

\begin{code}

numeral : {Γ : Cxt} → ℕ → T Γ ι
numeral 0        = Zero
numeral (succ n) = Succ (numeral n)

ν₀ : {Γ : Cxt} {σ : type}  → T (Γ ,, σ) σ
ν₀ {Γ} {σ} = ν (∈Cxt0 Γ)

ν₁ : {Γ : Cxt} {σ₁ σ₂ : type} → T (Γ ,, σ₁ ,, σ₂) σ₁
ν₁ {Γ} {σ₁} {σ₂} = ν (∈CxtS σ₂ (∈Cxt0 Γ))

ν₂ : {Γ : Cxt} {σ₁ σ₂ σ₃ : type} → T (Γ ,, σ₁ ,, σ₂ ,, σ₃) σ₁
ν₂ {Γ} {σ₁} {σ₂} {σ₃} = ν (∈CxtS σ₃ (∈CxtS σ₂ (∈Cxt0 Γ)))

ν₃ : {Γ : Cxt} {σ₁ σ₂ σ₃ σ₄ : type} → T (Γ ,, σ₁ ,, σ₂ ,, σ₃ ,, σ₄) σ₁
ν₃ {Γ} {σ₁} {σ₂} {σ₃} {σ₄} = ν (∈CxtS σ₄ (∈CxtS σ₃ (∈CxtS σ₂ (∈Cxt0 Γ))))

ν₄ : {Γ : Cxt} {σ₁ σ₂ σ₃ σ₄ σ₅ : type} → T (Γ ,, σ₁ ,, σ₂ ,, σ₃ ,, σ₄ ,, σ₅) σ₁
ν₄ {Γ} {σ₁} {σ₂} {σ₃} {σ₄} {σ₅} = ν (∈CxtS σ₅ (∈CxtS σ₄ (∈CxtS σ₃ (∈CxtS σ₂ (∈Cxt0 Γ)))))

ν₅ : {Γ : Cxt} {σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ : type} → T (Γ ,, σ₁ ,, σ₂ ,, σ₃ ,, σ₄ ,, σ₅ ,, σ₆) σ₁
ν₅ {Γ} {σ₁} {σ₂} {σ₃} {σ₄} {σ₅} {σ₆} = ν (∈CxtS σ₆ (∈CxtS σ₅ (∈CxtS σ₄ (∈CxtS σ₃ (∈CxtS σ₂ (∈Cxt0 Γ))))))

Succ' : {Γ : Cxt} → T Γ (ι ⇒ ι)
Succ' {Γ} = ƛ (Succ ν₀)

Rec' : {σ : type} {Γ : Cxt} → T Γ ((ι ⇒ σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
Rec' {σ} {Γ} = ƛ (ƛ (ƛ (Rec ν₂ ν₁ ν₀)))

\end{code}

Composition operation in System T:

\begin{code}

comp : {Γ : Cxt} {ρ σ τ : type} → T Γ ((σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
comp {Γ = Γ} = ƛ (ƛ (ƛ (ν₂ · (ν₁ · ν₀))))

\end{code}
