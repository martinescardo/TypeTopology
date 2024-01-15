Tom de Jong & Martin Escardo, 20 May 2019.

Combinatory version of Platek-Scott-Plotkin PCF.
Includes (reflexive transitive closure of) operational semantics.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc

module PCF.Combinatory.PCF (pt : propositional-truncations-exist) where

open PropositionalTruncation pt

open import MLTT.Spartan
open import UF.Subsingletons

data type : 𝓤₀ ̇ where
  ι   : type
  _⇒_ : type → type → type

infixr 1 _⇒_

data PCF : (σ : type) → 𝓤₀ ̇ where
  Zero   : PCF ι
  Succ   : PCF (ι ⇒ ι)
  Pred   : PCF (ι ⇒ ι)
  ifZero : PCF (ι ⇒ ι ⇒ ι ⇒ ι)
  Fix    : {σ : type}     → PCF ((σ ⇒ σ) ⇒ σ)
  K      : {σ τ : type}   → PCF (σ ⇒ τ ⇒ σ)
  S      : {ρ σ τ : type} → PCF ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
  _·_    : {σ τ : type}   → PCF (σ ⇒ τ) → PCF σ → PCF τ

infixl 1 _·_

⌜_⌝ : ℕ → PCF ι
⌜ zero ⌝ = Zero
⌜ succ n ⌝ = Succ · ⌜ n ⌝

data _▹'_ : {σ : type} → PCF σ → PCF σ → 𝓤₀ ̇ where
  Pred-zero   : (Pred · Zero) ▹' Zero
  Pred-succ   : (n : ℕ) → (Pred · ⌜ succ n ⌝) ▹' ⌜ n ⌝
  ifZero-zero : (s t : PCF ι) → (ifZero · s · t · Zero) ▹' s
  ifZero-succ : (n : ℕ) (s t : PCF ι) → (ifZero · s · t · ⌜ succ n ⌝) ▹' t
  Fix-step    : {σ : type} (t : PCF (σ ⇒ σ)) → (Fix · t) ▹' (t · (Fix · t))
  K-step      : {σ τ : type} (s : PCF σ) (t : PCF τ) → (K · s · t) ▹' s
  S-step      : {ρ σ τ : type} (f : PCF (ρ ⇒ σ ⇒ τ)) (g : PCF (ρ ⇒ σ)) (x : PCF ρ) →
                (S · f · g · x) ▹' (f · x · (g · x))
  ·-step      : {σ τ : type} (s t : PCF (σ ⇒ τ)) (r : PCF σ) →
                s ▹' t → (s · r) ▹' (t · r)
  Pred-arg    : (s t : PCF ι) → s ▹' t → (Pred · s) ▹' (Pred · t)
  Succ-arg    : (s t : PCF ι) → s ▹' t → (Succ · s) ▹' (Succ · t)
  ifZero-arg  : (s t r r' : PCF ι) →
                r ▹' r' → (ifZero · s · t · r) ▹' (ifZero · s · t · r')

_▹_ : {σ : type} → PCF σ → PCF σ → 𝓤₀ ̇
s ▹ t = ∥ s ▹' t ∥

data _▹*'_ : {σ : type} → PCF σ → PCF σ → 𝓤₀ ̇ where
  extend : {σ : type} {s t : PCF σ} → s ▹ t → s ▹*' t
  refl   : {σ : type} (s : PCF σ) → s ▹*' s
  trans  : {σ : type} {s t r : PCF σ} → s ▹*' t → t ▹*' r → s ▹*' r

_▹*_ : {σ : type} → PCF σ → PCF σ → 𝓤₀ ̇
s ▹* t = ∥ s ▹*' t ∥

▹'-to-▹*' : {σ τ : type} (f : PCF σ → PCF τ) →
            ((s t : PCF σ) → s ▹' t → (f s) ▹' (f t)) →
            (s t : PCF σ) → s ▹*' t → (f s) ▹*' (f t)
▹'-to-▹*' f f-preserves-▹' s t (extend rel) = extend (∥∥-rec a b rel)
 where
  a : is-prop (f s ▹ f t)
  a = ∥∥-is-prop
  b : (step : s ▹' t) → ∥ f s ▹' f t ∥
  b step = ∣ f-preserves-▹' s t step ∣

▹'-to-▹*' f f-preserves-▹' s s (refl s) = refl (f s)
▹'-to-▹*' f f-preserves-▹' s r (trans {σ} {s} {t} {r} rel₁ rel₂) = trans IH₁ IH₂
 where
  IH₁ : f s ▹*' f t
  IH₁ = ▹'-to-▹*' f f-preserves-▹' s t rel₁
  IH₂ : f t ▹*' f r
  IH₂ = ▹'-to-▹*' f f-preserves-▹' t r rel₂

▹'-to-▹* : {σ τ : type} (f : PCF σ → PCF τ) →
           ((s t : PCF σ) → s ▹' t → (f s) ▹' (f t)) →
           (s t : PCF σ) → s ▹* t → (f s) ▹* (f t)
▹'-to-▹* f f-preserves-▹' s t = ∥∥-functor (▹'-to-▹*' f f-preserves-▹' s t)

·-step* : {σ τ : type} (f g : PCF (σ ⇒ τ)) (t : PCF σ)
        → f ▹* g → (f · t) ▹* (g · t)
·-step* f g t rel = ▹'-to-▹* (λ x → x · t) (λ f' g' → ·-step f' g' t) f g rel

Succ-arg* : (s t : PCF ι) → s ▹* t → (Succ · s) ▹* (Succ · t)
Succ-arg* = ▹'-to-▹* (λ x → Succ · x) Succ-arg

Pred-arg* : (s t : PCF ι) → s ▹* t → (Pred · s) ▹* (Pred · t)
Pred-arg* = ▹'-to-▹* (λ x → Pred · x) Pred-arg

ifZero-arg* : (s t r r' : PCF ι) → r ▹* r'
            → (ifZero · s · t · r) ▹* (ifZero · s · t · r')
ifZero-arg* s t = ▹'-to-▹* (λ x → ifZero · s · t · x) (ifZero-arg s t)

\end{code}
