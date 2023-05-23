Martin Escardo, Vincent Rahli, Bruno da Rocha Paiva, Ayberk Tosun 20 May 2023

This is an adaptation of Internal.lagda written by Martin, which defines dialogue-tree⋆ without using T'
but directly using T.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.InternalWithoutOracle where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import MLTT.Athenian using (Fin)
open import EffectfulForcing.Continuity
open import EffectfulForcing.Dialogue
open import EffectfulForcing.Internal hiding (B⋆⟦_⟧ ; dialogue-tree⋆)
open import EffectfulForcing.LambdaWithoutOracle
open import EffectfulForcing.SystemT

B⋆⟦_⟧ : {n : ℕ} {Γ : Cxt n} {σ : type} {A : Type}
      → T Γ σ
      → B⋆【 Γ 】 A
      → B⋆〖 σ 〗 A
B⋆⟦ Zero            ⟧  _ = zero⋆
B⋆⟦ Succ            ⟧  _ = succ⋆
B⋆⟦ Rec {_} {_} {σ} ⟧  _ = rec⋆ {σ}
B⋆⟦ ν i             ⟧ xs = xs i
B⋆⟦ ƛ t             ⟧ xs = λ x → B⋆⟦ t ⟧ (xs ‚‚⋆ x)
B⋆⟦ t · u           ⟧ xs = (B⋆⟦ t ⟧ xs) (B⋆⟦ u ⟧ xs)

B⋆⟦_⟧₀ : {σ : type} {A : Type} → T₀ σ → B⋆〖 σ 〗 A
B⋆⟦ t ⟧₀ = B⋆⟦ t ⟧ ⟪⟫⋆

dialogue-tree⋆ : {A : Type} → T₀ ((ι ⇒ ι) ⇒ ι) → B⋆ ℕ A
dialogue-tree⋆ t = B⋆⟦ t ⟧₀ generic⋆

\end{code}

TODO. Formulate and prove the correctness of ⌜dialogue-tree⌝.

\begin{code}
{-
R⋆ : (σ : type) → B⋆〖 σ 〗 (B ℕ) → B〖 σ 〗 → Type
R⋆ ι       x y = church-decode x ≣ y
R⋆ (σ ⇒ τ) f g = (x : B⋆〖 σ 〗 (B ℕ))
                 (y : B〖 σ 〗)
               → R⋆ σ x y
               → R⋆ τ (f x) (g y)

Rs⋆ : {n : ℕ} {Γ : Cxt n}
    → B⋆【 Γ 】 (B ℕ) → B【 Γ 】 → Type
Rs⋆ {n} {Γ} xs ys = (i : Fin n) → R⋆ (Γ [ i ]) (xs i) (ys i)

main-lemma⋆ : {n : ℕ} {Γ : Cxt n}
              {σ : type}
              (t : T Γ σ)
              (α : Baire)
              (xs : B⋆【 Γ 】 (B ℕ))
              (ys : B【 Γ 】)
            → Rs⋆ xs ys
            → R⋆ σ (B⋆⟦ t ⟧ xs) (B⟦ t ⟧ ys)
main-lemma⋆ = {!!}
-}
\end{code}

The above should be true, but do we really need it?

\begin{code}

⌜R⌝ : ({A} σ : type) → T₀ (⌜B⌝ σ A) → B⋆〖 σ 〗 〖 A 〗 → Type
⌜R⌝ ι       t d = ⟦ t ⟧₀ ＝ d
⌜R⌝ (σ ⇒ τ) f g = (t : {!!})
                 (d : {!!})
               → ⌜R⌝ σ t d
               → ⌜R⌝ τ {!!} (g d)

{-
⌜Rs⌝ : {n : ℕ} {Γ : Cxt n}
    → B⋆【 Γ 】 (B ℕ) → B【 Γ 】 → Type
⌜Rs⌝ {n} {Γ} xs ys = (i : Fin n) → ⌜R⌝ (Γ [ i ]) (xs i) (ys i)

⌜main-lemma⌝ : {n : ℕ} {Γ : Cxt n}
              {σ : type}
              (t : T Γ σ)
              (α : Baire)
              (xs : B⋆【 Γ 】 (B ℕ))
              (ys : B【 Γ 】)
            → ⌜Rs⌝ xs ys
            → ⌜R⌝ σ (B⋆⟦ t ⟧ xs) (B⟦ t ⟧ ys)
⌜main-lemma⌝ = {!!}
-}

R⋆ : {σ : type} → Baire → 〖 σ 〗 → T₀ (⌜B⌝ σ ((ι ⇒ ι) ⇒ ι)) → Type
R⋆ {ι}     α n d  = n ＝ dialogue⋆ ⟦ d ⟧₀ α
R⋆ {σ ⇒ τ} α f f' = (x  : 〖 σ 〗)
                   (x' : {!!})
                 → R⋆ {σ} α x x'
                 → R⋆ {τ} α (f x) {!!} -- (f' x')


\end{code}
