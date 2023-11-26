Martin Escardo & Paulo Oliva, Fri 24-25 Feb 2017

Conversion of dialogue trees to Brouwer trees.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.MFPSAndVariations.Dialogue-to-Brouwer where

open import MLTT.Spartan
open import EffectfulForcing.MFPSAndVariations.Dialogue

\end{code}

Dialogue trees represent functions (ℕ → ℕ) → ℕ.

\begin{code}

Dialogue = B ℕ

deval : Dialogue → (ℕ → ℕ) → ℕ
deval = dialogue

\end{code}

Brouwer trees.

\begin{code}

data Brouwer : Set where
 η : ℕ → Brouwer
 δ : (ℕ → Brouwer) → Brouwer

\end{code}

We use φ to range over forests of dialogue trees, that is,
functions ℕ → D.

We use γ to range over forests of Brower trees.

Brouwer trees represent functions (ℕ → ℕ) → ℕ too:

\begin{code}

beval : Brouwer → (ℕ → ℕ) → ℕ
beval (η k) α = k
beval (δ γ) α = beval (γ (α 0)) (λ i → α (succ i))

\end{code}

Conversion from dialogue to Brouwer trees, with two auxiliary
functions follow and β':

\begin{code}

follow : ℕ → Brouwer → Brouwer
follow n (η k) = η k
follow n (δ γ) = γ n

\end{code}

The function β' simulates the constructor β in Brouwer trees:

\begin{code}

β' : (ℕ → Brouwer) → ℕ → Brouwer
β' γ 0        = δ (λ i → follow i (γ i))
β' γ (succ n) = δ (λ i → β' (λ j → follow i (γ j)) n)

\end{code}

Conversion is the unique homomorphism w.r.t. dialogue structure:

\begin{code}

convert : Dialogue → Brouwer
convert (η k)   = η k
convert (β φ n) = β' (λ i → convert (φ i)) n

\end{code}

The correctness proof of the function convert uses two lemmas, one
for the function follow and the other for the function β':

By cases on b:

\begin{code}

follow-lemma : (b : Brouwer) (α : ℕ → ℕ)
             → beval b α ＝ beval (follow (α 0) b) (λ i → α (succ i))
follow-lemma (η k) α = refl
follow-lemma (δ φ) α = refl

\end{code}

By induction on n, using follow-lemma both in the base case and the
induction step:

\begin{code}

β'-lemma : (n : ℕ) (φ : ℕ → Brouwer) (α : ℕ → ℕ)
         → beval (φ (α n)) α ＝ beval (β' φ n) α

β'-lemma 0 φ α =
 beval (φ (α 0)) α                                 ＝⟨ I ⟩
 beval (follow (α 0) (φ (α 0))) (λ i → α (succ i)) ＝⟨ refl ⟩
 beval (δ (λ i → follow i (φ i))) α                ＝⟨ refl ⟩
 beval (β' φ 0) α                                  ∎
  where
   I = follow-lemma (φ (α 0)) α

β'-lemma (succ n) φ α =
 beval (φ (α (succ n))) α                                   ＝⟨ I ⟩
 beval (follow (α 0) (φ (α (succ n)))) (λ i → α (succ i))   ＝⟨ II ⟩
 beval (β' (λ j → follow (α 0) (φ j)) n) (λ i → α (succ i)) ＝⟨ refl ⟩
 beval (δ (λ i → β' (λ j → follow i (φ j)) n)) α            ＝⟨ refl ⟩
 beval (β' φ (succ n)) α                                    ∎
  where
   I  = follow-lemma (φ (α (succ n))) α
   II = β'-lemma n (λ j → follow (α 0) (φ j)) (λ i → α (succ i))

\end{code}

By induction on d, using β'-lemma in the induction step:

\begin{code}

convert-correctness : (d : Dialogue) (α : ℕ → ℕ) → deval d α ＝ beval (convert d) α
convert-correctness (η k)   α = refl
convert-correctness (β φ n) α =
 deval (φ (α n)) α                      ＝⟨ convert-correctness (φ(α n)) α ⟩
 beval (convert (φ (α n))) α            ＝⟨ β'-lemma n (λ i → convert (φ i)) α ⟩
 beval (β' (λ i → convert (φ i)) n) α   ∎

\end{code}
