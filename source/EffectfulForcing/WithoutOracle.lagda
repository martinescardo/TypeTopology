Vincent Rahli, 14 March 2015.

This is a variant of the proof given by Martin Escardo in
https://doi.org/10.1016/j.entcs.2013.09.010 (MFPS XXIX) that does not
use the formal oracle Ω, and instead directly shows the relation
between ⟦_⟧ and B⟦_⟧ (see R's definition and main-lemma).  Then, as
before in dialogue-tree-correct, we use generic sequence to consult
the ``oracle'' α.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module EffectfulForcing.WithoutOracle where

open import MLTT.Spartan
open import MLTT.Athenian
open import UF.Base
open import EffectfulForcing.Combinators
open import EffectfulForcing.Continuity
open import EffectfulForcing.Dialogue
open import EffectfulForcing.CombinatoryT

B-Set⟦_⟧ : type → 𝓤₀ ̇
B-Set⟦ ι ⟧     = B ℕ
B-Set⟦ σ ⇒ τ ⟧ = B-Set⟦ σ ⟧ → B-Set⟦ τ ⟧

Kleisli-extension : {X : 𝓤₀ ̇ } {σ : type} → (X → B-Set⟦ σ ⟧) → B X → B-Set⟦ σ ⟧
Kleisli-extension {X} {ι}     = kleisli-extension
Kleisli-extension {X} {σ ⇒ τ} = λ g d s → Kleisli-extension {X} {τ} (λ x → g x s) d

zero' : B ℕ
zero' = η zero

succ' : B ℕ → B ℕ
succ' = B-functor succ

iter' : {σ : type} → (B-Set⟦ σ ⟧ → B-Set⟦ σ ⟧) → B-Set⟦ σ ⟧ → B ℕ → B-Set⟦ σ ⟧
iter' f x = Kleisli-extension (iter f x)

B⟦_⟧ : {σ : type} → T σ → B-Set⟦ σ ⟧
B⟦ Zero ⟧  = zero'
B⟦ Succ ⟧  = succ'
B⟦ Iter ⟧  = iter'
B⟦ K ⟧     = Ķ
B⟦ S ⟧     = Ş
B⟦ t · u ⟧ = B⟦ t ⟧ (B⟦ u ⟧)

dialogue-tree : T((ι ⇒ ι) ⇒ ι) → B ℕ
dialogue-tree t = B⟦ t ⟧ generic

R : {σ : type} → Baire → Set⟦ σ ⟧ → B-Set⟦ σ ⟧ → Set
R {ι}     α n d  = n ＝ dialogue d α
R {σ ⇒ τ} α f f' = (x  : Set⟦ σ ⟧)
                   (x' : B-Set⟦ σ ⟧)
                 → R {σ} α x x'
                 → R {τ} α (f x) (f' x')

R-kleisli-lemma : (σ : type)
                  (α : Baire)
                  (g  : ℕ → Set⟦ σ ⟧)
                  (g' : ℕ → B-Set⟦ σ ⟧)
                → ((k : ℕ) → R α (g k) (g' k))
                → (n  : ℕ)
                  (n' : B ℕ)
                → R α n n'
                → R α (g n) (Kleisli-extension g' n')

R-kleisli-lemma ι α g g' rg n n' rn =
 g n                                   ＝⟨ rg n ⟩
 dialogue (g' n) α                     ＝⟨ ap (λ - → dialogue (g' -) α) rn ⟩
 dialogue (g' (dialogue n' α)) α       ＝⟨ decode-kleisli-extension g' n' α ⟩
 dialogue (Kleisli-extension g' n') α  ∎

R-kleisli-lemma (σ ⇒ τ) α g g' rg n n' rn
  = λ y y' ry → R-kleisli-lemma
                 τ
                 α
                 (λ k → g k y)
                 (λ k → g' k y')
                 (λ k → rg k y y' ry)
                 n
                 n'
                 rn

main-lemma : {σ : type} (t : T σ) (α : Baire) → R α ⟦ t ⟧ (B⟦ t ⟧)

main-lemma Zero = λ α → refl

main-lemma Succ = λ α n n' rn →
 succ n               ＝⟨ ap succ rn ⟩
 succ (dialogue n' α) ＝⟨ decode-α-is-natural succ n' α ⟩
 decode α (succ' n')  ∎

main-lemma {(σ ⇒ .σ) ⇒ .σ ⇒ ι ⇒ .σ} Iter = lemma
 where
  lemma :  (α : Baire)
           (f  : Set⟦ σ ⟧ → Set⟦ σ ⟧)
           (f' : B-Set⟦ σ ⟧ → B-Set⟦ σ ⟧)
        → R {σ ⇒ σ} α f f'
        → (x  : Set⟦ σ ⟧)
          (x' : B-Set⟦ σ ⟧)
        → R {σ} α x x'
        → (n  : ℕ)
          (n' : B ℕ)
        → R {ι} α n n'
        → R {σ} α (iter f x n) (Kleisli-extension (iter f' x') n')
  lemma α f f' rf x x' rx = R-kleisli-lemma σ α g g' rg
    where
      g : ℕ → Set⟦ σ ⟧
      g k = iter f x k

      g' : ℕ → B-Set⟦ σ ⟧
      g' k = iter f' x' k

      rg : (k : ℕ) → R α (g k) (g' k)
      rg zero     = rx
      rg (succ k) = rf (g k) (g' k) (rg k)

main-lemma K = λ α x x' rx y y' ry → rx

main-lemma S = λ α f f' rf g g' rg x x' rx → rf x x' rx (g x) (g' x') (rg x x' rx)

main-lemma (t · u) = λ α → main-lemma t α ⟦ u ⟧ B⟦ u ⟧ (main-lemma u α)

dialogue-tree-correct : (t : T ((ι ⇒ ι) ⇒ ι))
                        (α : Baire)
                      → ⟦ t ⟧ α ＝ dialogue (dialogue-tree t) α
dialogue-tree-correct t α =
 ⟦ t ⟧ α                      ＝⟨ main-lemma t α α generic lemma ⟩
 dialogue (B⟦ t ⟧ generic) α  ＝⟨ refl ⟩
 dialogue (dialogue-tree t) α ∎
  where
   lemma : (n  : ℕ)
           (n' : B ℕ)
         → n ＝ dialogue n' α
         → α n ＝ dialogue (generic n') α
   lemma n n' rn = α n                     ＝⟨ ap α rn ⟩
                   α (dialogue n' α)       ＝⟨ generic-diagram α n' ⟩
                   decode α (generic n')   ＝⟨ refl ⟩
                   dialogue (generic n') α ∎

eloquence-theorem : (f : Baire → ℕ)
                  → is-T-definable f
                  → eloquent f
eloquence-theorem f (t , r) =
 (dialogue-tree t ,
  (λ α → dialogue (dialogue-tree t) α ＝⟨ (dialogue-tree-correct t α)⁻¹ ⟩
         ⟦ t ⟧ α                      ＝⟨ ap (λ - → - α) r ⟩
         f α                          ∎))

eloquence-corollary₀ : (f : Baire → ℕ)
                     → is-T-definable f
                     → is-continuous f
eloquence-corollary₀ f d = eloquent-functions-are-continuous
                            f
                            (eloquence-theorem f d)

eloquence-corollary₁ : (f : Baire → ℕ)
                     → is-T-definable f
                     → is-uniformly-continuous (C-restriction f)
eloquence-corollary₁ f d = eloquent-functions-are-UC
                            (C-restriction f)
                            (restriction-is-eloquent f (eloquence-theorem f d))
