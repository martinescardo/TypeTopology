This is an adaptation of WithoutOracle where we're using SystemT instead of CombinatryT.

Alternatively, it can be seen as adaptation of LambdaCalculusVersionOfMFPS, where we use
a slighlty different relation instead of using T'

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.WithoutOracleLambda where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import MLTT.Athenian using (Fin)
open import UF.Base
open import EffectfulForcing.Combinators
open import EffectfulForcing.Continuity
open import EffectfulForcing.Dialogue
open import EffectfulForcing.SystemT

open Fin

B〖_〗 : type → 𝓤₀ ̇
B〖 ι 〗     = B ℕ
B〖 σ ⇒ τ 〗 = B〖 σ 〗 → B〖 τ 〗

Kleisli-extension : {X : 𝓤₀ ̇ } {σ : type} → (X → B〖 σ 〗) → B X → B〖 σ 〗
Kleisli-extension {X} {ι}     = kleisli-extension
Kleisli-extension {X} {σ ⇒ τ} = λ g d s → Kleisli-extension {X} {τ} (λ x → g x s) d

zero' : B ℕ
zero' = η zero

succ' : B ℕ → B ℕ
succ' = B-functor succ

rec' : {σ : type} → (B ℕ → B〖 σ 〗 → B〖 σ 〗) → B〖 σ 〗 → B ℕ → B〖 σ 〗
rec' f x = Kleisli-extension(rec (f ∘ η) x)


B【_】 : {n : ℕ} (Γ : Cxt n) → Type
B【 Γ 】 = (i : Fin _) → B〖 (Γ [ i ]) 〗

⟪⟫ : B【 〈〉 】
⟪⟫ ()

_‚‚_ : {n : ℕ} {Γ : Cxt n} {σ : type} → B【 Γ 】 → B〖 σ 〗 → B【 Γ , σ 】
(xs ‚‚ x) 𝟎       = x
(xs ‚‚ x) (suc i) = xs i

infixl 6 _‚‚_

B⟦_⟧ : {n : ℕ} {Γ : Cxt n} {σ : type} → T Γ σ → B【 Γ 】 → B〖 σ 〗
B⟦ Zero  ⟧  _ = zero'
B⟦ Succ  ⟧  _ = succ'
B⟦ Rec   ⟧  _ = rec'
B⟦ ν i   ⟧ xs = xs i
B⟦ ƛ t   ⟧ xs = λ x → B⟦ t ⟧ (xs ‚‚ x)
B⟦ t · u ⟧ xs = (B⟦ t ⟧ xs) (B⟦ u ⟧ xs)

B⟦_⟧₀ : {σ : type} → T₀ σ → B〖 σ 〗
B⟦ t ⟧₀ = B⟦ t ⟧ ⟪⟫

dialogue-tree : T₀((ι ⇒ ι) ⇒ ι) → B ℕ
dialogue-tree t = B⟦ t ⟧₀ generic

R : {σ : type} → Baire → 〖 σ 〗 → B〖 σ 〗 → Set
R {ι}     α n d  = n ＝ dialogue d α
R {σ ⇒ τ} α f f' = (x  : 〖 σ 〗)
                   (x' : B〖 σ 〗)
                 → R {σ} α x x'
                 → R {τ} α (f x) (f' x')

R-kleisli-lemma : (σ : type)
                  (α : Baire)
                  (g  : ℕ → 〖 σ 〗)
                  (g' : ℕ → B〖 σ 〗)
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

Rs : {n : ℕ} {Γ : Cxt n} → Baire → 【 Γ 】 → B【 Γ 】 → Type
Rs {n} {Γ} α xs ys = (i : Fin n) → R {Γ [ i ]} α (xs i) (ys i)

main-lemma : {n : ℕ} {Γ : Cxt n} {σ : type} (t : T Γ σ) (α : Baire)
             (xs : 【 Γ 】)
             (ys : B【 Γ 】)
             → Rs α xs ys
             → R α (⟦ t ⟧ xs) (B⟦ t ⟧ ys)

main-lemma Zero α xs ys cr = refl

main-lemma Succ α xs ys cr = λ n n' rn →
 succ n               ＝⟨ ap succ rn ⟩
 succ (dialogue n' α) ＝⟨ decode-α-is-natural succ n' α ⟩
 decode α (succ' n')  ∎

main-lemma (Rec {_} {_} {σ}) α xs ys cr = lemma
 where
  lemma :  (f  : ℕ → 〖 σ 〗 → 〖 σ 〗) (f' : B ℕ → B〖 σ 〗 → B〖 σ 〗)
        → R {ι ⇒ σ ⇒ σ} α f f'
        → (x  : 〖 σ 〗) (y : B〖 σ 〗)
        → R {σ} α x y
        → (n  : ℕ) (n' : B ℕ)
        → R {ι} α n n'
        → R {σ} α (rec f x n) (Kleisli-extension (rec (f' ∘ η) y) n')
  lemma f f' rf x y rx = R-kleisli-lemma σ α g g' rg
    where
      g : ℕ → 〖 σ 〗
      g k = rec f x k

      g' : ℕ → B〖 σ 〗
      g' k = rec (f' ∘ η) y k

      rg : (k : ℕ) → R α (g k) (g' k)
      rg zero     = rx
      rg (succ k) = rf k (η k) refl (g k) (g' k) (rg k)

main-lemma (ν i) α xs ys cr = cr i

main-lemma {n} {Γ} {σ ⇒ τ} (ƛ t) α xs ys cr = lemma
  where
    lemma : (x : 〖 σ 〗) (y : B〖 σ 〗)
            → R α x y
            → R α (⟦ t ⟧ (xs ‚ x)) (B⟦ t ⟧ (ys ‚‚ y))
    lemma x y r = main-lemma t α (xs ‚ x) (ys ‚‚ y) h
      where
        h : (i : Fin (succ n)) → R α ((xs ‚ x) i) ((ys ‚‚ y) i)
        h 𝟎       = r
        h (suc i) = cr i

main-lemma (t · u) α xs ys cr = IH-t (⟦ u ⟧ xs) (B⟦ u ⟧ ys) IH-u
 where
  IH-t : (x  : 〖 _ 〗)
         (y : B〖 _ 〗)
       → R α x y
       → R α (⟦ t ⟧ xs x) (B⟦ t ⟧ ys y)
  IH-t = main-lemma t α xs ys cr

  IH-u : R α (⟦ u ⟧ xs) (B⟦ u ⟧ ys)
  IH-u = main-lemma u α xs ys cr

main-lemma-closed : {σ : type} (t : T₀ σ) (α : Baire)
                    → R α ⟦ t ⟧₀ (B⟦ t ⟧₀)
main-lemma-closed {σ} t α = main-lemma t α ⟨⟩ ⟪⟫ (λ())

dialogue-tree-correct : (t : T₀ ((ι ⇒ ι) ⇒ ι))
                        (α : Baire)
                      → ⟦ t ⟧₀ α ＝ dialogue (dialogue-tree t) α
dialogue-tree-correct t α =
 ⟦ t ⟧₀ α                      ＝⟨ main-lemma-closed t α α generic lemma ⟩
 dialogue (B⟦ t ⟧₀ generic) α  ＝⟨ refl ⟩
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
                  → T-definable f
                  → eloquent f
eloquence-theorem f (t , r) =
 (dialogue-tree t ,
  (λ α → dialogue (dialogue-tree t) α ＝⟨ (dialogue-tree-correct t α)⁻¹ ⟩
         ⟦ t ⟧₀ α                      ＝⟨ ap (λ - → - α) r ⟩
         f α                          ∎))

eloquence-corollary₀ : (f : Baire → ℕ)
                     → T-definable f
                     → is-continuous f
eloquence-corollary₀ f d = eloquent-functions-are-continuous
                            f
                            (eloquence-theorem f d)

eloquence-corollary₁ : (f : Baire → ℕ)
                     → T-definable f
                     → is-uniformly-continuous (C-restriction f)
eloquence-corollary₁ f d = eloquent-functions-are-UC
                            (C-restriction f)
                            (restriction-is-eloquent f (eloquence-theorem f d))
