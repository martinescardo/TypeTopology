Vincent Rahli 2015, 20 May 2023

The original version of effectful forcing used system T extended with
oracles. Here we avoid the oracles by modifying the logical
relation. We work with the lambda calculus version of system T. The
original 2015 version was for the combinatory version of system T.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.Internal.External where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Continuity
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.SystemT using (type ; ι ; _⇒_ ; 〖_〗)
open import EffectfulForcing.MFPSAndVariations.LambdaCalculusVersionOfMFPS using (B〖_〗 ; Kleisli-extension ; zero' ; succ' ; rec')
open import EffectfulForcing.Internal.SystemT

B【_】 : (Γ : Cxt) → Type
B【 Γ 】 = {σ : type} (i : ∈Cxt σ Γ) → B〖 σ 〗

⟪⟫ : B【 〈〉 】
⟪⟫ ()

_‚‚_ : {Γ : Cxt} {σ : type} → B【 Γ 】 → B〖 σ 〗 → B【 Γ ,, σ 】
(xs ‚‚ x) (∈Cxt0 _) = x
(xs ‚‚ x) (∈CxtS _ i) = xs i

infixl 6 _‚‚_

B⟦_⟧ : {Γ : Cxt} {σ : type} → T Γ σ → B【 Γ 】 → B〖 σ 〗
B⟦ Zero      ⟧  _ = zero'
B⟦ Succ t    ⟧ xs = succ' (B⟦ t ⟧ xs)
B⟦ Rec f g t ⟧ xs = rec' (B⟦ f ⟧ xs) (B⟦ g ⟧ xs) (B⟦ t ⟧ xs)
B⟦ ν i       ⟧ xs = xs i
B⟦ ƛ t       ⟧ xs = λ x → B⟦ t ⟧ (xs ‚‚ x)
B⟦ t · u     ⟧ xs = (B⟦ t ⟧ xs) (B⟦ u ⟧ xs)

B⟦_⟧₀ : {σ : type} → T₀ σ → B〖 σ 〗
B⟦ t ⟧₀ = B⟦ t ⟧ ⟪⟫

dialogue-tree : T₀((ι ⇒ ι) ⇒ ι) → B ℕ
dialogue-tree t = B⟦ t ⟧₀ generic

R : {σ : type} → Baire → 〖 σ 〗 → B〖 σ 〗 → Type
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

Rs : {Γ : Cxt} → Baire → 【 Γ 】 → B【 Γ 】 → Type
Rs {Γ} α xs ys = {σ : type} (i : ∈Cxt σ Γ) → R {σ} α (xs i) (ys i)

main-lemma : {Γ : Cxt}
             {σ : type} (t : T Γ σ)
             (α : Baire)
             (xs : 【 Γ 】)
             (ys : B【 Γ 】)
           → Rs α xs ys
           → R α (⟦ t ⟧ xs) (B⟦ t ⟧ ys)

main-lemma Zero α xs ys cr = refl

main-lemma (Succ t) α xs ys cr =
 succ (⟦ t ⟧ xs)      ＝⟨ ap succ (main-lemma t α xs ys cr) ⟩
 succ (dialogue (B⟦ t ⟧ ys) α) ＝⟨ decode-α-is-natural succ (B⟦ t ⟧ ys) α ⟩
 decode α (succ' (B⟦ t ⟧ ys))  ∎

main-lemma (Rec {_} {σ} a b t) α xs ys cr =
 R-kleisli-lemma σ α g g' rg (⟦ t ⟧ xs) (B⟦ t ⟧ ys) (main-lemma t α xs ys cr)
  where
   g : ℕ → 〖 σ 〗
   g = rec (⟦ a ⟧ xs) (⟦ b ⟧ xs)

   g' : ℕ → B〖 σ 〗
   g' = rec (B⟦ a ⟧ ys ∘ η) (B⟦ b ⟧ ys)

   rg : (k : ℕ) → R α (g k) (g' k)
   rg zero     = main-lemma b α xs ys cr
   rg (succ k) = main-lemma a α xs ys cr k (η k) refl (g k) (g' k) (rg k)

main-lemma (ν i) α xs ys cr = cr i

main-lemma {Γ} {σ ⇒ τ} (ƛ t) α xs ys cr = lemma
 where
  lemma : (x : 〖 σ 〗)
          (y : B〖 σ 〗)
        → R α x y
        → R α (⟦ t ⟧ (xs ‚ x)) (B⟦ t ⟧ (ys ‚‚ y))
  lemma x y r = main-lemma t α (xs ‚ x) (ys ‚‚ y) h
    where
      h : {σ₁ : type} (i : ∈Cxt σ₁ (Γ ,, σ)) → R α ((xs ‚ x) i) ((ys ‚‚ y) i)
      h {σ₁} (∈Cxt0 .Γ) = r
      h {σ₁} (∈CxtS .σ i) = cr i

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
 dialogue (dialogue-tree t) α  ∎
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
         ⟦ t ⟧₀ α                     ＝⟨ ap (λ - → - α) r ⟩
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
