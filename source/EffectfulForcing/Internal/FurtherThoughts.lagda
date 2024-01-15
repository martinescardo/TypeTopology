Martin Escardo, Vincent Rahli, Bruno da Rocha Paiva, Ayberk Tosun 20 May 2023

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.Internal.FurtherThoughts where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Continuity
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.SystemT using (type ; ι ; _⇒_ ; 〖_〗)
open import EffectfulForcing.MFPSAndVariations.LambdaCalculusVersionOfMFPS
                              using (B〖_〗 ; Kleisli-extension ; zero' ; succ' ; rec')
open import EffectfulForcing.MFPSAndVariations.Church
                              hiding (B⋆【_】 ; ⟪⟫⋆ ; _‚‚⋆_ ; B⋆⟦_⟧ ; dialogue-tree⋆)
open import EffectfulForcing.Internal.Internal hiding (B⋆⟦_⟧ ; dialogue-tree⋆)
open import EffectfulForcing.Internal.External
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.Internal.Subst
open import EffectfulForcing.Internal.Correctness
open import UF.Base using (transport₂ ; transport₃ ; ap₂ ; ap₃)

\end{code}

\begin{code}

B⋆⟦_⟧ : {Γ : Cxt} {σ : type} {A : Type}
      → T Γ σ
      → B⋆【 Γ 】 A
      → B⋆〖 σ 〗 A
B⋆⟦ Zero      ⟧  _ = zero⋆
B⋆⟦ Succ t    ⟧ xs = succ⋆ (B⋆⟦ t ⟧ xs)
B⋆⟦ Rec f g t ⟧ xs = rec⋆ (B⋆⟦ f ⟧ xs) (B⋆⟦ g ⟧ xs) (B⋆⟦ t ⟧ xs)
B⋆⟦ ν i       ⟧ xs = xs i
B⋆⟦ ƛ t       ⟧ xs = λ x → B⋆⟦ t ⟧ (xs ‚‚⋆ x)
B⋆⟦ t · u     ⟧ xs = (B⋆⟦ t ⟧ xs) (B⋆⟦ u ⟧ xs)

B⋆⟦_⟧₀ : {σ : type} {A : Type} → T₀ σ → B⋆〖 σ 〗 A
B⋆⟦ t ⟧₀ = B⋆⟦ t ⟧ ⟪⟫⋆

dialogue-tree⋆ : {A : Type} → T₀ ((ι ⇒ ι) ⇒ ι) → B⋆ ℕ A
dialogue-tree⋆ t = B⋆⟦ t ⟧₀ generic⋆

\end{code}

We are not using the following relarion R⋆ for the moment, but we want
to keep it around for a bit to maybe relate it to Rnorm and R.

\begin{code}

R⋆ : {σ : type} → Baire → 〖 σ 〗 → T₀ (B-type〖 σ 〗 ((ι ⇒ ι) ⇒ ι)) → Type
R⋆ {ι}     α n d  = n ＝ dialogue⋆ ⟦ d ⟧₀ α
R⋆ {σ ⇒ τ} α f f' = (x  : 〖 σ 〗)
                    (x' : T₀ σ)
                 → R⋆ {σ} α x ⌜ x' ⌝
--                 → Σ u ꞉ T₀ (B-type〖 τ 〗 ((ι ⇒ ι) ⇒ ι)) , (⟦ u ⟧ ＝ ⟦ f' · x' ⟧)
                 → R⋆ {τ} α (f x) (f' · ⌜ x' ⌝)
{-                    (x' : T₀ σ)
                 → R⋆ {σ} α x ⌜ x' ⌝
                 → R⋆ {τ} α (f x) (f' · ⌜ x' ⌝)-} -- would this be enough?

IB₀ : {A : type} → IB【 〈〉 】 A
IB₀ {A} ()

R⋆s : Baire → {Γ : Cxt}
  → 【 Γ 】 → IB【 Γ 】 ((ι ⇒ ι) ⇒ ι) → Type
R⋆s α {Γ} xs ys = {σ : type} (i : ∈Cxt σ Γ) → R⋆ α (xs i) (ys (∈Cxt-B-type i))

R⋆-preserves-⟦⟧' : {α : Baire} {σ : type}
                  (a : 〖 σ 〗) (t u : T₀ (B-type〖 σ 〗 ((ι ⇒ ι) ⇒ ι)))
                → ⟦ t ⟧₀ ＝ ⟦ u ⟧₀
                → R⋆ α a t
                → R⋆ α a u
R⋆-preserves-⟦⟧' {α} {ι} a t u e r = r ∙ ap (λ k → k (λ z α₁ → z) (λ φ x α₁ → φ (α₁ x) α₁) α) e
R⋆-preserves-⟦⟧' {α} {σ ⇒ σ₁} a t u e r x x' rx =
 R⋆-preserves-⟦⟧' (a x) (t · ⌜ x' ⌝) (u · ⌜ x' ⌝) (ap (λ x → x ⟦ ⌜ x' ⌝ ⟧₀) e) (r x x' rx)

R⋆-preserves-⟦⟧ : {α : Baire} {σ : type}
                  (a : 〖 σ 〗) (t u : T₀ σ)
                → ⟦ ⌜_⌝ {〈〉} {σ} {(ι ⇒ ι) ⇒ ι} t ⟧₀ ＝ ⟦ ⌜ u ⌝ ⟧₀
                → R⋆ α a ⌜ t ⌝
                → R⋆ α a ⌜ u ⌝
R⋆-preserves-⟦⟧ {α} {σ} a t u e r = R⋆-preserves-⟦⟧' a ⌜ t ⌝ ⌜ u ⌝ e r

R⋆s-Sub,, : {α : Baire} {Γ : Cxt} {σ : type}
            (xs : 【 Γ 】) (x : 〖 σ 〗)
            (ys : IB【 Γ 】 ((ι ⇒ ι) ⇒ ι)) (y : T₀ (B-type〖 σ 〗 ((ι ⇒ ι) ⇒ ι)))
          → R⋆s α xs ys
          → R⋆ α x y
          → R⋆s α (xs ‚ x) (Sub,, ys y)
R⋆s-Sub,, {α} {Γ} {σ} xs x ys y rs r {.σ} (∈Cxt0 .Γ) = r
R⋆s-Sub,, {α} {Γ} {σ} xs x ys y rs r {τ} (∈CxtS .σ i) = rs i

R⋆s-⌜Sub,,⌝ : {α : Baire} {Γ : Cxt} {σ : type}
            (xs : 【 Γ 】) (x : 〖 σ 〗)
            (ys : Sub₀ Γ) (y : T₀ σ)
          → R⋆s α xs (⌜Sub⌝ ys)
          → R⋆ α x ⌜ y ⌝
          → R⋆s α (xs ‚ x) (⌜Sub⌝ (Sub,, ys y))
R⋆s-⌜Sub,,⌝ {α} {Γ} {σ} xs x ys y rs r {.σ} (∈Cxt0 .Γ) = r
R⋆s-⌜Sub,,⌝ {α} {Γ} {σ} xs x ys y rs r {τ} (∈CxtS .σ i) = p (rs i)
 where
  p : (ri : R⋆ α (xs i) (⌜Sub⌝ ys (∈Cxt-B-type i)))
    → R⋆ α (xs i) (⌜Sub⌝ (Sub,, ys y) (∈CxtS (B-type〖 σ 〗 ((ι ⇒ ι) ⇒ ι)) (∈Cxt-B-type i)))
  p ri with ∈Cxt-B-context'' {B-type〖 τ 〗 ((ι ⇒ ι) ⇒ ι)} (∈Cxt-B-type i)
  ... | τ₁ , e , j , z with ＝B-type e
  ... | refl with ＝type-refl e
  ... | refl with ＝∈Cxt-B-type i j z
  ... | refl = ri

-- derived from Rnorm-lemma and main-lemma
R⋆-main-lemma-ι : (t : T₀ ι)
                 (α : Baire)
               → R⋆ α ⟦ t ⟧₀ ⌜ t ⌝
R⋆-main-lemma-ι t α =
 ⟦ t ⟧₀
  ＝⟨ main-lemma t α ⟨⟩ ⟪⟫ (λ ()) ⟩
 dialogue B⟦ t ⟧₀ α
  ＝⟨ dialogues-agreement B⟦ t ⟧₀ α ⟩
 dialogue⋆ (church-encode B⟦ t ⟧₀) α
  ＝⟨ ≡-sym (Rnorm-lemmaι t α _ _ e) ⟩
 dialogue⋆ ⟦ ⌜ t ⌝ ⟧₀ α
  ∎
 where
  e : (a b : ℕ) → a ＝ b → α a ＝ α b
  e a .a refl = refl

{-

-- Is that even provable? (we don't need it, but we want to explore this)
RnormAs : {σ : type} (d : B〖 σ 〗) (t : {A : type} → T₀ (B-type〖 σ 〗 A)) (α : Baire)
         → Rnorm d t ↔ (Σ x ꞉ 〖 σ 〗 , ((R α x d) × (R⋆ α x t)))
RnormAs {ι} d t α = c1 , c2
 where
  c0 : is-dialogue-for d t → dialogue d α ＝ dialogue⋆ ⟦ t ⟧₀ α
  c0 i =
   dialogue d α
    ＝⟨ dialogues-agreement d α ⟩
   dialogue⋆ (church-encode d) α
    ＝⟨ ap (λ k → k α) (i ((ι ⇒ ι) ⇒ ι) (λ z α → z) (λ φ x α → φ (α x) α) ⁻¹) ⟩
   dialogue⋆ ⟦ t ⟧₀ α
    ∎

  c1 : is-dialogue-for d t → (Σ n ꞉ ℕ , ((n ＝ dialogue d α ) × (n ＝ dialogue⋆ ⟦ t ⟧₀ α)))
  c1 h = dialogue d α , refl , c0 h

  c2 : Σ x ꞉ ℕ , (x ＝ dialogue d α) × (x ＝ dialogue⋆ ⟦ t ⟧₀ α) → is-dialogue-for d t
  c2 (x , a , b) A η' β' = {!!}
RnormAs {σ ⇒ σ₁} d t α = {!!} , {!!}

{--
Can we get R⋆'s main lemma from R's and Rnorm's:

  ⟦ t ⟧ ＝ dialogue B⟦ t ⟧ α
→ ⟦ ⌜ t ⌝ ⟧₀ ≣⋆ church-encode B⟦ t ⟧
→ ⟦ t ⟧ ＝ dialogue⋆ ⟦ ⌜ t ⌝ ⟧₀ α

----

→ dialogue B⟦ t ⟧ α ＝ dialogue⋆ church-encode B⟦ t ⟧ α
--}

-}

\end{code}
