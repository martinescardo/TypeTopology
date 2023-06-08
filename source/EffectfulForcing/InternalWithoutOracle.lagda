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

data subCxt : {n : ℕ} (Γ₁ : Cxt n) {m : ℕ} (Γ₂ : Cxt m) → Type where
  subCxt0 : {m : ℕ} (Γ₂ : Cxt m) → subCxt {0} 〈〉 {m} Γ₂
  subCxtS : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (σ : type)
            → subCxt Γ₁ Γ₂
            → subCxt (Γ₁ , σ) (Γ₂ , σ)

subFin : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} → subCxt Γ₁ Γ₂ → Fin n → Fin m
subFin {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} (subCxtS σ sub) Fin.𝟎 = Fin.𝟎
subFin {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} (subCxtS σ sub) (Fin.suc f) = Fin.suc (subFin sub f)

sub[] : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (i : Fin n) (s : subCxt Γ₁ Γ₂) → Γ₁ [ i ] ＝ Γ₂ [ subFin s i ]
sub[] {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} Fin.𝟎 (subCxtS σ sub) = refl
sub[] {(succ n)} {(Γ₁ , σ)} {(succ m)} {(Γ₂ , σ)} (Fin.suc i) (subCxtS σ sub) = sub[] i sub

Tweaken : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} {σ : type}
          → subCxt Γ₁ Γ₂
          → T Γ₁ σ
          → T Γ₂ σ
Tweaken {n} {Γ₁} {m} {Γ₂} {.ι} sub Zero = Zero
Tweaken {n} {Γ₁} {m} {Γ₂} {.(ι ⇒ ι)} sub Succ = Succ
Tweaken {n} {Γ₁} {m} {Γ₂} {.((ι ⇒ _ ⇒ _) ⇒ _ ⇒ ι ⇒ _)} sub Rec = Rec
Tweaken {n} {Γ₁} {m} {Γ₂} {.(Γ₁ [ i ])} sub (ν i) = transport⁻¹ (λ σ → T Γ₂ σ) (sub[] i sub) (ν _)
Tweaken {n} {Γ₁} {m} {Γ₂} {σ ⇒ τ} sub (ƛ t) = ƛ (Tweaken (subCxtS σ sub) t)
Tweaken {n} {Γ₁} {m} {Γ₂} {σ} sub (t · t₁) = Tweaken sub t · Tweaken sub t₁

⌜star⌝ : {X Y A : type} {n : ℕ} {Γ : Cxt n}
                    → T Γ ((⌜B⌝ (X ⇒ Y) A) ⇒ ⌜B⌝ X A ⇒ ⌜B⌝ Y A)
⌜star⌝ =
 ƛ (ƛ (⌜kleisli-extension⌝ · ƛ (⌜B-functor⌝ · ƛ (ν Fin.𝟎 · ν (Fin.suc Fin.𝟎)) · ν (Fin.suc (Fin.suc Fin.𝟎))) · ν Fin.𝟎))

-- λη.λβ.t (λs.f (λg.η(g s)) β) β
dapp : {A : type} {σ τ : type} {n : ℕ} {Γ : Cxt n}
       (f : T Γ (⌜B⌝ (σ ⇒ τ) A)) (t : T Γ (⌜B⌝ σ A)) → T Γ (⌜B⌝ τ A)
dapp {A} {σ} {τ} {n} {Γ} f t = ⌜star⌝ · f · t

-- generalize to open terms
⌜R⌝ : ({A} σ : type) → T₀ (⌜B⌝ σ A) → B⋆〖 σ 〗 〖 A 〗 → Type
⌜R⌝ ι       t d = ⟦ t ⟧₀ ＝ d
⌜R⌝ {A} (σ ⇒ τ) f g = (t : T₀ (⌜B⌝ σ A))
                 (d : B⋆〖 σ 〗 〖 A 〗)
               → ⌜R⌝ σ t d
               → ⌜R⌝ τ (dapp f t) (g d)

{-
⌜R⌝ : {n : ℕ} (Γ : Cxt n) {A : type} (σ : type) → T Γ (⌜B⌝ σ A) → B⋆〖 σ 〗 〖 A 〗 → Type
⌜R⌝ {n} Γ ι       t d = ⟦ t ⟧ ? ＝ d
⌜R⌝ {n} Γ {A} (σ ⇒ τ) f g = (t : T₀ (⌜B⌝ σ A))
                 (d : B⋆〖 σ 〗 〖 A 〗)
               → ⌜R⌝ Γ σ t d
               → ⌜R⌝ Γ τ (dapp f t) (g d)
-}

CXT : {n : ℕ} (Γ : Cxt n) (A : type) → Type
CXT Γ A = (i : Fin _) → T₀ (⌜B⌝ (Γ [ i ]) A)

⌜Rs⌝ : {n : ℕ} {Γ : Cxt n} {A : type}
    → CXT Γ A → B⋆【 Γ 】 〖 A 〗 → Type
⌜Rs⌝ {n} {Γ} xs ys = (i : Fin n) → ⌜R⌝ (Γ [ i ]) (xs i) (ys i)

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
                    (x' : T₀ (⌜B⌝ σ ((ι ⇒ ι) ⇒ ι)))
                 → R⋆ {σ} α x x'
                 → R⋆ {τ} α (f x) (dapp f' x')


\end{code}
