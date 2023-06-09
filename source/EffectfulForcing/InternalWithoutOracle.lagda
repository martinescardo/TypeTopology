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
open import UF.Base

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

R⋆₀ : (σ : type) → B⋆〖 σ 〗 (B ℕ) → B〖 σ 〗 → Type
R⋆₀ ι       x y = church-decode x ≣ y
R⋆₀ (σ ⇒ τ) f g = (x : B⋆〖 σ 〗 (B ℕ))
                 (y : B〖 σ 〗)
               → R⋆₀ σ x y
               → R⋆₀ τ (f x) (g y)


{-
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

data ⊆Γ : {n : ℕ} (Γ₁ : Cxt n) {m : ℕ} (Γ₂ : Cxt m) → Type where
  ⊆Γ0 : ⊆Γ {0} 〈〉 {0} 〈〉
  ⊆ΓR : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (σ : type)
      → ⊆Γ Γ₁ Γ₂
      → ⊆Γ Γ₁ (Γ₂ , σ)
  ⊆ΓS : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (σ : type)
      → ⊆Γ Γ₁ Γ₂
      → ⊆Γ (Γ₁ , σ) (Γ₂ , σ)

⊆Γ-refl : {n : ℕ} (Γ : Cxt n) → ⊆Γ Γ Γ
⊆Γ-refl {zero} 〈〉 = ⊆Γ0
⊆Γ-refl {succ n} (Γ , τ) = ⊆ΓS τ (⊆Γ-refl Γ)

⊆Γ-trans : {n₁ : ℕ} {Γ₁ : Cxt n₁} {n₂ : ℕ} {Γ₂ : Cxt n₂} {n₃ : ℕ} {Γ₃ : Cxt n₃}
         → ⊆Γ Γ₁ Γ₂ → ⊆Γ Γ₂ Γ₃ → ⊆Γ Γ₁ Γ₃
⊆Γ-trans {.0} {.〈〉} {.0} {.〈〉} {n₃} {Γ₃} ⊆Γ0 q = q
⊆Γ-trans {n₁} {Γ₁} {.(succ _)} {Γ₂ , σ} {.(succ _)} {Γ₃ , σ₁} (⊆ΓR σ h) (⊆ΓR σ₁ q) =
 ⊆Γ-trans h (⊆ΓR σ₁ (⊆Γ-trans (⊆ΓR σ (⊆Γ-refl Γ₂)) q))
⊆Γ-trans {n₁} {Γ₁} {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} (⊆ΓR σ h) (⊆ΓS .σ q) =
 ⊆ΓR σ (⊆Γ-trans h q)
⊆Γ-trans {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ₁)} (⊆ΓS σ h) (⊆ΓR σ₁ q) =
 ⊆ΓR σ₁ (⊆Γ-trans (⊆ΓS σ h) q)
⊆Γ-trans {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} (⊆ΓS σ h) (⊆ΓS .σ q) =
 ⊆ΓS σ (⊆Γ-trans h q)

-- From the standard library. Is that defined somewhere? Can we import it from the standard library?
data _≤_ : ℕ → ℕ → Type where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → succ m ≤ succ n

¬s≤n : (n : ℕ) → ¬ (succ n ≤ n)
¬s≤n (succ n) (s≤s h) = ¬s≤n n h

n≤s : (n : ℕ) → n ≤ succ n
n≤s zero = z≤n
n≤s (succ n) = s≤s (n≤s n)

≤-trans : {n1 n2 n3 : ℕ} → n1 ≤ n2 → n2 ≤ n3 → n1 ≤ n3
≤-trans {.zero} {n2} {n3} z≤n q = z≤n
≤-trans {.(succ _)} {.(succ _)} {.(succ _)} (s≤s h) (s≤s q) = s≤s (≤-trans h q)

⊆Γ≤ : {n : ℕ} {Γ : Cxt n} {m : ℕ} {Δ : Cxt m} → ⊆Γ Γ Δ → n ≤ m
⊆Γ≤ {.0} {.〈〉} {.0} {.〈〉} ⊆Γ0 = z≤n
⊆Γ≤ {n} {Γ} {succ m} {.(_ , σ)} (⊆ΓR σ h) = ≤-trans (⊆Γ≤ h) (n≤s m)
⊆Γ≤ {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} (⊆ΓS σ h) = s≤s (⊆Γ≤ h)

¬⊆Γ, : {n : ℕ} {Γ : Cxt n} {τ : type} → ¬ ⊆Γ (Γ , τ) Γ
¬⊆Γ, {n} {Γ} {τ} h = ¬s≤n n (⊆Γ≤ h)

⊆〈〉 : {n : ℕ} (Γ : Cxt n) → ⊆Γ 〈〉 Γ
⊆〈〉 {zero} 〈〉 = ⊆Γ0
⊆〈〉 {succ n} (Γ , τ) = ⊆ΓR τ (⊆〈〉 Γ)

⊆ΓFin : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} → ⊆Γ Γ₁ Γ₂ → Fin n → Fin m
⊆ΓFin {n} {Γ₁} {.(succ _)} {.(_ , σ)} (⊆ΓR σ h) i = Fin.suc (⊆ΓFin h i)
⊆ΓFin {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} (⊆ΓS σ h) Fin.𝟎 = Fin.𝟎
⊆ΓFin {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} (⊆ΓS σ h) (Fin.suc i) = Fin.suc (⊆ΓFin h i)

⊆Γ[] : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (i : Fin n) (s : ⊆Γ Γ₁ Γ₂) → Γ₁ [ i ] ＝ Γ₂ [ ⊆ΓFin s i ]
⊆Γ[] {n} {Γ₁} {.(succ _)} {.(_ , σ)} i (⊆ΓR σ s) = ⊆Γ[] i s
⊆Γ[] {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} Fin.𝟎 (⊆ΓS σ s) = refl
⊆Γ[] {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} (Fin.suc i) (⊆ΓS σ s) = ⊆Γ[] i s

weaken : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} {σ : type}
          → ⊆Γ Γ₁ Γ₂
          → T Γ₁ σ
          → T Γ₂ σ
weaken {n} {Γ₁} {m} {Γ₂} {_} sub Zero = Zero
weaken {n} {Γ₁} {m} {Γ₂} {_} sub Succ = Succ
weaken {n} {Γ₁} {m} {Γ₂} {_} sub Rec = Rec
weaken {n} {Γ₁} {m} {Γ₂} {.(Γ₁ [ i ])} sub (ν i) = transport⁻¹ (λ σ → T Γ₂ σ) (⊆Γ[] i sub) (ν (⊆ΓFin sub i))
weaken {n} {Γ₁} {m} {Γ₂} {σ ⇒ τ} sub (ƛ t) = ƛ (weaken (⊆ΓS σ sub) t)
weaken {n} {Γ₁} {m} {Γ₂} {σ} sub (t · t₁) = weaken sub t · weaken sub t₁

weaken₀ : {n : ℕ} {Γ : Cxt n} {σ : type}
        → T₀ σ
        → T Γ σ
weaken₀ {n} {Γ} {σ} t = weaken (⊆〈〉 Γ) t

⊆ΓFin-refl : {n : ℕ} {Γ₁ Γ₂ : Cxt n} (i : Fin n) (s : ⊆Γ Γ₁ Γ₂) → Γ₁ ＝ Γ₂ → ⊆ΓFin s i ＝ i
⊆ΓFin-refl {.(succ _)} {Γ₁ , τ} {.Γ₁ , .τ} i (⊆ΓR .τ s) refl = 𝟘-elim (¬⊆Γ, s)
⊆ΓFin-refl {.(succ _)} {Γ₁ , τ} {.(Γ₂ , τ)} Fin.𝟎 (⊆ΓS {Γ₂ = Γ₂} .τ s) e = refl
⊆ΓFin-refl {.(succ _)} {Γ₁ , τ} {.(Γ₂ , τ)} (Fin.suc i) (⊆ΓS {Γ₂ = Γ₂} .τ s) e =
 ap Fin.suc (⊆ΓFin-refl i s (pr₁ (from-×-＝' e)))

-- Can't we prove that without K?
transport⁻¹-T-type : {n : ℕ} {Γ : Cxt n} {σ : type} (e : σ ＝ σ) (t : T Γ σ) → transport⁻¹ (T Γ) e t ＝ t
transport⁻¹-T-type {n} {Γ} {σ} e t = {!!}

weaken₀-reflν : {n : ℕ} {Γ : Cxt n} (i : Fin n) (s : ⊆Γ Γ Γ)
                (e : (Γ [ i ]) ＝ (Γ [ ⊆ΓFin s i ]))
              → transport⁻¹ (T Γ) e (ν (⊆ΓFin s i)) ＝ ν i
weaken₀-reflν {n} {Γ} i s =
 transport⁻¹ (λ k → (e : (Γ [ i ]) ＝ (Γ [ k ])) → transport⁻¹ (T Γ) e (ν k) ＝ ν i)
             (⊆ΓFin-refl i s refl) λ e → transport⁻¹-T-type e _

weaken-id : {σ : type} {n : ℕ} {Γ : Cxt n} (s : ⊆Γ Γ Γ) (t : T Γ σ) → weaken s t ＝ t
weaken-id {_} {n} {Γ} s Zero = refl
weaken-id {_} {n} {Γ} s Succ = refl
weaken-id {_} {n} {Γ} s Rec = refl
weaken-id {.(Γ [ i ])} {n} {Γ} s (ν i) = {!!}
weaken-id {σ ⇒ τ} {n} {Γ} s (ƛ t) = ap ƛ (weaken-id (⊆ΓS σ s) t)
weaken-id {σ} {n} {Γ} s (t₁ · t₂) =
 weaken s t₁ · weaken s t₂
  ＝⟨ ap (λ k → k · weaken s t₂) (weaken-id s t₁) ⟩
 t₁ · weaken s t₂
  ＝⟨ ap (λ k → t₁ · k) (weaken-id s t₂) ⟩
 t₁ · t₂
  ∎

⊆Γ, : {n : ℕ} (Γ : Cxt n) (τ : type) → ⊆Γ Γ (Γ , τ)
⊆Γ, {n} Γ τ = ⊆ΓR τ (⊆Γ-refl Γ)

weaken, : {n : ℕ} {Γ : Cxt n} {σ : type} (τ : type)
        → T Γ σ
        → T (Γ , τ) σ
weaken, {n} {Γ} {σ} τ t = weaken {n} {Γ} {succ n} {Γ , τ} (⊆Γ, Γ τ) t

⌜star⌝ : {X Y A : type} {n : ℕ} {Γ : Cxt n}
                    → T Γ ((⌜B⌝ (X ⇒ Y) A) ⇒ ⌜B⌝ X A ⇒ ⌜B⌝ Y A)
⌜star⌝ =
 ƛ (ƛ (⌜kleisli-extension⌝
       · ƛ (⌜B-functor⌝
            · ƛ (ν Fin.𝟎 · ν (Fin.suc Fin.𝟎))
            · ν (Fin.suc (Fin.suc Fin.𝟎)))
       · ν Fin.𝟎))

-- λη.λβ.t (λs.f (λg.η(g s)) β) β
dapp : {A : type} {σ τ : type} {n : ℕ} {Γ : Cxt n}
       (f : T Γ (⌜B⌝ (σ ⇒ τ) A)) (t : T Γ (⌜B⌝ σ A)) → T Γ (⌜B⌝ τ A)
dapp {A} {σ} {τ} {n} {Γ} f t = ⌜star⌝ · f · t

-- indirect relation that relates
-- (1) internal terms of a Church-encoded dialogue tree type
-- (2) external Church-encoded dialogue trees
⌜R⌝ : ({A} σ : type) → T₀ (⌜B⌝ σ A) → B⋆〖 σ 〗 〖 A 〗 → Type
⌜R⌝ ι       t d = ⟦ t ⟧₀ ＝ d
⌜R⌝ {A} (σ ⇒ τ) f g = (t : T₀ (⌜B⌝ σ A))
                 (d : B⋆〖 σ 〗 〖 A 〗)
               → ⌜R⌝ σ t d
               → ⌜R⌝ τ (dapp f t) (g d)

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

-- 1st attempt
R⋆₁ : {σ : type} → Baire → 〖 σ 〗 → T₀ (⌜B⌝ σ ((ι ⇒ ι) ⇒ ι)) → Type
R⋆₁ {ι}     α n d  = n ＝ dialogue⋆ ⟦ d ⟧₀ α
R⋆₁ {σ ⇒ τ} α f f' = (x  : 〖 σ 〗)
                    (x' : T₀ (⌜B⌝ σ ((ι ⇒ ι) ⇒ ι)))
                 → R⋆₁ {σ} α x x'
                 → R⋆₁ {τ} α (f x) (dapp f' x')

⌜main-lemma⌝₁ : {n : ℕ} {Γ : Cxt n}
               {σ : type}
               (t : T Γ σ)
               (α : Baire)
               (xs : 【 Γ 】)
--               (ys : IB【 Γ 】 ((ι ⇒ ι) ⇒ ι))
--             → R⋆s α xs ys
             → R⋆₁ α (⟦ t ⟧ xs) (ƛ (ƛ (ƛ Zero))) --(close ⌜ t ⌝ ys)
⌜main-lemma⌝₁ {n} {Γ} {σ} t α xs {--ys rxys--} = {!!}

Sub₀ : {n : ℕ} (Γ : Cxt n) → Type
Sub₀ {n} Γ = (i : Fin n) → T₀ (Γ [ i ])

rmCxt : {n : ℕ} (Γ : Cxt (succ n)) (i : Fin (succ n)) → Cxt n
rmCxt {n} (Γ , τ) Fin.𝟎 = Γ
rmCxt {succ n} (Γ , τ) (Fin.suc i) = rmCxt Γ i , τ

suc-inj : {n : ℕ} (i j : Fin n) → Fin.suc i ＝ Fin.suc j → i ＝ j
suc-inj {n} i .i refl = refl

_=?_ : {n : ℕ} (i j : Fin n) → (i ＝ j) + ¬ (i ＝ j)
Fin.𝟎 =? Fin.𝟎 = inl refl
Fin.𝟎 =? Fin.suc j = inr (λ ())
Fin.suc i =? Fin.𝟎 = inr (λ ())
Fin.suc i =? Fin.suc j with i =? j
... | inl p = inl (ap Fin.suc p)
... | inr p = inr λ q → p (suc-inj i j q)

subν : {n : ℕ} {Γ : Cxt (succ n)} (i j : Fin (succ n)) → T₀ (Γ [ i ]) → T (rmCxt Γ i) (Γ [ j ])
subν {n} {Γ , τ} Fin.𝟎 Fin.𝟎 u = weaken₀ u
subν {n} {Γ , τ} Fin.𝟎 (Fin.suc j) u = ν j
subν {succ n} {Γ , τ} (Fin.suc i) Fin.𝟎 u = ν Fin.𝟎
subν {succ n} {Γ , τ} (Fin.suc i) (Fin.suc j) u = weaken, τ (subν i j u)

sub : {σ : type} {n : ℕ} {Γ : Cxt (succ n)} (i : Fin (succ n)) → T Γ σ → T₀ (Γ [ i ]) → T (rmCxt Γ i) σ
sub {_} {n} {Γ} i Zero u = Zero
sub {_} {n} {Γ} i Succ u = Succ
sub {_} {n} {Γ} i Rec u = Rec
sub {.(Γ [ j ])} {n} {Γ} i (ν j) u = subν i j u
sub {σ₁ ⇒ σ₂} {n} {Γ} i (ƛ t) u = ƛ (sub {σ₂} {succ n} {Γ , σ₁} (Fin.suc i) t u)
sub {σ} {n} {Γ} i (t₁ · t₂) u = sub i t₁ u · sub i t₂ u

sub₀ : {σ : type} {n : ℕ} {Γ : Cxt n} {τ : type} → T (Γ , τ) σ → T₀ τ → T Γ σ
sub₀ {σ} {n} {Γ} {τ} = sub Fin.𝟎

-- This can either be defined through a succession of applications
close-ap : {σ : type} {n : ℕ} {Γ : Cxt n} → T Γ σ → Sub₀ Γ → T₀ σ
close-ap {σ} {zero} {Γ} t s = t
close-ap {σ} {succ n} {Γ , τ} t s =
 close-ap (ƛ t · weaken₀ (s Fin.𝟎))
          (λ i → s (Fin.suc i))

-- ... or through substitution
close : {σ : type} {n : ℕ} {Γ : Cxt n} → T Γ σ → Sub₀ Γ → T₀ σ
close {σ} {zero} {Γ} t s = t
close {σ} {succ n} {Γ , τ} t s = close (sub₀ t (s Fin.𝟎)) (λ i → s (Fin.suc i))

close· : {σ τ : type} {n : ℕ} {Γ : Cxt n} → (t : T Γ (σ ⇒ τ)) (u : T Γ σ) (s : Sub₀ Γ)
      → close (t · u) s ＝ close t s · close u s
close· {σ} {τ} {zero} {Γ} t u s = refl
close· {σ} {τ} {succ n} {Γ} t u s = close· (sub₀ t (s Fin.𝟎)) (sub₀ u (s Fin.𝟎)) (λ i → s (Fin.suc i))

sub₀-weaken₀ : {σ τ : type} {n : ℕ} {Γ : Cxt n} (t : T₀ σ) (u : T₀ τ)
             → sub₀ (weaken₀ {succ n} {Γ , τ} {σ} t) u ＝ weaken₀ {n} {Γ} {σ} t
sub₀-weaken₀ {σ} {τ} {n} {Γ} t u = {!!}

-- to use in the lambda case
close₀ : {σ : type} {n : ℕ} {Γ : Cxt n} → (t : T₀ σ) (s : Sub₀ Γ)
      → close (weaken₀ {n} {Γ} {σ} t) s ＝ t
close₀ {σ} {zero} {〈〉} t s = weaken-id (⊆〈〉 〈〉) t
close₀ {σ} {succ n} {Γ , τ} t s = {!!}

-- Compared to R⋆₁, this version relates a T₀ (B-type〖 σ 〗 ((ι ⇒ ι) ⇒ ι))
-- instead of T₀ (⌜B⌝ σ ((ι ⇒ ι) ⇒ ι))
--
-- As opposed to ⌜R⌝, this is a more direct relation that relates
-- (1) the standard semantics
-- (2) internal terms of a Church-encoded dialogue tree type
R⋆ : {σ : type} → Baire → 〖 σ 〗 → T₀ (B-type〖 σ 〗 ((ι ⇒ ι) ⇒ ι)) → Type
R⋆ {ι}     α n d  = n ＝ dialogue⋆ ⟦ d ⟧₀ α
R⋆ {σ ⇒ τ} α f f' = (x  : 〖 σ 〗)
                    (x' : T₀ (B-type〖 σ 〗 ((ι ⇒ ι) ⇒ ι)))
                 → R⋆ {σ} α x x'
                 → R⋆ {τ} α (f x) (f' · x')
{-                    (x' : T₀ σ)
                 → R⋆ {σ} α x ⌜ x' ⌝
                 → R⋆ {τ} α (f x) (f' · ⌜ x' ⌝)-} -- would this be enough?

-- internal semantics of context as dialogue trees
IB【_】 : {n : ℕ} → Cxt n → type → Type
IB【 Γ 】 A = Sub₀ (B-context【 Γ 】 A)

T₀-B-context-sel : {A : type} {n : ℕ} (Γ : Cxt n) {i : Fin n}
                 → T₀ ((B-context【 Γ 】 A) [ i ])
                 → T₀ (B-type〖 Γ [ i ] 〗 A)
T₀-B-context-sel {A} {.(succ _)} Γ {Fin.𝟎} t = t
T₀-B-context-sel {A} {.(succ _)} Γ {Fin.suc i} t = T₀-B-context-sel (pr₁ Γ) t

R⋆s : Baire → {n : ℕ} {Γ : Cxt n}
  → 【 Γ 】 → IB【 Γ 】 ((ι ⇒ ι) ⇒ ι) → Type
R⋆s α {n} {Γ} xs ys = (i : Fin n) → R⋆ α (xs i) (T₀-B-context-sel Γ (ys i))

【sub】 : {n : ℕ} {Γ : Cxt n} (s : Sub₀ Γ) → 【 Γ 】
【sub】 {n} {Γ} s i = ⟦ s i ⟧₀

close-⌜zero⌝ : {σ : type} {n : ℕ} {Γ : Cxt n} (ys : IB【 Γ 】 σ)
            → close (⌜zero⌝ {σ}) ys ＝ ⌜zero⌝
close-⌜zero⌝ {σ} {zero} {Γ} ys = refl
close-⌜zero⌝ {σ} {succ n} {Γ , τ} ys = close-⌜zero⌝ (λ i → ys (Fin.suc i))

close-⌜succ⌝ : {σ : type} {n : ℕ} {Γ : Cxt n} (ys : IB【 Γ 】 σ)
            → close (⌜succ⌝ {σ}) ys ＝ ⌜succ⌝
close-⌜succ⌝ {σ} {zero} {Γ} ys = refl
close-⌜succ⌝ {σ} {succ n} {Γ , τ} ys = close-⌜succ⌝ (λ i → ys (Fin.suc i))

-- provable without knowing what d is?
succ-dialogue⋆ : (d : B⋆ ℕ (Baire → ℕ)) (α : Baire)
              → succ (dialogue⋆ d α) ＝ dialogue⋆ (succ⋆ d) α
succ-dialogue⋆ d α =
 succ (dialogue⋆ d α)
  ＝⟨ refl ⟩
 succ (d (λ z α → z) (λ φ x α → φ (α x) α) α)
  ＝⟨ {!!} ⟩
 d (λ x α → succ x) (λ φ x α → φ (α x) α) α
  ＝⟨ refl ⟩
 dialogue⋆ (succ⋆ d) α
  ∎

succ-dialogue⋆-aux' : {A : Type} {σ τ : type} (d : T₀ (⌜B⌝ σ ((τ ⇒ τ) ⇒ σ))) (α : 〖 τ 〗 → 〖 τ 〗) (f : 〖 σ 〗 → 〖 σ 〗)
                     (a : 〖 σ 〗 → (〖 τ 〗 → 〖 τ 〗) → 〖 σ 〗)
                     (b : (ℕ → (〖 τ 〗 → 〖 τ 〗) → 〖 σ 〗) → ℕ → (〖 τ 〗 → 〖 τ 〗) → 〖 σ 〗)
                   → f (⟦ d ⟧₀ a b α)
                     ＝ ⟦ d ⟧₀ (λ x → a (f x)) b α
succ-dialogue⋆-aux' {A} {σ} {τ} d α f a b = {!!}

{-
succ-dialogue⋆-aux : {A : Type} {σ τ : type} {n : ℕ} {Γ : Cxt n} (d : T Γ σ)
                     (g : 【 B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι) 】)
                     (α : 〖 τ 〗 → 〖 τ 〗)
                     (f : 〖 σ 〗 → 〖 σ 〗)
                     (a : 〖 σ 〗 → (〖 τ 〗 → 〖 τ 〗) → 〖 σ 〗)
                     (b : (ℕ → (〖 τ 〗 → 〖 τ 〗) → 〖 σ 〗) → ℕ → (〖 τ 〗 → 〖 τ 〗) → 〖 σ 〗)
                   → f (⟦ ⌜ d ⌝ ⟧ g a b α)
                     ＝ ⟦ ⌜ d ⌝ ⟧  g (λ x → a (f x)) b α
succ-dialogue⋆-aux = ?
-}

succ-dialogue⋆' : (d : T₀ (⌜B⌝ ι ((ι ⇒ ι) ⇒ ι))) (α : Baire)
              → succ (dialogue⋆ ⟦ d ⟧₀ α) ＝ dialogue⋆ (succ⋆ ⟦ d ⟧₀) α
succ-dialogue⋆' d α =
 succ (dialogue⋆ ⟦ d ⟧₀ α)
  ＝⟨ refl ⟩
 succ (⟦ d ⟧₀ (λ z α → z) (λ φ x α → φ (α x) α) α)
  ＝⟨ {!!} ⟩
 ⟦ d ⟧₀ (λ x α → succ x) (λ φ x α → φ (α x) α) α
  ＝⟨ refl ⟩
 dialogue⋆ (succ⋆ ⟦ d ⟧₀) α
  ∎

⌜main-lemma⌝ : {n : ℕ} {Γ : Cxt n}
              {σ : type}
              (t : T Γ σ)
              (α : Baire)
              (xs : 【 Γ 】)
              (ys : IB【 Γ 】 ((ι ⇒ ι) ⇒ ι))
            → R⋆s α xs ys
            → R⋆ α (⟦ t ⟧ xs) (close ⌜ t ⌝ ys)
⌜main-lemma⌝ {n} {Γ} {_} Zero α xs ys rxys = ap (λ k → dialogue⋆ ⟦ k ⟧₀ α) ((close-⌜zero⌝ ys) ⁻¹)
⌜main-lemma⌝ {n} {Γ} {_} Succ α xs ys rxys x y rxy =
 succ x
  ＝⟨ ap succ rxy ⟩
 succ (dialogue⋆ ⟦ y ⟧₀ α)
  ＝⟨ succ-dialogue⋆ ⟦ y ⟧₀ α ⟩
 dialogue⋆ (succ⋆ ⟦ y ⟧₀) α
  ＝⟨ ap (λ k → dialogue⋆ ⟦ k · y ⟧₀ α) ((close-⌜succ⌝ ys) ⁻¹) ⟩
 dialogue⋆ ⟦ close ⌜succ⌝ ys · y ⟧₀ α
  ∎
⌜main-lemma⌝ {n} {Γ} {_} Rec α xs ys rxys x y rxy x₁ y₁ rxy₁ x₂ y₂ rxyz₂ = {!!}
⌜main-lemma⌝ {n} {Γ} {.(Γ [ i ])} (ν i) α xs ys rxys = {!!}
⌜main-lemma⌝ {n} {Γ} {σ ⇒ τ} (ƛ t) α xs ys rxys x y rxy = {!!}
⌜main-lemma⌝ {n} {Γ} {σ} (t · t₁) α xs ys rxys =
 transport⁻¹
  (λ k → R⋆ α (⟦ t ⟧ xs (⟦ t₁ ⟧ xs)) k)
  (close· ⌜ t ⌝ ⌜ t₁ ⌝ ys)
  (⌜main-lemma⌝
    t α xs ys rxys (⟦ t₁ ⟧ xs) (close ⌜ t₁ ⌝ ys)
    (⌜main-lemma⌝ t₁ α xs ys rxys ))

\end{code}
