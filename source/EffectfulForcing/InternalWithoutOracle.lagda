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
open import EffectfulForcing.Church hiding (B⋆⟦_⟧ ; dialogue-tree⋆)
open import EffectfulForcing.Internal
open import EffectfulForcing.LambdaWithoutOracle
open import EffectfulForcing.SystemT
open import UF.Base using (from-×-＝' ; transport₂)
open import MGS.hlevels using (hedberg)
open import MGS.MLTT using (has-decidable-equality)

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

-- ⊆Γ Γ₁ Γ₂ states that Γ₁ is a sub context of Γ₂
data ⊆Γ : {n : ℕ} (Γ₁ : Cxt n) {m : ℕ} (Γ₂ : Cxt m) → Type where
  ⊆Γ0 : ⊆Γ {0} 〈〉 {0} 〈〉
  ⊆ΓR : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (σ : type)
      → ⊆Γ Γ₁ Γ₂
      → ⊆Γ Γ₁ (Γ₂ , σ)
  ⊆ΓS : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (σ : type)
      → ⊆Γ Γ₁ Γ₂
      → ⊆Γ (Γ₁ , σ) (Γ₂ , σ)

-- ⊆Γ is reflexive
⊆Γ-refl : {n : ℕ} (Γ : Cxt n) → ⊆Γ Γ Γ
⊆Γ-refl {zero} 〈〉 = ⊆Γ0
⊆Γ-refl {succ n} (Γ , τ) = ⊆ΓS τ (⊆Γ-refl Γ)

-- ⊆Γ is transitive
⊆Γ-trans : {n₁ : ℕ} {Γ₁ : Cxt n₁} {n₂ : ℕ} {Γ₂ : Cxt n₂} {n₃ : ℕ} {Γ₃ : Cxt n₃}
         → ⊆Γ Γ₁ Γ₂ → ⊆Γ Γ₂ Γ₃ → ⊆Γ Γ₁ Γ₃
⊆Γ-trans {n₁} {Γ₁} {.0} {.〈〉} {.0} {.〈〉} h ⊆Γ0 = h
⊆Γ-trans {n₁} {Γ₁} {n₂} {Γ₂} {.(succ _)} {.(_ , σ)} h (⊆ΓR σ q) = ⊆ΓR σ (⊆Γ-trans h q)
⊆Γ-trans {n₁} {Γ₁} {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} (⊆ΓR .σ h) (⊆ΓS σ q) = ⊆ΓR σ (⊆Γ-trans h q)
⊆Γ-trans {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} (⊆ΓS .σ h) (⊆ΓS σ q) = ⊆ΓS σ (⊆Γ-trans h q)

-- From the standard library. Is that defined somewhere? Can we import it from the standard library?
data _≤_ : ℕ → ℕ → Type where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → succ m ≤ succ n

_<_ : ℕ → ℕ → Type
i < j = succ i ≤ j

¬s≤n : (n : ℕ) → ¬ (succ n ≤ n)
¬s≤n (succ n) (s≤s h) = ¬s≤n n h

n≤s : (n : ℕ) → n ≤ succ n
n≤s zero = z≤n
n≤s (succ n) = s≤s (n≤s n)

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = z≤n
≤-refl (succ n) = s≤s (≤-refl n)

≤-trans : {n1 n2 n3 : ℕ} → n1 ≤ n2 → n2 ≤ n3 → n1 ≤ n3
≤-trans {.zero} {n2} {n3} z≤n q = z≤n
≤-trans {.(succ _)} {.(succ _)} {.(succ _)} (s≤s h) (s≤s q) = s≤s (≤-trans h q)

≤＝-trans : {n1 n2 n3 : ℕ} → n1 ≤ n2 → n2 ＝ n3 → n1 ≤ n3
≤＝-trans {n1} {n2} {.n2} a refl = a

≤<-trans : {n1 n2 n3 : ℕ} → n1 ≤ n2 → n2 < n3 → n1 < n3
≤<-trans {n1} {n2} {n3} a b = ≤-trans (s≤s a) b

<-irrefl : (n : ℕ) → ¬ (n < n)
<-irrefl zero ()
<-irrefl (succ n) (s≤s h) = <-irrefl n h

<+> : (n m : ℕ) → ¬ (n ＝ m) → n < m + m < n
<+> zero zero d = 𝟘-elim (d refl)
<+> zero (succ m) d = inl (s≤s z≤n)
<+> (succ n) zero d = inr (s≤s z≤n)
<+> (succ n) (succ m) d with <+> n m (λ p → d (ap succ p))
... | inl p = inl (s≤s p)
... | inr p = inr (s≤s p)

Fin→ℕ : {n : ℕ} (i : Fin n) → ℕ
Fin→ℕ {.(succ _)} Fin.𝟎 = 0
Fin→ℕ {.(succ _)} (Fin.suc i) = succ (Fin→ℕ i)

<Fin : {n : ℕ} (j : Fin n) → Fin→ℕ j < n
<Fin {.(succ _)} Fin.𝟎 = s≤s z≤n
<Fin {.(succ _)} (Fin.suc j) = s≤s (<Fin j)

⊆Γ≤ : {n : ℕ} {Γ : Cxt n} {m : ℕ} {Δ : Cxt m} → ⊆Γ Γ Δ → n ≤ m
⊆Γ≤ {.0} {.〈〉} {.0} {.〈〉} ⊆Γ0 = z≤n
⊆Γ≤ {n} {Γ} {succ m} {.(_ , σ)} (⊆ΓR σ h) = ≤-trans (⊆Γ≤ h) (n≤s m)
⊆Γ≤ {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} (⊆ΓS σ h) = s≤s (⊆Γ≤ h)

¬⊆Γ, : {n : ℕ} {Γ : Cxt n} {τ : type} → ¬ ⊆Γ (Γ , τ) Γ
¬⊆Γ, {n} {Γ} {τ} h = ¬s≤n n (⊆Γ≤ h)

⊆Γ, : {n : ℕ} (Γ : Cxt n) (τ : type) → ⊆Γ Γ (Γ , τ)
⊆Γ, {n} Γ τ = ⊆ΓR τ (⊆Γ-refl Γ)

-- 〈〉 is the smallest element w.r.t. the ⊆Γ order
⊆〈〉 : {n : ℕ} (Γ : Cxt n) → ⊆Γ 〈〉 Γ
⊆〈〉 {zero} 〈〉 = ⊆Γ0
⊆〈〉 {succ n} (Γ , τ) = ⊆ΓR τ (⊆〈〉 Γ)

-- Given (⊆Γ Γ₁ Γ₂) and a "pointer" to a type in Γ₁, ⊆ΓFin extracts a pointer to the same type in Γ₂
⊆ΓFin : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} → ⊆Γ Γ₁ Γ₂ → Fin n → Fin m
⊆ΓFin {n} {Γ₁} {.(succ _)} {.(_ , σ)} (⊆ΓR σ h) i = Fin.suc (⊆ΓFin h i)
⊆ΓFin {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} (⊆ΓS σ h) Fin.𝟎 = Fin.𝟎
⊆ΓFin {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} (⊆ΓS σ h) (Fin.suc i) = Fin.suc (⊆ΓFin h i)

-- All the types in Γ₁ are in Γ₂
⊆Γ[] : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (i : Fin n) (s : ⊆Γ Γ₁ Γ₂) → Γ₁ [ i ] ＝ Γ₂ [ ⊆ΓFin s i ]
⊆Γ[] {n} {Γ₁} {.(succ _)} {.(_ , σ)} i (⊆ΓR σ s) = ⊆Γ[] i s
⊆Γ[] {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} Fin.𝟎 (⊆ΓS σ s) = refl
⊆Γ[] {.(succ _)} {.(_ , σ)} {.(succ _)} {.(_ , σ)} (Fin.suc i) (⊆ΓS σ s) = ⊆Γ[] i s

-- Removes a type from the context, using a "pointer" to the type (i)
rmCxt : {n : ℕ} (Γ : Cxt (succ n)) (i : Fin (succ n)) → Cxt n
rmCxt {n} (Γ , τ) Fin.𝟎 = Γ
rmCxt {succ n} (Γ , τ) (Fin.suc i) = rmCxt Γ i , τ

-- Removing a type from a context is a sub-context of the initial context
→⊆Γ-rmCxt : {m : ℕ} {Γ : Cxt (succ m)} (i : Fin (succ m)) → ⊆Γ (rmCxt Γ i) Γ
→⊆Γ-rmCxt {m} {Γ , τ} Fin.𝟎 = ⊆ΓR τ (⊆Γ-refl Γ)
→⊆Γ-rmCxt {succ m} {Γ , τ} (Fin.suc i) = ⊆ΓS τ (→⊆Γ-rmCxt i)

⊆Γ-rmCxt→ : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt (succ m)} (i : Fin (succ m))
           → ⊆Γ Γ₁ (rmCxt Γ₂ i) → ⊆Γ Γ₁ Γ₂
⊆Γ-rmCxt→ {n} {Γ₁} {m} {Γ₂} i h = ⊆Γ-trans h (→⊆Γ-rmCxt i)

T＝type : {n : ℕ} {Γ : Cxt n} {σ τ : type}
       → τ ＝ σ
       → T Γ σ
       → T Γ τ
T＝type {n} {Γ} {σ} {.σ} refl t = t

-- extends the context of a term
weaken : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} {σ : type}
          → ⊆Γ Γ₁ Γ₂
          → T Γ₁ σ
          → T Γ₂ σ
weaken {n} {Γ₁} {m} {Γ₂} {_} sub Zero = Zero
weaken {n} {Γ₁} {m} {Γ₂} {_} sub Succ = Succ
weaken {n} {Γ₁} {m} {Γ₂} {_} sub Rec = Rec
--weaken {n} {Γ₁} {m} {Γ₂} {.(Γ₁ [ i ])} sub (ν i) = T＝type (⊆Γ[] i sub) (ν (⊆ΓFin sub i))
weaken {n} {Γ₁} {m} {Γ₂} {.(Γ₁ [ i ])} sub (ν i) = transport⁻¹ (T Γ₂) (⊆Γ[] i sub) (ν (⊆ΓFin sub i))
weaken {n} {Γ₁} {m} {Γ₂} {σ ⇒ τ} sub (ƛ t) = ƛ (weaken (⊆ΓS σ sub) t)
weaken {n} {Γ₁} {m} {Γ₂} {σ} sub (t · t₁) = weaken sub t · weaken sub t₁

-- extends the context of a closed term
weaken₀ : {n : ℕ} {Γ : Cxt n} {σ : type} → T₀ σ → T Γ σ
weaken₀ {n} {Γ} {σ} t = weaken (⊆〈〉 Γ) t

-- extends the context with one type
weaken, : {n : ℕ} {Γ : Cxt n} {σ : type} (τ : type) → T Γ σ → T (Γ , τ) σ
weaken, {n} {Γ} {σ} τ t = weaken {n} {Γ} {succ n} {Γ , τ} (⊆Γ, Γ τ) t

⊆ΓFin-refl : {n : ℕ} {Γ₁ Γ₂ : Cxt n} (i : Fin n) (s : ⊆Γ Γ₁ Γ₂) → Γ₁ ＝ Γ₂ → ⊆ΓFin s i ＝ i
⊆ΓFin-refl {.(succ _)} {Γ₁ , τ} {.Γ₁ , .τ} i (⊆ΓR .τ s) refl = 𝟘-elim (¬⊆Γ, s)
⊆ΓFin-refl {.(succ _)} {Γ₁ , τ} {.(Γ₂ , τ)} Fin.𝟎 (⊆ΓS {Γ₂ = Γ₂} .τ s) e = refl
⊆ΓFin-refl {.(succ _)} {Γ₁ , τ} {.(Γ₂ , τ)} (Fin.suc i) (⊆ΓS {Γ₂ = Γ₂} .τ s) e =
 ap Fin.suc (⊆ΓFin-refl i s (pr₁ (from-×-＝' e)))

dec-type : has-decidable-equality type
dec-type ι ι = inl refl
dec-type ι (τ ⇒ τ₁) = inr (λ ())
dec-type (σ ⇒ σ₁) ι = inr (λ ())
dec-type (σ ⇒ σ₁) (τ ⇒ τ₁) with dec-type σ τ | dec-type σ₁ τ₁
... | inl p | inl q = inl (transport₂ (λ τ τ₁ → σ ⇒ σ₁ ＝ τ ⇒ τ₁) p q refl)
... | inl p | inr q = inr h
 where
 h : σ ⇒ σ₁ ＝ τ ⇒ τ₁ → 𝟘
 h refl = q refl
... | inr p | _ = inr h
 where
 h : σ ⇒ σ₁ ＝ τ ⇒ τ₁ → 𝟘
 h refl = p refl

＝type-refl : {σ : type} (e : σ ＝ σ) → e ＝ refl
＝type-refl {σ} e = hedberg dec-type σ σ e refl

transport⁻¹-T-type : {n : ℕ} {Γ : Cxt n} {σ : type} (e : σ ＝ σ) (t : T Γ σ) → transport⁻¹ (T Γ) e t ＝ t
transport⁻¹-T-type {n} {Γ} {σ} e t = transport⁻¹ (λ k → transport⁻¹ (T Γ) k t ＝ t) (＝type-refl e) refl

weaken₀-reflν : {n : ℕ} {Γ : Cxt n} (i : Fin n) (s : ⊆Γ Γ Γ)
                (e : (Γ [ i ]) ＝ (Γ [ ⊆ΓFin s i ]))
              → transport⁻¹ (T Γ) e (ν (⊆ΓFin s i)) ＝ ν i
weaken₀-reflν {n} {Γ} i s =
 transport⁻¹ (λ k → (e : (Γ [ i ]) ＝ (Γ [ k ])) → transport⁻¹ (T Γ) e (ν k) ＝ ν i)
             (⊆ΓFin-refl i s refl) λ e → transport⁻¹-T-type e _

weaken₀-reflν' : {n : ℕ} {Γ : Cxt n} (i : Fin n) (s : ⊆Γ Γ Γ)
               → transport⁻¹ (T Γ) (⊆Γ[] i s) (ν (⊆ΓFin s i)) ＝ ν i
weaken₀-reflν' {n} {Γ} i s = weaken₀-reflν i s (⊆Γ[] i s)

weaken-id : {σ : type} {n : ℕ} {Γ : Cxt n} (s : ⊆Γ Γ Γ) (t : T Γ σ) → weaken s t ＝ t
weaken-id {_} {n} {Γ} s Zero = refl
weaken-id {_} {n} {Γ} s Succ = refl
weaken-id {_} {n} {Γ} s Rec = refl
weaken-id {.(Γ [ i ])} {n} {Γ} s (ν i) = weaken₀-reflν' i s
weaken-id {σ ⇒ τ} {n} {Γ} s (ƛ t) = ap ƛ (weaken-id (⊆ΓS σ s) t)
weaken-id {σ} {n} {Γ} s (t₁ · t₂) =
 weaken s t₁ · weaken s t₂
  ＝⟨ ap (λ k → k · weaken s t₂) (weaken-id s t₁) ⟩
 t₁ · weaken s t₂
  ＝⟨ ap (λ k → t₁ · k) (weaken-id s t₂) ⟩
 t₁ · t₂
  ∎

⌜star⌝ : {X Y A : type} {n : ℕ} {Γ : Cxt n}
                    → T Γ ((⌜B⌝ (X ⇒ Y) A) ⇒ ⌜B⌝ X A ⇒ ⌜B⌝ Y A)
⌜star⌝ =
 ƛ (ƛ (⌜kleisli-extension⌝
       · ƛ (⌜B-functor⌝
            · ƛ (ν₀ · ν₁)
            · ν₂)
       · ν₀))

-- λη.λβ.t (λs.f (λg.η(g s)) β) β
⌜app⌝ : {A : type} {σ τ : type} {n : ℕ} {Γ : Cxt n}
       (f : T Γ (⌜B⌝ (σ ⇒ τ) A)) (t : T Γ (⌜B⌝ σ A)) → T Γ (⌜B⌝ τ A)
⌜app⌝ {A} {σ} {τ} {n} {Γ} f t = ⌜star⌝ · f · t

-- indirect relation that relates
-- (1) internal terms of a Church-encoded dialogue tree type
-- (2) external Church-encoded dialogue trees
⌜R⌝ : ({A} σ : type) → T₀ (⌜B⌝ σ A) → B⋆〖 σ 〗 〖 A 〗 → Type
⌜R⌝ ι       t d = ⟦ t ⟧₀ ＝ d
⌜R⌝ {A} (σ ⇒ τ) f g = (t : T₀ (⌜B⌝ σ A))
                 (d : B⋆〖 σ 〗 〖 A 〗)
               → ⌜R⌝ σ t d
               → ⌜R⌝ τ (⌜app⌝ f t) (g d)

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
                 → R⋆₁ {τ} α (f x) (⌜app⌝ f' x')

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
subν {succ n} {Γ , τ} (Fin.suc i) Fin.𝟎 u = ν₀
subν {succ n} {Γ , τ} (Fin.suc i) (Fin.suc j) u = weaken, τ (subν i j u)

sub : {σ : type} {n : ℕ} {Γ : Cxt (succ n)} (i : Fin (succ n)) → T Γ σ → T₀ (Γ [ i ]) → T (rmCxt Γ i) σ
sub {_} {n} {Γ} i Zero u = Zero
sub {_} {n} {Γ} i Succ u = Succ
sub {_} {n} {Γ} i Rec u  = Rec
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

Sub⊆Γ : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (s : ⊆Γ Γ₁ Γ₂) → Type
Sub⊆Γ {.0} {.〈〉} {.0} {.〈〉} ⊆Γ0 = 𝟙
Sub⊆Γ {n} {Γ₁} {succ m} {Γ₂ , σ} (⊆ΓR σ s) = Sub⊆Γ s × T₀ σ
Sub⊆Γ {succ n} {Γ₁ , σ} {succ m} {Γ₂ , σ} (⊆ΓS σ s) = Sub⊆Γ s

Sub⊆Γ〈〉 : {n : ℕ} {Γ : Cxt n} → Sub₀ Γ → Sub⊆Γ (⊆〈〉 Γ)
Sub⊆Γ〈〉 {zero} {〈〉} s = MLTT.Spartan.⋆
Sub⊆Γ〈〉 {succ n} {Γ , τ} s = Sub⊆Γ〈〉 {n} {Γ} (λ k → s (Fin.suc k)) , s Fin.𝟎

-- A more general definition of close, which does not necessarily go down to a closed term
close2 : {σ : type} {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} → {s : ⊆Γ Γ₁ Γ₂} → T Γ₂ σ → Sub⊆Γ s  → T Γ₁ σ
close2 {σ} {.0} {.〈〉} {.0} {.〈〉} {⊆Γ0} t subst = t
close2 {σ} {n} {Γ₁} {succ m} {Γ₂ , σ₁} {⊆ΓR σ₁ s} t (subst , u) =
 close2 {σ} {n} {Γ₁} {m} {Γ₂} {s} (sub {σ} {m} {Γ₂ , σ₁} Fin.𝟎 t u) subst
close2 {σ} {succ n} {Γ₁ , σ₁} {succ m} {Γ₂ , σ₁} {⊆ΓS σ₁ s} t subst =
 weaken, {n} {Γ₁} {σ₁ ⇒ σ} σ₁ (close2 {σ₁ ⇒ σ} {n} {Γ₁} {m} {Γ₂} {s} (ƛ t) subst) · ν₀

-- close and close2 produce the same result
close-as-close2 : {σ : type} {n : ℕ} {Γ : Cxt n} (t : T Γ σ) (s : Sub₀ Γ)
                → close t s ＝ close2 {σ} {0} {〈〉} {n} {Γ} {⊆〈〉 Γ} t (Sub⊆Γ〈〉 s)
close-as-close2 {σ} {zero} {〈〉} t s = refl
close-as-close2 {σ} {succ n} {Γ , τ} t s = close-as-close2 (sub₀ t (s Fin.𝟎)) (λ i → s (Fin.suc i))

closeƛ : {n : ℕ} {Γ : Cxt n} {σ τ : type} (t : T (Γ , σ) τ) (s : Sub₀ Γ)
       → close (ƛ t) s ＝ ƛ (close2 {τ} {1} {〈〉 , σ} {succ n} {Γ , σ} {⊆ΓS σ (⊆〈〉 Γ)} t (Sub⊆Γ〈〉 s))
closeƛ {n} {Γ} {σ} {τ} t s =
 close (ƛ t) s
  ＝⟨ {!!} ⟩
 {!close2 {τ} {0} {〈〉} {n} {Γ} {⊆〈〉 Γ} (ƛ t) (Sub⊆Γ〈〉 s)!}
  ＝⟨ {!!} ⟩
 ƛ (close2 {τ} {1} {〈〉 , σ} {succ n} {Γ , σ} {⊆ΓS σ (⊆〈〉 Γ)} t (Sub⊆Γ〈〉 s))
  ∎

Fin∈Γ : {n : ℕ} (i : Fin n) {m : ℕ} (Γ : Cxt m) → Type
Fin∈Γ {n} i {m} Γ = Fin→ℕ i < m

¬Fin∈Γ〈〉 : {n : ℕ} (i : Fin n) → ¬ Fin∈Γ {1} Fin.𝟎 〈〉
¬Fin∈Γ〈〉 {n} i ()

¬Fin∈Γsuc : {n : ℕ} (i : Fin n) {m : ℕ} (Γ : Cxt m) (σ : type)
           → ¬ Fin∈Γ i Γ
           → ¬ Fin∈Γ (Fin.suc i) (Γ , σ)
¬Fin∈Γsuc {n} i {m} Γ σ h (s≤s q) = h q

-- true if i is free in t
is-free : (i : ℕ) {n : ℕ} {Γ : Cxt n} {σ : type} (t : T Γ σ) → Type
is-free i {n} {Γ} {_} Zero = 𝟘
is-free i {n} {Γ} {_} Succ = 𝟘
is-free i {n} {Γ} {_} Rec  = 𝟘
is-free i {n} {Γ} {.(Γ [ i₁ ])} (ν i₁) = i ＝ Fin→ℕ i₁
is-free i {n} {Γ} {σ ⇒ τ} (ƛ t) = is-free (succ i) t
is-free i {n} {Γ} {σ} (t₁ · t₂) = is-free i t₁ + is-free i t₂

-- a term is closed if it does not contain free variables
closed : {n : ℕ} {Γ : Cxt n} {σ : type} (t : T Γ σ) → Type
closed {n} {Γ} {σ} t = (i : ℕ) → ¬ is-free i t

¬is-free≤ : (i : ℕ) {n : ℕ} {Γ : Cxt n} {σ : type} (t : T Γ σ)
          → n ≤ i → ¬ is-free i t
¬is-free≤ i {n} {Γ} {_} Zero ni = λ ()
¬is-free≤ i {n} {Γ} {_} Succ ni = λ ()
¬is-free≤ i {n} {Γ} {_} Rec  ni = λ ()
¬is-free≤ i {n} {Γ} {.(Γ [ i₁ ])} (ν i₁) ni e = <-irrefl n (≤<-trans (≤＝-trans ni e) (<Fin i₁))
¬is-free≤ i {n} {Γ} {σ ⇒ τ} (ƛ t) ni = ¬is-free≤ (succ i) t (s≤s ni)
¬is-free≤ i {n} {Γ} {σ} (t₁ · t₂) ni (inl x) = ¬is-free≤ i t₁ ni x
¬is-free≤ i {n} {Γ} {σ} (t₁ · t₂) ni (inr x) = ¬is-free≤ i t₂ ni x

closed₀ : {σ : type} (t : T₀ σ) → closed t
closed₀ {σ} t i = ¬is-free≤ i t z≤n

is-free-transport⁻¹ : {m : ℕ} {Γ : Cxt m} {σ τ : type} (e : τ ＝ σ) (t : T Γ σ) (j : ℕ)
                   → is-free j (transport⁻¹ (T Γ) e t)
                    → is-free j t
is-free-transport⁻¹ {m} {Γ} {σ} {.σ} refl t j h = h

is-free-¬transport⁻¹ : {m : ℕ} {Γ : Cxt m} {σ τ : type} (e : τ ＝ σ) (t : T Γ σ) (j : ℕ)
                   → ¬ is-free j (transport⁻¹ (T Γ) e t)
                    → ¬ is-free j t
is-free-¬transport⁻¹ {m} {Γ} {σ} {.σ} refl t j h = h

free-weaken : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (s : ⊆Γ Γ₁ Γ₂) {σ : type} (t : T Γ₁ σ) (i : ℕ)
            → is-free i (weaken s t)
            → Σ p ꞉ Fin n , (Fin→ℕ (⊆ΓFin s p) ＝ i) × (is-free (Fin→ℕ p) t)
free-weaken {n} {Γ₁} {m} {Γ₂} s {.(Γ₁ [ i₁ ])} (ν i₁) i h =
 i₁ , (is-free-transport⁻¹ (⊆Γ[] i₁ s) (ν (⊆ΓFin s i₁)) i h ⁻¹) , refl
free-weaken {n} {Γ₁} {m} {Γ₂} s {σ ⇒ τ} (ƛ t) i h with free-weaken (⊆ΓS σ s) t (succ i) h
... | Fin.suc p , refl , h2 = p , refl , h2
free-weaken {n} {Γ₁} {m} {Γ₂} s {σ} (t · t₁) i (inl x) with free-weaken s t i x
... | p , h1 , h2 = p , h1 , inl h2
free-weaken {n} {Γ₁} {m} {Γ₂} s {σ} (t · t₁) i (inr x) with free-weaken s t₁ i x
... | p , h1 , h2 = p , h1 , inr h2

closed-weaken₀ : {n : ℕ} {Γ : Cxt n} {σ : type} (e : ⊆Γ 〈〉 Γ) (t : T₀ σ) → closed {n} {Γ} (weaken e t)
closed-weaken₀ {n} {Γ} {σ} e t i h with free-weaken e t i h
... | p , h1 , h2 = closed₀ t (Fin→ℕ p) h2

sub-transport⁻¹ : {m : ℕ} {Γ : Cxt (succ m)} (i : Fin (succ m)) (u : T₀ (Γ [ i ])) {σ τ : type} (e : τ ＝ σ) (t : T Γ σ)
               → sub {τ} {m} {Γ} i (transport⁻¹ (T Γ) e t) u
                  ＝ transport⁻¹ (T (rmCxt Γ i)) e (sub {σ} i t u)
sub-transport⁻¹ {m} {Γ} i u {σ} {.σ} refl t = refl

⊆Γ-trans-refl : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (s : ⊆Γ Γ₁ Γ₂)
              → ⊆Γ-trans s (⊆Γ-refl Γ₂) ＝ s
⊆Γ-trans-refl {n} {Γ₁} {zero} {〈〉} s = refl
⊆Γ-trans-refl {n} {Γ₁} {succ m} {Γ₂ , τ} (⊆ΓR .τ s) = ap (⊆ΓR τ) (⊆Γ-trans-refl s)
⊆Γ-trans-refl {.(succ _)} {.(_ , τ)} {succ m} {Γ₂ , τ} (⊆ΓS .τ s) = ap (⊆ΓS τ) (⊆Γ-trans-refl s)

⊆Γ-rmCxt→⊆〈〉 : {n : ℕ} (Γ : Cxt n) (τ : type) → ⊆Γ-rmCxt→ Fin.𝟎 (⊆〈〉 Γ) ＝ ⊆〈〉 (Γ , τ)
⊆Γ-rmCxt→⊆〈〉 {n} Γ τ = ap (⊆ΓR τ) (⊆Γ-trans-refl (⊆〈〉 Γ))

transport⁻¹ν-as-weaken, : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (s : ⊆Γ Γ₁ Γ₂) (i : Fin n) (τ : type)
                          (j : Fin m) (σ : type) (e : σ ＝ Γ₂ [ j ])
                       → transport⁻¹ (T (Γ₂ , τ)) e (ν (Fin.suc j))
                       ＝ weaken, τ (transport⁻¹ (T Γ₂) e (ν j))
transport⁻¹ν-as-weaken, {n} {Γ₁} {m} {Γ₂} s i τ j .(Γ₂ [ j ]) refl =
 transport⁻¹ (T (Γ₂ , τ)) refl (ν (Fin.suc j))
  ＝⟨ refl ⟩
 ν (Fin.suc j)
  ＝⟨ (h (⊆Γ-refl Γ₂) (⊆Γ[] j (⊆Γ-refl Γ₂))) ⁻¹ ⟩
 transport⁻¹ (T (Γ₂ , τ)) (⊆Γ[] j (⊆Γ-refl Γ₂)) (ν (Fin.suc (⊆ΓFin (⊆Γ-refl Γ₂) j)))
  ＝⟨ refl ⟩
 weaken, τ (transport⁻¹ (T Γ₂) refl (ν j))
  ∎
 where
 h : (s : ⊆Γ Γ₂ Γ₂) (e : Γ₂ [ j ] ＝ Γ₂ [ ⊆ΓFin s j ])
     → transport⁻¹ (T (Γ₂ , τ)) e (ν (Fin.suc (⊆ΓFin s j)))
     ＝ ν (Fin.suc j)
 h s = transport⁻¹
         (λ k →
            (e : (Γ₂ [ j ]) ＝ (Γ₂ [ k ])) →
            transport⁻¹ (T (Γ₂ , τ)) e (ν (Fin.suc k)) ＝ ν (Fin.suc j))
         (⊆ΓFin-refl j s refl) (λ e → transport⁻¹-T-type e _)


transport⁻¹ν-as-weaken,' : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (s : ⊆Γ Γ₁ Γ₂) (i : Fin n) (τ : type)
                        → transport⁻¹ (T (Γ₂ , τ)) (⊆Γ[] i s) (ν (Fin.suc (⊆ΓFin s i)))
                        ＝ weaken, τ (transport⁻¹ (T Γ₂) (⊆Γ[] i s) (ν (⊆ΓFin s i)))
transport⁻¹ν-as-weaken,' {n} {Γ₁} {m} {Γ₂} s i τ =
 transport⁻¹ν-as-weaken, s i τ (⊆ΓFin s i) (Γ₁ [ i ]) (⊆Γ[] i s)

transport⁻¹-weaken, : {σ₁ σ₂ τ : type} {n : ℕ} {Γ : Cxt n} (t : T Γ σ₂) (e : σ₁ ＝ σ₂)
                   → transport⁻¹ (T (Γ , τ)) e (weaken, τ t)
                   ＝ weaken, τ (transport⁻¹ (T Γ ) e t)
transport⁻¹-weaken, {σ₁} {.σ₁} {τ} {n} {Γ} t refl = refl

subν-diff : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt (succ m)} {i : Fin (succ m)}
            (s : ⊆Γ Γ₁ (rmCxt Γ₂ i)) (i₁ : Fin n) (u : T₀ (Γ₂ [ i ]))
            (nf : ¬ (Fin→ℕ i ＝ Fin→ℕ (⊆ΓFin (⊆Γ-rmCxt→ i s) i₁)))
         → transport⁻¹ (T (rmCxt Γ₂ i)) (⊆Γ[] i₁ (⊆Γ-rmCxt→ i s)) (subν i (⊆ΓFin (⊆Γ-rmCxt→ i s) i₁) u)
         ＝ transport⁻¹ (T (rmCxt Γ₂ i)) (⊆Γ[] i₁ s) (ν (⊆ΓFin s i₁))
subν-diff {n} {Γ₁} {succ m} {(Γ₂ , τ₁) , τ₂} {Fin.𝟎} (⊆ΓR τ₁ s) i₁ u nf =
 transport⁻¹
   (λ k →
      transport⁻¹ (T (Γ₂ , τ₁)) (⊆Γ[] i₁ k) (ν (Fin.suc (⊆ΓFin k i₁))) ＝
      transport⁻¹ (T (Γ₂ , τ₁)) (⊆Γ[] i₁ s) (ν (Fin.suc (⊆ΓFin s i₁))))
   (⊆Γ-trans-refl s)
   refl
subν-diff {n} {Γ₁} {.(succ _)} {Γ₂ , τ} {Fin.suc i} (⊆ΓR τ s) i₁ u nf =
 transport⁻¹ (T (rmCxt Γ₂ i , τ)) (⊆Γ[] i₁ (⊆Γ-trans s (→⊆Γ-rmCxt i))) (weaken, τ (subν i (⊆ΓFin (⊆Γ-trans s (→⊆Γ-rmCxt i)) i₁) u))
  ＝⟨ transport⁻¹-weaken, (subν i (⊆ΓFin (⊆Γ-trans s (→⊆Γ-rmCxt i)) i₁) u) (⊆Γ[] i₁ (⊆Γ-trans s (→⊆Γ-rmCxt i))) ⟩
 weaken, τ (transport⁻¹ (T (rmCxt Γ₂ i)) (⊆Γ[] i₁ (⊆Γ-trans s (→⊆Γ-rmCxt i))) (subν i (⊆ΓFin (⊆Γ-trans s (→⊆Γ-rmCxt i)) i₁) u))
  ＝⟨ ap (weaken, τ) (subν-diff {_} {Γ₁} {_} {Γ₂} {i} s i₁ u (λ p → 𝟘-elim (nf (ap succ p)))) ⟩
 weaken, τ (transport⁻¹ (T (rmCxt Γ₂ i)) (⊆Γ[] i₁ s) (ν (⊆ΓFin s i₁)))
  ＝⟨ (transport⁻¹ν-as-weaken,' s i₁ τ) ⁻¹ ⟩
 transport⁻¹ (T (rmCxt Γ₂ i , τ)) (⊆Γ[] i₁ s) (ν (Fin.suc (⊆ΓFin s i₁)))
  ∎
subν-diff {succ n} {Γ₁ , τ₂} {succ m} {(Γ₂ , τ₀) , τ₁} {Fin.𝟎} (⊆ΓS τ₂ s) i₁ u nf =
 transport⁻¹
   (λ k →
      transport⁻¹ (T (Γ₂ , τ₂)) (⊆Γ[] i₁ (⊆ΓS τ₂ k)) (ν (⊆ΓFin (⊆ΓS τ₂ k) i₁))
      ＝ transport⁻¹ (T (Γ₂ , τ₂)) (⊆Γ[] i₁ (⊆ΓS τ₂ s)) (ν (⊆ΓFin (⊆ΓS τ₂ s) i₁)))
   (⊆Γ-trans-refl s)
   refl
subν-diff {succ n} {Γ₁ , τ₂} {succ m} {(Γ₂ , τ₀) , .τ₂} {Fin.suc i} (⊆ΓS τ₂ s) Fin.𝟎 u nf = refl
subν-diff {succ n} {Γ₁ , τ₂} {succ m} {(Γ₂ , τ₀) , .τ₂} {Fin.suc i} (⊆ΓS τ₂ s) (Fin.suc i₁) u nf =
 transport⁻¹ (T (rmCxt (Γ₂ , τ₀) i , τ₂)) (⊆Γ[] i₁ (⊆Γ-trans s (→⊆Γ-rmCxt i))) (weaken, τ₂ (subν i (⊆ΓFin (⊆Γ-trans s (→⊆Γ-rmCxt i)) i₁) u))
  ＝⟨ transport⁻¹-weaken, (subν i (⊆ΓFin (⊆Γ-trans s (→⊆Γ-rmCxt i)) i₁) u) (⊆Γ[] i₁ (⊆Γ-trans s (→⊆Γ-rmCxt i))) ⟩
 weaken, τ₂ (transport⁻¹ (T (rmCxt (Γ₂ , τ₀) i)) (⊆Γ[] i₁ (⊆Γ-trans s (→⊆Γ-rmCxt i))) (subν i (⊆ΓFin (⊆Γ-trans s (→⊆Γ-rmCxt i)) i₁) u))
  ＝⟨ ap (weaken, τ₂) (subν-diff {_} {Γ₁} {_} {Γ₂ , τ₀} {i} s i₁ u (λ p → 𝟘-elim (nf (ap succ p)))) ⟩
 weaken, τ₂ (transport⁻¹ (T (rmCxt (Γ₂ , τ₀) i)) (⊆Γ[] i₁ s) (ν (⊆ΓFin s i₁)))
  ＝⟨ (transport⁻¹ν-as-weaken,' s i₁ τ₂) ⁻¹ ⟩
 transport⁻¹ (T (rmCxt (Γ₂ , τ₀) i , τ₂)) (⊆Γ[] i₁ s) (ν (Fin.suc (⊆ΓFin s i₁)))
  ∎

sub-weaken : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt (succ m)} {σ : type} (i : Fin (succ m))
             (s : ⊆Γ Γ₁ (rmCxt Γ₂ i))
             (t : T Γ₁ σ) (u : T₀ (Γ₂ [ i ]))
             (nf : ¬ is-free (Fin→ℕ i) (weaken (⊆Γ-rmCxt→ i s) t))
           → sub i (weaken (⊆Γ-rmCxt→ i s) t) u ＝ weaken {n} {Γ₁} {m} {rmCxt Γ₂ i} {σ} s t
sub-weaken {n} {Γ₁} {m} {Γ₂} {_} i s Zero u nf = refl
sub-weaken {n} {Γ₁} {m} {Γ₂} {_} i s Succ u nf = refl
sub-weaken {n} {Γ₁} {m} {Γ₂} {_} i s Rec  u nf = refl
sub-weaken {n} {Γ₁} {m} {Γ₂} {.(Γ₁ [ i₁ ])} i s (ν i₁) u nf =
 sub i (transport⁻¹ (T Γ₂) (⊆Γ[] i₁ (⊆Γ-rmCxt→ i s)) (ν (⊆ΓFin (⊆Γ-rmCxt→ i s) i₁))) u
  ＝⟨ sub-transport⁻¹ i u (⊆Γ[] i₁ (⊆Γ-rmCxt→ i s)) (ν (⊆ΓFin (⊆Γ-rmCxt→ i s) i₁)) ⟩
 transport⁻¹ (T (rmCxt Γ₂ i)) (⊆Γ[] i₁ (⊆Γ-rmCxt→ i s)) (subν i (⊆ΓFin (⊆Γ-rmCxt→ i s) i₁) u)
  ＝⟨ subν-diff s i₁ u nf1 ⟩
 transport⁻¹ (T (rmCxt Γ₂ i)) (⊆Γ[] i₁ s) (ν (⊆ΓFin s i₁))
  ∎
 where
 nf1 : ¬ (Fin→ℕ i ＝ Fin→ℕ (⊆ΓFin (⊆Γ-rmCxt→ i s) i₁))
 nf1 = is-free-¬transport⁻¹ (⊆Γ[] i₁ (⊆Γ-rmCxt→ i s)) (ν (⊆ΓFin (⊆Γ-rmCxt→ i s) i₁)) (Fin→ℕ i) nf
sub-weaken {n} {Γ₁} {m} {Γ₂} {σ ⇒ τ} i s (ƛ t) u nf =
 ap ƛ (sub-weaken (Fin.suc i) (⊆ΓS σ s) t u nf)
sub-weaken {n} {Γ₁} {m} {Γ₂} {σ} i s (t₁ · t₂) u nf =
 sub i (weaken (⊆Γ-rmCxt→ i s) t₁) u · sub i (weaken (⊆Γ-rmCxt→ i s) t₂) u
  ＝⟨ ap (λ k → k · sub i (weaken (⊆Γ-rmCxt→ i s) t₂) u) (sub-weaken i s t₁ u λ z → nf (inl z)) ⟩
 weaken s t₁ · sub i (weaken (⊆Γ-rmCxt→ i s) t₂) u
  ＝⟨ ap (λ k → weaken s t₁ · k) (sub-weaken i s t₂ u λ z → nf (inr z)) ⟩
 weaken s t₁ · weaken s t₂
  ∎

sub₀-weaken₀ : {σ τ : type} {n : ℕ} {Γ : Cxt n} (t : T₀ σ) (u : T₀ τ)
             → sub₀ (weaken₀ {succ n} {Γ , τ} {σ} t) u ＝ weaken₀ {n} {Γ} {σ} t
sub₀-weaken₀ {σ} {τ} {n} {Γ} t u =
 transport (λ k → sub₀ (weaken k t) u ＝ weaken₀ t)
           (⊆Γ-rmCxt→⊆〈〉 Γ τ) (sub-weaken Fin.𝟎 (⊆〈〉 Γ) t u (closed-weaken₀ (⊆Γ-rmCxt→ Fin.𝟎 (⊆〈〉 Γ)) t 0))

{-
-- untyped version of System T
data $T : Type where
 $Zero : $T
 $Succ : $T
 $Rec  : $T
 $ν    : (i : ℕ)  → $T
 $ƛ    : $T → $T
 _$·_  : $T → $T → $T

curryfy : {n : ℕ} {Γ : Cxt n} {σ : type} (t : T Γ σ) → $T
curryfy {n} {Γ} {.ι} Zero = $Zero
curryfy {n} {Γ} {.(ι ⇒ ι)} Succ = $Succ
curryfy {n} {Γ} {.((ι ⇒ _ ⇒ _) ⇒ _ ⇒ ι ⇒ _)} Rec = $Rec
curryfy {n} {Γ} {.(Γ [ i ])} (ν i) = $ν (Fin→ℕ i)
curryfy {n} {Γ} {.(_ ⇒ _)} (ƛ t) = $ƛ (curryfy t)
curryfy {n} {Γ} {σ} (t · t₁) = curryfy t $· curryfy t₁

-- Can we prove close₀ in a simpler way using an untyped version of System T?
curryfy＝ : {n : ℕ} {Γ : Cxt n} {σ : type} (t₁ : T Γ σ) (t₂ : T Γ σ)
          → curryfy t₁ ＝ curryfy t₂
          → t₁ ＝ t₂
curryfy＝ {n} {Γ} {_} t₁ Zero p = {!!}
curryfy＝ {n} {Γ} {_} t₁ Succ p = {!!}
curryfy＝ {n} {Γ} {_} t₁ Rec p = {!!}
curryfy＝ {n} {Γ} {.(Γ [ i ])} t₁ (ν i) p = {!!}
curryfy＝ {n} {Γ} {.(_ ⇒ _)} t₁ (ƛ t₂) p = {!!}
curryfy＝ {n} {Γ} {σ} (t₁ · t₄) (t₂ · t₃) p = {!!}
-}

-- to use in the lambda case
-- closing a closed term does not change the term
close₀ : {σ : type} {n : ℕ} {Γ : Cxt n} (t : T₀ σ) (s : Sub₀ Γ)
      → close (weaken₀ {n} {Γ} {σ} t) s ＝ t
close₀ {σ} {zero} {〈〉} t s = weaken-id (⊆〈〉 〈〉) t
close₀ {σ} {succ n} {Γ , τ} t s =
 close (sub₀ (weaken₀ t) (s Fin.𝟎)) (λ i → s (Fin.suc i))
  ＝⟨ ap (λ k → close k (λ i → s (Fin.suc i))) (sub₀-weaken₀ t (s Fin.𝟎)) ⟩
 close (weaken₀ t) (λ i → s (Fin.suc i))
  ＝⟨ close₀ t (λ i → s (Fin.suc i)) ⟩
 t
  ∎

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

-- testing...
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

{-
xx : (d : T₀ ι) (α : Baire)
  → succ (⟦ ⌜ d ⌝ ⟧₀ (λ z α → z) (λ φ x α → φ (α x) α) α)
    ＝ ⟦ ⌜ d ⌝ ⟧₀ (λ z α → succ z) (λ φ x α → φ (α x) α) α
xx = {!!}
-}

succ-dialogue⋆ : (d : T₀ (⌜B⌝ ι ((ι ⇒ ι) ⇒ ι))) (α : Baire)
              → succ (dialogue⋆ ⟦ d ⟧₀ α) ＝ dialogue⋆ (succ⋆ ⟦ d ⟧₀) α
succ-dialogue⋆ d α =
 succ (dialogue⋆ ⟦ d ⟧₀ α)
  ＝⟨ refl ⟩
 succ (⟦ d ⟧₀ (λ z α → z) (λ φ x α → φ (α x) α) α)
  ＝⟨ {!!} ⟩
 ⟦ d ⟧₀ (λ z α → succ z) (λ φ x α → φ (α x) α) α
  ＝⟨ refl ⟩
 dialogue⋆ (succ⋆ ⟦ d ⟧₀) α
  ∎

Succ? : {n : ℕ} {Γ : Cxt n} {σ : type} (t : T Γ σ) → 𝟚
Succ? {n} {Γ} {_} Zero = ₁
Succ? {n} {Γ} {_} Succ = ₀
Succ? {n} {Γ} {_} Rec  = ₀
Succ? {n} {Γ} {.(Γ [ i ])} (ν i) = ₀
Succ? {n} {Γ} {σ ⇒ τ} (ƛ t) = ₀
Succ? {n} {Γ} {σ} (t · t₁) = ₀

-- doesn't belong here
_∧?_ : 𝟚 → 𝟚 → 𝟚
₀ ∧? b = ₀
₁ ∧? b = b

val? : {n : ℕ} {Γ : Cxt n} {σ : type} (t : T Γ σ) → 𝟚
val? {n} {Γ} {_} Zero = ₁
val? {n} {Γ} {_} Succ = ₁
val? {n} {Γ} {_} Rec = ₁
val? {n} {Γ} {.(Γ [ i ])} (ν i) = ₀
val? {n} {Γ} {σ ⇒ τ} (ƛ t) = ₁
val? {n} {Γ} {σ} (t · u) = Succ? t ∧? val? u

isVal : {n : ℕ} {Γ : Cxt n} {σ : type} (t : T Γ σ) → Type
isVal {n} {Γ} {α} t = val? t ＝ ₁

isVal?  : {n : ℕ} {Γ : Cxt n} {σ : type} (t : T Γ σ) → isVal t + ¬ (isVal t)
isVal? {n} {Γ} {σ} t with val? t
... | ₁ = inl refl
... | ₀ = inr (λ ())

step· : {n : ℕ} {Γ : Cxt n} {σ₀ σ τ : type} (f : T Γ σ₀) (a : T Γ σ) → σ₀ ＝ σ ⇒ τ → isVal f → T Γ τ
step· {n} {Γ} {σ₀} {σ} {τ} t a e isv = {!!}
--step· {n} {Γ} {σ₀} {σ} {τ} t a e isv = {!!}
{--step· {n} {Γ} {_} {τ} Zero a () isv
step· {n} {Γ} {_} {.ι} Succ a refl isv = Succ · a -- not actually a step
step· {n} {Γ} {_} {.(ι ⇒ _ ⇒ _)} Rec a refl isv = {!!}
step· {n} {Γ} {.(Γ [ i ])} {τ} (ν i) a e isv = {!!}
step· {n} {Γ} {σ₁ ⇒ σ₂} {τ} (ƛ f) a e isv = {!!}
step· {n} {Γ} {.(τ ⇒ _)} {τ} (t · u) a refl isv = t · u · a -- not actually a step--}

-- call-by-name semantics
step : {n : ℕ} {Γ : Cxt n} {σ : type} (t : T Γ σ) → T Γ σ
step {n} {Γ} {_} Zero = Zero
step {n} {Γ} {_} Succ = Succ
step {n} {Γ} {_} Rec = Rec
step {n} {Γ} {.(Γ [ i ])} (ν i) = ν i
step {n} {Γ} {σ ⇒ τ} (ƛ t) = ƛ t
step {n} {Γ} {σ} (f · a) with isVal? f
... | inr p = step f · a
... | inl p = step· f a refl p

⌜main-lemma⌝ : {n : ℕ} {Γ : Cxt n} {σ : type} (t : T Γ σ)
              (α : Baire)
              (xs : 【 Γ 】) (ys : IB【 Γ 】 ((ι ⇒ ι) ⇒ ι))
            → R⋆s α xs ys
            → R⋆ α (⟦ t ⟧ xs) (close ⌜ t ⌝ ys)
⌜main-lemma⌝ {n} {Γ} {_} Zero α xs ys rxys = ap (λ k → dialogue⋆ ⟦ k ⟧₀ α) ((close-⌜zero⌝ ys) ⁻¹)
⌜main-lemma⌝ {n} {Γ} {_} Succ α xs ys rxys x y rxy =
 succ x
  ＝⟨ ap succ rxy ⟩
 succ (dialogue⋆ ⟦ y ⟧₀ α)
  ＝⟨ succ-dialogue⋆ y α ⟩
 dialogue⋆ (succ⋆ ⟦ y ⟧₀) α
  ＝⟨ ap (λ k → dialogue⋆ ⟦ k · y ⟧₀ α) ((close-⌜succ⌝ ys) ⁻¹) ⟩
 dialogue⋆ ⟦ close ⌜succ⌝ ys · y ⟧₀ α
  ∎
⌜main-lemma⌝ {n} {Γ} {_} Rec α xs ys rxys x y rxy x₁ y₁ rxy₁ x₂ y₂ rxyz₂ = {!!}
⌜main-lemma⌝ {n} {Γ} {.(Γ [ i ])} (ν i) α xs ys rxys = {!!}
⌜main-lemma⌝ {n} {Γ} {σ ⇒ τ} (ƛ t) α xs ys rxys x y rxy =
 transport
  (λ k → R⋆ α (⟦ t ⟧ (xs ‚ x)) (close (ƛ ⌜ t ⌝) ys · k))
  (close₀ y ys)
  (transport
    (λ k → R⋆ α (⟦ t ⟧ (xs ‚ x)) k)
    (close· (ƛ ⌜ t ⌝) (weaken₀ y) ys)
    {!!})
-- [DONE] The plan for ƛ is to use close₀ to turn
--   (close (ƛ ⌜ t ⌝) ys · y) into (close (ƛ ⌜ t ⌝) ys · close (weaken y) ys)
-- [DONE] and then use close· to turn
--   (close (ƛ ⌜ t ⌝) ys · close (weaken y) ys) into (close ((ƛ ⌜ t ⌝) · y) ys)
-- [TODO] and then use the operational semantics of System T? to turn
--   (close ((ƛ ⌜ t ⌝) · y) ys) into (close ⌜ t ⌝ (y , ys))
⌜main-lemma⌝ {n} {Γ} {σ} (t · t₁) α xs ys rxys =
 transport⁻¹
  (λ k → R⋆ α (⟦ t ⟧ xs (⟦ t₁ ⟧ xs)) k)
  (close· ⌜ t ⌝ ⌜ t₁ ⌝ ys)
  (⌜main-lemma⌝
    t α xs ys rxys (⟦ t₁ ⟧ xs) (close ⌜ t₁ ⌝ ys)
    (⌜main-lemma⌝ t₁ α xs ys rxys ))

\end{code}
