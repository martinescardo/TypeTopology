Martin Escardo, Vincent Rahli, Bruno da Rocha Paiva, Ayberk Tosun 20 May 2023

This is an adaptation of Internal.lagda written by Martin, which defines dialogue-tree⋆ without using T'
but directly using T.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.Internal.InternalWithoutOracle where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import MLTT.Athenian using (Fin)
open import EffectfulForcing.MFPSAndVariations.Continuity
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.SystemT using (type ; ι ; _⇒_ ; 〖_〗)
open import EffectfulForcing.MFPSAndVariations.Church hiding (B⋆【_】 ; ⟪⟫⋆ ; _‚‚⋆_ ; B⋆⟦_⟧ ; dialogue-tree⋆)
open import EffectfulForcing.Internal.Internal hiding (B⋆⟦_⟧ ; dialogue-tree⋆)
open import EffectfulForcing.Internal.LambdaWithoutOracle
open import EffectfulForcing.Internal.SystemT
open import UF.Base using (transport₂ ; ap₂ ; ap₃)
open import MGS.hlevels using (hedberg)
open import MGS.MLTT using (has-decidable-equality)

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

-- Γ₁ ⊆ Γ₂ states that Γ₁ is a sub context of Γ₂
_⊆_ : (Γ₁ Γ₂ : Cxt) → Type
Γ₁ ⊆ Γ₂ = {σ : type} → ∈Cxt σ Γ₁ → ∈Cxt σ Γ₂

-- ⊆ is reflexive
⊆-refl : (Γ : Cxt) → Γ ⊆ Γ
⊆-refl Γ {σ} i = i

-- ⊆ is transitive
⊆-trans : {Γ₁ : Cxt} {Γ₂ : Cxt} {Γ₃ : Cxt}
         → Γ₁ ⊆ Γ₂ → Γ₂ ⊆ Γ₃ → Γ₁ ⊆ Γ₃
⊆-trans {Γ₁} {Γ₂} {Γ₃} p q {σ} i = q (p i)

＝⊆ : {Γ₁ Γ₂ : Cxt} (s1 s2 : Γ₁ ⊆ Γ₂) → Type
＝⊆ {Γ₁} {Γ₂} s1 s2 = {σ : type} (i : ∈Cxt σ Γ₁) → s1 i ＝ s2 i

{-
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
-}

⊆, : (Γ : Cxt) (τ : type) → Γ ⊆ (Γ ,, τ)
⊆, Γ τ {σ} i = ∈CxtS τ i

-- 〈〉 is the smallest element w.r.t. the ⊆Γ order
⊆〈〉 : (Γ : Cxt) → 〈〉 ⊆ Γ
⊆〈〉 Γ {σ} ()

{-
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
-}

-- Removes a type from the context, using a "pointer" to the type (i)
rmCxt : {Γ : Cxt} {σ : type} (i : ∈Cxt σ Γ) → Cxt
rmCxt {Γ ,, σ} {σ} (∈Cxt0 Γ) = Γ
rmCxt {Γ ,, τ} {σ} (∈CxtS τ i) = rmCxt i ,, τ

{-
-- Removing a type from a context is a sub-context of the initial context
→⊆Γ-rmCxt : {m : ℕ} {Γ : Cxt (succ m)} (i : Fin (succ m)) → ⊆Γ (rmCxt Γ i) Γ
→⊆Γ-rmCxt {m} {Γ , τ} Fin.𝟎 = ⊆ΓR τ (⊆-refl Γ)
→⊆Γ-rmCxt {succ m} {Γ , τ} (Fin.suc i) = ⊆ΓS τ (→⊆Γ-rmCxt i)

⊆Γ-rmCxt→ : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt (succ m)} (i : Fin (succ m))
           → ⊆Γ Γ₁ (rmCxt Γ₂ i) → ⊆Γ Γ₁ Γ₂
⊆Γ-rmCxt→ {n} {Γ₁} {m} {Γ₂} i h = ⊆-trans h (→⊆Γ-rmCxt i)

T＝type : {n : ℕ} {Γ : Cxt n} {σ τ : type}
       → τ ＝ σ
       → T Γ σ
       → T Γ τ
T＝type {n} {Γ} {σ} {.σ} refl t = t
-}

⊆,, : {Γ₁ Γ₂ : Cxt} (σ : type)
    → Γ₁ ⊆ Γ₂
    → (Γ₁ ,, σ) ⊆ (Γ₂ ,, σ)
⊆,, {Γ₁} {Γ₂} σ s {.σ} (∈Cxt0 .Γ₁) = ∈Cxt0 Γ₂
⊆,, {Γ₁} {Γ₂} σ s {τ} (∈CxtS .σ i) = ∈CxtS σ (s i)

＝⊆,, : {Γ₁ Γ₂ : Cxt} (s1 s2 : Γ₁ ⊆ Γ₂) (σ : type)
      → ＝⊆ s1 s2
      → ＝⊆ (⊆,, σ s1) (⊆,, σ s2)
＝⊆,, {Γ₁} {Γ₂} s1 s2 σ e {.σ} (∈Cxt0 .Γ₁) = refl
＝⊆,, {Γ₁} {Γ₂} s1 s2 σ e {τ} (∈CxtS .σ i) = ap (∈CxtS σ) (e i)

-- extends the context of a term
weaken : {Γ₁ : Cxt} {Γ₂ : Cxt} {σ : type}
          → Γ₁ ⊆ Γ₂
          → T Γ₁ σ
          → T Γ₂ σ
weaken {Γ₁} {Γ₂} {_}     sub Zero        = Zero
weaken {Γ₁} {Γ₂} {_}     sub (Succ t)    = Succ (weaken sub t)
weaken {Γ₁} {Γ₂} {_}     sub (Rec f g t) = Rec (weaken sub f) (weaken sub g) (weaken sub t)
weaken {Γ₁} {Γ₂} {σ}     sub (ν i)       = ν (sub i)
weaken {Γ₁} {Γ₂} {σ ⇒ τ} sub (ƛ t)       = ƛ (weaken (⊆,, σ sub) t)
weaken {Γ₁} {Γ₂} {σ}     sub (t · t₁)    = weaken sub t · weaken sub t₁

-- extends the context of a closed term
weaken₀ : {Γ : Cxt} {σ : type} → T₀ σ → T Γ σ
weaken₀ {Γ} {σ} t = weaken (⊆〈〉 Γ) t

-- extends the context with one type
weaken, : {Γ : Cxt} {σ : type} (τ : type) → T Γ σ → T (Γ ,, τ) σ
weaken, {Γ} {σ} τ t = weaken {Γ} {Γ ,, τ} (⊆, Γ τ) t

{-
⊆ΓFin-refl : {n : ℕ} {Γ₁ Γ₂ : Cxt n} (i : Fin n) (s : ⊆Γ Γ₁ Γ₂) → Γ₁ ＝ Γ₂ → ⊆ΓFin s i ＝ i
⊆ΓFin-refl {.(succ _)} {Γ₁ , τ} {.Γ₁ , .τ} i (⊆ΓR .τ s) refl = 𝟘-elim (¬⊆, s)
⊆ΓFin-refl {.(succ _)} {Γ₁ , τ} {.(Γ₂ , τ)} Fin.𝟎 (⊆ΓS {Γ₂ = Γ₂} .τ s) e = refl
⊆ΓFin-refl {.(succ _)} {Γ₁ , τ} {.(Γ₂ , τ)} (Fin.suc i) (⊆ΓS {Γ₂ = Γ₂} .τ s) e =
 ap Fin.suc (⊆ΓFin-refl i s (pr₁ (from-×-＝' e)))
-}

＝⇒ : {σ₁ σ₂ τ₁ τ₂ : type} → σ₁ ⇒ σ₂ ＝ τ₁ ⇒ τ₂ → (σ₁ ＝ τ₁) × (σ₂ ＝ τ₂)
＝⇒ {σ₁} {σ₂} {.σ₁} {.σ₂} refl = refl , refl

＝,, : {Γ Δ : Cxt} {σ τ : type} → Γ ,, σ ＝ Δ ,, τ → (Γ ＝ Δ) × (σ ＝ τ)
＝,, {Γ} {.Γ} {σ} {.σ} refl = refl , refl

dec-type : has-decidable-equality type
dec-type ι ι = inl refl
dec-type ι (τ ⇒ τ₁) = inr (λ ())
dec-type (σ ⇒ σ₁) ι = inr (λ ())
dec-type (σ ⇒ σ₁) (τ ⇒ τ₁) with dec-type σ τ | dec-type σ₁ τ₁
... | inl refl | inl refl = inl refl
... | inl refl | inr q = inr (λ z → q (pr₂ (＝⇒ z)))
... | inr p | _ = inr (λ z → p (pr₁ (＝⇒ z)))

＝type-refl : {σ : type} (e : σ ＝ σ) → e ＝ refl
＝type-refl {σ} e = hedberg dec-type σ σ e refl

dec-Cxt : has-decidable-equality Cxt
dec-Cxt 〈〉 〈〉 = inl refl
dec-Cxt 〈〉 (Δ ,, x) = inr (λ ())
dec-Cxt (Γ ,, x) 〈〉 = inr (λ ())
dec-Cxt (Γ ,, σ) (Δ ,, τ) with dec-Cxt Γ Δ | dec-type σ τ
... | inl refl | inl refl = inl refl
... | inl refl | inr q = inr (λ x → q (pr₂ (＝,, x)))
... | inr p | _ = inr (λ x → p (pr₁ (＝,, x)))

＝Cxt-refl : {Γ : Cxt} (e : Γ ＝ Γ) → e ＝ refl
＝Cxt-refl {Γ} e = hedberg dec-Cxt Γ Γ e refl

{-
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
-}

⌜star⌝ : {X Y A : type} {Γ : Cxt}
       → T Γ ((⌜B⌝ (X ⇒ Y) A) ⇒ ⌜B⌝ X A ⇒ ⌜B⌝ Y A)
⌜star⌝ =
 ƛ (ƛ (⌜kleisli-extension⌝
       · ƛ (⌜B-functor⌝
            · ƛ (ν₀ · ν₁)
            · ν₂)
       · ν₀))

-- λη.λβ.t (λs.f (λg.η(g s)) β) β
⌜app⌝ : {A : type} {σ τ : type} {Γ : Cxt}
       (f : T Γ (⌜B⌝ (σ ⇒ τ) A)) (t : T Γ (⌜B⌝ σ A)) → T Γ (⌜B⌝ τ A)
⌜app⌝ {A} {σ} {τ} {Γ} f t = ⌜star⌝ · f · t

-- indirect relation that relates
-- (1) internal terms of a Church-encoded dialogue tree type
-- (2) external Church-encoded dialogue trees
⌜R⌝ : ({A} σ : type) → T₀ (⌜B⌝ σ A) → B⋆〖 σ 〗 〖 A 〗 → Type
⌜R⌝ ι       t d = ⟦ t ⟧₀ ＝ d
⌜R⌝ {A} (σ ⇒ τ) f g = (t : T₀ (⌜B⌝ σ A))
                 (d : B⋆〖 σ 〗 〖 A 〗)
               → ⌜R⌝ σ t d
               → ⌜R⌝ τ (⌜app⌝ f t) (g d)

CXT : (Γ : Cxt) (A : type) → Type
CXT Γ A = {σ : type} (i : ∈Cxt σ Γ) → T₀ (⌜B⌝ σ A)

⌜Rs⌝ : {Γ : Cxt} {A : type}
    → CXT Γ A → B⋆【 Γ 】 〖 A 〗 → Type
⌜Rs⌝ {Γ} xs ys = {σ : type} (i : ∈Cxt σ Γ) → ⌜R⌝ σ (xs i) (ys i)

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

⌜main-lemma⌝₁ : {Γ : Cxt}
                {σ : type}
                (t : T Γ σ)
                (α : Baire)
                (xs : 【 Γ 】)
--               (ys : IB【 Γ 】 ((ι ⇒ ι) ⇒ ι))
--             → R⋆s α xs ys
              → R⋆₁ α (⟦ t ⟧ xs) (ƛ (ƛ (ƛ Zero))) --(close ⌜ t ⌝ ys)
⌜main-lemma⌝₁ {Γ} {σ} t α xs {--ys rxys--} = {!!}

Sub : (Γ₁ Γ₂ : Cxt) → Type
Sub Γ₁ Γ₂ = {σ : type} (i : ∈Cxt σ Γ₁) → T Γ₂ σ

Sub₀ : (Γ : Cxt) → Type
Sub₀ Γ = Sub Γ 〈〉

＝Sub : {Γ₁ Γ₂ : Cxt} (s1 s2 : Sub Γ₁ Γ₂) → Type
＝Sub {Γ₁} {Γ₂} s1 s2 = {σ : type} (i : ∈Cxt σ Γ₁) → s1 i ＝ s2 i

Subƛ : {Γ₁ Γ₂ : Cxt} {σ : type}
      → Sub Γ₁ Γ₂
      → Sub (Γ₁ ,, σ) (Γ₂ ,, σ)
Subƛ {Γ₁} {Γ₂} {σ} s {.σ} (∈Cxt0 .Γ₁) = ν₀
Subƛ {Γ₁} {Γ₂} {σ} s {τ} (∈CxtS .σ i) = weaken, σ (s i)

Sub,, : {Γ₁ Γ₂ : Cxt} {σ : type} (s : Sub Γ₁ Γ₂) (t : T Γ₂ σ) → Sub (Γ₁ ,, σ) Γ₂
Sub,, {Γ₁} {Γ₂} {σ} s t {.σ} (∈Cxt0 .Γ₁) = t
Sub,, {Γ₁} {Γ₂} {σ} s t {τ} (∈CxtS .σ i) = s i

＝Subƛ : {Γ₁ Γ₂ : Cxt} (s1 s2 : Sub Γ₁ Γ₂) (σ : type)
        → ＝Sub s1 s2
        → ＝Sub (Subƛ {Γ₁} {Γ₂} {σ} s1) (Subƛ s2)
＝Subƛ {Γ₁} {Γ₂} s1 s2 σ e {.σ} (∈Cxt0 .Γ₁) = refl
＝Subƛ {Γ₁} {Γ₂} s1 s2 σ e {τ} (∈CxtS .σ i) = ap (weaken, σ) (e i)

{-
suc-inj : {n : ℕ} (i j : Fin n) → Fin.suc i ＝ Fin.suc j → i ＝ j
suc-inj {n} i .i refl = refl

_=?_ : {n : ℕ} (i j : Fin n) → (i ＝ j) + ¬ (i ＝ j)
Fin.𝟎 =? Fin.𝟎 = inl refl
Fin.𝟎 =? Fin.suc j = inr (λ ())
Fin.suc i =? Fin.𝟎 = inr (λ ())
Fin.suc i =? Fin.suc j with i =? j
... | inl p = inl (ap Fin.suc p)
... | inr p = inr λ q → p (suc-inj i j q)
-}

subν : {Γ : Cxt} {σ : type} (j : ∈Cxt σ Γ) {τ : type} (i : ∈Cxt τ Γ) → T₀ τ → T (rmCxt i) σ
subν {.(Γ ,, σ)} {σ} (∈Cxt0 Γ) {.σ} (∈Cxt0 .Γ) u = weaken₀ u
subν {.(Γ ,, σ)} {σ} (∈Cxt0 Γ) {τ} (∈CxtS .σ i) u = ν (∈Cxt0 (rmCxt i))
subν {.(_ ,, τ₁)} {σ} (∈CxtS τ₁ j) {.τ₁} (∈Cxt0 _) u = ν j
subν {.(_ ,, τ₁)} {σ} (∈CxtS τ₁ j) {τ} (∈CxtS .τ₁ i) u = weaken, τ₁ (subν j i u)

sub : {σ : type} {Γ : Cxt} {τ : type} → T Γ σ → (i : ∈Cxt τ Γ) → T₀ τ → T (rmCxt i) σ
sub {_}       {Γ} {τ} Zero        i u = Zero
sub {_}       {Γ} {τ} (Succ t)    i u = Succ (sub t i u)
sub {_}       {Γ} {τ} (Rec f g t) i u = Rec (sub f i u) (sub g i u) (sub t i u)
sub {σ}       {Γ} {τ} (ν j)       i u = subν j i u
sub {σ₁ ⇒ σ₂} {Γ} {τ} (ƛ t)       i u = ƛ (sub {σ₂} {Γ ,, σ₁} {τ} t (∈CxtS _ i) u)
sub {σ}       {Γ} {τ} (t₁ · t₂)   i u = sub t₁ i u · sub t₂ i u

sub₀ : {σ : type} {Γ : Cxt} {τ : type} → T (Γ ,, τ) σ → T₀ τ → T Γ σ
sub₀ {σ} {Γ} {τ} t u = sub t (∈Cxt0 Γ) u

{-
-- This can either be defined through a succession of applications
close-ap : {σ : type} {n : ℕ} {Γ : Cxt n} → T Γ σ → Sub₀ Γ → T₀ σ
close-ap {σ} {zero} {Γ} t s = t
close-ap {σ} {succ n} {Γ , τ} t s =
 close-ap (ƛ t · weaken₀ (s Fin.𝟎))
          (λ i → s (Fin.suc i))
-}

close : {σ : type} {Γ₁ Γ₂ : Cxt} → T Γ₁ σ → Sub Γ₁ Γ₂ → T Γ₂ σ
close {_}       {Γ₁} {Γ₂} Zero        s = Zero
close {_}       {Γ₁} {Γ₂} (Succ t)    s = Succ (close t s)
close {_}       {Γ₁} {Γ₂} (Rec f g t) s = Rec (close f s) (close g s) (close t s)
close {σ}       {Γ₁} {Γ₂} (ν i)       s = s i
close {σ₁ ⇒ σ₂} {Γ₁} {Γ₂} (ƛ t)       s = ƛ (close t (Subƛ s))
close {σ}       {Γ₁} {Γ₂} (t₁ · t₂)   s = close t₁ s · close t₂ s

Sub1 : {Γ : Cxt} {τ : type} → T Γ τ → Sub (Γ ,, τ) Γ
Sub1 {Γ} {τ} t {.τ} (∈Cxt0 .Γ) = t
Sub1 {Γ} {τ} t {σ} (∈CxtS .τ i) = ν i

close₀ : {σ τ : type} {Γ : Cxt} → T (Γ ,, τ) σ → T Γ τ → T Γ σ
close₀ {σ} {τ} {Γ} t u = close {σ} {Γ ,, τ} {Γ} t (Sub1 u)

{-
close· : {σ τ : type} {Γ : Cxt} → (t : T Γ (σ ⇒ τ)) (u : T Γ σ) (s : Sub₀ Γ)
       → close (t · u) s ＝ close t s · close u s
close· {σ} {τ} {Γ} t u s = refl
-}

{-
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
-}

{-
-- call-by-name semantics
step : {Γ : Cxt} {σ : type} (t : T Γ σ) → T Γ σ
step {Γ} {σ} t = {!!}
{-
step {Γ} {_} Zero = Zero
step {Γ} {_} Succ = Succ
step {Γ} {_} Rec = Rec
step {Γ} {σ} (ν i) = ν i
step {Γ} {σ ⇒ τ} (ƛ t) = ƛ t
-- app case
step {Γ} {_} (Succ · a) = Succ · a
step {Γ} {_} (Rec · a) = Rec · a
step {Γ} {σ} (ν i · a) = ν i · a
step {Γ} {σ} (ƛ f · a) = close₀ f a -- reduces (beta)
step {Γ} {_} (Rec · a₁ · a₂) = Rec · a₁ · a₂
step {Γ} {σ} (ν i · a₁ · a₂) = ν i · a₁ · a₂
step {Γ} {σ} (ƛ f · a₁ · a₂) = (close₀ f a₁) · a₂ -- reduces (nested beta)
step {Γ} {σ} (Rec · f · g · Zero) = g -- reduces (rec/zero)
step {Γ} {σ} (Rec · f · g · ν i) = Rec · f · g · ν i
step {Γ} {σ} (Rec · f · g · (Succ · a)) = f · a · (Rec · f · g · a) -- reduces (rec/succ)
step {Γ} {σ} (Rec · f · g · (ν i · a)) = Rec · f · g · (ν i · a)
step {Γ} {σ} (Rec · f · g · (ƛ h · a)) = Rec · f · g · close₀ h a -- reduces (nested beta)
step {Γ} {σ} (Rec · f · g · (h · h₁ · a)) = Rec · f · g · step (h · h₁ · a) -- reduces (nested red)
step {Γ} {σ} (ν i · a₁ · a₂ · a₃) = ν i · a₁ · a₂ · a₃
step {Γ} {σ} (ƛ f · a₁ · a₂ · a₃) = (close₀ f a₁) · a₂ · a₃ -- reduces (nested beta)
step {Γ} {σ} (f · a₁ · a₂ · a₃ · a₄) = step (f · a₁ · a₂ · a₃) · a₄ -- reduces (nested red)
-}
-}

{-
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

⊆-trans-refl : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (s : ⊆Γ Γ₁ Γ₂)
              → ⊆-trans s (⊆-refl Γ₂) ＝ s
⊆-trans-refl {n} {Γ₁} {zero} {〈〉} s = refl
⊆-trans-refl {n} {Γ₁} {succ m} {Γ₂ , τ} (⊆ΓR .τ s) = ap (⊆ΓR τ) (⊆-trans-refl s)
⊆-trans-refl {.(succ _)} {.(_ , τ)} {succ m} {Γ₂ , τ} (⊆ΓS .τ s) = ap (⊆ΓS τ) (⊆-trans-refl s)

⊆Γ-rmCxt→⊆〈〉 : {n : ℕ} (Γ : Cxt n) (τ : type) → ⊆Γ-rmCxt→ Fin.𝟎 (⊆〈〉 Γ) ＝ ⊆〈〉 (Γ , τ)
⊆Γ-rmCxt→⊆〈〉 {n} Γ τ = ap (⊆ΓR τ) (⊆-trans-refl (⊆〈〉 Γ))

transport⁻¹ν-as-weaken, : {n : ℕ} {Γ₁ : Cxt n} {m : ℕ} {Γ₂ : Cxt m} (s : ⊆Γ Γ₁ Γ₂) (i : Fin n) (τ : type)
                          (j : Fin m) (σ : type) (e : σ ＝ Γ₂ [ j ])
                       → transport⁻¹ (T (Γ₂ , τ)) e (ν (Fin.suc j))
                       ＝ weaken, τ (transport⁻¹ (T Γ₂) e (ν j))
transport⁻¹ν-as-weaken, {n} {Γ₁} {m} {Γ₂} s i τ j .(Γ₂ [ j ]) refl =
 transport⁻¹ (T (Γ₂ , τ)) refl (ν (Fin.suc j))
  ＝⟨ refl ⟩
 ν (Fin.suc j)
  ＝⟨ (h (⊆-refl Γ₂) (⊆Γ[] j (⊆-refl Γ₂))) ⁻¹ ⟩
 transport⁻¹ (T (Γ₂ , τ)) (⊆Γ[] j (⊆-refl Γ₂)) (ν (Fin.suc (⊆ΓFin (⊆-refl Γ₂) j)))
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
   (⊆-trans-refl s)
   refl
subν-diff {n} {Γ₁} {.(succ _)} {Γ₂ , τ} {Fin.suc i} (⊆ΓR τ s) i₁ u nf =
 transport⁻¹ (T (rmCxt Γ₂ i , τ)) (⊆Γ[] i₁ (⊆-trans s (→⊆Γ-rmCxt i))) (weaken, τ (subν i (⊆ΓFin (⊆-trans s (→⊆Γ-rmCxt i)) i₁) u))
  ＝⟨ transport⁻¹-weaken, (subν i (⊆ΓFin (⊆-trans s (→⊆Γ-rmCxt i)) i₁) u) (⊆Γ[] i₁ (⊆-trans s (→⊆Γ-rmCxt i))) ⟩
 weaken, τ (transport⁻¹ (T (rmCxt Γ₂ i)) (⊆Γ[] i₁ (⊆-trans s (→⊆Γ-rmCxt i))) (subν i (⊆ΓFin (⊆-trans s (→⊆Γ-rmCxt i)) i₁) u))
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
   (⊆-trans-refl s)
   refl
subν-diff {succ n} {Γ₁ , τ₂} {succ m} {(Γ₂ , τ₀) , .τ₂} {Fin.suc i} (⊆ΓS τ₂ s) Fin.𝟎 u nf = refl
subν-diff {succ n} {Γ₁ , τ₂} {succ m} {(Γ₂ , τ₀) , .τ₂} {Fin.suc i} (⊆ΓS τ₂ s) (Fin.suc i₁) u nf =
 transport⁻¹ (T (rmCxt (Γ₂ , τ₀) i , τ₂)) (⊆Γ[] i₁ (⊆-trans s (→⊆Γ-rmCxt i))) (weaken, τ₂ (subν i (⊆ΓFin (⊆-trans s (→⊆Γ-rmCxt i)) i₁) u))
  ＝⟨ transport⁻¹-weaken, (subν i (⊆ΓFin (⊆-trans s (→⊆Γ-rmCxt i)) i₁) u) (⊆Γ[] i₁ (⊆-trans s (→⊆Γ-rmCxt i))) ⟩
 weaken, τ₂ (transport⁻¹ (T (rmCxt (Γ₂ , τ₀) i)) (⊆Γ[] i₁ (⊆-trans s (→⊆Γ-rmCxt i))) (subν i (⊆ΓFin (⊆-trans s (→⊆Γ-rmCxt i)) i₁) u))
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
-}

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

{-
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
-}

-- Compared to R⋆₁, this version relates a T₀ (B-type〖 σ 〗 ((ι ⇒ ι) ⇒ ι))
-- instead of T₀ (⌜B⌝ σ ((ι ⇒ ι) ⇒ ι))
--
-- As opposed to ⌜R⌝, this is a more direct relation that relates
-- (1) the standard semantics
-- (2) internal terms of a Church-encoded dialogue tree type
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

-- internal semantics of contexts as dialogue trees
IB【_】 : Cxt → type → Type
IB【 Γ 】 A = Sub₀ (B-context【 Γ 】 A)

{-
T₀-B-context-sel : {A : type} (Γ : Cxt) {σ : type} (i : ∈Cxt σ (B-context【 Γ 】 A))
                 → T₀ σ
                 → T₀ (B-type〖 σ 〗 A)
T₀-B-context-sel {A} Γ {σ} i t = {!!}
{- {.(succ _)} Γ {Fin.𝟎} t = t
T₀-B-context-sel {A} {.(succ _)} Γ {Fin.suc i} t = T₀-B-context-sel (pr₁ Γ) t
-}
-}

R⋆s : Baire → {Γ : Cxt}
  → 【 Γ 】 → IB【 Γ 】 ((ι ⇒ ι) ⇒ ι) → Type
R⋆s α {Γ} xs ys = {σ : type} (i : ∈Cxt σ Γ) → R⋆ α (xs i) (ys (∈Cxt-B-type i))

【sub】 : {Γ : Cxt} (s : Sub₀ Γ) → 【 Γ 】
【sub】 {Γ} s i = ⟦ s i ⟧₀

{-
close-⌜zero⌝ : {σ : type} {Γ : Cxt} (ys : IB【 Γ 】 σ)
            → close (⌜zero⌝ {σ}) ys ＝ ⌜zero⌝
close-⌜zero⌝ {σ} {Γ} ys = refl

close-⌜succ⌝ : {σ : type} {Γ : Cxt} (ys : IB【 Γ 】 σ)
            → close (⌜succ⌝ {σ}) ys ＝ ⌜succ⌝
close-⌜succ⌝ {σ} {Γ} ys = refl
-}

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

{-
RR⋆₀ : (σ : type) → (d :  T₀ σ) → Type
RR⋆₀ ι       succ (⟦ ⌜ d ⌝ ⟧₀ η β α) ＝ ⟦ ⌜ d ⌝ ⟧₀ (η · succ) β α
RR⋆₀ (σ ⇒ τ) f g = (x : B⋆〖 σ 〗 (B ℕ))
                   (y : B〖 σ 〗)
               → RR⋆₀ σ x y ?
               → RR⋆₀ τ (f x η' β') (g y η' β') ?
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

∈Cxt-B-context : {σ : type} {Γ : Cxt} {A : type} {Δ : Cxt}
               → Δ ＝ B-context【 Γ 】 A
               → (i : ∈Cxt σ Δ)
               → Σ τ ꞉ type , ∈Cxt τ Γ × {-(i ＝ ∈Cxt-B-type j) ×-} (σ ＝ B-type〖 τ 〗 A)
∈Cxt-B-context {.(B-type〖 x 〗 A)} {Γ ,, x} {A} {.(B-context【 Γ 】 A ,, B-type〖 x 〗 A)} refl (∈Cxt0 .(B-context【 Γ 】 A)) =
 x , ∈Cxt0 _ , refl
∈Cxt-B-context {σ} {Γ ,, x} {A} {.(B-context【 Γ 】 A ,, B-type〖 x 〗 A)} refl (∈CxtS .(B-type〖 x 〗 A) i)
 with ∈Cxt-B-context {σ} {Γ} {A} {B-context【 Γ 】 A} refl i
... | τ , j , e = τ , ∈CxtS x j , e

∈Cxt-B-context' : {σ : type} {Γ : Cxt} {A : type} {Δ : Cxt}
                → (e : Δ ＝ B-context【 Γ 】 A)
                → (i : ∈Cxt σ Δ)
                → Σ τ ꞉ type , Σ z ꞉ σ ＝ B-type〖 τ 〗 A , Σ j ꞉ ∈Cxt τ Γ ,
                   transport (λ σ → ∈Cxt σ (B-context【 Γ 】 A)) z (transport (∈Cxt σ) e i) ＝ ∈Cxt-B-type j
∈Cxt-B-context' {.(B-type〖 x 〗 A)} {Γ ,, x} {A} {.(B-context【 Γ 】 A ,, B-type〖 x 〗 A)} refl (∈Cxt0 .(B-context【 Γ 】 A)) =
 x , refl , ∈Cxt0 _ , refl
∈Cxt-B-context' {σ} {Γ ,, x} {A} {.(B-context【 Γ 】 A ,, B-type〖 x 〗 A)} refl (∈CxtS .(B-type〖 x 〗 A) i)
 with ∈Cxt-B-context' {σ} {Γ} {A} {B-context【 Γ 】 A} refl i
... | τ , refl , j , w = τ , refl , ∈CxtS x j , ap (∈CxtS (B-type〖 x 〗 A)) w

∈Cxt-B-context'' : {σ : type} {Γ : Cxt} {A : type}
                 → (i : ∈Cxt σ (B-context【 Γ 】 A))
                 → Σ τ ꞉ type , Σ z ꞉ σ ＝ B-type〖 τ 〗 A , Σ j ꞉ ∈Cxt τ Γ ,
                    transport (λ σ → ∈Cxt σ (B-context【 Γ 】 A)) z i ＝ ∈Cxt-B-type j
∈Cxt-B-context'' {σ} {Γ} {A} = ∈Cxt-B-context' refl

{-
∈Cxt-B-context {σ : type} {Γ : Cxt} {A : type} {Δ : Cxt}
               → (e : Δ ＝ B-context【 Γ 】 A)
               → (i : ∈Cxt σ Δ)
               → i ＝ pr₁ (pr₂ (∈Cxt-B-context e i))
-}

⌜Sub⌝ : {A : type} {Γ Δ : Cxt} (s : Sub Γ Δ) → Sub (B-context【 Γ 】 A) (B-context【 Δ 】 A)
⌜Sub⌝ {A} {Γ} {Δ} s {σ} i
 with ∈Cxt-B-context'' {σ} {Γ} {A} i
... | τ , refl , j , z = ⌜ s j ⌝

⊆-B-context : {A : type} {Γ₁ Γ₂ : Cxt}
            → Γ₁ ⊆ Γ₂
            → B-context【 Γ₁ 】 A ⊆ B-context【 Γ₂ 】 A
⊆-B-context {A} {Γ₁} {Γ₂} s {σ} i with ∈Cxt-B-context'' {σ} {Γ₁} {A} i
... | τ , refl , j , z = ∈Cxt-B-type (s j)

＝⊆-∈CxtS-B-type : {A : type} {Γ : Cxt} (σ : type)
                 → ＝⊆ (∈CxtS {_} {B-context【 Γ 】 A} (B-type〖 σ 〗 A))
                       (⊆-B-context (∈CxtS σ))
＝⊆-∈CxtS-B-type {A} {Γ} σ {τ} i
 with ∈Cxt-B-context'' i
... | x , refl , j , z = ap (∈CxtS (B-type〖 σ 〗 A)) z

-- weaken and ⌜kleisli-extension⌝
weaken-⌜Kleisli-extension⌝ : {X A : type} {Γ₁ Γ₂ : Cxt}
                             (s : Γ₁ ⊆ Γ₂)
                             {σ : type}
                           → ⌜Kleisli-extension⌝ {X} {A} {σ} ＝ weaken s (⌜Kleisli-extension⌝ {X} {A} {σ})
weaken-⌜Kleisli-extension⌝ {X} {A} {Γ₁} {Γ₂} s {ι} = refl
weaken-⌜Kleisli-extension⌝ {X} {A} {Γ₁} {Γ₂} s {σ ⇒ σ₁} =
 ap ƛ (ap ƛ (ap ƛ (ap₂ _·_ (ap₂ _·_ (weaken-⌜Kleisli-extension⌝ _) refl) refl)))

-- weaken and ⌜rec⌝
weaken-⌜rec⌝ : {A : type} {Γ₁ Γ₂ : Cxt} (s : Γ₁ ⊆ Γ₂) {σ : type}
             → ⌜rec⌝ {σ} {A} ＝ weaken s (⌜rec⌝ {σ} {A})
weaken-⌜rec⌝ {A} {Γ₁} {Γ₂} s {σ} =
 ap ƛ (ap ƛ (ap₂ _·_ (weaken-⌜Kleisli-extension⌝ _) refl))

-- close and ⌜kleisli-extension⌝
close-⌜Kleisli-extension⌝ : {X A : type} {Γ₁ Γ₂ : Cxt}
                             (s : Sub Γ₁ Γ₂)
                             {σ : type}
                           → ⌜Kleisli-extension⌝ {X} {A} {σ} ＝ close (⌜Kleisli-extension⌝ {X} {A} {σ}) s
close-⌜Kleisli-extension⌝ {X} {A} {Γ₁} {Γ₂} s {ι} = refl
close-⌜Kleisli-extension⌝ {X} {A} {Γ₁} {Γ₂} s {σ ⇒ σ₁} =
 ap ƛ (ap ƛ (ap ƛ (ap₂ _·_ (ap₂ _·_ (close-⌜Kleisli-extension⌝ _) refl) refl)))

-- close and ⌜rec⌝
close-⌜rec⌝ : {A : type} {Γ₁ Γ₂ : Cxt} (s : Sub Γ₁ Γ₂) {σ : type}
             → ⌜rec⌝ {σ} {A} ＝ close (⌜rec⌝ {σ} {A}) s
close-⌜rec⌝ {A} {Γ₁} {Γ₂} s {σ} =
 ap ƛ (ap ƛ (ap₂ _·_ (close-⌜Kleisli-extension⌝ _) refl))


＝B-type : {A σ τ : type}
         → B-type〖 σ 〗 A ＝ B-type〖 τ 〗 A
         → σ ＝ τ
＝B-type {A} {ι} {ι} e = refl
＝B-type {A} {ι} {ι ⇒ σ₁} e with ＝⇒ e
... | e₁ , e₂ with ＝⇒ e₁
... | () , e₄
＝B-type {A} {ι} {(ι ⇒ σ₃) ⇒ σ₁} e with ＝⇒ e
... | e₁ , e₂ with ＝⇒ e₁
... | () , e₄
＝B-type {A} {ι} {((σ₄ ⇒ σ₅) ⇒ σ₃) ⇒ σ₁} e with ＝⇒ e
... | e₁ , e₂ with ＝⇒ e₁
... | () , e₄
＝B-type {A} {ι ⇒ σ₁} {ι} e with ＝⇒ e
... | e₁ , e₂ with ＝⇒ e₁
... | () , e₄
＝B-type {A} {(ι ⇒ σ₃) ⇒ σ₁} {ι} e with ＝⇒ e
... | e₁ , e₂ with ＝⇒ e₁
... | () , e₄
＝B-type {A} {((σ₄ ⇒ σ₅) ⇒ σ₃) ⇒ σ₁} {ι} e with ＝⇒ e
... | e₁ , e₂ with ＝⇒ e₁
... | () , e₄
-- Why do we need to split the LHS of the left type here???
＝B-type {A} {ι ⇒ σ₁} {τ ⇒ τ₁} e with ＝⇒ e
... | e₁ , e₂ with ＝B-type {A} {ι} e₁ | ＝B-type e₂
... | refl | refl = refl
＝B-type {A} {(ι ⇒ σ₃) ⇒ σ₁} {τ ⇒ τ₁} e with ＝⇒ e
... | e₁ , e₂ with ＝B-type {A} {ι ⇒ σ₃} e₁ | ＝B-type e₂
... | refl | refl = refl
＝B-type {A} {((σ₄ ⇒ σ₅) ⇒ σ₃) ⇒ σ₁} {τ ⇒ τ₁} e with ＝⇒ e
... | e₁ , e₂ with ＝B-type {A} {(σ₄ ⇒ σ₅) ⇒ σ₃} e₁ | ＝B-type e₂
... | refl | refl = refl

＝∈CxtS : {σ : type} {Γ : Cxt} (τ : type) → (i j : ∈Cxt σ Γ)
        → ∈CxtS τ i ＝ ∈CxtS τ j
        → i ＝ j
＝∈CxtS {σ} {Γ} τ i .i refl = refl

＝∈Cxt-B-type : {Γ : Cxt} {A : type} {σ : type} (i j : ∈Cxt σ Γ)
              → ∈Cxt-B-type {Γ} {A} {σ} i ＝ ∈Cxt-B-type j
              → i ＝ j
＝∈Cxt-B-type {Γ ,, σ} {A} {σ} (∈Cxt0 Γ) j e = p (Γ ,, σ) j refl e
 where
  p : (Δ : Cxt) (j : ∈Cxt σ Δ) (z : Δ ＝ Γ ,, σ)
      (e : ∈Cxt0 (B-context【 Γ 】 A) ＝ transport (λ Δ → ∈Cxt (B-type〖 σ 〗 A) (B-context【 Δ 】 A)) z (∈Cxt-B-type j))
    → ∈Cxt0 Γ ＝ transport (∈Cxt σ) z j
  p .(Γ ,, σ) (∈Cxt0 Γ) z e with ＝,, z
  ... | refl , e2 with ＝Cxt-refl z
  ... | refl = refl
  p .(Γ ,, τ) (∈CxtS τ j) refl ()
＝∈Cxt-B-type {Γ ,, τ} {A} {σ} (∈CxtS τ i) (∈CxtS τ j) e = ap (∈CxtS τ) (＝∈Cxt-B-type i j (＝∈CxtS _ _ _ e))

-- weaken and ⌜ ⌝ - ν case
⊆-B-context-∈Cxt-B-type : {A : type} {Γ₁ Γ₂ : Cxt} {σ : type} (i : ∈Cxt σ Γ₁) (s : Γ₁ ⊆ Γ₂)
                        → ∈Cxt-B-type {_} {A} (s i) ＝ ⊆-B-context s (∈Cxt-B-type i)
⊆-B-context-∈Cxt-B-type {A} {Γ₁ ,, σ} {Γ₂} {σ} (∈Cxt0 Γ) s = refl
⊆-B-context-∈Cxt-B-type {A} {Γ₁ ,, τ} {Γ₂} {σ} (∈CxtS τ i) s
-- with ∈Cxt-B-context {σ} {Γ₁} {A} {Γ₁} {!!} i
 with ∈Cxt-B-context'' {B-type〖 σ 〗 A} {Γ₁} {A} (∈Cxt-B-type i)
-- ∈Cxt-B-context {B-type〖 σ 〗 A} {Γ₁ ,, τ} {A} {B-context【 Γ₁ ,, τ 】 A} refl (∈CxtS (B-type〖 τ 〗 A) (∈Cxt-B-type i))
... | τ₁ , e , j , z with ＝B-type e
... | refl with ＝type-refl e
... | refl with ＝∈Cxt-B-type i j z
... | refl = refl

weaken-eta : {Γ₁ : Cxt} {Γ₂ : Cxt} {σ : type} (s1 s2 : Γ₁ ⊆ Γ₂) (t : T Γ₁ σ)
           → ＝⊆ s1 s2
           → weaken s1 t ＝ weaken s2 t
weaken-eta {Γ₁} {Γ₂} {.ι}    s1 s2 Zero e = refl
weaken-eta {Γ₁} {Γ₂} {.ι}    s1 s2 (Succ t) e = ap Succ (weaken-eta s1 s2 t e)
weaken-eta {Γ₁} {Γ₂} {σ}     s1 s2 (Rec t t₁ t₂) e = ap₃ Rec (weaken-eta s1 s2 t e) (weaken-eta s1 s2 t₁ e) (weaken-eta s1 s2 t₂ e)
weaken-eta {Γ₁} {Γ₂} {σ}     s1 s2 (ν i) e = ap ν (e i)
weaken-eta {Γ₁} {Γ₂} {σ ⇒ τ} s1 s2 (ƛ t) e = ap ƛ (weaken-eta (⊆,, σ s1) (⊆,, σ s2) t (＝⊆,, s1 s2 σ e))
weaken-eta {Γ₁} {Γ₂} {σ}     s1 s2 (t · t₁) e = ap₂ _·_ (weaken-eta s1 s2 t e) (weaken-eta s1 s2 t₁ e)

＝⊆-⊆-B-context : {A : type} {Γ₁ Γ₂ : Cxt} {σ : type} (s : Γ₁ ⊆ Γ₂)
               → ＝⊆ (⊆-B-context (⊆,, σ s)) (⊆,, (B-type〖 σ 〗 A) (⊆-B-context s))
＝⊆-⊆-B-context {A} {Γ₁} {Γ₂} {σ} s {.(B-type〖 σ 〗 A)} (∈Cxt0 .(B-context【 Γ₁ 】 A)) = refl
＝⊆-⊆-B-context {A} {Γ₁} {Γ₂} {σ} s {τ} (∈CxtS .(B-type〖 σ 〗 A) i)
 with  ∈Cxt-B-context'' {τ} {Γ₁} {A} i
... | x , refl , j , z = refl

-- weaken and ⌜ ⌝
⌜weaken⌝ : {A : type} {Γ₁ Γ₂ : Cxt} (s : Γ₁ ⊆ Γ₂) {σ : type} (t : T Γ₁ σ)
   → ⌜ weaken s t ⌝ ＝ weaken (⊆-B-context {A} s) ⌜ t ⌝
⌜weaken⌝ {A} {Γ₁} {Γ₂} s {_} Zero = refl
⌜weaken⌝ {A} {Γ₁} {Γ₂} s {_} (Succ t) = ap (λ k → ⌜succ⌝ · k) (⌜weaken⌝ s t)
⌜weaken⌝ {A} {Γ₁} {Γ₂} s {σ} (Rec t t₁ t₂) =
 ⌜rec⌝ · ⌜ weaken s t ⌝ · ⌜ weaken s t₁ ⌝ · ⌜ weaken s t₂ ⌝
  ＝⟨ ap₃ (λ k1 k2 k3 → ⌜rec⌝ · k1 · k2 · k3) (⌜weaken⌝ s t) (⌜weaken⌝ s t₁) (⌜weaken⌝ s t₂) ⟩
 ⌜rec⌝ · weaken (⊆-B-context {A} s) ⌜ t ⌝ · weaken (⊆-B-context {A} s) ⌜ t₁ ⌝ · weaken (⊆-B-context {A} s) ⌜ t₂ ⌝
  ＝⟨ ap (λ k → k · weaken (⊆-B-context {A} s) ⌜ t ⌝ · weaken (⊆-B-context {A} s) ⌜ t₁ ⌝ · weaken (⊆-B-context {A} s) ⌜ t₂ ⌝) (weaken-⌜rec⌝ _) ⟩
 weaken (⊆-B-context {A} s) ⌜rec⌝ · weaken (⊆-B-context {A} s) ⌜ t ⌝ · weaken (⊆-B-context {A} s) ⌜ t₁ ⌝ · weaken (⊆-B-context {A} s) ⌜ t₂ ⌝
  ∎
⌜weaken⌝ {A} {Γ₁} {Γ₂} s {σ} (ν i) = ap ν (⊆-B-context-∈Cxt-B-type i s)
⌜weaken⌝ {A} {Γ₁} {Γ₂} s {σ₁ ⇒ σ₂} (ƛ t) = ap ƛ p
 where
  p : ⌜ weaken (⊆,, σ₁ s) t ⌝ ＝ weaken (⊆,, (B-type〖 σ₁ 〗 A) (⊆-B-context s)) ⌜ t ⌝
  p =
   ⌜ weaken (⊆,, σ₁ s) t ⌝
    ＝⟨ ⌜weaken⌝ (⊆,, σ₁ s) t ⟩
   weaken (⊆-B-context {A} (⊆,, σ₁ s)) ⌜ t ⌝
    ＝⟨ weaken-eta _ _ ⌜ t ⌝ (＝⊆-⊆-B-context s) ⟩
   weaken (⊆,, (B-type〖 σ₁ 〗 A) (⊆-B-context s)) ⌜ t ⌝
    ∎
⌜weaken⌝ {A} {Γ₁} {Γ₂} s {σ} (t · t₁) = ap₂ _·_ (⌜weaken⌝ s t) (⌜weaken⌝ s t₁)

Subƛ⌜Sub⌝ : {A : type} {Γ Δ : Cxt} {σ : type} (s : Sub Γ Δ)
           → ＝Sub (Subƛ {B-context【 Γ 】 A} {B-context【 Δ 】 A} {B-type〖 σ 〗 A} (⌜Sub⌝ s))
                   (⌜Sub⌝ (Subƛ {Γ} {Δ} {σ} s))
Subƛ⌜Sub⌝ {A} {Γ} {Δ} {σ} s {.(B-type〖 σ 〗 A)} (∈Cxt0 .(B-context【 Γ 】 A)) = refl
Subƛ⌜Sub⌝ {A} {Γ} {Δ} {σ} s {τ} (∈CxtS .(B-type〖 σ 〗 A) i) with ∈Cxt-B-context'' i
... | τ₂ , refl , j₂ , z₂ =
 weaken (∈CxtS (B-type〖 σ 〗 A)) ⌜ s j₂ ⌝
  ＝⟨ weaken-eta _ _  ⌜ s j₂ ⌝ (＝⊆-∈CxtS-B-type {A} {Δ} σ) ⟩
 weaken (⊆-B-context (λ i₁ → ∈CxtS σ i₁)) ⌜ s j₂ ⌝
  ＝⟨ ⌜weaken⌝ (⊆, Δ σ) (s j₂) ⁻¹ ⟩
 ⌜ weaken, σ (s j₂) ⌝
  ∎

-- cloes returns the same result given "equivalent" substitutions
close-eta : {Γ₁ : Cxt} {Γ₂ : Cxt} {σ : type} (s1 s2 : Sub Γ₁ Γ₂) (t : T Γ₁ σ)
           → ＝Sub s1 s2
           → close t s1 ＝ close t s2
close-eta {Γ₁} {Γ₂} {_}     s1 s2 Zero          e = refl
close-eta {Γ₁} {Γ₂} {_}     s1 s2 (Succ t)      e = ap Succ (close-eta s1 s2 t e)
close-eta {Γ₁} {Γ₂} {σ}     s1 s2 (Rec t t₁ t₂) e = ap₃ Rec (close-eta s1 s2 t e) (close-eta s1 s2 t₁ e) (close-eta s1 s2 t₂ e)
close-eta {Γ₁} {Γ₂} {σ}     s1 s2 (ν i)         e = e i
close-eta {Γ₁} {Γ₂} {σ ⇒ τ} s1 s2 (ƛ t)         e = ap ƛ (close-eta (Subƛ s1) (Subƛ s2) t (＝Subƛ s1 s2 σ e))
close-eta {Γ₁} {Γ₂} {σ}     s1 s2 (t · t₁)      e = ap₂ _·_ (close-eta s1 s2 t e) (close-eta s1 s2 t₁ e)

-- close and ⌜ ⌝
⌜close⌝ : {A : type} {σ : type} {Γ : Cxt} (t : T Γ σ) {Δ : Cxt} (s : Sub Γ Δ)
        → close ⌜ t ⌝ (⌜Sub⌝ {A} s) ＝ ⌜ close t s ⌝
⌜close⌝ {A} {_}       {Γ} Zero          {Δ} s = refl
⌜close⌝ {A} {_}       {Γ} (Succ t)      {Δ} s = ap (λ k → ⌜succ⌝ · k) (⌜close⌝ t s)
⌜close⌝ {A} {_}       {Γ} (Rec t t₁ t₂) {Δ} s =
 close ⌜rec⌝ (⌜Sub⌝ {A} s) · close ⌜ t ⌝ (⌜Sub⌝ {A} s) · close ⌜ t₁ ⌝ (⌜Sub⌝ {A} s) · close ⌜ t₂ ⌝ (⌜Sub⌝ {A} s)
  ＝⟨ ap (λ k → k · close ⌜ t ⌝ (⌜Sub⌝ {A} s) · close ⌜ t₁ ⌝ (⌜Sub⌝ {A} s) · close ⌜ t₂ ⌝ (⌜Sub⌝ {A} s)) ((close-⌜rec⌝ _) ⁻¹) ⟩
 ⌜rec⌝ · close ⌜ t ⌝ (⌜Sub⌝ {A} s) · close ⌜ t₁ ⌝ (⌜Sub⌝ {A} s) · close ⌜ t₂ ⌝ (⌜Sub⌝ {A} s)
  ＝⟨ ap₃ (λ k1 k2 k3 → ⌜rec⌝ · k1 · k2 · k3) (⌜close⌝ t s) (⌜close⌝ t₁ s) (⌜close⌝ t₂ s) ⟩
 ⌜rec⌝ · ⌜ close t s ⌝ · ⌜ close t₁ s ⌝ · ⌜ close t₂ s ⌝
  ∎
⌜close⌝ {A} {σ}       {Γ} (ν i)       {Δ} s
 with ∈Cxt-B-context'' {B-type〖 σ 〗 A} {Γ} {A} (∈Cxt-B-type i)
... | τ , e , j , z with ＝B-type e
... | refl with ＝type-refl e
... | refl with ＝∈Cxt-B-type i j z
... | refl = refl
⌜close⌝ {A} {σ₁ ⇒ σ₂} {Γ} (ƛ t)       {Δ} s = ap ƛ p
 where
  p : close ⌜ t ⌝ (Subƛ (⌜Sub⌝ s)) ＝ ⌜ close t (Subƛ s) ⌝
  p =
   close ⌜ t ⌝ (Subƛ (⌜Sub⌝ s))
    ＝⟨ close-eta {_} {_} {B-type〖 σ₂ 〗 A} (Subƛ (⌜Sub⌝ s)) (⌜Sub⌝ (Subƛ s)) ⌜ t ⌝ (Subƛ⌜Sub⌝ s) ⟩
   close ⌜ t ⌝ (⌜Sub⌝ {A} (Subƛ s))
    ＝⟨ ⌜close⌝ t (Subƛ s) ⟩
   ⌜ close t (Subƛ s) ⌝
    ∎
⌜close⌝ {A} {σ}       {Γ} (t · t₁)    {Δ} s = ap₂ _·_ (⌜close⌝ t s) (⌜close⌝ t₁ s)

R⋆-preserves-⟦⟧ : {α : Baire} {σ : type}
                  (a : 〖 σ 〗) (t u : T₀ σ)
                → ⟦ ⌜_⌝ {〈〉} {σ} {(ι ⇒ ι) ⇒ ι} t ⟧₀ ＝ ⟦ ⌜ u ⌝ ⟧₀
                → R⋆ α a ⌜ t ⌝
                → R⋆ α a ⌜ u ⌝
R⋆-preserves-⟦⟧ {α} {ι} a t u e r =
 a                      ＝⟨ r ⟩
 dialogue⋆ ⟦ ⌜ t ⌝ ⟧₀ α ＝⟨ ap (λ k → dialogue⋆ k α) e ⟩
 dialogue⋆ ⟦ ⌜ u ⌝ ⟧₀ α ∎
R⋆-preserves-⟦⟧ {α} {σ ⇒ σ₁} a t u e r x x' rx =
 R⋆-preserves-⟦⟧ {α} {σ₁} (a x) (t · x') (u · x') (ap (λ x → x ⟦ ⌜ x' ⌝ ⟧₀) e) (r x x' rx)

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

⌜main-lemma⌝ : {Γ : Cxt} {σ : type} (t : T Γ σ)
               (α : Baire)
               (xs : 【 Γ 】) (ys : Sub₀ Γ) --IB【 Γ 】 ((ι ⇒ ι) ⇒ ι))
             → R⋆s α xs (⌜Sub⌝ ys)
             → R⋆ α (⟦ t ⟧ xs) (close ⌜ t ⌝ (⌜Sub⌝ ys))
⌜main-lemma⌝ {Γ} {_} Zero α xs ys rxys = refl
⌜main-lemma⌝ {Γ} {_} (Succ t) α xs ys rxys =
 succ (⟦ t ⟧ xs)
  ＝⟨ ap succ (⌜main-lemma⌝ t α xs ys rxys) ⟩
 succ (dialogue⋆ ⟦ close ⌜ t ⌝ (⌜Sub⌝ ys) ⟧₀ α)
  ＝⟨ succ-dialogue⋆ (close ⌜ t ⌝ (⌜Sub⌝ ys)) α ⟩
 dialogue⋆ (succ⋆ ⟦ close ⌜ t ⌝ (⌜Sub⌝ ys) ⟧₀) α
  ＝⟨ refl ⟩
 dialogue⋆ ⟦ close ⌜succ⌝ ys · (close ⌜ t ⌝ (⌜Sub⌝ ys)) ⟧₀ α
  ∎
⌜main-lemma⌝ {Γ} {_} (Rec f g t) α xs ys rxys = {!!}
⌜main-lemma⌝ {Γ} {σ} (ν i) α xs ys rxys = rxys i
⌜main-lemma⌝ {Γ} {σ ⇒ τ} (ƛ t) α xs ys rxys x y rxy =
 transport
  (λ k → R⋆ α (⟦ t ⟧ (xs ‚ x)) k)
  e₁
  (R⋆-preserves-⟦⟧
    (⟦ t ⟧ (xs ‚ x))
    (close t (Sub,, ys y))
    (ƛ (close t (Subƛ ys)) · y)
    e₃
    (transport (λ k → R⋆ α (⟦ t ⟧ (xs ‚ x)) k) (⌜close⌝ t (Sub,, ys y)) ind))
 where
  e₃ : ⟦ ⌜ close t (Sub,, ys y) ⌝ ⟧₀ ＝ ⟦ ƛ ⌜ close t (Subƛ ys) ⌝ · ⌜ y ⌝ ⟧₀
  e₃ =
   ⟦ ⌜ close t (Sub,, ys y) ⌝ ⟧₀
    ＝⟨ {!!} ⟩
   {!!}
    ＝⟨ {!!} ⟩
   ⟦ ⌜ close t (Subƛ ys) ⌝ ⟧ (⟨⟩ ‚ ⟦ ⌜ y ⌝ ⟧₀)
    ∎

  e₂ : ⌜ close t (Subƛ ys) ⌝ ＝ close ⌜ t ⌝ (Subƛ (⌜Sub⌝ ys))
  e₂ =
   ⌜ close t (Subƛ ys) ⌝
    ＝⟨ (⌜close⌝ t (Subƛ ys)) ⁻¹ ⟩
   close ⌜ t ⌝ (⌜Sub⌝ (Subƛ ys))
    ＝⟨ (close-eta (Subƛ (⌜Sub⌝ ys)) (⌜Sub⌝ (Subƛ ys)) ⌜ t ⌝ (Subƛ⌜Sub⌝ ys)) ⁻¹ ⟩
   close ⌜ t ⌝ (Subƛ (⌜Sub⌝ ys))
    ∎
  e₁ : ⌜ (ƛ (close t (Subƛ ys))) · y ⌝ ＝ ƛ (close ⌜ t ⌝ (Subƛ (⌜Sub⌝ ys))) · ⌜ y ⌝
  e₁ = ap₂ _·_ (ap ƛ e₂) refl

  ind : R⋆ α (⟦ t ⟧ (xs ‚ x)) (close ⌜ t ⌝ (⌜Sub⌝ (Sub,, ys y)))
  ind = ⌜main-lemma⌝ {Γ ,, σ} {τ} t α (xs ‚ x) (Sub,, ys y) (R⋆s-⌜Sub,,⌝ xs x ys y rxys rxy)
⌜main-lemma⌝ {Γ} {σ} (t · t₁) α xs ys rxys =
 transport
  (λ k → R⋆ α (⟦ t ⟧ xs (⟦ t₁ ⟧ xs)) (close ⌜ t ⌝ (⌜Sub⌝ ys) · k))
  ((⌜close⌝ t₁ ys) ⁻¹)
  (⌜main-lemma⌝
    t α xs ys rxys (⟦ t₁ ⟧ xs) _
    (transport
      (λ k → R⋆ α (⟦ t₁ ⟧ xs) k)
      (⌜close⌝ t₁ ys)
      (⌜main-lemma⌝ t₁ α xs ys rxys)))

\end{code}
