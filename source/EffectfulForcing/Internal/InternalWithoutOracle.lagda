Martin Escardo, Vincent Rahli, Bruno da Rocha Paiva, Ayberk Tosun 20 May 2023

This is an adaptation of Internal.lagda written by Martin, which defines dialogue-tree⋆ without using T'
but directly using T.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.Internal.InternalWithoutOracle where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import MLTT.Athenian using (Fin)
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Continuity
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.SystemT using (type ; ι ; _⇒_ ; 〖_〗)
open import EffectfulForcing.MFPSAndVariations.Church hiding (B⋆【_】 ; ⟪⟫⋆ ; _‚‚⋆_ ; B⋆⟦_⟧ ; dialogue-tree⋆)
open import EffectfulForcing.Internal.Internal hiding (B⋆⟦_⟧ ; dialogue-tree⋆)
open import EffectfulForcing.Internal.LambdaWithoutOracle
open import EffectfulForcing.Internal.SystemT
open import UF.Base using (transport₂ ; transport₃ ; ap₂ ; ap₃)
open import UF.FunExt using (naive-funext)
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

{-
⌜main-lemma⌝₁ : {Γ : Cxt}
                {σ : type}
                (t : T Γ σ)
                (α : Baire)
                (xs : 【 Γ 】)
--               (ys : IB【 Γ 】 ((ι ⇒ ι) ⇒ ι))
--             → R⋆s α xs ys
              → R⋆₁ α (⟦ t ⟧ xs) (ƛ (ƛ (ƛ Zero))) --(close ⌜ t ⌝ ys)
⌜main-lemma⌝₁ {Γ} {σ} t α xs {--ys rxys--} = {!!}
-}

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

Sub1 : {Γ : Cxt} {τ : type} → T Γ τ → Sub (Γ ,, τ) Γ
Sub1 {Γ} {τ} t {.τ} (∈Cxt0 .Γ) = t
Sub1 {Γ} {τ} t {σ} (∈CxtS .τ i) = ν i

＝Subƛ : {Γ₁ Γ₂ : Cxt} (s1 s2 : Sub Γ₁ Γ₂) (σ : type)
        → ＝Sub s1 s2
        → ＝Sub (Subƛ {Γ₁} {Γ₂} {σ} s1) (Subƛ s2)
＝Subƛ {Γ₁} {Γ₂} s1 s2 σ e {.σ} (∈Cxt0 .Γ₁) = refl
＝Subƛ {Γ₁} {Γ₂} s1 s2 σ e {τ} (∈CxtS .σ i) = ap (weaken, σ) (e i)


Sub〈〉 : Sub 〈〉 〈〉
Sub〈〉 ()

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

{-
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
-}

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

IB₀ : {A : type} → IB【 〈〉 】 A
IB₀ {A} ()

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

【Sub】 : {Γ Δ : Cxt} (s : Sub Γ Δ) → 【 Δ 】 → 【 Γ 】
【Sub】 {Γ} {Δ} s c {τ} i = ⟦ s i ⟧ c

【Sub₀】 : {Γ : Cxt} (s : Sub₀ Γ) → 【 Γ 】
【Sub₀】 {Γ} s = 【Sub】 s ⟨⟩

{-
Sub₀1 : {σ : type} (t : T₀ σ) → Sub₀ (〈〉 ,, σ)
Sub₀1 {σ} t = Sub1 t
-}

{-
close-⌜zero⌝ : {σ : type} {Γ : Cxt} (ys : IB【 Γ 】 σ)
            → close (⌜zero⌝ {σ}) ys ＝ ⌜zero⌝
close-⌜zero⌝ {σ} {Γ} ys = refl

close-⌜succ⌝ : {σ : type} {Γ : Cxt} (ys : IB【 Γ 】 σ)
            → close (⌜succ⌝ {σ}) ys ＝ ⌜succ⌝
close-⌜succ⌝ {σ} {Γ} ys = refl
-}

-- testing...
{-
succ-dialogue⋆-aux' : {A : Type} {σ τ : type} (d : T₀ (⌜B⌝ σ ((τ ⇒ τ) ⇒ σ))) (α : 〖 τ 〗 → 〖 τ 〗) (f : 〖 σ 〗 → 〖 σ 〗)
                     (a : 〖 σ 〗 → (〖 τ 〗 → 〖 τ 〗) → 〖 σ 〗)
                     (b : (ℕ → (〖 τ 〗 → 〖 τ 〗) → 〖 σ 〗) → ℕ → (〖 τ 〗 → 〖 τ 〗) → 〖 σ 〗)
                   → f (⟦ d ⟧₀ a b α)
                     ＝ ⟦ d ⟧₀ (λ x → a (f x)) b α
succ-dialogue⋆-aux' {A} {σ} {τ} d α f a b = {!!}
-}

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

{-
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
-}

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
 weaken (⊆-B-context (∈CxtS σ)) ⌜ s j₂ ⌝
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

-- Since the equality is only used in the ι case, could we relax that hypothesis for function types?
-- Some of the funext we use are related to this, as we end up having to prove this for higher types.
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

＝【】 : {Γ : Cxt} (a b : 【 Γ 】) → Type
＝【】 {Γ} a b = {σ : type} (i : ∈Cxt σ Γ) → a i ＝ b i

{-
Reta : {Γ : Cxt} {σ : type} (t : T Γ σ) → Type
Reta {Γ} {ι} t = (a b : 【 Γ 】)
               → ＝【】 a b
               → ⟦ t ⟧ a ＝ ⟦ t ⟧ b
Reta {Γ} {σ ⇒ τ} t = (x : T Γ σ) → Reta x → Reta (t · x)

⟦⟧-eta' : {Γ : Cxt} {σ : type} (t : T Γ σ)
         → Reta t
⟦⟧-eta' {Γ} {.ι} Zero = {!!}
⟦⟧-eta' {Γ} {.ι} (Succ t) = {!!}
⟦⟧-eta' {Γ} {σ} (Rec t t₁ t₂) = {!!}
⟦⟧-eta' {Γ} {σ} (ν i) = {!!}
⟦⟧-eta' {Γ} {.(_ ⇒ _)} (ƛ t) = {!!}
⟦⟧-eta' {Γ} {σ} (t · t₁) = {!!}
-}

＝【】‚ : {Γ : Cxt} {σ : type} (a b : 【 Γ 】) (x : 〖 σ 〗)
        → ＝【】 a b
        → ＝【】 (a ‚ x) (b ‚ x)
＝【】‚ {Γ} {σ} a b x e {.σ} (∈Cxt0 .Γ) = refl
＝【】‚ {Γ} {σ} a b x e {τ} (∈CxtS .σ i) = e i

⟦⟧-eta : {Γ : Cxt} {σ : type} (t : T Γ σ) (a b : 【 Γ 】)
       → ＝【】 a b
       → ⟦ t ⟧ a ＝ ⟦ t ⟧ b
⟦⟧-eta {Γ} {_} Zero a b e = refl
⟦⟧-eta {Γ} {_} (Succ t) a b e = ap succ (⟦⟧-eta t a b e)
⟦⟧-eta {Γ} {σ} (Rec t t₁ t₂) a b e = ap₃ rec (⟦⟧-eta t a b e) (⟦⟧-eta t₁ a b e) (⟦⟧-eta t₂ a b e)
⟦⟧-eta {Γ} {σ} (ν i) a b e = e i
⟦⟧-eta {Γ} {σ ⇒ τ} (ƛ t) a b e = c {!!} -- can we get this without funext?
 where
  c : (ext : naive-funext 𝓤₀ 𝓤₀) → (λ x → ⟦ t ⟧ (a ‚ x)) ＝ (λ x → ⟦ t ⟧ (b ‚ x))
  c ext = ext (λ x → ⟦⟧-eta t (a ‚ x) (b ‚ x) (＝【】‚ a b x e))
⟦⟧-eta {Γ} {σ} (t · t₁) a b e = ap₂ (λ f g → f g) (⟦⟧-eta t a b e) (⟦⟧-eta t₁ a b e)

⊆【】 : {Γ Δ : Cxt} (s : Γ ⊆ Δ) → 【 Δ 】 → 【 Γ 】
⊆【】 {Γ} {Δ} s c {τ} i = c (s i)

【】,,₁ : {Γ : Cxt} {σ : type} → 【 Γ ,, σ 】 → 【 Γ 】
【】,,₁ {Γ} {σ} h {τ} i = h (∈CxtS σ i)

【】,,₂ : {Γ : Cxt} {σ : type} → 【 Γ ,, σ 】 → 〖 σ 〗
【】,,₂ {Γ} {σ} h = h (∈Cxt0 Γ)

＝【】-⊆【】-⊆,, : {Γ Δ : Cxt} {σ : type} (s : Γ ⊆ Δ) (y : 【 Δ ,, σ 】)
                 → ＝【】 (⊆【】 (⊆,, σ s) y) (⊆【】 s (【】,,₁ y) ‚ 【】,,₂ y)
＝【】-⊆【】-⊆,, {Γ} {Δ} {σ} s y {.σ} (∈Cxt0 .Γ) = refl
＝【】-⊆【】-⊆,, {Γ} {Δ} {σ} s y {τ} (∈CxtS .σ i) = refl

-- can we prove this without funext?
⟦weaken⟧-aux : (ext : naive-funext 𝓤₀ 𝓤₀) {Γ Δ : Cxt} {σ τ : type} (t : T (Γ ,, σ) τ) (s : Γ ⊆ Δ)
              → (λ (y : 【 Δ ,, σ 】) → ⟦ t ⟧ (⊆【】 (⊆,, σ s) y))
                ＝ (λ y → ⟦ t ⟧ (⊆【】 s (【】,,₁ y) ‚ 【】,,₂ y))
⟦weaken⟧-aux ext {Γ} {Δ} {σ} {τ} t s = ext e
 where
  e : (λ (y : 【 Δ ,, σ 】) → ⟦ t ⟧ (⊆【】 (⊆,, σ s) y)) ∼ (λ y → ⟦ t ⟧ (⊆【】 s (【】,,₁ y) ‚ 【】,,₂ y))
  e y = ⟦⟧-eta t (⊆【】 (⊆,, σ s) y) (⊆【】 s (【】,,₁ y) ‚ 【】,,₂ y) (＝【】-⊆【】-⊆,, s y)

⟦weaken⟧ : {Γ Δ : Cxt} {σ : type} (t : T Γ σ) (s : Γ ⊆ Δ)
           → ⟦ weaken s t ⟧ ＝ λ y → ⟦ t ⟧ (⊆【】 s y)
⟦weaken⟧ {Γ} {Δ} {_} Zero s = refl
⟦weaken⟧ {Γ} {Δ} {_} (Succ t) s = ap (λ f xs → succ (f xs)) (⟦weaken⟧ t s)
⟦weaken⟧ {Γ} {Δ} {σ} (Rec t t₁ t₂) s =
 ap₃ (λ f g h xs → rec (f xs) (g xs) (h xs)) (⟦weaken⟧ t s) (⟦weaken⟧ t₁ s) (⟦weaken⟧ t₂ s)
⟦weaken⟧ {Γ} {Δ} {σ} (ν i) s = refl
⟦weaken⟧ {Γ} {Δ} {σ ⇒ τ} (ƛ t) s =
 ap {_} {_} {【 Δ ,, σ 】 → 〖 τ 〗} {【 Δ 】 → 〖 σ 〗 → 〖 τ 〗}
   (λ f xs x → f (xs ‚ x)) {⟦ weaken (⊆,, σ s) t ⟧}
   {λ y → ⟦ t ⟧ (⊆【】 s (【】,,₁ y) ‚ 【】,,₂ y)}
   (⟦weaken⟧ t (⊆,, σ s)  ∙ ⟦weaken⟧-aux {!!} t s) -- can we prove this without funext?
⟦weaken⟧ {Γ} {Δ} {σ} (t · t₁) s = ap₂ (λ f g xs → f xs (g xs)) (⟦weaken⟧ t s) (⟦weaken⟧ t₁ s)

⟦weaken,⟧ : {Γ : Cxt} {σ : type} (t : T Γ σ) (τ : type)
           → ⟦ weaken, τ t ⟧ ＝ λ y → ⟦ t ⟧ (⊆【】 (⊆, Γ τ) y)
⟦weaken,⟧ {Γ} {σ} t τ = ⟦weaken⟧ t (⊆, Γ τ)

＝【】-⊆【】-⊆〈〉 : {Γ : Cxt} (s : 【 Γ 】)
                 → ＝【】 (⊆【】 (⊆〈〉 Γ) s) ⟨⟩
＝【】-⊆【】-⊆〈〉 {Γ} s {σ} ()

⟦weaken₀⟧ : {Γ : Cxt} {σ : type} (t : T₀ σ) (s : 【 Γ 】)
          → ⟦ weaken₀ t ⟧ s ＝ ⟦ t ⟧₀
⟦weaken₀⟧ {Γ} {σ} t s =
 ⟦ weaken₀ t ⟧ s
  ＝⟨ ap (λ k → k s) (⟦weaken⟧ t (⊆〈〉 Γ)) ⟩
 ⟦ t ⟧ (⊆【】 (⊆〈〉 Γ) s)
  ＝⟨ ⟦⟧-eta t (⊆【】 (⊆〈〉 Γ) s) ⟨⟩ (＝【】-⊆【】-⊆〈〉 s) ⟩
 ⟦ t ⟧₀
  ∎

＝【】-【Sub】-Subƛ :  {Γ Δ : Cxt} {σ : type} (y : 【 Δ ,, σ 】) (s : Sub Γ Δ)
                    → ＝【】 (【Sub】 (Subƛ s) y) (【Sub】 s (【】,,₁ y) ‚ 【】,,₂ y)
＝【】-【Sub】-Subƛ {Γ} {Δ} {σ} y s {.σ} (∈Cxt0 .Γ) = refl
＝【】-【Sub】-Subƛ {Γ} {Δ} {σ} y s {τ} (∈CxtS .σ i) = ap (λ k → k y) (⟦weaken,⟧ (s i) σ)

-- can we prove this without funext?
⟦close⟧-aux : (ext : naive-funext 𝓤₀ 𝓤₀) {Γ Δ : Cxt} {σ τ : type} (t : T (Γ ,, σ) τ) (s : Sub Γ Δ)
              → (λ (y : 【 Δ ,, σ 】) → ⟦ t ⟧ (【Sub】 (Subƛ s) y))
                ＝ (λ y → ⟦ t ⟧ (【Sub】 s (【】,,₁ y) ‚ 【】,,₂ y))
⟦close⟧-aux ext {Γ} {Δ} {σ} {τ} t s = ext e
 where
  e : (λ (y : 【 Δ ,, σ 】) → ⟦ t ⟧ (【Sub】 (Subƛ s) y)) ∼ (λ y → ⟦ t ⟧ (【Sub】 s (【】,,₁ y) ‚ 【】,,₂ y))
  e y = ⟦⟧-eta t (【Sub】 (Subƛ s) y) (【Sub】 s (【】,,₁ y) ‚ 【】,,₂ y) (＝【】-【Sub】-Subƛ y s)

⟦close⟧ : {Γ Δ : Cxt} {σ : type} (t : T Γ σ) (s : Sub Γ Δ)
           → ⟦ close t s ⟧ ＝ λ y → ⟦ t ⟧ (【Sub】 s y)
⟦close⟧ {Γ} {Δ} Zero s = refl
⟦close⟧ {Γ} {Δ} (Succ t) s = ap (λ f xs → succ (f xs)) (⟦close⟧ t s)
⟦close⟧ {Γ} {Δ} (Rec t t₁ t₂) s =
 ap₃ (λ f g h xs → rec (f xs) (g xs) (h xs)) (⟦close⟧ t s) (⟦close⟧ t₁ s) (⟦close⟧ t₂ s)
⟦close⟧ {Γ} {Δ} (ν i) s = refl
⟦close⟧ {Γ} {Δ} {σ ⇒ τ} (ƛ t) s =
 ap {_} {_} {【 Δ ,, σ 】 → 〖 τ 〗} {【 Δ 】 → 〖 σ 〗 → 〖 τ 〗} (λ f xs x → f (xs ‚ x))
    {⟦ close t (Subƛ s) ⟧}
    {λ y → ⟦ t ⟧ (【Sub】 s (【】,,₁  y) ‚ 【】,,₂ y)}
    (⟦close⟧ t (Subƛ s) ∙ ⟦close⟧-aux {!!} t s) -- can we prove this without funext?
⟦close⟧ {Γ} {Δ} (t · t₁) s = ap₂ (λ f g xs → f xs (g xs)) (⟦close⟧ t s) (⟦close⟧ t₁ s)

⟦close⟧' : {Γ : Cxt} {σ : type} (t : T Γ σ) (s : Sub₀ Γ)
           → ⟦ close t s ⟧₀ ＝ ⟦ t ⟧ (【Sub₀】 s)
⟦close⟧' {Γ} {σ} t s = ap (λ k → k ⟨⟩) (⟦close⟧ t s)

{-
⟦close⟧'' : {Γ Δ : Cxt} {σ : type} (t : T Γ σ) (s : Sub Γ Δ) (y : 【 Δ 】)
           → ⟦ close t s ⟧ y ＝ ⟦ t ⟧ (【Sub】 s y)
⟦close⟧'' {Γ} {Δ} Zero s y = refl
⟦close⟧'' {Γ} {Δ} (Succ t) s y = ap succ (⟦close⟧'' t s y)
⟦close⟧'' {Γ} {Δ} (Rec t t₁ t₂) s y = ap₃ rec (⟦close⟧'' t s y) (⟦close⟧'' t₁ s y) (⟦close⟧'' t₂ s y)
⟦close⟧'' {Γ} {Δ} (ν i) s y = refl
⟦close⟧'' {Γ} {Δ} (ƛ t) s y = {!!}
⟦close⟧'' {Γ} {Δ} (t · t₁) s y = {!!}
-}

{-
Rsub : {Γ : Cxt} {σ : type} (t : T Γ σ) (s : Sub₀ Γ) → Type
Rsub {Γ} {ι} t s = ⟦ close t s ⟧₀ ＝ ⟦ t ⟧ (【sub】 s)
Rsub {Γ} {σ ⇒ τ} t s = (x : T Γ σ)
                     → Rsub x s
                     → Rsub (t · x) s

⟦close⟧ : {Γ : Cxt} {σ : type} (t : T Γ σ) (s : Sub₀ Γ)
          → Rsub t s
⟦close⟧ {Γ} {_} Zero s = refl
⟦close⟧ {Γ} {_} (Succ t) s = ap succ (⟦close⟧ t s)
⟦close⟧ {Γ} {σ} (Rec t t₁ t₂) s = {!!}
⟦close⟧ {Γ} {σ} (ν i) s = {!!}
⟦close⟧ {Γ} {σ ⇒ τ} (ƛ t) s x rx = {!!}
⟦close⟧ {Γ} {σ} (t · t₁) s = ⟦close⟧ t s t₁ (⟦close⟧ t₁ s)
-}

{-
⟦close⟧ : {Γ : Cxt} {σ : type} (t : T Γ σ) (s : Sub₀ Γ)
          → ⟦ close t s ⟧₀ ＝ ⟦ t ⟧ (【sub】 s)
⟦close⟧ {Γ} {_}     Zero          s = refl
⟦close⟧ {Γ} {_}     (Succ t)      s = ap succ (⟦close⟧ t s)
⟦close⟧ {Γ} {σ}     (Rec t t₁ t₂) s = ap₃ rec (⟦close⟧ t s) (⟦close⟧ t₁ s) (⟦close⟧ t₂ s)
⟦close⟧ {Γ} {σ}     (ν i)         s = refl
⟦close⟧ {Γ} {σ ⇒ τ} (ƛ t)         s = {!ap (λ f x → f x) {}!}
⟦close⟧ {Γ} {σ}     (t · u)       s =
 ⟦ close t s · close u s ⟧₀
  ＝⟨ ap (λ k → k ⟦ close u s ⟧₀) (⟦close⟧ t s) ⟩
 ⟦ t ⟧ (【sub】 s) ⟦ close u s ⟧₀
  ＝⟨ ap (⟦ t ⟧ (【sub】 s)) (⟦close⟧ u s) ⟩
 ⟦ t ⟧ (【sub】 s) (⟦ u ⟧ (【sub】 s))
  ∎
-}

＝【】-【sub】-⌜Sub⌝-Sub1 : {A : type} {σ : type} (y : T₀ σ)
                          → ＝【】 (【Sub₀】 (⌜Sub⌝ {A} (Sub1 y))) (⟨⟩ ‚ ⟦ ⌜ y ⌝ ⟧₀)
＝【】-【sub】-⌜Sub⌝-Sub1 {A} {σ} y {τ} i with ∈Cxt-B-context'' i
... | τ₁ , refl , ∈Cxt0 .〈〉 , refl = refl

Sub-trans : {Γ₁ Γ₂ Γ₃ : Cxt} (s₁ : Sub Γ₁ Γ₂) (s₂ : Sub Γ₂ Γ₃) → Sub Γ₁ Γ₃
Sub-trans {Γ₁} {Γ₂} {Γ₃} s₁ s₂ {τ} i = close (s₁ i) s₂

⊆Sub : {Γ₁ Γ₂ Γ₃ : Cxt} (s1 : Γ₁ ⊆ Γ₂) (s2 : Sub Γ₂ Γ₃) → Sub Γ₁ Γ₃
⊆Sub {Γ₁} {Γ₂} {Γ₃} s1 s2 {σ} i = s2 (s1 i)

Sub⊆ : {Γ₁ Γ₂ Γ₃ : Cxt} (s1 : Sub Γ₁ Γ₂) (s2 : Γ₂ ⊆ Γ₃) → Sub Γ₁ Γ₃
Sub⊆ {Γ₁} {Γ₂} {Γ₃} s1 s2 {σ} i = weaken s2 (s1 i)

＝Sub-⊆Sub-⊆,, : {σ : type} {Γ₁ Γ₂ Γ₃ : Cxt} (s1 : Γ₁ ⊆ Γ₂) (s2 : Sub Γ₂ Γ₃)
                → ＝Sub (⊆Sub (⊆,, σ s1) (Subƛ s2)) (Subƛ (⊆Sub s1 s2))
＝Sub-⊆Sub-⊆,, {σ} {Γ₁} {Γ₂} {Γ₃} s1 s2 {.σ} (∈Cxt0 .Γ₁) = refl
＝Sub-⊆Sub-⊆,, {σ} {Γ₁} {Γ₂} {Γ₃} s1 s2 {τ} (∈CxtS .σ i) = refl

close-weaken : {σ : type} {Γ₁ Γ₂ Γ₃ : Cxt} (t : T Γ₁ σ) (s1 : Γ₁ ⊆ Γ₂) (s2 : Sub Γ₂ Γ₃)
              → close (weaken s1 t) s2 ＝ close t (⊆Sub s1 s2)
close-weaken {_} {Γ₁} {Γ₂} {Γ₃} Zero s1 s2 = refl
close-weaken {_} {Γ₁} {Γ₂} {Γ₃} (Succ t) s1 s2 = ap Succ (close-weaken t s1 s2)
close-weaken {σ} {Γ₁} {Γ₂} {Γ₃} (Rec t t₁ t₂) s1 s2 =
 ap₃ Rec (close-weaken t s1 s2) (close-weaken t₁ s1 s2) (close-weaken t₂ s1 s2)
close-weaken {σ} {Γ₁} {Γ₂} {Γ₃} (ν i) s1 s2 = refl
close-weaken {σ ⇒ τ} {Γ₁} {Γ₂} {Γ₃} (ƛ t) s1 s2 =
 ap ƛ (close-weaken t (⊆,, σ s1) (Subƛ s2)
       ∙ close-eta (⊆Sub (⊆,, σ s1) (Subƛ s2)) (Subƛ (⊆Sub s1 s2)) t (＝Sub-⊆Sub-⊆,, s1 s2))
close-weaken {σ} {Γ₁} {Γ₂} {Γ₃} (t · t₁) s1 s2 = ap₂ _·_ (close-weaken t s1 s2) (close-weaken t₁ s1 s2)

＝⊆-⊆-trans-⊆,, : {σ : type} {Γ₁ Γ₂ Γ₃ : Cxt} (s1 : Γ₁ ⊆ Γ₂) (s2 : Γ₂ ⊆ Γ₃)
                → ＝⊆ (⊆-trans (⊆,, σ s1) (⊆,, σ s2)) (⊆,, σ (⊆-trans s1 s2))
＝⊆-⊆-trans-⊆,, {σ} {Γ₁} {Γ₂} {Γ₃} s1 s2 {.σ} (∈Cxt0 .Γ₁) = refl
＝⊆-⊆-trans-⊆,, {σ} {Γ₁} {Γ₂} {Γ₃} s1 s2 {τ} (∈CxtS .σ i) = refl

weaken-weaken : {σ : type} {Γ₁ Γ₂ Γ₃ : Cxt} (t : T Γ₁ σ) (s1 : Γ₁ ⊆ Γ₂) (s2 : Γ₂ ⊆ Γ₃)
              → weaken s2 (weaken s1 t) ＝ weaken (⊆-trans s1 s2) t
weaken-weaken {_} {Γ₁} {Γ₂} {Γ₃} Zero s1 s2 = refl
weaken-weaken {_} {Γ₁} {Γ₂} {Γ₃} (Succ t) s1 s2 = ap Succ (weaken-weaken t s1 s2)
weaken-weaken {σ} {Γ₁} {Γ₂} {Γ₃} (Rec t t₁ t₂) s1 s2 =
 ap₃ Rec (weaken-weaken t s1 s2) (weaken-weaken t₁ s1 s2) (weaken-weaken t₂ s1 s2)
weaken-weaken {σ} {Γ₁} {Γ₂} {Γ₃} (ν i) s1 s2 = refl
weaken-weaken {σ ⇒ τ} {Γ₁} {Γ₂} {Γ₃} (ƛ t) s1 s2 =
 ap ƛ (weaken-weaken t (⊆,, σ s1) (⊆,, σ s2)
       ∙ weaken-eta (⊆-trans (⊆,, σ s1) (⊆,, σ s2)) (⊆,, σ (⊆-trans s1 s2)) t (＝⊆-⊆-trans-⊆,, s1 s2))
weaken-weaken {σ} {Γ₁} {Γ₂} {Γ₃} (t · t₁) s1 s2 =
 ap₂ _·_ (weaken-weaken t s1 s2) (weaken-weaken t₁ s1 s2)

＝⊆-⊆-trans-S-⊆,, : {σ : type} {Γ₁ Γ₂ Γ₃ : Cxt} (s1 : Sub Γ₁ Γ₂) (s2 : Γ₂ ⊆ Γ₃)
                  → ＝⊆ (⊆-trans (∈CxtS σ) (⊆,, σ s2)) (⊆-trans s2 (∈CxtS σ))
＝⊆-⊆-trans-S-⊆,, {σ} {Γ₁} {.(Γ ,, τ)} {Γ₃} s1 s2 {τ} (∈Cxt0 Γ) = refl
＝⊆-⊆-trans-S-⊆,, {σ} {Γ₁} {.(_ ,, τ₁)} {Γ₃} s1 s2 {τ} (∈CxtS τ₁ i) = refl

＝Sub-Sub⊆-Subƛ : {σ : type} {Γ₁ Γ₂ Γ₃ : Cxt} (s1 : Sub Γ₁ Γ₂) (s2 : Γ₂ ⊆ Γ₃)
                → ＝Sub (Sub⊆ (Subƛ s1) (⊆,, σ s2)) (Subƛ (Sub⊆ s1 s2))
＝Sub-Sub⊆-Subƛ {σ} {Γ₁} {Γ₂} {Γ₃} s1 s2 {.σ} (∈Cxt0 .Γ₁) = refl
＝Sub-Sub⊆-Subƛ {σ} {Γ₁} {Γ₂} {Γ₃} s1 s2 {τ} (∈CxtS .σ i) = c
 where
  c : weaken (⊆,, σ s2) (weaken, σ (s1 i)) ＝ weaken, σ (weaken s2 (s1 i))
  c = weaken-weaken (s1 i) (⊆, Γ₂ σ) (⊆,, σ s2)
      ∙ weaken-eta (⊆-trans (∈CxtS σ) (⊆,, σ s2)) (⊆-trans s2 (∈CxtS σ)) (s1 i) (＝⊆-⊆-trans-S-⊆,, s1 s2)
      ∙ weaken-weaken (s1 i) s2 (⊆, Γ₃ σ) ⁻¹

weaken-close : {σ : type} {Γ₁ Γ₂ Γ₃ : Cxt} (t : T Γ₁ σ) (s1 : Sub Γ₁ Γ₂) (s2 : Γ₂ ⊆ Γ₃)
              → weaken s2 (close t s1) ＝ close t (Sub⊆ s1 s2)
weaken-close {.ι} {Γ₁} {Γ₂} {Γ₃} Zero s1 s2 = refl
weaken-close {.ι} {Γ₁} {Γ₂} {Γ₃} (Succ t) s1 s2 = ap Succ (weaken-close t s1 s2)
weaken-close {σ} {Γ₁} {Γ₂} {Γ₃} (Rec t t₁ t₂) s1 s2 =
 ap₃ Rec (weaken-close t s1 s2) (weaken-close t₁ s1 s2) (weaken-close t₂ s1 s2)
weaken-close {σ} {Γ₁} {Γ₂} {Γ₃} (ν i) s1 s2 = refl
weaken-close {σ ⇒ τ} {Γ₁} {Γ₂} {Γ₃} (ƛ t) s1 s2 =
 ap ƛ (weaken-close t (Subƛ s1) (⊆,, σ s2)
       ∙ close-eta (Sub⊆ (Subƛ s1) (⊆,, σ s2)) (Subƛ (Sub⊆ s1 s2)) t (＝Sub-Sub⊆-Subƛ s1 s2))
weaken-close {σ} {Γ₁} {Γ₂} {Γ₃} (t · t₁) s1 s2 = ap₂ _·_ (weaken-close t s1 s2) (weaken-close t₁ s1 s2)

＝Sub-∘Sub-Subƛ : {Γ₁ Γ₂ Γ₃ : Cxt} {τ : type} (s1 : Sub Γ₁ Γ₂) (s2 : Sub Γ₂ Γ₃)
               → ＝Sub (Sub-trans (Subƛ {_} {_} {τ} s1) (Subƛ s2)) (Subƛ (Sub-trans s1 s2))
＝Sub-∘Sub-Subƛ {Γ₁} {Γ₂} {Γ₃} {τ} s1 s2 {.τ} (∈Cxt0 .Γ₁) = refl
＝Sub-∘Sub-Subƛ {Γ₁} {Γ₂} {Γ₃} {τ} s1 s2 {σ} (∈CxtS .τ i) =
 close (weaken, τ (s1 i)) (Subƛ s2)
  ＝⟨ close-weaken (s1 i) (⊆, Γ₂ τ) (Subƛ s2) ⟩
 close (s1 i) (⊆Sub (∈CxtS τ) (Subƛ s2))
  ＝⟨ refl ⟩
 close (s1 i) (Sub⊆ s2 (∈CxtS τ))
  ＝⟨ (weaken-close (s1 i) s2 (⊆, Γ₃ τ)) ⁻¹ ⟩
 weaken, τ (close (s1 i) s2)
  ∎

close-close : {Γ₁ Γ₂ Γ₃ : Cxt} {σ : type} (t : T Γ₁ σ) (s1 : Sub Γ₁ Γ₂) (s2 : Sub Γ₂ Γ₃)
            → close (close t s1) s2 ＝ close t (Sub-trans s1 s2)
close-close {Γ₁} {Γ₂} {Γ₃} {.ι} Zero s1 s2 = refl
close-close {Γ₁} {Γ₂} {Γ₃} {.ι} (Succ t) s1 s2 = ap Succ (close-close t s1 s2)
close-close {Γ₁} {Γ₂} {Γ₃} {σ} (Rec t t₁ t₂) s1 s2 = ap₃ Rec (close-close t s1 s2) (close-close t₁ s1 s2) (close-close t₂ s1 s2)
close-close {Γ₁} {Γ₂} {Γ₃} {σ} (ν i) s1 s2 = refl
close-close {Γ₁} {Γ₂} {Γ₃} {.(_ ⇒ _)} (ƛ t) s1 s2 =
 ap ƛ (close-close t (Subƛ s1) (Subƛ s2)
       ∙ close-eta (Sub-trans (Subƛ s1) (Subƛ s2)) (Subƛ (Sub-trans s1 s2)) t (＝Sub-∘Sub-Subƛ s1 s2))
close-close {Γ₁} {Γ₂} {Γ₃} {σ} (t · t₁) s1 s2 = ap₂ _·_ (close-close t s1 s2) (close-close t₁ s1 s2)

＝Subν : {Γ : Cxt} {τ : type} (y : T Γ τ)
       → ＝Sub (⊆Sub (∈CxtS τ) (Sub1 y)) ν
＝Subν {Γ} {τ} y {x} i = refl

＝Sub-Subƛ-ν : {Γ : Cxt} {σ : type}
             → ＝Sub (Subƛ {Γ} {Γ} {σ} ν) ν
＝Sub-Subƛ-ν {Γ} {σ} {.σ} (∈Cxt0 .Γ) = refl
＝Sub-Subƛ-ν {Γ} {σ} {x} (∈CxtS .σ i) = refl

close-refl : {Γ : Cxt} {σ : type} (t : T Γ σ)
           → close t ν ＝ t
close-refl {Γ} {.ι} Zero = refl
close-refl {Γ} {.ι} (Succ t) = ap Succ (close-refl t)
close-refl {Γ} {σ} (Rec t t₁ t₂) = ap₃ Rec (close-refl t) (close-refl t₁) (close-refl t₂)
close-refl {Γ} {σ} (ν i) = refl
close-refl {Γ} {.(_ ⇒ _)} (ƛ t) = ap ƛ (close-eta (Subƛ ν) ν t ＝Sub-Subƛ-ν ∙ close-refl t)
close-refl {Γ} {σ} (t · t₁) = ap₂ _·_ (close-refl t) (close-refl t₁)

＝Sub-Sub,, : {Γ : Cxt} {σ τ : type} (y : T₀ σ) (ys : Sub₀ Γ)
            → ＝Sub (Sub,, ys y) (Sub-trans (Subƛ ys) (Sub1 y))
＝Sub-Sub,, {Γ} {σ} {τ} y ys {.σ} (∈Cxt0 .Γ) = refl
＝Sub-Sub,, {Γ} {σ} {τ} y ys {x} (∈CxtS .σ i) =
 close-refl (ys i) ⁻¹
 ∙ close-eta (⊆Sub (∈CxtS σ) (Sub1 y)) ν (ys i) (＝Subν y) ⁻¹
 ∙ (close-weaken (ys i) (⊆, 〈〉 σ) (Sub1 y)) ⁻¹

close-Sub,,-as-close-Subƛ : {Γ : Cxt} {σ τ : type} (t : T (Γ ,, σ) τ) (ys : Sub₀ Γ) (y : T₀ σ)
                          → close t (Sub,, ys y) ＝ close (close t (Subƛ ys)) (Sub1 y)
close-Sub,,-as-close-Subƛ {Γ} {σ} {τ} t ys y =
 close t (Sub,, ys y)
  ＝⟨ close-eta (Sub,, ys y) (Sub-trans (Subƛ ys) (Sub1 y)) t (＝Sub-Sub,, {Γ} {σ} {τ} y ys) ⟩
 close t (Sub-trans (Subƛ ys) (Sub1 y))
  ＝⟨ close-close t (Subƛ ys) (Sub1 y) ⁻¹ ⟩
 close (close t (Subƛ ys)) (Sub1 y)
  ∎

⟦⌜Kleisli-extension⌝⟧ : (ext : naive-funext 𝓤₀ 𝓤₀) {X A σ : type} {Γ Δ : Cxt} (xs : 【 Γ 】) (ys : 【 Δ 】)
                      → ⟦ ⌜Kleisli-extension⌝ {X} {A} {σ} ⟧ xs
                     ＝ ⟦ ⌜Kleisli-extension⌝ {X} {A} {σ} ⟧ ys
⟦⌜Kleisli-extension⌝⟧ ext {X} {A} {ι} {Γ} {Δ} xs ys = refl
⟦⌜Kleisli-extension⌝⟧ ext {X} {A} {σ ⇒ τ} {Γ} {Δ} xs ys =
 ext (λ x → ext (λ y → ext λ z → ap (λ k → k (λ x₁ → x x₁ z) y) (⟦⌜Kleisli-extension⌝⟧ ext (xs ‚ x ‚ y ‚ z) (ys ‚ x ‚ y ‚ z))))

⟦⌜Rec⌝⟧-aux : (ext : naive-funext 𝓤₀ 𝓤₀) {A : type} {σ : type} {Γ : Cxt}
              (s : 【 B-context【 Γ 】 A 】) (a : T Γ (ι ⇒ σ ⇒ σ)) (b : T Γ σ)
            → rec (λ y → ⟦ ⌜_⌝ {_} {_} {A} a ⟧ s (η⋆ y)) (⟦ ⌜ b ⌝ ⟧ s)
           ＝ (λ x → rec (λ y → ⟦ weaken, ι (weaken, ι ⌜ a ⌝) ⟧ (s ‚ x ‚ y) (η⋆ y)) (⟦ weaken, ι ⌜ b ⌝ ⟧ (s ‚ x)) x)
⟦⌜Rec⌝⟧-aux ext {A} {σ} {Γ} s a b = ext h
 where
   h : rec (λ y → ⟦ ⌜ a ⌝ ⟧ s (η⋆ y)) (⟦ ⌜ b ⌝ ⟧ s)
       ∼ (λ x → rec (λ y → ⟦ weaken, ι (weaken, ι ⌜ a ⌝) ⟧ (s ‚ x ‚ y) (η⋆ y)) (⟦ weaken, ι ⌜ b ⌝ ⟧ (s ‚ x)) x)
   h x = ap₂ (λ p q → rec p (q (s ‚ x)) x)
             (ext (λ y → ap (λ k → k (s ‚ x) (η⋆ y)) (⟦weaken,⟧ ⌜ a ⌝ ι) ⁻¹
                       ∙ ap (λ k → k (s ‚ x ‚ y) (η⋆ y)) (⟦weaken,⟧ (weaken, ι ⌜ a ⌝) ι) ⁻¹))
             ((⟦weaken,⟧ ⌜ b ⌝ ι) ⁻¹)

{-
⟦⌜Rec⌝⟧' : {A : type} {σ : type} (a : T₀ (ι ⇒ σ ⇒ σ)) (b : T₀ σ) (c : T₀ ι)
        → ⟦ ⌜_⌝  {〈〉} {σ} {A} (Rec a b c) ⟧₀
       ＝ ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ} ⟧₀ (λ x → rec (λ y → ⟦ ⌜ a ⌝ ⟧₀ (η⋆ y)) ⟦ ⌜ b ⌝ ⟧₀ x) ⟦ ⌜ c ⌝ ⟧₀
⟦⌜Rec⌝⟧' {A} {σ} a b c =
 ⟦ ⌜_⌝  {〈〉} {σ} {A} (Rec a b c) ⟧₀
  ＝⟨ refl ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ} ⟧ (⟨⟩ ‚ ⟦ ⌜ a ⌝ ⟧₀ ‚ ⟦ ⌜ b ⌝ ⟧₀) (λ x → rec (λ y → ⟦ ⌜ a ⌝ ⟧₀ (η⋆ y)) ⟦ ⌜ b ⌝ ⟧₀ x) ⟦ ⌜ c ⌝ ⟧₀
  ＝⟨ ap (λ k → k (λ x → rec (λ y → ⟦ ⌜ a ⌝ ⟧₀ (η⋆ y)) ⟦ ⌜ b ⌝ ⟧₀ x) ⟦ ⌜ c ⌝ ⟧₀) (⟦⌜Kleisli-extension⌝⟧ {!!} (⟨⟩ ‚ ⟦ ⌜ a ⌝ ⟧₀ ‚ ⟦ ⌜ b ⌝ ⟧₀) ⟨⟩)  ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ} ⟧₀ (λ x → rec (λ y → ⟦ ⌜ a ⌝ ⟧₀ (η⋆ y)) ⟦ ⌜ b ⌝ ⟧₀ x) ⟦ ⌜ c ⌝ ⟧₀
  ∎
-}

⟦⌜Rec⌝⟧ : {A : type} {σ : type} {Γ : Cxt} (s : 【 B-context【 Γ 】 A 】) (a : T Γ (ι ⇒ σ ⇒ σ)) (b : T Γ σ) (c : T Γ ι)
        → ⟦ ⌜_⌝  {Γ} {σ} {A} (Rec a b c) ⟧ s
       ＝ ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
            · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀))
            · ⌜ c ⌝ ⟧ s
⟦⌜Rec⌝⟧ {A} {σ} {Γ} s a b c =
 ⟦ ⌜_⌝  {Γ} {σ} {A} (Rec a b c) ⟧ s
  ＝⟨ refl ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ} ⟧ (s ‚ ⟦ ⌜ a ⌝ ⟧ s ‚ ⟦ ⌜ b ⌝ ⟧ s)
  (λ x → rec (λ y → ⟦ ⌜ a ⌝ ⟧ s (η⋆ y)) (⟦ ⌜ b ⌝ ⟧ s) x)
  (⟦ ⌜ c ⌝ ⟧ s)
  -- can we prove those without funext?
  ＝⟨ ap₂ (λ p q → p q (⟦ ⌜ c ⌝ ⟧ s)) (⟦⌜Kleisli-extension⌝⟧ {!!} (s ‚ ⟦ ⌜ a ⌝ ⟧ s ‚ ⟦ ⌜ b ⌝ ⟧ s) s) (⟦⌜Rec⌝⟧-aux {!!} s a b) ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ} ⟧ s
   (λ x → rec (λ y → ⟦ weaken, ι (weaken, ι ⌜ a ⌝) ⟧ (s ‚ x ‚ y) (η⋆ y)) (⟦ weaken, ι ⌜ b ⌝ ⟧ (s ‚ x)) x)
   (⟦ ⌜ c ⌝ ⟧ s)
  ＝⟨ refl ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ} · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) · ⌜ c ⌝ ⟧ s
  ∎

⟦close-⌜Rec⌝⟧ : {A : type} {σ : type} {Γ : Cxt} (s : IB【 Γ 】 A) (a : T Γ (ι ⇒ σ ⇒ σ)) (b : T Γ σ) (c : T Γ ι)
              → ⟦ close (⌜_⌝  {Γ} {σ} {A} (Rec a b c)) s ⟧₀
             ＝ ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
                   · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s
                   · close ⌜ c ⌝ s ⟧₀
⟦close-⌜Rec⌝⟧ {A} {σ} {Γ} s a b c =
 ⟦ close (⌜_⌝  {Γ} {σ} {A} (Rec a b c)) s ⟧₀
  ＝⟨ ap (λ k → k ⟨⟩) (⟦close⟧ (⌜_⌝  {Γ} {σ} {A} (Rec a b c)) s) ⟩
 ⟦ ⌜_⌝  {Γ} {σ} {A} (Rec a b c) ⟧ (【Sub】 s ⟨⟩)
  ＝⟨ ⟦⌜Rec⌝⟧ (【Sub】 s ⟨⟩) a b c ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
   · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀))
   · ⌜ c ⌝ ⟧ (【Sub】 s ⟨⟩)
  ＝⟨ (ap (λ k → k ⟨⟩) (⟦close⟧ (⌜Kleisli-extension⌝ {ι} {A} {σ} · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) · ⌜ c ⌝) s)) ⁻¹ ⟩
 ⟦ close ⌜Kleisli-extension⌝ s
   · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s
   · close ⌜ c ⌝ s ⟧₀
  ＝⟨ ap (λ k → ⟦ k · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s · close ⌜ c ⌝ s ⟧₀)
         ((close-⌜Kleisli-extension⌝ s) ⁻¹) ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
   · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s
   · close ⌜ c ⌝ s ⟧₀
  ∎

{-
-- in the middle of generalising this lemma
⌜main-lemma⌝-rec : {σ : type} (α : Baire) (f : 〖 ι ⇒ σ ⇒ σ 〗) (g : 〖 σ 〗) (t : ℕ)
                   (f' : T₀ (B-type〖 ι ⇒ σ ⇒ σ 〗 ((ι ⇒ ι) ⇒ ι)))
                   (g' : T₀ (B-type〖 σ 〗 ((ι ⇒ ι) ⇒ ι)))
                   (t' : T₀ (B-type〖 ι 〗 ((ι ⇒ ι) ⇒ ι)))
                 → R⋆ α f f'
                 → R⋆ α g g'
                 → R⋆ α t t'
                 → R⋆ α (rec f g t)
                        (⌜Kleisli-extension⌝ {ι} {(ι ⇒ ι) ⇒ ι} {σ}
                          · ƛ (Rec (ƛ (weaken, ι (weaken, ι f') · (⌜η⌝ · ν₀))) (weaken, ι g') ν₀)
                          · t')
⌜main-lemma⌝-rec {ι} α f g t f' g' t' rf rg rt =
 rec f g t
  ＝⟨ ap (rec f g) rt ⟩
 rec f g (⟦ t' ⟧₀ (λ z α₁ → z) (λ φ x α₁ → φ (α₁ x) α₁) α)
  ＝⟨ {!!} ⟩
 ⟦ t' ⟧₀
   (λ s → rec (λ u → ⟦ weaken, ι (weaken, ι f') ⟧ (⟨⟩ ‚ s ‚ u) (η⋆ u))
              (⟦ weaken, ι g' ⟧ (⟨⟩ ‚ s))
              s
          (λ z α → z) (λ φ x α → φ (α x) α))
   (λ φ x α → φ (α x) α)
   α
  ＝⟨ refl ⟩
 dialogue⋆ ⟦ ⌜kleisli-extension⌝ · ƛ (Rec (ƛ (weaken, ι (weaken, ι f') · (⌜η⌝ · ν₀))) (weaken, ι g') ν₀) · t' ⟧₀ α
  ∎
⌜main-lemma⌝-rec {σ ⇒ τ} α f g t f' g' t' rf rg rt x x' rx =
 R⋆-preserves-⟦⟧'
  (rec f g t x)
  (⌜Kleisli-extension⌝ · ƛ (Rec (ƛ (weaken, ι (weaken, ι f') · (⌜η⌝ · ν₀))) (weaken, ι g') ν₀ · weaken, ι  ⌜ x' ⌝) · t')
  (ƛ (ƛ (ƛ (⌜Kleisli-extension⌝ · ƛ (ν₃ · ν₀ · ν₁) · ν₁))) ·
    ƛ (Rec (ƛ (weaken, ι (weaken, ι f') · (⌜η⌝ · ν₀))) (weaken, ι g') ν₀)
    · t'
    · ⌜ x' ⌝)
   e c
 where
  c : R⋆ α (rec f g t x)
           (⌜Kleisli-extension⌝
            · ƛ (Rec (ƛ (weaken, ι (weaken, ι f') · (⌜η⌝ · ν₀))) (weaken, ι g') ν₀ · weaken, ι ⌜ x' ⌝)
            · t')
  c = {!!}

  e : ⟦ ⌜Kleisli-extension⌝
        · ƛ (Rec (ƛ (weaken, ι (weaken, ι f') · (⌜η⌝ · ν₀))) (weaken, ι g') ν₀ · weaken, ι ⌜ x' ⌝)
        · t' ⟧₀
      ＝ ⟦ ƛ (ƛ (ƛ (⌜Kleisli-extension⌝ · ƛ (ν₃ · ν₀ · ν₁) · ν₁)))
           · ƛ (Rec (ƛ (weaken, ι (weaken, ι f') · (⌜η⌝ · ν₀))) (weaken, ι g') ν₀)
           · t'
           · ⌜ x' ⌝ ⟧₀
  e =
   ⟦ ⌜Kleisli-extension⌝
     · ƛ (Rec (ƛ (weaken, ι (weaken, ι f') · (⌜η⌝ · ν₀))) (weaken, ι g') ν₀ · weaken, ι ⌜ x' ⌝)
     · t' ⟧₀
    ＝⟨ refl ⟩
   ⟦ ⌜Kleisli-extension⌝ ⟧₀
     (λ w → ⟦ Rec (ƛ (weaken, ι (weaken, ι f') · (⌜η⌝ · ν₀))) (weaken, ι g') ν₀ ⟧ (⟨⟩ ‚ w) (⟦ weaken, ι ⌜ x' ⌝ ⟧ (⟨⟩ ‚ w)))
     ⟦ t' ⟧₀
    ＝⟨ ap₂ -- can we prove that without funext?
          (λ p q → p (λ w → ⟦ Rec (ƛ (weaken, ι (weaken, ι f') · (⌜η⌝ · ν₀))) (weaken, ι g') ν₀ ⟧ (⟨⟩ ‚ w) (q (⟨⟩ ‚ w))) ⟦ t' ⟧₀)
          (⟦⌜Kleisli-extension⌝⟧ {!!} ⟨⟩ (⟨⟩ ‚ ⟦ ƛ (Rec (ƛ (weaken, ι (weaken, ι f') · (⌜η⌝ · ν₀))) (weaken, ι g') ν₀) ⟧₀ ‚ ⟦ t' ⟧₀ ‚ ⟦ ⌜ x' ⌝ ⟧₀))
          (⟦weaken,⟧ ⌜ x' ⌝ ι) ⟩
   ⟦ ⌜Kleisli-extension⌝ ⟧ (⟨⟩ ‚ ⟦ ƛ (Rec (ƛ (weaken, ι (weaken, ι f') · (⌜η⌝ · ν₀))) (weaken, ι g') ν₀) ⟧₀ ‚ ⟦ t' ⟧₀ ‚ ⟦ ⌜ x' ⌝ ⟧₀)
     (λ w → ⟦ Rec (ƛ (weaken, ι (weaken, ι f') · (⌜η⌝ · ν₀))) (weaken, ι g') ν₀ ⟧ (⟨⟩ ‚ w) ⟦ ⌜ x' ⌝ ⟧₀)
     ⟦ t' ⟧₀
    ＝⟨ refl ⟩
   ⟦ ƛ (ƛ (ƛ (⌜Kleisli-extension⌝ · ƛ (ν₃ · ν₀ · ν₁) · ν₁)))
     · ƛ (Rec (ƛ (weaken, ι (weaken, ι f') · (⌜η⌝ · ν₀))) (weaken, ι g') ν₀)
     · t'
     · ⌜ x' ⌝ ⟧₀
    ∎
-}

ℕ→B : ℕ → B ℕ
ℕ→B zero = zero'
ℕ→B (succ n) = succ' (ℕ→B n)

ℕ→T : ℕ → T 〈〉 ι
ℕ→T zero = Zero
ℕ→T (succ n) = Succ (ℕ→T n)

⟦ℕ→T⟧ : (n : ℕ) → ⟦ ℕ→T n ⟧₀ ＝ n
⟦ℕ→T⟧ zero = refl
⟦ℕ→T⟧ (succ n) = ap succ (⟦ℕ→T⟧ n)

η⋆ℕ→T : {A : type} (n : ℕ) → η⋆ ⟦ ℕ→T n ⟧₀ ＝ ⟦ ⌜_⌝ {_} {_} {A} (ℕ→T n) ⟧₀
η⋆ℕ→T {A} zero = refl
η⋆ℕ→T {A} (succ n) = ap₂ (λ p q → p succ q) (B-functor-meaning ⁻¹) (η⋆ℕ→T n)

⌜η⌝ℕ→T : {A : type} (n : ℕ) → ⟦ ⌜η⌝ · ℕ→T n ⟧₀ ＝ ⟦ ⌜_⌝ {_} {_} {A} (ℕ→T n) ⟧₀
⌜η⌝ℕ→T {A} n = ap (λ k → k ⟦ ℕ→T n ⟧₀) η-meaning ∙ η⋆ℕ→T n

⌜η⌝ℕ→T' : {X Y A : type} (n : ℕ) → ⟦ ⌜η⌝ {X} {Y} {ι} {A} · ℕ→T n ⟧₀ ＝ η⋆ n
⌜η⌝ℕ→T' {X} {Y} {A} n = ap η⋆ (⟦ℕ→T⟧ n)

⌜main-lemma⌝-rec-zero : {σ : type}
                        (a : T (〈〉 ,, ι) (ι ⇒ B-type〖 σ ⇒ σ 〗 ((ι ⇒ ι) ⇒ ι)))
                        (b : T₀ (B-type〖 σ 〗 ((ι ⇒ ι) ⇒ ι)))
                      → ⟦ (ƛ (Rec a (weaken, ι b) ν₀)) · Zero ⟧₀
                     ＝ ⟦ b ⟧₀
⌜main-lemma⌝-rec-zero {σ} a b =
 ⟦ (ƛ (Rec a (weaken, ι b) ν₀)) · Zero ⟧₀
  ＝⟨ refl ⟩
 rec (⟦ a ⟧ (⟨⟩ ‚ zero)) (⟦ weaken, ι b ⟧ (⟨⟩ ‚ zero)) zero
  ＝⟨ refl ⟩
 ⟦ weaken, ι b ⟧ (⟨⟩ ‚ zero)
  ＝⟨ ap (λ k → k (⟨⟩ ‚ zero)) (⟦weaken,⟧ b ι) ⟩
 ⟦ b ⟧₀
  ∎

＝rec : {X : 𝓤 ̇ } → (f g : ℕ → X → X) → (x y : X) → (n : ℕ)
       → x ＝ y
       → ((i : ℕ) (u v : X) → u ＝ v → f i u ＝ g i v)
       → rec f x n ＝ rec g y n
＝rec {X} {X₁} f g x y zero z e = z
＝rec {X} {X₁} f g x y (succ n) z e = e n (rec f x n) (rec g y n) (＝rec f g x y n z e)

⟦weaken,-weaken,⟧-as-⟦weaken,⟧ : {Γ : Cxt} {σ τ : type} (s : 【 Γ 】) (x y z : 〖 σ 〗) (a : T Γ τ)
                               → ⟦ weaken, σ (weaken, σ a) ⟧ (s ‚ y ‚ z)
                               ＝ ⟦ weaken, σ a ⟧ (s ‚ x)
⟦weaken,-weaken,⟧-as-⟦weaken,⟧ {Γ} {σ} {τ} s x y z a =
 ⟦ weaken, σ (weaken, σ a) ⟧ (s ‚ y ‚ z)
  ＝⟨ ap (λ k → k (s ‚ y ‚ z)) (⟦weaken,⟧ (weaken, σ a) σ) ⟩
 ⟦ weaken, σ a ⟧ (s ‚ y)
  ＝⟨ ap (λ k → k (s ‚ y)) (⟦weaken,⟧ a σ) ⟩
 ⟦ a ⟧ s
  ＝⟨ ap (λ k → k (s ‚ x)) (⟦weaken,⟧ a σ) ⁻¹ ⟩
 ⟦ weaken, σ a ⟧ (s ‚ x)
  ∎

{-
⌜main-lemma⌝-rec-succ : {σ : type}
                        (a : T₀ (B-type〖 ι ⇒ σ ⇒ σ 〗 ((ι ⇒ ι) ⇒ ι)))
                        (b : T₀ (B-type〖 σ 〗 ((ι ⇒ ι) ⇒ ι)))
                        (n : T₀ ι)
                      → ⟦ (ƛ (Rec (ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀))) (weaken, ι b) ν₀)) · Succ n ⟧₀
                     ＝ ⟦ a · (⌜η⌝ · n) · Rec (ƛ (weaken, ι a · (⌜η⌝ · ν₀))) b n ⟧₀
⌜main-lemma⌝-rec-succ {σ} a b n =
 ⟦ (ƛ (Rec (ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀))) (weaken, ι b) ν₀)) · Succ n ⟧₀
  ＝⟨ refl ⟩
 rec (⟦ ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)) (⟦ weaken, ι b ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)) (succ ⟦ n ⟧₀)
  ＝⟨ refl ⟩
 ⟦ weaken, ι (weaken, ι a) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
   (η⋆ ⟦ n ⟧₀)
   (rec (⟦ ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)) (⟦ weaken, ι b ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)) ⟦ n ⟧₀)
  ＝⟨ ap₂ (λ p q → p (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀) (η⋆ ⟦ n ⟧₀) (rec (⟦ ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)) (q (⟨⟩ ‚ succ ⟦ n ⟧₀)) ⟦ n ⟧₀))
          (⟦weaken,⟧ (weaken, ι a) ι) (⟦weaken,⟧ b ι) ⟩
 ⟦ weaken, ι a ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀) (η⋆ ⟦ n ⟧₀) (rec (λ x → ⟦ weaken, ι (weaken, ι a) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x) (η⋆  x)) ⟦ b ⟧₀ ⟦ n ⟧₀)
  ＝⟨ ap (λ p → p (⟨⟩ ‚ succ ⟦ n ⟧₀) (η⋆ ⟦ n ⟧₀) (rec (λ x → ⟦ weaken, ι (weaken, ι a) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x) (η⋆ x)) ⟦ b ⟧₀ ⟦ n ⟧₀))
        (⟦weaken,⟧ a ι) ⟩
 ⟦ a ⟧₀ (η⋆ ⟦ n ⟧₀) (rec (λ x → ⟦ weaken, ι (weaken, ι a) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x) (η⋆ x)) ⟦ b ⟧₀ ⟦ n ⟧₀)
  ＝⟨ ap (λ p → ⟦ a ⟧₀ (η⋆ ⟦ n ⟧₀) p)
         (＝rec
           (λ x → ⟦ weaken, ι (weaken, ι a) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x) (η⋆ x))
           (λ x → ⟦ weaken, ι a ⟧ (⟨⟩ ‚ x) (η⋆ x))
           ⟦ b ⟧₀ ⟦ b ⟧₀ ⟦ n ⟧₀ refl
           (λ i u v e → ap₂ (λ q r → q (η⋆ i) r) (⟦weaken,-weaken,⟧-as-⟦weaken,⟧ ⟨⟩ i (succ ⟦ n ⟧₀) i a) e )) ⟩
 ⟦ a · (⌜η⌝ · n) · Rec (ƛ (weaken, ι a · (⌜η⌝ · ν₀))) b n ⟧₀
  ∎
-}

{-
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
⌜main-lemma⌝ {Γ} {σ} (Rec f g t) α xs ys rxys =
 transport
  (λ k → R⋆ α (rec (⟦ f ⟧ xs) (⟦ g ⟧ xs) (⟦ t ⟧ xs)) k)
  (⌜close⌝ (Rec f g t) ys ⁻¹)
  (R⋆-preserves-⟦⟧'
    (rec (⟦ f ⟧ xs) (⟦ g ⟧ xs) (⟦ t ⟧ xs))
    (⌜Kleisli-extension⌝ {ι} {(ι ⇒ ι) ⇒ ι} {σ} · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ close f ys ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ close g ys ⌝) ν₀)) · ⌜ close t ys ⌝)
    ⌜ Rec (close f ys) (close g ys) (close t ys) ⌝
    ((⟦⌜Rec⌝⟧ ⟨⟩ (close f ys) (close g ys) (close t ys)) ⁻¹)
    (transport₃ (λ p q r → R⋆ α (rec (⟦ f ⟧ xs) (⟦ g ⟧ xs) (⟦ t ⟧ xs))
                                (⌜Kleisli-extension⌝
                                 · ƛ (Rec (ƛ (weaken, ι (weaken, ι p) · (⌜η⌝ · ν₀))) (weaken, ι q) ν₀)
                                 · r))
       (⌜close⌝ f ys) (⌜close⌝ g ys) (⌜close⌝ t ys) c))
 where
  rf : (x  : 〖 ι 〗) (x' : T₀ ι) (rx : R⋆ {ι} α x ⌜ x' ⌝)
       (y  : 〖 σ 〗) (y' : T₀ σ) (ry : R⋆ {σ} α y ⌜ y' ⌝)
     → R⋆ α (⟦ f ⟧ xs x y) (close ⌜ f ⌝ (⌜Sub⌝ ys) · ⌜ x' ⌝ · ⌜ y' ⌝)
  rf = ⌜main-lemma⌝ f α xs ys rxys

  rn : ℕ → 〖 σ 〗
  rn n = rec (⟦ f ⟧ xs) (⟦ g ⟧ xs) n

  rn' : T₀ (ι ⇒ B-type〖 σ 〗 ((ι ⇒ ι) ⇒ ι))
  rn' = ƛ (Rec (ƛ (weaken, ι (weaken, ι (close ⌜ f ⌝ (⌜Sub⌝ ys))) · (⌜η⌝ · ν₀))) (weaken, ι (close ⌜ g ⌝ (⌜Sub⌝ ys))) ν₀)

  r1 : (n : ℕ) → ⟦ ⌜η⌝ · ℕ→T n ⟧₀ ＝ ⟦ ⌜_⌝ {_} {_} {(ι ⇒ ι) ⇒ ι} (ℕ→T n) ⟧₀
  r1 n = ⌜η⌝ℕ→T n

--  r2 : (n : ℕ) → ⟦ Rec (ƛ (weaken, ι (close ⌜ f ⌝ (⌜Sub⌝ ys)) · (⌜η⌝ · ν₀))) (close ⌜ g ⌝ (⌜Sub⌝ ys)) (ℕ→T n) ⟧₀
--              ＝ ⟦ ⌜ ? ⌝ ⟧₀
--  r2 n = ?

  rnn : (n : ℕ) → R⋆ α (rn n) (rn' · ℕ→T n)
  rnn zero = r
   where
    r : R⋆ α (⟦ g ⟧ xs) (rn' · Zero)
    r = R⋆-preserves-⟦⟧'
         (⟦ g ⟧ xs)
         (close ⌜ g ⌝ (⌜Sub⌝ ys))
         (rn' · Zero)
         (⌜main-lemma⌝-rec-zero (ƛ (weaken, ι (weaken, ι (close ⌜ f ⌝ (⌜Sub⌝ ys))) · (⌜η⌝ · ν₀))) (close ⌜ g ⌝ (⌜Sub⌝ ys)) ⁻¹)
         (⌜main-lemma⌝ g α xs ys rxys)
  rnn (succ n) = r
   where
    r : R⋆ α (⟦ f ⟧ xs n (rn n)) (rn' · Succ (ℕ→T n))
    r = R⋆-preserves-⟦⟧'
         (⟦ f ⟧ xs n (rn n))
         (close ⌜ f ⌝ (⌜Sub⌝ ys) · (⌜η⌝ · ℕ→T n) · Rec (ƛ (weaken, ι (close ⌜ f ⌝ (⌜Sub⌝ ys)) · (⌜η⌝ · ν₀))) (close ⌜ g ⌝ (⌜Sub⌝ ys)) (ℕ→T n))
         (rn' · Succ (ℕ→T n))
         ((⌜main-lemma⌝-rec-succ (close ⌜ f ⌝ (⌜Sub⌝ ys)) (close ⌜ g ⌝ (⌜Sub⌝ ys)) (ℕ→T n)) ⁻¹)
         {!!} -- use rf, but for that turn the arguments into ⌜_⌝s (r1 & ?)

  -- Generalise this lemma (⌜main-lemma⌝-rec) with the above as it is done in LambdaWithoutOracle?
  c : R⋆ α (rec (⟦ f ⟧ xs) (⟦ g ⟧ xs) (⟦ t ⟧ xs))
           (⌜Kleisli-extension⌝ {ι} {(ι ⇒ ι) ⇒ ι} {σ}
             · ƛ (Rec (ƛ (weaken, ι (weaken, ι (close ⌜ f ⌝ (⌜Sub⌝ ys))) · (⌜η⌝ · ν₀))) (weaken, ι (close ⌜ g ⌝ (⌜Sub⌝ ys))) ν₀)
             · close ⌜ t ⌝ (⌜Sub⌝ ys))
  c = ⌜main-lemma⌝-rec α
        (⟦ f ⟧ xs) (⟦ g ⟧ xs) (⟦ t ⟧ xs)
        (close ⌜ f ⌝ (⌜Sub⌝ ys)) (close ⌜ g ⌝ (⌜Sub⌝ ys)) (close ⌜ t ⌝ (⌜Sub⌝ ys))
        (⌜main-lemma⌝ f α xs ys rxys) (⌜main-lemma⌝ g α xs ys rxys) (⌜main-lemma⌝ t α xs ys rxys)
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
    ＝⟨ ap (λ k → ⟦ ⌜ k ⌝ ⟧₀) (close-Sub,,-as-close-Subƛ t ys y) ⟩
   ⟦ ⌜ close (close t (Subƛ ys)) (Sub1 y) ⌝ ⟧₀
    ＝⟨ ap (λ k → ⟦ k ⟧₀) (⌜close⌝ (close t (Subƛ ys)) (Sub1 y) ⁻¹) ⟩
   ⟦ close ⌜ close t (Subƛ ys) ⌝ (⌜Sub⌝ (Sub1 y)) ⟧₀
    ＝⟨ ⟦close⟧' (⌜ close t (Subƛ ys) ⌝) (⌜Sub⌝ (Sub1 y)) ⟩
   ⟦ ⌜ close t (Subƛ ys) ⌝ ⟧ (【Sub₀】 (⌜Sub⌝ (Sub1 y)))
    ＝⟨ ⟦⟧-eta ⌜ close t (Subƛ ys) ⌝ (【Sub₀】 (⌜Sub⌝ (Sub1 y))) (⟨⟩ ‚ ⟦ ⌜ y ⌝ ⟧₀) (＝【】-【sub】-⌜Sub⌝-Sub1 y) ⟩
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
-}

\end{code}

TODO move results about substitution to Internal.lagda and move this
     to either Internal.lagda or a new file.

Using a logical relation we show that the the internal, church-encoded dialogue
translation of a System T term coincides with its external, inductive dialogue
translation.

From this result and the main-lemma we can derive an internal result of
strong continuity in System T.

\begin{code}

_≣⋆_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
      → ({A : type} → D⋆ X Y Z 〖 A 〗) → ({A : type } → D⋆ X Y Z 〖 A 〗) → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
_≣⋆_ {_} {_} {_} {X} {Y} {Z} d d' =
 (A : type ) → (η' : Z → 〖 A 〗) → (β' : (Y → 〖 A 〗) → X → 〖 A 〗) → d η' β' ＝ d' η' β'

≣⋆-symm : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {d d' : {A : type} → D⋆ X Y Z 〖 A 〗}
        → d ≣⋆ d' → d' ≣⋆ d
≣⋆-symm eq A η' β' = (eq A η' β') ⁻¹

≣⋆-trans : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {d d' d'' : {A : type} → D⋆ X Y Z 〖 A 〗}
          → d ≣⋆ d' → d' ≣⋆ d'' → d ≣⋆ d''
≣⋆-trans eq eq' A η' β' = eq A η' β' ∙ eq' A η' β'

is-dialogue-for : (d : B ℕ) (t : {A : type} → T₀ (B-type〖 ι 〗 A)) → Type
is-dialogue-for d t = ⟦ t ⟧₀ ≣⋆ church-encode d

-- Logical predicate for internal dialogue trees which can be pattern matched on
-- and for functions that preserve said pattern matching.
Rnorm : {σ : type} (d : B〖 σ 〗) (t : {A : type} → T₀ (B-type〖 σ 〗 A)) → Type
Rnorm {ι}     d t = is-dialogue-for d t
Rnorm {σ ⇒ τ} d t = (u : B〖 σ 〗) (u' : {A : type} → T₀ (B-type〖 σ 〗 A))
                  → Rnorm u u' → Rnorm (d u) (t · u')

Rnorms : {Γ : Cxt} → B【 Γ 】 → ({A : type} → IB【 Γ 】 A) → Type
Rnorms {Γ} xs ys = {σ : type} (i : ∈Cxt σ Γ) → Rnorm (xs i) (ys (∈Cxt-B-type i))

-- To avoid the operational semantics, we use the following lemma.
Rnorm-preserves-⟦⟧ : {σ : type} (d : B〖 σ 〗) (t u : {A : type} → T₀ (B-type〖 σ 〗 A))
                   → ((A : type) →  ⟦ t {A} ⟧₀ ＝ ⟦ u {A} ⟧₀)
                   → Rnorm d t
                   → Rnorm d u
Rnorm-preserves-⟦⟧ {ι} d t u t＝u eq A η' β' =
 transport (λ f → f η' β' ＝ church-encode d η' β') (t＝u A) (eq A η' β')
Rnorm-preserves-⟦⟧ {σ ⇒ τ} d t u t＝u Rnorm-t v v' Rnorm-v =
 Rnorm-preserves-⟦⟧ (d v) (t · v') (u · v') (λ A → ap (λ f → f ⟦ v' ⟧₀) (t＝u A)) (Rnorm-t v v' Rnorm-v)

\end{code}

As Rnorm quantifies over all System T types, we can elimate a family of
church-encoded trees into different types, allowing us to reify terms into
the shape of ⌜η⌝ or ⌜β⌝.

This sort of reification is crucial when we need to pattern match on the
constructor of a church-encoded tree.

\begin{code}

Rnormη : (n : ℕ) → Rnorm (η n) (⌜η⌝ · ℕ→T n)
Rnormη n A η' β' = ap (λ k → k η' β') (⌜η⌝ℕ→T' n)

Rnormη⌜η⌝ : (n : ℕ) (n' : T₀ ι) → Rnorm (η n) (⌜η⌝ · n') → ⟦ n' ⟧₀ ＝ ⟦ ℕ→T n ⟧₀
Rnormη⌜η⌝ n n' rn = rn ι (λ x → x) (λ x → x) ∙ ⟦ℕ→T⟧ n ⁻¹

Rnorm-reify-η' : (n : ℕ) (t : {A : type} → T₀ (⌜B⌝ ι A))
               → Rnorm (η n) t
               → ⟦ t ⟧₀ ≣⋆ ⟦ ⌜η⌝ · ℕ→T n ⟧₀ × Rnorm (η n) (⌜η⌝ · ℕ→T n)
Rnorm-reify-η' n t eq =
 ≣⋆-trans eq (≣⋆-symm (Rnormη n)) ,
 Rnormη n

Rnorm-reify-η : (n : ℕ) (t : {A : type} → T₀ (⌜B⌝ ι A))
                → Rnorm (η n) t
                → Σ n' ꞉ T₀ ι , ⟦ t ⟧₀ ≣⋆ ⟦ ⌜η⌝ · n' ⟧₀ × Rnorm (η n) (⌜η⌝ · n')
Rnorm-reify-η n t eq = n' , eq' , rη
 where
 -- We get the leaf value at t with the following
 --   t · (ƛ n : ι , n)
 --     · foobar
 -- It does not matter what the second argument to t is, since it is definitely
 -- something of the shape η n.
  n' : T₀ ι
  n' = t · ƛ ν₀ · ƛ (ƛ Zero)

  eq' : ⟦ t ⟧₀ ≣⋆ ⟦ ⌜η⌝ · n' ⟧₀
  eq' A η' β' = ⟦ t ⟧₀ η' β'              ＝⟨ eq A η' β' ⟩
                church-encode (η n) η' β' ＝⟨ by-definition ⟩
                η' n                      ＝⟨ ap η' (eq ι ⟦ ƛ ν₀ ⟧₀ ⟦ ƛ (ƛ Zero) ⟧₀) ⁻¹ ⟩
                η' ⟦ n' ⟧₀                ＝⟨ by-definition ⟩
                ⟦ ⌜η⌝ · n' ⟧₀ η' β'       ∎

  rη : Rnorm (η n) (⌜η⌝ · n')
  rη = ≣⋆-trans (≣⋆-symm eq') eq

church-encode-β : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {A : 𝓣 ̇ } (ψ : Y → D X Y Z) (y : X)
                  (η' : Z → A) (β' : (Y → A) → X → A)
                → church-encode (β ψ y) η' β' ＝ β' (λ y → church-encode (ψ y) η' β') y
church-encode-β {X} {Y} {Z} {A} ψ y η' β' = refl

B-branch : (t : {A : type} → T₀ (⌜B⌝ ι A)) → {A : type} → T₀ (ι ⇒ ⌜B⌝ ι A)
B-branch t {A} =
 -- λ i. λ η. λ β. t η' β' h
 ƛ (ƛ (ƛ (weaken₀ (t {((ι ⇒ A) ⇒ (ι ⇒ A)) ⇒ A}) · η' · β' · h)))
 where
  -- λ n. λ k. η(n)
  η' : T (〈〉 ,, ι ,, (ι ⇒ A) ,, ((ι ⇒ A) ⇒ ι ⇒ A)) (ι ⇒ ((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A)
  η' = ƛ (ƛ (ν₃ · ν₁))

  -- λ g. λ n. λ h. h (λ j. g j β) n
  β' : T (〈〉 ,, ι ,, (ι ⇒ A) ,, ((ι ⇒ A) ⇒ ι ⇒ A)) ((ι ⇒ ((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A) ⇒ ι ⇒ ((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A)
  β' = ƛ (ƛ (ƛ (ν₀ · ƛ (ν₃ · ν₀ · ν₄) · ν₁)))

  -- λ k. λ n.k i
  h : T (〈〉 ,, ι ,, (ι ⇒ A) ,, ((ι ⇒ A) ⇒ ι ⇒ A)) ((ι ⇒ A) ⇒ ι ⇒ A)
  h = ƛ (ƛ (ν₁ · ν₄))

⟦B-branch⟧ : (ϕ : ℕ → B ℕ) (i : ℕ) (n : ℕ) (t : {A : type} → T₀ (⌜B⌝ ι A))
           → Rnorm (β ϕ n) t
           → ⟦ B-branch t ⟧₀ i ≣⋆ church-encode (ϕ i)
⟦B-branch⟧ ϕ i n t h A η' β' =
 ⟦ B-branch t ⟧₀ i η' β'
  ＝⟨ refl ⟩
 ⟦ weaken₀ (t {((ι ⇒ A) ⇒ (ι ⇒ A)) ⇒ A}) ⟧ (⟨⟩ ‚ i ‚ η' ‚ β') η₀ β₀ h₀
  ＝⟨ ap (λ k → k η₀ β₀ h₀) (⟦weaken₀⟧ (t {((ι ⇒ A) ⇒ (ι ⇒ A)) ⇒ A}) (⟨⟩ ‚ i ‚ η' ‚ β')) ⟩
 ⟦ t {((ι ⇒ A) ⇒ (ι ⇒ A)) ⇒ A} ⟧₀ η₀ β₀ h₀
  ＝⟨ ap (λ k → k h₀) (h (((ι ⇒ A) ⇒ (ι ⇒ A)) ⇒ A) η₀ β₀) ⟩
 church-encode (β ϕ n) η₀ β₀ h₀
  ＝⟨ refl ⟩
 church-encode (ϕ i) η₀ β₀ β'
  ＝⟨ q {!!} (ϕ i) ⟩ -- can we do without funext?
 church-encode (ϕ i) η' β'
  ∎
 where
  η₀ : 〖 ι ⇒ ((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A 〗
  η₀ = λ n → λ k → η' n

  β₀ : 〖 (ι ⇒ ((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A) ⇒ ι ⇒ ((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A 〗
  β₀ = λ g → λ n → λ h → h (λ j → g j β') n

  h₀ : 〖 (ι ⇒ A) ⇒ ι ⇒ A 〗
  h₀ = λ k → λ n → k i

  q : (ext : naive-funext 𝓤₀ 𝓤₀) (d : B ℕ) → church-encode d η₀ β₀ β' ＝ church-encode d η' β'
  q ext (η x) = refl
  q ext (β ψ y) =
   church-encode (β ψ y) η₀ β₀ β'
    ＝⟨ refl ⟩
   β' (λ j → church-encode (ψ j) η₀ β₀ β') y
    ＝⟨ ap (λ k → β' k y) (ext (λ j → q ext (ψ j))) ⟩
   β' (λ y → church-encode (ψ y) η' β') y
    ＝⟨ refl ⟩
   church-encode (β ψ y) η' β'
    ∎

η⋆≣⋆ : (x : ℕ) (x' : T₀ ι) → η⋆ {_} {_} {_} {_} {ℕ} {ℕ} ⟦ x' ⟧₀ ≣⋆ η⋆ x → ⟦ x' ⟧₀ ＝ x
η⋆≣⋆ x x' h = h ι (λ z → z) (λ _ z → z)

Rnorm-reify-β : (ϕ : ℕ → B ℕ) (n : ℕ) (t : {A : type} → T₀ (⌜B⌝ ι A))
                → Rnorm (β ϕ n) t
                → Σ ϕ' ꞉ ({A : type} → T₀ (ι ⇒ ⌜B⌝ ι A))
                , Σ n' ꞉ T₀ ι
                , ⟦ t ⟧₀ ≣⋆ ⟦ ⌜β⌝ · ϕ' · n' ⟧₀
                × Rnorm (β ϕ n) (⌜β⌝ · ϕ' · n')
                × (⟦ n' ⟧₀ ＝ n)
                × ((x : ℕ) (x' : T₀ ι) → Rnorm (η x) (⌜η⌝ · x') → Rnorm (ϕ x) (ϕ' · x'))
Rnorm-reify-β ϕ n t eq = ϕ' , n' , eq' {!!} , rβ , ⟦ℕ→T⟧ n , rϕ
 where
  -- We get the branching at t with the following
  --   ϕ' = t · ( ƛ z : ι . ƛ i : ι , ⌜η⌝ n )
  --          · ( ƛ ψ : ι ⇒ (ι ⇒ ⌜B⌝ ι A) , ƛ n : ι , ƛ x : ι , ⌜β⌝ ψ x x )
  -- Which does ?TODO figure out what this does?
  ϕ' : {A : type} → T₀ (ι ⇒ ⌜B⌝ ι A)
  ϕ' {A} = B-branch t -- t {ι ⇒ A} · ƛ (ƛ ν₀) · ƛ (ƛ (ƛ (ν₂ · ν₀ · ν₀)))

  -- We get the oracle query at t with the following
  --   n' = t · foobar · ƛ ψ : ι ⇒ ι , ƛ n : ι , n
  -- Which ignores the branching and immediately returns the query.
  n' : T₀ ι
  n' = ℕ→T n --t · ƛ Zero · ƛ (ƛ ν₀)

  -- can we do without funext?
  eq' : (ext : naive-funext 𝓤₀ 𝓤₀) → ⟦ t ⟧₀ ≣⋆ ⟦ ⌜β⌝ · ϕ' · n' ⟧₀
  eq' ext A η' β' =
   ⟦ t ⟧₀ η' β'
    ＝⟨ eq A η' β' ⟩
   church-encode (β ϕ n) η' β'
    ＝⟨ by-definition ⟩
   --β' (λ y → D-rec (λ z η'' β'' → η'' z) (λ Φ x η'' β'' → β'' (λ y₁ → Φ y₁ η'' β'') x) (ϕ y) η' β') n
   β' (λ y → church-encode (ϕ y) η' β') n
    ＝⟨ ap (λ k → β' k n) (ext (λ j → ⟦B-branch⟧ ϕ j n t eq A η' β' ⁻¹)) ⟩
   β' (λ y → ⟦ B-branch t ⟧₀ y η' β') n
    ＝⟨ ap (λ k → β' (λ y → ⟦ ϕ' ⟧₀ y η' β') k) ((⟦ℕ→T⟧ n) ⁻¹) ⟩
   β' (λ y → ⟦ ϕ' ⟧₀ y η' β') ⟦ n' ⟧₀ --β' ⟦ ϕ' ⟧₀ ⟦ n' ⟧₀
    ＝⟨ by-definition ⟩
   β⋆ ⟦ ϕ' ⟧₀ ⟦ n' ⟧₀ η' β'
    ＝⟨ by-definition ⟩
   ⟦ ⌜β⌝ · ϕ' · n' ⟧₀ η' β'
    ∎

  rβ : Rnorm (β ϕ n) (⌜β⌝ · ϕ' · n')
  rβ = ≣⋆-trans (≣⋆-symm (eq' {!!})) eq

  rϕ : (x : ℕ) (x' : T₀ ι)
     → η⋆ ⟦ x' ⟧₀ ≣⋆ η⋆ x
     → ⟦ B-branch t ⟧₀ ⟦ x' ⟧₀ ≣⋆ church-encode (ϕ x)
  rϕ x x' h = transport (λ k → ⟦ B-branch t ⟧₀ k ≣⋆ church-encode (ϕ x)) ((η⋆≣⋆ x x' h) ⁻¹) (⟦B-branch⟧ ϕ x n t eq)

-- TODO: can we generalize this?
church-encode-kleisli-extension : (ext : naive-funext 𝓤₀ 𝓤₀)
                                  {A : type} (η' : ℕ → 〖 A 〗) (β' : (ℕ → 〖 A 〗) → ℕ → 〖 A 〗) (d : B ℕ)
                                  (f : ℕ → B ℕ)
                                  (f' : {A : type} → T₀ (ι ⇒ ⌜B⌝ ι A))
                                → ((x : ℕ) (x' : T₀ ι) → Rnorm (η x) (⌜η⌝ · x') → Rnorm (f x) (f' · x'))
                                → church-encode (kleisli-extension f d) η' β'
                               ＝ kleisli-extension⋆ ⟦ f' ⟧₀ (church-encode d) η' β'
church-encode-kleisli-extension ext {A} η' β' (η x) f f' rf =
 church-encode (f x) η' β'
  ＝⟨ (rf x (ℕ→T x) (Rnormη x) A η' β') ⁻¹ ⟩
 ⟦ f' · ℕ→T x ⟧₀ η' β'
  ＝⟨ ap (λ x → ⟦ f' ⟧₀ x η' β') (⟦ℕ→T⟧ x) ⟩
 ⟦ f' ⟧₀ x η' β'
  ∎
church-encode-kleisli-extension ext {A} η' β' (β g y) f f' rf =
 church-encode (β (λ j → kleisli-extension f (g j)) y) η' β'
  ＝⟨ refl ⟩
 β' (λ y → church-encode (kleisli-extension f (g y)) η' β') y
  ＝⟨ ap (λ k → β' k y) (ext (λ y → church-encode-kleisli-extension ext {A} η' β' (g y) f f' rf)) ⟩
 β' (λ y → church-encode (g y) (λ z → ⟦ f' ⟧₀ z η' β') β') y
  ＝⟨ refl ⟩
 church-encode (β g y) (λ z → ⟦ f' ⟧₀ z η' β') β'
  ∎

-- Since rec is interpreted using ⌜Kleisli-extension⌝, we need to know that
-- ⌜Kleisli-extension⌝ preserves this normalisation property.
-- TODO is it enough to get a context free kleisli lemma
Rnorm-kleisli-lemma : (ext : naive-funext 𝓤₀ 𝓤₀)
                      {σ : type}

                      (f : ℕ → B〖 σ 〗)
                      (f' : {A : type} → T₀ (ι ⇒ B-type〖 σ 〗 A))
                    → ((x : ℕ) (x' : T₀ ι) → Rnorm (η x) (⌜η⌝ · x') → Rnorm (f x) (f' · x'))

                    → (n : B ℕ)
                      (n' : {A : type} → T₀ (⌜B⌝ ι A))
                    → Rnorm {ι} n n'

                    → Rnorm (Kleisli-extension f n) (⌜Kleisli-extension⌝ · f' · n')
Rnorm-kleisli-lemma ext {ι} f f' rf (η y) n' rn A η' β' =
 ⟦ n' ⟧₀ (λ x → ⟦ f' ⟧₀ x η' β') β'
  ＝⟨ rn A (λ x → ⟦ f' ⟧₀ x η' β') β' ⟩
 ⟦ f' ⟧₀ y η' β'
  ＝⟨ ap (λ k → ⟦ f' ⟧₀ k η' β') (⟦ℕ→T⟧ y ⁻¹) ⟩
 ⟦ f' · ℕ→T y ⟧₀ η' β'
  ＝⟨ rf y (ℕ→T y) (Rnormη y) A η' β' ⟩
 church-encode (f y) η' β'
  ∎
Rnorm-kleisli-lemma ext {ι} f f' rf (β ϕ y) n' rn A η' β' with Rnorm-reify-β ϕ y n' rn
... | (ϕ' , y' , eq , rb , ry , rϕ) =
 ⟦ n' ⟧₀ (λ x → ⟦ f' ⟧₀ x η' β') β'
  ＝⟨ eq A (λ x → ⟦ f' ⟧₀ x η' β') β' ⟩
 ⟦ ⌜β⌝ · ϕ' · y' ⟧₀ (λ x → ⟦ f' ⟧₀ x η' β') β'
  ＝⟨ by-definition ⟩
 β' (λ x → ⟦ ϕ' ⟧₀ x (λ z → ⟦ f' ⟧₀ z η' β') β') ⟦ y' ⟧₀
  ＝⟨ ap (β' (λ x → ⟦ ϕ' ⟧₀ x (λ z → ⟦ f' ⟧₀ z η' β') β')) ry ⟩
 β' (λ x → ⟦ ϕ' ⟧₀ x (λ z → ⟦ f' ⟧₀ z η' β') β') y
  ＝⟨ ap (λ k → β' k y) (ext (λ x → ap (λ j → ⟦ ϕ' ⟧₀ j (λ z → ⟦ f' ⟧₀ z η' β') β') ((⟦ℕ→T⟧ x) ⁻¹))) ⟩
 β' (λ x → ⟦ ϕ' · ℕ→T x ⟧₀ (λ z → ⟦ f' ⟧₀ z η' β') β') y
  ＝⟨ ap (λ k → β' k y) (ext (λ x → rϕ x (ℕ→T x) (Rnormη x) A (λ z → ⟦ f' ⟧₀ z η' β') β')) ⟩
 β' (λ x → church-encode (ϕ x) (λ z → ⟦ f' ⟧₀ z η' β') β') y
  ＝⟨ ap (λ k → β' k y) (ext (λ x → church-encode-kleisli-extension ext η' β' (ϕ x) f f' rf ⁻¹)) ⟩
 β' (λ x → church-encode (kleisli-extension f (ϕ x)) η' β') y -- church-encode (f y) η' β'
  ∎
Rnorm-kleisli-lemma ext {σ ⇒ τ} f f' rf n n' rn A η' β' =
 Rnorm-preserves-⟦⟧ (Kleisli-extension (λ x → f x A) n)
   (⌜Kleisli-extension⌝ · ƛ (weaken₀ f' · ν₀ · weaken₀ η') · n')
   (ƛ (ƛ (ƛ (⌜Kleisli-extension⌝ · ƛ (ν₃ · ν₀ · ν₁) · ν₁))) · f' · n' · η')
   e
   (Rnorm-kleisli-lemma ext (λ x → f x A)
     (ƛ (weaken₀ f' · ν₀ · weaken₀ η'))
     rf'
     n n' rn)
 where
  e : (A : type)
    → ⟦ ⌜Kleisli-extension⌝ · ƛ (weaken₀ f' · ν₀ · weaken₀ η') · n' ⟧₀
   ＝ ⟦ ƛ (ƛ (ƛ (⌜Kleisli-extension⌝ · ƛ (ν₃ · ν₀ · ν₁) · ν₁))) · f' · n' · η' ⟧₀
  e A =
   ⟦ ⌜Kleisli-extension⌝ · ƛ (weaken₀ f' · ν₀ · weaken₀ η') · n' ⟧₀
    ＝⟨ refl ⟩
   ⟦ ⌜Kleisli-extension⌝ ⟧₀ (λ x → ⟦ weaken₀ f' ⟧ (⟨⟩ ‚ x) x (⟦ weaken₀ η' ⟧ (⟨⟩ ‚ x))) ⟦ n' ⟧₀
    ＝⟨ ap₂ (λ p q → p q ⟦ n' ⟧₀)
            (⟦⌜Kleisli-extension⌝⟧ {!!} ⟨⟩ (⟨⟩ ‚ ⟦ f' ⟧₀ ‚ ⟦ n' ⟧₀ ‚ ⟦ η' ⟧₀))
            (ext (λ x → ap₂ (λ i j → i x j) (⟦weaken₀⟧ f' (⟨⟩ ‚ x)) (⟦weaken₀⟧ η' (⟨⟩ ‚ x)))) ⟩
   ⟦ ⌜Kleisli-extension⌝ ⟧ (⟨⟩ ‚ ⟦ f' ⟧₀ ‚ ⟦ n' ⟧₀ ‚ ⟦ η' ⟧₀) (λ x → ⟦ f' ⟧₀ x ⟦ η' ⟧₀) ⟦ n' ⟧₀
    ＝⟨ refl ⟩
   ⟦ ƛ (ƛ (ƛ (⌜Kleisli-extension⌝ · ƛ (ν₃ · ν₀ · ν₁) · ν₁))) · f' · n' · η' ⟧₀
    ∎

  rf' : (x : ℕ) (x' : T₀ ι)
      → is-dialogue-for (η x) (⌜η⌝ · x')
      → Rnorm (f x A) (ƛ (weaken₀ f' · ν₀ · weaken₀ η') · x')
  rf' x x' rx =
   Rnorm-preserves-⟦⟧ (f x A)
    (f' · x' · η')
    (ƛ (weaken₀ f' · ν₀ · weaken₀ η') · x')
    (λ A → ap₂ (λ i j → i ⟦ x' ⟧₀ j) ((⟦weaken₀⟧ f' (⟨⟩ ‚ ⟦ x' ⟧₀)) ⁻¹) ((⟦weaken₀⟧ η' (⟨⟩ ‚ ⟦ x' ⟧₀)) ⁻¹))
    (rf x x' (λ A η' β' → rx A η' (λ z → z)) A η' β')

＝【】-【Sub】-Sub,, : {Γ : Cxt} {A σ : type} (ys : IB【 Γ 】 A) (u : T₀ (B-type〖 σ 〗 A))
                     → ＝【】 (【Sub】 (Sub,, ys u) ⟨⟩) (【Sub】 (Subƛ ys) (⟨⟩ ‚ ⟦ u ⟧₀))
＝【】-【Sub】-Sub,, {Γ} {A} {σ} ys u {.(B-type〖 σ 〗 A)} (∈Cxt0 .(B-context【 Γ 】 A)) = refl
＝【】-【Sub】-Sub,, {Γ} {A} {σ} ys u {τ} (∈CxtS .(B-type〖 σ 〗 A) i) =
 ap (λ k → k (⟨⟩ ‚ ⟦ u ⟧₀)) (⟦weaken,⟧ (ys i) (B-type〖 σ 〗 A)) ⁻¹

church-encode-is-natural : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (g : X → Y) (d : B X)
                         → B⋆-functor g (church-encode d) ≣⋆ church-encode (B-functor g d)
church-encode-is-natural g (η n) A η' β' = refl
church-encode-is-natural g (β ϕ n) A η' β' = c {!!}
 where
  c : (ext : naive-funext 𝓤₀ 𝓤₀)
    → β' (λ y → B⋆-functor g (church-encode (ϕ y)) η' β') n
   ＝ β' (λ y → church-encode (B-functor g (ϕ y)) η' β') n
  c ext = ap (λ k → β' k n) (ext (λ y → church-encode-is-natural g (ϕ y) A η' β'))

＝【】-【Sub】-⊆Sub : {Γ : Cxt} (s : Sub₀ Γ)
                   → ＝【】 (【Sub】 (⊆Sub (∈CxtS ι) (Subƛ s)) (⟨⟩ ‚ zero))
                            (【Sub】 s ⟨⟩)
＝【】-【Sub】-⊆Sub {Γ} s {σ} i = ap (λ k → k (⟨⟩ ‚ zero)) (⟦weaken,⟧ (s i) ι)

Rnorm-lemma-rec-zero : {A σ : type} {Γ : Cxt}
                       (a : T (Γ ,, ι) (ι ⇒ B-type〖 σ ⇒ σ 〗 A))
                       (b : T Γ (B-type〖 σ 〗 A))
                       (s : Sub₀ Γ)
                     → ⟦ (close (ƛ (Rec a (weaken, ι b) ν₀)) s) · Zero ⟧₀
                    ＝ ⟦ close b s ⟧₀
Rnorm-lemma-rec-zero {A} {σ} {Γ} a b s =
 ⟦ (close (ƛ (Rec a (weaken, ι b) ν₀)) s) · Zero ⟧₀
  ＝⟨ refl ⟩
 ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ zero)
  ＝⟨ ap (λ k → ⟦ k ⟧ (⟨⟩ ‚ zero)) (close-weaken b (⊆, Γ ι) (Subƛ s)) ⟩
 ⟦ close b (⊆Sub (∈CxtS ι) (Subƛ s)) ⟧ (⟨⟩ ‚ zero)
  ＝⟨ ap (λ k → k (⟨⟩ ‚ zero)) (⟦close⟧ b (⊆Sub (∈CxtS ι) (Subƛ s))) ⟩
 ⟦ b ⟧ (【Sub】 (⊆Sub (∈CxtS ι) (Subƛ s)) (⟨⟩ ‚ zero))
  ＝⟨ ⟦⟧-eta b (【Sub】 (⊆Sub (∈CxtS ι) (Subƛ s)) (⟨⟩ ‚ zero)) (【Sub】 s ⟨⟩) (＝【】-【Sub】-⊆Sub s) ⟩
 ⟦ b ⟧ (【Sub】 s ⟨⟩)
  ＝⟨ ap (λ k → k ⟨⟩) ((⟦close⟧ b s) ⁻¹) ⟩
 ⟦ close b s ⟧₀
  ∎

Rnorm-lemma-rec-succ : {A σ : type} {Γ : Cxt}
                       (a : T Γ (B-type〖 ι ⇒ σ ⇒ σ 〗 A))
                       (b : T Γ (B-type〖 σ 〗 A))
                       (n : T₀ ι)
                       (s : Sub₀ Γ)
                     → ⟦ close (ƛ (Rec (ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀))) (weaken, ι b) ν₀)) s · Succ n ⟧₀
                    ＝ ⟦ close a s · (⌜η⌝ · n) · Rec (ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀))) (close b s) n ⟧₀
Rnorm-lemma-rec-succ {A} {σ} {Γ} a b n s =
 ⟦ close (ƛ (Rec (ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀))) (weaken, ι b) ν₀)) s · Succ n ⟧₀
  ＝⟨ refl ⟩
 ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
  (η⋆ ⟦ n ⟧₀)
  (rec (λ x → ⟦ close (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x))
       (⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀))
       ⟦ n ⟧₀)
  ＝⟨ ap₂ (λ p q → p (η⋆ ⟦ n ⟧₀) q) e1 e2 ⟩
 ⟦ close a s ⟧₀
  (η⋆ ⟦ n ⟧₀)
  (rec ⟦ ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀)) ⟧₀ ⟦ close b s ⟧₀ ⟦ n ⟧₀)
  ＝⟨ refl ⟩
 ⟦ close a s · (⌜η⌝ · n) · Rec (ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀))) (close b s) n ⟧₀
  ∎
 where
  e0 : {τ : type} (i : ∈Cxt τ Γ)
     → ⟦ weaken, ι (weaken, ι (s i)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
     ＝ ⟦ s i ⟧₀
  e0 {τ} i =
   ⟦ weaken, ι (weaken, ι (s i)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
    ＝⟨ ap (λ k → k (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)) (⟦weaken,⟧ (weaken, ι (s i)) ι) ⟩
   ⟦ weaken, ι (s i) ⟧ (⊆【】 (⊆, (〈〉 ,, ι) ι) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀))
    ＝⟨ ap (λ k → k (⊆【】 (⊆, (〈〉 ,, ι) ι) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀))) (⟦weaken,⟧ (s i) ι) ⟩
   ⟦ s i ⟧₀
    ∎

  e4 : {τ : type} (i : ∈Cxt τ Γ)
     → ⟦ weaken, ι (s i) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)
     ＝ ⟦ s i ⟧₀
  e4 {τ} i = ap (λ k → k (⟨⟩ ‚ succ ⟦ n ⟧₀)) (⟦weaken,⟧ (s i) ι)

  e1 : ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀) ＝ ⟦ close a s ⟧₀
  e1 =
   ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
    ＝⟨ ap (λ k → k (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)) (⟦close⟧ (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s))) ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀))
    ＝⟨ ap (λ k → k (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀))) (⟦weaken,⟧ (weaken, ι a) ι) ⟩
   ⟦ weaken, ι a ⟧ (⊆【】 (⊆, (Γ ,, ι) ι) (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)))
    ＝⟨ ap (λ k → k (⊆【】 (⊆, (Γ ,, ι) ι) (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)))) (⟦weaken,⟧ a ι) ⟩
   ⟦ a ⟧ (⊆【】 (⊆, Γ ι) (⊆【】 (∈CxtS ι) (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀))))
    ＝⟨ ⟦⟧-eta a (⊆【】 (⊆, Γ ι) (⊆【】 (∈CxtS ι) (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)))) (【Sub₀】 s) e0 ⟩
   ⟦ a ⟧ (【Sub₀】 s)
    ＝⟨ (⟦close⟧' a s) ⁻¹ ⟩
   ⟦ close a s ⟧₀
    ∎

  e3 : ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀) ＝ ⟦ close b s ⟧₀
  e3 =
   ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)
    ＝⟨ ap (λ k → k (⟨⟩ ‚ succ ⟦ n ⟧₀)) (⟦close⟧ (weaken, ι b) (Subƛ s)) ⟩
   ⟦ weaken, ι b ⟧ (【Sub】 (Subƛ s) (⟨⟩ ‚ succ ⟦ n ⟧₀))
    ＝⟨ ap (λ k → k (【Sub】 (Subƛ s) (⟨⟩ ‚ succ ⟦ n ⟧₀))) (⟦weaken,⟧ b ι) ⟩
   ⟦ b ⟧ (⊆【】 (⊆, Γ ι) (【Sub】 (Subƛ s) (⟨⟩ ‚ succ ⟦ n ⟧₀)))
    ＝⟨ ⟦⟧-eta b (⊆【】 (⊆, Γ ι) (【Sub】 (Subƛ s) (⟨⟩ ‚ succ ⟦ n ⟧₀))) (【Sub₀】 s) e4 ⟩
   ⟦ b ⟧ (【Sub₀】 s)
    ＝⟨ (⟦close⟧' b s) ⁻¹ ⟩
   ⟦ close b s ⟧₀
    ∎

  e6 : (i : ℕ) {τ : type} (j : ∈Cxt τ Γ)
     → ⟦ weaken, ι (weaken, ι (s j)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i)
    ＝ ⟦ s j ⟧₀
  e6 i {τ} j = ⟦weaken,-weaken,⟧-as-⟦weaken,⟧ ⟨⟩ i (succ ⟦ n ⟧₀) i (s j) ∙ ap (λ k → k (⟨⟩ ‚ i)) (⟦weaken,⟧ (s j) ι)

  e5 : (i : ℕ) (u v : 〖 B-type〖 σ 〗 A 〗)
     → u ＝ v
     → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
    ＝ ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
  e5 i u v e =
   ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
    ＝⟨ ap₂ (λ p q → p (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) q) (⟦close⟧ (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s))) e ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i)) (η⋆ i) v
    ＝⟨ ap (λ k → k (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i)) (η⋆ i) v) (⟦weaken,⟧ (weaken, ι a) ι) ⟩
   ⟦ weaken, ι a ⟧ (⊆【】 (⊆, (Γ ,, ι) ι) (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i))) (η⋆ i) v
    ＝⟨ ap (λ k → k (⊆【】 (⊆, (Γ ,, ι) ι) (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i))) (η⋆ i) v) (⟦weaken,⟧ a ι) ⟩
   ⟦ a ⟧ (⊆【】 (⊆, Γ ι) (⊆【】 (∈CxtS ι) (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i)))) (η⋆ i) v
    ＝⟨ ap (λ k → k (η⋆ i) v)
           (⟦⟧-eta a (⊆【】 (⊆, Γ ι) (⊆【】 (∈CxtS ι) (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i))))
                     (【Sub】 s (⊆【】 (∈CxtS ι) (⟨⟩ ‚ i))) (e6 i)) ⟩
   ⟦ a ⟧ (【Sub】 s (⊆【】 (∈CxtS ι) (⟨⟩ ‚ i))) (η⋆ i) v
    ＝⟨ ap (λ k → k (⊆【】 (⊆, 〈〉 ι) (⟨⟩ ‚ i)) (η⋆ i) v) ((⟦close⟧ a s) ⁻¹) ⟩
   ⟦ close a s ⟧ (⊆【】 (⊆, 〈〉 ι) (⟨⟩ ‚ i)) (η⋆ i) v
    ＝⟨ ap (λ k → k (⟨⟩ ‚ i) (η⋆ i) v) ((⟦weaken,⟧ (close a s) ι) ⁻¹) ⟩
   ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
    ∎

  e2 : rec (λ x → ⟦ close (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x))
        (⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀))
        ⟦ n ⟧₀
       ＝ rec ⟦ ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀)) ⟧₀ ⟦ close b s ⟧₀ ⟦ n ⟧₀
  e2 = ＝rec
          (λ x → ⟦ close (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x))
          ⟦ ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀)) ⟧₀
          (⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀))
          ⟦ close b s ⟧₀ ⟦ n ⟧₀
          e3 e5

-- as opposed to Rnorm-lemma-rec-succ, this one does not "reduce" as much
Rnorm-lemma-rec-succ2 : {A σ : type} {Γ : Cxt}
                        (a : T Γ (B-type〖 ι ⇒ σ ⇒ σ 〗 A))
                        (b : T Γ (B-type〖 σ 〗 A))
                        (n : T₀ ι)
                        (s : Sub₀ Γ)
                      → ⟦ close (ƛ (Rec (ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀))) (weaken, ι b) ν₀)) s  · n ⟧₀
                     ＝ ⟦ Rec (ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀))) (close b s) n ⟧₀
Rnorm-lemma-rec-succ2 {A} {σ} {Γ} a b n s =
 rec (λ y → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ y) (η⋆ y))
     (⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀))
     ⟦ n ⟧₀
  ＝⟨ ＝rec (λ y → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ y) (η⋆ y))
            (λ y → ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ y) (η⋆ y))
            (⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀)) ⟦ close b s ⟧₀
            ⟦ n ⟧₀ e1 e3 ⟩
 rec (λ y → ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ y) (η⋆ y))
     ⟦ close b s ⟧₀
     ⟦ n ⟧₀
  ∎
 where
  e4 : (i : ℕ) {τ : type} (j : ∈Cxt τ Γ)
     → ⟦ weaken, ι (weaken, ι (s j)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i)
    ＝ ⟦ s j ⟧₀
  e4 i {τ} j = ⟦weaken,-weaken,⟧-as-⟦weaken,⟧ ⟨⟩ i ⟦ n ⟧₀ i (s j) ∙ ap (λ k → k (⟨⟩ ‚ i)) (⟦weaken,⟧ (s j) ι)

  e3 : (i : ℕ) (u v : 〖 B-type〖 σ 〗 A 〗) → u ＝ v
     → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
    ＝ ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
  e3 i u v e =
   ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
    ＝⟨ ap (λ k → k (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) u) (⟦close⟧ (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s))) ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i)) (η⋆ i) u
    ＝⟨ ap (λ k → k (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i)) (η⋆ i) u) (⟦weaken,⟧ (weaken, ι a) ι) ⟩
   ⟦ weaken, ι a ⟧ (⊆【】 (⊆, (Γ ,, ι) ι) (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i))) (η⋆ i) u
    ＝⟨ ap (λ k → k (⊆【】 (⊆, (Γ ,, ι) ι) (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i))) (η⋆ i) u) (⟦weaken,⟧ a ι) ⟩
   ⟦ a ⟧ (⊆【】 (⊆, Γ ι) (⊆【】 (∈CxtS ι) (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i)))) (η⋆ i) u
    ＝⟨ ap₂ (λ p q → p (η⋆ i) q)
            (⟦⟧-eta a (⊆【】 (⊆, Γ ι) (⊆【】 (∈CxtS ι) (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i))))
                      (【Sub】 s (⊆【】 (∈CxtS ι) (⟨⟩ ‚ i)))
                      (e4 i))
            e ⟩
   ⟦ a ⟧ (【Sub】 s (⊆【】 (∈CxtS ι) (⟨⟩ ‚ i))) (η⋆ i) v
    ＝⟨ ap (λ k → k (⊆【】 (⊆, 〈〉 ι) (⟨⟩ ‚ i)) (η⋆ i) v) ((⟦close⟧ a s) ⁻¹) ⟩
   ⟦ close a s ⟧ (⊆【】 (⊆, 〈〉 ι) (⟨⟩ ‚ i)) (η⋆ i) v
    ＝⟨ ap (λ k → k (⟨⟩ ‚ i) (η⋆ i) v) ((⟦weaken,⟧ (close a s) ι) ⁻¹) ⟩
   ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
    ∎

  e2 : {τ : type} (i : ∈Cxt τ Γ)
     → ⟦ weaken, ι (s i) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀)
     ＝ ⟦ s i ⟧₀
  e2 {τ} i = ap (λ k → k (⟨⟩ ‚ ⟦ n ⟧₀)) (⟦weaken,⟧ (s i) ι)

  e1 : ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀) ＝ ⟦ close b s ⟧₀
  e1 =
   ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀)
    ＝⟨ ap (λ k → k (⟨⟩ ‚ ⟦ n ⟧₀)) (⟦close⟧ (weaken, ι b) (Subƛ s)) ⟩
   ⟦ weaken, ι b ⟧ (【Sub】 (Subƛ s) (⟨⟩ ‚ ⟦ n ⟧₀))
    ＝⟨ ap (λ k → k (【Sub】 (Subƛ s) (⟨⟩ ‚ ⟦ n ⟧₀))) (⟦weaken,⟧ b ι) ⟩
   ⟦ b ⟧ (⊆【】 (⊆, Γ ι) (【Sub】 (Subƛ s) (⟨⟩ ‚ ⟦ n ⟧₀)))
    ＝⟨ ⟦⟧-eta b (⊆【】 (⊆, Γ ι) (【Sub】 (Subƛ s) (⟨⟩ ‚ ⟦ n ⟧₀))) (【Sub₀】 s) e2 ⟩
   ⟦ b ⟧ (【Sub₀】 s)
    ＝⟨ (⟦close⟧' b s) ⁻¹ ⟩
   ⟦ close b s ⟧₀
    ∎

is-dialogue-for-zero : ⟦ ⌜zero⌝ ⟧₀ ≣⋆ church-encode zero'
is-dialogue-for-zero A η' β' = refl

≣⋆-B⋆-functor : {X Y : 𝓤 ̇ } {d d' : {A : type} → B⋆ X 〖 A 〗} (f : X → Y)
              → d ≣⋆ d'
              → B⋆-functor f d ≣⋆ B⋆-functor f d'
≣⋆-B⋆-functor {_} {X} {Y} {d} {d'} f eq A η' β' = eq _ _ _

Rnorm-lemma : {Γ : Cxt} {σ : type}
              (xs : B【 Γ 】) (ys : {A : type} → IB【 Γ 】 A)
              (t : T Γ σ)
            → Rnorms xs ys
            → Rnorm (B⟦ t ⟧ xs) (close ⌜ t ⌝ ys)

-- The zero term is always equal to the leaf holding zero.
Rnorm-lemma xs ys Zero Rnorm-xs = is-dialogue-for-zero

-- If at a leaf, apply successor to leaf value.
-- If at a branching node, propagate the successor one level down.
Rnorm-lemma xs ys (Succ t) Rnorm-xs = c
 where
  ind : ⟦ close ⌜ t ⌝ ys ⟧₀ ≣⋆ church-encode (B⟦ t ⟧ xs)
  ind = Rnorm-lemma xs ys t Rnorm-xs

  c : B⋆-functor succ ⟦ close ⌜ t ⌝ ys ⟧₀ ≣⋆ church-encode (B-functor succ (B⟦ t ⟧ xs))
  c = ≣⋆-trans (≣⋆-B⋆-functor succ ind) (church-encode-is-natural succ (B⟦ t ⟧ xs))

  --foo : B⋆-functor succ (church-encode {A = (ℕ → ℕ) → ℕ} d) ≣⋆ church-encode (B-functor succ d)
  --foo = church-encode-is-natural succ d

Rnorm-lemma {Γ} {σ} xs ys (Rec t u v) Rnorm-xs =
-- Rnorm-Rec xs t u v Rnorm-xs (Rnorm-lemma xs t Rnorm-xs) (Rnorm-lemma xs u Rnorm-xs) (Rnorm-lemma xs v Rnorm-xs)
 Rnorm-preserves-⟦⟧
   (rec' (B⟦ t ⟧ xs) (B⟦ u ⟧ xs) (B⟦ v ⟧ xs))
   (⌜Kleisli-extension⌝
    · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ t ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ u ⌝) ν₀)) ys
    · close ⌜ v ⌝ ys)
   (close ⌜ Rec t u v ⌝ ys)
   (λ A → (⟦close-⌜Rec⌝⟧ {A} ys t u v) ⁻¹)
   c1
 where
  rt : (x  : B〖 ι 〗) (x' : {A : type} → T₀ (B-type〖 ι 〗 A)) (rx : Rnorm {ι} x x')
       (y  : B〖 σ 〗) (y' : {A : type} → T₀ (B-type〖 σ 〗 A)) (ry : Rnorm {σ} y y')
     → Rnorm (B⟦ t ⟧ xs x y) (close ⌜ t ⌝ ys · x' · y')
  rt = Rnorm-lemma xs ys t Rnorm-xs

  rn : ℕ → B〖 σ 〗
  rn n = rec (B⟦ t ⟧ xs ∘ η) (B⟦ u ⟧ xs) n

  rn' : {A : type} → T₀ (ι ⇒ B-type〖 σ 〗 A)
  rn' = close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ t ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ u ⌝) ν₀)) ys

  rnn' : (n : ℕ) → Rnorm (rn n) (rn' · ℕ→T n)
  rnn' zero = r
   where
    r : Rnorm (B⟦ u ⟧ xs) (rn' · Zero)
    r = Rnorm-preserves-⟦⟧
         (B⟦ u ⟧ xs) (close ⌜ u ⌝ ys) (rn' · Zero)
         (λ A → (Rnorm-lemma-rec-zero {A} (ƛ (weaken, ι (weaken, ι ⌜ t ⌝) · (⌜η⌝ · ν₀))) ⌜ u ⌝ ys) ⁻¹)
         (Rnorm-lemma xs ys u Rnorm-xs)
  rnn' (succ n) = r
   where
    r : Rnorm (B⟦ t ⟧ xs (η n) (rn n)) (rn' · Succ (ℕ→T n))
    r = Rnorm-preserves-⟦⟧
         (B⟦ t ⟧ xs (η n) (rn n))
         (close ⌜ t ⌝ ys · (⌜η⌝ · ℕ→T n) · Rec (ƛ (weaken, ι (close ⌜ t ⌝ ys) · (⌜η⌝ · ν₀))) (close ⌜ u ⌝ ys) (ℕ→T n))
         (rn' · Succ (ℕ→T n))
         (λ A → (Rnorm-lemma-rec-succ {A} ⌜ t ⌝ ⌜ u ⌝ (ℕ→T n) ys) ⁻¹)
         (rt (η n) (⌜η⌝ · ℕ→T n) (Rnormη n)
             (rn n) (Rec (ƛ (weaken, ι (close ⌜ t ⌝ ys) · (⌜η⌝ · ν₀))) (close ⌜ u ⌝ ys) (ℕ→T n))
             (Rnorm-preserves-⟦⟧
               (rn n)
               (close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ t ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ u ⌝) ν₀)) ys · ℕ→T n)
               (Rec (ƛ (weaken, ι (close ⌜ t ⌝ ys) · (⌜η⌝ · ν₀))) (close ⌜ u ⌝ ys) (ℕ→T n))
               (λ A → Rnorm-lemma-rec-succ2 {A} ⌜ t ⌝ ⌜ u ⌝ (ℕ→T n) ys)
               (rnn' n)))

  rnn'' : (n : ℕ) (n' : T₀ ι) → Rnorm (η n) (⌜η⌝ · n') → Rnorm (rn n) (rn' · n')
  rnn'' n n' r =
   Rnorm-preserves-⟦⟧
    (rn n) (rn' · ℕ→T n) (rn' · n')
    (λ A → ap (λ k → ⟦ rn' ⟧₀ k) (Rnormη⌜η⌝ n n' r) ⁻¹)
    (rnn' n)

  c1 : Rnorm (Kleisli-extension rn (B⟦ v ⟧ xs))
             (⌜Kleisli-extension⌝ · rn' · close ⌜ v ⌝ ys)
  c1 = Rnorm-kleisli-lemma {!!} rn rn' rnn'' (B⟦ v ⟧ xs) (close ⌜ v ⌝ ys) (Rnorm-lemma xs ys v Rnorm-xs)

Rnorm-lemma xs ys (ν i) Rnorm-xs = Rnorm-xs i

Rnorm-lemma xs ys (ƛ t) Rnorm-xs u u' Rnorm-u =
 Rnorm-preserves-⟦⟧
  (B⟦ t ⟧ (xs ‚‚ u))
  (close ⌜ t ⌝ (Sub,, ys u'))
  (ƛ (close ⌜ t ⌝ (Subƛ ys)) · u')
  eq
  (Rnorm-lemma (xs ‚‚ u) (Sub,, ys u') t Rnorm-xs,,u)
 where
  eq : (A : type) → ⟦ close ⌜ t ⌝ (Sub,, ys u') ⟧₀ ＝[ 〖 B-type〖 _ 〗 A 〗 ] ⟦ ƛ (close ⌜ t ⌝ (Subƛ ys)) · u' ⟧₀
  eq A =
   ⟦ close ⌜ t ⌝ (Sub,, ys u') ⟧₀
    ＝⟨ ap (λ k → k ⟨⟩) (⟦close⟧ ⌜ t ⌝ (Sub,, ys u')) ⟩
   ⟦ ⌜ t ⌝ ⟧ (【Sub】 (Sub,, ys u') ⟨⟩)
    ＝⟨ ⟦⟧-eta ⌜ t ⌝ (【Sub】 (Sub,, ys u') ⟨⟩) (【Sub】 (Subƛ ys) (⟨⟩ ‚ ⟦ u' ⟧₀)) (＝【】-【Sub】-Sub,, ys u') ⟩
   ⟦ ⌜ t ⌝ ⟧ (【Sub】 (Subƛ ys) (⟨⟩ ‚ ⟦ u' ⟧₀))
    ＝⟨ ap (λ k → k (⟨⟩ ‚ ⟦ u' ⟧₀)) (⟦close⟧ ⌜ t ⌝ (Subƛ ys) ⁻¹) ⟩
   ⟦ ƛ (close ⌜ t ⌝ (Subƛ ys)) · u' ⟧₀
    ∎

  Rnorm-xs,,u : Rnorms (xs ‚‚ u) (Sub,, ys u')
  Rnorm-xs,,u (∈Cxt0 _)   = Rnorm-u
  Rnorm-xs,,u (∈CxtS _ i) = Rnorm-xs i

Rnorm-lemma xs ys (t · u) Rnorm-xs =
 Rnorm-lemma xs ys t Rnorm-xs (B⟦ u ⟧ xs) (close ⌜ u ⌝ ys) (Rnorm-lemma xs ys u Rnorm-xs)

＝【】-⟨⟩ : ＝【】 ⟨⟩ (【Sub】 (λ ()) ⟨⟩)
＝【】-⟨⟩ {τ} ()

-- a consequence of Rnorm-lemma for terms of type ι
Rnorm-lemmaι : (t : T₀ ι) (α : Baire)
             → dialogue⋆ ⟦ ⌜ t ⌝ ⟧₀ ＝ dialogue⋆ (church-encode B⟦ t ⟧₀)
Rnorm-lemmaι t α =
 dialogue⋆ ⟦ ⌜ t ⌝ ⟧₀
  ＝⟨ ap dialogue⋆ (⟦⟧-eta ⌜ t ⌝ ⟨⟩ (【Sub】 (λ ()) ⟨⟩) ＝【】-⟨⟩) ⟩
 dialogue⋆ (⟦ ⌜ t ⌝ ⟧ (【Sub】 (λ ()) ⟨⟩))
  ＝⟨ ap (λ k → dialogue⋆ (k ⟨⟩)) (⟦close⟧ ⌜ t ⌝ (λ ()) ⁻¹) ⟩
 dialogue⋆ ⟦ close ⌜ t ⌝ (λ ()) ⟧₀
  ＝⟨ Rnorm-lemma ⟪⟫ (λ ()) t (λ ()) ((ι ⇒ ι) ⇒ ι) η' β' ⟩
 dialogue⋆ (church-encode B⟦ t ⟧₀)
  ∎
 where
  η' : ℕ → (ℕ → ℕ) → ℕ
  η' = λ z α → z

  β' : (ℕ → (ℕ → ℕ) → ℕ) → ℕ → (ℕ → ℕ) → ℕ
  β' = λ φ x α → φ (α x) α

-- derived from Rnorm-lemma and main-lemma
R-main-lemma-ι : (t : T₀ ι)
                 (α : Baire)
               → R⋆ α ⟦ t ⟧₀ ⌜ t ⌝
R-main-lemma-ι t α =
 ⟦ t ⟧₀
  ＝⟨ main-lemma t α ⟨⟩ ⟪⟫ (λ ()) ⟩
 dialogue B⟦ t ⟧₀ α
  ＝⟨ dialogues-agreement B⟦ t ⟧₀ α ⟩
 dialogue⋆ (church-encode B⟦ t ⟧₀) α
  ＝⟨ ap (λ k → k α) ((Rnorm-lemmaι t α) ⁻¹) ⟩
 dialogue⋆ ⟦ ⌜ t ⌝ ⟧₀ α
  ∎

Rnorm-lemma₀ : {σ : type} (t : T₀ σ) → Rnorm B⟦ t ⟧₀ ⌜ t ⌝
Rnorm-lemma₀ {σ} t =
 Rnorm-preserves-⟦⟧
  B⟦ t ⟧₀ (close ⌜ t ⌝ (λ ())) ⌜ t ⌝
  (λ A → ap (λ k → k ⟨⟩) (⟦close⟧ ⌜ t ⌝ (λ ())) ∙ (⟦⟧-eta ⌜ t ⌝ ⟨⟩ (【Sub】 (λ ()) ⟨⟩) ＝【】-⟨⟩) ⁻¹) -- TODO: abstact that into a lemma
  (Rnorm-lemma ⟪⟫ (λ ()) t λ ())

Rnorm-generic : (u : B ℕ) (u' : {A : type} → T₀ (⌜B⌝ ι A))
              → is-dialogue-for u u'
              → is-dialogue-for (generic u) (⌜generic⌝ · u')
Rnorm-generic u u' ru =
 Rnorm-kleisli-lemma {!!} (β η) (⌜β⌝ · ⌜η⌝) c u u' ru
 where
  c : (x : ℕ) (x' : T₀ ι)
    → is-dialogue-for (η x) (⌜η⌝ · x')
    → β⋆ η⋆ ⟦ x' ⟧₀ ≣⋆ β⋆ η⋆ x
  c x x' rx A η' β' = ap (λ k → β⋆ η⋆ k η' β') (η⋆≣⋆ x x' rx)

⌜dialogue-tree⌝-correct : (t : T₀ ((ι ⇒ ι) ⇒ ι))
                          (α : Baire)
                        → ⟦ t ⟧₀ α ＝ dialogue⋆ ⟦ ⌜dialogue-tree⌝ t ⟧₀ α
⌜dialogue-tree⌝-correct t α =
 dialogue-tree-correct t α
 ∙ dialogues-agreement (dialogue-tree t) α
 ∙ ap (λ k → k α) (e ⁻¹)
 where
  η' : ℕ → Baire → ℕ
  η' = λ z i → z

  β' : (ℕ → Baire → ℕ) → ℕ → Baire → ℕ
  β' = λ φ x α → φ (α x) α

  rt : Rnorm B⟦ t ⟧₀ ⌜ t ⌝
  rt = Rnorm-lemma₀ {(ι ⇒ ι) ⇒ ι} t

  e : ⟦ ⌜ t ⌝ · ⌜generic⌝ ⟧₀ η' β' ＝ church-encode (B⟦ t ⟧₀ generic) η' β'
  e = rt generic ⌜generic⌝ Rnorm-generic ((ι ⇒ ι) ⇒ ι) η' β'

⌜dialogue⌝ : {Γ : Cxt}
           → T (B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι)) (⌜B⌝ ι ((ι ⇒ ι) ⇒ ι))
           → T (B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι)) ((ι ⇒ ι) ⇒ ι)
⌜dialogue⌝ {Γ} t = t · ƛ (ƛ ν₁) · ƛ (ƛ (ƛ (ν₂ · (ν₀ · ν₁) · ν₀)))

-- Same as ⌜dialogue-tree⌝-correct but using an internal dialogue function
⌜dialogue-tree⌝-correct' : (t : T₀ ((ι ⇒ ι) ⇒ ι))
                           (α : Baire)
                         → ⟦ t ⟧₀ α ＝ ⟦ ⌜dialogue⌝ (⌜dialogue-tree⌝ t) ⟧₀ α
⌜dialogue-tree⌝-correct' t α = ⌜dialogue-tree⌝-correct t α

-- Is that even provable? (we probably don't need it)
RnormAs : {σ : type} (d : B〖 σ 〗) (t : {A : type} → T₀ (B-type〖 σ 〗 A)) (α : Baire)
         → Rnorm d t ⇔ (Σ x ꞉ 〖 σ 〗 , ((R α x d) × (R⋆ α x t)))
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

\end{code}
