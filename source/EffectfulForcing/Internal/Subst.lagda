Martin Escardo, Vincent Rahli, Bruno da Rocha Paiva, Ayberk Tosun 20 May 2023

Substitution on System T terms, along with related results.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.Internal.Subst where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.SystemT using (type ; ι ; _⇒_ ; 〖_〗)
open import EffectfulForcing.Internal.Internal hiding (B⋆⟦_⟧ ; dialogue-tree⋆)
open import EffectfulForcing.Internal.SystemT
open import UF.Base using (transport₂ ; transport₃ ; ap₂ ; ap₃)
open import MGS.hlevels using (hedberg)
open import MGS.MLTT using (has-decidable-equality)


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

⊆, : (Γ : Cxt) (τ : type) → Γ ⊆ (Γ ,, τ)
⊆, Γ τ {σ} i = ∈CxtS τ i

-- 〈〉 is the smallest element w.r.t. the ⊆Γ order
⊆〈〉 : (Γ : Cxt) → 〈〉 ⊆ Γ
⊆〈〉 Γ {σ} ()

-- Removes a type from the context, using a "pointer" to the type (i)
rmCxt : {Γ : Cxt} {σ : type} (i : ∈Cxt σ Γ) → Cxt
rmCxt {Γ ,, σ} {σ} (∈Cxt0 Γ) = Γ
rmCxt {Γ ,, τ} {σ} (∈CxtS τ i) = rmCxt i ,, τ

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

Sub〈〉 : Sub₀ 〈〉
Sub〈〉 ()

close : {σ : type} {Γ₁ Γ₂ : Cxt} → T Γ₁ σ → Sub Γ₁ Γ₂ → T Γ₂ σ
close {_}       {Γ₁} {Γ₂} Zero        s = Zero
close {_}       {Γ₁} {Γ₂} (Succ t)    s = Succ (close t s)
close {_}       {Γ₁} {Γ₂} (Rec f g t) s = Rec (close f s) (close g s) (close t s)
close {σ}       {Γ₁} {Γ₂} (ν i)       s = s i
close {σ₁ ⇒ σ₂} {Γ₁} {Γ₂} (ƛ t)       s = ƛ (close t (Subƛ s))
close {σ}       {Γ₁} {Γ₂} (t₁ · t₂)   s = close t₁ s · close t₂ s

close0 : {σ τ : type} {Γ : Cxt} → T (Γ ,, τ) σ → T Γ τ → T Γ σ
close0 {σ} {τ} {Γ} t u = close {σ} {Γ ,, τ} {Γ} t (Sub1 u)

【Sub】 : {Γ Δ : Cxt} (s : Sub Γ Δ) → 【 Δ 】 → 【 Γ 】
【Sub】 {Γ} {Δ} s c {τ} i = ⟦ s i ⟧ c

【Sub₀】 : {Γ : Cxt} (s : Sub₀ Γ) → 【 Γ 】
【Sub₀】 {Γ} s = 【Sub】 s ⟨⟩

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
                           → ⌜Kleisli-extension⌝ {X} {A} {σ}
                          ＝ weaken s (⌜Kleisli-extension⌝ {X} {A} {σ})
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
                           → ⌜Kleisli-extension⌝ {X} {A} {σ}
                          ＝ close (⌜Kleisli-extension⌝ {X} {A} {σ}) s
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
      (e : ∈Cxt0 (B-context【 Γ 】 A)
        ＝ transport (λ Δ → ∈Cxt (B-type〖 σ 〗 A) (B-context【 Δ 】 A)) z (∈Cxt-B-type j))
    → ∈Cxt0 Γ ＝ transport (∈Cxt σ) z j
  p .(Γ ,, σ) (∈Cxt0 Γ) z e with ＝,, z
  ... | refl , e2 with ＝Cxt-refl z
  ... | refl = refl
  p .(Γ ,, τ) (∈CxtS τ j) refl ()
＝∈Cxt-B-type {Γ ,, τ} {A} {σ} (∈CxtS τ i) (∈CxtS τ j) e =
 ap (∈CxtS τ) (＝∈Cxt-B-type i j (＝∈CxtS _ _ _ e))

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
weaken-eta {Γ₁} {Γ₂} {σ}     s1 s2 (Rec t t₁ t₂) e =
 ap₃ Rec (weaken-eta s1 s2 t e) (weaken-eta s1 s2 t₁ e) (weaken-eta s1 s2 t₂ e)
weaken-eta {Γ₁} {Γ₂} {σ}     s1 s2 (ν i) e = ap ν (e i)
weaken-eta {Γ₁} {Γ₂} {σ ⇒ τ} s1 s2 (ƛ t) e =
 ap ƛ (weaken-eta (⊆,, σ s1) (⊆,, σ s2) t (＝⊆,, s1 s2 σ e))
weaken-eta {Γ₁} {Γ₂} {σ}     s1 s2 (t · t₁) e =
 ap₂ _·_ (weaken-eta s1 s2 t e) (weaken-eta s1 s2 t₁ e)

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
 ⌜rec⌝ · weaken (⊆-B-context {A} s) ⌜ t ⌝
       · weaken (⊆-B-context {A} s) ⌜ t₁ ⌝
       · weaken (⊆-B-context {A} s) ⌜ t₂ ⌝
  ＝⟨ ap (λ k → k · weaken (⊆-B-context {A} s) ⌜ t ⌝
                  · weaken (⊆-B-context {A} s) ⌜ t₁ ⌝
                  · weaken (⊆-B-context {A} s) ⌜ t₂ ⌝)
        (weaken-⌜rec⌝ _) ⟩
 weaken (⊆-B-context {A} s) ⌜rec⌝
 · weaken (⊆-B-context {A} s) ⌜ t ⌝
 · weaken (⊆-B-context {A} s) ⌜ t₁ ⌝
 · weaken (⊆-B-context {A} s) ⌜ t₂ ⌝
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
close-eta {Γ₁} {Γ₂} {σ}     s1 s2 (Rec t t₁ t₂) e =
 ap₃ Rec (close-eta s1 s2 t e) (close-eta s1 s2 t₁ e) (close-eta s1 s2 t₂ e)
close-eta {Γ₁} {Γ₂} {σ}     s1 s2 (ν i)         e = e i
close-eta {Γ₁} {Γ₂} {σ ⇒ τ} s1 s2 (ƛ t)         e =
 ap ƛ (close-eta (Subƛ s1) (Subƛ s2) t (＝Subƛ s1 s2 σ e))
close-eta {Γ₁} {Γ₂} {σ}     s1 s2 (t · t₁)      e =
 ap₂ _·_ (close-eta s1 s2 t e) (close-eta s1 s2 t₁ e)

-- close and ⌜ ⌝
⌜close⌝ : {A : type} {σ : type} {Γ : Cxt} (t : T Γ σ) {Δ : Cxt} (s : Sub Γ Δ)
        → close ⌜ t ⌝ (⌜Sub⌝ {A} s) ＝ ⌜ close t s ⌝
⌜close⌝ {A} {_}       {Γ} Zero          {Δ} s = refl
⌜close⌝ {A} {_}       {Γ} (Succ t)      {Δ} s = ap (λ k → ⌜succ⌝ · k) (⌜close⌝ t s)
⌜close⌝ {A} {_}       {Γ} (Rec t t₁ t₂) {Δ} s =
 close ⌜rec⌝ (⌜Sub⌝ {A} s)
 · close ⌜ t ⌝ (⌜Sub⌝ {A} s)
 · close ⌜ t₁ ⌝ (⌜Sub⌝ {A} s)
 · close ⌜ t₂ ⌝ (⌜Sub⌝ {A} s)
  ＝⟨ ap (λ k → k · close ⌜ t ⌝ (⌜Sub⌝ {A} s)
                  · close ⌜ t₁ ⌝ (⌜Sub⌝ {A} s)
                  · close ⌜ t₂ ⌝ (⌜Sub⌝ {A} s))
         ((close-⌜rec⌝ _) ⁻¹) ⟩
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

_≡_ : {A : type} (f g : 〖 A 〗) → Type
_≡_ {ι} f g = f ＝ g
_≡_ {σ ⇒ τ} f g = (a b : 〖 σ 〗) → a ≡ b → f a ≡ g b

≡T : (A : type) (f g : 〖 A 〗) → Type
≡T A f g = f ≡ g

syntax ≡T A f g = f ≡[ A ] g

≡rec-aux : {σ : type} {a₁ a₂ : 〖 ι ⇒ σ ⇒ σ 〗} {b₁ b₂ : 〖 σ 〗} {c : ℕ}
         → a₁ ≡ a₂
         → b₁ ≡ b₂
         → rec a₁ b₁ c ≡ rec a₂ b₂ c
≡rec-aux {σ} {a₁} {a₂} {b₁} {b₂} {zero} e₁ e₂ = e₂
≡rec-aux {σ} {a₁} {a₂} {b₁} {b₂} {succ c} e₁ e₂ =
 e₁ c c refl _ _ (≡rec-aux {σ} {a₁} {a₂} {b₁} {b₂} {c} e₁ e₂)

≡rec : {σ : type} {a₁ a₂ : 〖 ι ⇒ σ ⇒ σ 〗} {b₁ b₂ : 〖 σ 〗} {c₁ c₂ : ℕ}
      → a₁ ≡ a₂
      → b₁ ≡ b₂
      → c₁ ≡ c₂
      → rec a₁ b₁ c₁ ≡ rec a₂ b₂ c₂
≡rec {σ} {a₁} {a₂} {b₁} {b₂} {c₁} {.c₁} e₁ e₂ refl =
 ≡rec-aux {σ} {a₁} {a₂} {b₁} {b₂} {c₁} e₁ e₂

_【≡】_ : {Γ : Cxt} (a b : 【 Γ 】) → Type
_【≡】_ {Γ} a b = {σ : type} (i : ∈Cxt σ Γ) → a i ≡ b i

≡-refl : {Γ : Cxt} {σ : type} (t : T Γ σ) (u v : 【 Γ 】)
       → u 【≡】 v → ⟦ t ⟧ u ≡ ⟦ t ⟧ v
≡-refl {Γ} {.ι} Zero u v e = refl
≡-refl {Γ} {.ι} (Succ t) u v e = ap succ (≡-refl t u v e)
≡-refl {Γ} {σ} (Rec t t₁ t₂) u v e =
 ≡rec (≡-refl t u v e) (≡-refl t₁ u v e) (≡-refl t₂ u v e)
≡-refl {Γ} {σ} (ν i) u v e = e i
≡-refl {Γ} {σ ⇒ τ} (ƛ t) u v e a b k = ≡-refl t (u ‚ a) (v ‚ b) i
 where
  i : (u ‚ a) 【≡】 (v ‚ b)
  i {τ'} (∈Cxt0 .Γ) = k
  i {τ'} (∈CxtS .σ j) = e j
≡-refl {Γ} {σ} (t · t₁) u v e =
 ≡-refl t u v e (⟦ t₁ ⟧ u) (⟦ t₁ ⟧ v) (≡-refl t₁ u v e)

≡-refl₀ : {σ : type} (t : T₀ σ) → ⟦ t ⟧₀ ≡ ⟦ t ⟧₀
≡-refl₀ {σ} t = ≡-refl t ⟨⟩ ⟨⟩ (λ ())

≡-sym : {σ : type} {a b : 〖 σ 〗}
       → a ≡ b
       → b ≡ a
≡-sym {ι} {a} {.a} refl = refl
≡-sym {σ ⇒ τ} {a} {b} e a₁ a₂ a≡ =
 ≡-sym {τ} {a a₂} {b a₁} (e a₂ a₁ (≡-sym {σ} {a₁} {a₂} a≡))

≡-trans : {σ : type} {a b c : 〖 σ 〗}
         → a ≡ b
         → b ≡ c
         → a ≡ c
≡-trans {ι} {a} {.a} {c} refl e₂ = e₂
≡-trans {σ ⇒ τ} {a} {b} {c} e₁ e₂ a₁ a₂ a≡ =
 ≡-trans {τ} {a a₁} {b a₁} {c a₂}
         (e₁ a₁ a₁ (≡-trans {σ} {a₁} {a₂} {a₁} a≡ (≡-sym a≡)))
         (e₂ a₁ a₂ a≡)

≡ₗ : {σ : type} {a b : 〖 σ 〗}
       → a ≡ b
       → a ≡ a
≡ₗ {σ} {a} {b} e = ≡-trans e (≡-sym e)

≡ᵣ : {σ : type} {a b : 〖 σ 〗}
       → a ≡ b
       → b ≡ b
≡ᵣ {σ} {a} {b} e = ≡-trans (≡-sym e) e

【⊆】 : {Γ Δ : Cxt} (s : Γ ⊆ Δ) → 【 Δ 】 → 【 Γ 】
【⊆】 {Γ} {Δ} s c {τ} i = c (s i)

⟦weaken⟧ : {Γ Δ : Cxt} {σ : type} (t : T Γ σ) (s : Γ ⊆ Δ) (c : 【 Δ 】) (c' : 【 Γ 】)
           → (【⊆】 s c) 【≡】 c'
           → ⟦ weaken s t ⟧ c ≡ ⟦ t ⟧ c'
⟦weaken⟧ {Γ} {Δ} {_} Zero s c c' e = refl
⟦weaken⟧ {Γ} {Δ} {_} (Succ t) s c c' e = ap succ (⟦weaken⟧ t s c c' e)
⟦weaken⟧ {Γ} {Δ} {σ} (Rec t t₁ t₂) s c c' e =
 ≡rec (⟦weaken⟧ t s c c' e) (⟦weaken⟧ t₁ s c c' e) (⟦weaken⟧ t₂ s c c' e)
⟦weaken⟧ {Γ} {Δ} {σ} (ν i) s c c' e = e i
⟦weaken⟧ {Γ} {Δ} {σ ⇒ τ} (ƛ t) s c c' e a b x =
 ⟦weaken⟧ t (⊆,, σ s) (c ‚ a) (c' ‚ b) x'
 where
  x' : (【⊆】 (⊆,, σ s) (c ‚ a)) 【≡】 (c' ‚ b)
  x' {σ'} (∈Cxt0 .Γ) = x
  x' {σ'} (∈CxtS .σ i) = e i
⟦weaken⟧ {Γ} {Δ} {σ} (t · t₁) s c c' e =
 ⟦weaken⟧ t s c c' e _ _ (⟦weaken⟧ t₁ s c c' e)

⟦weaken,⟧ : {Γ : Cxt} {σ : type} (t : T Γ σ) (τ : type)
            (c' : 【 Γ ,, τ 】) (c'' : 【 Γ 】)
           → (【⊆】 (⊆, Γ τ) c') 【≡】 c''
           → ⟦ weaken, τ t ⟧ c' ≡ ⟦ t ⟧ c''
⟦weaken,⟧ {Γ} {σ} t τ c' c'' e = ⟦weaken⟧ t (⊆, Γ τ) c' c'' e

⟦weaken₀⟧ : {Γ : Cxt} {σ : type} (t : T₀ σ) (s : 【 Γ 】)
          → ⟦ weaken₀ t ⟧ s ≡ ⟦ t ⟧₀
⟦weaken₀⟧ {Γ} {σ} t s = ⟦weaken⟧ t (⊆〈〉 Γ) s ⟨⟩ (λ ())

【≡】-is-refl : {Γ : Cxt} (s : 【 Γ 】) → Type
【≡】-is-refl {Γ} s = s 【≡】 s

【≡】-is-refl‚ : {Γ : Cxt} (s : 【 Γ 】) {σ : type} (a : 〖 σ 〗)
              → 【≡】-is-refl s
              → a ≡ a
              → 【≡】-is-refl (s ‚ a)
【≡】-is-refl‚ {Γ} s {σ} a e₁ e₂ {.σ} (∈Cxt0 .Γ) = e₂
【≡】-is-refl‚ {Γ} s {σ} a e₁ e₂ {τ} (∈CxtS .σ i) = e₁ i

⟦close⟧ : {Γ Δ : Cxt} {σ : type} (t : T Γ σ) (s : Sub Γ Δ)
          (c : 【 Δ 】) (c' : 【 Γ 】) (r : 【≡】-is-refl c)
           → (【Sub】 s c) 【≡】 c'
           → ⟦ close t s ⟧ c ≡ ⟦ t ⟧ c'
⟦close⟧ {Γ} {Δ} Zero s c c' r e = refl
⟦close⟧ {Γ} {Δ} (Succ t) s c c' r e = ap succ (⟦close⟧ t s c c' r e)
⟦close⟧ {Γ} {Δ} (Rec t t₁ t₂) s c c' r e =
 ≡rec (⟦close⟧ t s c c' r e) (⟦close⟧ t₁ s c c' r e) (⟦close⟧ t₂ s c c' r e)
⟦close⟧ {Γ} {Δ} (ν i) s c c' r e = e i
⟦close⟧ {Γ} {Δ} {σ ⇒ τ} (ƛ t) s c c' r e a b z =
 ⟦close⟧ t (Subƛ s) (c ‚ a) (c' ‚ b) (【≡】-is-refl‚ c a r (≡ₗ z)) x
 where
  x : (【Sub】 (Subƛ s) (c ‚ a)) 【≡】 (c' ‚ b)
  x {σ'} (∈Cxt0 .Γ) = z
  x {σ'} (∈CxtS .σ i) = y
   where
    k : {τ' : type} (j : ∈Cxt τ' Δ) → c j ≡ c j
    k {τ'} j = r j

    y : ⟦ weaken, σ (s i) ⟧ (c ‚ a)  ≡ c' i
    y = ≡-trans (⟦weaken,⟧ (s i) σ (c ‚ a) c k) (e i)
⟦close⟧ {Γ} {Δ} (t · t₁) s c c' r e =
 ⟦close⟧ t s c c' r e _ _ (⟦close⟧ t₁ s c c' r e)

⟦close⟧' : {Γ : Cxt} {σ : type} (t : T Γ σ) (s : Sub₀ Γ)
           → ⟦ close t s ⟧₀ ≡ ⟦ t ⟧ (【Sub₀】 s)
⟦close⟧' {Γ} {σ} t s = ⟦close⟧ t s ⟨⟩ (【Sub₀】 s) (λ ()) x
 where
  x : (【Sub₀】 s) 【≡】 (【Sub₀】 s)
  x {τ} i = ≡-refl₀ (s i)

⟦closeν⟧ : {Γ : Cxt} {σ : type} (t : T Γ σ)
           (s : 【 Γ 】) (r : 【≡】-is-refl s)
         → ⟦ close t ν ⟧ s ≡ ⟦ t ⟧ s
⟦closeν⟧ {Γ} {σ} t s r = ⟦close⟧ t ν s s r r

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
       ∙ close-eta (⊆Sub (⊆,, σ s1) (Subƛ s2))
                   (Subƛ (⊆Sub s1 s2)) t
                   (＝Sub-⊆Sub-⊆,, s1 s2))
close-weaken {σ} {Γ₁} {Γ₂} {Γ₃} (t · t₁) s1 s2 =
 ap₂ _·_ (close-weaken t s1 s2) (close-weaken t₁ s1 s2)

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
       ∙ weaken-eta (⊆-trans (⊆,, σ s1) (⊆,, σ s2))
                    (⊆,, σ (⊆-trans s1 s2)) t
                    (＝⊆-⊆-trans-⊆,, s1 s2))
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
      ∙ weaken-eta (⊆-trans (∈CxtS σ) (⊆,, σ s2))
                   (⊆-trans s2 (∈CxtS σ))
                   (s1 i)
                   (＝⊆-⊆-trans-S-⊆,, s1 s2)
      ∙ weaken-weaken (s1 i) s2 (⊆, Γ₃ σ) ⁻¹

weaken-close : {σ : type} {Γ₁ Γ₂ Γ₃ : Cxt} (t : T Γ₁ σ)
               (s1 : Sub Γ₁ Γ₂) (s2 : Γ₂ ⊆ Γ₃)
              → weaken s2 (close t s1) ＝ close t (Sub⊆ s1 s2)
weaken-close {.ι} {Γ₁} {Γ₂} {Γ₃} Zero s1 s2 = refl
weaken-close {.ι} {Γ₁} {Γ₂} {Γ₃} (Succ t) s1 s2 = ap Succ (weaken-close t s1 s2)
weaken-close {σ} {Γ₁} {Γ₂} {Γ₃} (Rec t t₁ t₂) s1 s2 =
 ap₃ Rec (weaken-close t s1 s2) (weaken-close t₁ s1 s2) (weaken-close t₂ s1 s2)
weaken-close {σ} {Γ₁} {Γ₂} {Γ₃} (ν i) s1 s2 = refl
weaken-close {σ ⇒ τ} {Γ₁} {Γ₂} {Γ₃} (ƛ t) s1 s2 =
 ap ƛ (weaken-close t (Subƛ s1) (⊆,, σ s2)
       ∙ close-eta (Sub⊆ (Subƛ s1) (⊆,, σ s2)) (Subƛ (Sub⊆ s1 s2)) t (＝Sub-Sub⊆-Subƛ s1 s2))
weaken-close {σ} {Γ₁} {Γ₂} {Γ₃} (t · t₁) s1 s2 =
 ap₂ _·_ (weaken-close t s1 s2) (weaken-close t₁ s1 s2)

＝Sub-∘Sub-Subƛ : {Γ₁ Γ₂ Γ₃ : Cxt} {τ : type} (s1 : Sub Γ₁ Γ₂) (s2 : Sub Γ₂ Γ₃)
               → ＝Sub (Sub-trans (Subƛ {_} {_} {τ} s1) (Subƛ s2))
                       (Subƛ (Sub-trans s1 s2))
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
close-close {Γ₁} {Γ₂} {Γ₃} {σ} (Rec t t₁ t₂) s1 s2 =
 ap₃ Rec (close-close t s1 s2) (close-close t₁ s1 s2) (close-close t₂ s1 s2)
close-close {Γ₁} {Γ₂} {Γ₃} {σ} (ν i) s1 s2 = refl
close-close {Γ₁} {Γ₂} {Γ₃} {.(_ ⇒ _)} (ƛ t) s1 s2 =
 ap ƛ (close-close t (Subƛ s1) (Subƛ s2)
       ∙ close-eta (Sub-trans (Subƛ s1) (Subƛ s2))
                   (Subƛ (Sub-trans s1 s2)) t
                   (＝Sub-∘Sub-Subƛ s1 s2))
close-close {Γ₁} {Γ₂} {Γ₃} {σ} (t · t₁) s1 s2 =
 ap₂ _·_ (close-close t s1 s2) (close-close t₁ s1 s2)

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
close-refl {Γ} {σ} (Rec t t₁ t₂) =
 ap₃ Rec (close-refl t) (close-refl t₁) (close-refl t₂)
close-refl {Γ} {σ} (ν i) = refl
close-refl {Γ} {.(_ ⇒ _)} (ƛ t) =
 ap ƛ (close-eta (Subƛ ν) ν t ＝Sub-Subƛ-ν ∙ close-refl t)
close-refl {Γ} {σ} (t · t₁) =
 ap₂ _·_ (close-refl t) (close-refl t₁)

＝Sub-Sub,, : {Γ : Cxt} {σ τ : type} (y : T₀ σ) (ys : Sub₀ Γ)
            → ＝Sub (Sub,, ys y) (Sub-trans (Subƛ ys) (Sub1 y))
＝Sub-Sub,, {Γ} {σ} {τ} y ys {.σ} (∈Cxt0 .Γ) = refl
＝Sub-Sub,, {Γ} {σ} {τ} y ys {x} (∈CxtS .σ i) =
 close-refl (ys i) ⁻¹
 ∙ close-eta (⊆Sub (∈CxtS σ) (Sub1 y)) ν (ys i) (＝Subν y) ⁻¹
 ∙ (close-weaken (ys i) (⊆, 〈〉 σ) (Sub1 y)) ⁻¹

close-Sub,,-as-close-Subƛ : {Γ : Cxt} {σ τ : type}
                            (t : T (Γ ,, σ) τ)
                            (ys : Sub₀ Γ) (y : T₀ σ)
                          → close t (Sub,, ys y) ＝ close (close t (Subƛ ys)) (Sub1 y)
close-Sub,,-as-close-Subƛ {Γ} {σ} {τ} t ys y =
 close t (Sub,, ys y)
  ＝⟨ close-eta (Sub,, ys y) (Sub-trans (Subƛ ys) (Sub1 y)) t (＝Sub-Sub,, {Γ} {σ} {τ} y ys) ⟩
 close t (Sub-trans (Subƛ ys) (Sub1 y))
  ＝⟨ close-close t (Subƛ ys) (Sub1 y) ⁻¹ ⟩
 close (close t (Subƛ ys)) (Sub1 y)
  ∎

_≡⟨_⟩_ : {σ : type} (x : 〖 σ 〗) {y z : 〖 σ 〗} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = ≡-trans p q

_＝≡⟨_⟩_ : {σ : type} (x : 〖 σ 〗) {y z : 〖 σ 〗} → x ＝ y → y ≡ z → x ≡ z
_ ＝≡⟨ refl ⟩ q = q

_≡＝⟨_⟩_ : {σ : type} (x : 〖 σ 〗) {y z : 〖 σ 〗} → x ≡ y → y ＝ z → x ≡ z
_ ≡＝⟨ p ⟩ refl = p

infixr 0 _≡⟨_⟩_
infixr 0 _＝≡⟨_⟩_
infixr 0 _≡＝⟨_⟩_

⟦weaken,-weaken,⟧ : {Γ : Cxt} {σ₁ σ₂ τ : type}
                    (s : 【 Γ 】)
                    (y : 〖 σ₁ 〗) (z : 〖 σ₂ 〗)
                    (a : T Γ τ)
                  → y ≡ y
                  → 【≡】-is-refl s
                  → ⟦ weaken, σ₂ (weaken, σ₁ a) ⟧ (s ‚ y ‚ z)
                  ≡ ⟦ a ⟧ s
⟦weaken,-weaken,⟧ {Γ} {σ₁} {σ₂} {τ} s y z a ry rs =
 ⟦ weaken, σ₂ (weaken, σ₁ a) ⟧ (s ‚ y ‚ z)
  ≡⟨ ⟦weaken,⟧ (weaken, σ₁ a) σ₂ (s ‚ y ‚ z) (s ‚ y) e ⟩
 ⟦ weaken, σ₁ a ⟧ (s ‚ y)
  ≡＝⟨ ⟦weaken,⟧ a σ₁ (s ‚ y) s rs ⟩
 ⟦ a ⟧ s
  ∎
 where
  e : (【⊆】 (⊆, (Γ ,, σ₁) σ₂) (s ‚ y ‚ z)) 【≡】 (s ‚ y)
  e {τ} (∈Cxt0 .Γ) = ry
  e {τ} (∈CxtS .σ₁ i) = rs i

⟦weaken,-weaken,⟧-as-⟦weaken,⟧ : {Γ : Cxt} {σ τ : type}
                                 (s : 【 Γ 】)
                                 (x y z : 〖 σ 〗)
                                 (a : T Γ τ)
                               → y ≡ y
                               → 【≡】-is-refl s
                               → ⟦ weaken, σ (weaken, σ a) ⟧ (s ‚ y ‚ z)
                               ≡ ⟦ weaken, σ a ⟧ (s ‚ x)
⟦weaken,-weaken,⟧-as-⟦weaken,⟧ {Γ} {σ} {τ} s x y z a ry rs =
 ⟦ weaken, σ (weaken, σ a) ⟧ (s ‚ y ‚ z)
  ≡⟨ ⟦weaken,-weaken,⟧ s y z a ry rs ⟩
 ⟦ a ⟧ s
  ≡＝⟨ ≡-sym (⟦weaken,⟧ a σ (s ‚ x) s rs) ⟩
 ⟦ weaken, σ a ⟧ (s ‚ x)
  ∎

【≡】-trans : {Γ : Cxt} {a b c : 【 Γ 】} → a 【≡】 b → b 【≡】 c → a 【≡】 c
【≡】-trans {Γ} {a} {b} {c} e₁ e₂ {τ} i = ≡-trans (e₁ i) (e₂ i)

【≡】-sym : {Γ : Cxt} {a b : 【 Γ 】} → a 【≡】 b → b 【≡】 a
【≡】-sym {Γ} {a} {b} e {τ} i = ≡-sym (e i)

【≡】-is-refl-【Sub₀】 : {Γ : Cxt} (s : Sub₀ Γ) → 【≡】-is-refl (【Sub₀】 s)
【≡】-is-refl-【Sub₀】 {Γ} s {τ} i = ≡-refl (s i) ⟨⟩ ⟨⟩ (λ ())

【≡】-【sub】-⌜Sub⌝-Sub1 : {A : type} {σ : type} (y : T₀ σ)
                          → (【Sub₀】 (⌜Sub⌝ {A} (Sub1 y))) 【≡】 (⟨⟩ ‚ ⟦ ⌜ y ⌝ ⟧₀)
【≡】-【sub】-⌜Sub⌝-Sub1 {A} {σ} y {τ} i with ∈Cxt-B-context'' i
... | τ₁ , refl , ∈Cxt0 .〈〉 , refl = ≡-refl ⌜ y ⌝ _ _ (λ ())

【≡】-【Sub】-Sub,, : {Γ : Cxt} {σ : type} (ys : Sub₀ Γ) (u : T₀ σ)
                     → (【Sub】 (Sub,, ys u) ⟨⟩) 【≡】 (【Sub】 (Subƛ ys) (⟨⟩ ‚ ⟦ u ⟧₀))
【≡】-【Sub】-Sub,, {Γ} {σ} ys u {.σ} (∈Cxt0 .Γ) = ≡-refl u _ _ (λ ())
【≡】-【Sub】-Sub,, {Γ} {σ} ys u {τ} (∈CxtS .σ i) =
 ≡-sym (⟦weaken,⟧ (ys i) σ _ _ (λ ()))

【≡】-【Sub】-⊆Sub : {Γ : Cxt} (s : Sub₀ Γ)
                   → (【Sub】 (⊆Sub (∈CxtS ι) (Subƛ s)) (⟨⟩ ‚ zero)) 【≡】 (【Sub₀】 s)
【≡】-【Sub】-⊆Sub {Γ} s {σ} i = x
 where
  x : ⟦ weaken, ι (s i) ⟧ (⟨⟩ ‚ zero) ≡ ⟦ s i ⟧ ⟨⟩
  x = ⟦weaken,⟧ (s i) ι (⟨⟩ ‚ zero) ⟨⟩ (λ ())

【≡】-【Sub】-⊆Sub' : {Γ : Cxt} (s : Sub₀ Γ)
                   → 【≡】-is-refl (【Sub】 (⊆Sub (∈CxtS ι) (Subƛ s)) (⟨⟩ ‚ zero))
【≡】-【Sub】-⊆Sub' {Γ} s = 【≡】-trans (【≡】-【Sub】-⊆Sub s) (【≡】-sym (【≡】-【Sub】-⊆Sub s))

【≡】-【Sub】-Subƛ : {Γ : Cxt} {σ : type} (s : Sub₀ Γ) (a : 〖 σ 〗)
                   → a ≡ a
                   → 【≡】-is-refl (【Sub】 (Subƛ s) (⟨⟩ ‚ a))
【≡】-【Sub】-Subƛ {Γ} {σ} s a ra {.σ} (∈Cxt0 .Γ) = ra
【≡】-【Sub】-Subƛ {Γ} {σ} s a ra {τ} (∈CxtS .σ i) =
 ≡-refl (weaken, σ (s i)) _ _ (【≡】-is-refl‚ _ _ (λ ()) ra)

【≡】-【Sub】-Subƛ' : {Γ : Cxt} {σ τ : type} (s : Sub₀ Γ) (a : 〖 σ 〗) (b : 〖 τ 〗)
                    → a ≡ a
                    → b ≡ b
                    → 【≡】-is-refl (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ a ‚ b))
【≡】-【Sub】-Subƛ' {Γ} {σ} {τ} s a b ra rb {.τ} (∈Cxt0 .(Γ ,, σ)) = rb
【≡】-【Sub】-Subƛ' {Γ} {σ} {τ} s a b ra rb {.σ} (∈CxtS .τ (∈Cxt0 .Γ)) = ra
【≡】-【Sub】-Subƛ' {Γ} {σ} {τ} s a b ra rb {σ'} (∈CxtS .τ (∈CxtS .σ i)) =
 ≡-refl (weaken, τ (weaken, σ (s i))) _ _ (【≡】-is-refl‚ _ _ (【≡】-is-refl‚ _ _ (λ ()) ra) rb)

【≡】-【Sub】-Subƛ2 : {Γ : Cxt} {σ τ : type} (s : Sub₀ Γ) (a : 〖 σ 〗) (b : 〖 τ 〗)
                     → a ≡ a
                     → b ≡ b
                     → (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ a ‚ b)) 【≡】 (【Sub₀】 s ‚ a ‚ b)
【≡】-【Sub】-Subƛ2 {Γ} {σ} {τ} s a b ea eb {.τ} (∈Cxt0 .(Γ ,, σ)) = eb
【≡】-【Sub】-Subƛ2 {Γ} {σ} {τ} s a b ea eb {.σ} (∈CxtS .τ (∈Cxt0 .Γ)) = ea
【≡】-【Sub】-Subƛ2 {Γ} {σ} {τ} s a b ea eb {x} (∈CxtS .τ (∈CxtS .σ i)) =
 ⟦weaken,-weaken,⟧ ⟨⟩ a b (s i) ea λ ()

【≡】-is-refl-【⊆】-⊆,-【Sub】-Subƛ : {Γ : Cxt} {σ : type} (s : Sub₀ Γ) (a : 〖 σ 〗)
                                  → a ≡ a
                                  → 【≡】-is-refl (【⊆】 (⊆, Γ σ) (【Sub】 (Subƛ s) (⟨⟩ ‚ a)))
【≡】-is-refl-【⊆】-⊆,-【Sub】-Subƛ {Γ} {σ} s a ea {τ} i =
 ≡-refl (weaken, σ (s i)) (⟨⟩ ‚ a) (⟨⟩ ‚ a) (【≡】-is-refl‚ _ _ (λ ()) ea)

\end{code}
