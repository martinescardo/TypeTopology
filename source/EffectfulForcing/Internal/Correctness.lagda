Martin Escardo, Vincent Rahli, Bruno da Rocha Paiva, Ayberk Tosun 20 May 2023

We prove the correctness of the internal translation.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module EffectfulForcing.Internal.Correctness where

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
open import EffectfulForcing.Internal.LambdaWithoutOracle
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.Internal.Subst
open import UF.Base using (transport₂ ; transport₃ ; ap₂ ; ap₃)

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

\begin{code}

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

-- internal semantics of contexts as dialogue trees
IB【_】 : Cxt → type → Type
IB【 Γ 】 A = Sub₀ (B-context【 Γ 】 A)

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

⟦⌜Kleisli-extension⌝⟧ : {X A σ : type} {Γ Δ : Cxt} (xs : 【 Γ 】) (ys : 【 Δ 】)
                      → ⟦ ⌜Kleisli-extension⌝ {X} {A} {σ} ⟧ xs
                      ≡ ⟦ ⌜Kleisli-extension⌝ {X} {A} {σ} ⟧ ys
⟦⌜Kleisli-extension⌝⟧ {X} {A} {ι} {Γ} {Δ} xs ys a b a≡ f g f≡ u v u≡ x y x≡ =
 f≡ (λ x₁ → a x₁ u x) (λ x₁ → b x₁ v y) (λ a₁ b₁ z → a≡ a₁ b₁ z u v u≡ x y x≡) x y x≡ --refl
⟦⌜Kleisli-extension⌝⟧ {X} {A} {σ ⇒ τ} {Γ} {Δ} xs ys a b a≡ f g f≡ u v u≡ =
 ⟦⌜Kleisli-extension⌝⟧ (xs ‚ a ‚ f ‚ u) (ys ‚ b ‚ g ‚ v) (λ x → a x u) (λ x → b x v) (λ a₁ b₁ z → a≡ a₁ b₁ z u v u≡) f g f≡

≡η⋆ : {σ σ₁ σ₂ σ₃ : type} {a b : 〖 σ 〗}
    → a ≡ b
    → η⋆ {_} {_} {_} {_} {〖 σ₁ 〗} {〖 σ₂ 〗} {〖 σ 〗} {〖 σ₃ 〗} a ≡ η⋆ b
≡η⋆ {σ} {σ₁} {σ₂} {σ₃} {a} {b} e a₁ b₁ a≡₁ a₂ b₂ a≡₂ = a≡₁ _ _ e

⟦⌜Rec⌝⟧-aux : {A : type} {σ : type} {Γ : Cxt} (s : 【 B-context【 Γ 】 A 】) (a : T Γ (ι ⇒ σ ⇒ σ)) (b : T Γ σ)
              (a₁ b₁ : ℕ)
            → a₁ ＝ b₁
            → 【≡】-is-refl s
            → rec (λ y → ⟦ ⌜ a ⌝ ⟧ s (η⋆ y)) (⟦ ⌜ b ⌝ ⟧ s) a₁
            ≡ rec (λ y → ⟦ weaken, ι (weaken, ι ⌜ a ⌝) ⟧ (s ‚ b₁ ‚ y) (η⋆ y)) (⟦ weaken, ι ⌜ b ⌝ ⟧ (s ‚ b₁)) b₁
⟦⌜Rec⌝⟧-aux {A} {σ} {Γ} s a b a₁ b₁ a≡₁ r =
 ≡rec
  {_} {λ y → ⟦ ⌜ a ⌝ ⟧ s (η⋆ y)} {λ y → ⟦ weaken, ι (weaken, ι ⌜ a ⌝) ⟧ (s ‚ b₁ ‚ y) (η⋆ y)}
  {⟦ ⌜ b ⌝ ⟧ s} {⟦ weaken, ι ⌜ b ⌝ ⟧ (s ‚ b₁)} {a₁} {b₁}
  c (≡-sym (⟦weaken,⟧ ⌜ b ⌝ ι (s ‚ b₁) s r)) a≡₁
 where
  c : (a₂ b₂ : ℕ)
    → a₂ ＝ b₂
    → (a₃ b₃ : 〖 B-type〖 σ 〗 A 〗)
    → a₃ ≡ b₃
    → ⟦ ⌜ a ⌝ ⟧ s (η⋆ a₂) a₃
    ≡ ⟦ weaken, ι (weaken, ι ⌜ a ⌝) ⟧ (s ‚ b₁ ‚ b₂) (η⋆ b₂) b₃
  c a₂ b₂ a≡₂ a₃ b₃ a≡₃ =
   ≡-sym (⟦weaken,-weaken,⟧ s b₁ b₂ ⌜ a ⌝ refl r (η⋆ b₂) (η⋆ a₂) (≡η⋆ (≡-sym a≡₂)) b₃ a₃ (≡-sym a≡₃))

⟦⌜Rec⌝⟧ : {A : type} {σ : type} {Γ : Cxt} (s : 【 B-context【 Γ 】 A 】) (a : T Γ (ι ⇒ σ ⇒ σ)) (b : T Γ σ) (c : T Γ ι)
        → 【≡】-is-refl s
        → ⟦ ⌜_⌝  {Γ} {σ} {A} (Rec a b c) ⟧ s
        ≡ ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
            · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀))
            · ⌜ c ⌝ ⟧ s
⟦⌜Rec⌝⟧ {A} {σ} {Γ} s a b c r =
 ⟦ ⌜_⌝  {Γ} {σ} {A} (Rec a b c) ⟧ s
  ＝≡⟨ refl ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ} ⟧ (s ‚ ⟦ ⌜ a ⌝ ⟧ s ‚ ⟦ ⌜ b ⌝ ⟧ s)
  (λ x → rec (λ y → ⟦ ⌜ a ⌝ ⟧ s (η⋆ y)) (⟦ ⌜ b ⌝ ⟧ s) x)
  (⟦ ⌜ c ⌝ ⟧ s)
  ≡＝⟨ ⟦⌜Kleisli-extension⌝⟧ (s ‚ ⟦ ⌜ a ⌝ ⟧ s ‚ ⟦ ⌜ b ⌝ ⟧ s) s
       (λ x → rec (λ y → ⟦ ⌜ a ⌝ ⟧ s (η⋆ y)) (⟦ ⌜ b ⌝ ⟧ s) x)
       (λ x → rec (λ y → ⟦ weaken, ι (weaken, ι ⌜ a ⌝) ⟧ (s ‚ x ‚ y) (η⋆ y)) (⟦ weaken, ι ⌜ b ⌝ ⟧ (s ‚ x)) x)
       (λ a₁ b₁ a≡ → ⟦⌜Rec⌝⟧-aux s a b a₁ b₁ a≡ r)
       (⟦ ⌜ c ⌝ ⟧ s) (⟦ ⌜ c ⌝ ⟧ s) (≡-refl ⌜ c ⌝ s s r) ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ} · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) · ⌜ c ⌝ ⟧ s
  ∎

⟦close-⌜Rec⌝⟧ : {A : type} {σ : type} {Γ : Cxt} (s : IB【 Γ 】 A) (a : T Γ (ι ⇒ σ ⇒ σ)) (b : T Γ σ) (c : T Γ ι)
              → ⟦ close (⌜_⌝  {Γ} {σ} {A} (Rec a b c)) s ⟧₀
              ≡ ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
                   · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s
                   · close ⌜ c ⌝ s ⟧₀
⟦close-⌜Rec⌝⟧ {A} {σ} {Γ} s a b c =
 ⟦ close (⌜_⌝  {Γ} {σ} {A} (Rec a b c)) s ⟧₀
  ≡⟨ ⟦close⟧' ⌜ Rec a b c ⌝ s ⟩
 ⟦ ⌜_⌝  {Γ} {σ} {A} (Rec a b c) ⟧ (【Sub₀】 s)
  ≡⟨ ⟦⌜Rec⌝⟧ (【Sub₀】 s) a b c (【≡】-is-refl-【Sub₀】 s) ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
   · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀))
   · ⌜ c ⌝ ⟧ (【Sub₀】 s)
  ≡＝⟨ ≡-sym (⟦close⟧' (⌜Kleisli-extension⌝ {ι} {A} {σ} · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) · ⌜ c ⌝) s) ⟩
 ⟦ close ⌜Kleisli-extension⌝ s
   · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s
   · close ⌜ c ⌝ s ⟧₀
  ＝⟨ ap (λ k → ⟦ k · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s · close ⌜ c ⌝ s ⟧₀)
         ((close-⌜Kleisli-extension⌝ s) ⁻¹) ⟩
 ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
   · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s
   · close ⌜ c ⌝ s ⟧₀
  ∎

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

⌜η⌝ℕ→T≡ : {X Y A : type} (n : ℕ) → ⟦ ⌜η⌝ {X} {Y} {ι} {A} · ℕ→T n ⟧₀ ≡ η⋆ n
⌜η⌝ℕ→T≡ {X} {Y} {A} n = ≡η⋆ {_} {_} {_} {_} {⟦ ℕ→T n ⟧₀} {n} (⟦ℕ→T⟧ n)

\end{code}

TODO. move results about substitution to Internal.lagda and move this
to either Internal.lagda or a new file.

Using a logical relation we show that the the internal, church-encoded dialogue
translation of a System T term coincides with its external, inductive dialogue
translation.

From this result and the main-lemma we can derive an internal result of
strong continuity in System T.

\begin{code}

extβ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : type} (β' : (Y → 〖 A 〗) → X → 〖 A 〗) → 𝓤 ⊔ 𝓥  ̇
extβ {_} {_} {X} {Y} {A} β' =
 (f g : Y → 〖 A 〗) (x y : X)
 → x ＝ y
 → ((y : Y) → f y ≡ g y)
 → β' f x ≡ β' g y

extη : {X : 𝓤 ̇ } {A : type} (η' : X → 〖 A 〗) → 𝓤 ̇
extη {_} {X} {A} η' = (n : X) → η' n ≡ η' n

extβℕ : {A : type} {β' : (ℕ → 〖 A 〗) → ℕ → 〖 A 〗} → extβ β'
      → (a b : ℕ → 〖 A 〗)
      → ((a₁ b₁ : ℕ) → a₁ ＝ b₁ → a a₁ ≡ b b₁)
      → (a₁ b₁ : ℕ) → a₁ ＝ b₁ → β' a a₁ ≡ β' b b₁
extβℕ {A} {β'} eβ a b a≡ a₁ b₁ a≡₁ = eβ a b a₁ b₁ a≡₁ (λ y → a≡ y y refl)

extηℕ : {A : type} {η' : ℕ → 〖 A 〗} → extη η' → (a b : ℕ) → a ＝ b → η' a ≡ η' b
extηℕ {A} {η'} eη a .a refl = eη a

_≣⋆_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
      → ({A : type} → D⋆ X Y Z 〖 A 〗) → ({A : type } → D⋆ X Y Z 〖 A 〗) → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
_≣⋆_ {_} {_} {_} {X} {Y} {Z} d d' =
 (A : type) (η' : Z → 〖 A 〗) (β' : (Y → 〖 A 〗) → X → 〖 A 〗)
 → extη η'
 → extβ β'
 → d η' β' ≡ d' η' β'

≣⋆-symm : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {d d' : {A : type} → D⋆ X Y Z 〖 A 〗}
        → d ≣⋆ d' → d' ≣⋆ d
≣⋆-symm eq A η' β' eη eβ = ≡-sym (eq A η' β' eη eβ)

≣⋆-trans : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {d d' d'' : {A : type} → D⋆ X Y Z 〖 A 〗}
          → d ≣⋆ d' → d' ≣⋆ d'' → d ≣⋆ d''
≣⋆-trans eq eq' A η' β' eη eβ = ≡-trans (eq A η' β' eη eβ) (eq' A η' β' eη eβ)

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
                   → ((A : type) →  ⟦ t {A} ⟧₀ ≡ ⟦ u {A} ⟧₀)
                   → Rnorm d t
                   → Rnorm d u
Rnorm-preserves-⟦⟧ {ι} d t u t≡u eq A η' β' eη eβ =
 ≡-trans (≡-sym (t≡u _ _ _ (extηℕ eη) _ _ (extβℕ eβ))) (eq _ _ _ eη eβ)
Rnorm-preserves-⟦⟧ {σ ⇒ τ} d t u t≡u Rnorm-t v v' Rnorm-v =
 Rnorm-preserves-⟦⟧
  (d v) (t · v') (u · v')
  (λ A → t≡u A _ _ (≡-refl₀ v'))
  (Rnorm-t v v' Rnorm-v)

\end{code}

As Rnorm quantifies over all System T types, we can elimate a family of
church-encoded trees into different types, allowing us to reify terms into
the shape of ⌜η⌝ or ⌜β⌝.

This sort of reification is crucial when we need to pattern match on the
constructor of a church-encoded tree.

\begin{code}

extη-id : extη {_} {ℕ} {ι} (λ x → x)
extη-id n = refl

extβ-id : extβ {_} {_} {ℕ} {ℕ} {ι} (λ x → x)
extβ-id f g x .x refl f≡ = f≡ x

Rnormη : (n : ℕ) → Rnorm (η n) (⌜η⌝ · ℕ→T n)
Rnormη n A η' β' eη eβ = ⌜η⌝ℕ→T≡ n η' η' (extηℕ eη) β' β' (extβℕ eβ)

Rnormη⌜η⌝ : (n : ℕ) (n' : T₀ ι) → Rnorm (η n) (⌜η⌝ · n') → ⟦ n' ⟧₀ ＝ ⟦ ℕ→T n ⟧₀
Rnormη⌜η⌝ n n' rn = rn ι (λ x → x) (λ x → x) extη-id extβ-id ∙ ⟦ℕ→T⟧ n ⁻¹

Rnorm-reify-η : (n : ℕ) (t : {A : type} → T₀ (⌜B⌝ ι A))
              → Rnorm (η n) t
              → ⟦ t ⟧₀ ≣⋆ ⟦ ⌜η⌝ · ℕ→T n ⟧₀ × Rnorm (η n) (⌜η⌝ · ℕ→T n)
Rnorm-reify-η n t eq =
 ≣⋆-trans eq (≣⋆-symm (Rnormη n)) ,
 Rnormη n

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
⟦B-branch⟧ ϕ i n t h A η' β' eη eβ =
 ⟦ B-branch t ⟧₀ i η' β'
  ≡⟨ ⟦weaken₀⟧ (t {((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A}) (⟨⟩ ‚ i ‚ η' ‚ β') η₀ η₀ η₀≡ β₀ β₀ β₀≡ h₀ h₀ h₀≡ ⟩
 ⟦ t {((ι ⇒ A) ⇒ (ι ⇒ A)) ⇒ A} ⟧₀ η₀ β₀ h₀
  ≡⟨ h (((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A) η₀ β₀ extη₀ extβ₀ h₀ h₀ exth₀ ⟩
 church-encode (β ϕ n) η₀ β₀ h₀
  ≡＝⟨ q (ϕ i) ⟩
 church-encode (ϕ i) η' β'
  ∎
 where
  η₀ : 〖 ι ⇒ ((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A 〗
  η₀ = λ n → λ k → η' n

  β₀ : 〖 (ι ⇒ ((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A) ⇒ ι ⇒ ((ι ⇒ A) ⇒ ι ⇒ A) ⇒ A 〗
  β₀ = λ g → λ n → λ h → h (λ j → g j β') n

  h₀ : 〖 (ι ⇒ A) ⇒ ι ⇒ A 〗
  h₀ = λ k → λ n → k i

  η₀≡ : η₀ ≡ η₀
  η₀≡ a .a refl a₁ b₁ a≡₁ = eη a

  β₀≡ : β₀ ≡ β₀
  β₀≡ a b a≡ a₁ .a₁ refl a₂ b₂ a≡₂ = a≡₂ _ _ (λ a₃ b₃ a≡₃ → a≡ a₃ b₃ a≡₃ β' β' (extβℕ eβ)) _ _ refl

  h₀≡ : h₀ ≡ h₀
  h₀≡ a b a≡ a₁ b₁ a≡₁ = a≡ _ _ refl

  extη₀ : extη η₀
  extη₀ n a b a≡ = eη n

  extβ₀ : extβ β₀
  extβ₀ f g x y x≡ f≡ a b a≡ = a≡ _ _ f≡g _ _ x≡
   where
    f≡g : (a₁ b₁ : ℕ) → a₁ ＝ b₁ → f a₁ β' ≡ g b₁ β'
    f≡g a₁ .a₁ refl = f≡ a₁ _ _ β≡
     where
      β≡ : (a₂ b₁ : ℕ → 〖 A 〗) → ((a₃ b₂ : ℕ) → a₃ ＝ b₂ → a₂ a₃ ≡ b₁ b₂) → (a₃ b₂ : ℕ) → a₃ ＝ b₂ → β' a₂ a₃ ≡ β' b₁ b₂
      β≡ a₂ b₂ a≡₂ a₃ .a₃ refl = eβ _ _ _ _ refl (λ y → a≡₂ y y refl)

  exth₀ : (a b : ℕ → 〖 A 〗) → ((a₁ b₁ : ℕ) → a₁ ＝ b₁ → a a₁ ≡ b b₁)
        → (a₁ b₁ : ℕ) → a₁ ＝ b₁ → a i ≡ b i
  exth₀ a b e a₁ b₁ a≡ = e i i refl

  q : (d : B ℕ) → church-encode d η₀ β₀ β' ≡ church-encode d η' β'
  q (η x) = eη x
  q (β ψ y) = eβ _ _ _ _ refl (λ j → q (ψ j))

η⋆≣⋆ : (x : ℕ) (x' : T₀ ι) → η⋆ {_} {_} {_} {_} {ℕ} {ℕ} ⟦ x' ⟧₀ ≣⋆ η⋆ x → ⟦ x' ⟧₀ ≡ x
η⋆≣⋆ x x' h = h ι (λ z → z) (λ z → z) extη-id extβ-id

Rnorm-reify-β : (ϕ : ℕ → B ℕ) (n : ℕ) (t : {A : type} → T₀ (⌜B⌝ ι A))
                → Rnorm (β ϕ n) t
                → Σ ϕ' ꞉ ({A : type} → T₀ (ι ⇒ ⌜B⌝ ι A))
                , Σ n' ꞉ T₀ ι
                , ⟦ t ⟧₀ ≣⋆ ⟦ ⌜β⌝ · ϕ' · n' ⟧₀
                × Rnorm (β ϕ n) (⌜β⌝ · ϕ' · n')
                × (⟦ n' ⟧₀ ≡ n)
                × ((x : ℕ) → Rnorm (ϕ x) (ϕ' · ℕ→T x))
Rnorm-reify-β ϕ n t eq = ϕ' , n' , eq' , rβ , ⟦ℕ→T⟧ n , rϕ
 where
  -- We get the branching at t with the following
  ϕ' : {A : type} → T₀ (ι ⇒ ⌜B⌝ ι A)
  ϕ' {A} = B-branch t

  -- We get the oracle query at t with the following
  n' : T₀ ι
  n' = ℕ→T n

  eq' : ⟦ t ⟧₀ ≣⋆ ⟦ ⌜β⌝ · ϕ' · n' ⟧₀
  eq' A η' β' eη eβ =
   ⟦ t ⟧₀ η' β'
    ≡⟨ eq A η' β' eη eβ ⟩
   β' (λ y → church-encode (ϕ y) η' β') n
    ≡＝⟨ eβ _ _ _ _ ((⟦ℕ→T⟧ n) ⁻¹) (λ y → ≡-sym (⟦B-branch⟧ ϕ y n t eq A η' β' eη eβ)) ⟩
   ⟦ ⌜β⌝ · ϕ' · n' ⟧₀ η' β'
    ∎

  rβ : Rnorm (β ϕ n) (⌜β⌝ · ϕ' · n')
  rβ = ≣⋆-trans (≣⋆-symm eq') eq

  rϕ : (x : ℕ) → ⟦ B-branch t ⟧₀ ⟦ ℕ→T x ⟧₀ ≣⋆ church-encode (ϕ x)
  rϕ x = transport (λ k → ⟦ B-branch t ⟧₀ k ≣⋆ church-encode (ϕ x)) (⟦ℕ→T⟧ x ⁻¹) (⟦B-branch⟧ ϕ x n t eq)

-- TODO: can we generalize this?
church-encode-kleisli-extension : {A : type} (η' : ℕ → 〖 A 〗) (β' : (ℕ → 〖 A 〗) → ℕ → 〖 A 〗) (d : B ℕ)
                                → extη η'
                                → extβ β'
                                → (f : ℕ → B ℕ) (f' : {A : type} → T₀ (ι ⇒ ⌜B⌝ ι A))
                                → ((x : ℕ) → Rnorm (f x) (f' · ℕ→T x))
                                → church-encode (kleisli-extension f d) η' β'
                                ≡ kleisli-extension⋆ ⟦ f' ⟧₀ (church-encode d) η' β'
church-encode-kleisli-extension {A} η' β' (η x) eη eβ f f' rf =
 church-encode (f x) η' β'
  ≡⟨ ≡-sym (rf x A η' β' eη eβ) ⟩
 ⟦ f' · ℕ→T x ⟧₀ η' β'
  ≡＝⟨ ≡-refl₀ f' _ _ (⟦ℕ→T⟧ x) _ _ (extηℕ eη) _ _ (extβℕ eβ) ⟩
 ⟦ f' ⟧₀ x η' β'
  ∎
church-encode-kleisli-extension {A} η' β' (β g y) eη eβ f f' rf =
 church-encode (β (λ j → kleisli-extension f (g j)) y) η' β'
  ≡＝⟨ eβ _ _ _ _ refl (λ y → church-encode-kleisli-extension {A} η' β' (g y) eη eβ f f' rf) ⟩
 church-encode (β g y) (λ z → ⟦ f' ⟧₀ z η' β') β'
  ∎

-- Since rec is interpreted using ⌜Kleisli-extension⌝, we need to know that
-- ⌜Kleisli-extension⌝ preserves this normalisation property.
-- TODO is it enough to get a context free kleisli lemma
Rnorm-kleisli-lemma : {σ : type}

                      (f : ℕ → B〖 σ 〗)
                      (f' : {A : type} → T₀ (ι ⇒ B-type〖 σ 〗 A))
                    → ((x : ℕ) → Rnorm (f x) (f' · ℕ→T x))

                    → (n : B ℕ)
                      (n' : {A : type} → T₀ (⌜B⌝ ι A))
                    → Rnorm {ι} n n'

                    → Rnorm (Kleisli-extension f n) (⌜Kleisli-extension⌝ · f' · n')
Rnorm-kleisli-lemma {ι} f f' rf (η y) n' rn A η' β' eη eβ =
 ⟦ n' ⟧₀ (λ x → ⟦ f' ⟧₀ x η' β') β'
  ≡⟨ rn A (λ x → ⟦ f' ⟧₀ x η' β') β' (λ x → ≡-refl₀ f' _ _ refl _ _ (extηℕ eη) _ _ (extβℕ eβ)) eβ ⟩
 ⟦ f' ⟧₀ y η' β'
  ≡⟨ ≡-refl₀ f' _ _ (⟦ℕ→T⟧ y ⁻¹) _ _ (extηℕ eη) _ _ (extβℕ eβ) ⟩
 ⟦ f' · ℕ→T y ⟧₀ η' β'
  ≡＝⟨ rf y A η' β' eη eβ ⟩
 church-encode (f y) η' β'
  ∎
Rnorm-kleisli-lemma {ι} f f' rf (β ϕ y) n' rn A η' β' eη eβ with Rnorm-reify-β ϕ y n' rn
... | (ϕ' , y' , eq , rb , ry , rϕ) =
 ⟦ n' ⟧₀ (λ x → ⟦ f' ⟧₀ x η' β') β'
  ≡⟨ eq A (λ x → ⟦ f' ⟧₀ x η' β') β' (λ x → ≡-refl₀ f' _ _ refl _ _ (extηℕ eη) _ _ (extβℕ eβ)) eβ ⟩
 β' (λ x → ⟦ ϕ' ⟧₀ x (λ z → ⟦ f' ⟧₀ z η' β') β') ⟦ y' ⟧₀
  ≡⟨ eβ _ _ _ _ ry (λ y → ≡-sym (≡-refl₀ ϕ' _ _ (⟦ℕ→T⟧ y) _ _ (λ a b e → ≡-refl₀ f' _ _ e _ _ (extηℕ eη) _ _ (extβℕ eβ)) _ _ (extβℕ eβ))) ⟩
 β' (λ x → ⟦ ϕ' · ℕ→T x ⟧₀ (λ z → ⟦ f' ⟧₀ z η' β') β') y
  ≡⟨ eβ _ _ _ _ refl (λ x → rϕ x A (λ z → ⟦ f' ⟧₀ z η' β') β' (λ x → ≡-refl₀ f' _ _ refl _ _ (extηℕ eη) _ _ (extβℕ eβ)) eβ) ⟩
 β' (λ x → church-encode (ϕ x) (λ z → ⟦ f' ⟧₀ z η' β') β') y
  ≡＝⟨ eβ _ _ _ _ refl (λ x → ≡-sym (church-encode-kleisli-extension η' β' (ϕ x) eη eβ f f' rf)) ⟩
 β' (λ x → church-encode (kleisli-extension f (ϕ x)) η' β') y
  ∎
Rnorm-kleisli-lemma {σ ⇒ τ} f f' rf n n' rn A η' β' =
 Rnorm-preserves-⟦⟧ (Kleisli-extension (λ x → f x A) n)
   (⌜Kleisli-extension⌝ · ƛ (weaken₀ f' · ν₀ · weaken₀ η') · n')
   (ƛ (ƛ (ƛ (⌜Kleisli-extension⌝ · ƛ (ν₃ · ν₀ · ν₁) · ν₁))) · f' · n' · η')
   e
   (Rnorm-kleisli-lemma (λ x → f x A)
     (ƛ (weaken₀ f' · ν₀ · weaken₀ η'))
     rf'
     n n' rn)
 where
  e : (A : type)
    → ⟦ ⌜Kleisli-extension⌝ · ƛ (weaken₀ f' · ν₀ · weaken₀ η') · n' ⟧₀
    ≡ ⟦ ƛ (ƛ (ƛ (⌜Kleisli-extension⌝ · ƛ (ν₃ · ν₀ · ν₁) · ν₁))) · f' · n' · η' ⟧₀
  e A =
   ⟦ ⌜Kleisli-extension⌝ · ƛ (weaken₀ f' · ν₀ · weaken₀ η') · n' ⟧₀
    ≡＝⟨ ⟦⌜Kleisli-extension⌝⟧
          ⟨⟩ (⟨⟩ ‚ ⟦ f' ⟧₀ ‚ ⟦ n' ⟧₀ ‚ ⟦ η' ⟧₀)
          _ _ (λ a b a≡ → ⟦weaken₀⟧ f' (⟨⟩ ‚ a) _ _ a≡ _ _ (⟦weaken₀⟧ η' (⟨⟩ ‚ a)))
          _ _ (λ a b a≡ a₁ b₁ a≡₁ → ≡-refl₀ n' _ _ a≡ _ _ a≡₁) ⟩
   ⟦ ƛ (ƛ (ƛ (⌜Kleisli-extension⌝ · ƛ (ν₃ · ν₀ · ν₁) · ν₁))) · f' · n' · η' ⟧₀
    ∎

  rf' : (x : ℕ) → Rnorm (f x A) (ƛ (weaken₀ f' · ν₀ · weaken₀ η') · ℕ→T x)
  rf' x =
   Rnorm-preserves-⟦⟧ (f x A)
    (f' · ℕ→T x · η')
    (ƛ (weaken₀ f' · ν₀ · weaken₀ η') · ℕ→T x)
    (λ A → ≡-sym (⟦weaken₀⟧ f' (⟨⟩ ‚ ⟦ ℕ→T x ⟧₀) _ _ refl _ _ (⟦weaken₀⟧ η' (⟨⟩ ‚ ⟦ ℕ→T x ⟧₀))))
    (rf x A η' β')

church-encode-is-natural : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (g : X → Y) (d : B X)
                         → B⋆-functor g (church-encode d) ≣⋆ church-encode (B-functor g d)
church-encode-is-natural g (η n) A η' β' eη eβ = eη (g n)
church-encode-is-natural g (β ϕ n) A η' β' eη eβ =
 eβ _ _ _ _ refl (λ y → church-encode-is-natural g (ϕ y) A η' β' eη eβ)

Rnorm-lemma-rec-zero : {A σ : type} {Γ : Cxt}
                       (a : T (Γ ,, ι) (ι ⇒ B-type〖 σ ⇒ σ 〗 A))
                       (b : T Γ (B-type〖 σ 〗 A))
                       (s : Sub₀ Γ)
                     → ⟦ (close (ƛ (Rec a (weaken, ι b) ν₀)) s) · Zero ⟧₀
                     ≡ ⟦ close b s ⟧₀
Rnorm-lemma-rec-zero {A} {σ} {Γ} a b s =
 ⟦ (close (ƛ (Rec a (weaken, ι b) ν₀)) s) · Zero ⟧₀
  ＝≡⟨ refl ⟩
 ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ zero)
  ＝≡⟨ ap (λ k → ⟦ k ⟧ (⟨⟩ ‚ zero)) (close-weaken b (⊆, Γ ι) (Subƛ s)) ⟩
 ⟦ close b (⊆Sub (∈CxtS ι) (Subƛ s)) ⟧ (⟨⟩ ‚ zero)
  ≡⟨ ⟦close⟧ b (⊆Sub (∈CxtS ι) (Subƛ s)) _ _ (【≡】-is-refl‚ _ _ (λ ()) refl) (【≡】-【Sub】-⊆Sub' s) ⟩
 ⟦ b ⟧ (【Sub】 (⊆Sub (∈CxtS ι) (Subƛ s)) (⟨⟩ ‚ zero))
  ≡⟨ ⟦⟧-eta b _ _ (【≡】-【Sub】-⊆Sub s) ⟩
 ⟦ b ⟧ (【Sub₀】 s)
  ≡＝⟨ ≡-sym (⟦close⟧ b s _ _ (λ ()) (【≡】-is-refl-【Sub₀】 s)) ⟩
 ⟦ close b s ⟧₀
  ∎

η⋆ι≡ : {σ₁ σ₂ σ₃ : type} (i : ℕ) → η⋆ {_} {_} {_} {_} {〖 σ₁ 〗} {〖 σ₂ 〗} {ℕ} {〖 σ₃ 〗} i ≡ η⋆ i
η⋆ι≡ {σ₁} {σ₂} {σ₃} i a₁ b₁ a≡₁ a₂ b₂ a≡₂ = a≡₁ _ _ refl

Rnorm-lemma-rec-succ : {A σ : type} {Γ : Cxt}
                       (a : T Γ (B-type〖 ι ⇒ σ ⇒ σ 〗 A))
                       (b : T Γ (B-type〖 σ 〗 A))
                       (n : T₀ ι)
                       (s : Sub₀ Γ)
                     → ⟦ close (ƛ (Rec (ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀))) (weaken, ι b) ν₀)) s · Succ n ⟧₀
                     ≡ ⟦ close a s · (⌜η⌝ · n) · Rec (ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀))) (close b s) n ⟧₀
Rnorm-lemma-rec-succ {A} {σ} {Γ} a b n s =
 ⟦ close (ƛ (Rec (ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀))) (weaken, ι b) ν₀)) s · Succ n ⟧₀
  ＝≡⟨ refl ⟩
 ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
  (η⋆ ⟦ n ⟧₀)
  (rec (λ x → ⟦ close (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x))
       (⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀))
       ⟦ n ⟧₀)
  ≡＝⟨ e1 _ _ (λ a₁ b₁ a≡₁ a₂ b₂ a≡₂ → a≡₁ _ _ refl) _ _ e2 ⟩
 ⟦ close a s ⟧₀
  (η⋆ ⟦ n ⟧₀)
  (rec ⟦ ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀)) ⟧₀ ⟦ close b s ⟧₀ ⟦ n ⟧₀)
  ＝⟨ refl ⟩
 ⟦ close a s · (⌜η⌝ · n) · Rec (ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀))) (close b s) n ⟧₀
  ∎
 where
  e0 : {τ : type} (i : ∈Cxt τ Γ)
     → ⟦ weaken, ι (weaken, ι (s i)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
     ≡ ⟦ s i ⟧₀
  e0 {τ} i =
   ⟦ weaken, ι (weaken, ι (s i)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
    ≡＝⟨ ⟦weaken,-weaken,⟧ ⟨⟩ (succ ⟦ n ⟧₀) ⟦ n ⟧₀ (s i) refl (λ ()) ⟩
   ⟦ s i ⟧₀
    ∎

  e4 : {τ : type} (i : ∈Cxt τ Γ)
     → ⟦ weaken, ι (s i) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)
     ≡ ⟦ s i ⟧₀
  e4 {τ} i = ⟦weaken,⟧ (s i) ι _ _ (λ ())

  e1 : ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
     ≡ ⟦ close a s ⟧₀
  e1 =
   ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
    ≡⟨ ⟦close⟧ (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) _ _ (【≡】-is-refl‚ _ _ (【≡】-is-refl‚ _ _ (λ ()) refl) refl) (【≡】-【Sub】-Subƛ' _ _ _ refl refl) ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀))
    ≡⟨ ≡-refl (weaken, ι (weaken, ι a)) _ _ (【≡】-【Sub】-Subƛ2 s (succ ⟦ n ⟧₀) ⟦ n ⟧₀ refl refl) ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub₀】 s ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
    ≡⟨ ⟦weaken,-weaken,⟧ (【Sub₀】 s) (succ ⟦ n ⟧₀) ⟦ n ⟧₀ a refl (【≡】-is-refl-【Sub₀】 s) ⟩
   ⟦ a ⟧ (【Sub₀】 s)
    ≡＝⟨ ≡-sym (⟦close⟧' a s) ⟩
   ⟦ close a s ⟧₀
    ∎

  e3 : ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀) ≡ ⟦ close b s ⟧₀
  e3 =
   ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)
    ≡⟨ ⟦close⟧ (weaken, ι b) (Subƛ s) _ _ (【≡】-is-refl‚ _ _ (λ ()) refl) (【≡】-【Sub】-Subƛ _ _ refl) ⟩
   ⟦ weaken, ι b ⟧ (【Sub】 (Subƛ s) (⟨⟩ ‚ succ ⟦ n ⟧₀))
    ≡⟨ ⟦weaken,⟧ b ι _ _ (【≡】-is-refl-【⊆】-⊆,-【Sub】-Subƛ s _ refl) ⟩
   ⟦ b ⟧ (【⊆】 (⊆, Γ ι) (【Sub】 (Subƛ s) (⟨⟩ ‚ succ ⟦ n ⟧₀)))
    ≡⟨ ⟦⟧-eta b (【⊆】 (⊆, Γ ι) (【Sub】 (Subƛ s) (⟨⟩ ‚ succ ⟦ n ⟧₀))) (【Sub₀】 s) e4 ⟩
   ⟦ b ⟧ (【Sub₀】 s)
    ≡＝⟨ ≡-sym (⟦close⟧' b s) ⟩
   ⟦ close b s ⟧₀
    ∎

  e6 : (i : ℕ) {τ : type} (j : ∈Cxt τ Γ)
     → ⟦ weaken, ι (weaken, ι (s j)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i)
     ≡ ⟦ s j ⟧₀
  e6 i {τ} j = ≡-trans (⟦weaken,-weaken,⟧-as-⟦weaken,⟧ ⟨⟩ i (succ ⟦ n ⟧₀) i (s j) refl (λ ()))
                       (⟦weaken,⟧ (s j) ι _ _ (λ ()))

  e5 : (i : ℕ) (u v : 〖 B-type〖 σ 〗 A 〗)
     → u ≡ v
     → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
     ≡ ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
  e5 i u v e =
   ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
    ≡⟨ ⟦close⟧ (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i)
        (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i))
        (【≡】-is-refl‚ _ _ (【≡】-is-refl‚ _ _ (λ ()) refl) refl)
        (【≡】-【Sub】-Subƛ' _ _ _ refl refl)
        _ _ (λ a₁ b₁ a≡₁ a₂ b₂ a≡₂ → a≡₁ _ _ refl) _ _ e ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i)) (η⋆ i) v
    ≡⟨ ≡-refl (weaken, ι (weaken, ι a)) _ _ (【≡】-【Sub】-Subƛ2 s (succ ⟦ n ⟧₀) i refl refl) _ _ (η⋆ι≡ i) _ _ (≡ᵣ e) ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub₀】 s ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) v
    ≡⟨ ⟦weaken,-weaken,⟧ (【Sub₀】 s) (succ ⟦ n ⟧₀) i a refl (【≡】-is-refl-【Sub₀】 s) _ _ (η⋆ι≡ i) _ _ (≡ᵣ e) ⟩
   ⟦ a ⟧ (【Sub₀】 s ) (η⋆ i) v
    ≡⟨ ≡-sym (⟦close⟧ a s (【⊆】 (∈CxtS ι) (⟨⟩ ‚ i)) (【Sub₀】 s) (λ ()) (【≡】-is-refl-【Sub₀】 s) _ _ (η⋆ι≡ i) _ _ (≡ᵣ e)) ⟩
   ⟦ close a s ⟧ (【⊆】 (⊆, 〈〉 ι) (⟨⟩ ‚ i)) (η⋆ i) v
    ≡＝⟨ ≡-sym (⟦weaken,⟧ (close a s) ι _ _ (λ ()) _ _ (η⋆ι≡ i) _ _ (≡ᵣ e)) ⟩
   ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
    ∎

  e7 : (i j : ℕ) → i ＝ j → (u v : 〖 B-type〖 σ 〗 A 〗)
     → u ≡ v
     → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
     ≡ ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ j) (η⋆ j) v
  e7 i .i refl u v e = e5 i u v e

  e2 : rec (λ x → ⟦ close (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x))
        (⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀))
        ⟦ n ⟧₀
     ≡ rec ⟦ ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀)) ⟧₀ ⟦ close b s ⟧₀ ⟦ n ⟧₀
  e2 = ≡rec {_}
        {λ x → ⟦ close (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x)}
        {⟦ ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀)) ⟧₀}
        {⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)}
        {⟦ close b s ⟧₀}
        {⟦ n ⟧₀} {⟦ n ⟧₀}
        e7 e3 (≡-refl₀ n)

-- as opposed to Rnorm-lemma-rec-succ, this one does not "reduce" as much
Rnorm-lemma-rec-succ2 : {A σ : type} {Γ : Cxt}
                        (a : T Γ (B-type〖 ι ⇒ σ ⇒ σ 〗 A))
                        (b : T Γ (B-type〖 σ 〗 A))
                        (n : T₀ ι)
                        (s : Sub₀ Γ)
                      → ⟦ close (ƛ (Rec (ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀))) (weaken, ι b) ν₀)) s  · n ⟧₀
                      ≡ ⟦ Rec (ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀))) (close b s) n ⟧₀
Rnorm-lemma-rec-succ2 {A} {σ} {Γ} a b n s =
 rec (λ y → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ y) (η⋆ y))
     (⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀))
     ⟦ n ⟧₀
  ≡＝⟨ ≡rec {_}
         {λ y → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ y) (η⋆ y)}
         {λ y → ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ y) (η⋆ y)}
         {⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀)} {⟦ close b s ⟧₀}
         {⟦ n ⟧₀} {⟦ n ⟧₀} e5 e1 refl ⟩
 rec (λ y → ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ y) (η⋆ y))
     ⟦ close b s ⟧₀
     ⟦ n ⟧₀
  ∎
 where
  e4 : (i : ℕ) {τ : type} (j : ∈Cxt τ Γ)
     → ⟦ weaken, ι (weaken, ι (s j)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i)
     ≡ ⟦ s j ⟧₀
  e4 i {τ} j = ⟦weaken,-weaken,⟧ ⟨⟩ ⟦ n ⟧₀ i (s j) refl (λ ())

  e3 : (i : ℕ) (u v : 〖 B-type〖 σ 〗 A 〗)
     → u ≡ v
     → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
     ≡ ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
  e3 i u v e =
   ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
    ≡⟨ ⟦close⟧ (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i)
        (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i))
        (【≡】-is-refl‚ _ _ (【≡】-is-refl‚ _ _ (λ ()) refl) refl)
        (【≡】-【Sub】-Subƛ' _ _ _ refl refl)
        _ _ (η⋆ι≡ i) _ _ e ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i)) (η⋆ i) v
    ≡⟨ ≡-refl (weaken, ι (weaken, ι a)) _ _ (【≡】-【Sub】-Subƛ2 s (⟦ n ⟧₀) i refl refl) _ _ (η⋆ι≡ i) _ _ (≡ᵣ e) ⟩
   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub₀】 s ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) v
    ≡⟨ ⟦weaken,-weaken,⟧ (【Sub₀】 s) (⟦ n ⟧₀) i a refl (【≡】-is-refl-【Sub₀】 s) _ _ (η⋆ι≡ i) _ _ (≡ᵣ e) ⟩
   ⟦ a ⟧ (【Sub₀】 s ) (η⋆ i) v
    ≡⟨ ≡-sym (⟦close⟧ a s (【⊆】 (∈CxtS ι) (⟨⟩ ‚ i)) (【Sub₀】 s) (λ ()) (【≡】-is-refl-【Sub₀】 s) _ _ (η⋆ι≡ i) _ _ (≡ᵣ e)) ⟩
   ⟦ close a s ⟧ (【⊆】 (⊆, 〈〉 ι) (⟨⟩ ‚ i)) (η⋆ i) v
    ≡＝⟨ ≡-sym (⟦weaken,⟧ (close a s) ι _ _ (λ ()) _ _ (η⋆ι≡ i) _ _ (≡ᵣ e)) ⟩
   ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
    ∎

  e5 : (i j : ℕ) → i ＝ j → (u v : 〖 B-type〖 σ 〗 A 〗)
     → u ≡ v
     → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
     ≡ ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ j) (η⋆ j) v
  e5 i .i refl u v e = e3 i u v e

  e2 : {τ : type} (i : ∈Cxt τ Γ)
     → ⟦ weaken, ι (s i) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀)
     ≡ ⟦ s i ⟧₀
  e2 {τ} i = ⟦weaken,⟧ (s i) ι _ _ (λ ())

  e1 : ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀) ≡ ⟦ close b s ⟧₀
  e1 =
   ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀)
    ≡⟨ ⟦close⟧ (weaken, ι b) (Subƛ s) _ _ (【≡】-is-refl‚ _ _ (λ ()) refl) (【≡】-【Sub】-Subƛ _ _ refl) ⟩
   ⟦ weaken, ι b ⟧ (【Sub】 (Subƛ s) (⟨⟩ ‚ ⟦ n ⟧₀))
    ≡⟨ ⟦weaken,⟧ b ι _ _ (【≡】-is-refl-【⊆】-⊆,-【Sub】-Subƛ s _ refl) ⟩
   ⟦ b ⟧ (【⊆】 (⊆, Γ ι) (【Sub】 (Subƛ s) (⟨⟩ ‚ ⟦ n ⟧₀)))
    ≡⟨ ⟦⟧-eta b (【⊆】 (⊆, Γ ι) (【Sub】 (Subƛ s) (⟨⟩ ‚ ⟦ n ⟧₀))) (【Sub₀】 s) e2 ⟩
   ⟦ b ⟧ (【Sub₀】 s)
    ≡＝⟨ ≡-sym (⟦close⟧' b s) ⟩
   ⟦ close b s ⟧₀
    ∎

is-dialogue-for-zero : ⟦ ⌜zero⌝ ⟧₀ ≣⋆ church-encode zero'
is-dialogue-for-zero A η' β' eη eβ = eη 0

≣⋆-B⋆-functor : {X Y : 𝓤 ̇ } {d d' : {A : type} → B⋆ X 〖 A 〗} (f : X → Y)
              → d ≣⋆ d'
              → B⋆-functor f d ≣⋆ B⋆-functor f d'
≣⋆-B⋆-functor {_} {X} {Y} {d} {d'} f eq A η' β' eη eβ =
 eq _ _ _ (λ x → eη (f x)) eβ

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

Rnorm-lemma {Γ} {σ} xs ys (Rec t u v) Rnorm-xs =
 Rnorm-preserves-⟦⟧
   (rec' (B⟦ t ⟧ xs) (B⟦ u ⟧ xs) (B⟦ v ⟧ xs))
   (⌜Kleisli-extension⌝
    · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ t ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ u ⌝) ν₀)) ys
    · close ⌜ v ⌝ ys)
   (close ⌜ Rec t u v ⌝ ys)
   (λ A → ≡-sym (⟦close-⌜Rec⌝⟧ {A} ys t u v))
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
         (λ A → ≡-sym (Rnorm-lemma-rec-zero {A} (ƛ (weaken, ι (weaken, ι ⌜ t ⌝) · (⌜η⌝ · ν₀))) ⌜ u ⌝ ys))
         (Rnorm-lemma xs ys u Rnorm-xs)
  rnn' (succ n) = r
   where
    r : Rnorm (B⟦ t ⟧ xs (η n) (rn n)) (rn' · Succ (ℕ→T n))
    r = Rnorm-preserves-⟦⟧
         (B⟦ t ⟧ xs (η n) (rn n))
         (close ⌜ t ⌝ ys · (⌜η⌝ · ℕ→T n) · Rec (ƛ (weaken, ι (close ⌜ t ⌝ ys) · (⌜η⌝ · ν₀))) (close ⌜ u ⌝ ys) (ℕ→T n))
         (rn' · Succ (ℕ→T n))
         (λ A → ≡-sym (Rnorm-lemma-rec-succ {A} ⌜ t ⌝ ⌜ u ⌝ (ℕ→T n) ys))
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
    (λ A → ≡-sym (≡-refl₀ rn' _ _ (Rnormη⌜η⌝ n n' r)))
    (rnn' n)

  c1 : Rnorm (Kleisli-extension rn (B⟦ v ⟧ xs))
             (⌜Kleisli-extension⌝ · rn' · close ⌜ v ⌝ ys)
  c1 = Rnorm-kleisli-lemma rn rn' rnn' (B⟦ v ⟧ xs) (close ⌜ v ⌝ ys) (Rnorm-lemma xs ys v Rnorm-xs)

Rnorm-lemma xs ys (ν i) Rnorm-xs = Rnorm-xs i

Rnorm-lemma xs ys (ƛ t) Rnorm-xs u u' Rnorm-u =
 Rnorm-preserves-⟦⟧
  (B⟦ t ⟧ (xs ‚‚ u))
  (close ⌜ t ⌝ (Sub,, ys u'))
  (ƛ (close ⌜ t ⌝ (Subƛ ys)) · u')
  eq
  (Rnorm-lemma (xs ‚‚ u) (Sub,, ys u') t Rnorm-xs,,u)
 where
  eq : (A : type) → ⟦ close ⌜ t ⌝ (Sub,, ys u') ⟧₀ ≡[ (B-type〖 _ 〗 A) ] ⟦ ƛ (close ⌜ t ⌝ (Subƛ ys)) · u' ⟧₀
  eq A =
   ⟦ close ⌜ t ⌝ (Sub,, ys u') ⟧₀
    ≡⟨ ⟦close⟧' ⌜ t ⌝ (Sub,, ys u') ⟩
   ⟦ ⌜ t ⌝ ⟧ (【Sub₀】 (Sub,, ys u'))
    ≡⟨ ⟦⟧-eta ⌜ t ⌝ (【Sub₀】 (Sub,, ys u')) (【Sub】 (Subƛ ys) (⟨⟩ ‚ ⟦ u' ⟧₀)) (【≡】-【Sub】-Sub,, ys u') ⟩
   ⟦ ⌜ t ⌝ ⟧ (【Sub】 (Subƛ ys) (⟨⟩ ‚ ⟦ u' ⟧₀))
    ≡＝⟨ ≡-sym (⟦close⟧ ⌜ t ⌝ (Subƛ ys) _ _ (【≡】-is-refl‚ _ _ (λ ()) (≡-refl₀ u')) (【≡】-【Sub】-Subƛ ys _ (≡-refl₀ u'))) ⟩
   ⟦ ƛ (close ⌜ t ⌝ (Subƛ ys)) · u' ⟧₀
    ∎

  Rnorm-xs,,u : Rnorms (xs ‚‚ u) (Sub,, ys u')
  Rnorm-xs,,u (∈Cxt0 _)   = Rnorm-u
  Rnorm-xs,,u (∈CxtS _ i) = Rnorm-xs i

Rnorm-lemma xs ys (t · u) Rnorm-xs =
 Rnorm-lemma xs ys t Rnorm-xs (B⟦ u ⟧ xs) (close ⌜ u ⌝ ys) (Rnorm-lemma xs ys u Rnorm-xs)

-- a consequence of Rnorm-lemma for terms of type ι
Rnorm-lemmaι : (t : T₀ ι) (α : Baire)
             → dialogue⋆ ⟦ ⌜ t ⌝ ⟧₀ ≡ dialogue⋆ (church-encode B⟦ t ⟧₀)
Rnorm-lemmaι t α =
 dialogue⋆ ⟦ ⌜ t ⌝ ⟧₀
  ≡⟨ ≡-sym (⟦closeν⟧ ⌜ t ⌝ _ (λ ()) _ _ η≡ _ _ β≡) ⟩
 dialogue⋆ ⟦ close ⌜ t ⌝ ν ⟧₀
  ≡＝⟨ Rnorm-lemma ⟪⟫ ν t (λ ()) ((ι ⇒ ι) ⇒ ι) η' β' eη eβ ⟩
 dialogue⋆ (church-encode B⟦ t ⟧₀)
  ∎
 where
  η' : ℕ → (ℕ → ℕ) → ℕ
  η' = λ z α → z

  β' : (ℕ → (ℕ → ℕ) → ℕ) → ℕ → (ℕ → ℕ) → ℕ
  β' = λ φ x α → φ (α x) α

  η≡ : η' ≡ η'
  η≡ a b a≡ a₁ b₁ a≡₁ = a≡

  β≡ : β' ≡ β'
  β≡ a b a≡ a₁ b₁ a≡₁ a₂ b₂ a≡₂ = a≡ _ _ (a≡₂ _ _ a≡₁) _ _ a≡₂

  eη : extη η'
  eη x a b a≡ = refl

  eβ : extβ β'
  eβ a b x .x refl a≡ a₁ b₁ a≡₁ =
   a≡ _ _ _ a≡₁ ∙ a≡b _ _ (a≡₁ _ _ refl ⁻¹) ⁻¹ ∙ a≡ _ _ _ a≡₁
   where
    a≡b : (n m : ℕ) → n ＝ m → a n a₁ ＝ b m b₁
    a≡b n .n refl = a≡ _ _ _ a≡₁

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
  ＝⟨ ≡-sym (Rnorm-lemmaι t α _ _ e) ⟩
 dialogue⋆ ⟦ ⌜ t ⌝ ⟧₀ α
  ∎
 where
  e : (a b : ℕ) → a ＝ b → α a ＝ α b
  e a .a refl = refl

Rnorm-lemma₀ : {σ : type} (t : T₀ σ) → Rnorm B⟦ t ⟧₀ ⌜ t ⌝
Rnorm-lemma₀ {σ} t =
 Rnorm-preserves-⟦⟧
  B⟦ t ⟧₀ (close ⌜ t ⌝ ν) ⌜ t ⌝
  (λ A → ⟦closeν⟧ ⌜ t ⌝ _ (λ ()))
  (Rnorm-lemma ⟪⟫ ν t (λ ()))

Rnorm-generic : (u : B ℕ) (u' : {A : type} → T₀ (⌜B⌝ ι A))
              → is-dialogue-for u u'
              → is-dialogue-for (generic u) (⌜generic⌝ · u')
Rnorm-generic u u' ru =
 Rnorm-kleisli-lemma (β η) (⌜β⌝ · ⌜η⌝) c u u' ru
 where
  c : (x : ℕ)
    → β⋆ η⋆ ⟦ ℕ→T x ⟧₀ ≣⋆ β⋆ η⋆ x
  c x A η' β' eη eβ = eβ _ _ _ _ (⟦ℕ→T⟧ x) eη

⌜dialogue-tree⌝-correct : (t : T₀ ((ι ⇒ ι) ⇒ ι))
                          (α : Baire)
                        → ⟦ t ⟧₀ α ＝ dialogue⋆ ⟦ ⌜dialogue-tree⌝ t ⟧₀ α
⌜dialogue-tree⌝-correct t α =
 dialogue-tree-correct t α
 ∙ dialogues-agreement (dialogue-tree t) α
 ∙ e ⁻¹
 where
  η' : ℕ → Baire → ℕ
  η' = λ z i → z

  β' : (ℕ → Baire → ℕ) → ℕ → Baire → ℕ
  β' = λ φ x α → φ (α x) α

  rt : Rnorm B⟦ t ⟧₀ ⌜ t ⌝
  rt = Rnorm-lemma₀ {(ι ⇒ ι) ⇒ ι} t

  eη : extη η'
  eη x a b a≡ = refl

  eβ : extβ β'
  eβ f g x .x refl f≡ a b a≡ = f≡ _ _ _ a≡ ∙ a≡b _ _ (a≡ _ _ refl ⁻¹) ⁻¹ ∙ f≡ _ _ _ a≡
   where
    a≡b : (n m : ℕ) → n ＝ m → f n a ＝ g m b
    a≡b n .n refl = f≡ _ _ _ a≡

  eα : (a b : ℕ) → a ＝ b → α a ＝ α b
  eα a .a refl = refl

  e : ⟦ ⌜ t ⌝ · ⌜generic⌝ ⟧₀ η' β' α ≡ church-encode (B⟦ t ⟧₀ generic) η' β' α
  e = rt generic ⌜generic⌝ Rnorm-generic ((ι ⇒ ι) ⇒ ι) η' β' eη eβ _ _ eα

⌜dialogue⌝ : {Γ : Cxt}
           → T (B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι)) (⌜B⌝ ι ((ι ⇒ ι) ⇒ ι))
           → T (B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι)) ((ι ⇒ ι) ⇒ ι)
⌜dialogue⌝ {Γ} t = t · ƛ (ƛ ν₁) · ƛ (ƛ (ƛ (ν₂ · (ν₀ · ν₁) · ν₀)))

-- Same as ⌜dialogue-tree⌝-correct but using an internal dialogue function
⌜dialogue-tree⌝-correct' : (t : T₀ ((ι ⇒ ι) ⇒ ι))
                           (α : Baire)
                         → ⟦ t ⟧₀ α ＝ ⟦ ⌜dialogue⌝ (⌜dialogue-tree⌝ t) ⟧₀ α
⌜dialogue-tree⌝-correct' t α = ⌜dialogue-tree⌝-correct t α

{-

-- Is that even provable? (we don't need it, but we want to explore this)
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

-}

\end{code}
