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
open import EffectfulForcing.Internal.External
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.Internal.Subst
open import UF.Base using (transport₂ ; transport₃ ; ap₂ ; ap₃)

\end{code}

Using a logical relation we show that the the internal, church-encoded dialogue
translation of a System T term coincides with its external, inductive dialogue
translation.

From this result and the main-lemma we can derive an internal result of
strong continuity in System T.

\begin{code}

is-dialogue-for : B ℕ → ({A : type} → T₀ (B-type〖 ι 〗 A)) → Type
is-dialogue-for d t = {A : type} → ⟦ t ⟧₀ ≡[ B-type〖 ι 〗 A ] church-encode d

-- Logical relation for internal dialogue trees which can be pattern matched on
-- and for functions that preserve said pattern matching.
Rnorm : {σ : type} (d : B〖 σ 〗) (t : {A : type} → T₀ (B-type〖 σ 〗 A)) → Type
Rnorm {ι}     d t = is-dialogue-for d t
Rnorm {σ ⇒ τ} d t = (u : B〖 σ 〗) (u' : {A : type} → T₀ (B-type〖 σ 〗 A))
                  → Rnorm u u' → Rnorm (d u) (t · u')

-- internal semantics of contexts as dialogue trees
IB【_】 : Cxt → type → Type
IB【 Γ 】 A = Sub₀ (B-context【 Γ 】 A)

Rnorms : {Γ : Cxt} → B【 Γ 】 → ({A : type} → IB【 Γ 】 A) → Type
Rnorms {Γ} xs ys = {σ : type} (i : ∈Cxt σ Γ) → Rnorm (xs i) (ys (∈Cxt-B-type i))

-- To avoid the operational semantics, we use the following lemma.
Rnorm-respects-≡ : {σ : type} {d : B〖 σ 〗} {t u : {A : type} → T₀ (B-type〖 σ 〗 A)}
                   → ({A : type} → ⟦ t ⟧₀ ≡[ (B-type〖 σ 〗 A) ] ⟦ u ⟧₀)
                   → Rnorm d t
                   → Rnorm d u
Rnorm-respects-≡ {ι} {d} {t} {u} t≡u Rnorm-d-t {A} {η₁} {η₂} η₁≡η₂ {β₁} {β₂} β₁≡β₂ =
 ⟦ u ⟧₀ η₁ β₁          ≡⟨ ≡-symm (t≡u {A} (≡ₗ η₁ η₁≡η₂) (≡ₗ β₁ β₁≡β₂)) ⟩
 ⟦ t ⟧₀ η₁ β₁          ≡＝⟨ Rnorm-d-t η₁≡η₂ β₁≡β₂ ⟩
 church-encode d η₂ β₂ ∎
Rnorm-respects-≡ {σ ⇒ τ} {d} {t} {u} t≡u Rnorm-t v₁ v₂ Rnorm-vs =
 Rnorm-respects-≡ -- (d v₁) (t · v₂) (u · v₂)
                    (t≡u (≡-refl₀ v₂))
                    (Rnorm-t v₁ v₂ Rnorm-vs)

\end{code}

As Rnorm quantifies over all System T types, we can elimate a family of
church-encoded trees into different types, allowing us to reify terms into
the shape of ⌜η⌝ or ⌜β⌝.

This sort of reification is crucial when we need to pattern match on the
constructor of a church-encoded tree.

Require fact that Rnorm is parametric when proving the reflects-≡ lemmas.

\begin{code}

-- TODO this should be moved to the definition of numeral?
⟦numeral⟧ : {Γ : Cxt} (γ : 【 Γ 】) (n : ℕ) → ⟦ numeral n ⟧ γ ≡ n
⟦numeral⟧ γ  zero    = refl
⟦numeral⟧ γ (succ n) = ap succ (⟦numeral⟧ γ n)

⟦numeral⟧₀ : (n : ℕ) → ⟦ numeral n ⟧₀ ＝ n
⟦numeral⟧₀  n = ⟦numeral⟧ ⟨⟩ n

Rnorm-numeral : (n : ℕ) → Rnorm (η n) (⌜η⌝ · numeral n)
Rnorm-numeral n η₁≡η₂ β₁≡β₂ = η₁≡η₂ (⟦numeral⟧₀ n)

Rnorm-η-implies-≡ : {n₁ : ℕ} {n₂ : T₀ ι}
                  → Rnorm (η n₁) (⌜η⌝ · n₂)
                  → ⟦ numeral n₁ ⟧₀ ≡ ⟦ n₂ ⟧₀
Rnorm-η-implies-≡ {n₁} {n₂} Rnorm-ns =
 ⟦ numeral n₁ ⟧₀ ≡⟨ ⟦numeral⟧₀ n₁ ⟩
 n₁              ≡⟨ ≡-symm (Rnorm-ns η₁≡η₁ β₁≡β₁) ⟩
 ⟦ n₂ ⟧₀ ∎
 where
  η₁ : ℕ → ℕ
  η₁ n = n

  η₁≡η₁ : η₁ ≡ η₁
  η₁≡η₁ n₁＝n₂ = n₁＝n₂

  β₁ : (ℕ → ℕ) → ℕ → ℕ
  β₁ ϕ n = 0

  β₁≡β₁ : β₁ ≡ β₁
  β₁≡β₁ ϕ₁≡ϕ₂ n₁≡n₂ = refl

-- TODO give this a better name

η-type : type → type
η-type A = ι ⇒ A

β-type : type → type
β-type A = (ι ⇒ A) ⇒ ι ⇒ A

branch : ({A : type} → T₀ (⌜B⌝ ι A)) → {A : type} → T₀ (ι ⇒ ⌜B⌝ ι A)
branch t {A} =
 -- λ i. λ η. λ β. t η' β' h
 ƛ (ƛ (ƛ (weaken₀ (t {A'}) · η' · β' · h)))
 where
  -- To pull out the branching ϕ we use the following elimination type
  A' : type
  A' = β-type A ⇒ A

  -- λ n. λ k. η(n)
  η' : T (〈〉 ,, ι ,, η-type A ,, β-type A) (η-type A')
  η' = ƛ (ƛ (ν₃ · ν₁))

  -- λ g. λ n. λ h. h (λ j. g j β) n
  β' : T (〈〉 ,, ι ,, η-type A ,, β-type A) (β-type A')
  β' = ƛ (ƛ (ƛ (ν₀ · ƛ (ν₃ · ν₀ · ν₄) · ν₁)))

  -- λ k. λ n.k i
  h : T (〈〉 ,, ι ,, η-type A ,, β-type A) (β-type A)
  h = ƛ (ƛ (ν₁ · ν₄))

-- TODO can this proof be tidied at all?
Rnorm-branch : {ϕ : ℕ → B ℕ} {n : ℕ} {t : {A : type} → T₀ (⌜B⌝ ι A)} (i : ℕ)
               → Rnorm (β ϕ n) t
               → Rnorm (ϕ i) (branch t · numeral i)
               --→ ⟦ branch t · numeral i⟧ i ≡ church-encode (ϕ i)
Rnorm-branch {ϕ} {n} {t} i Rnorm-βt {A} {η₁} {η₂} η₁≡η₂ {β₁} {β₂} β₁≡β₂ =
 ⟦ branch t · numeral i ⟧₀ η₁ β₁                        ＝≡⟨ refl ⟩
 ⟦ weaken₀ t ⟧ (⟨⟩ ‚ ⟦ numeral i ⟧₀ ‚ η₁ ‚ β₁) η₀ β₀ h₀ ≡⟨ I η₀≡η₀ β₀≡β₀ h₀≡h₁ ⟩
 church-encode (β ϕ n) η₀ β₀ h₁                         ＝≡⟨ refl ⟩
 church-encode (ϕ i) η₀ β₀ β₁                           ≡＝⟨ q (ϕ i) ⟩
 church-encode (ϕ i) η₂ β₂                              ∎
 where
  -- To pull out the branching ϕ we use the following elimination type
  A' : type
  A' = β-type A ⇒ A

  I : ⟦ weaken₀ (t {A'}) ⟧ (⟨⟩ ‚ ⟦ numeral i ⟧₀ ‚ η₁ ‚ β₁) ≡ church-encode (β ϕ n)
  I = ≡-trans {⌜B⌝ ι _} (⟦weaken₀⟧ t ((⟨⟩ ‚ ⟦ numeral i ⟧ ⟨⟩ ‚ η₁ ‚ β₁))) Rnorm-βt

  η₀ : 〖 η-type A' 〗
  η₀ = λ n → λ k → η₁ n

  η₀≡η₀ : η₀ ≡ η₀
  η₀≡η₀ n₁≡n₂ k₁≡k₂ = ≡ₗ η₁ η₁≡η₂ n₁≡n₂

  β₀ : 〖 β-type A' 〗
  β₀ = λ g → λ n → λ h → h (λ j → g j β₁) n

  β₀≡β₀ : β₀ ≡ β₀
  β₀≡β₀ g₁≡g₂ n₁≡n₂ h₁≡h₂ = h₁≡h₂ (λ j₁≡j₂ → g₁≡g₂ j₁≡j₂ (≡ₗ β₁ β₁≡β₂)) n₁≡n₂

  h₀ : 〖 β-type A 〗
  h₀ = λ k → λ n → k ⟦ numeral i ⟧₀

  h₁ : 〖 β-type A 〗
  h₁ = λ k → λ n → k i

  h₀≡h₁ : h₀ ≡ h₁
  h₀≡h₁ k₁≡k₂ n₁≡n₂ = k₁≡k₂ (⟦numeral⟧₀ i)

  q : (d : B ℕ) → church-encode d η₀ β₀ β₁ ≡ church-encode d η₂ β₂
  q (η x)   = η₁≡η₂ refl
  q (β ψ y) = β₁≡β₂ ψ≡ψ refl
   where
    ψ≡ψ : (λ i → church-encode (ψ i) η₀ β₀ β₁) ≡ (λ i → church-encode (ψ i) η₂ β₂)
    ψ≡ψ {j} {.j} refl = q (ψ j)

Rnorm-β-implies-Rnorm-ϕ : {ϕ₁ : ℕ → B ℕ} {n₁ : ℕ}
                          {ϕ₂ : {A : type} → T₀ (ι ⇒  ⌜B⌝ ι A)} {n₂ : T₀ ι}
                          (i : ℕ)
                        → Rnorm (β ϕ₁ n₁) (⌜β⌝ · ϕ₂ · n₂)
                        → Rnorm (ϕ₁ i) (ϕ₂ · numeral i)
Rnorm-β-implies-Rnorm-ϕ = {!!}

Rnorm-β-implies-n-≡ : {ϕ₁ : ℕ → B ℕ} {n₁ : ℕ}
                      {ϕ₂ : {A : type} → T₀ (ι ⇒ ⌜B⌝ ι A)} {n₂ : T₀ ι}
                    → Rnorm (β ϕ₁ n₁) (⌜β⌝ · ϕ₂ · n₂)
                    → ⟦ numeral n₁ ⟧₀ ≡ ⟦ n₂ ⟧₀
Rnorm-β-implies-n-≡ = {!!}

Rnorm-reify-β : (ϕ : ℕ → B ℕ) (n : ℕ) (t : {A : type} → T₀ (⌜B⌝ ι A))
                → Rnorm (β ϕ n) t
                → Σ ϕ' ꞉ ({A : type} → T₀ (ι ⇒ ⌜B⌝ ι A))                -- branch
                , Σ n' ꞉ T₀ ι                                           -- numeral
                , ({A : type} → ⟦ t ⟧₀ ≡[ ⌜B⌝ ι A ] ⟦ ⌜β⌝ · ϕ' · n' ⟧₀) -- follows (almost?) directly from assumption that Rnorm (β ϕ n) t, does it not?
                × Rnorm (β ϕ n) (⌜β⌝ · ϕ' · n')                         -- Rnorm-branch
                × (⟦ n' ⟧₀ ≡ n)                                         -- Rnorm-β-implies-n-≡
                × ((x : ℕ) → Rnorm (ϕ x) (ϕ' · numeral x))              -- Rnorm-β-implies-Rnorm-ϕ
Rnorm-reify-β = {!!}
-- where
--  -- We get the branching at t with the following
--  ϕ' : {A : type} → T₀ (ι ⇒ ⌜B⌝ ι A)
--  ϕ' {A} = B-branch t
--
--  -- We get the oracle query at t with the following
--  n' : T₀ ι
--  n' = numeral n
--
--  eq' : ⟦ t ⟧₀ ≣⋆ ⟦ ⌜β⌝ · ϕ' · n' ⟧₀
--  eq' A η' β' eη eβ =
--   ⟦ t ⟧₀ η' β'
--    ≡⟨ eq A η' β' eη eβ ⟩
--   β' (λ y → church-encode (ϕ y) η' β') n
--    ≡＝⟨ eβ _ _ _ _ ((⟦numeral⟧ n) ⁻¹) (λ y → ≡-symm (⟦B-branch⟧ ϕ y n t eq A η' β' eη eβ)) ⟩
--   ⟦ ⌜β⌝ · ϕ' · n' ⟧₀ η' β'
--    ∎
--
--  rβ : Rnorm (β ϕ n) (⌜β⌝ · ϕ' · n')
--  rβ = ≣⋆-trans (≣⋆-symm eq') eq
--
--  rϕ : (x : ℕ) → ⟦ B-branch t ⟧₀ ⟦ numeral x ⟧₀ ≣⋆ church-encode (ϕ x)
--  rϕ x = transport (λ k → ⟦ B-branch t ⟧₀ k ≣⋆ church-encode (ϕ x))
--                   (⟦numeral⟧ x ⁻¹) (⟦B-branch⟧ ϕ x n t eq)
--
-- TODO: can we generalize this?
church-encode-kleisli-extension : {A : type} (d : B ℕ)
                                → (f₁ : ℕ → B ℕ) (f₂ : {A : type} → T₀ (ι ⇒ ⌜B⌝ ι A))
                                → ((i : ℕ) → Rnorm (f₁ i) (f₂ · numeral i))
                                → church-encode (kleisli-extension f₁ d)
                                  ≡[ ⌜B⌝ ι A ] kleisli-extension⋆ ⟦ f₂ ⟧₀ (church-encode d)
church-encode-kleisli-extension {A} (η n) f₁ f₂ f₁≡f₂ =
 church-encode (f₁ n)                             ≡⟨ ≡-symm {⌜B⌝ ι A} (f₁≡f₂ n) ⟩
 ⟦ f₂ ⟧₀ ⟦ numeral n ⟧₀                           ≡＝⟨ ≡-refl₀ f₂ (⟦numeral⟧₀ n) ⟩
 kleisli-extension⋆ ⟦ f₂ ⟧₀ (church-encode (η n)) ∎
church-encode-kleisli-extension {A} (β ϕ n) f₁ f₂ f₁≡f₂ {η₁} {η₂} η₁≡η₂ {β₁} {β₂} β₁≡β₂ =
 β₁≡β₂ ϕ₁≡ϕ₂ refl
 where
  ϕ₁ : ℕ → 〖 A 〗
  ϕ₁ i = church-encode (kleisli-extension f₁ (ϕ i)) η₁ β₁

  ϕ₂ : ℕ → 〖 A 〗
  ϕ₂ i = kleisli-extension⋆ ⟦ f₂ ⟧₀ (church-encode (ϕ i)) η₂ β₂

  ϕ₁≡ϕ₂ : ϕ₁ ≡ ϕ₂
  ϕ₁≡ϕ₂ {i} {.i} refl = church-encode-kleisli-extension (ϕ i) f₁ f₂ f₁≡f₂ η₁≡η₂ β₁≡β₂

⟦⌜Kleisli-extension⌝⟧ : {X A σ : type} {Γ Δ : Cxt} (xs : 【 Γ 】) (ys : 【 Δ 】)
                      → ⟦ ⌜Kleisli-extension⌝ {X} {A} {σ} ⟧ xs
                      ≡ ⟦ ⌜Kleisli-extension⌝ {X} {A} {σ} ⟧ ys
⟦⌜Kleisli-extension⌝⟧ {X} {A} {ι} {Γ} {Δ} xs ys d₁≡d₂ f₁≡f₂ η₁≡η₂ β₁≡β₂ =
 f₁≡f₂ (λ x₁≡x₂ → d₁≡d₂ x₁≡x₂ η₁≡η₂ β₁≡β₂) β₁≡β₂
⟦⌜Kleisli-extension⌝⟧ {X} {A} {σ ⇒ τ} {Γ} {Δ} xs ys g₁≡g₂ f₁≡f₂ x₁≡x₂ =
 ⟦⌜Kleisli-extension⌝⟧ _ _ (λ y₁≡y₂ → g₁≡g₂ y₁≡y₂ x₁≡x₂) f₁≡f₂

-- Recursion in System T is interpreted by the internal dialogue tree translation
-- using ⌜Kleisli-extension⌝, so to prove the fundamental theorem of Rnorm we
-- need to know that ⌜Kleisli-extension⌝ preserves Rnorm.
Rnorm-kleisli-lemma : {σ : type}

                      (f₁ : ℕ → B〖 σ 〗)
                      (f₂ : {A : type} → T₀ (ι ⇒ B-type〖 σ 〗 A))
                    → ((x : ℕ) → Rnorm (f₁ x) (f₂ · numeral x))

                    → (n₁ : B ℕ)
                      (n₂ : {A : type} → T₀ (⌜B⌝ ι A))
                    → Rnorm {ι} n₁ n₂

                    → Rnorm (Kleisli-extension f₁ n₁) (⌜Kleisli-extension⌝ · f₂ · n₂)
Rnorm-kleisli-lemma {ι} f₁ f₂ Rnorm-fs n₁ n₂ Rnorm-ns {A} =
 ⟦ ⌜kleisli-extension⌝ · f₂ · n₂ ⟧₀
  ≡⟨ ≡-refl₀ {⌜B⌝ ι A ⇒ ⌜B⌝ ι A} (⌜kleisli-extension⌝ · f₂) Rnorm-ns ⟩
 kleisli-extension⋆ ⟦ f₂ ⟧₀ (church-encode n₁)
  ≡＝⟨ ≡-symm {⌜B⌝ ι A} (church-encode-kleisli-extension n₁ f₁ f₂ Rnorm-fs) ⟩
 church-encode (kleisli-extension f₁ n₁)
  ∎
Rnorm-kleisli-lemma {σ ⇒ τ} f₁ f₂ Rnorm-fs n₁ n₂ Rnorm-ns u₁ u₂ Rnorm-us =
 Rnorm-respects-≡ I IH
 where
  -- We perform some computation steps using the semantics.
  I : {A : type}
    → ⟦ ⌜Kleisli-extension⌝ · ƛ (weaken₀ f₂ · ν₀ · weaken₀ u₂) · n₂ ⟧₀
      ≡[ B-type〖 τ 〗 A ] ⟦ ƛ (ƛ (ƛ (⌜Kleisli-extension⌝ · ƛ (ν₃ · ν₀ · ν₁) · ν₁))) · f₂ · n₂ · u₂ ⟧₀
  I = ⟦⌜Kleisli-extension⌝⟧ ⟨⟩ (⟨⟩ ‚ ⟦ f₂ ⟧₀ ‚ ⟦ n₂ ⟧₀ ‚ ⟦ u₂ ⟧₀)
       (λ x₁≡x₂ → ⟦weaken₀⟧ f₂ _ x₁≡x₂ (⟦weaken₀⟧ u₂ _))
       (≡-refl₀ n₂)

  II : (x : ℕ) {A : type}
     → ⟦ ƛ (weaken₀ f₂ · ν₀ · weaken₀ u₂) · numeral x ⟧₀
       ≡[ B-type〖 τ 〗 A ] ⟦ f₂ · numeral x · u₂ ⟧₀
  II x = ⟦weaken₀⟧ f₂ (⟨⟩ ‚ ⟦ numeral x ⟧ ⟨⟩) refl (⟦weaken₀⟧ u₂ (⟨⟩ ‚ ⟦ numeral x ⟧₀))

  -- In the recursive case, Kleisli-extension calls Kleisli-extension at
  -- the codomain type with the following new fs'.
  f₁' : ℕ → B〖 τ 〗
  f₁' x = f₁ x u₁

  f₂' : {A : type} → T₀ (ι ⇒ B-type〖 τ 〗 A)
  f₂' = ƛ (weaken₀ f₂ · ν₀ · weaken₀ u₂)

  -- Crucially, these fs' are still related by Rnorm, so we can use them to get
  -- the inductive hypothesis IH.
  Rnorm-fs' : (x : ℕ) → Rnorm (f₁' x) (f₂' · numeral x)
  Rnorm-fs' x = Rnorm-respects-≡ (≡-symm (II x)) (Rnorm-fs x u₁ u₂ Rnorm-us)

  IH : Rnorm (Kleisli-extension f₁' n₁) (⌜Kleisli-extension⌝ · f₂' · n₂)
  IH = Rnorm-kleisli-lemma f₁' f₂' Rnorm-fs' n₁ n₂ Rnorm-ns


-- TODO is it possible to prove this in general?
-- We could when using ≣⋆ but it seems it would only be true when
-- g : ℕ → ℕ now that we are using ≡
church-encode-is-natural : {g₁ g₂ :  ℕ → ℕ} (d : B ℕ)
                         → g₁ ≡ g₂
                         → {A : type}
                         → B⋆-functor g₁ (church-encode d)
                           ≡[ ⌜B⌝ ι A ] church-encode (B-functor g₂ d)
church-encode-is-natural (η n) g₁≡g₂ {A} η₁≡η₂ β₁≡β₂ = η₁≡η₂ (g₁≡g₂ refl)
church-encode-is-natural {g₁} {g₂} (β ϕ n) g₁≡g₂ {A} {η₁} {η₂} η₁≡η₂ {β₁} {β₂} β₁≡β₂ =
 β₁≡β₂ ϕ₁≡ϕ₂ refl
 where
  ϕ₁ : ℕ → 〖 A 〗
  ϕ₁ i = B⋆-functor g₁ (church-encode (ϕ i)) η₁ β₁

  ϕ₂ : ℕ → 〖 A 〗
  ϕ₂ i = church-encode (B-functor g₂ (ϕ i)) η₂ β₂

  ϕ₁≡ϕ₂ : ϕ₁ ≡ ϕ₂
  ϕ₁≡ϕ₂ {i} {.i} refl = church-encode-is-natural (ϕ i) g₁≡g₂ η₁≡η₂ β₁≡β₂


--Rnorm-lemma-rec-zero : {A σ : type} {Γ : Cxt}
--                       (a : T (Γ ,, ι) (ι ⇒ B-type〖 σ ⇒ σ 〗 A))
--                       (b : T Γ (B-type〖 σ 〗 A))
--                       (s : Sub₀ Γ)
--                     → ⟦ (close (ƛ (Rec a (weaken, ι b) ν₀)) s) · Zero ⟧₀
--                     ≡ ⟦ close b s ⟧₀
--Rnorm-lemma-rec-zero {A} {σ} {Γ} a b s =
-- ⟦ (close (ƛ (Rec a (weaken, ι b) ν₀)) s) · Zero ⟧₀
--  ＝≡⟨ refl ⟩
-- ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ zero)
--  ＝≡⟨ ap (λ k → ⟦ k ⟧ (⟨⟩ ‚ zero)) (close-weaken b (⊆, Γ ι) (Subƛ s)) ⟩
-- ⟦ close b (⊆Sub (∈CxtS ι) (Subƛ s)) ⟧ (⟨⟩ ‚ zero)
--  ≡⟨ ⟦close⟧ b (⊆Sub (∈CxtS ι) (Subƛ s)) _ _ (【≡】-is-refl‚ _ _ (λ ()) refl) (【≡】-【Sub】-⊆Sub' s) ⟩
-- ⟦ b ⟧ (【Sub】 (⊆Sub (∈CxtS ι) (Subƛ s)) (⟨⟩ ‚ zero))
--  ≡⟨ ≡-refl b _ _ (【≡】-【Sub】-⊆Sub s) ⟩
-- ⟦ b ⟧ (【Sub₀】 s)
--  ≡＝⟨ ≡-symm (⟦close⟧ b s _ _ (λ ()) (【≡】-is-refl-【Sub₀】 s)) ⟩
-- ⟦ close b s ⟧₀
--  ∎
--
--η⋆ι≡ : {σ₁ σ₂ σ₃ : type} (i : ℕ)
--     → η⋆ {_} {_} {_} {_} {〖 σ₁ 〗} {〖 σ₂ 〗} {ℕ} {〖 σ₃ 〗} i ≡ η⋆ i
--η⋆ι≡ {σ₁} {σ₂} {σ₃} i a₁ b₁ a≡₁ a₂ b₂ a≡₂ = a≡₁ _ _ refl
--
--Rnorm-lemma-rec-succ : {A σ : type} {Γ : Cxt}
--                       (a : T Γ (B-type〖 ι ⇒ σ ⇒ σ 〗 A))
--                       (b : T Γ (B-type〖 σ 〗 A))
--                       (n : T₀ ι)
--                       (s : Sub₀ Γ)
--                     → ⟦ close (ƛ (Rec (ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀))) (weaken, ι b) ν₀)) s · Succ n ⟧₀
--                     ≡ ⟦ close a s · (⌜η⌝ · n) · Rec (ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀))) (close b s) n ⟧₀
--Rnorm-lemma-rec-succ {A} {σ} {Γ} a b n s =
-- ⟦ close (ƛ (Rec (ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀))) (weaken, ι b) ν₀)) s · Succ n ⟧₀
--  ＝≡⟨ refl ⟩
-- ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
--  (η⋆ ⟦ n ⟧₀)
--  (rec (λ x → ⟦ close (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x))
--       (⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀))
--       ⟦ n ⟧₀)
--  ≡＝⟨ e1 _ _ (λ a₁ b₁ a≡₁ a₂ b₂ a≡₂ → a≡₁ _ _ refl) _ _ e2 ⟩
-- ⟦ close a s ⟧₀
--  (η⋆ ⟦ n ⟧₀)
--  (rec ⟦ ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀)) ⟧₀ ⟦ close b s ⟧₀ ⟦ n ⟧₀)
--  ＝⟨ refl ⟩
-- ⟦ close a s · (⌜η⌝ · n) · Rec (ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀))) (close b s) n ⟧₀
--  ∎
-- where
--  e0 : {τ : type} (i : ∈Cxt τ Γ)
--     → ⟦ weaken, ι (weaken, ι (s i)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
--     ≡ ⟦ s i ⟧₀
--  e0 {τ} i =
--   ⟦ weaken, ι (weaken, ι (s i)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
--    ≡＝⟨ ⟦weaken,-weaken,⟧ ⟨⟩ (succ ⟦ n ⟧₀) ⟦ n ⟧₀ (s i) refl (λ ()) ⟩
--   ⟦ s i ⟧₀
--    ∎
--
--  e4 : {τ : type} (i : ∈Cxt τ Γ)
--     → ⟦ weaken, ι (s i) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)
--     ≡ ⟦ s i ⟧₀
--  e4 {τ} i = ⟦weaken,⟧ (s i) ι _ _ (λ ())
--
--  e1 : ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
--     ≡ ⟦ close a s ⟧₀
--  e1 =
--   ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
--    ≡⟨ ⟦close⟧ (weaken, ι (weaken, ι a))
--               (Subƛ (Subƛ s))
--               _ _
--               (【≡】-is-refl‚ _ _ (【≡】-is-refl‚ _ _ (λ ()) refl) refl)
--               (【≡】-【Sub】-Subƛ' _ _ _ refl refl) ⟩
--   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀))
--    ≡⟨ ≡-refl (weaken, ι (weaken, ι a)) _ _ (【≡】-【Sub】-Subƛ2 s (succ ⟦ n ⟧₀) ⟦ n ⟧₀ refl refl) ⟩
--   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub₀】 s ‚ succ ⟦ n ⟧₀ ‚ ⟦ n ⟧₀)
--    ≡⟨ ⟦weaken,-weaken,⟧ (【Sub₀】 s) (succ ⟦ n ⟧₀) ⟦ n ⟧₀ a refl (【≡】-is-refl-【Sub₀】 s) ⟩
--   ⟦ a ⟧ (【Sub₀】 s)
--    ≡＝⟨ ≡-symm (⟦close⟧' a s) ⟩
--   ⟦ close a s ⟧₀
--    ∎
--
--  e3 : ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀) ≡ ⟦ close b s ⟧₀
--  e3 =
--   ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)
--    ≡⟨ ⟦close⟧ (weaken, ι b)
--               (Subƛ s)
--               _ _
--               (【≡】-is-refl‚ _ _ (λ ()) refl)
--               (【≡】-【Sub】-Subƛ _ _ refl) ⟩
--   ⟦ weaken, ι b ⟧ (【Sub】 (Subƛ s) (⟨⟩ ‚ succ ⟦ n ⟧₀))
--    ≡⟨ ⟦weaken,⟧ b ι _ _ (【≡】-is-refl-【⊆】-⊆,-【Sub】-Subƛ s _ refl) ⟩
--   ⟦ b ⟧ (【⊆】 (⊆, Γ ι) (【Sub】 (Subƛ s) (⟨⟩ ‚ succ ⟦ n ⟧₀)))
--    ≡⟨ ≡-refl b (【⊆】 (⊆, Γ ι) (【Sub】 (Subƛ s) (⟨⟩ ‚ succ ⟦ n ⟧₀))) (【Sub₀】 s) e4 ⟩
--   ⟦ b ⟧ (【Sub₀】 s)
--    ≡＝⟨ ≡-symm (⟦close⟧' b s) ⟩
--   ⟦ close b s ⟧₀
--    ∎
--
--  e6 : (i : ℕ) {τ : type} (j : ∈Cxt τ Γ)
--     → ⟦ weaken, ι (weaken, ι (s j)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i)
--     ≡ ⟦ s j ⟧₀
--  e6 i {τ} j = ≡-trans (⟦weaken,-weaken,⟧-as-⟦weaken,⟧ ⟨⟩ i (succ ⟦ n ⟧₀) i (s j) refl (λ ()))
--                       (⟦weaken,⟧ (s j) ι _ _ (λ ()))
--
--  e5 : (i : ℕ) (u v : 〖 B-type〖 σ 〗 A 〗)
--     → u ≡ v
--     → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
--     ≡ ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
--  e5 i u v e =
--   ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
--    ≡⟨ ⟦close⟧ (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i)
--        (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i))
--        (【≡】-is-refl‚ _ _ (【≡】-is-refl‚ _ _ (λ ()) refl) refl)
--        (【≡】-【Sub】-Subƛ' _ _ _ refl refl)
--        _ _ (λ a₁ b₁ a≡₁ a₂ b₂ a≡₂ → a≡₁ _ _ refl) _ _ e ⟩
--   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i)) (η⋆ i) v
--    ≡⟨ ≡-refl (weaken, ι (weaken, ι a))
--              _ _
--              (【≡】-【Sub】-Subƛ2 s (succ ⟦ n ⟧₀) i refl refl)
--              _ _ (η⋆ι≡ i) _ _ (≡ᵣ e) ⟩
--   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub₀】 s ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) v
--    ≡⟨ ⟦weaken,-weaken,⟧ (【Sub₀】 s) (succ ⟦ n ⟧₀)
--                         i a refl
--                         (【≡】-is-refl-【Sub₀】 s)
--                         _ _ (η⋆ι≡ i) _ _ (≡ᵣ e) ⟩
--   ⟦ a ⟧ (【Sub₀】 s ) (η⋆ i) v
--    ≡⟨ ≡-symm (⟦close⟧ a s (【⊆】 (∈CxtS ι) (⟨⟩ ‚ i))
--                      (【Sub₀】 s) (λ ())
--                      (【≡】-is-refl-【Sub₀】 s)
--                      _ _ (η⋆ι≡ i) _ _ (≡ᵣ e)) ⟩
--   ⟦ close a s ⟧ (【⊆】 (⊆, 〈〉 ι) (⟨⟩ ‚ i)) (η⋆ i) v
--    ≡＝⟨ ≡-symm (⟦weaken,⟧ (close a s) ι _ _ (λ ()) _ _ (η⋆ι≡ i) _ _ (≡ᵣ e)) ⟩
--   ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
--    ∎
--
--  e7 : (i j : ℕ) → i ＝ j → (u v : 〖 B-type〖 σ 〗 A 〗)
--     → u ≡ v
--     → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
--     ≡ ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ j) (η⋆ j) v
--  e7 i .i refl u v e = e5 i u v e
--
--  e2 : rec (λ x → ⟦ close (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x))
--        (⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀))
--        ⟦ n ⟧₀
--     ≡ rec ⟦ ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀)) ⟧₀ ⟦ close b s ⟧₀ ⟦ n ⟧₀
--  e2 = rec-respects-≡ {_}
--        {λ x → ⟦ close (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀ ‚ x)}
--        {⟦ ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀)) ⟧₀}
--        {⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ succ ⟦ n ⟧₀)}
--        {⟦ close b s ⟧₀}
--        {⟦ n ⟧₀} {⟦ n ⟧₀}
--        e7 e3 (≡-refl₀ n)
--
---- as opposed to Rnorm-lemma-rec-succ, this one does not "reduce" as much
--Rnorm-lemma-rec-succ2 : {A σ : type} {Γ : Cxt}
--                        (a : T Γ (B-type〖 ι ⇒ σ ⇒ σ 〗 A))
--                        (b : T Γ (B-type〖 σ 〗 A))
--                        (n : T₀ ι)
--                        (s : Sub₀ Γ)
--                      → ⟦ close (ƛ (Rec (ƛ (weaken, ι (weaken, ι a) · (⌜η⌝ · ν₀))) (weaken, ι b) ν₀)) s  · n ⟧₀
--                      ≡ ⟦ Rec (ƛ (weaken, ι (close a s) · (⌜η⌝ · ν₀))) (close b s) n ⟧₀
--Rnorm-lemma-rec-succ2 {A} {σ} {Γ} a b n s =
-- rec (λ y → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ y) (η⋆ y))
--     (⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀))
--     ⟦ n ⟧₀
--  ≡＝⟨ rec-respects-≡ {_}
--         {λ y → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ y) (η⋆ y)}
--         {λ y → ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ y) (η⋆ y)}
--         {⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀)} {⟦ close b s ⟧₀}
--         {⟦ n ⟧₀} {⟦ n ⟧₀} e5 e1 refl ⟩
-- rec (λ y → ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ y) (η⋆ y))
--     ⟦ close b s ⟧₀
--     ⟦ n ⟧₀
--  ∎
-- where
--  e4 : (i : ℕ) {τ : type} (j : ∈Cxt τ Γ)
--     → ⟦ weaken, ι (weaken, ι (s j)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i)
--     ≡ ⟦ s j ⟧₀
--  e4 i {τ} j = ⟦weaken,-weaken,⟧ ⟨⟩ ⟦ n ⟧₀ i (s j) refl (λ ())
--
--  e3 : (i : ℕ) (u v : 〖 B-type〖 σ 〗 A 〗)
--     → u ≡ v
--     → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
--     ≡ ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
--  e3 i u v e =
--   ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
--    ≡⟨ ⟦close⟧ (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i)
--        (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i))
--        (【≡】-is-refl‚ _ _ (【≡】-is-refl‚ _ _ (λ ()) refl) refl)
--        (【≡】-【Sub】-Subƛ' _ _ _ refl refl)
--        _ _ (η⋆ι≡ i) _ _ e ⟩
--   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub】 (Subƛ (Subƛ s)) (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i)) (η⋆ i) v
--    ≡⟨ ≡-refl (weaken, ι (weaken, ι a))
--              _ _ (【≡】-【Sub】-Subƛ2 s (⟦ n ⟧₀) i refl refl)
--              _ _ (η⋆ι≡ i) _ _ (≡ᵣ e) ⟩
--   ⟦ weaken, ι (weaken, ι a) ⟧ (【Sub₀】 s ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) v
--    ≡⟨ ⟦weaken,-weaken,⟧ (【Sub₀】 s) (⟦ n ⟧₀)
--                         i a refl
--                         (【≡】-is-refl-【Sub₀】 s)
--                         _ _ (η⋆ι≡ i) _ _ (≡ᵣ e) ⟩
--   ⟦ a ⟧ (【Sub₀】 s ) (η⋆ i) v
--    ≡⟨ ≡-symm (⟦close⟧ a s (【⊆】 (∈CxtS ι) (⟨⟩ ‚ i))
--                      (【Sub₀】 s) (λ ())
--                      (【≡】-is-refl-【Sub₀】 s)
--                      _ _ (η⋆ι≡ i) _ _ (≡ᵣ e)) ⟩
--   ⟦ close a s ⟧ (【⊆】 (⊆, 〈〉 ι) (⟨⟩ ‚ i)) (η⋆ i) v
--    ≡＝⟨ ≡-symm (⟦weaken,⟧ (close a s) ι _ _ (λ ()) _ _ (η⋆ι≡ i) _ _ (≡ᵣ e)) ⟩
--   ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ i) (η⋆ i) v
--    ∎
--
--  e5 : (i j : ℕ) → i ＝ j → (u v : 〖 B-type〖 σ 〗 A 〗)
--     → u ≡ v
--     → ⟦ close (weaken, ι (weaken, ι a)) (Subƛ (Subƛ s)) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀ ‚ i) (η⋆ i) u
--     ≡ ⟦ weaken, ι (close a s) ⟧ (⟨⟩ ‚ j) (η⋆ j) v
--  e5 i .i refl u v e = e3 i u v e
--
--  e2 : {τ : type} (i : ∈Cxt τ Γ)
--     → ⟦ weaken, ι (s i) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀)
--     ≡ ⟦ s i ⟧₀
--  e2 {τ} i = ⟦weaken,⟧ (s i) ι _ _ (λ ())
--
--  e1 : ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀) ≡ ⟦ close b s ⟧₀
--  e1 =
--   ⟦ close (weaken, ι b) (Subƛ s) ⟧ (⟨⟩ ‚ ⟦ n ⟧₀)
--    ≡⟨ ⟦close⟧ (weaken, ι b) (Subƛ s)
--               _ _ (【≡】-is-refl‚ _ _ (λ ()) refl)
--               (【≡】-【Sub】-Subƛ _ _ refl) ⟩
--   ⟦ weaken, ι b ⟧ (【Sub】 (Subƛ s) (⟨⟩ ‚ ⟦ n ⟧₀))
--    ≡⟨ ⟦weaken,⟧ b ι _ _ (【≡】-is-refl-【⊆】-⊆,-【Sub】-Subƛ s _ refl) ⟩
--   ⟦ b ⟧ (【⊆】 (⊆, Γ ι) (【Sub】 (Subƛ s) (⟨⟩ ‚ ⟦ n ⟧₀)))
--    ≡⟨ ≡-refl b (【⊆】 (⊆, Γ ι) (【Sub】 (Subƛ s) (⟨⟩ ‚ ⟦ n ⟧₀))) (【Sub₀】 s) e2 ⟩
--   ⟦ b ⟧ (【Sub₀】 s)
--    ≡＝⟨ ≡-symm (⟦close⟧' b s) ⟩
--   ⟦ close b s ⟧₀
--    ∎
--
--⟦⌜Rec⌝⟧-aux : {A : type} {σ : type} {Γ : Cxt}
--              (s : 【 B-context【 Γ 】 A 】)
--              (a : T Γ (ι ⇒ σ ⇒ σ))
--              (b : T Γ σ)
--              (a₁ b₁ : ℕ)
--            → a₁ ＝ b₁
--            → 【≡】-is-refl s
--            → rec (λ y → ⟦ ⌜ a ⌝ ⟧ s (η⋆ y)) (⟦ ⌜ b ⌝ ⟧ s) a₁
--            ≡ rec (λ y → ⟦ weaken, ι (weaken, ι ⌜ a ⌝) ⟧ (s ‚ b₁ ‚ y) (η⋆ y))
--                  (⟦ weaken, ι ⌜ b ⌝ ⟧ (s ‚ b₁))
--                  b₁
--⟦⌜Rec⌝⟧-aux {A} {σ} {Γ} s a b a₁ b₁ a≡₁ r =
-- rec-respects-≡
--  {_} {λ y → ⟦ ⌜ a ⌝ ⟧ s (η⋆ y)} {λ y → ⟦ weaken, ι (weaken, ι ⌜ a ⌝) ⟧ (s ‚ b₁ ‚ y) (η⋆ y)}
--  {⟦ ⌜ b ⌝ ⟧ s} {⟦ weaken, ι ⌜ b ⌝ ⟧ (s ‚ b₁)} {a₁} {b₁}
--  c (≡-symm (⟦weaken,⟧ ⌜ b ⌝ ι (s ‚ b₁) s r)) a≡₁
-- where
--  c : (a₂ b₂ : ℕ)
--    → a₂ ＝ b₂
--    → (a₃ b₃ : 〖 B-type〖 σ 〗 A 〗)
--    → a₃ ≡ b₃
--    → ⟦ ⌜ a ⌝ ⟧ s (η⋆ a₂) a₃
--    ≡ ⟦ weaken, ι (weaken, ι ⌜ a ⌝) ⟧ (s ‚ b₁ ‚ b₂) (η⋆ b₂) b₃
--  c a₂ b₂ a≡₂ a₃ b₃ a≡₃ =
--   ≡-symm (⟦weaken,-weaken,⟧ s b₁ b₂ ⌜ a ⌝ refl r (η⋆ b₂) (η⋆ a₂) (≡η⋆ (≡-symm a≡₂)) b₃ a₃ (≡-symm a≡₃))
--
--⟦⌜Rec⌝⟧ : {A : type} {σ : type} {Γ : Cxt}
--          (s : 【 B-context【 Γ 】 A 】)
--          (a : T Γ (ι ⇒ σ ⇒ σ))
--          (b : T Γ σ)
--          (c : T Γ ι)
--        → 【≡】-is-refl s
--        → ⟦ ⌜_⌝  {Γ} {σ} {A} (Rec a b c) ⟧ s
--        ≡ ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
--            · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀))
--            · ⌜ c ⌝ ⟧ s
--⟦⌜Rec⌝⟧ {A} {σ} {Γ} s a b c r =
-- ⟦ ⌜_⌝  {Γ} {σ} {A} (Rec a b c) ⟧ s
--  ＝≡⟨ refl ⟩
-- ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ} ⟧ (s ‚ ⟦ ⌜ a ⌝ ⟧ s ‚ ⟦ ⌜ b ⌝ ⟧ s)
--  (λ x → rec (λ y → ⟦ ⌜ a ⌝ ⟧ s (η⋆ y)) (⟦ ⌜ b ⌝ ⟧ s) x)
--  (⟦ ⌜ c ⌝ ⟧ s)
--  ≡＝⟨ ⟦⌜Kleisli-extension⌝⟧ (s ‚ ⟦ ⌜ a ⌝ ⟧ s ‚ ⟦ ⌜ b ⌝ ⟧ s) s
--       (λ x → rec (λ y → ⟦ ⌜ a ⌝ ⟧ s (η⋆ y)) (⟦ ⌜ b ⌝ ⟧ s) x)
--       (λ x → rec (λ y → ⟦ weaken, ι (weaken, ι ⌜ a ⌝) ⟧ (s ‚ x ‚ y) (η⋆ y)) (⟦ weaken, ι ⌜ b ⌝ ⟧ (s ‚ x)) x)
--       (λ a₁ b₁ a≡ → ⟦⌜Rec⌝⟧-aux s a b a₁ b₁ a≡ r)
--       (⟦ ⌜ c ⌝ ⟧ s) (⟦ ⌜ c ⌝ ⟧ s) (≡-refl ⌜ c ⌝ s s r) ⟩
-- ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
--   · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀))
--   · ⌜ c ⌝ ⟧ s
--  ∎
--
--⟦close-⌜Rec⌝⟧ : {A : type} {σ : type} {Γ : Cxt}
--                (s : IB【 Γ 】 A)
--                (a : T Γ (ι ⇒ σ ⇒ σ))
--                (b : T Γ σ)
--                (c : T Γ ι)
--              → ⟦ close (⌜_⌝  {Γ} {σ} {A} (Rec a b c)) s ⟧₀
--              ≡ ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
--                   · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s
--                   · close ⌜ c ⌝ s ⟧₀
--⟦close-⌜Rec⌝⟧ {A} {σ} {Γ} s a b c =
-- ⟦ close (⌜_⌝  {Γ} {σ} {A} (Rec a b c)) s ⟧₀
--  ≡⟨ ⟦close⟧' ⌜ Rec a b c ⌝ s ⟩
-- ⟦ ⌜_⌝  {Γ} {σ} {A} (Rec a b c) ⟧ (【Sub₀】 s)
--  ≡⟨ ⟦⌜Rec⌝⟧ (【Sub₀】 s) a b c (【≡】-is-refl-【Sub₀】 s) ⟩
-- ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
--   · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀))
--   · ⌜ c ⌝ ⟧ (【Sub₀】 s)
--  ≡＝⟨ ≡-symm (⟦close⟧' (⌜Kleisli-extension⌝ {ι} {A} {σ}
--                        · (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀))
--                        · ⌜ c ⌝) s) ⟩
-- ⟦ close ⌜Kleisli-extension⌝ s
--   · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s
--   · close ⌜ c ⌝ s ⟧₀
--  ＝⟨ ap (λ k → ⟦ k · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s
--                    · close ⌜ c ⌝ s ⟧₀)
--         ((close-⌜Kleisli-extension⌝ s) ⁻¹) ⟩
-- ⟦ ⌜Kleisli-extension⌝ {ι} {A} {σ}
--   · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ a ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ b ⌝) ν₀)) s
--   · close ⌜ c ⌝ s ⟧₀
--  ∎
--
--is-dialogue-for-zero : ⟦ ⌜zero⌝ ⟧₀ ≣⋆ church-encode zero'
--is-dialogue-for-zero A η' β' eη eβ = eη 0
--
--≣⋆-B⋆-functor : {X Y : 𝓤 ̇ } {d d' : {A : type} → B⋆ X 〖 A 〗} (f : X → Y)
--              → d ≣⋆ d'
--              → B⋆-functor f d ≣⋆ B⋆-functor f d'
--≣⋆-B⋆-functor {_} {X} {Y} {d} {d'} f eq A η' β' eη eβ =
-- eq _ _ _ (λ x → eη (f x)) eβ
--
--Rnorm-lemma : {Γ : Cxt} {σ : type}
--              (xs : B【 Γ 】) (ys : {A : type} → IB【 Γ 】 A)
--              (t : T Γ σ)
--            → Rnorms xs ys
--            → Rnorm (B⟦ t ⟧ xs) (close ⌜ t ⌝ ys)
--
---- The zero term is always equal to the leaf holding zero.
--Rnorm-lemma xs ys Zero Rnorm-xs = is-dialogue-for-zero
--
---- If at a leaf, apply successor to leaf value.
---- If at a branching node, propagate the successor one level down.
--Rnorm-lemma xs ys (Succ t) Rnorm-xs = c
-- where
--  ind : ⟦ close ⌜ t ⌝ ys ⟧₀ ≣⋆ church-encode (B⟦ t ⟧ xs)
--  ind = Rnorm-lemma xs ys t Rnorm-xs
--
--  c : B⋆-functor succ ⟦ close ⌜ t ⌝ ys ⟧₀ ≣⋆ church-encode (B-functor succ (B⟦ t ⟧ xs))
--  c = ≣⋆-trans (≣⋆-B⋆-functor succ ind) (church-encode-is-natural succ (B⟦ t ⟧ xs))
--
--Rnorm-lemma {Γ} {σ} xs ys (Rec t u v) Rnorm-xs =
-- Rnorm-respects-≡
--   (rec' (B⟦ t ⟧ xs) (B⟦ u ⟧ xs) (B⟦ v ⟧ xs))
--   (⌜Kleisli-extension⌝
--    · close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ t ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ u ⌝) ν₀)) ys
--    · close ⌜ v ⌝ ys)
--   (close ⌜ Rec t u v ⌝ ys)
--   (λ A → ≡-symm (⟦close-⌜Rec⌝⟧ {A} ys t u v))
--   c1
-- where
--  rt : (x  : B〖 ι 〗) (x' : {A : type} → T₀ (B-type〖 ι 〗 A)) (rx : Rnorm {ι} x x')
--       (y  : B〖 σ 〗) (y' : {A : type} → T₀ (B-type〖 σ 〗 A)) (ry : Rnorm {σ} y y')
--     → Rnorm (B⟦ t ⟧ xs x y) (close ⌜ t ⌝ ys · x' · y')
--  rt = Rnorm-lemma xs ys t Rnorm-xs
--
--  rn : ℕ → B〖 σ 〗
--  rn n = rec (B⟦ t ⟧ xs ∘ η) (B⟦ u ⟧ xs) n
--
--  rn' : {A : type} → T₀ (ι ⇒ B-type〖 σ 〗 A)
--  rn' = close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ t ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ u ⌝) ν₀)) ys
--
--  rnn' : (n : ℕ) → Rnorm (rn n) (rn' · numeral n)
--  rnn' zero = r
--   where
--    r : Rnorm (B⟦ u ⟧ xs) (rn' · Zero)
--    r = Rnorm-respects-≡
--         (B⟦ u ⟧ xs) (close ⌜ u ⌝ ys) (rn' · Zero)
--         (λ A → ≡-symm (Rnorm-lemma-rec-zero {A} (ƛ (weaken, ι (weaken, ι ⌜ t ⌝) · (⌜η⌝ · ν₀))) ⌜ u ⌝ ys))
--         (Rnorm-lemma xs ys u Rnorm-xs)
--  rnn' (succ n) = r
--   where
--    r : Rnorm (B⟦ t ⟧ xs (η n) (rn n)) (rn' · Succ (numeral n))
--    r = Rnorm-respects-≡
--         (B⟦ t ⟧ xs (η n) (rn n))
--         (close ⌜ t ⌝ ys
--          · (⌜η⌝ · numeral n)
--          · Rec (ƛ (weaken, ι (close ⌜ t ⌝ ys) · (⌜η⌝ · ν₀))) (close ⌜ u ⌝ ys) (numeral n))
--         (rn' · Succ (numeral n))
--         (λ A → ≡-symm (Rnorm-lemma-rec-succ {A} ⌜ t ⌝ ⌜ u ⌝ (numeral n) ys))
--         (rt (η n) (⌜η⌝ · numeral n) (Rnorm-ηnumeral n)
--             (rn n) (Rec (ƛ (weaken, ι (close ⌜ t ⌝ ys) · (⌜η⌝ · ν₀))) (close ⌜ u ⌝ ys) (numeral n))
--             (Rnorm-respects-≡
--               (rn n)
--               (close (ƛ (Rec (ƛ (weaken, ι (weaken, ι ⌜ t ⌝) · (⌜η⌝ · ν₀))) (weaken, ι ⌜ u ⌝) ν₀)) ys
--                · numeral n)
--               (Rec (ƛ (weaken, ι (close ⌜ t ⌝ ys) · (⌜η⌝ · ν₀))) (close ⌜ u ⌝ ys) (numeral n))
--               (λ A → Rnorm-lemma-rec-succ2 {A} ⌜ t ⌝ ⌜ u ⌝ (numeral n) ys)
--               (rnn' n)))
--
--  rnn'' : (n : ℕ) (n' : T₀ ι) → Rnorm (η n) (⌜η⌝ · n') → Rnorm (rn n) (rn' · n')
--  rnn'' n n' r =
--   Rnorm-respects-≡
--    (rn n) (rn' · numeral n) (rn' · n')
--    (λ A → ≡-symm (≡-refl₀ rn' _ _ (Rnormη⌜η⌝ n n' r)))
--    (rnn' n)
--
--  c1 : Rnorm (Kleisli-extension rn (B⟦ v ⟧ xs))
--             (⌜Kleisli-extension⌝ · rn' · close ⌜ v ⌝ ys)
--  c1 = Rnorm-kleisli-lemma rn rn' rnn' (B⟦ v ⟧ xs) (close ⌜ v ⌝ ys) (Rnorm-lemma xs ys v Rnorm-xs)
--
--Rnorm-lemma xs ys (ν i) Rnorm-xs = Rnorm-xs i
--
--Rnorm-lemma xs ys (ƛ t) Rnorm-xs u u' Rnorm-u =
-- Rnorm-respects-≡
--  (B⟦ t ⟧ (xs ‚‚ u))
--  (close ⌜ t ⌝ (Sub,, ys u'))
--  (ƛ (close ⌜ t ⌝ (Subƛ ys)) · u')
--  eq
--  (Rnorm-lemma (xs ‚‚ u) (Sub,, ys u') t Rnorm-xs,,u)
-- where
--  eq : (A : type) → ⟦ close ⌜ t ⌝ (Sub,, ys u') ⟧₀ ≡[ (B-type〖 _ 〗 A) ] ⟦ ƛ (close ⌜ t ⌝ (Subƛ ys)) · u' ⟧₀
--  eq A =
--   ⟦ close ⌜ t ⌝ (Sub,, ys u') ⟧₀
--    ≡⟨ ⟦close⟧' ⌜ t ⌝ (Sub,, ys u') ⟩
--   ⟦ ⌜ t ⌝ ⟧ (【Sub₀】 (Sub,, ys u'))
--    ≡⟨ ≡-refl ⌜ t ⌝ (【Sub₀】 (Sub,, ys u')) (【Sub】 (Subƛ ys) (⟨⟩ ‚ ⟦ u' ⟧₀)) (【≡】-【Sub】-Sub,, ys u') ⟩
--   ⟦ ⌜ t ⌝ ⟧ (【Sub】 (Subƛ ys) (⟨⟩ ‚ ⟦ u' ⟧₀))
--    ≡＝⟨ ≡-symm (⟦close⟧ ⌜ t ⌝ (Subƛ ys)
--                        _ _ (【≡】-is-refl‚ _ _ (λ ()) (≡-refl₀ u'))
--                        (【≡】-【Sub】-Subƛ ys _ (≡-refl₀ u'))) ⟩
--   ⟦ ƛ (close ⌜ t ⌝ (Subƛ ys)) · u' ⟧₀
--    ∎
--
--  Rnorm-xs,,u : Rnorms (xs ‚‚ u) (Sub,, ys u')
--  Rnorm-xs,,u (∈Cxt0 _)   = Rnorm-u
--  Rnorm-xs,,u (∈CxtS _ i) = Rnorm-xs i
--
--Rnorm-lemma xs ys (t · u) Rnorm-xs =
-- Rnorm-lemma xs ys t Rnorm-xs (B⟦ u ⟧ xs) (close ⌜ u ⌝ ys) (Rnorm-lemma xs ys u Rnorm-xs)
--
---- a consequence of Rnorm-lemma for terms of type ι
--Rnorm-lemmaι : (t : T₀ ι) (α : Baire)
--             → dialogue⋆ ⟦ ⌜ t ⌝ ⟧₀ ≡ dialogue⋆ (church-encode B⟦ t ⟧₀)
--Rnorm-lemmaι t α =
-- dialogue⋆ ⟦ ⌜ t ⌝ ⟧₀
--  ≡⟨ ≡-symm (⟦closeν⟧ ⌜ t ⌝ _ (λ ()) _ _ η≡ _ _ β≡) ⟩
-- dialogue⋆ ⟦ close ⌜ t ⌝ ν ⟧₀
--  ≡＝⟨ Rnorm-lemma ⟪⟫ ν t (λ ()) ((ι ⇒ ι) ⇒ ι) η' β' eη eβ ⟩
-- dialogue⋆ (church-encode B⟦ t ⟧₀)
--  ∎
-- where
--  η' : ℕ → Baire → ℕ
--  η' = λ z α → z
--
--  β' : (ℕ → Baire → ℕ) → ℕ → Baire → ℕ
--  β' = λ φ x α → φ (α x) α
--
--  η≡ : η' ≡ η'
--  η≡ a b a≡ a₁ b₁ a≡₁ = a≡
--
--  β≡ : β' ≡ β'
--  β≡ a b a≡ a₁ b₁ a≡₁ a₂ b₂ a≡₂ = a≡ _ _ (a≡₂ _ _ a≡₁) _ _ a≡₂
--
--  eη : extη η'
--  eη x a b a≡ = refl
--
--  eβ : extβ β'
--  eβ a b x .x refl a≡ a₁ b₁ a≡₁ =
--   a≡ _ _ _ a≡₁ ∙ a≡b _ _ (a≡₁ _ _ refl ⁻¹) ⁻¹ ∙ a≡ _ _ _ a≡₁
--   where
--    a≡b : (n m : ℕ) → n ＝ m → a n a₁ ＝ b m b₁
--    a≡b n .n refl = a≡ _ _ _ a≡₁
--
--Rnorm-lemma₀ : {σ : type} (t : T₀ σ) → Rnorm B⟦ t ⟧₀ ⌜ t ⌝
--Rnorm-lemma₀ {σ} t =
-- Rnorm-respects-≡
--  B⟦ t ⟧₀ (close ⌜ t ⌝ ν) ⌜ t ⌝
--  (λ A → ⟦closeν⟧ ⌜ t ⌝ _ (λ ()))
--  (Rnorm-lemma ⟪⟫ ν t (λ ()))
--
--Rnorm-generic : (u : B ℕ) (u' : {A : type} → T₀ (⌜B⌝ ι A))
--              → is-dialogue-for u u'
--              → is-dialogue-for (generic u) (⌜generic⌝ · u')
--Rnorm-generic u u' ru =
-- Rnorm-kleisli-lemma (β η) (⌜β⌝ · ⌜η⌝) c u u' ru
-- where
--  c : (x : ℕ)
--    → β⋆ η⋆ ⟦ numeral x ⟧₀ ≣⋆ β⋆ η⋆ x
--  c x A η' β' eη eβ = eβ _ _ _ _ (⟦numeral⟧ x) eη
--
--⌜dialogue-tree⌝-correct : (t : T₀ ((ι ⇒ ι) ⇒ ι))
--                          (α : Baire)
--                        → ⟦ t ⟧₀ α ＝ dialogue⋆ ⟦ ⌜dialogue-tree⌝ t ⟧₀ α
--⌜dialogue-tree⌝-correct t α =
-- dialogue-tree-correct t α
-- ∙ dialogues-agreement (dialogue-tree t) α
-- ∙ e ⁻¹
-- where
--  η' : ℕ → Baire → ℕ
--  η' = λ z i → z
--
--  β' : (ℕ → Baire → ℕ) → ℕ → Baire → ℕ
--  β' = λ φ x α → φ (α x) α
--
--  rt : Rnorm B⟦ t ⟧₀ ⌜ t ⌝
--  rt = Rnorm-lemma₀ {(ι ⇒ ι) ⇒ ι} t
--
--  eη : extη η'
--  eη x a b a≡ = refl
--
--  eβ : extβ β'
--  eβ f g x .x refl f≡ a b a≡ =
--   f≡ _ _ _ a≡ ∙ a≡b _ _ (a≡ _ _ refl ⁻¹) ⁻¹ ∙ f≡ _ _ _ a≡
--   where
--    a≡b : (n m : ℕ) → n ＝ m → f n a ＝ g m b
--    a≡b n .n refl = f≡ _ _ _ a≡
--
--  eα : (a b : ℕ) → a ＝ b → α a ＝ α b
--  eα a .a refl = refl
--
--  e : ⟦ ⌜ t ⌝ · ⌜generic⌝ ⟧₀ η' β' α ≡ church-encode (B⟦ t ⟧₀ generic) η' β' α
--  e = rt generic ⌜generic⌝ Rnorm-generic ((ι ⇒ ι) ⇒ ι) η' β' eη eβ _ _ eα
--
--⌜dialogue⌝ : {Γ : Cxt}
--           → T (B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι)) (⌜B⌝ ι ((ι ⇒ ι) ⇒ ι))
--           → T (B-context【 Γ 】 ((ι ⇒ ι) ⇒ ι)) ((ι ⇒ ι) ⇒ ι)
--⌜dialogue⌝ {Γ} t = t · ƛ (ƛ ν₁) · ƛ (ƛ (ƛ (ν₂ · (ν₀ · ν₁) · ν₀)))
--
---- Same as ⌜dialogue-tree⌝-correct but using an internal dialogue function
--⌜dialogue-tree⌝-correct' : (t : T₀ ((ι ⇒ ι) ⇒ ι))
--                           (α : Baire)
--                         → ⟦ t ⟧₀ α ＝ ⟦ ⌜dialogue⌝ (⌜dialogue-tree⌝ t) ⟧₀ α
--⌜dialogue-tree⌝-correct' t α = ⌜dialogue-tree⌝-correct t α

\end{code}
