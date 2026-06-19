Tom de Jong, 18 June 2026.

\begin{code}

{-# OPTIONS --rewriting --without-K #-}

open import MLTT.Spartan
open import UF.Univalence

module SyntheticHomotopyTheory.Circle.FundamentalGroup
        (ua : is-univalent 𝓤₀)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : funext 𝓤₀ 𝓤₀
 fe = univalence-gives-funext ua

open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Singleton-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Yoneda

open import SyntheticHomotopyTheory.Circle.Integers
open import SyntheticHomotopyTheory.Circle.Integers-Properties
open import SyntheticHomotopyTheory.Circle.Integers-SymmetricInduction
open import SyntheticHomotopyTheory.Circle.WithRewriting

private
 𝕤 : ℤ ＝ ℤ
 𝕤 = eqtoid ua ℤ ℤ succ-ℤ-≃

 C : S¹ → 𝓤₀ ̇
 C = S¹-recursion (𝓤₀ ̇ ) ℤ 𝕤

 _ : ap C loop ＝ 𝕤
 _ = refl

 C-transport-lemma₁
  : {X : 𝓤 ̇ } (f : ℤ → X)
  → transport (λ - → C - → X) loop f ＝ f ∘ transport C (loop ⁻¹)
 C-transport-lemma₁ f = transport-along-→' C loop f

 C-transport-lemma₂ : transport C loop ＝ succ-ℤ
 C-transport-lemma₂ = transport-is-idtofun-after-ap C loop ∙ II
  where
   I : idtoeq ℤ ℤ 𝕤 ＝ succ-ℤ-≃
   I = idtoeq-eqtoid ua ℤ ℤ succ-ℤ-≃

   II : ⌜ idtoeq ℤ ℤ (ap C loop) ⌝ ＝ succ-ℤ
   II = ap ⌜_⌝ I

 C-transport-lemma₂' : transport C (loop ⁻¹) ＝ pred-ℤ
 C-transport-lemma₂' = transport-is-idtofun-after-ap⁻¹ C loop ∙ II
  where
   I : idtoeq ℤ ℤ 𝕤 ＝ succ-ℤ-≃
   I = idtoeq-eqtoid ua ℤ ℤ succ-ℤ-≃

   II : ⌜ idtoeq ℤ ℤ (ap C loop) ⌝⁻¹ ＝ pred-ℤ
   II = ap ⌜_⌝⁻¹ I

 ΣC-mapping-out-≃ : (X : 𝓤₀ ̇ ) → ((Σ s ꞉ S¹ , C s) → X) ≃ X
 ΣC-mapping-out-≃ X =
  ((Σ s ꞉ S¹ , C s) → X)                                  ≃⟨ I   ⟩
  (Π s ꞉ S¹ , (C s → X))                                  ≃⟨ II  ⟩
  (Σ f ꞉ (ℤ → X) , transport (λ - → C - → X) loop f ＝ f) ≃⟨ III ⟩
  (Σ f ꞉ (ℤ → X) , f ∘ transport C (loop ⁻¹) ＝ f)        ≃⟨ IV  ⟩
  (Σ f ꞉ (ℤ → X) , f ∘ pred-ℤ ＝ f)                       ≃⟨ V   ⟩
  X                                                       ■
   where
    I   = curry-uncurry' fe fe
    II  = S¹-dependent-universal-property-≃ fe (λ s → C s → X)
    III = Σ-cong (λ f → ＝-cong-l _ _ (C-transport-lemma₁ f))
    IV  = Σ-cong (λ f → ＝-cong-l _ _ (ap (f ∘_) C-transport-lemma₂'))
    V   = maps-equalizing-pred-ℤ-and-id-≃ fe X

 private
  nice : (X : 𝓤₀ ̇ ) → ⌜ ΣC-mapping-out-≃ X ⌝ ∘ (consts (Σ C) X) ∼ id
  nice X x = refl

 ΣC-contractible : is-singleton (Σ s ꞉ S¹ , C s)
 ΣC-contractible =
  singleton-if-universal-property⁻
   (λ X → ≃-2-out-of-3-left ⌜ ΣC-mapping-out-≃ X ⌝-is-equiv (id-is-equiv X))

 φ : (s : S¹) → pt ＝ s → C s
 φ s refl = 𝟎

loop-space-is-ℤ : (pt ＝ pt) ≃ ℤ
loop-space-is-ℤ = φ pt , Yoneda-Theorem-forth pt φ ΣC-contractible pt

private
 ϕ = ⌜ loop-space-is-ℤ ⌝

 _ : ϕ refl ＝ 𝟎
 _ = refl

 _ : ϕ ＝ φ pt
 _ = refl

φ-nat : {s₁ s₂ : S¹} (p : s₁ ＝ s₂) (q : pt ＝ s₁)
      → transport C p (φ s₁ q) ＝ φ s₂ (q ∙ p)
φ-nat refl q = refl

eq-2 : (q : pt ＝ pt) → transport C loop (ϕ q) ＝ ϕ (q ∙ loop)
eq-2 = φ-nat loop

eq-2' : (q : pt ＝ pt) → ϕ (q ∙ loop) ＝ succ-ℤ (ϕ q)
eq-2' q =
 ϕ (q ∙ loop)           ＝⟨ (eq-2 q) ⁻¹ ⟩
 transport C loop (ϕ q) ＝⟨ happly C-transport-lemma₂ (ϕ q) ⟩
 succ-ℤ (ϕ q)           ∎

eq-3 : (q : pt ＝ pt) → ϕ (q ∙ loop ⁻¹) ＝ pred-ℤ (ϕ q)
eq-3 q =
 ϕ (q ∙ loop ⁻¹)             ＝⟨ (φ-nat (loop ⁻¹) q) ⁻¹ ⟩
 transport C (loop ⁻¹) (ϕ q) ＝⟨ happly C-transport-lemma₂' (ϕ q) ⟩
 pred-ℤ (ϕ q)                ∎

ϕ-loop : ϕ loop ＝ succ-ℤ 𝟎
ϕ-loop = ap ϕ refl-left-neutral ⁻¹ ∙ eq-2' refl

loop^ : (n : ℕ) → pt ＝ pt
loop^ 0 = refl
loop^ (succ n) = loop^ n ∙ loop

succ-ℤ-commutes-with-ℕ-to-ℤ₊
 : (n : ℕ) → succ-ℤ (ℕ-to-ℤ₊ n) ＝ ℕ-to-ℤ₊ (succ n)
succ-ℤ-commutes-with-ℕ-to-ℤ₊ zero     = refl
succ-ℤ-commutes-with-ℕ-to-ℤ₊ (succ n) = refl

ϕ-loop-iterated : (n : ℕ) → ϕ (loop^ n) ＝ ℕ-to-ℤ₊ n
ϕ-loop-iterated zero = refl
ϕ-loop-iterated (succ n) =
 ϕ (loop^ n ∙ loop)   ＝⟨ eq-2' (loop^ n) ⟩
 succ-ℤ (ϕ (loop^ n)) ＝⟨ ap succ-ℤ (ϕ-loop-iterated n) ⟩
 succ-ℤ (ℕ-to-ℤ₊ n)   ＝⟨ succ-ℤ-commutes-with-ℕ-to-ℤ₊ n ⟩
 ℕ-to-ℤ₊ (succ n)     ∎

loop^⁻ : (n : ℕ) → pt ＝ pt
loop^⁻ 0 = refl
loop^⁻ (succ n) = loop^⁻ n ∙ (loop ⁻¹)

ℕ-to-ℤ₋-on-succ : (n : ℕ) → ℕ-to-ℤ₋ (succ n) ＝ pred-ℤ (ℕ-to-ℤ₋ n)
ℕ-to-ℤ₋-on-succ zero     = refl
ℕ-to-ℤ₋-on-succ (succ n) = refl

ϕ-loop⁻¹-iterated : (n : ℕ) → ϕ (loop^⁻ n) ＝ ℕ-to-ℤ₋ n
ϕ-loop⁻¹-iterated zero = refl
ϕ-loop⁻¹-iterated (succ n) =
 ϕ (loop^⁻ n ∙ (loop ⁻¹)) ＝⟨ eq-3 (loop^⁻ n) ⟩
 pred-ℤ (ϕ (loop^⁻ n))    ＝⟨ ap pred-ℤ (ϕ-loop⁻¹-iterated n) ⟩
 pred-ℤ (ℕ-to-ℤ₋ n)       ＝⟨ (ℕ-to-ℤ₋-on-succ n) ⁻¹ ⟩
 ℕ-to-ℤ₋ (succ n)         ∎

\end{code}