Brendan Hart 2019-2020

\begin{code}

{-# OPTIONS --without-K --safe --exact-split --no-sized-types --no-guardedness --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module PCF.Correctness
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
open import DomainTheory.Basics.LeastFixedPoint pt fe
open import DomainTheory.Basics.Pointed pt fe 𝓤₀
open import DomainTheory.ScottModelOfPCF.PCFCombinators pt fe 𝓤₀
open import Lifting.Lifting 𝓤₀
open import Lifting.Miscelanea-PropExt-FunExt 𝓤₀ pe fe
open import Lifting.Monad 𝓤₀ hiding (μ)
open import Naturals.Properties
open import PCF.AbstractSyntax pt
open import PCF.BigStep pt
open import PCF.Dcpo-Contexts pt fe pe
open import PCF.DcpoProducts pt fe
open import PCF.DcpoProducts-Curry pt fe 𝓤₀
open import PCF.ScottModelTerms pt fe pe
open import PCF.ScottModelTypes pt fe pe
open import PCF.SubstitutionDenotational pt fe pe
open import UF.Miscelanea

open DcpoProductsGeneral 𝓤₀
open IfZeroDenotationalSemantics pe

canonical-numeral-correctness : {n : ℕ} {Γ : Context n} (k : ℕ) (d : ⟨ (【 Γ 】 ⁻) ⟩)
                              → pr₁ ⟦ numeral {_} {Γ} k ⟧ₑ d ＝ η k
canonical-numeral-correctness zero d     = refl
canonical-numeral-correctness (succ n) d =
 pr₁ ⟦ Succ (numeral n) ⟧ₑ d     ＝⟨ refl ⟩
 (𝓛̇ succ ∘ pr₁ ⟦ numeral n ⟧ₑ) d ＝⟨ ap (𝓛̇ succ) IH ⟩
 𝓛̇ succ (η n)                    ＝⟨ refl ⟩
 η (succ n)                      ∎
  where
   IH = canonical-numeral-correctness n d

correctness-IfZero-zero : {n : ℕ} {Γ : Context n}
                          (N t t₁ t₂ : PCF Γ ι)
                        → pr₁ ⟦ t ⟧ₑ ∼ pr₁ ⟦ Zero {_} {Γ} ⟧ₑ
                        → pr₁ ⟦ t₁ ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
                        → pr₁ ⟦ IfZero t t₁ t₂ ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
correctness-IfZero-zero N t t₁ t₂ c₁ c₂ d =
 ((⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d)) ♯) (pr₁ ⟦ t ⟧ₑ d) ＝⟨ i ⟩
 (⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d) ♯) (η zero)         ＝⟨ ii ⟩
 ⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d) zero                 ＝⟨ c₂ d ⟩
 pr₁ ⟦ N ⟧ₑ d                                                     ∎
  where
    i  = ap ((⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d)) ♯) (c₁ d)
    ii = ♯-on-total-element (⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d)) {η zero} ⋆


correctness-IfZero-succ : {n : ℕ} {Γ : Context n}
                          (N t t₁ t₂ : PCF Γ ι)
                          (k : ℕ)
                        → pr₁ ⟦ t ⟧ₑ ∼ pr₁ ⟦ numeral {_} {Γ} (succ k) ⟧ₑ
                        → pr₁ ⟦ t₂ ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
                        → pr₁ ⟦ IfZero t t₁ t₂ ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
correctness-IfZero-succ N t t₁ t₂ k c₁ c₂ d =
 ((⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d)) ♯) (pr₁ ⟦ t ⟧ₑ d)              ＝⟨ i ⟩
 (⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d) ♯) (pr₁ ⟦ Succ (numeral k) ⟧ₑ d) ＝⟨ ii ⟩
 (⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d) ♯) (η (succ k))                  ＝⟨ iii ⟩
 ⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d) (succ k)                          ＝⟨ c₂ d ⟩
 pr₁ ⟦ N ⟧ₑ d                                                                  ∎
  where
    i   = ap ((⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d)) ♯ ) (c₁ d)
    ii  = ap (⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d) ♯)
             (canonical-numeral-correctness (succ k) d)
    iii = ♯-on-total-element
           (⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d)
           (pr₁ ⟦ t₂ ⟧ₑ d))
           {η (succ k)}
           ⋆

correctness-Fix : {n : ℕ} {Γ : Context n} {σ : type}
                  (M : PCF Γ (σ ⇒ σ))
                  (N : PCF Γ σ)
                → pr₁ ⟦ M · Fix M ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
                → pr₁ ⟦ Fix M ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
correctness-Fix {_} {_} {σ} M N c d =
 pr₁ ⟦ Fix M ⟧ₑ d                                   ＝⟨ refl ⟩
 pr₁ (μ ⟦ σ ⟧) (pr₁ ⟦ M ⟧ₑ d)                       ＝⟨ i ⟩
 pr₁ (pr₁ ⟦ M ⟧ₑ d) (pr₁ (μ ⟦ σ ⟧) ( pr₁ ⟦ M ⟧ₑ d)) ＝⟨ refl ⟩
 pr₁ ⟦ M · Fix M ⟧ₑ d                               ＝⟨ c d ⟩
 pr₁ ⟦ N ⟧ₑ d                                       ∎
  where
    i = μ-gives-a-fixed-point ⟦ σ ⟧ (pr₁ ⟦ M ⟧ₑ d)

correctness-· : {n : ℕ} {Γ : Context n} {σ τ : type}
                (M : PCF Γ (σ ⇒ τ))
                (E : PCF (Γ ’ σ) τ)
                (T : PCF Γ σ)
                (N : PCF Γ τ)
              → pr₁ ⟦ M ⟧ₑ ∼ pr₁ ⟦ ƛ E ⟧ₑ
              → pr₁ ⟦ E [ T ] ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
              → pr₁ ⟦ M · T ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
correctness-· {_} {Γ} {σ} {τ} M E T N c₁ c₂ d =
 pr₁ ⟦ M · T ⟧ₑ d                    ＝⟨ refl ⟩
 pr₁ (pr₁ ⟦ M ⟧ₑ d) (pr₁ ⟦ T ⟧ₑ d)   ＝⟨ i ⟩
 pr₁ (pr₁ ⟦ ƛ E ⟧ₑ d) (pr₁ ⟦ T ⟧ₑ d) ＝⟨ ii ⟩
 pr₁ ⟦ E [ T ] ⟧ₑ d                  ＝⟨ c₂ d ⟩
 pr₁ ⟦ N ⟧ₑ d                        ∎
  where
   i  = ap (λ - → pr₁ - (pr₁ ⟦ T ⟧ₑ d)) (c₁ d)
   ii = β-equality E T d

correctness' : {n : ℕ} {Γ : Context n} {σ : type}
               (M N : PCF Γ σ)
             → M ⇓' N
             → pr₁ ⟦ M ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
correctness' .(v _) .(v _) var-id d  = refl
correctness' .(ƛ _) .(ƛ _) ƛ-id d    = refl
correctness' .Zero  .Zero  zero-id d = refl
correctness' (Pred M) .Zero (pred-zero r) d =
 ap (𝓛̇ pred) (correctness' M Zero r d)

correctness' (Pred M) .(numeral _) (pred-succ {_} {_} {_} {k} r) d =
 ap (𝓛̇ pred) (correctness' M (numeral (succ k)) r d)

correctness' (Succ M) .(Succ (numeral _)) (succ-arg {_} {_} {_} {k} r) d =
 ap (𝓛̇ succ) (correctness' M (numeral k) r d)

correctness' (IfZero t t₁ t₂) N (IfZero-zero r r₁) =
 correctness-IfZero-zero N t t₁ t₂
  (correctness' t Zero r)
  (correctness' t₁ N r₁)

correctness' (IfZero t t₁ t₂) N (IfZero-succ {_} {_} {_} {_} {_} {_} {k} r r₁) =
 correctness-IfZero-succ N t t₁ t₂ k
  (correctness' t (numeral (succ k)) r)
  (correctness' t₂ N r₁)

correctness' (Fix M) N (Fix-step r) =
 correctness-Fix M N (correctness' (M · Fix M) N r)

correctness' .(_ · _) N (·-step {_} {_} {_} {_} {M} {E} {T} {_} r r₁) =
 correctness-· M E T N
  (correctness' M (ƛ E) r)
  (correctness' (E [ T ]) N r₁)

correctness : {n : ℕ} {Γ : Context n} {σ : type}
              (M N : PCF Γ σ)
            → M ⇓ N
            → ⟦ M ⟧ₑ ＝ ⟦ N ⟧ₑ
correctness {_} {Γ} {σ} M N x = γ
 where
  i : pr₁ ⟦ M ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
  i d = ∥∥-rec (sethood (⟦ σ ⟧ ⁻)) (λ x₁ → correctness' M N x₁ d) x

  γ : ⟦ M ⟧ₑ ＝ ⟦ N ⟧ₑ
  γ = to-subtype-＝
       (being-continuous-is-prop (【 Γ 】 ⁻) (⟦ σ ⟧ ⁻))
       (dfunext fe i)

\end{code}
