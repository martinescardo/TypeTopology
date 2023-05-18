Brendan Hart 2019-2020

\begin{code}

{-# OPTIONS --without-K --safe --exact-split --no-sized-types --no-guardedness --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module PCF.Adequacy
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
open import DomainTheory.Basics.Exponential pt fe 𝓤₀
open import DomainTheory.Basics.LeastFixedPoint pt fe
open import DomainTheory.Basics.Pointed pt fe 𝓤₀
open import DomainTheory.Lifting.LiftingDcpo pt fe 𝓤₀ pe
open import DomainTheory.ScottModelOfPCF.PCFCombinators pt fe 𝓤₀
open import Lifting.Lifting 𝓤₀ hiding (⊥)
open import Lifting.Miscelanea 𝓤₀
open import Lifting.Miscelanea-PropExt-FunExt 𝓤₀ pe fe
open import Lifting.Monad 𝓤₀ hiding (μ)
open import Naturals.Properties hiding (pred-succ)
open import PCF.AbstractSyntax pt
open import PCF.ApplicativeApproximation pt
open import PCF.Dcpo-Contexts pt fe pe
open import PCF.ScottModelTerms pt fe pe
open import PCF.ScottModelTypes pt fe pe
open import PCF.Substitution pt fe pe
open import UF.Miscelanea

open IfZeroDenotationalSemantics pe

adequacy-relation : (σ : type) (d : ⟨ (⟦ σ ⟧ ⁻) ⟩) (M : PCF ⟨⟩ σ) → 𝓤₁ ̇
adequacy-relation ι l t = 𝟙 × ∀ (p : is-defined l) → t ⇓ ℕ-to-ι (value l p)
adequacy-relation (σ ⇒ σ₁) l t = ∀ (d : ⟨ ( ⟦ σ ⟧ ⁻) ⟩) (M : PCF ⟨⟩ σ)
                                      → adequacy-relation σ d M
                                      → adequacy-relation σ₁ (pr₁ l d) (t · M)

lemma7-1-1 : {σ : type}
           → (d : ⟨ ( ⟦ σ ⟧ ⁻) ⟩)
           → (d' : ⟨ ( ⟦ σ ⟧ ⁻) ⟩)
           → (d' ⊑⟨ ( ⟦ σ ⟧ ⁻) ⟩ d)
           → (M : PCF ⟨⟩ σ)
           → adequacy-relation σ d M
           → adequacy-relation σ d' M
lemma7-1-1 {ι} d d' x M (_ , o) = ⋆ , f
 where
   f : (p : is-defined d') → M ⇓ ℕ-to-ι (value d' p)
   f p = transport (λ - → M ⇓ ℕ-to-ι -) (e₂ ⁻¹) (o (＝-to-is-defined e₁ p))
    where
     e₁ : d' ＝ d
     e₁ = x p

     e₂ : value d' p ＝ value d (＝-to-is-defined e₁ p)
     e₂ = ＝-of-values-from-＝ e₁
lemma7-1-1 {σ ⇒ σ₁} f g x M p = γ
  where
   γ : (d : ⟨ ( ⟦ σ ⟧ ⁻) ⟩) →
             Π (λ M₁ → adequacy-relation σ d M₁ → adequacy-relation σ₁ (pr₁ g d) (M · M₁))
   γ d N x₃ = IH
    where
     i : adequacy-relation σ₁ (pr₁ f d) (M · N)
     i = p d N x₃

     ii : pr₁ g d ⊑⟨ ( ⟦ σ₁ ⟧ ⁻) ⟩ pr₁ f d
     ii = x d

     IH : adequacy-relation σ₁ (pr₁ g d) (M · N)
     IH = lemma7-1-1 (pr₁ f d) (pr₁ g d) ii (M · N) i

adequacy-lubs : {σ : type} {I : 𝓤₀ ̇}
              → (u : I → ⟨ ( ⟦ σ ⟧ ⁻) ⟩)
              → (isdirec : is-Directed ( ⟦ σ ⟧ ⁻) u)
              → (t : PCF ⟨⟩ σ)
              → ((i : I) → adequacy-relation σ (u i) t)
              → adequacy-relation σ (∐ ( ⟦ σ ⟧ ⁻) isdirec) t
adequacy-lubs {ι} {I} u isdirec t rel = ⋆ , g
 where
  g : (p : is-defined (∐ ( ⟦ ι ⟧ ⁻) isdirec)) →
        t ⇓ ℕ-to-ι (value (∐ ( ⟦ ι ⟧ ⁻) isdirec) p)
  g p = ∥∥-rec ∥∥-is-prop f p
    where
     f : Σ (λ (i : I) → is-defined (u i)) → t ⇓ ℕ-to-ι (value (∐ ( ⟦ ι ⟧ ⁻) isdirec) p)
     f i = transport (λ - → t ⇓ ℕ-to-ι -) value-lub-is-same (pr₂ (rel (pr₁ i)) (pr₂ i))
      where
       lub-is-same : u (pr₁ i) ＝ ∐ ( ⟦ ι ⟧ ⁻) isdirec
       lub-is-same = ∐-is-upperbound ( ⟦ ι ⟧ ⁻) isdirec (pr₁ i) (pr₂ i)

       value-lub-is-same : value (u (pr₁ i)) (pr₂ i) ＝ value (∐ ( ⟦ ι ⟧ ⁻) isdirec) p
       value-lub-is-same = ＝-of-values-from-＝ lub-is-same
adequacy-lubs {σ ⇒ σ₁} {I} u isdirec t rel p M x = IH
 where
  ptfam : I → ⟨ ( ⟦ σ₁ ⟧ ⁻) ⟩
  ptfam = pointwise-family ( ⟦ σ ⟧ ⁻) ( ⟦ σ₁ ⟧ ⁻) u p

  ptfam-is-directed : is-Directed ( ⟦ σ₁ ⟧ ⁻) ptfam
  ptfam-is-directed = pointwise-family-is-directed ( ⟦ σ ⟧ ⁻) ( ⟦ σ₁ ⟧ ⁻) u isdirec p

  new_rel : (i : I) → adequacy-relation σ₁ (ptfam i) (t · M)
  new_rel i = rel i p M x

  IH : adequacy-relation σ₁ (∐ ( ⟦ σ₁ ⟧ ⁻) ptfam-is-directed) (t · M)
  IH = adequacy-lubs {σ₁} {I} ptfam ptfam-is-directed (t · M) new_rel

adequacy-step : {σ : type}
                (M M' : PCF ⟨⟩ σ)
              → M ⊏̰ M'
              → (a : ⟨ ( ⟦ σ ⟧ ⁻) ⟩)
              → adequacy-relation σ a M
              → adequacy-relation σ a M'
adequacy-step {ι} M M' r a (⋆ , rel) = ⋆ , f
 where
  f : (p : is-defined a) → M' ⇓ ℕ-to-ι (value a p)
  f p = r (pr₁ (pr₂ a) p) (rel p)
adequacy-step {σ ⇒ σ₁} M M' r a rel d M₁ x = IH
 where
  new_rel : adequacy-relation σ₁ (pr₁ a d) (M · M₁)
  new_rel = rel d M₁ x
  IH : adequacy-relation σ₁ (pr₁ a d) (M' · M₁)
  IH = adequacy-step (M · M₁) (M' · M₁) (r M₁) (pr₁ a d) new_rel

adequacy-bottom : {σ : type}
                → (t : PCF ⟨⟩ σ)
                → adequacy-relation σ (⊥ ⟦ σ ⟧) t
adequacy-bottom {ι}      t = ⋆ , (λ p → 𝟘-elim p)
adequacy-bottom {σ ⇒ σ₁} t = (λ _ M _ → adequacy-bottom (t · M))

lemma7-3 : {σ : type}
         → (M : PCF ⟨⟩ (σ ⇒ σ))
         → (f : ⟨ ( ⟦ σ ⇒ σ ⟧ ⁻) ⟩)
         → adequacy-relation (σ ⇒ σ) f M
         → adequacy-relation σ (pr₁ (μ ⟦ σ ⟧) f) (Fix M)
lemma7-3 {σ} M f rel = adequacy-lubs iter-M iter-M-is-directed (Fix M) fn
 where
  iter-M : ℕ → ⟨ ( ⟦ σ ⟧ ⁻) ⟩
  iter-M n = iter ⟦ σ ⟧ n f
  iter-M-is-directed : is-Directed ( ⟦ σ ⟧ ⁻) iter-M
  iter-M-is-directed = (pr₁ (iter-is-directed ⟦ σ ⟧)) , order
   where
    order : (i j : ℕ) →
              ∃
              (λ k →
                 underlying-order ( ⟦ σ ⟧ ⁻) (iter-M i) (iter-M k) ×
                 underlying-order ( ⟦ σ ⟧ ⁻) (iter-M j) (iter-M k))
    order i j = ∥∥-functor (λ x → (pr₁ x) ,
                                       ((pr₁ (pr₂ x) f) ,
                                       (pr₂ (pr₂ x) f)))
                          (pr₂ (iter-is-directed ⟦ σ ⟧) i j)

  fn : ∀ n → adequacy-relation σ (iter ⟦ σ ⟧ n f) (Fix M)
  fn zero = adequacy-bottom (Fix M)
  fn (succ n) = adequacy-step (M · Fix M) (Fix M) fix-⊏̰ (iter ⟦ σ ⟧ (succ n) f) IH₁
   where
    IH : adequacy-relation σ (iter ⟦ σ ⟧ n f) (Fix M)
    IH = fn n

    IH₁ : adequacy-relation σ (iter ⟦ σ ⟧ (succ n) f) (M · (Fix M))
    IH₁ = rel (iter ⟦ σ ⟧ n f) (Fix M) IH

adequacy-succ :  {n : ℕ} {Γ : Context n}
              → (M : PCF Γ ι)
              → (d : ⟨ ( 【 Γ 】 ⁻) ⟩)
              → (f : ∀ {A} → (x : Γ ∋ A) → PCF ⟨⟩ A)
              → adequacy-relation ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
              → adequacy-relation ι (pr₁ ⟦ Succ M ⟧ₑ d) (subst f (Succ M))
adequacy-succ M d f (⋆ , rel) = ⋆ , g
 where
  g : (p : is-defined (pr₁ ⟦ Succ M ⟧ₑ d))
    → subst f (Succ M) ⇓ ℕ-to-ι (value (pr₁ ⟦ Succ M ⟧ₑ d) p)
  g p = ∥∥-functor (λ x → succ-arg x) (rel p)

pred-lemma : ∀ {n : ℕ} {Γ : Context n} {k : ℕ}
           → {M : PCF Γ ι}
           → M ⇓' ℕ-to-ι k
           → (Pred M) ⇓' ℕ-to-ι (pred k)
pred-lemma {n} {Γ} {zero}   x = pred-zero x
pred-lemma {n} {Γ} {succ k} x = pred-succ x

ifzero-lemma : {n : ℕ} {Γ : Context n} {k : ℕ}
      → (M : PCF Γ ι)
      → (M₁ : PCF Γ ι)
      → (M₂ : PCF Γ ι)
      → (f : ∀ {A} → Γ ∋ A → PCF ⟨⟩ A)
      → (subst f M) ⇓ ℕ-to-ι k
      → (d : ⟨ ( 【 Γ 】 ⁻) ⟩)
      → (M-is-defined : is-defined (pr₁ ⟦ M ⟧ₑ d))
      → (result-is-defined : is-defined (⦅ifZero⦆₀ (pr₁ ⟦ M₁ ⟧ₑ d) (pr₁ ⟦ M₂ ⟧ₑ d) k))
      → (M₁-rel : adequacy-relation ι (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁))
      → (M₂-rel : adequacy-relation ι (pr₁ ⟦ M₂ ⟧ₑ d) (subst f M₂))
      → subst f (IfZero M M₁ M₂) ⇓ ℕ-to-ι (value (⦅ifZero⦆₀ (pr₁ ⟦ M₁ ⟧ₑ d) (pr₁ ⟦ M₂ ⟧ₑ d) k) result-is-defined)
ifzero-lemma {n} {Γ} {zero} M M₁ M₂ f x d M-is-defined result-is-defined (⋆ , M₁-rel) (⋆ , M₂-rel) = γ
  where
    M₁-⇓ : subst f M₁ ⇓ ℕ-to-ι (value (pr₁ ⟦ M₁ ⟧ₑ d) result-is-defined)
    M₁-⇓ = M₁-rel result-is-defined
    γ : subst f (IfZero M M₁ M₂) ⇓ ℕ-to-ι (value (⦅ifZero⦆₀ (pr₁ ⟦ M₁ ⟧ₑ d) (pr₁ ⟦ M₂ ⟧ₑ d) zero) result-is-defined)
    γ = ∥∥-functor (λ x → IfZero-zero (pr₁ x) (pr₂ x)) (binary-choice x M₁-⇓)
ifzero-lemma {n} {Γ} {succ k} M M₁ M₂ f x d M-is-defined result-is-defined (⋆ , M₁-rel) (⋆ , M₂-rel) = γ
  where
    M₂-⇓ : subst f M₂ ⇓ ℕ-to-ι (value (pr₁ ⟦ M₂ ⟧ₑ d) result-is-defined)
    M₂-⇓ = M₂-rel result-is-defined
    γ : subst f (IfZero M M₁ M₂) ⇓ ℕ-to-ι (value (⦅ifZero⦆₀ (pr₁ ⟦ M₁ ⟧ₑ d) (pr₁ ⟦ M₂ ⟧ₑ d) (succ k)) result-is-defined)
    γ = ∥∥-functor (λ x → IfZero-succ (pr₁ x) (pr₂ x)) (binary-choice x M₂-⇓)

adequacy-pred :  {n : ℕ} {Γ : Context n}
                 → (M : PCF Γ ι)
                 → (d : ⟨ ( 【 Γ 】 ⁻) ⟩)
                 → (f : ∀ {A} → (x : Γ ∋ A) → PCF ⟨⟩ A)
                 → adequacy-relation ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
                 → adequacy-relation ι (pr₁ ⟦ Pred M ⟧ₑ d) (subst f (Pred M))
adequacy-pred M d f (⋆ , rel) = ⋆ , g
  where
    g : (p : is-defined (pr₁ ⟦ Pred M ⟧ₑ d)) →
          subst f (Pred M) ⇓ ℕ-to-ι (value (pr₁ ⟦ Pred M ⟧ₑ d) p)
    g p = ∥∥-functor pred-lemma (rel p)

adequacy-ifzero :   {n : ℕ} {Γ : Context n}
                 → (M : PCF Γ ι) (M₁ : PCF Γ ι) (M₂ : PCF Γ ι)
                 → (d : ⟨ ( 【 Γ 】 ⁻) ⟩)
                 → (f : ∀ {A} → (x : Γ ∋ A) → PCF ⟨⟩ A)
                 → adequacy-relation ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
                 → adequacy-relation ι (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁)
                 → adequacy-relation ι (pr₁ ⟦ M₂ ⟧ₑ d) (subst f M₂)
                 → adequacy-relation ι (pr₁ ⟦ IfZero M M₁ M₂ ⟧ₑ d) (subst f (IfZero M M₁ M₂))
adequacy-ifzero {n} {Γ} M M₁ M₂ d f (⋆ , M-rel) M₁-rel M₂-rel = ⋆ , g
  where
    g : (p : is-defined (pr₁ ⟦ IfZero M M₁ M₂ ⟧ₑ d)) →
          subst f (IfZero M M₁ M₂) ⇓
          ℕ-to-ι (value (pr₁ ⟦ IfZero M M₁ M₂ ⟧ₑ d) p)
    g (M-is-defined , result-is-defined) = ifzero-lemma M M₁ M₂ f (M-rel M-is-defined) d M-is-defined result-is-defined M₁-rel M₂-rel

lemma7-4 : {n : ℕ} {Γ : Context n} {τ : type}
           (M : PCF Γ τ)
           (d : ⟨ ( 【 Γ 】 ⁻) ⟩)
           (f : ∀ {A} → (x : Γ ∋ A) → PCF ⟨⟩ A)
           (g : ∀ {A} → (x : Γ ∋ A) → adequacy-relation A (extract x d) (f x))
           → adequacy-relation τ (pr₁ ⟦ M ⟧ₑ d) (subst f M)
lemma7-4 {n} {Γ} {.ι} Zero d f g = ⋆ , λ p → ∣ zero-id ∣

lemma7-4 {n} {Γ} {.ι} (Succ M) d f g = adequacy-succ M d f IH
  where
    IH : adequacy-relation ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
    IH = lemma7-4 M d f g

lemma7-4 {n} {Γ} {.ι} (Pred M) d f g = adequacy-pred M d f IH
  where
    IH : adequacy-relation ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
    IH = lemma7-4 M d f g

lemma7-4 {n} {Γ} {.ι} (IfZero M M₁ M₂) d f g = adequacy-ifzero M M₁ M₂ d f IH₀ IH₁ IH₂
  where
    IH₀ : adequacy-relation ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
    IH₀ = lemma7-4 M d f g

    IH₁ : adequacy-relation ι (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁)
    IH₁ = lemma7-4 M₁ d f g

    IH₂ : adequacy-relation ι (pr₁ ⟦ M₂ ⟧ₑ d) (subst f M₂)
    IH₂ = lemma7-4 M₂ d f g

lemma7-4 {n} {Γ} {.(_ ⇒ _)} (ƛ {n} {Γ} {σ} {τ} M) d f g d₁ M₁ x = γ
  where
    IH : adequacy-relation τ (pr₁ ⟦ M ⟧ₑ (d , d₁)) (subst (extend-with M₁ f) M)
    IH = lemma7-4 M (d , d₁) (extend-with M₁ f) extended-g
      where
        extended-g : ∀ {A} → (x₁ : (Γ ’ σ) ∋ A) → adequacy-relation A (extract x₁ (d , d₁)) (extend-with M₁ f x₁)
        extended-g Z = x
        extended-g (S x₁) = g x₁
    i : subst (extend-with M₁ f) M ＝ subst (exts f) M [ M₁ ]
    i = subst-ext M M₁ f

    ii : subst (extend-with M₁ f) M ⊏̰ (subst f (ƛ M) · M₁)
    ii = transport⁻¹ (λ - → - ⊏̰ (subst f (ƛ M) · M₁)) i β-⊏̰

    γ : adequacy-relation τ (pr₁ (pr₁ ⟦ ƛ M ⟧ₑ d) d₁) (subst f (ƛ M) · M₁)
    γ = adequacy-step (subst (extend-with M₁ f) M) (subst f (ƛ M) · M₁) ii (pr₁ (pr₁ ⟦ ƛ M ⟧ₑ d) d₁) IH

lemma7-4 (_·_ {n} {Γ} {σ} {σ₁} M M₁) d f g = IH₀ (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁) IH₁
 where
  IH₀ : adequacy-relation (σ ⇒ σ₁) (pr₁ ⟦ M ⟧ₑ d) (subst f M)
  IH₀ = lemma7-4 M d f g

  IH₁ : adequacy-relation σ (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁)
  IH₁ = lemma7-4 M₁ d f g

lemma7-4 {n} {Γ} {σ} (v x) d f g = g x

lemma7-4 {n} {Γ} {σ} (Fix M) d f g = lemma7-3 (subst f M) (pr₁ ⟦ M ⟧ₑ d) IH
 where
  IH : (d₁ : ⟨ (⟦ σ ⟧ ⁻) ⟩) (M₁ : PCF ⟨⟩ σ)
     → adequacy-relation σ d₁ M₁
     → adequacy-relation σ (pr₁ (pr₁ ⟦ M ⟧ₑ d) d₁) (subst (λ {A} → f) M · M₁)
  IH = lemma7-4 M d f g

adequacy : (M : PCF ⟨⟩ ι) (n : ℕ) → pr₁ ⟦ M ⟧ₑ ⋆ ＝ η n → M ⇓ ℕ-to-ι n
adequacy M n p = pr₂ iv ⋆
 where
  i : adequacy-relation ι (pr₁ ⟦ M ⟧ₑ ⋆) (subst ids M)
  i = lemma7-4 M ⋆ ids f
   where
    f : ∀ {A} → (x : ⟨⟩ ∋ A) → adequacy-relation A (extract x ⋆) (v x)
    f ()

  ii : subst ids M ＝ M
  ii = sub-id M

  iii : adequacy-relation ι (pr₁ ⟦ M ⟧ₑ ⋆) M
  iii = transport (adequacy-relation ι (pr₁ ⟦ M ⟧ₑ ⋆)) ii i

  iv : adequacy-relation ι (η n) M
  iv = transport (λ - → adequacy-relation ι - M) p iii

\end{code}
