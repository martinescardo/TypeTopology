Brendan Hart 2019-2020

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module PCF.Lambda.Adequacy
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
open import Lifting.Lifting 𝓤₀ hiding (⊥)
open import Lifting.Miscelanea 𝓤₀
open import Lifting.Miscelanea-PropExt-FunExt 𝓤₀ pe fe
open import Lifting.Monad 𝓤₀ hiding (μ)
open import Naturals.Properties hiding (pred-succ)
open import PCF.Combinatory.PCFCombinators pt fe 𝓤₀
open import PCF.Lambda.AbstractSyntax pt
open import PCF.Lambda.ApplicativeApproximation pt
open import PCF.Lambda.BigStep pt
open import PCF.Lambda.ScottModelOfContexts pt fe pe
open import PCF.Lambda.ScottModelOfTerms pt fe pe
open import PCF.Lambda.ScottModelOfTypes pt fe pe
open import PCF.Lambda.Substitution pt fe pe

open IfZeroDenotationalSemantics pe

adequate : (σ : type) (d : ⟨ ⟦ σ ⟧ ⁻ ⟩) (M : PCF ⟨⟩ σ) → 𝓤₁ ̇
adequate ι        l t = 𝟙 × ((p : is-defined l) → t ⇓ numeral (value l p))
adequate (σ ⇒ σ₁) l t = (d : ⟨ ⟦ σ ⟧ ⁻ ⟩) (M : PCF ⟨⟩ σ)
                           → adequate σ d M
                           → adequate σ₁ (pr₁ l d) (t · M)

lemma7-1-1 : {σ : type}
           → (d : ⟨ ⟦ σ ⟧ ⁻ ⟩)
           → (d' : ⟨ ⟦ σ ⟧ ⁻ ⟩)
           → (d' ⊑⟨ ⟦ σ ⟧ ⁻ ⟩ d)
           → (M : PCF ⟨⟩ σ)
           → adequate σ d M
           → adequate σ d' M
lemma7-1-1 {ι} d d' x M (_ , o) = ⋆ , f
 where
  f : (p : is-defined d') → M ⇓ numeral (value d' p)
  f p = transport (λ - → M ⇓ numeral -) (e₂ ⁻¹) (o (＝-to-is-defined e₁ p))
   where
    e₁ : d' ＝ d
    e₁ = x p

    e₂ : value d' p ＝ value d (＝-to-is-defined e₁ p)
    e₂ = ＝-of-values-from-＝ e₁

lemma7-1-1 {σ ⇒ σ₁} f g x M p = γ
  where
   γ : (d : ⟨ ⟦ σ ⟧ ⁻ ⟩)
     → ∀ N → adequate σ d N → adequate σ₁ (pr₁ g d) (M · N)
   γ d N a = IH
    where
     i : adequate σ₁ (pr₁ f d) (M · N)
     i = p d N a

     ii : pr₁ g d ⊑⟨ ⟦ σ₁ ⟧ ⁻ ⟩ pr₁ f d
     ii = x d

     IH : adequate σ₁ (pr₁ g d) (M · N)
     IH = lemma7-1-1 (pr₁ f d) (pr₁ g d) ii (M · N) i

adequacy-lubs : {σ : type} {I : 𝓤₀ ̇}
              → (u : I → ⟨ ⟦ σ ⟧ ⁻ ⟩)
              → (δ : is-Directed ( ⟦ σ ⟧ ⁻) u)
              → (t : PCF ⟨⟩ σ)
              → ((i : I) → adequate σ (u i) t)
              → adequate σ (∐ ( ⟦ σ ⟧ ⁻) δ) t
adequacy-lubs {ι} {I} u δ t a = ⋆ , g
 where
  g : (p : is-defined (∐ ( ⟦ ι ⟧ ⁻) δ))
    → t ⇓ numeral (value (∐ ( ⟦ ι ⟧ ⁻) δ) p)
  g p = ∥∥-rec ∥∥-is-prop f p
   where
    f : (Σ i ꞉ I , is-defined (u i))
      → t ⇓ numeral (value (∐ ( ⟦ ι ⟧ ⁻) δ) p)
    f (i , d) = transport (λ - → t ⇓ numeral -) value-lub-is-same (pr₂ (a i) d)
     where
      lub-is-same : u i ＝ ∐ ( ⟦ ι ⟧ ⁻) δ
      lub-is-same = ∐-is-upperbound ( ⟦ ι ⟧ ⁻) δ i d

      value-lub-is-same : value (u i) d ＝ value (∐ ( ⟦ ι ⟧ ⁻) δ) p
      value-lub-is-same = ＝-of-values-from-＝ lub-is-same

adequacy-lubs {σ ⇒ σ₁} {I} u δ t a p M x = IH
 where
  ptfam : I → ⟨ ⟦ σ₁ ⟧ ⁻ ⟩
  ptfam = pointwise-family ( ⟦ σ ⟧ ⁻) ( ⟦ σ₁ ⟧ ⁻) u p

  ptfam-is-directed : is-Directed ( ⟦ σ₁ ⟧ ⁻) ptfam
  ptfam-is-directed = pointwise-family-is-directed ( ⟦ σ ⟧ ⁻) ( ⟦ σ₁ ⟧ ⁻) u δ p

  new_rel : (i : I) → adequate σ₁ (ptfam i) (t · M)
  new_rel i = a i p M x

  IH : adequate σ₁ (∐ ( ⟦ σ₁ ⟧ ⁻) ptfam-is-directed) (t · M)
  IH = adequacy-lubs {σ₁} {I} ptfam ptfam-is-directed (t · M) new_rel

adequacy-step : {σ : type}
                (M M' : PCF ⟨⟩ σ)
              → M ⊏̰ M'
              → (a : ⟨ ⟦ σ ⟧ ⁻ ⟩)
              → adequate σ a M
              → adequate σ a M'
adequacy-step {ι} M M' r a (⋆ , ρ) = ⋆ , f
 where
  f : (p : is-defined a) → M' ⇓ numeral (value a p)
  f p = r (value a p) (ρ p)

adequacy-step {σ ⇒ σ₁} M M' r (ϕ , _) rel d M₁ x = IH
 where
  new_rel : adequate σ₁ (ϕ d) (M · M₁)
  new_rel = rel d M₁ x

  IH : adequate σ₁ (ϕ d) (M' · M₁)
  IH = adequacy-step (M · M₁) (M' · M₁) (r M₁) (ϕ d) new_rel

adequacy-bottom : {σ : type}
                → (t : PCF ⟨⟩ σ)
                → adequate σ (⊥ ⟦ σ ⟧) t
adequacy-bottom {ι}      t = ⋆ , (λ p → 𝟘-elim p)
adequacy-bottom {σ ⇒ σ₁} t = (λ _ M _ → adequacy-bottom (t · M))

lemma7-3 : {σ : type}
         → (M : PCF ⟨⟩ (σ ⇒ σ))
         → (f : ⟨ ⟦ σ ⇒ σ ⟧ ⁻ ⟩)
         → adequate (σ ⇒ σ) f M
         → adequate σ (pr₁ (μ ⟦ σ ⟧) f) (Fix M)
lemma7-3 {σ} M f rel = adequacy-lubs iter-M iter-M-is-directed (Fix M) fn
 where
  iter-M : ℕ → ⟨ ⟦ σ ⟧ ⁻ ⟩
  iter-M n = iter ⟦ σ ⟧ n f

  iter-M-is-directed : is-Directed ( ⟦ σ ⟧ ⁻) iter-M
  iter-M-is-directed = (pr₁ (iter-is-directed ⟦ σ ⟧)) , order
   where
    order : (i j : ℕ)
          → ∃ k ꞉ ℕ , ((iter-M i) ⊑⟨ ⟦ σ ⟧ ⁻ ⟩ (iter-M k) ×
                       (iter-M j) ⊑⟨  ⟦ σ ⟧ ⁻ ⟩ (iter-M k))
    order i j = ∥∥-functor
                 (λ (n , g , h) → n , g f , h f)
                 (pr₂ (iter-is-directed ⟦ σ ⟧) i j)

  fn : ∀ n → adequate σ (iter ⟦ σ ⟧ n f) (Fix M)
  fn zero     = adequacy-bottom (Fix M)
  fn (succ n) = adequacy-step (M · Fix M) (Fix M) fix-⊏̰ (iter ⟦ σ ⟧ (succ n) f) IH₁
   where
    IH : adequate σ (iter ⟦ σ ⟧ n f) (Fix M)
    IH = fn n

    IH₁ : adequate σ (iter ⟦ σ ⟧ (succ n) f) (M · (Fix M))
    IH₁ = rel (iter ⟦ σ ⟧ n f) (Fix M) IH

adequacy-succ : {n : ℕ} {Γ : Context n}
              → (M : PCF Γ ι)
              → (d : ⟨ 【 Γ 】 ⁻ ⟩)
              → (f : ∀ {A} → (x : Γ ∋ A) → PCF ⟨⟩ A)
              → adequate ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
              → adequate ι (pr₁ ⟦ Succ M ⟧ₑ d) (subst f (Succ M))
adequacy-succ M d f (⋆ , rel) = ⋆ , g
 where
  g : (p : is-defined (pr₁ ⟦ Succ M ⟧ₑ d))
    → subst f (Succ M) ⇓ numeral (value (pr₁ ⟦ Succ M ⟧ₑ d) p)
  g p = ∥∥-functor (λ x → succ-arg x) (rel p)

pred-lemma : ∀ {n : ℕ} {Γ : Context n} {k : ℕ}
           → {M : PCF Γ ι}
           → M ⇓' numeral k
           → (Pred M) ⇓' numeral (pred k)
pred-lemma {n} {Γ} {zero}   x = pred-zero x
pred-lemma {n} {Γ} {succ k} x = pred-succ x

ifzero-lemma :
  {n : ℕ}
  {Γ : Context n} {k : ℕ}
  (M : PCF Γ ι)
  (M₁ : PCF Γ ι)
  (M₂ : PCF Γ ι)
  (f : ∀ {A} → Γ ∋ A → PCF ⟨⟩ A)
 → subst f M ⇓ numeral k
 → (d : ⟨ 【 Γ 】 ⁻ ⟩)
   (M-is-defined : is-defined (pr₁ ⟦ M ⟧ₑ d))
   (δ : is-defined (⦅ifZero⦆₀ (pr₁ ⟦ M₁ ⟧ₑ d) (pr₁ ⟦ M₂ ⟧ₑ d) k))
   (M₁-rel : adequate ι (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁))
   (M₂-rel : adequate ι (pr₁ ⟦ M₂ ⟧ₑ d) (subst f M₂))
 → subst f (IfZero M M₁ M₂)
   ⇓ numeral (value (⦅ifZero⦆₀ (pr₁ ⟦ M₁ ⟧ₑ d) (pr₁ ⟦ M₂ ⟧ₑ d) k) δ)
ifzero-lemma {n} {Γ} {zero} M M₁ M₂ f x d M-is-defined δ
             (⋆ , M₁-rel) (⋆ , M₂-rel) = γ
  where
   M₁-⇓ : subst f M₁ ⇓ numeral (value (pr₁ ⟦ M₁ ⟧ₑ d) δ)
   M₁-⇓ = M₁-rel δ

   γ : subst f (IfZero M M₁ M₂)
     ⇓ numeral (value (⦅ifZero⦆₀ (pr₁ ⟦ M₁ ⟧ₑ d) (pr₁ ⟦ M₂ ⟧ₑ d) zero) δ)
   γ = ∥∥-functor (λ x → IfZero-zero (pr₁ x) (pr₂ x)) (binary-choice x M₁-⇓)

ifzero-lemma {n} {Γ} {succ k} M M₁ M₂ f x d M-is-defined δ
             (⋆ , M₁-rel) (⋆ , M₂-rel) = γ
 where
   M₂-⇓ : subst f M₂ ⇓ numeral (value (pr₁ ⟦ M₂ ⟧ₑ d) δ)
   M₂-⇓ = M₂-rel δ

   γ : subst f (IfZero M M₁ M₂)
     ⇓ numeral (value (⦅ifZero⦆₀ (pr₁ ⟦ M₁ ⟧ₑ d) (pr₁ ⟦ M₂ ⟧ₑ d) (succ k)) δ)
   γ = ∥∥-functor (λ x → IfZero-succ (pr₁ x) (pr₂ x)) (binary-choice x M₂-⇓)

adequacy-pred : {n : ℕ} {Γ : Context n}
              → (M : PCF Γ ι)
              → (d : ⟨ 【 Γ 】 ⁻ ⟩)
              → (f : ∀ {A} → (x : Γ ∋ A) → PCF ⟨⟩ A)
              → adequate ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
              → adequate ι (pr₁ ⟦ Pred M ⟧ₑ d) (subst f (Pred M))
adequacy-pred M d f (⋆ , rel) = ⋆ , g
 where
   g : (p : is-defined (pr₁ ⟦ Pred M ⟧ₑ d))
     → subst f (Pred M) ⇓ numeral (value (pr₁ ⟦ Pred M ⟧ₑ d) p)
   g p = ∥∥-functor pred-lemma (rel p)

adequacy-ifzero : {n : ℕ} {Γ : Context n}
                  (M : PCF Γ ι) (M₁ : PCF Γ ι) (M₂ : PCF Γ ι)
                  (d : ⟨ 【 Γ 】 ⁻ ⟩)
                  (f : ∀ {A} → (x : Γ ∋ A) → PCF ⟨⟩ A)
                → adequate ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
                → adequate ι (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁)
                → adequate ι (pr₁ ⟦ M₂ ⟧ₑ d) (subst f M₂)
                → adequate ι (pr₁ ⟦ IfZero M M₁ M₂ ⟧ₑ d)
                             (subst f (IfZero M M₁ M₂))
adequacy-ifzero {n} {Γ} M M₁ M₂ d f (⋆ , M-rel) M₁-rel M₂-rel = ⋆ , g
 where
  g : (p : is-defined (pr₁ ⟦ IfZero M M₁ M₂ ⟧ₑ d))
    → subst f (IfZero M M₁ M₂) ⇓ numeral (value (pr₁ ⟦ IfZero M M₁ M₂ ⟧ₑ d) p)
  g (M-is-defined , δ) = ifzero-lemma
                          M
                          M₁
                          M₂
                          f
                          (M-rel M-is-defined)
                          d
                          M-is-defined
                          δ
                          M₁-rel
                          M₂-rel

lemma7-4 : {n : ℕ} {Γ : Context n} {τ : type}
           (M : PCF Γ τ)
           (d : ⟨ 【 Γ 】 ⁻ ⟩)
           (f : ∀ {A} → (x : Γ ∋ A) → PCF ⟨⟩ A)
           (g : ∀ {A} → (x : Γ ∋ A) → adequate A (extract x d) (f x))
         → adequate τ (pr₁ ⟦ M ⟧ₑ d) (subst f M)
lemma7-4 {n} {Γ} {.ι} Zero d f g = ⋆ , λ p → ∣ zero-id ∣

lemma7-4 {n} {Γ} {.ι} (Succ M) d f g = adequacy-succ M d f IH
 where
  IH : adequate ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
  IH = lemma7-4 M d f g

lemma7-4 {n} {Γ} {.ι} (Pred M) d f g = adequacy-pred M d f IH
 where
  IH : adequate ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
  IH = lemma7-4 M d f g

lemma7-4 {n} {Γ} {.ι} (IfZero M M₁ M₂) d f g =
 adequacy-ifzero M M₁ M₂ d f IH₀ IH₁ IH₂
 where
  IH₀ : adequate ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
  IH₀ = lemma7-4 M d f g

  IH₁ : adequate ι (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁)
  IH₁ = lemma7-4 M₁ d f g

  IH₂ : adequate ι (pr₁ ⟦ M₂ ⟧ₑ d) (subst f M₂)
  IH₂ = lemma7-4 M₂ d f g

lemma7-4 {n} {Γ} {.(_ ⇒ _)} (ƛ {n} {Γ} {σ} {τ} M) d f g d₁ M₁ x = γ
 where
  IH : adequate τ (pr₁ ⟦ M ⟧ₑ (d , d₁)) (subst (extend-with M₁ f) M)
  IH = lemma7-4 M (d , d₁) (extend-with M₁ f) extended-g
   where
    extended-g : {A : type} (x₁ : (Γ ’ σ) ∋ A)
               → adequate A (extract x₁ (d , d₁)) (extend-with M₁ f x₁)
    extended-g Z      = x
    extended-g (S x₁) = g x₁

  i : subst (extend-with M₁ f) M ＝ subst (exts f) M [ M₁ ]
  i = subst-ext M M₁ f

  ii : subst (extend-with M₁ f) M ⊏̰ (subst f (ƛ M) · M₁)
  ii = transport⁻¹ (λ - → - ⊏̰ (subst f (ƛ M) · M₁)) i β-⊏̰

  γ : adequate τ (pr₁ (pr₁ ⟦ ƛ M ⟧ₑ d) d₁) (subst f (ƛ M) · M₁)
  γ = adequacy-step
       (subst (extend-with M₁ f) M)
       (subst f (ƛ M) · M₁)
       ii
       (pr₁ (pr₁ ⟦ ƛ M ⟧ₑ d) d₁)
       IH

lemma7-4 (_·_ {n} {Γ} {σ} {σ₁} M M₁) d f g = IH₀ (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁) IH₁
 where
  IH₀ : adequate (σ ⇒ σ₁) (pr₁ ⟦ M ⟧ₑ d) (subst f M)
  IH₀ = lemma7-4 M d f g

  IH₁ : adequate σ (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁)
  IH₁ = lemma7-4 M₁ d f g

lemma7-4 {n} {Γ} {σ} (v x) d f g = g x

lemma7-4 {n} {Γ} {σ} (Fix M) d f g = lemma7-3 (subst f M) (pr₁ ⟦ M ⟧ₑ d) IH
 where
  IH : (d₁ : ⟨ ⟦ σ ⟧ ⁻ ⟩) (M₁ : PCF ⟨⟩ σ)
     → adequate σ d₁ M₁
     → adequate σ (pr₁ (pr₁ ⟦ M ⟧ₑ d) d₁) (subst (λ {A} → f) M · M₁)
  IH = lemma7-4 M d f g

adequacy : (M : PCF ⟨⟩ ι) (n : ℕ) → pr₁ ⟦ M ⟧ₑ ⋆ ＝ η n → M ⇓ numeral n
adequacy M n p = pr₂ iv ⋆
 where
  i : adequate ι (pr₁ ⟦ M ⟧ₑ ⋆) (subst ids M)
  i = lemma7-4 M ⋆ ids f
   where
    f : ∀ {A} → (x : ⟨⟩ ∋ A) → adequate A (extract x ⋆) (v x)
    f ()

  ii : subst ids M ＝ M
  ii = sub-id M

  iii : adequate ι (pr₁ ⟦ M ⟧ₑ ⋆) M
  iii = transport (adequate ι (pr₁ ⟦ M ⟧ₑ ⋆)) ii i

  iv : adequate ι (η n) M
  iv = transport (λ - → adequate ι - M) p iii

\end{code}
