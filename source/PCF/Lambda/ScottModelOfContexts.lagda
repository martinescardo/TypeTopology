Brendan Hart 2019-2020

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module PCF.Lambda.ScottModelOfContexts
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
open import DomainTheory.Basics.FunctionComposition pt fe 𝓤₀
open import DomainTheory.Basics.Pointed pt fe 𝓤₀
open import DomainTheory.Basics.Products pt fe
open import PCF.Lambda.AbstractSyntax pt
open import PCF.Lambda.ScottModelOfTypes pt fe pe
open import OrderedTypes.Poset fe
open import UF.Sets
open import UF.Subsingletons-Properties

open DcpoProductsGeneral 𝓤₀
open PosetAxioms

⊤ᵈᶜᵖᵒ : DCPO {𝓤₁} {𝓤₁}
⊤ᵈᶜᵖᵒ = 𝟙 , _⊑⟨⊤⟩_ , (s , p , (λ _ → ⋆) , t , a) , dc
 where
   _⊑⟨⊤⟩_ : 𝟙 {𝓤₁} → 𝟙 {𝓤₁} → 𝓤₁ ̇
   x ⊑⟨⊤⟩ y = 𝟙

   s : is-set 𝟙
   s = props-are-sets 𝟙-is-prop

   p : is-prop-valued {𝓤₁} {𝓤₁} {𝟙} (λ x y → 𝟙)
   p _ _ ⋆ ⋆ = refl

   r : is-reflexive _⊑⟨⊤⟩_
   r _ = ⋆

   t : is-transitive {𝓤₁} {𝓤₁} {𝟙} (λ x y → 𝟙)
   t _ _ _ _ _ = ⋆

   a : ∀ (x : 𝟙) y → x ⊑⟨⊤⟩ y → _ → x ＝ y
   a ⋆ ⋆ _ _ = refl

   dc : is-directed-complete (λ x y → 𝟙)
   dc _ _ _ = ⋆ , ((λ _ → ⋆) , (λ _ _ → ⋆))

⊤ᵈᶜᵖᵒ⊥ : DCPO⊥ {𝓤₁} {𝓤₁}
⊤ᵈᶜᵖᵒ⊥ = ⊤ᵈᶜᵖᵒ , (⋆ , (λ y → ⋆))

【_】 : {n : ℕ} (Γ : Context n) → DCPO⊥ {𝓤₁} {𝓤₁}
【 ⟨⟩ 】 = ⊤ᵈᶜᵖᵒ⊥
【 Γ ’ σ 】 = 【 Γ 】 ×ᵈᶜᵖᵒ⊥ ⟦ σ ⟧

extract : {n : ℕ} {σ : type} {Γ : Context n}
        → (x : Γ ∋ σ)
        → ⟨(【 Γ 】 ⁻)⟩  → ⟨(⟦ σ ⟧ ⁻)⟩
extract {n} {σ} {a} Z d = pr₂ d
extract {n} {σ₁} {Γ ’ σ} (S x) d = extract x (pr₁ d)

Γ₁⊑Γ₂→lookups-less : {n : ℕ} {Γ : Context n} {σ : type}
                   → (x : ⟨(【 Γ 】 ⁻)⟩)
                   → (y : ⟨(【 Γ 】 ⁻)⟩)
                   → x ⊑⟨(【 Γ 】 ⁻)⟩ y
                   → (z : Γ ∋ σ)
                   → extract z x ⊑⟨(⟦ σ ⟧ ⁻)⟩ extract z y
Γ₁⊑Γ₂→lookups-less {n}      {⟨⟩}    {σ}  x y e z =
 𝟘-elim (∋-gives-Context-is-non-empty z)
Γ₁⊑Γ₂→lookups-less {succ n} {Γ ’ σ} {σ}  x y e Z     = pr₂ e
Γ₁⊑Γ₂→lookups-less {succ n} {Γ ’ τ} {σ}  x y e (S z) =
 Γ₁⊑Γ₂→lookups-less (pr₁ x) (pr₁ y) (pr₁ e) z

∘-of-prₓ-is-continuous : {n : ℕ} {Γ : Context n} {σ : type} (x : Γ ∋ σ)
                       → is-continuous (【 Γ 】 ⁻) (⟦ σ ⟧ ⁻) (extract x)
∘-of-prₓ-is-continuous {n} {⟨⟩}    {σ} x =
 𝟘-elim (∋-gives-Context-is-non-empty x)
∘-of-prₓ-is-continuous {n} {Γ ’ σ} {σ} Z =
 continuity-of-function (【 Γ ’ σ 】 ⁻) (⟦ σ ⟧ ⁻)
  (pr₂-is-continuous (【 Γ 】 ⁻) (⟦ σ ⟧ ⁻))

∘-of-prₓ-is-continuous {n} {Γ ’ τ} {σ} (S x) =
 continuity-of-function (【 Γ ’ τ 】 ⁻) (⟦ σ ⟧ ⁻)
  ([ (【 Γ ’ τ 】 ⁻) , (【 Γ 】 ⁻) , (⟦ σ ⟧ ⁻) ] (extract x) ,
   ∘-of-prₓ-is-continuous x ∘ᵈᶜᵖᵒ pr₁-is-continuous (【 Γ 】 ⁻) (⟦ τ ⟧ ⁻))

var-DCPO : {n : ℕ} {σ : type} (Γ : Context n) (x : Γ ∋ σ)
         → DCPO[ (【 Γ 】 ⁻) , (⟦ σ ⟧ ⁻) ]
var-DCPO {n} {σ} Γ x = extract x , c
 where
  c : is-continuous (【 Γ 】 ⁻) (⟦ σ ⟧ ⁻) (extract x)
  c = ∘-of-prₓ-is-continuous x

var-DCPO⊥ : {n : ℕ} {σ : type} (Γ : Context n)
          → (x : Γ ∋ σ)→ DCPO⊥[ 【 Γ 】 , ⟦ σ ⟧ ]
var-DCPO⊥ Γ x = var-DCPO Γ x
