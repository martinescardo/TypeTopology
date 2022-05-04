Martin Escardo, 2-4 May 2022

Roughly, we show that, for any family β of ordinals indexed by ordinals

    EM → sup β ⊴ ∑ β → WEM

where EM is the principle of excluded middle and WEM is the weak
principle of excluded middle (excluded middle for negated
propositions).

The problem is that the sum doesn't always exist constructively. So we
need a more precise formulation of the above.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import UF-Univalence

module OrdinalsSupSum
        (ua : Univalence)
       where

open import SpartanMLTT
open import OrdinalNotions
open import OrdinalsType
open import OrdinalOfOrdinals ua
open import OrdinalOfOrdinalsSuprema ua
open import CanonicalMapNotation

open import UF-FunExt
open import UF-UA-FunExt
open import UF-ExcludedMiddle
open import UF-Size
open import UF-PropTrunc
open import UF-Subsingletons

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥
 pe : PropExt
 pe = Univalence-gives-PropExt ua

open import OrdinalArithmetic fe

order-preserving-gives-not-⊲ : (α β : Ordinal 𝓤)
                             → (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-order-preserving α β f)
                             → ¬ (β ⊲ α)
order-preserving-gives-not-⊲ {𝓤} α β σ (x₀ , refl) = γ σ
 where
  γ : ¬ (Σ f ꞉ (⟨ α ⟩ → ⟨ α ↓ x₀ ⟩) , is-order-preserving α (α ↓ x₀) f)
  γ (f , fop) = κ
   where
    g : ⟨ α ⟩ → ⟨ α ⟩
    g x = pr₁ (f x)

    h : (x : ⟨ α ⟩) → g x ≺⟨ α ⟩ x₀
    h x = pr₂ (f x)

    δ : (n : ℕ) → (g ^ succ n) x₀ ≺⟨ α ⟩ (g ^ n) x₀
    δ 0        = h x₀
    δ (succ n) = fop _ _ (δ n)

    A : ⟨ α ⟩ → 𝓤 ̇
    A x = Σ n ꞉ ℕ , (g ^ n) x₀ ≡ x

    d : (x : ⟨ α ⟩) → A x → Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × A y
    d x (n , refl) = g x , δ n , succ n , refl

    κ : 𝟘
    κ = no-minimal-is-empty' (underlying-order α) (Well-foundedness α)
         A d (x₀ , 0 , refl)

order-preserving-gives-≼ : EM (𝓤 ⁺)
                         → (α β : Ordinal 𝓤)
                         → (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-order-preserving α β f)
                         → α ≼ β
order-preserving-gives-≼ em α β σ = δ
 where
  γ : (α ≼ β) + (β ⊲ α) → α ≼ β
  γ (inl l) = l
  γ (inr m) = 𝟘-elim (order-preserving-gives-not-⊲ α β σ m)

  δ : α ≼ β
  δ = γ (≼-or-> _⊲_ fe' em ⊲-is-well-order α β)


module _ {𝓤 : Universe}
         (em : Excluded-Middle)
         (sr : Set-Replacement (fe-and-em-give-propositional-truncations fe em))
       where

 open sums-assuming-EM (em {𝓤})
 open suprema (fe-and-em-give-propositional-truncations fe em) sr

 sup-bounded-by-sum : (α : Ordinal 𝓤) (β : ⟨ α ⟩ → Ordinal 𝓤)
                    → sup β ⊴ ∑ α β
 sup-bounded-by-sum α β = sup-is-lower-bound-of-upper-bounds β (∑ α β) l
  where
   l : (x : ⟨ α ⟩) → β x ⊴ ∑ α β
   l x = ≼-gives-⊴ (β x) (∑ α β) m
    where
     f : ⟨ β x ⟩ → ⟨ ∑ α β ⟩
     f y = x , y
     fop : is-order-preserving (β x) (∑ α β) f
     fop y z l = inr (refl , l)
     m : β x ≼ ∑ α β
     m = order-preserving-gives-≼ em (β x) (∑ α β) (f , fop)

 open import OrdinalsToppedType fe
 open import OrdinalToppedArithmetic fe renaming (∑ to ∑ᵀ)

 sup-bounded-by-sumᵀ : (τ : Ordinalᵀ 𝓤) (υ : ⟪ τ ⟫ → Ordinalᵀ 𝓤)
                     → sup (λ x → [ υ x ]) ⊴ [ ∑ᵀ τ υ ]
 sup-bounded-by-sumᵀ τ υ = sup-bounded-by-sum [ τ ] (λ x → [ υ x ])
\end{code}

To get closure under sums constructively, we need to restrict to
particular kinds of ordinals. Having a top element is a simple
sufficient condition, which holds in the applications we have in mind
(for compact ordinals).

\begin{code}

module _ {𝓤 : Universe}
         (pt : propositional-truncations-exist)
         (sr : Set-Replacement pt)
       where

 open import OrdinalsToppedType fe
 open import OrdinalToppedArithmetic fe
 open suprema pt sr

 sup-bounded-by-sum-gives-EM : ({𝓤 : Universe} (τ : Ordinalᵀ 𝓤) (υ : ⟪ τ ⟫ → Ordinalᵀ 𝓤)
                                   → sup (λ x → [ υ x ]) ⊴ [ ∑ τ υ ])
                             → {𝓤 : Universe} → WEM 𝓤
 sup-bounded-by-sum-gives-EM ϕ {𝓤} = γ
  where
   open import OrdinalOfTruthValues fe 𝓤 (pe 𝓤)
   open Omega (pe 𝓤)
   open import OrdinalArithmetic-Properties ua

   τ = 𝟚ᵒ

   υ : ⟪ 𝟚ᵒ ⟫ →  Ordinalᵀ (𝓤 ⁺)
   υ = cases (λ ⋆ → 𝟙ᵒ) (λ ⋆ → Ωᵒ)

   l : sup (λ x → [ υ x ]) ⊴ [ ∑ τ υ ]
   l = ϕ τ υ

   m : Ωₒ ⊴ sup (λ x → [ υ x ])
   m = sup-is-upper-bound (λ x → [ υ x ]) (inr ⋆)

   o : Ωₒ ⊴ [ ∑ τ υ ]
   o = ⊴-trans _ _ _ m l

   p : [ ∑ τ υ ] ≡ (𝟙ₒ +ₒ Ωₒ)
   p = eqtoidₒ _ _ (alternative-plus 𝟙ᵒ Ωᵒ)

   q : Ωₒ ⊴ (𝟙ₒ +ₒ Ωₒ)
   q = transport (Ωₒ ⊴_) p o

   γ : WEM 𝓤
   γ = ⊴-add-taboo q

\end{code}
