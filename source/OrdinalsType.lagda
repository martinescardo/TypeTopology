Martin Escardo, 29 June 2018

The type Ordinals of ordinals in a universe U, and the subtype Ordinalsᵀ of
ordinals with a top element.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

open import OrdinalNotions hiding (_≤_)

open import UF-Base
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Embeddings

module OrdinalsType where

\end{code}

An ordinal is a type equipped with ordinal structure. Such a type is
automatically a set.

\begin{code}

OrdinalStructure : 𝓤 ̇ → 𝓤 ⁺ ̇
OrdinalStructure {𝓤} X = Σ _<_ ꞉ (X → X → 𝓤 ̇ ) , (is-well-order _<_)

Ordinal : ∀ 𝓤 → 𝓤 ⁺ ̇
Ordinal 𝓤 = Σ X ꞉ 𝓤 ̇ , OrdinalStructure X

\end{code}

NB. Perhaps we will eventually need to have two parameters U (the
universe where the underlying type X lives) and V (the universe where
_<_ takes values in) for Ordinal.

Ordinals are ranged over by α,β,γ.

The underlying type of an ordinal (which happens to be necessarily a
set):

\begin{code}

⟨_⟩ : Ordinal 𝓤 → 𝓤 ̇
⟨ X , _<_ , o ⟩ = X

structure : (α : Ordinal 𝓤) → OrdinalStructure ⟨ α ⟩
structure (X , s) = s

underlying-order : (α : Ordinal 𝓤) → ⟨ α ⟩ → ⟨ α ⟩ → 𝓤 ̇
underlying-order (X , _<_ , o) = _<_

underlying-porder : (α : Ordinal 𝓤) → ⟨ α ⟩ → ⟨ α ⟩ → 𝓤 ̇
underlying-porder (X , _<_ , o) = _≼_ _<_

syntax underlying-order  α x y = x ≺⟨ α ⟩ y
syntax underlying-porder α x y = x ≼⟨ α ⟩ y

is-well-ordered : (α : Ordinal 𝓤) → is-well-order (underlying-order α)
is-well-ordered (X , _<_ , o) = o

Prop-valuedness : (α : Ordinal 𝓤) → is-prop-valued (underlying-order α)
Prop-valuedness α = prop-valuedness (underlying-order α) (is-well-ordered α)

Transitivity : (α : Ordinal 𝓤) → is-transitive (underlying-order α)
Transitivity α = transitivity (underlying-order α) (is-well-ordered α)

Well-foundedness : (α : Ordinal 𝓤) (x : ⟨ α ⟩) → is-accessible (underlying-order α) x
Well-foundedness α = well-foundedness (underlying-order α) (is-well-ordered α)

Transfinite-induction : (α : Ordinal 𝓤)
                      → (P : ⟨ α ⟩ → 𝓦 ̇ )
                      → ((x : ⟨ α ⟩) → ((y : ⟨ α ⟩) → y ≺⟨ α ⟩ x → P y) → P x)
                      → (x : ⟨ α ⟩) → P x
Transfinite-induction α = transfinite-induction
                           (underlying-order α)
                           (Well-foundedness α)

Extensionality : (α : Ordinal 𝓤) → is-extensional (underlying-order α)
Extensionality α = extensionality (underlying-order α) (is-well-ordered α)

\end{code}

TODO. We should add further properties of the order from the module
OrdinalNotions. For the moment, we add this:

\begin{code}

irrefl : (α : Ordinal 𝓤) (x : ⟨ α ⟩) → ¬(x ≺⟨ α ⟩ x)
irrefl α x = accessible-points-are-irreflexive
              (underlying-order α) x (Well-foundedness α x)

\end{code}

Characterization of equality of ordinals using the structure identity
principle:

\begin{code}

open import UF-Equiv
open import UF-Univalence

Ordinal-≡ : FunExt → is-univalent 𝓤
          → (α β : Ordinal 𝓤)
          → (α ≡ β)
          ≃ (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) ,
                 is-equiv f
               × ((λ x x' → x ≺⟨ α ⟩ x') ≡ (λ x x' → f x ≺⟨ β ⟩ f x')))
Ordinal-≡ {𝓤} fe = generalized-metric-space.characterization-of-M-≡ (𝓤 ̇)
                    (λ _ → is-well-order)
                    (λ X _<_ → being-well-order-is-prop _<_ fe)
 where
  open import UF-SIP-Examples

\end{code}

Often it is convenient to work with the following alternative notion
of ordinal equivalence, which we take as the official one:

\begin{code}

is-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                    → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇
is-order-preserving α β f = (x y : ⟨ α ⟩) → x ≺⟨ α ⟩ y → f x ≺⟨ β ⟩ f y

is-order-equiv : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇
is-order-equiv α β f = is-order-preserving α β f
                     × (Σ e ꞉ is-equiv f , is-order-preserving β α (inverse f e))

_≃ₒ_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
α ≃ₒ β = Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-order-equiv α β f

\end{code}

See the module OrdinalOfOrdinals for a proof that α ≃ₒ β is
canonically equivalent to α ≡ β. (For historical reasons, that proof
doesn't use the structure identity principle.)

\begin{code}

≃ₒ-sym : ∀ {𝓤} {𝓥} (α : Ordinal 𝓤) (β : Ordinal 𝓥 )
       → α ≃ₒ β → β ≃ₒ α
≃ₒ-sym α β (f , p , e , q) = inverse f e , q , inverse-is-equiv f e , p

≃ₒ-trans : ∀ {𝓤} {𝓥} {𝓦} (α : Ordinal 𝓤) (β : Ordinal 𝓥 ) (γ : Ordinal 𝓦)
         → α ≃ₒ β → β ≃ₒ γ → α ≃ₒ γ
≃ₒ-trans α β γ (f , p , e , q) (f' , p' , e' , q') =
  f' ∘ f ,
  (λ x y l → p' (f x) (f y) (p x y l)) ,
  ∘-is-equiv e e' ,
  (λ x y l → q (inverse f' e' x) (inverse f' e' y) (q' x y l))

\end{code}
