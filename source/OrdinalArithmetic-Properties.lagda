Martin Escardo, 18 January 2021.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Univalence

module OrdinalArithmetic-Properties
       (ua : Univalence)
       where

open import UF-Base
open import UF-Subsingletons
open import UF-Equiv
open import UF-UA-FunExt
open import UF-FunExt
open import UF-EquivalenceExamples

private
 fe : FunExt
 fe = FunExt-from-Univalence ua

open import SpartanMLTT
open import OrdinalsType
open import OrdinalOfOrdinals ua
open import OrdinalArithmetic fe

𝟘ₒ-left-neutral : (α : Ordinal 𝓤) → 𝟘ₒ +ₒ α ≡ α
𝟘ₒ-left-neutral α = eqtoidₒ (𝟘ₒ +ₒ α) α h
 where
  f : 𝟘 + ⟨ α ⟩ → ⟨ α ⟩
  f = ⌜ 𝟘-lneutral ⌝

  f-preserves-order : (x y : 𝟘 + ⟨ α ⟩) → x ≺⟨ 𝟘ₒ +ₒ α ⟩ y → f x ≺⟨ α ⟩ f y
  f-preserves-order (inr x) (inr y) l = l

  f-reflects-order : (x y : 𝟘 + ⟨ α ⟩) → f x ≺⟨ α ⟩ f y → x ≺⟨ 𝟘ₒ +ₒ α ⟩ y
  f-reflects-order (inr x) (inr y) l = l


  h : (𝟘ₒ +ₒ α) ≃ₒ α
  h = f , order-equiv-criterion (𝟘ₒ +ₒ α) α f
           (⌜⌝-is-equiv 𝟘-lneutral) f-preserves-order f-reflects-order

𝟘ₒ-right-neutral : (α : Ordinal 𝓤) → α  +ₒ 𝟘ₒ ≡ α
𝟘ₒ-right-neutral α = eqtoidₒ (α +ₒ 𝟘ₒ) α h
 where
  f : ⟨ α ⟩ + 𝟘 → ⟨ α ⟩
  f = ⌜ 𝟘-rneutral' ⌝

  f-preserves-order : is-order-preserving (α  +ₒ 𝟘ₒ) α f
  f-preserves-order (inl x) (inl y) l = l

  f-reflects-order : is-order-reflecting (α  +ₒ 𝟘ₒ) α f
  f-reflects-order (inl x) (inl y) l = l


  h : (α +ₒ 𝟘ₒ) ≃ₒ α
  h = f , order-equiv-criterion (α +ₒ 𝟘ₒ) α f
           (⌜⌝-is-equiv 𝟘-rneutral') f-preserves-order f-reflects-order

+ₒ-assoc : (α β γ : Ordinal 𝓤) → (α  +ₒ β) +ₒ γ ≡ α  +ₒ (β +ₒ γ)
+ₒ-assoc α β γ = eqtoidₒ ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ)) h
 where
  f : ⟨ (α +ₒ β) +ₒ γ ⟩ → ⟨ α +ₒ (β +ₒ γ) ⟩
  f = ⌜ +assoc ⌝

  f-preserves-order : is-order-preserving  ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ)) f
  f-preserves-order (inl (inl x)) (inl (inl y)) l = l
  f-preserves-order (inl (inl x)) (inl (inr y)) l = l
  f-preserves-order (inl (inr x)) (inl (inr y)) l = l
  f-preserves-order (inl (inl x)) (inr y)       l = l
  f-preserves-order (inl (inr x)) (inr y)       l = l
  f-preserves-order (inr x)       (inr y)       l = l


  f-reflects-order : is-order-reflecting ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ)) f
  f-reflects-order (inl (inl x)) (inl (inl y)) l = l
  f-reflects-order (inl (inl x)) (inl (inr y)) l = l
  f-reflects-order (inl (inr x)) (inl (inr y)) l = l
  f-reflects-order (inl (inl x)) (inr y)       l = l
  f-reflects-order (inl (inr x)) (inr y)       l = l
  f-reflects-order (inr x)       (inl (inl y)) l = l
  f-reflects-order (inr x)       (inl (inr y)) l = l
  f-reflects-order (inr x)       (inr y)       l = l


  h : ((α  +ₒ β) +ₒ γ) ≃ₒ (α  +ₒ (β +ₒ γ))
  h = f , order-equiv-criterion ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ)) f
           (⌜⌝-is-equiv +assoc) f-preserves-order f-reflects-order

+ₒ-↓-left : {α β : Ordinal 𝓤} (a : ⟨ α ⟩)
          → (α ↓ a) ≡ ((α  +ₒ β) ↓ inl a)
+ₒ-↓-left {𝓤} {α} {β} a = h
 where
  γ = α ↓ a
  δ = (α  +ₒ β) ↓ inl a

  f : ⟨ γ ⟩ → ⟨ δ ⟩
  f (x , l) = inl x , l

  g :  ⟨ δ ⟩ → ⟨ γ ⟩
  g (inl x , l) = x , l

  η : g ∘ f ∼ id
  η u = refl

  ε : f ∘ g ∼ id
  ε (inl x , l) = refl

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f (g , η , ε)

  f-is-order-preserving : is-order-preserving γ δ f
  f-is-order-preserving (x , _) (x' , _) l = l


  g-is-order-preserving : is-order-preserving δ γ g
  g-is-order-preserving (inl x , _) (inl x' , _) l = l

  h : γ ≡ δ
  h = eqtoidₒ γ δ (f , f-is-order-preserving , f-is-equiv , g-is-order-preserving)


+ₒ-↓-right : {α β : Ordinal 𝓤} (b : ⟨ β ⟩)
           → (α  +ₒ (β ↓ b)) ≡ ((α  +ₒ β) ↓ inr b)
+ₒ-↓-right {𝓤} {α} {β} b = h
 where
  γ = α  +ₒ (β ↓ b)
  δ = (α  +ₒ β) ↓ inr b

  f : ⟨ γ ⟩ → ⟨ δ ⟩
  f (inl a)       = inl a , *
  f (inr (y , l)) = inr y , l

  g :  ⟨ δ ⟩ → ⟨ γ ⟩
  g (inl a , *) = inl a
  g (inr y , l) = inr (y , l)

  η : g ∘ f ∼ id
  η (inl a)       = refl
  η (inr (y , l)) = refl

  ε : f ∘ g ∼ id
  ε (inl a , *) = refl
  ε (inr y , l) = refl

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f (g , η , ε)

  f-is-order-preserving : is-order-preserving γ δ f
  f-is-order-preserving (inl _) (inl _) l = l
  f-is-order-preserving (inl _) (inr _) l = l
  f-is-order-preserving (inr _) (inr _) l = l

  g-is-order-preserving : is-order-preserving δ γ g
  g-is-order-preserving (inl _ , _) (inl _ , _) l = l
  g-is-order-preserving (inl _ , _) (inr _ , _) l = l
  g-is-order-preserving (inr _ , _) (inr _ , _) l = l

  h : γ ≡ δ
  h = eqtoidₒ γ δ (f , f-is-order-preserving , f-is-equiv , g-is-order-preserving)

+ₒ-increasing-on-right : {α β γ : Ordinal 𝓤} → β ⊲ γ → (α  +ₒ β) ⊲ (α  +ₒ γ)
+ₒ-increasing-on-right {𝓤} {α} {β} {γ} (c , p) = inr c , q
 where
  q =  (α +ₒ β)           ≡⟨ ap (α +ₒ_) p ⟩
       (α +ₒ (γ ↓ c))     ≡⟨ +ₒ-↓-right c ⟩
       ((α +ₒ γ) ↓ inr c) ∎

+ₒ-⊲-left : {α β : Ordinal 𝓤} (a : ⟨ α ⟩)
          → (α  ↓ a) ⊲ (α  +ₒ β)
+ₒ-⊲-left {𝓤} {α} {β} a = inl a , +ₒ-↓-left a

+ₒ-right-monotone : (α β γ : Ordinal 𝓤)
                  → β ≼ γ
                  → (α  +ₒ β) ≼ (α  +ₒ γ)
+ₒ-right-monotone α β γ m = to-≼ ϕ
 where
  l : (a : ⟨ α ⟩) → ((α  +ₒ β) ↓ inl a) ⊲  (α  +ₒ γ)
  l a = o
   where
    n : (α  ↓ a) ⊲ (α  +ₒ γ)
    n = +ₒ-⊲-left a

    o : ((α  +ₒ β) ↓ inl a) ⊲  (α  +ₒ γ)
    o = transport (_⊲ (α +ₒ γ)) (+ₒ-↓-left a) n

  r : (b : ⟨ β ⟩) → ((α  +ₒ β) ↓ inr b) ⊲  (α  +ₒ γ)
  r b = s
   where
    o : (β ↓ b) ⊲ γ
    o = from-≼ m b

    p : (α +ₒ (β ↓ b)) ⊲ (α  +ₒ γ)
    p = +ₒ-increasing-on-right o

    q : α +ₒ (β ↓ b) ≡ (α  +ₒ β) ↓ inr b
    q = +ₒ-↓-right b

    s : ((α  +ₒ β) ↓ inr b) ⊲  (α  +ₒ γ)
    s = transport (_⊲  (α  +ₒ γ)) q p

  ϕ : (x : ⟨ α  +ₒ β ⟩) → ((α  +ₒ β) ↓ x) ⊲  (α  +ₒ γ)
  ϕ = dep-cases l r

{- TODO
+ₒ-left-cancellable' : (α β γ : Ordinal 𝓤)
                     → (α  +ₒ β) ≼ (α  +ₒ γ)
                     → β ≼ γ
+ₒ-left-cancellable' {𝓤} α β γ = Transfinite-induction (O 𝓤) P ϕ β
{-
Pick u ◁ β. Then u ≡ β ↓ b for some b : ⟨ β ⟩.
Then u ◁ α  +ₒ β because β ↓ b ≡ δ

γ ≡ δ


-}
 where
  P : Ordinal 𝓤 → 𝓤 ⁺ ̇
  P β = (α  +ₒ β) ≼ (α  +ₒ γ) → β ≼ γ

  ϕ : (β : Ordinal 𝓤)
    → ((β' : Ordinal 𝓤 ) → β' ⊲ β → P β')
    → P β
  ϕ β f p β' l = g
   where
    IH : (α +ₒ β') ≼ (α +ₒ γ) → β' ≼ γ
    IH = f β' l
    r : (α +ₒ β') ≼ (α +ₒ γ)
    r = {!!}
    g : β' ⊲ γ
    g = {!≼⟨ OrdinalOfOrdinals 𝓤 ⟩!}


+ₒ-left-cancellable : (α β γ : Ordinal 𝓤) → (α  +ₒ β) ≡ (α  +ₒ γ) → β ≡ γ
+ₒ-left-cancellable {𝓤} = Transfinite-induction (OrdinalOfOrdinals 𝓤) P ϕ
 where
  P : Ordinal 𝓤 → 𝓤 ⁺ ̇
  P α = (β γ : Ordinal 𝓤) → (α  +ₒ β) ≡ (α  +ₒ γ) → β ≡ γ

  ϕ : (α : Ordinal 𝓤)
    → ((α' : Ordinal 𝓤 ) → α' ⊲ α → P α')
    → P α
  ϕ α f p = {!!}
   where
    IH : {!!}
    IH = {!!}
-}
\end{code}
