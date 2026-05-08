Martin Escardo, 18 January 2021.

Several additions by Tom de Jong in May and June 2024 and July 2025.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.AdditionProperties
       (ua : Univalence)
       where

open import UF.Base
open import UF.ClassicalLogic
open import UF.Embeddings hiding (⌊_⌋)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import Notation.CanonicalMap
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying

𝟘ₒ-left-neutral : (α : Ordinal 𝓤) → 𝟘ₒ +ₒ α ＝ α
𝟘ₒ-left-neutral {𝓤} α = eqtoidₒ (ua 𝓤) fe' (𝟘ₒ +ₒ α) α h
 where
  f : 𝟘 + ⟨ α ⟩ → ⟨ α ⟩
  f = ⌜ 𝟘-lneutral ⌝

  f-preserves-order : (x y : 𝟘 + ⟨ α ⟩) → x ≺⟨ 𝟘ₒ +ₒ α ⟩ y → f x ≺⟨ α ⟩ f y
  f-preserves-order (inr x) (inr y) l = l

  f-reflects-order : (x y : 𝟘 + ⟨ α ⟩) → f x ≺⟨ α ⟩ f y → x ≺⟨ 𝟘ₒ +ₒ α ⟩ y
  f-reflects-order (inr x) (inr y) l = l


  h : (𝟘ₒ +ₒ α) ≃ₒ α
  h = f , order-preserving-reflecting-equivs-are-order-equivs (𝟘ₒ +ₒ α) α f
           (⌜⌝-is-equiv 𝟘-lneutral) f-preserves-order f-reflects-order

𝟘ₒ-right-neutral : (α : Ordinal 𝓤) → α  +ₒ 𝟘ₒ ＝ α
𝟘ₒ-right-neutral α = eqtoidₒ (ua _) fe' (α +ₒ 𝟘ₒ) α h
 where
  f : ⟨ α ⟩ + 𝟘 → ⟨ α ⟩
  f = ⌜ 𝟘-rneutral' ⌝

  f-preserves-order : is-order-preserving (α  +ₒ 𝟘ₒ) α f
  f-preserves-order (inl x) (inl y) l = l

  f-reflects-order : is-order-reflecting (α  +ₒ 𝟘ₒ) α f
  f-reflects-order (inl x) (inl y) l = l


  h : (α +ₒ 𝟘ₒ) ≃ₒ α
  h = f , order-preserving-reflecting-equivs-are-order-equivs (α +ₒ 𝟘ₒ) α f
           (⌜⌝-is-equiv 𝟘-rneutral') f-preserves-order f-reflects-order

+ₒ-assoc : (α β γ : Ordinal 𝓤) → (α  +ₒ β) +ₒ γ ＝ α  +ₒ (β +ₒ γ)
+ₒ-assoc α β γ = eqtoidₒ (ua _) fe' ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ)) h
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
  h = f , order-preserving-reflecting-equivs-are-order-equivs
           ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ))
           f (⌜⌝-is-equiv +assoc) f-preserves-order f-reflects-order

+ₒ-↓-left : {α β : Ordinal 𝓤} (a : ⟨ α ⟩)
          → (α ↓ a) ＝ ((α +ₒ β) ↓ inl a)
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

  h : γ ＝ δ
  h = eqtoidₒ (ua 𝓤) fe' γ δ
       (f , f-is-order-preserving , f-is-equiv , g-is-order-preserving)

+ₒ-left-⊴ : (α β : Ordinal 𝓤)
          → α ⊴ α +ₒ β
+ₒ-left-⊴ α β = to-⊴ α (α +ₒ β) (λ a → inl a , +ₒ-↓-left a)

+ₒ-↓-right : {α β : Ordinal 𝓤} (b : ⟨ β ⟩)
           → (α +ₒ (β ↓ b)) ＝ ((α +ₒ β) ↓ inr b)
+ₒ-↓-right {𝓤} {α} {β} b = h
 where
  γ = α  +ₒ (β ↓ b)
  δ = (α  +ₒ β) ↓ inr b

  f : ⟨ γ ⟩ → ⟨ δ ⟩
  f (inl a)       = inl a , ⋆
  f (inr (y , l)) = inr y , l

  g :  ⟨ δ ⟩ → ⟨ γ ⟩
  g (inl a , ⋆) = inl a
  g (inr y , l) = inr (y , l)

  η : g ∘ f ∼ id
  η (inl a)       = refl
  η (inr (y , l)) = refl

  ε : f ∘ g ∼ id
  ε (inl a , ⋆) = refl
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

  h : γ ＝ δ
  h = eqtoidₒ (ua 𝓤) fe' γ δ
       (f , f-is-order-preserving , f-is-equiv , g-is-order-preserving)

+ₒ-⊲-left : {α β : Ordinal 𝓤} (a : ⟨ α ⟩)
          → (α ↓ a) ⊲ (α +ₒ β)
+ₒ-⊲-left {𝓤} {α} {β} a = inl a , +ₒ-↓-left a

+ₒ-⊲-right : {α β : Ordinal 𝓤} (b : ⟨ β ⟩)
           → (α +ₒ (β ↓ b)) ⊲ (α +ₒ β)
+ₒ-⊲-right {𝓤} {α} {β} b = inr b , +ₒ-↓-right {𝓤} {α} {β} b

+ₒ-increasing-on-right : {α β γ : Ordinal 𝓤}
                       → β ⊲ γ
                       → (α +ₒ β) ⊲ (α +ₒ γ)
+ₒ-increasing-on-right {𝓤} {α} {β} {γ} (c , p) = inr c , q
 where
  q =  (α +ₒ β)           ＝⟨ ap (α +ₒ_) p ⟩
       (α +ₒ (γ ↓ c))     ＝⟨ +ₒ-↓-right c ⟩
       ((α +ₒ γ) ↓ inr c) ∎

+ₒ-right-monotone : (α β γ : Ordinal 𝓤)
                  → β ≼ γ
                  → (α +ₒ β) ≼ (α +ₒ γ)
+ₒ-right-monotone α β γ m = to-≼ ϕ
 where
  l : (a : ⟨ α ⟩) → ((α +ₒ β) ↓ inl a) ⊲  (α +ₒ γ)
  l a = o
   where
    n : (α  ↓ a) ⊲ (α +ₒ γ)
    n = +ₒ-⊲-left a

    o : ((α +ₒ β) ↓ inl a) ⊲  (α +ₒ γ)
    o = transport (_⊲ (α +ₒ γ)) (+ₒ-↓-left a) n

  r : (b : ⟨ β ⟩) → ((α +ₒ β) ↓ inr b) ⊲ (α +ₒ γ)
  r b = s
   where
    o : (β ↓ b) ⊲ γ
    o = from-≼ m b

    p : (α +ₒ (β ↓ b)) ⊲ (α +ₒ γ)
    p = +ₒ-increasing-on-right o

    q : α +ₒ (β ↓ b) ＝ (α +ₒ β) ↓ inr b
    q = +ₒ-↓-right b

    s : ((α +ₒ β) ↓ inr b) ⊲ (α +ₒ γ)
    s = transport (_⊲ (α  +ₒ γ)) q p

  ϕ : (x : ⟨ α +ₒ β ⟩) → ((α +ₒ β) ↓ x) ⊲ (α +ₒ γ)
  ϕ = dep-cases l r

+ₒ-right-monotone-⊴ : (α : Ordinal 𝓤) → is-⊴-preserving (α +ₒ_)
+ₒ-right-monotone-⊴ α β γ l =
 ≼-gives-⊴ (α +ₒ β) (α +ₒ γ) (+ₒ-right-monotone α β γ (⊴-gives-≼ β γ l))

\end{code}

Added by Tom de Jong in July/October 2025. The following proof has
better computational properties (and is arguably simpler) than the one
above.

\begin{code}

+ₒ-right-monotone-⊴' : (α : Ordinal 𝓤) → is-⊴-preserving (α +ₒ_)
+ₒ-right-monotone-⊴' α β γ 𝕗@(f , f-sim) = g , g-init-seg , g-order-pres
 where
  g : ⟨ α +ₒ β ⟩ → ⟨ α +ₒ γ ⟩
  g (inl a) = inl a
  g (inr b) = inr (f b)
  g-order-pres : is-order-preserving (α +ₒ β) (α +ₒ γ) g
  g-order-pres (inl a) (inl a') l = l
  g-order-pres (inl a) (inr b)  l = l
  g-order-pres (inr b) (inr b') l =
   simulations-are-order-preserving β γ f f-sim b b' l
  g-init-seg : is-initial-segment (α +ₒ β) (α +ₒ γ) g
  g-init-seg (inl a) (inl a') l = inl a' , l , refl
  g-init-seg (inr b) (inl a)  l = inl a , ⋆ , refl
  g-init-seg (inr b) (inr b') l =
   inr (pr₁ I) , pr₁ (pr₂ I) , ap inr (pr₂ (pr₂ I))
    where
     I : Σ b'' ꞉ ⟨ β ⟩ , (b'' ≺⟨ β ⟩ b) × (f b'' ＝ b')
     I = simulations-are-initial-segments β γ f f-sim b b' l

\end{code}

TODO. Find better names for the following lemmas.

\begin{code}

AP-lemma₀ : {α β : Ordinal 𝓤}
          → α ≼ (α +ₒ β)
AP-lemma₀ {𝓤} {α} {β} = to-≼ ϕ
 where
  ϕ : (a : ⟨ α ⟩) → Σ z ꞉ ⟨ α +ₒ β ⟩ , (α ↓ a) ＝ ((α +ₒ β) ↓ z)
  ϕ a = inl a , (+ₒ-↓-left a)

AP-lemma₁ : {α β : Ordinal 𝓤}
            (a : ⟨ α ⟩)
          → (α +ₒ β) ≠ (α ↓ a)
AP-lemma₁ {𝓤} {α} {β} a p = irrefl (OO 𝓤) (α +ₒ β) m
 where
  l : (α +ₒ β) ⊲ α
  l = (a , p)

  m : (α +ₒ β) ⊲ (α +ₒ β)
  m = AP-lemma₀ (α +ₒ β) l

AP-lemma₂ : {α β : Ordinal 𝓤} (a : ⟨ α ⟩)
          → α ＝ β
          → Σ b ꞉ ⟨ β ⟩ , (α ↓ a) ＝ (β ↓ b)
AP-lemma₂ a refl = a , refl

AP-lemma₃ : {α β γ : Ordinal 𝓤} (b : ⟨ β ⟩) (z : ⟨ α +ₒ γ ⟩)
          → ((α +ₒ β) ↓ inr b) ＝ ((α +ₒ γ) ↓ z)
          → Σ c ꞉ ⟨ γ ⟩ , z ＝ inr c
AP-lemma₃ {𝓤} {α} {β} {γ} b (inl a) p = 𝟘-elim (AP-lemma₁ a q)
 where
  q : (α +ₒ (β ↓ b)) ＝ (α ↓ a)
  q = +ₒ-↓-right b ∙ p ∙ (+ₒ-↓-left a)⁻¹

AP-lemma₃ b (inr c) p = c , refl

+ₒ-left-cancellable : (α β γ : Ordinal 𝓤)
                    → (α +ₒ β) ＝ (α +ₒ γ)
                    → β ＝ γ
+ₒ-left-cancellable {𝓤} α = g
 where
  P : Ordinal 𝓤 → 𝓤 ⁺ ̇
  P β = ∀ γ → (α +ₒ β) ＝ (α +ₒ γ) → β ＝ γ

  ϕ : ∀ β
    → (∀ b → P (β ↓ b))
    → P β
  ϕ β f γ p = Extensionality (OO 𝓤) β γ (to-≼ u) (to-≼ v)
   where
    u : (b : ⟨ β ⟩) → (β ↓ b) ⊲ γ
    u b = c , t
     where
      z : ⟨ α +ₒ γ ⟩
      z = pr₁ (AP-lemma₂ (inr b) p)

      r : ((α +ₒ β) ↓ inr b) ＝ ((α +ₒ γ) ↓ z)
      r = pr₂ (AP-lemma₂ (inr b) p)

      c : ⟨ γ ⟩
      c = pr₁ (AP-lemma₃ b z r)

      s : z ＝ inr c
      s = pr₂ (AP-lemma₃ b z r)

      q = (α +ₒ (β ↓ b))     ＝⟨ +ₒ-↓-right b ⟩
          ((α +ₒ β) ↓ inr b) ＝⟨ r ⟩
          ((α +ₒ γ) ↓ z)     ＝⟨ ap ((α +ₒ γ) ↓_) s ⟩
          ((α +ₒ γ) ↓ inr c) ＝⟨ (+ₒ-↓-right c)⁻¹ ⟩
          (α +ₒ (γ ↓ c))     ∎

      t : (β ↓ b) ＝ (γ ↓ c)
      t = f b (γ ↓ c) q

    v : (c : ⟨ γ ⟩) → (γ ↓ c) ⊲ β
    v c = b , (t ⁻¹)
     where
      z : ⟨ α +ₒ β ⟩
      z = pr₁ (AP-lemma₂ (inr c) (p ⁻¹))

      r : ((α +ₒ γ) ↓ inr c) ＝ ((α +ₒ β) ↓ z)
      r = pr₂ (AP-lemma₂ (inr c) (p ⁻¹))

      b : ⟨ β ⟩
      b = pr₁ (AP-lemma₃ c z r)

      s : z ＝ inr b
      s = pr₂ (AP-lemma₃ c z r)

      q = (α +ₒ (γ ↓ c))     ＝⟨ +ₒ-↓-right c ⟩
          ((α +ₒ γ) ↓ inr c) ＝⟨ r ⟩
          ((α +ₒ β) ↓ z)     ＝⟨ ap ((α +ₒ β) ↓_) s ⟩
          ((α +ₒ β) ↓ inr b) ＝⟨ (+ₒ-↓-right b)⁻¹ ⟩
          (α +ₒ (β ↓ b))     ∎

      t : (β ↓ b) ＝ (γ ↓ c)
      t = f b (γ ↓ c) (q ⁻¹)

  g : (β : Ordinal 𝓤) → P β
  g = transfinite-induction-on-OO P ϕ


left-+ₒ-is-embedding : (α : Ordinal 𝓤) → is-embedding (α +ₒ_)
left-+ₒ-is-embedding α = lc-maps-into-sets-are-embeddings (α +ₒ_)
                           (λ {β} {γ} → +ₒ-left-cancellable α β γ)
                           (the-type-of-ordinals-is-a-set (ua _) fe')
\end{code}

This implies that the function α +ₒ_ reflects the _⊲_ ordering:

\begin{code}

+ₒ-left-reflects-⊲ : (α β γ : Ordinal 𝓤)
                   → (α +ₒ β) ⊲ (α +ₒ γ)
                   → β ⊲ γ
+ₒ-left-reflects-⊲ α β γ (inl a , p) = 𝟘-elim (AP-lemma₁ a q)
   where
    q : (α +ₒ β) ＝ (α ↓ a)
    q = p ∙ (+ₒ-↓-left a)⁻¹

+ₒ-left-reflects-⊲ α β γ (inr c , p) = l
   where
    q : (α +ₒ β) ＝ (α +ₒ (γ ↓ c))
    q = p ∙ (+ₒ-↓-right c)⁻¹

    r : β ＝ (γ ↓ c)
    r = +ₒ-left-cancellable α β (γ ↓ c) q

    l : β ⊲ γ
    l = c , r

\end{code}

And in turn this implies that the function α +ₒ_ reflects the _≼_
partial ordering:

\begin{code}

+ₒ-left-reflects-≼ : (α β γ : Ordinal 𝓤)
                   → (α +ₒ β) ≼ (α +ₒ γ)
                   → β ≼ γ
+ₒ-left-reflects-≼ {𝓤} α β γ l = to-≼ (ϕ β l)
 where
  ϕ : (β : Ordinal 𝓤)
    → (α +ₒ β) ≼ (α +ₒ γ)
    → (b : ⟨ β ⟩) → (β ↓ b) ⊲ γ
  ϕ β l b = o
   where
    m : (α +ₒ (β ↓ b)) ⊲ (α +ₒ β)
    m = +ₒ-⊲-right b

    n : (α +ₒ (β ↓ b)) ⊲ (α +ₒ γ)
    n = l (α +ₒ (β ↓ b)) m

    o : (β ↓ b) ⊲ γ
    o = +ₒ-left-reflects-⊲ α (β ↓ b) γ n

+ₒ-left-reflects-⊴ : (α β γ : Ordinal 𝓤)
                   → (α +ₒ β) ⊴ (α +ₒ γ)
                   → β ⊴ γ
+ₒ-left-reflects-⊴ α β γ l =
 ≼-gives-⊴ β γ (+ₒ-left-reflects-≼ α β γ (⊴-gives-≼ (α +ₒ β) (α +ₒ γ) l))

\end{code}

Added 4th April 2022.

\begin{code}

𝟘ₒ-least-⊴ : (α : Ordinal 𝓤) → 𝟘ₒ {𝓤} ⊴ α
𝟘ₒ-least-⊴ α = unique-from-𝟘 , (λ x y l → 𝟘-elim x) , (λ x y l → 𝟘-elim x)

𝟘ₒ-least : (α : Ordinal 𝓤) → 𝟘ₒ {𝓤} ≼ α
𝟘ₒ-least α = ⊴-gives-≼ 𝟘ₒ α (𝟘ₒ-least-⊴ α)

\end{code}

Added 11 April 2025 by Tom de Jong.

\begin{code}

initial-segment-of-least-element-is-𝟘ₒ : (α : Ordinal 𝓤) (a : ⟨ α ⟩)
                                       → is-least α a
                                       → α ↓ a ＝ 𝟘ₒ
initial-segment-of-least-element-is-𝟘ₒ α a a-is-least =
 ⊴-antisym (α ↓ a) 𝟘ₒ
  (to-⊴ (α ↓ a) 𝟘ₒ (λ (x , l) → 𝟘-elim (least-is-minimal α a a-is-least x l)))
  (𝟘ₒ-least-⊴ (α ↓ a))

\end{code}

Originally added 21st April 2022 by Martín Escardó.
Moved up here on 27th May 2024 by Tom de Jong.

\begin{code}

successor-lemma-left : (α : Ordinal 𝓤) (x : ⟨ α ⟩) → ((α +ₒ 𝟙ₒ) ↓ inl x) ⊴ α
successor-lemma-left α x = III
   where
    I : (α ↓ x) ⊴ α
    I = segment-⊴ α x

    II : (α ↓ x) ＝ ((α +ₒ 𝟙ₒ) ↓ inl x)
    II = +ₒ-↓-left x

    III : ((α +ₒ 𝟙ₒ) ↓ inl x) ⊴ α
    III = transport (_⊴ α) II I

successor-lemma-right : (α : Ordinal 𝓤) → (α +ₒ 𝟙ₒ) ↓ inr ⋆ ＝ α
successor-lemma-right α  = III
 where
  I : (𝟙ₒ ↓ ⋆) ⊴ 𝟘ₒ
  I = (λ x → 𝟘-elim (pr₂ x)) , (λ x → 𝟘-elim (pr₂ x)) , (λ x → 𝟘-elim (pr₂ x))

  II : (𝟙ₒ ↓ ⋆) ＝ 𝟘ₒ
  II = ⊴-antisym _ _ I (𝟘ₒ-least-⊴ (𝟙ₒ ↓ ⋆))

  III : (α +ₒ 𝟙ₒ) ↓ inr ⋆ ＝ α
  III = (α +ₒ 𝟙ₒ) ↓ inr ⋆ ＝⟨ (+ₒ-↓-right ⋆)⁻¹ ⟩
        α +ₒ (𝟙ₒ ↓ ⋆)     ＝⟨ ap (α +ₒ_) II ⟩
        α +ₒ 𝟘ₒ           ＝⟨ 𝟘ₒ-right-neutral α ⟩
        α                 ∎

successor-increasing : (α : Ordinal 𝓤) → α ⊲ (α +ₒ 𝟙ₒ)
successor-increasing α = inr ⋆ , ((successor-lemma-right α)⁻¹)

\end{code}

Added on 24th May 2024 by Tom de Jong.

\begin{code}

upper-bound-of-successors-of-initial-segments :
 (α : Ordinal 𝓤) (a : ⟨ α ⟩) → ((α ↓ a) +ₒ 𝟙ₒ) ⊴ α
upper-bound-of-successors-of-initial-segments α a = to-⊴ ((α ↓ a) +ₒ 𝟙ₒ) α I
 where
  I : (x : ⟨ (α ↓ a) +ₒ 𝟙ₒ ⟩) → (((α ↓ a) +ₒ 𝟙ₒ) ↓ x) ⊲ α
  I (inl (b , l)) = b , (((α ↓ a) +ₒ 𝟙ₒ) ↓ inl (b , l) ＝⟨ e₁ ⟩
                         (α ↓ a) ↓ (b , l)             ＝⟨ e₂ ⟩
                         α ↓ b                         ∎)
   where
    e₁ = (+ₒ-↓-left (b , l)) ⁻¹
    e₂ = iterated-↓ α a b l
  I (inr ⋆) = a , successor-lemma-right (α ↓ a)

\end{code}

End of addition.

Classically, if α ≼ β then there is (a necessarily unique) γ with
α +ₒ γ ＝ β. But this not necessarily the case constructively. For
that purpose, we first characterize the order of subsingleton
ordinals.

\begin{code}

module _ {𝓤 : Universe}
         (P Q : 𝓤 ̇ )
         (P-is-prop : is-prop P)
         (Q-is-prop : is-prop Q)
       where

 private
   p q : Ordinal 𝓤
   p = prop-ordinal P P-is-prop
   q = prop-ordinal Q Q-is-prop

 fact₀ : p ⊲ q → ¬ P × Q
 fact₀ (y , r) = u , y
  where
   s : P ＝ (Q × 𝟘)
   s = ap ⟨_⟩ r

   u : ¬ P
   u p = 𝟘-elim (pr₂ (⌜ idtoeq P (Q × 𝟘) s ⌝ p))

 fact₀-converse : ¬ P × Q → p ⊲ q
 fact₀-converse (u , y) = (y , g)
  where
   r : P ＝ Q × 𝟘
   r = univalence-gives-propext (ua 𝓤)
        P-is-prop
        ×-𝟘-is-prop
        (λ p → 𝟘-elim (u p))
        (λ (q , z) → 𝟘-elim z)

   g : p ＝ (q ↓ y)
   g = to-Σ-＝ (r ,
       to-Σ-＝ (dfunext fe' (λ (y , z) → 𝟘-elim z) ,
               being-well-order-is-prop (underlying-order (q ↓ y)) fe _ _))

 fact₁ : p ≼ q → (P → Q)
 fact₁ l x = pr₁ (from-≼ {𝓤} {p} {q} l x)

 fact₁-converse : (P → Q) → p ≼ q
 fact₁-converse f = to-≼ {𝓤} {p} {q} ϕ
  where
   r : P × 𝟘 ＝ Q × 𝟘
   r = univalence-gives-propext (ua 𝓤)
        ×-𝟘-is-prop
        ×-𝟘-is-prop
        (λ (p , z) → 𝟘-elim z)
        (λ (q , z) → 𝟘-elim z)

   ϕ : (x : ⟨ p ⟩) → (p ↓ x) ⊲ q
   ϕ x = f x , s
    where
     s : ((P × 𝟘) , (λ x x' → 𝟘) , _) ＝ ((Q × 𝟘) , (λ y y' → 𝟘) , _)
     s = to-Σ-＝ (r ,
         to-Σ-＝ (dfunext fe' (λ z → 𝟘-elim (pr₂ z)) ,
                 being-well-order-is-prop (underlying-order (q ↓ f x)) fe _ _))
\end{code}

The existence of ordinal subtraction implies excluded middle.

\begin{code}

existence-of-subtraction : (𝓤 : Universe) → 𝓤 ⁺ ̇
existence-of-subtraction 𝓤 = (α β : Ordinal 𝓤)
                           → α ≼ β
                           → Σ γ ꞉ Ordinal 𝓤 , α +ₒ γ ＝ β

existence-of-subtraction-is-prop : is-prop (existence-of-subtraction 𝓤)
existence-of-subtraction-is-prop = Π₃-is-prop fe'
                                    (λ α β l → left-+ₒ-is-embedding α β)

ordinal-subtraction-gives-excluded-middle : existence-of-subtraction 𝓤 → EM 𝓤
ordinal-subtraction-gives-excluded-middle {𝓤} ϕ P P-is-prop = g
 where
  α = prop-ordinal P P-is-prop
  β = prop-ordinal 𝟙 𝟙-is-prop
  σ = ϕ α β (fact₁-converse {𝓤} P 𝟙 P-is-prop 𝟙-is-prop (λ _ → ⋆))

  γ : Ordinal 𝓤
  γ = pr₁ σ

  r : α +ₒ γ ＝ β
  r = pr₂ σ

  s : P + ⟨ γ ⟩ ＝ 𝟙
  s = ap ⟨_⟩ r

  t : P + ⟨ γ ⟩
  t = idtofun 𝟙 (P + ⟨ γ ⟩) (s ⁻¹) ⋆

  f : ⟨ γ ⟩ → ¬ P
  f c p = z
   where
    A : 𝓤 ̇ → 𝓤 ̇
    A X = Σ x ꞉ X , Σ y ꞉ X , x ≠ y

    u : A (P + ⟨ γ ⟩)
    u = inl p , inr c , +disjoint

    v : ¬ A 𝟙
    v (x , y , d) = d (𝟙-is-prop x y)

    w : A (P + ⟨ γ ⟩) → A 𝟙
    w = transport A s

    z : 𝟘
    z = v (w u)

  g : P + ¬ P
  g = Cases t inl (λ c → inr (f c))

\end{code}

TODO. Another example where subtraction doesn't necessarily exist is
the situation (ω +ₒ 𝟙ₒ) ≼ ℕ∞ₒ, discussed in the module
OrdinalOfOrdinals. The types ω +ₒ 𝟙ₒ and ℕ∞ₒ are equal if and only if
LPO holds. Without assuming LPO, the image of the inclusion (ω +ₒ 𝟙ₒ)
→ ℕ∞ₒ, has empty complement, and so there is nothing that can be added
to (ω +ₒ 𝟙ₒ) to get ℕ∞ₒ, unless LPO holds.

\begin{code}

open import UF.Retracts
open import UF.SubtypeClassifier

retract-Ω-of-Ordinal : retract (Ω 𝓤) of (Ordinal 𝓤)
retract-Ω-of-Ordinal {𝓤} = r , s , η
 where
  s : Ω 𝓤 → Ordinal 𝓤
  s (P , i) = prop-ordinal P i

  r : Ordinal 𝓤 → Ω 𝓤
  r α = has-least α , having-least-is-prop fe' α

  η : r ∘ s ∼ id
  η (P , i) = to-subtype-＝ (λ _ → being-prop-is-prop fe') t
   where
    f : P → has-least (prop-ordinal P i)
    f p = p , (λ x u → id)

    g : has-least (prop-ordinal P i) → P
    g (p , _) = p

    t : has-least (prop-ordinal P i) ＝ P
    t = pe 𝓤 (having-least-is-prop fe' (prop-ordinal P i)) i g f

\end{code}

Added 17 September 2024 by Fredrik Nordvall Forsberg.

\begin{code}

left-preserves-least : (α β : Ordinal 𝓤)
                     → (a₀ : ⟨ α ⟩) → is-least α a₀ → is-least (α +ₒ β) (inl a₀)
left-preserves-least α β a₀ a₀-least (inl x) (inl u) l = a₀-least x u l
left-preserves-least α β a₀ a₀-least (inr x) (inl u) l = ⋆

\end{code}

End of addition.

Added 29 March 2022.

It is not the case in general that β ≼ α +ₒ β. We work with the
equivalent order _⊴_.

\begin{code}

module _ {𝓤 : Universe} where

 open import Ordinals.OrdinalOfTruthValues fe 𝓤 (pe 𝓤)

 open import UF.DiscreteAndSeparated

 ⊴-add-taboo : Ωₒ ⊴ (𝟙ₒ +ₒ Ωₒ) → typal-WEM 𝓤
 ⊴-add-taboo (f , s) = VI
  where
   I : is-least (𝟙ₒ +ₒ Ωₒ) (inl ⋆)
   I = left-preserves-least 𝟙ₒ Ωₒ ⋆ (λ ⋆ ⋆ ())

   II : f ⊥ ＝ inl ⋆
   II = simulations-preserve-least Ωₒ (𝟙ₒ +ₒ Ωₒ) ⊥ (inl ⋆) f s ⊥-is-least I

   III : is-isolated (f ⊥)
   III = transport⁻¹ is-isolated II (inl-is-isolated ⋆ (𝟙-is-discrete ⋆))

   IV : is-isolated ⊥
   IV = lc-maps-reflect-isolatedness
         f
         (simulations-are-lc Ωₒ (𝟙ₒ +ₒ Ωₒ) f s)
         ⊥
         III

   V : ∀ P → is-prop P → ¬ P + ¬¬ P
   V P i = Cases (IV (P , i))
            (λ (e : ⊥ ＝ (P , i))
                  → inl (equal-𝟘-is-empty (ap pr₁ (e ⁻¹))))
            (λ (ν : ⊥ ≠ (P , i))
                  → inr (contrapositive
                          (λ (u : ¬ P)
                                → to-subtype-＝ (λ _ → being-prop-is-prop fe')
                                   (empty-types-are-＝-𝟘 (pe 𝓤) u)⁻¹) ν))

   VI : ∀ P → ¬ P + ¬¬ P
   VI = WEM-gives-typal-WEM fe' V

\end{code}

Added 5th April 2022.

Successor reflects order:

\begin{code}

succₒ-reflects-⊴ : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                 → (α +ₒ 𝟙ₒ) ⊴ (β +ₒ 𝟙ₒ) → α ⊴ β
succₒ-reflects-⊴ α β (f , i , p) = g , j , q
 where
  k : (x : ⟨ α ⟩) (t : ⟨ β ⟩ + 𝟙)
    → f (inl x) ＝ t → Σ y ꞉ ⟨ β ⟩ , f (inl x) ＝ inl y
  k x (inl y) e = y , e
  k x (inr ⋆) e = 𝟘-elim (III (f (inr ⋆)) II)
   where
    I : f (inl x) ≺⟨ β +ₒ 𝟙ₒ ⟩ (f (inr ⋆))
    I = p (inl x) (inr ⋆) ⋆

    II : inr ⋆ ≺⟨ β +ₒ 𝟙ₒ ⟩ (f (inr ⋆))
    II = transport (λ - → - ≺⟨ β +ₒ 𝟙ₒ ⟩ (f (inr ⋆))) e I

    III : (t : ⟨ β ⟩ + 𝟙) → ¬ (inr ⋆  ≺⟨ β +ₒ 𝟙ₒ ⟩ t)
    III (inl y) l = 𝟘-elim l
    III (inr ⋆) l = 𝟘-elim l

  h : (x : ⟨ α ⟩) → Σ y ꞉ ⟨ β ⟩ , f (inl x) ＝ inl y
  h x = k x (f (inl x)) refl

  g : ⟨ α ⟩ → ⟨ β ⟩
  g x = pr₁ (h x)

  ϕ : (x : ⟨ α ⟩) → f (inl x) ＝ inl (g x)
  ϕ x = pr₂ (h x)

  j : is-initial-segment α β g
  j x y l = II I
   where
    m : inl y ≺⟨ β +ₒ 𝟙ₒ ⟩ f (inl x)
    m = transport⁻¹ (λ - → inl y ≺⟨ β +ₒ 𝟙ₒ ⟩ -) (ϕ x) l

    I : Σ z ꞉ ⟨ α +ₒ 𝟙ₒ ⟩ , (z ≺⟨ α +ₒ 𝟙ₒ ⟩ inl x) × (f z ＝ inl y)
    I = i (inl x) (inl y) m

    II : type-of I → Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (g x' ＝ y)
    II (inl x' , n , e) = x' , n , inl-lc (inl (g x') ＝⟨ (ϕ x')⁻¹ ⟩
                                           f (inl x') ＝⟨ e ⟩
                                           inl y      ∎)

  q : is-order-preserving α β g
  q x x' l = transport₂ (λ y y' → y ≺⟨ β +ₒ 𝟙ₒ ⟩ y') (ϕ x) (ϕ x') I
   where
    I : f (inl x) ≺⟨ β +ₒ 𝟙ₒ ⟩ f (inl x')
    I = p (inl x) (inl x') l

succₒ-reflects-≼ : (α β : Ordinal 𝓤) → (α +ₒ 𝟙ₒ) ≼ (β +ₒ 𝟙ₒ) → α ≼ β
succₒ-reflects-≼ α β l = ⊴-gives-≼ α β
                          (succₒ-reflects-⊴ α β
                            (≼-gives-⊴ (α +ₒ 𝟙ₒ) (β +ₒ 𝟙ₒ) l))

succₒ-preserves-≾ : (α β : Ordinal 𝓤) → α ≾ β → (α +ₒ 𝟙ₒ) ≾ (β +ₒ 𝟙ₒ)
succₒ-preserves-≾ α β = contrapositive (succₒ-reflects-≼ β α)

\end{code}

TODO. Actually (α +ₒ 𝟙ₒ) ⊴ (β +ₒ 𝟙ₒ) is equivalent to
α ≃ₒ β or β ≃ₒ α +ₒ 𝟙ₒ + γ for some (necessarily unique) γ.
This condition in turn implies α ⊴ β (and is equivalent to α ⊴ β under
excluded middle).

However, the successor function does not preserve _⊴_ in general:

\begin{code}

succ-not-necessarily-monotone : ((α β : Ordinal 𝓤)
                                      → α ⊴ β
                                      → (α +ₒ 𝟙ₒ) ⊴ (β +ₒ 𝟙ₒ))
                              → typal-WEM 𝓤
succ-not-necessarily-monotone {𝓤} ϕ = XII
 where
  module _ (P : 𝓤 ̇ ) (isp : is-prop P) where
   α : Ordinal 𝓤
   α = prop-ordinal P isp

   I :  (α +ₒ 𝟙ₒ) ⊴ 𝟚ₒ
   I = ϕ α 𝟙ₒ l
    where
     l : α ⊴ 𝟙ₒ
     l = unique-to-𝟙 ,
         (λ x y (l : y ≺⟨ 𝟙ₒ ⟩ ⋆) → 𝟘-elim l) ,
         (λ x y l → l)

   II : type-of I → ¬ P + ¬¬ P
   II (f , f-is-initial , f-is-order-preserving) = III (f (inr ⋆)) refl
    where
     III : (y : ⟨ 𝟚ₒ ⟩) → f (inr ⋆) ＝ y → ¬ P + ¬¬ P
     III (inl ⋆) e = inl VII
      where
       IV : (p : P) → f (inl p) ≺⟨ 𝟚ₒ ⟩ f (inr ⋆)
       IV p = f-is-order-preserving (inl p) (inr ⋆) ⋆

       V : (p : P) → f (inl p) ≺⟨ 𝟚ₒ ⟩ inl ⋆
       V p = transport (λ - → f (inl p) ≺⟨ 𝟚ₒ ⟩ -) e (IV p)

       VI : (z : ⟨ 𝟚ₒ ⟩) → ¬ (z ≺⟨ 𝟚ₒ ⟩ inl ⋆)
       VI (inl ⋆) l = 𝟘-elim l
       VI (inr ⋆) l = 𝟘-elim l

       VII : ¬ P
       VII p = VI (f (inl p)) (V p)
     III (inr ⋆) e = inr IX
      where
       VIII : Σ x' ꞉ ⟨ α +ₒ 𝟙ₒ ⟩ , (x' ≺⟨ α +ₒ 𝟙ₒ ⟩ inr ⋆) × (f x' ＝ inl ⋆)
       VIII = f-is-initial
               (inr ⋆)
               (inl ⋆)
               (transport⁻¹ (λ - → inl ⋆ ≺⟨ 𝟚ₒ ⟩ -) e ⋆)

       IX : ¬¬ P
       IX u = XI
        where
         X : ∀ x' → ¬ (x' ≺⟨ α +ₒ 𝟙ₒ ⟩ inr ⋆)
         X (inl p) l = u p
         X (inr ⋆) l = 𝟘-elim l

         XI : 𝟘
         XI = X (pr₁ VIII) (pr₁ (pr₂ VIII))

  XII : typal-WEM 𝓤
  XII = WEM-gives-typal-WEM fe' (λ P isp → II P isp (I P isp))

\end{code}

TODO. Also the implication α ⊲ β → (α +ₒ 𝟙ₒ) ⊲ (β +ₒ 𝟙ₒ) fails in general.

\begin{code}

succ-monotone : EM (𝓤 ⁺) → (α β : Ordinal 𝓤) → α ⊴ β → (α +ₒ 𝟙ₒ) ⊴ (β +ₒ 𝟙ₒ)
succ-monotone em α β l = II I
 where
  I : ((α +ₒ 𝟙ₒ) ⊲ (β +ₒ 𝟙ₒ)) + ((α +ₒ 𝟙ₒ) ＝ (β +ₒ 𝟙ₒ)) + ((β +ₒ 𝟙ₒ) ⊲ (α +ₒ 𝟙ₒ))
  I = trichotomy _⊲_ fe' em ⊲-is-well-order (α +ₒ 𝟙ₒ) (β +ₒ 𝟙ₒ)

  II : type-of I → (α +ₒ 𝟙ₒ) ⊴ (β +ₒ 𝟙ₒ)
  II (inl m)       = ⊲-gives-⊴ _ _ m
  II (inr (inl e)) = transport ((α +ₒ 𝟙ₒ) ⊴_) e  (⊴-refl (α +ₒ 𝟙ₒ))
  II (inr (inr m)) = transport ((α +ₒ 𝟙ₒ) ⊴_) VI (⊴-refl (α +ₒ 𝟙ₒ))
   where
    III : (β +ₒ 𝟙ₒ) ⊴ (α +ₒ 𝟙ₒ)
    III = ⊲-gives-⊴ _ _ m

    IV : β ⊴ α
    IV = succₒ-reflects-⊴ β α III

    V : α ＝ β
    V = ⊴-antisym _ _ l IV

    VI : (α +ₒ 𝟙ₒ) ＝ (β +ₒ 𝟙ₒ)
    VI = ap (_+ₒ 𝟙ₒ) V

\end{code}

TODO. EM 𝓤 is sufficient, because we can work with the resized order _⊲⁻_.

Added 13 November 2023 by Fredrik Nordvall Forsberg.

Addition satisfies the expected recursive equations (which classically define
addition): zero is the neutral element (this is 𝟘₀-right-neutral above), addition
commutes with successors and addition preserves inhabited suprema.

Note that (the index of) the supremum indeed has to be inhabited, because
preserving the empty supremum would give the false equation
  α +ₒ 𝟘 ＝ 𝟘
for any ordinal α.

\begin{code}

+ₒ-commutes-with-successor : (α β : Ordinal 𝓤) → α +ₒ (β +ₒ 𝟙ₒ) ＝ (α +ₒ β) +ₒ 𝟙ₒ
+ₒ-commutes-with-successor α β = (+ₒ-assoc α β 𝟙ₒ) ⁻¹

open import UF.PropTrunc
open import UF.Size

module _ (pt : propositional-truncations-exist)
         (sr : Set-Replacement pt)
       where

 open import Ordinals.OrdinalOfOrdinalsSuprema ua
 open suprema pt sr
 open PropositionalTruncation pt

 +ₒ-preserves-inhabited-suprema : (α : Ordinal 𝓤) {I : 𝓤 ̇ } (β : I → Ordinal 𝓤)
                                → ∥ I ∥
                                → α +ₒ sup β ＝ sup (λ i → α +ₒ β i)
 +ₒ-preserves-inhabited-suprema α {I} β =
  ∥∥-rec (the-type-of-ordinals-is-a-set (ua _) fe')
         (λ i₀ → ⊴-antisym _ _ (≼-gives-⊴ _ _ (⦅1⦆ i₀)) ⦅2⦆)
   where
    ⦅2⦆ : sup (λ i → α +ₒ β i) ⊴ (α +ₒ sup β)
    ⦅2⦆ = sup-is-lower-bound-of-upper-bounds (λ i → α +ₒ β i) (α +ₒ sup β) ⦅2⦆'
     where
      ⦅2⦆' : (i : I) → (α +ₒ β i) ⊴ (α +ₒ sup β)
      ⦅2⦆' i = +ₒ-right-monotone-⊴ α (β i) (sup β) (sup-is-upper-bound β i)

    ⦅1⦆ : I → (α +ₒ sup β) ≼ sup (λ i → α +ₒ β i)
    ⦅1⦆ i₀ _ (inl a , refl) =
     transport (_⊲ sup (λ i → α +ₒ β i))
               (+ₒ-↓-left a)
               (⊲-⊴-gives-⊲ (α ↓ a) (α +ₒ β i₀) (sup (λ i → α +ₒ β i))
                (inl a , +ₒ-↓-left a)
                (sup-is-upper-bound (λ i → α +ₒ β i) i₀))
    ⦅1⦆ i₀ _ (inr s , refl) =
     transport (_⊲ sup (λ i → α +ₒ β i))
               (+ₒ-↓-right s)
               (∥∥-rec (⊲-is-prop-valued _ _) ⦅1⦆'
                (initial-segment-of-sup-is-initial-segment-of-some-component
                  β s))
      where
       ⦅1⦆' : Σ i ꞉ I , Σ b ꞉ ⟨ β i ⟩ , sup β ↓ s ＝ β i ↓ b
            → (α +ₒ (sup β ↓ s)) ⊲ sup (λ i → α +ₒ β i)
       ⦅1⦆' (i , b , p) =
        transport⁻¹ (λ - → (α +ₒ -) ⊲ sup (λ j → α +ₒ β j)) p
         (⊲-⊴-gives-⊲ (α +ₒ (β i ↓ b)) (α +ₒ β i) (sup (λ j → α +ₒ β j))
          (inr b , +ₒ-↓-right b)
          (sup-is-upper-bound (λ j → α +ₒ β j) i))

\end{code}

Constructively, these equations do not fully characterize ordinal addition, at
least not as far as we know. If addition preserved *all* suprema, then,
expressing the ordinal β as a supremum via the result given below, we would have
the recursive equation
  α +ₒ β ＝ α +ₒ sup (λ b → (B ↓ b) +ₒ 𝟙ₒ)
         ＝ sup (λ b → α +ₒ ((B ↓ b) +ₒ 𝟙ₒ))
         ＝ sup (λ b → (α +ₒ (B ↓ b)) +ₒ 𝟙ₒ)
which would ensure that there is a unique operation satisfying the above
equations for successors and suprema. The problem is that constructively we
cannot, in general, make a case distinction on whether β is zero or not.

In contrast, multiplication behaves differently and is uniquely characterized by
similar equations since it does preserve all suprema, see
MultiplicationProperties.

Added 14 February 2025 by Tom de Jong.

However, we could reformulate the equations for addition to the classically
equivalent set of equations:

  α +ₒ (β +ₒ 𝟙ₒ) ＝ (α +ₒ βₒ) +ₒ 𝟙ₒ
  α +ₒ (sup β)   ＝ α ∨ sup (λ i → α +ₒ β i)

for all families β : I → Ord without any inhabitedness condition on the index
type I.

Note that the equation α +ₒ 𝟘ₒ = α follows by taking the empty family in the
supremum equation.

These reformulated equations have the benefit that they uniquely characterize
addition via the recursive equation
  α +ₒ β ＝ α +ₒ sup (λ b → (B ↓ b) +ₒ 𝟙ₒ)
         ＝ α ∨ sup (λ b → α +ₒ ((B ↓ b) +ₒ 𝟙ₒ))
         ＝ α ∨ sup (λ b → (α +ₒ (B ↓ b)) +ₒ 𝟙ₒ)
which also gives a construction of addition via transfinite recursion.

I first realized this in the context of ordinal exponentiation, cf.
Ordinals.Exponentiation.Specification.


Added 24th May 2024 by Tom de Jong.
Every ordinal is the supremum of the successors of its initial segments.

\begin{code}

 supremum-of-successors-of-initial-segments :
  (α : Ordinal 𝓤) → α ＝ sup (λ x → (α ↓ x) +ₒ 𝟙ₒ)
 supremum-of-successors-of-initial-segments {𝓤} α =
  Antisymmetry (OO 𝓤) α s (to-≼ I) (⊴-gives-≼ s α II)
   where
    s : Ordinal 𝓤
    s = sup (λ x → (α ↓ x) +ₒ 𝟙ₒ)
    F : ⟨ α ⟩ → Ordinal 𝓤
    F x = (α ↓ x) +ₒ 𝟙ₒ

    I : (a : ⟨ α ⟩) → (α ↓ a) ⊲ s
    I a = f (inr ⋆) , ((α ↓ a)         ＝⟨ e₁ ⟩
                       (F a ↓ inr ⋆)   ＝⟨ e₂ ⟩
                       (s ↓ f (inr ⋆)) ∎)
     where
      f : (y : ⟨ F a ⟩) → ⟨ s ⟩
      f = [ F a , s ]⟨ sup-is-upper-bound F a ⟩
      e₁ = (successor-lemma-right (α ↓ a)) ⁻¹
      e₂ = (initial-segment-of-sup-at-component F a (inr ⋆)) ⁻¹

    II : s ⊴ α
    II = sup-is-lower-bound-of-upper-bounds F α
          (upper-bound-of-successors-of-initial-segments α)

\end{code}

Added 14 July 2024.

We prove that α +ₒ (sup β) ＝ α ∨ sup (λ i → α +ₒ β i), but we formulate the RHS
as a single supremum by indexing over 𝟙 + I instead, sending inl ⋆ to α.

\begin{code}

 +ₒ-preserves-suprema-up-to-join
  : (α : Ordinal 𝓤) (I : 𝓤 ̇ ) (β : I → Ordinal 𝓤)
  → α +ₒ sup β ＝ sup (cases (λ ⋆ → α) (λ i → α +ₒ β i))
 +ₒ-preserves-suprema-up-to-join {𝓤} α I β =
  ⊴-antisym (α +ₒ sup β) (sup F) ⦅1⦆ ⦅2⦆
   where
    F : 𝟙 {𝓤} + I → Ordinal 𝓤
    F = cases (λ _ → α) (λ i → α +ₒ β i)

    ⦅1⦆ : α +ₒ sup β ⊴ sup F
    ⦅1⦆ = to-⊴ (α +ₒ sup β) (sup F) h
     where
      h : (z : ⟨ α +ₒ sup β ⟩)
        → (α +ₒ sup β) ↓ z ⊲ sup F
      h (inl a) = (s , (α +ₒ sup β ↓ inl a ＝⟨ (+ₒ-↓-left a) ⁻¹ ⟩
                        α ↓ a              ＝⟨ e ⟩
                        sup F ↓ s          ∎))
       where
        s : ⟨ sup F ⟩
        s = [ α , sup F ]⟨ sup-is-upper-bound F (inl ⋆) ⟩ a
        e = (initial-segment-of-sup-at-component F (inl ⋆) a) ⁻¹
      h (inr y) =
       ∥∥-rec
        (⊲-is-prop-valued (α +ₒ sup β ↓ inr y) (sup F))
        g
        (initial-segment-of-sup-is-initial-segment-of-some-component β y)
       where
        g : (Σ i ꞉ I , Σ x ꞉ ⟨ β i ⟩ , sup β ↓ y ＝ β i ↓ x)
          → α +ₒ sup β ↓ inr y ⊲ sup F
        g (i , x , e) = s , ((α +ₒ sup β) ↓ inr y ＝⟨ (+ₒ-↓-right y) ⁻¹ ⟩
                             α +ₒ (sup β ↓ y)     ＝⟨ ap (α +ₒ_) e ⟩
                             α +ₒ (β i ↓ x)       ＝⟨ +ₒ-↓-right x ⟩
                             (α +ₒ β i) ↓ inr x   ＝⟨ e' ⟩
                             sup F ↓ s            ∎)
         where
          s : ⟨ sup F ⟩
          s = [ F (inr i) , sup F ]⟨ sup-is-upper-bound F (inr i) ⟩ (inr x)
          e' = (initial-segment-of-sup-at-component F (inr i) (inr x)) ⁻¹

    ⦅2⦆ : sup F ⊴ α +ₒ sup β
    ⦅2⦆ = sup-is-lower-bound-of-upper-bounds F (α +ₒ sup β) h
     where
      h : (x : 𝟙 + I) → F x ⊴ α +ₒ sup β
      h (inl ⋆) = +ₒ-left-⊴ α (sup β)
      h (inr i) = +ₒ-right-monotone-⊴ α (β i) (sup β) (sup-is-upper-bound β i)

\end{code}

Added 22 July 2025 by Tom de Jong.

The above, together with +ₒ-commutes-with-successor, uniquely determines
addition of ordinals, see also the comment dated 14 February 2025.

\begin{code}

 private
  successor-equation : (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
  successor-equation {𝓤} _⊕_ =
   (α β : Ordinal 𝓤) → α ⊕ (β +ₒ 𝟙ₒ) ＝ (α ⊕ β) +ₒ 𝟙ₒ

  suprema-equation : (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
  suprema-equation {𝓤} _⊕_ =
   (α : Ordinal 𝓤) (I : 𝓤 ̇ ) (β : I → Ordinal 𝓤)
    → α ⊕ (sup β) ＝ sup (cases (λ (_ : 𝟙{𝓤}) → α) (λ i → α ⊕ β i))

  recursive-equation : (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
  recursive-equation {𝓤} _⊕_ =
   (α β : Ordinal 𝓤)
     → α ⊕ β ＝ sup (cases (λ (_ : 𝟙{𝓤}) → α) (λ b → (α ⊕ (β ↓ b)) +ₒ 𝟙ₒ))

  successor-and-suprema-equations-give-recursive-equation
   : (_⊕_ : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤)
   → successor-equation _⊕_
   → suprema-equation _⊕_
   → recursive-equation _⊕_
  successor-and-suprema-equations-give-recursive-equation
   {𝓤} _⊕_ ⊕-succ ⊕-sup α β =
    α ⊕ β                                             ＝⟨ I   ⟩
    (α ⊕ sup (λ b → (β ↓ b) +ₒ 𝟙ₒ))                   ＝⟨ II  ⟩
    sup (cases (λ ⋆ → α) (λ b → α ⊕ ((β ↓ b) +ₒ 𝟙ₒ))) ＝⟨ III ⟩
    sup (cases (λ ⋆ → α) (λ b → (α ⊕ (β ↓ b)) +ₒ 𝟙ₒ)) ∎
     where
      I   = ap (α ⊕_) (supremum-of-successors-of-initial-segments β)
      II  = ⊕-sup α ⟨ β ⟩ (λ b → (β ↓ b) +ₒ 𝟙ₒ)
      III = ap (λ - → sup (cases (λ (_ : 𝟙{𝓤}) → α) -))
               (dfunext fe' (λ b → ⊕-succ α (β ↓ b)))

 +ₒ-recursive-equation : recursive-equation {𝓤} _+ₒ_
 +ₒ-recursive-equation =
  successor-and-suprema-equations-give-recursive-equation
    _+ₒ_ +ₒ-commutes-with-successor +ₒ-preserves-suprema-up-to-join

 +ₒ-is-uniquely-specified'
  : (_⊕_ : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤)
  → recursive-equation _⊕_
  → (α β : Ordinal 𝓤) → α ⊕ β ＝ α +ₒ β
 +ₒ-is-uniquely-specified' {𝓤} _⊕_ ⊕-rec α =
  transfinite-induction-on-OO (λ - → (α ⊕ -) ＝ (α +ₒ -)) I
   where
    I : (β : Ordinal 𝓤)
      → ((b : ⟨ β ⟩) → (α ⊕ (β ↓ b)) ＝ (α +ₒ (β ↓ b)))
      → (α ⊕ β) ＝ (α +ₒ β)
    I β IH = α ⊕ β                                              ＝⟨ II  ⟩
             sup (cases (λ ⋆ → α) (λ b → (α ⊕ (β ↓ b)) +ₒ 𝟙ₒ))  ＝⟨ III ⟩
             sup (cases (λ ⋆ → α) (λ b → (α +ₒ (β ↓ b)) +ₒ 𝟙ₒ)) ＝⟨ IV  ⟩
             α +ₒ β                                             ∎
     where
      II  = ⊕-rec α β
      III = ap (λ - → sup (cases (λ (_ : 𝟙{𝓤}) → α) -))
               (dfunext fe' (λ b → ap (_+ₒ 𝟙ₒ) (IH b)))
      IV  = +ₒ-recursive-equation α β ⁻¹

 +ₒ-is-uniquely-specified
  : ∃! _⊕_ ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) ,
     (successor-equation _⊕_) × (suprema-equation _⊕_)
 +ₒ-is-uniquely-specified {𝓤} =
  (_+ₒ_ , (+ₒ-commutes-with-successor , +ₒ-preserves-suprema-up-to-join)) ,
  (λ (_⊕_ , ⊕-succ , ⊕-sup) →
   to-subtype-＝
    (λ F → ×-is-prop (Π₂-is-prop fe'
                       (λ _ _ → underlying-type-is-set fe (OO 𝓤)))
                     (Π₃-is-prop fe'
                       (λ _ _ _ → underlying-type-is-set fe (OO 𝓤))))
    (dfunext fe'
      (λ α → dfunext fe'
       (λ β →
        (+ₒ-is-uniquely-specified' _⊕_
          (successor-and-suprema-equations-give-recursive-equation
            _⊕_ ⊕-succ ⊕-sup)
        α β) ⁻¹))))

\end{code}

Added 2 June 2024 by Tom de Jong.

\begin{code}

no-greatest-ordinal : ¬ (Σ α ꞉ Ordinal 𝓤 , ((β : Ordinal 𝓤) → β ⊴ α))
no-greatest-ordinal {𝓤} (α , α-greatest) = irrefl (OO 𝓤) α IV
 where
  I : (α +ₒ 𝟙ₒ) ⊴ α
  I = α-greatest (α +ₒ 𝟙ₒ)
  II : α ⊴ (α +ₒ 𝟙ₒ)
  II = ⊲-gives-⊴ α (α +ₒ 𝟙ₒ) (successor-increasing α)
  III : α +ₒ 𝟙ₒ ＝ α
  III = ⊴-antisym (α +ₒ 𝟙ₒ) α I II
  IV : α ⊲ α
  IV = transport (α ⊲_) III (successor-increasing α)

\end{code}

Added 15 July 2025 by Tom de Jong after discussions with Nicolai Kraus, Fredrik
Nordvall Forsberg and Chuangjie Xu a year earlier.

\begin{code}

+ₒ-as-large-as-right-summand-implies-EM : ((α β : Ordinal 𝓤) → β ⊴ α +ₒ β)
                                        → EM 𝓤
+ₒ-as-large-as-right-summand-implies-EM hyp P P-is-prop = IV
 where
  α = prop-ordinal P P-is-prop
  β = 𝟙ₒ
  𝕗 : β ⊴ α +ₒ β
  𝕗 = hyp α β
  f = [ β , α +ₒ β ]⟨ 𝕗 ⟩
  I : (p : P) → f ⋆ ＝ inl p → P
  I p _ = p
  II : (p : P) → f ⋆ ＝ inl p
  II p = simulations-preserve-least β (α +ₒ β) ⋆ (inl p) f
                                    [ β , α +ₒ β ]⟨ 𝕗 ⟩-is-simulation
                                    𝟙ₒ-least
                                    l
   where
    l : is-least (α +ₒ β) (inl p)
    l = minimal-is-least (α +ₒ β) (inl p) m
     where
      m : is-minimal (α +ₒ β) (inl p)
      m (inl p') = 𝟘-elim
      m (inr ⋆ ) = 𝟘-elim
  III : f ⋆ ＝ inr ⋆ → ¬ P
  III e p = +disjoint ((II p) ⁻¹ ∙ e)
  IV : P + ¬ P
  IV = equality-cases (f ⋆) (λ p → inl ∘ I p) (λ _ → inr ∘ III)

EM-implies-+ₒ-as-large-as-right-summand : EM 𝓤
                                        → ((α β : Ordinal 𝓤) → β ⊴ α +ₒ β)
EM-implies-+ₒ-as-large-as-right-summand em α β =
 ≼-gives-⊴ β (α +ₒ β)
           (EM-implies-order-preserving-gives-≼ em β (α +ₒ β) (f , I))
  where
   f : ⟨ β ⟩ → ⟨ α +ₒ β ⟩
   f = inr
   I : is-order-preserving β (α +ₒ β) f
   I y y' l = l

\end{code}

Added 15 July 2025 by Tom de Jong.

\begin{code}

+ₒ-minimal : (α β : Ordinal 𝓤) (a₀ : ⟨ α ⟩)
           → is-minimal α a₀ → is-minimal (α +ₒ β) (inl a₀)
+ₒ-minimal α β a₀ a₀-minimal (inl a) = a₀-minimal a
+ₒ-minimal α β a₀ a₀-minimal (inr b) = 𝟘-elim

+ₒ-least : (α β : Ordinal 𝓤) (a₀ : ⟨ α ⟩)
         → is-least α a₀ → is-least (α +ₒ β) (inl a₀)
+ₒ-least α β  a₀ a₀-least =
 minimal-is-least (α +ₒ β) (inl a₀)
                  (+ₒ-minimal α β a₀ (least-is-minimal α a₀ a₀-least))

\end{code}

Added 26 September 2025 by Fredrik Nordvall Forsberg.

\begin{code}

𝟚ₒ-is-not-𝟙ₒ : 𝟚ₒ {𝓤} ≠ 𝟙ₒ {𝓤}
𝟚ₒ-is-not-𝟙ₒ p = 𝟘ₒ-is-not-𝟙ₒ (+ₒ-left-cancellable 𝟙ₒ 𝟙ₒ 𝟘ₒ p' ⁻¹)
 where
  p' : 𝟚ₒ ＝ 𝟙ₒ +ₒ 𝟘ₒ
  p' = p ∙ 𝟘ₒ-right-neutral 𝟙ₒ ⁻¹

\end{code}

Added in September 2025 by Fredrik Nordvall Forsberg.
Moved here from ArithmeticReflection by Tom de Jong in October 2025.

Some special cases of addition by ω.

\begin{code}

𝟘ₒ+ₒω-is-ω : 𝟘ₒ +ₒ ω ＝ ω
𝟘ₒ+ₒω-is-ω = 𝟘ₒ-left-neutral ω

𝟙ₒ+ₒω-is-ω : 𝟙ₒ +ₒ ω ＝ ω
𝟙ₒ+ₒω-is-ω = eqtoidₒ (ua _) fe' (𝟙ₒ +ₒ ω) ω h
 where
  f : 𝟙 + ℕ → ℕ
  f (inl ⋆) = 0
  f (inr n) = succ n

  g : ℕ → 𝟙 + ℕ
  g 0 = inl ⋆
  g (succ n) = inr n

  f-equiv : is-equiv f
  f-equiv = qinvs-are-equivs f (g , (η , ϵ))
   where
    η : (λ x → g (f x)) ∼ id
    η (inl ⋆) = refl
    η (inr n) = refl

    ϵ : (λ x → f (g x)) ∼ id
    ϵ zero = refl
    ϵ (succ x) = refl

  f-preserves-order : (x y : 𝟙 + ℕ) → x ≺⟨ 𝟙ₒ +ₒ ω ⟩ y → f x ≺⟨ ω ⟩ f y
  f-preserves-order (inl ⋆) (inr n) p = ⋆
  f-preserves-order (inr n) (inr m) p = p

  f-reflects-order : (x y : 𝟙 + ℕ) → f x ≺⟨ ω ⟩ f y → x ≺⟨ 𝟙ₒ +ₒ ω ⟩ y
  f-reflects-order (inl ⋆) (inr n) _ = ⋆
  f-reflects-order (inr n) (inr m) p = p

  h : (𝟙ₒ +ₒ ω) ≃ₒ ω
  h = f , order-preserving-reflecting-equivs-are-order-equivs (𝟙ₒ +ₒ ω) ω f
           f-equiv f-preserves-order f-reflects-order

\end{code}
