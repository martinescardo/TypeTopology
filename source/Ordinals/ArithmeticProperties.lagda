Martin Escardo, 18 January 2021.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.ArithmeticProperties
       (ua : Univalence)
       where

open import UF.Base
open import UF.Embeddings hiding (⌊_⌋)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
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
open import Ordinals.ConvergentSequence ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
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

\end{code}

Added 7 November 2022 by Tom de Jong.

A rather special case of the above is that adding 𝟙 and then taking the initial
segment capped at inr ⋆ is the same thing as the original ordinal.

It is indeed a special case of the above because (𝟙 ↓ ⋆) ＝ 𝟘ₒ and 𝟘ₒ is right
neutral, but we give a direct proof instead.

\begin{code}

+ₒ-𝟙ₒ-↓-right : (α : Ordinal 𝓤) → (α +ₒ 𝟙ₒ) ↓ inr ⋆ ＝ α
+ₒ-𝟙ₒ-↓-right α = eqtoidₒ (ua _) fe' ((α +ₒ 𝟙ₒ) ↓ inr ⋆) α h
 where
  f : ⟨ (α +ₒ 𝟙ₒ) ↓ inr ⋆ ⟩ → ⟨ α ⟩
  f (inl x , l) = x

  g : ⟨ α ⟩ → ⟨ (α +ₒ 𝟙ₒ) ↓ inr ⋆ ⟩
  g x = (inl x , ⋆)

  f-order-preserving : is-order-preserving ((α +ₒ 𝟙ₒ) ↓ inr ⋆) α f
  f-order-preserving (inl x , _) (inl y , _) l = l

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f (g , η , ε)
   where
    η : g ∘ f ∼ id
    η (inl _ , _) = refl

    ε : f ∘ g ∼ id
    ε _ = refl

  g-order-preserving : is-order-preserving α ((α +ₒ 𝟙ₒ) ↓ inr ⋆) g
  g-order-preserving x y l = l

  h : ((α +ₒ 𝟙ₒ) ↓ inr ⋆) ≃ₒ α
  h = f , f-order-preserving , f-is-equiv , g-order-preserving

\end{code}

End of addition.

\begin{code}

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

\end{code}

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

Added 29 March 2022.

It is not the case in general that β ≼ α +ₒ β. We work with the
equivalent order _⊴_.

\begin{code}

module _ {𝓤 : Universe} where

 open import Ordinals.OrdinalOfTruthValues fe 𝓤 (pe 𝓤)

 open import UF.DiscreteAndSeparated

 ⊴-add-taboo : Ωₒ ⊴ (𝟙ₒ +ₒ Ωₒ) → WEM 𝓤
 ⊴-add-taboo (f , s) = V
  where
   I : is-least (𝟙ₒ +ₒ Ωₒ) (inl ⋆)
   I (inl ⋆) u       l = l
   I (inr x) (inl ⋆) l = 𝟘-elim l
   I (inr x) (inr y) l = 𝟘-elim l

   II : f ⊥ ＝ inl ⋆
   II = simulations-preserve-least Ωₒ (𝟙ₒ +ₒ Ωₒ) ⊥ (inl ⋆) f s ⊥-is-least I

   III : is-isolated (f ⊥)
   III = transport⁻¹ is-isolated II (inl-is-isolated ⋆ (𝟙-is-discrete ⋆))

   IV : is-isolated ⊥
   IV = lc-maps-reflect-isolatedness f (simulations-are-lc Ωₒ (𝟙ₒ +ₒ Ωₒ) f s) ⊥ III

   V : ∀ P → is-prop P → ¬ P + ¬¬ P
   V P i = Cases (IV (P , i))
            (λ (e : ⊥ ＝ (P , i))
                  → inl (equal-𝟘-is-empty (ap pr₁ (e ⁻¹))))
            (λ (ν : ⊥ ≠ (P , i))
                  → inr (contrapositive
                          (λ (u : ¬ P)
                                → to-subtype-＝ (λ _ → being-prop-is-prop fe')
                                   (empty-types-are-＝-𝟘 fe' (pe 𝓤) u)⁻¹) ν))
\end{code}

Added 4th April 2022.

\begin{code}

𝟘ₒ-least-⊴ : (α : Ordinal 𝓤) → 𝟘ₒ {𝓤} ⊴ α
𝟘ₒ-least-⊴ α = unique-from-𝟘 , (λ x y l → 𝟘-elim x) , (λ x y l → 𝟘-elim x)

𝟘ₒ-least : (α : Ordinal 𝓤) → 𝟘ₒ {𝓤} ≼ α
𝟘ₒ-least α = ⊴-gives-≼ 𝟘ₒ α (𝟘ₒ-least-⊴ α)

\end{code}

Added 5th April 2022.

Successor reflects order:

\begin{code}

succₒ-reflects-⊴ : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (α +ₒ 𝟙ₒ) ⊴ (β +ₒ 𝟙ₒ) → α ⊴ β
succₒ-reflects-⊴ α β (f , i , p) = g , j , q
 where
  k : (x : ⟨ α ⟩) (t : ⟨ β ⟩ + 𝟙) → f (inl x) ＝ t → Σ y ꞉ ⟨ β ⟩ , f (inl x) ＝ inl y
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
                              → WEM 𝓤
succ-not-necessarily-monotone {𝓤} ϕ P isp = II I
 where
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
      VIII = f-is-initial (inr ⋆) (inl ⋆) (transport⁻¹ (λ - → inl ⋆ ≺⟨ 𝟚ₒ ⟩ -) e ⋆)

      IX : ¬¬ P
      IX u = XI
       where
        X : ∀ x' → ¬ (x' ≺⟨ α +ₒ 𝟙ₒ ⟩ inr ⋆)
        X (inl p) l = u p
        X (inr ⋆) l = 𝟘-elim l

        XI : 𝟘
        XI = X (pr₁ VIII) (pr₁ (pr₂ VIII))

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

Added 21st April 2022.

We say that an ordinal is a limit ordinal if it is the least upper
bound of its predecessors:

\begin{code}

is-limit-ordinal⁺ : Ordinal 𝓤 → 𝓤 ⁺ ̇
is-limit-ordinal⁺ {𝓤} α = (β : Ordinal 𝓤)
                         → ((γ : Ordinal 𝓤) → γ ⊲ α → γ ⊴ β)
                         → α ⊴ β
\end{code}

We give an equivalent definition below.

Recall from another module [say which one] that the existence
propositional truncations and the set-replacement property are
together equivalent to the existence of small quotients. With them we
can construct suprema of families of ordinals.

\begin{code}

open import UF.PropTrunc
open import UF.Size

module _ (pt : propositional-truncations-exist)
         (sr : Set-Replacement pt)
       where

 open import Ordinals.OrdinalOfOrdinalsSuprema ua
 open suprema pt sr

\end{code}

Recall that, by definition, γ ⊲ α iff γ is of the form α ↓ x for some
x : ⟨ α ⟩. We define the "floor" of an ordinal to be the supremum of
its predecessors:

\begin{code}

 ⌊_⌋ : Ordinal 𝓤 → Ordinal 𝓤
 ⌊ α ⌋ = sup (α ↓_)

 ⌊⌋-lower-bound : (α : Ordinal 𝓤) → ⌊ α ⌋ ⊴ α
 ⌊⌋-lower-bound α = sup-is-lower-bound-of-upper-bounds _ α (segment-⊴ α)

 is-limit-ordinal : Ordinal 𝓤 → 𝓤 ̇
 is-limit-ordinal α = α ⊴ ⌊ α ⌋

 is-limit-ordinal-fact : (α : Ordinal 𝓤)
                       → is-limit-ordinal α
                       ↔ α ＝ ⌊ α ⌋
 is-limit-ordinal-fact α = (λ ℓ → ⊴-antisym _ _ ℓ (⌊⌋-lower-bound α)) ,
                           (λ p → transport (α ⊴_) p (⊴-refl α))

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
         α +ₒ (𝟙ₒ ↓ ⋆) ＝⟨ ap (α +ₒ_) II ⟩
         α +ₒ 𝟘ₒ       ＝⟨ 𝟘ₒ-right-neutral α ⟩
         α             ∎

 ⌊⌋-of-successor : (α : Ordinal 𝓤)
                 → ⌊ α +ₒ 𝟙ₒ ⌋ ⊴ α
 ⌊⌋-of-successor α = sup-is-lower-bound-of-upper-bounds _ α h
  where
   h : (x : ⟨ α +ₒ 𝟙ₒ ⟩) → ((α +ₒ 𝟙ₒ) ↓ x) ⊴ α
   h (inl x) = successor-lemma-left α x
   h (inr ⋆) = transport⁻¹ (_⊴ α) (successor-lemma-right α) (⊴-refl α)

 ⌊⌋-of-successor' : (α : Ordinal 𝓤)
                  → ⌊ α +ₒ 𝟙ₒ ⌋ ＝ α
 ⌊⌋-of-successor' α = III
  where
   I : ((α +ₒ 𝟙ₒ) ↓ inr ⋆) ⊴ ⌊ α +ₒ 𝟙ₒ ⌋
   I = sup-is-upper-bound _ (inr ⋆)

   II : α ⊴ ⌊ α +ₒ 𝟙ₒ ⌋
   II = transport (_⊴ ⌊ α +ₒ 𝟙ₒ ⌋) (successor-lemma-right α) I

   III : ⌊ α +ₒ 𝟙ₒ ⌋ ＝ α
   III = ⊴-antisym _ _ (⌊⌋-of-successor α) II

 successor-increasing : (α : Ordinal 𝓤) → α ⊲ (α +ₒ 𝟙ₒ)
 successor-increasing α = inr ⋆ , ((successor-lemma-right α)⁻¹)

 successors-are-not-limit-ordinals : (α : Ordinal 𝓤)
                                   → ¬ is-limit-ordinal (α +ₒ 𝟙ₒ)
 successors-are-not-limit-ordinals α le = irrefl (OO _) α II
  where
   I : (α +ₒ 𝟙ₒ) ⊴ α
   I = ⊴-trans (α +ₒ 𝟙ₒ) ⌊ α +ₒ 𝟙ₒ ⌋ α le (⌊⌋-of-successor α)

   II : α ⊲ α
   II = ⊴-gives-≼ _ _ I α (successor-increasing α)

\end{code}

TODO (easy). Show that is-limit-ordinal⁺ α is logically equivalent to
is-limit-ordinal α.

\begin{code}

 ⌊⌋-monotone : (α β : Ordinal 𝓤) → α ⊴ β → ⌊ α ⌋ ⊴ ⌊ β ⌋
 ⌊⌋-monotone α β le = V
  where
   I : (y : ⟨ β ⟩) → (β ↓ y) ⊴ ⌊ β ⌋
   I = sup-is-upper-bound (β ↓_)

   II : (x : ⟨ α ⟩) → (α ↓ x) ⊲ β
   II x = ⊴-gives-≼ _ _ le (α ↓ x) (x , refl)

   III : (x : ⟨ α ⟩) → Σ y ꞉ ⟨ β ⟩ , (α ↓ x) ＝ (β ↓ y)
   III = II

   IV : (x : ⟨ α ⟩) → (α ↓ x) ⊴ ⌊ β ⌋
   IV x = transport⁻¹ (_⊴ ⌊ β ⌋) (pr₂ (III x)) (I (pr₁ (III x)))

   V : sup (α ↓_) ⊴ ⌊ β ⌋
   V = sup-is-lower-bound-of-upper-bounds (α ↓_) ⌊ β ⌋ IV

\end{code}

We now give an example of an ordinal which is not a limit ordinal and
also is not a successor ordinal unless LPO holds:

\begin{code}

 open import Notation.CanonicalMap
 open import CoNaturals.GenericConvergentSequence
 open import Notation.Order
 open import Naturals.Order

 ⌊⌋-of-ℕ∞ : ⌊ ℕ∞ₒ ⌋ ＝ ω
 ⌊⌋-of-ℕ∞ = c
  where
   a : ⌊ ℕ∞ₒ ⌋ ⊴ ω
   a = sup-is-lower-bound-of-upper-bounds (ℕ∞ₒ ↓_) ω I
    where
     I : (u : ⟨ ℕ∞ₒ ⟩) → (ℕ∞ₒ ↓ u) ⊴ ω
     I u = ≼-gives-⊴ (ℕ∞ₒ ↓ u) ω II
      where
       II : (α : Ordinal 𝓤₀) → α ⊲ (ℕ∞ₒ ↓ u) → α ⊲ ω
       II .((ℕ∞ₒ ↓ u) ↓ (ι n , n , refl , p)) ((.(ι n) , n , refl , p) , refl) = XI
        where
         III : ι n ≺ u
         III = n , refl , p

         IV : ((ℕ∞ₒ ↓ u) ↓ (ι n , n , refl , p)) ＝ ℕ∞ₒ ↓ ι n
         IV = iterated-↓ ℕ∞ₒ u (ι n) III

         V : (ℕ∞ₒ ↓ ι n) ≃ₒ (ω ↓ n)
         V = f , fop , qinvs-are-equivs f (g , gf , fg) , gop
          where
           f : ⟨ ℕ∞ₒ ↓ ι n ⟩ → ⟨ ω ↓ n ⟩
           f (.(ι k) , k , refl , q) = k , ⊏-gives-< _ _ q

           g : ⟨ ω ↓ n ⟩ → ⟨ ℕ∞ₒ ↓ ι n ⟩
           g (k , l) = (ι k , k , refl , <-gives-⊏ _ _ l)

           fg : f ∘ g ∼ id
           fg (k , l) = to-subtype-＝ (λ k → <-is-prop-valued k n) refl

           gf : g ∘ f ∼ id
           gf (.(ι k) , k , refl , q) = to-subtype-＝
                                         (λ u → ≺-prop-valued fe' u (ι n))
                                         refl

           fop : is-order-preserving (ℕ∞ₒ ↓ ι n) (ω ↓ n) f
           fop (.(ι k) , k , refl , q) (.(ι k') , k' , refl , q') (m , r , cc) =
            VIII
            where
             VI : k ＝ m
             VI = ℕ-to-ℕ∞-lc r

             VII : m < k'
             VII = ⊏-gives-< _ _ cc

             VIII : k < k'
             VIII = transport⁻¹ (_< k') VI VII

           gop : is-order-preserving (ω ↓ n) (ℕ∞ₒ ↓ ι n)  g
           gop (k , l) (k' , l') ℓ = k , refl , <-gives-⊏ _ _ ℓ

         IX : ℕ∞ₒ ↓ ι n ＝ ω ↓ n
         IX = eqtoidₒ (ua 𝓤₀) fe' _ _ V

         X : (ℕ∞ₒ ↓ (ι n)) ⊲ ω
         X = n , IX

         XI : ((ℕ∞ₒ ↓ u) ↓ (ι n , n , refl , p)) ⊲ ω
         XI = transport⁻¹ (_⊲ ω) IV X

   b : ω ⊴ ⌊ ℕ∞ₒ ⌋
   b = transport (_⊴ ⌊ ℕ∞ₒ ⌋) (⌊⌋-of-successor' ω) I
    where
     I : ⌊ ω +ₒ 𝟙ₒ ⌋ ⊴ ⌊ ℕ∞ₒ ⌋
     I = ⌊⌋-monotone (ω +ₒ 𝟙ₒ) ℕ∞ₒ ω+𝟙-is-⊴-ℕ∞

   c : ⌊ ℕ∞ₒ ⌋ ＝ ω
   c = ⊴-antisym _ _ a b

 ℕ∞-is-not-limit : ¬ is-limit-ordinal ℕ∞ₒ
 ℕ∞-is-not-limit ℓ = III II
  where
   I = ℕ∞ₒ     ＝⟨ lr-implication (is-limit-ordinal-fact ℕ∞ₒ) ℓ ⟩
       ⌊ ℕ∞ₒ ⌋ ＝⟨ ⌊⌋-of-ℕ∞  ⟩
       ω       ∎

   II : ℕ∞ₒ ≃ₒ ω
   II = idtoeqₒ _ _ I

   III : ¬ (ℕ∞ₒ ≃ₒ ω)
   III (f , e) = irrefl ω (f ∞) VII
    where
     IV : is-largest ω (f ∞)
     IV = order-equivs-preserve-largest ℕ∞ₒ ω f e ∞
           (λ u t l → ≺≼-gives-≺ t u ∞ l (∞-largest u))

     V : f ∞ ≺⟨ ω ⟩ succ (f ∞)
     V = <-succ (f ∞)

     VI : succ (f ∞) ≼⟨ ω ⟩ f ∞
     VI = IV (succ (f ∞))

     VII : f ∞ ≺⟨ ω ⟩ f ∞
     VII = VI (f ∞) V

 open import Taboos.LPO fe

 ℕ∞-successor-gives-LPO : (Σ α ꞉ Ordinal 𝓤₀ , (ℕ∞ₒ ＝ (α +ₒ 𝟙ₒ))) → LPO
 ℕ∞-successor-gives-LPO (α , p) = IV
  where
   I = α           ＝⟨ (⌊⌋-of-successor' α)⁻¹ ⟩
       ⌊ α +ₒ 𝟙ₒ ⌋ ＝⟨ ap ⌊_⌋ (p ⁻¹) ⟩
       ⌊ ℕ∞ₒ ⌋     ＝⟨ ⌊⌋-of-ℕ∞ ⟩
       ω           ∎

   II : ℕ∞ₒ ＝ (ω +ₒ 𝟙ₒ)
   II = transport (λ - → ℕ∞ₒ ＝ (- +ₒ 𝟙ₒ)) I p

   III : ℕ∞ₒ ⊴ (ω +ₒ 𝟙ₒ)
   III = transport (ℕ∞ₒ ⊴_) II (⊴-refl ℕ∞ₒ)

   IV : LPO
   IV = ℕ∞-⊴-ω+𝟙-gives-LPO III

 open PropositionalTruncation pt

 ℕ∞-successor-gives-LPO' : (∃ α ꞉ Ordinal 𝓤₀ , (ℕ∞ₒ ＝ (α +ₒ 𝟙ₒ))) → LPO
 ℕ∞-successor-gives-LPO' = ∥∥-rec LPO-is-prop ℕ∞-successor-gives-LPO

 LPO-gives-ℕ∞-successor : LPO → (Σ α ꞉ Ordinal 𝓤₀ , (ℕ∞ₒ ＝ (α +ₒ 𝟙ₒ)))
 LPO-gives-ℕ∞-successor lpo = ω , ℕ∞-is-successor₃ lpo

\end{code}

Therefore, constructively, it is not necessarily the case that every
ordinal is either a successor or a limit.

TODO (1st June 2023). A classically equivalently definition of limit
ordinal α is that there is some β < α, and for evert β < α there is γ
with β < γ < α. We have that ℕ∞ is a limit ordinal in this sense.

Added 4th May 2022.

\begin{code}

open import Ordinals.ToppedType fe
open import Ordinals.ToppedArithmetic fe

alternative-plusₒ : (τ₀ τ₁ : Ordinalᵀ 𝓤)
                  → [ τ₀ +ᵒ τ₁ ] ≃ₒ ([ τ₀ ] +ₒ [ τ₁ ])
alternative-plusₒ τ₀ τ₁ = e
 where
  υ = cases (λ ⋆ → τ₀) (λ ⋆ → τ₁)

  f : ⟨ ∑ 𝟚ᵒ υ ⟩ → ⟨ [ τ₀ ] +ₒ [ τ₁ ] ⟩
  f (inl ⋆ , x) = inl x
  f (inr ⋆ , y) = inr y

  g : ⟨ [ τ₀ ] +ₒ [ τ₁ ] ⟩ → ⟨ ∑ 𝟚ᵒ υ ⟩
  g (inl x) = (inl ⋆ , x)
  g (inr y) = (inr ⋆ , y)

  η : g ∘ f ∼ id
  η (inl ⋆ , x) = refl
  η (inr ⋆ , y) = refl

  ε : f ∘ g ∼ id
  ε (inl x) = refl
  ε (inr y) = refl

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f (g , η , ε)
  f-is-op : is-order-preserving [ ∑ 𝟚ᵒ υ ] ([ τ₀ ] +ₒ [ τ₁ ]) f

  f-is-op (inl ⋆ , _) (inl ⋆ , _) (inr (refl , l)) = l
  f-is-op (inl ⋆ , _) (inr ⋆ , _) (inl ⋆)          = ⋆
  f-is-op (inr ⋆ , _) (inl ⋆ , _) (inl l)          = l
  f-is-op (inr ⋆ , _) (inr ⋆ , _) (inr (refl , l)) = l

  g-is-op : is-order-preserving ([ τ₀ ] +ₒ [ τ₁ ]) [ ∑ 𝟚ᵒ υ ] g
  g-is-op (inl _) (inl _) l = inr (refl , l)
  g-is-op (inl _) (inr _) ⋆ = inl ⋆
  g-is-op (inr _) (inl _) ()
  g-is-op (inr _) (inr _) l = inr (refl , l)

  e : [ ∑ 𝟚ᵒ υ ] ≃ₒ ([ τ₀ ] +ₒ [ τ₁ ])
  e = f , f-is-op , f-is-equiv , g-is-op

alternative-plus : (τ₀ τ₁ : Ordinalᵀ 𝓤)
                 → [ τ₀ +ᵒ τ₁ ] ＝ ([ τ₀ ] +ₒ [ τ₁ ])
alternative-plus τ₀ τ₁ = eqtoidₒ (ua _) fe' _ _ (alternative-plusₒ τ₀ τ₁)

\end{code}
