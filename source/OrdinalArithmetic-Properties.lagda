Martin Escardo, 18 January 2021.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-Univalence

module OrdinalArithmetic-Properties
       (ua : Univalence)
       where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-UA-FunExt
open import UF-FunExt
open import UF-EquivalenceExamples
open import UF-Embeddings
open import UF-ExcludedMiddle

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

open import SpartanMLTT
open import OrdinalsType
open import OrdinalNotions
open import OrdinalOfOrdinals ua
open import OrdinalArithmetic fe
open import Plus-Properties

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
  h = f , order-preserving-reflecting-equivs-are-order-equivs (𝟘ₒ +ₒ α) α f
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
  h = f , order-preserving-reflecting-equivs-are-order-equivs (α +ₒ 𝟘ₒ) α f
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
  h = f , order-preserving-reflecting-equivs-are-order-equivs
           ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ))
           f (⌜⌝-is-equiv +assoc) f-preserves-order f-reflects-order

+ₒ-↓-left : {α β : Ordinal 𝓤} (a : ⟨ α ⟩)
          → (α ↓ a) ≡ ((α +ₒ β) ↓ inl a)
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
           → (α +ₒ (β ↓ b)) ≡ ((α +ₒ β) ↓ inr b)
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

  h : γ ≡ δ
  h = eqtoidₒ γ δ (f , f-is-order-preserving , f-is-equiv , g-is-order-preserving)

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
  q =  (α +ₒ β)           ≡⟨ ap (α +ₒ_) p ⟩
       (α +ₒ (γ ↓ c))     ≡⟨ +ₒ-↓-right c ⟩
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

    q : α +ₒ (β ↓ b) ≡ (α +ₒ β) ↓ inr b
    q = +ₒ-↓-right b

    s : ((α +ₒ β) ↓ inr b) ⊲ (α +ₒ γ)
    s = transport (_⊲ (α  +ₒ γ)) q p

  ϕ : (x : ⟨ α +ₒ β ⟩) → ((α +ₒ β) ↓ x) ⊲ (α +ₒ γ)
  ϕ = dep-cases l r


\end{code}

TODO. Find better names for the following lemmas.

\begin{code}

lemma₀ : {α β : Ordinal 𝓤}
       → α ≼ (α +ₒ β)
lemma₀ {𝓤} {α} {β} = to-≼ ϕ
 where
  ϕ : (a : ⟨ α ⟩) → Σ z ꞉ ⟨ α +ₒ β ⟩ , (α ↓ a) ≡ ((α +ₒ β) ↓ z)
  ϕ a = inl a , (+ₒ-↓-left a)

lemma₁ : {α β : Ordinal 𝓤}
         (a : ⟨ α ⟩)
       → (α +ₒ β) ≢ (α ↓ a)
lemma₁ {𝓤} {α} {β} a p = irrefl (OO 𝓤) (α +ₒ β) m
 where
  l : (α +ₒ β) ⊲ α
  l = (a , p)

  m : (α +ₒ β) ⊲ (α +ₒ β)
  m = lemma₀ (α +ₒ β) l

lemma₂ : {α β : Ordinal 𝓤} (a : ⟨ α ⟩)
       → α ≡ β
       → Σ b ꞉ ⟨ β ⟩ , (α ↓ a) ≡ (β ↓ b)
lemma₂ a refl = a , refl

lemma₃ : {α β γ : Ordinal 𝓤} (b : ⟨ β ⟩) (z : ⟨ α +ₒ γ ⟩)
       → ((α +ₒ β) ↓ inr b) ≡ ((α +ₒ γ) ↓ z)
       → Σ c ꞉ ⟨ γ ⟩ , z ≡ inr c
lemma₃ {𝓤} {α} {β} {γ} b (inl a) p = 𝟘-elim (lemma₁ a q)
 where
  q : (α +ₒ (β ↓ b)) ≡ (α ↓ a)
  q = +ₒ-↓-right b ∙ p ∙ (+ₒ-↓-left a)⁻¹

lemma₃ b (inr c) p = c , refl

+ₒ-left-cancellable : (α β γ : Ordinal 𝓤)
                    → (α +ₒ β) ≡ (α +ₒ γ)
                    → β ≡ γ
+ₒ-left-cancellable {𝓤} α = g
 where
  P : Ordinal 𝓤 → 𝓤 ⁺ ̇
  P β = ∀ γ → (α +ₒ β) ≡ (α +ₒ γ) → β ≡ γ

  ϕ : ∀ β
    → (∀ b → P (β ↓ b))
    → P β
  ϕ β f γ p = Extensionality (OO 𝓤) β γ (to-≼ u) (to-≼ v)
   where
    u : (b : ⟨ β ⟩) → (β ↓ b) ⊲ γ
    u b = c , t
     where
      z : ⟨ α +ₒ γ ⟩
      z = pr₁ (lemma₂ (inr b) p)

      r : ((α +ₒ β) ↓ inr b) ≡ ((α +ₒ γ) ↓ z)
      r = pr₂ (lemma₂ (inr b) p)

      c : ⟨ γ ⟩
      c = pr₁ (lemma₃ b z r)

      s : z ≡ inr c
      s = pr₂ (lemma₃ b z r)

      q = (α +ₒ (β ↓ b))     ≡⟨ +ₒ-↓-right b ⟩
          ((α +ₒ β) ↓ inr b) ≡⟨ r ⟩
          ((α +ₒ γ) ↓ z)     ≡⟨ ap ((α +ₒ γ) ↓_) s ⟩
          ((α +ₒ γ) ↓ inr c) ≡⟨ (+ₒ-↓-right c)⁻¹ ⟩
          (α +ₒ (γ ↓ c))     ∎

      t : (β ↓ b) ≡ (γ ↓ c)
      t = f b (γ ↓ c) q

    v : (c : ⟨ γ ⟩) → (γ ↓ c) ⊲ β
    v c = b , (t ⁻¹)
     where
      z : ⟨ α +ₒ β ⟩
      z = pr₁ (lemma₂ (inr c) (p ⁻¹))

      r : ((α +ₒ γ) ↓ inr c) ≡ ((α +ₒ β) ↓ z)
      r = pr₂ (lemma₂ (inr c) (p ⁻¹))

      b : ⟨ β ⟩
      b = pr₁ (lemma₃ c z r)

      s : z ≡ inr b
      s = pr₂ (lemma₃ c z r)

      q = (α +ₒ (γ ↓ c))     ≡⟨ +ₒ-↓-right c ⟩
          ((α +ₒ γ) ↓ inr c) ≡⟨ r ⟩
          ((α +ₒ β) ↓ z)     ≡⟨ ap ((α +ₒ β) ↓_) s ⟩
          ((α +ₒ β) ↓ inr b) ≡⟨ (+ₒ-↓-right b)⁻¹ ⟩
          (α +ₒ (β ↓ b))     ∎

      t : (β ↓ b) ≡ (γ ↓ c)
      t = f b (γ ↓ c) (q ⁻¹)

  g : (β : Ordinal 𝓤) → P β
  g = transfinite-induction-on-OO P ϕ


left-+ₒ-is-embedding : (α : Ordinal 𝓤) → is-embedding (α +ₒ_)
left-+ₒ-is-embedding α = lc-maps-into-sets-are-embeddings (α +ₒ_)
                           (λ {β} {γ} → +ₒ-left-cancellable α β γ)
                           the-type-of-ordinals-is-a-set

\end{code}

This implies that the function α +ₒ_ reflects the _⊲_ ordering:

\begin{code}

+ₒ-left-reflects-⊲ : (α β γ : Ordinal 𝓤)
                   → (α +ₒ β) ⊲ (α +ₒ γ)
                   → β ⊲ γ
+ₒ-left-reflects-⊲ α β γ (inl a , p) = 𝟘-elim (lemma₁ a q)
   where
    q : (α +ₒ β) ≡ (α ↓ a)
    q = p ∙ (+ₒ-↓-left a)⁻¹

+ₒ-left-reflects-⊲ α β γ (inr c , p) = l
   where
    q : (α +ₒ β) ≡ (α +ₒ (γ ↓ c))
    q = p ∙ (+ₒ-↓-right c)⁻¹

    r : β ≡ (γ ↓ c)
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
α +ₒ γ ≡ β. But this not the case constructively. For that purpose, we
first characterize the order of subsingleton ordinals.

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
   s : P ≡ (Q × 𝟘)
   s = ap ⟨_⟩ r

   u : ¬ P
   u p = 𝟘-elim (pr₂ (⌜ idtoeq P (Q × 𝟘) s ⌝ p))

 fact₀-converse : ¬ P × Q → p ⊲ q
 fact₀-converse (u , y) = (y , g)
  where
   r : P ≡ Q × 𝟘
   r = univalence-gives-propext (ua 𝓤)
        P-is-prop
        ×-𝟘-is-prop
        (λ p → 𝟘-elim (u p))
        (λ (q , z) → 𝟘-elim z)

   g : p ≡ (q ↓ y)
   g = to-Σ-≡ (r ,
       to-Σ-≡ (dfunext fe' (λ (y , z) → 𝟘-elim z) ,
               being-well-order-is-prop (underlying-order (q ↓ y)) fe _ _))

 fact₁ : p ≼ q → (P → Q)
 fact₁ l x = pr₁ (from-≼ {𝓤} {p} {q} l x)

 fact₁-converse : (P → Q) → p ≼ q
 fact₁-converse f = to-≼ {𝓤} {p} {q} ϕ
  where
   r : P × 𝟘 ≡ Q × 𝟘
   r = univalence-gives-propext (ua 𝓤)
        ×-𝟘-is-prop
        ×-𝟘-is-prop
        (λ (p , z) → 𝟘-elim z)
        (λ (q , z) → 𝟘-elim z)

   ϕ : (x : ⟨ p ⟩) → (p ↓ x) ⊲ q
   ϕ x = f x , s
    where
     s : ((P × 𝟘) , (λ x x' → 𝟘) , _) ≡ ((Q × 𝟘) , (λ y y' → 𝟘) , _)
     s = to-Σ-≡ (r ,
         to-Σ-≡ (dfunext fe' (λ z → 𝟘-elim (pr₂ z)) ,
                 being-well-order-is-prop (underlying-order (q ↓ f x)) fe _ _))
\end{code}

The existence of ordinal subtraction implies excluded middle.

\begin{code}

existence-of-subtraction : (𝓤 : Universe) → 𝓤 ⁺ ̇
existence-of-subtraction 𝓤 = (α β : Ordinal 𝓤) → α ≼ β → Σ γ ꞉ Ordinal 𝓤 , α +ₒ γ ≡ β

existence-of-subtraction-is-prop : is-prop (existence-of-subtraction 𝓤)
existence-of-subtraction-is-prop = Π₃-is-prop (λ {𝓤} {𝓥} → fe 𝓤 𝓥)
                                     (λ α β l → left-+ₒ-is-embedding α β)


ordinal-subtraction-gives-excluded-middle : existence-of-subtraction 𝓤 → EM 𝓤
ordinal-subtraction-gives-excluded-middle {𝓤} ϕ P P-is-prop = g
 where
  α = prop-ordinal P P-is-prop
  β = prop-ordinal 𝟙 𝟙-is-prop
  σ = ϕ α β (fact₁-converse {𝓤} P 𝟙 P-is-prop 𝟙-is-prop (λ _ → ⋆))

  γ : Ordinal 𝓤
  γ = pr₁ σ

  r : α +ₒ γ ≡ β
  r = pr₂ σ

  s : P + ⟨ γ ⟩ ≡ 𝟙
  s = ap ⟨_⟩ r

  t : P + ⟨ γ ⟩
  t = idtofun 𝟙 (P + ⟨ γ ⟩) (s ⁻¹) ⋆

  f : ⟨ γ ⟩ → ¬ P
  f c p = z
   where
    A : 𝓤 ̇ → 𝓤 ̇
    A X = Σ x ꞉ X , Σ y ꞉ X , x ≢ y

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

Another example where subtraction doesn't exist is (ℕₒ +ₒ 𝟙ₒ) ≼ ℕ∞ₒ,
discussed in the module OrdinalOfOrdinals. The types ℕₒ +ₒ 𝟙ₒ and ℕ∞ₒ
are equal if and only if LPO holds. Without assuming LPO, the image of
the inclusion (ℕₒ +ₒ 𝟙ₒ) → ℕ∞ₒ, has empty complement, and so there is
nothing that can be added to (ℕₒ +ₒ 𝟙ₒ) to get ℕ∞ₒ, unless LPO holds.

\begin{code}

open import UF-Retracts

retract-Ω-of-Ordinal : retract (Ω 𝓤) of (Ordinal 𝓤)
retract-Ω-of-Ordinal {𝓤} = r , s , η
 where
  s : Ω 𝓤 → Ordinal 𝓤
  s (P , i) = prop-ordinal P i

  r : Ordinal 𝓤 → Ω 𝓤
  r α = has-bottom α , having-bottom-is-prop fe' α

  η : r ∘ s ∼ id
  η (P , i) = to-subtype-≡ (λ _ → being-prop-is-prop fe') t
   where
    f : P → has-bottom (prop-ordinal P i)
    f p = p , (λ x u → id)

    g : has-bottom (prop-ordinal P i) → P
    g (p , _) = p

    t : has-bottom (prop-ordinal P i) ≡ P
    t = pe 𝓤 (having-bottom-is-prop fe' (prop-ordinal P i)) i g f

\end{code}

Added 29 March 2022.

It is not the case in general that β ≼ α +ₒ β. We work with the
equivalent order _⊴_.

\begin{code}

module _ {𝓤 : Universe} where

 open import OrdinalOfTruthValues fe 𝓤 (pe 𝓤)

 open import DiscreteAndSeparated
 open import UF-Miscelanea

 ⊴-add-taboo : Ωₒ ⊴ (𝟙ₒ +ₒ Ωₒ) → WEM 𝓤
 ⊴-add-taboo (f , s) = VI
  where
   I : is-minimal Ωₒ ⊥Ω
   I (P , i) (𝟘 , 𝟘-is-prop) (refl , q) = 𝟘-elim (equal-⊤-is-true 𝟘 𝟘-is-prop q)

   II : is-minimal (𝟙ₒ +ₒ Ωₒ) (inl ⋆)
   II (inl ⋆) u       l = l
   II (inr x) (inl ⋆) l = 𝟘-elim l
   II (inr x) (inr y) l = 𝟘-elim l

   III : f ⊥Ω ≡ inl ⋆
   III = simulations-preserve-minimals Ωₒ (𝟙ₒ +ₒ Ωₒ) ⊥Ω (inl ⋆) f s I II

   IV : is-isolated (f ⊥Ω)
   IV = transport is-isolated (III ⁻¹) (inl-is-isolated ⋆ (𝟙-is-discrete ⋆))

   V : is-isolated ⊥Ω
   V = lc-maps-reflect-isolatedness f (simulations-are-lc Ωₒ (𝟙ₒ +ₒ Ωₒ) f s) ⊥Ω IV

   VI : ∀ P → is-prop P → ¬ P + ¬¬ P
   VI P i = Cases (V (P , i))
             (λ (e : ⊥Ω ≡ (P , i))
                   → inl (equal-𝟘-is-empty (ap pr₁ (e ⁻¹))))
             (λ (ν : ⊥Ω ≢ (P , i))
                   → inr (contrapositive
                           (λ (u : ¬ P)
                                 → to-subtype-≡ (λ _ → being-prop-is-prop fe')
                                    (empty-types-are-≡-𝟘 fe' (pe 𝓤) u)⁻¹) ν))
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
  k : (x : ⟨ α ⟩) (t : ⟨ β ⟩ + 𝟙) → f (inl x) ≡ t → Σ y ꞉ ⟨ β ⟩ , f (inl x) ≡ inl y
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

  h : (x : ⟨ α ⟩) → Σ y ꞉ ⟨ β ⟩ , f (inl x) ≡ inl y
  h x = k x (f (inl x)) refl

  g : ⟨ α ⟩ → ⟨ β ⟩
  g x = pr₁ (h x)

  ϕ : (x : ⟨ α ⟩) → f (inl x) ≡ inl (g x)
  ϕ x = pr₂ (h x)

  j : is-initial-segment α β g
  j x y l = II I
   where
    m : inl y ≺⟨ β +ₒ 𝟙ₒ ⟩ f (inl x)
    m = transport (λ - → inl y ≺⟨ β +ₒ 𝟙ₒ ⟩ -) ((ϕ x)⁻¹) l

    I : Σ z ꞉ ⟨ α +ₒ 𝟙ₒ ⟩ , (z ≺⟨ α +ₒ 𝟙ₒ ⟩ inl x) × (f z ≡ inl y)
    I = i (inl x) (inl y) m

    II : type-of I → Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (g x' ≡ y)
    II (inl x' , n , e) = x' , n , inl-lc (inl (g x') ≡⟨ (ϕ x')⁻¹ ⟩
                                           f (inl x') ≡⟨ e ⟩
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

However, the successor function does not preserve _⊴_ in general:

\begin{code}

succ-not-necessarily-monotone : ((α β : Ordinal 𝓤) → α ⊴ β → (α +ₒ 𝟙ₒ) ⊴ (β +ₒ 𝟙ₒ))
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
    III : (y : ⟨ 𝟚ₒ ⟩) → f (inr ⋆) ≡ y → ¬ P + ¬¬ P
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
      VIII : Σ x' ꞉ ⟨ α +ₒ 𝟙ₒ ⟩ , (x' ≺⟨ α +ₒ 𝟙ₒ ⟩ inr ⋆) × (f x' ≡ inl ⋆)
      VIII = f-is-initial (inr ⋆) (inl ⋆) (transport (λ - → inl ⋆ ≺⟨ 𝟚ₒ ⟩ -) (e ⁻¹) ⋆)

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
