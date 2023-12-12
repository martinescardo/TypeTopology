Martin Escardo, August 2018

The ordinal of ordinals. Based on the HoTT Book, with a few
modifications in some of the definitions and arguments.

This is an example where we are studying sets only, but the univalence
axiom is used to show that (1) the type of ordinals forms a (large)
set, (2) its order is extensional, (3) hence it is itself a (large)
ordinal, (4) the type of ordinals is locally small.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence

module Ordinals.OrdinalOfOrdinals
        (ua : Univalence)
       where

open import MLTT.Spartan
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Subsingletons
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

\end{code}

The simulations make the ordinals into a poset:

\begin{code}

_⊴_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
α ⊴ β = Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-simulation α β f

⊴-gives-↪ : (α : Ordinal 𝓤)
            (β : Ordinal 𝓥)
          → α ⊴ β
          → ⟨ α ⟩ ↪ ⟨ β ⟩
⊴-gives-↪ α β (f , s) = f , simulations-are-embeddings fe α β f s

⊴-is-prop-valued : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → is-prop (α ⊴ β)
⊴-is-prop-valued {𝓤} {𝓥} α β (f , s) (g , t) =
 to-subtype-＝
  (being-simulation-is-prop fe' α β)
  (dfunext fe' (at-most-one-simulation α β f g s t))

⊴-refl : (α : Ordinal 𝓤) → α ⊴ α
⊴-refl α = id ,
           (λ x z l → z , l , refl) ,
           (λ x y l → l)

⊴-trans : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (γ : Ordinal 𝓦)
        → α ⊴ β → β ⊴ γ → α ⊴ γ
⊴-trans α β γ (f , i , p) (g , j , q) = g ∘ f ,
                                        k ,
                                        (λ x y l → q (f x) (f y) (p x y l))
 where
  k : (x : ⟨ α ⟩) (z : ⟨ γ ⟩) →  z ≺⟨ γ ⟩ (g (f x))
    → Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (g (f x') ＝ z)
  k x z l = pr₁ b , pr₁ (pr₂ b) , (ap g (pr₂ (pr₂ b)) ∙ pr₂ (pr₂ a))
   where
    a : Σ y ꞉ ⟨ β ⟩ , (y ≺⟨ β ⟩ f x) × (g y ＝ z)
    a = j (f x) z l

    y : ⟨ β ⟩
    y = pr₁ a

    b : Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ＝ y)
    b = i x y (pr₁ (pr₂ a))

≃ₒ-to-⊴ : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → α ≃ₒ β → α ⊴ β
≃ₒ-to-⊴ α β (f , e) = (f , order-equivs-are-simulations α β f e)

ordinal-equiv-gives-bisimilarity : (α β : Ordinal 𝓤)
                                 → α ≃ₒ β
                                 → (α ⊴ β) × (β ⊴ α)
ordinal-equiv-gives-bisimilarity α β (f , p , e , q) = γ
 where
  g : ⟨ β ⟩ → ⟨ α ⟩
  g = ⌜ f , e ⌝⁻¹

  d : is-equiv g
  d = ⌜⌝-is-equiv (≃-sym (f , e))

  γ : (α ⊴ β) × (β ⊴ α)
  γ = (f , order-equivs-are-simulations α β f (p , e , q)) ,
      (g , order-equivs-are-simulations β α g (q , d , p))

bisimilarity-gives-ordinal-equiv : (α β : Ordinal 𝓤)
                                 → α ⊴ β
                                 → β ⊴ α
                                 → α ≃ₒ β
bisimilarity-gives-ordinal-equiv α β (f , s) (g , t) = γ
 where
  ηs : is-simulation β β (f ∘ g)
  ηs = pr₂ (⊴-trans β α β (g , t) (f , s))

  η : (y : ⟨ β ⟩) → f (g y) ＝ y
  η = at-most-one-simulation β β (f ∘ g) id ηs (pr₂ (⊴-refl β))

  εs : is-simulation α α (g ∘ f)
  εs = pr₂ (⊴-trans α β α (f , s) (g , t))

  ε : (x : ⟨ α ⟩) → g (f x) ＝ x
  ε = at-most-one-simulation α α (g ∘ f) id εs (pr₂ (⊴-refl α))

  γ : α ≃ₒ β
  γ =  f , pr₂ s , qinvs-are-equivs f (g , ε , η) , pr₂ t

\end{code}

A corollary of the above is that the ordinal order _⊴_ is
antisymmetric.

\begin{code}

⊴-antisym : (α β : Ordinal 𝓤)
          → α ⊴ β
          → β ⊴ α
          → α ＝ β
⊴-antisym α β l m =
 eqtoidₒ (ua _) fe' α β (bisimilarity-gives-ordinal-equiv α β l m)

\end{code}

Any lower set α ↓ a of a point a : ⟨ α ⟩ forms a (sub-)ordinal:

\begin{code}

_↓_ : (α : Ordinal 𝓤) → ⟨ α ⟩ → Ordinal 𝓤
α ↓ a = (Σ x ꞉ ⟨ α ⟩ , x ≺⟨ α ⟩ a) , _<_ , p , w , e , t
 where
  _<_ : (Σ x ꞉ ⟨ α ⟩ , x ≺⟨ α ⟩ a) → (Σ x ꞉ ⟨ α ⟩ , x ≺⟨ α ⟩ a) → _ ̇
  (y , _) < (z , _) = y ≺⟨ α ⟩ z

  p : is-prop-valued _<_
  p (x , _) (y , _)  = Prop-valuedness α x y

  w : is-well-founded _<_
  w (x , l) = f x (Well-foundedness α x) l
   where
    f : ∀ x
      → is-accessible (underlying-order α) x
      → ∀ l → is-accessible _<_ (x , l)
    f x (acc s) l = acc (λ σ m → f (pr₁ σ) (s (pr₁ σ) m) (pr₂ σ))

  e : is-extensional _<_
  e (x , l) (y , m) f g =
    to-subtype-＝
     (λ z → Prop-valuedness α z a)
     (Extensionality α x y
       (λ u n → f (u , Transitivity α u x a n l) n)
       (λ u n → g (u , Transitivity α u y a n m) n))

  t : is-transitive _<_
  t (x , _) (y , _) (z , _) = Transitivity α x y z

segment-inclusion : (α : Ordinal 𝓤) (a : ⟨ α ⟩)
                  → ⟨ α ↓ a ⟩ → ⟨ α ⟩
segment-inclusion α a = pr₁

segment-inclusion-bound : (α : Ordinal 𝓤) (a : ⟨ α ⟩)
                        → (x : ⟨ α ↓ a ⟩)
                        → segment-inclusion α a x ≺⟨ α ⟩ a
segment-inclusion-bound α a = pr₂

segment-inclusion-is-simulation : (α : Ordinal 𝓤) (a : ⟨ α ⟩)
                                → is-simulation (α ↓ a) α (segment-inclusion α a)
segment-inclusion-is-simulation α a = i , p
 where
  i : is-initial-segment (α ↓ a) α (segment-inclusion α a)
  i (x , l) y m = (y , Transitivity α y x a m l) , m , refl

  p : is-order-preserving (α ↓ a) α (segment-inclusion α a)
  p x x' = id

segment-⊴ : (α : Ordinal 𝓤) (a : ⟨ α ⟩)
          → (α ↓ a) ⊴ α
segment-⊴ α a = segment-inclusion α a , segment-inclusion-is-simulation α a

↓-⊴-lc : (α : Ordinal 𝓤) (a b : ⟨ α ⟩)
       → (α ↓ a) ⊴ (α ↓ b )
       → a ≼⟨ α ⟩ b
↓-⊴-lc {𝓤} α a b (f , s) u l = n
 where
  h : segment-inclusion α a ∼ segment-inclusion α b ∘ f
  h = at-most-one-simulation (α ↓ a) α
        (segment-inclusion α a)
        (segment-inclusion α b ∘ f)
        (segment-inclusion-is-simulation α a)
        (pr₂ (⊴-trans (α ↓ a) (α ↓ b) α
                 (f , s)
                 (segment-⊴ α b)))

  v : ⟨ α ⟩
  v = segment-inclusion α b (f (u , l))

  m : v ≺⟨ α ⟩ b
  m = segment-inclusion-bound α b (f (u , l))

  q : u ＝ v
  q = h (u , l)

  n : u ≺⟨ α ⟩ b
  n = transport⁻¹ (λ - → - ≺⟨ α ⟩ b) q m

↓-lc : (α : Ordinal 𝓤) (a b : ⟨ α ⟩)
     → α ↓ a ＝ α ↓ b
     → a ＝ b
↓-lc α a b p =
 Extensionality α a b
  (↓-⊴-lc α a b (transport      (λ - → (α ↓ a) ⊴ -) p (⊴-refl (α ↓ a))))
  (↓-⊴-lc α b a (transport⁻¹ (λ - → (α ↓ b) ⊴ -) p (⊴-refl (α ↓ b))))

↓-is-embedding : (α : Ordinal 𝓤) → is-embedding (α ↓_)
↓-is-embedding α = lc-maps-into-sets-are-embeddings
                    (α ↓_)
                    (↓-lc α _ _)
                    (the-type-of-ordinals-is-a-set (ua _) fe')
\end{code}

We are now ready to make the type of ordinals into an ordinal.

\begin{code}

_⊲_ : Ordinal 𝓤 → Ordinal 𝓤 → 𝓤 ⁺ ̇
α ⊲ β = Σ b ꞉ ⟨ β ⟩ , α ＝ (β ↓ b)

⊲-is-prop-valued : (α β : Ordinal 𝓤) → is-prop (α ⊲ β)
⊲-is-prop-valued {𝓤} α β (b , p) (b' , p') = γ
 where
  q = (β ↓ b)  ＝⟨ p ⁻¹ ⟩
       α       ＝⟨ p' ⟩
      (β ↓ b') ∎

  r : b ＝ b'
  r = ↓-lc β b b' q

  γ : (b , p) ＝ (b' , p')
  γ = to-subtype-＝ (λ x → the-type-of-ordinals-is-a-set (ua 𝓤) fe') r

\end{code}

NB. We could instead define α ⊲ β to mean that we have b with
α ≃ₒ (β ↓ b), or with α ⊴ (β ↓ b) and (β ↓ b) ⊴ α, by antisymmetry,
and these two alternative, equivalent, definitions make ⊲ to have
values in the universe 𝓤 rather than the next universe 𝓤 ⁺.

Added 23 December 2020. The previous observation turns out to be
useful to resize down the relation _⊲_ in certain applications. So we
make it official:

\begin{code}

_⊲⁻_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
α ⊲⁻ β = Σ b ꞉ ⟨ β ⟩ , α ≃ₒ (β ↓ b)

⊲-is-equivalent-to-⊲⁻ : (α β : Ordinal 𝓤) → (α ⊲ β) ≃ (α ⊲⁻ β)
⊲-is-equivalent-to-⊲⁻ α β = Σ-cong (λ (b : ⟨ β ⟩) → UAₒ-≃ (ua _) fe' α (β ↓ b))

\end{code}

Back to the past.

A lower set of a lower set is a lower set:

\begin{code}

iterated-↓ : (α : Ordinal 𝓤) (a b : ⟨ α ⟩) (l : b ≺⟨ α ⟩ a)
           → ((α ↓ a ) ↓ (b , l)) ＝ (α ↓ b)
iterated-↓ α a b l = ⊴-antisym ((α ↓ a) ↓ (b , l)) (α ↓ b)
                      (φ α a b l) (ψ α a b l)
 where
  φ : (α : Ordinal 𝓤) (b u : ⟨ α ⟩) (l : u ≺⟨ α ⟩ b)
    → ((α ↓ b ) ↓ (u , l)) ⊴ (α ↓ u)
  φ α b u l = f , i , p
   where
    f : ⟨ (α ↓ b) ↓ (u , l) ⟩ → ⟨ α ↓ u ⟩
    f ((x , m) , n) = x , n

    i : (w : ⟨ (α ↓ b) ↓ (u , l) ⟩) (t : ⟨ α ↓ u ⟩)
      → t ≺⟨ α ↓ u ⟩ f w
      → Σ w' ꞉ ⟨ (α ↓ b) ↓ (u , l) ⟩ , (w' ≺⟨ (α ↓ b) ↓ (u , l) ⟩ w) × (f w' ＝ t)
    i ((x , m) , n) (x' , m') n' = ((x' , Transitivity α x' u b m' l) , m') ,
                                    (n' , refl)

    p : (w w' : ⟨ (α ↓ b) ↓ (u , l) ⟩)
      → w ≺⟨ (α ↓ b) ↓ (u , l) ⟩ w' → f w ≺⟨ α ↓ u ⟩ (f w')
    p w w' = id

  ψ : (α : Ordinal 𝓤) (b u : ⟨ α ⟩) (l : u ≺⟨ α ⟩ b)
    → (α ↓ u) ⊴ ((α ↓ b ) ↓ (u , l))
  ψ α b u l = f , (i , p)
   where
    f : ⟨ α ↓ u ⟩ → ⟨ (α ↓ b) ↓ (u , l) ⟩
    f (x , n) = ((x , Transitivity α x u b n l) , n)

    i : (t : ⟨ α ↓ u ⟩)
        (w : ⟨ (α ↓ b) ↓ (u , l) ⟩)
      → w ≺⟨ (α ↓ b) ↓ (u , l) ⟩ f t
      → Σ t' ꞉ ⟨ α ↓ u ⟩ , (t' ≺⟨ α ↓ u ⟩ t) × (f t' ＝ w)
    i (x , n) ((x' , m') , n') o = (x' , n') , (o , r)
     where
      r : ((x' , Transitivity α x' u b n' l) , n') ＝ (x' , m') , n'
      r = ap (λ - → ((x' , -) , n'))
             (Prop-valuedness α x' b (Transitivity α x' u b n' l) m')

    p : (t t' : ⟨ α ↓ u ⟩) → t ≺⟨ α ↓ u ⟩ t' → f t ≺⟨ (α ↓ b) ↓ (u , l) ⟩ f t'
    p t t' = id

\end{code}

Therefore the map (α ↓ -) reflects and preserves order:

\begin{code}

↓-reflects-order : (α : Ordinal 𝓤) (a b : ⟨ α ⟩)
                 → (α ↓ a) ⊲ (α ↓ b)
                 → a ≺⟨ α ⟩ b
↓-reflects-order α a b ((u , l) , p) = γ
 where
  have : type-of l ＝ (u ≺⟨ α ⟩ b)
  have = refl

  q : (α ↓ a) ＝ (α ↓ u)
  q = (α ↓ a)             ＝⟨ p ⟩
      ((α ↓ b) ↓ (u , l)) ＝⟨ iterated-↓ α b u l ⟩
      (α ↓ u)             ∎

  r : a ＝ u
  r = ↓-lc α a u q

  γ : a ≺⟨ α ⟩ b
  γ = transport⁻¹ (λ - → - ≺⟨ α ⟩ b) r l

↓-preserves-order : (α : Ordinal 𝓤) (a b : ⟨ α ⟩)
                  → a ≺⟨ α ⟩ b
                  → (α ↓ a) ⊲ (α ↓ b)
↓-preserves-order α a b l = (a , l) , ((iterated-↓ α b a l)⁻¹)

\end{code}

It remains to show that _⊲_ is a well-order:

\begin{code}

↓-accessible : (α : Ordinal 𝓤) (a : ⟨ α ⟩)
             → is-accessible _⊲_ (α ↓ a)
↓-accessible {𝓤} α a = f a (Well-foundedness α a)
 where
  f : (a : ⟨ α ⟩)
    → is-accessible (underlying-order α) a
    → is-accessible _⊲_ (α ↓ a)
  f a (acc s) = acc g
   where
    IH : (b : ⟨ α ⟩) → b ≺⟨ α ⟩ a → is-accessible _⊲_ (α ↓ b)
    IH b l = f b (s b l)

    g : (β : Ordinal 𝓤) → β ⊲ (α ↓ a) → is-accessible _⊲_ β
    g β ((b , l) , p) = transport⁻¹ (is-accessible _⊲_) q (IH b l)
     where
      q : β ＝ (α ↓ b)
      q = p ∙ iterated-↓ α a b l

⊲-is-well-founded : is-well-founded (_⊲_ {𝓤})
⊲-is-well-founded {𝓤} α = acc g
 where
  g : (β : Ordinal 𝓤) → β ⊲ α → is-accessible _⊲_ β
  g β (b , p) = transport⁻¹ (is-accessible _⊲_) p (↓-accessible α b)

⊲-is-extensional : is-extensional (_⊲_ {𝓤})
⊲-is-extensional α β f g = ⊴-antisym α β
                           ((λ x → pr₁ (φ x)) , i , p)
                           ((λ y → pr₁ (γ y)) , j , q)
 where
  φ : (x : ⟨ α ⟩) → Σ y ꞉ ⟨ β ⟩ , α ↓ x ＝ β ↓ y
  φ x = f (α ↓ x) (x , refl)

  γ : (y : ⟨ β ⟩) → Σ x ꞉ ⟨ α ⟩ , β ↓ y ＝ α ↓ x
  γ y = g (β ↓ y) (y , refl)

  η : (x : ⟨ α ⟩) → pr₁ (γ (pr₁ (φ x))) ＝ x
  η x = (↓-lc α x (pr₁ (γ (pr₁ (φ x)))) a)⁻¹
   where
    a : (α ↓ x) ＝ (α ↓ pr₁ (γ (pr₁ (φ x))))
    a = pr₂ (φ x) ∙ pr₂ (γ (pr₁ (φ x)))

  ε : (y : ⟨ β ⟩) → pr₁ (φ (pr₁ (γ y))) ＝ y
  ε y = (↓-lc β y (pr₁ (φ (pr₁ (γ y)))) a)⁻¹
   where
    a : (β ↓ y) ＝ (β ↓ pr₁ (φ (pr₁ (γ y))))
    a = pr₂ (γ y) ∙ pr₂ (φ (pr₁ (γ y)))

  p : is-order-preserving α β (λ x → pr₁ (φ x))
  p x x' l = ↓-reflects-order β (pr₁ (φ x)) (pr₁ (φ x')) b
   where
    a : (α ↓ x) ⊲ (α ↓ x')
    a = ↓-preserves-order α x x' l

    b : (β ↓ pr₁ (φ x)) ⊲ (β ↓ pr₁ (φ x'))
    b = transport₂ _⊲_ (pr₂ (φ x)) (pr₂ (φ x')) a

  q : is-order-preserving β α (λ y → pr₁ (γ y))
  q y y' l = ↓-reflects-order α (pr₁ (γ y)) (pr₁ (γ y')) b
   where
    a : (β ↓ y) ⊲ (β ↓ y')
    a = ↓-preserves-order β y y' l

    b : (α ↓ pr₁ (γ y)) ⊲ (α ↓ pr₁ (γ y'))
    b = transport₂ _⊲_ (pr₂ (γ y)) (pr₂ (γ y')) a

  i : is-initial-segment α β (λ x → pr₁ (φ x))
  i x y l = pr₁ (γ y) , transport (λ - → pr₁ (γ y) ≺⟨ α ⟩ -) (η x) a , ε y
   where
    a : pr₁ (γ y) ≺⟨ α ⟩ (pr₁ (γ (pr₁ (φ x))))
    a = q y (pr₁ (φ x)) l

  j : is-initial-segment β α (λ y → pr₁ (γ y))
  j y x l = pr₁ (φ x) , transport (λ - → pr₁ (φ x) ≺⟨ β ⟩ -) (ε y) a , η x
   where
    a : pr₁ (φ x) ≺⟨ β ⟩ (pr₁ (φ (pr₁ (γ y))))
    a = p x (pr₁ (γ y)) l

⊲-is-transitive : is-transitive (_⊲_ {𝓤})
⊲-is-transitive {𝓤} α β φ (a , p) (b , q) = γ
 where
  t : (q : β ＝ (φ ↓ b)) → (β ↓ a) ＝ ((φ ↓ b) ↓ transport ⟨_⟩ q a)
  t refl = refl

  u : ⟨ φ ↓ b ⟩
  u = transport (⟨_⟩) q a

  c : ⟨ φ ⟩
  c = pr₁ u

  l : c ≺⟨ φ ⟩ b
  l = pr₂ u

  r : α ＝ (φ ↓ c)
  r = α             ＝⟨ p ⟩
      (β ↓ a)       ＝⟨ t q ⟩
      ((φ ↓ b) ↓ u) ＝⟨ iterated-↓ φ b c l ⟩
      (φ ↓ c)       ∎

  γ : Σ c ꞉ ⟨ φ ⟩ , α ＝ (φ ↓ c)
  γ = c , r

⊲-is-well-order : is-well-order (_⊲_ {𝓤})
⊲-is-well-order = ⊲-is-prop-valued ,
                  ⊲-is-well-founded ,
                  ⊲-is-extensional ,
                  ⊲-is-transitive
\end{code}

We denote the ordinal of ordinals in the universe 𝓤 by OO 𝓤. It lives
in the next universe 𝓤 ⁺.

\begin{code}

OO : (𝓤 : Universe) → Ordinal (𝓤 ⁺)
OO 𝓤 = Ordinal 𝓤 , _⊲_ , ⊲-is-well-order

\end{code}

Any ordinal in OO 𝓤 is embedded in OO 𝓤 as an initial segment:

\begin{code}

ordinals-in-OO-are-embedded-in-OO : (α : ⟨ OO 𝓤 ⟩) → α ⊴ OO 𝓤
ordinals-in-OO-are-embedded-in-OO {𝓤} α = (λ x → α ↓ x) , i , ↓-preserves-order α
 where
  i : is-initial-segment α (OO 𝓤) (λ x → α ↓ x)
  i x β ((u , l) , p) = u , l , ((p ∙ iterated-↓ α x u l)⁻¹)

OO-⊴-next-OO : OO 𝓤 ⊴ OO (𝓤 ⁺)
OO-⊴-next-OO {𝓤} = ordinals-in-OO-are-embedded-in-OO (OO 𝓤)

ordinals-are-embedded-in-Ordinal : (α : Ordinal 𝓤) → ⟨ α ⟩ ↪ Ordinal 𝓤
ordinals-are-embedded-in-Ordinal {𝓤} α = ⊴-gives-↪ α (OO 𝓤)
                                          (ordinals-in-OO-are-embedded-in-OO α)

Ordinal-embedded-in-next-Ordinal : Ordinal 𝓤 ↪ Ordinal (𝓤 ⁺)
Ordinal-embedded-in-next-Ordinal {𝓤} = ordinals-are-embedded-in-Ordinal (OO 𝓤)

\end{code}

Any ordinal in OO 𝓤 is a lower set of OO 𝓤:

\begin{code}

ordinals-in-OO-are-lowersets-of-OO : (α : ⟨ OO 𝓤 ⟩) → α ≃ₒ (OO 𝓤 ↓ α)
ordinals-in-OO-are-lowersets-of-OO {𝓤} α = f , p , ((g , η) , (g , ε)) , q
 where
  f : ⟨ α ⟩ → ⟨ OO 𝓤 ↓ α ⟩
  f x = α ↓ x , x , refl

  p : is-order-preserving α (OO 𝓤 ↓ α) f
  p x y l = (x , l) , ((iterated-↓ α y x l)⁻¹)

  g : ⟨ OO 𝓤 ↓ α ⟩ → ⟨ α ⟩
  g (β , x , r) = x

  η : (σ : ⟨ OO 𝓤 ↓ α ⟩) → f (g σ) ＝ σ
  η (.(α ↓ x) , x , refl) = refl

  ε : (x : ⟨ α ⟩) → g (f x) ＝ x
  ε x = refl

  q : is-order-preserving (OO 𝓤 ↓ α) α g
  q (.(α ↓ x) , x , refl) (.(α ↓ x') , x' , refl) = ↓-reflects-order α x x'

\end{code}

Added 19-20 January 2021.

The partial order _⊴_ is equivalent to _≼_.

We first observe that, almost tautologically, the relation α ≼ β is
logically equivalent to the condition (a : ⟨ α ⟩) → (α ↓ a) ⊲ β.

\begin{code}

_≼_ _≾_ : Ordinal 𝓤 → Ordinal 𝓤 → 𝓤 ⁺ ̇
α ≼ β = α ≼⟨ OO _ ⟩ β
α ≾ β = ¬ (β ≼ α)


to-≼ : {α β : Ordinal 𝓤}
     → ((a : ⟨ α ⟩)
     → (α ↓ a) ⊲ β)
     → α ≼ β
to-≼ {𝓤} {α} {β} ϕ α' (a , p) = m
 where
  l : (α ↓ a) ⊲ β
  l = ϕ a

  m : α' ⊲ β
  m = transport (_⊲ β) (p ⁻¹) l

from-≼ : {α β : Ordinal 𝓤}
       → α ≼ β
       → (a : ⟨ α ⟩)
       → (α ↓ a) ⊲ β
from-≼ {𝓤} {α} {β} l a = l (α ↓ a) m
 where
  m : (α ↓ a) ⊲ α
  m = (a , refl)

⊴-gives-≼ : (α β : Ordinal 𝓤) → α ⊴ β → α ≼ β
⊴-gives-≼ α β (f , f-is-initial-segment , f-is-order-preserving) α' (a , p) = l
 where
  f-is-simulation : is-simulation α β f
  f-is-simulation = f-is-initial-segment , f-is-order-preserving

  g : ⟨ α ↓ a ⟩ → ⟨ β ↓ f a ⟩
  g (x , l) = f x , f-is-order-preserving x a l

  h : ⟨ β ↓ f a ⟩ → ⟨ α ↓ a ⟩
  h (y , m) = pr₁ σ , pr₁ (pr₂ σ)
   where
    σ : Σ x ꞉ ⟨ α ⟩ , (x ≺⟨ α ⟩ a) × (f x ＝ y)
    σ = f-is-initial-segment a y m

  η : h ∘ g ∼ id
  η (x , l) = to-subtype-＝ (λ - → Prop-valuedness α - a) r
   where
    σ : Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ a) × (f x' ＝ f x)
    σ = f-is-initial-segment a (f x) (f-is-order-preserving x a l)

    x' = pr₁ σ

    have : pr₁ (h (g (x , l))) ＝ x'
    have = refl

    s : f x' ＝ f x
    s = pr₂ (pr₂ σ)

    r : x' ＝ x
    r = simulations-are-lc α β f f-is-simulation s

  ε : g ∘ h ∼ id
  ε (y , m) = to-subtype-＝ (λ - → Prop-valuedness β - (f a)) r
   where
    r : f (pr₁ (f-is-initial-segment a y m)) ＝ y
    r = pr₂ (pr₂ (f-is-initial-segment a y m))

  g-is-order-preserving : is-order-preserving (α ↓ a) (β ↓ f a) g
  g-is-order-preserving (x , _) (x' , _) = f-is-order-preserving x x'

  h-is-order-preserving : is-order-preserving (β ↓ f a) (α ↓ a) h
  h-is-order-preserving (y , m) (y' , m') l = o
   where
    have : y ≺⟨ β ⟩ y'
    have = l

    σ  = f-is-initial-segment a y  m
    σ' = f-is-initial-segment a y' m'

    x  = pr₁ σ
    x' = pr₁ σ'

    s : f x ＝ y
    s = pr₂ (pr₂ σ)

    s' : f x' ＝ y'
    s' = pr₂ (pr₂ σ')

    t : f x ≺⟨ β ⟩ f x'
    t = transport₂ (λ y y' → y ≺⟨ β ⟩ y') (s ⁻¹) (s' ⁻¹) l

    o : x ≺⟨ α ⟩ x'
    o = simulations-are-order-reflecting α β f f-is-simulation x x' t

  q : (α ↓ a) ＝ (β ↓ f a)
  q = eqtoidₒ (ua _) fe' (α ↓ a) (β ↓ f a)
        (g ,
         g-is-order-preserving ,
         qinvs-are-equivs g (h , η , ε) ,
         h-is-order-preserving)

  l : α' ⊲ β
  l = transport (_⊲ β) (p ⁻¹) (f a , q)

\end{code}

For the converse of the above, it suffices to show the following:

\begin{code}

to-⊴ : (α β : Ordinal 𝓤)
     → ((a : ⟨ α ⟩) → (α ↓ a) ⊲ β)
     → α ⊴ β
to-⊴ α β ϕ = g
 where
  f : ⟨ α ⟩ → ⟨ β ⟩
  f a = pr₁ (ϕ a)

  f-property : (a : ⟨ α ⟩) → (α ↓ a) ＝ (β ↓ f a)
  f-property a = pr₂ (ϕ a)

  f-is-order-preserving : is-order-preserving α β f
  f-is-order-preserving a a' l = o
   where
    m : (α ↓ a) ⊲ (α ↓ a')
    m = ↓-preserves-order α a a' l

    n : (β ↓ f a) ⊲ (β ↓ f a')
    n = transport₂ _⊲_ (f-property a) (f-property a') m

    o : f a ≺⟨ β ⟩ f a'
    o = ↓-reflects-order β (f a) (f a') n

  f-is-initial-segment : (x : ⟨ α ⟩) (y : ⟨ β ⟩)
                       → y ≺⟨ β ⟩ f x
                       → Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ＝ y)
  f-is-initial-segment x y l = x' , o , (q ⁻¹)
   where
    m : (β ↓ y) ⊲ (β ↓ f x)
    m = ↓-preserves-order β y (f x) l

    n : (β ↓ y) ⊲ (α ↓ x)
    n = transport ((β ↓ y) ⊲_) ((f-property x)⁻¹) m

    x' : ⟨ α ⟩
    x' = pr₁ (pr₁ n)

    o : x' ≺⟨ α ⟩ x
    o = pr₂ (pr₁ n)

    p = (β ↓ y)              ＝⟨ pr₂ n ⟩
        ((α ↓ x) ↓ (x' , o)) ＝⟨ iterated-↓ α x x' o ⟩
        (α ↓ x')             ＝⟨ f-property x' ⟩
        (β ↓ f x')           ∎

    q : y ＝ f x'
    q = ↓-lc β y (f x') p

  g : α ⊴ β
  g = f , f-is-initial-segment , f-is-order-preserving

≼-gives-⊴ : (α β : Ordinal 𝓤) → α ≼ β → α ⊴ β
≼-gives-⊴ {𝓤} α β l = to-⊴ α β (from-≼ l)

⊲-gives-≼ : (α β : Ordinal 𝓤) → α ⊲ β → α ≼ β
⊲-gives-≼ {𝓤} α β l α' m = Transitivity (OO 𝓤) α' α β m l

⊲-gives-⊴ : (α β : Ordinal 𝓤) → α ⊲ β → α ⊴ β
⊲-gives-⊴ α β l = ≼-gives-⊴ α β (⊲-gives-≼ α β l)

\end{code}

Transfinite induction on the ordinal of ordinals:

\begin{code}

transfinite-induction-on-OO : (P : Ordinal 𝓤 → 𝓥 ̇ )
                            → ((α : Ordinal 𝓤) → ((a : ⟨ α ⟩) → P (α ↓ a)) → P α)
                            → (α : Ordinal 𝓤) → P α
transfinite-induction-on-OO {𝓤} {𝓥} P f = Transfinite-induction (OO 𝓤) P f'
 where
  f' : (α : Ordinal 𝓤)
     → ((α' : Ordinal 𝓤) → α' ⊲ α → P α')
     → P α
  f' α g = f α (λ a → g (α ↓ a) (a , refl))

transfinite-recursion-on-OO : (X : 𝓥 ̇ )
                            → ((α : Ordinal 𝓤) → (⟨ α ⟩ → X) → X)
                            → Ordinal 𝓤 → X
transfinite-recursion-on-OO {𝓤} {𝓥} X = transfinite-induction-on-OO (λ _ → X)

has-minimal-element : Ordinal 𝓤 → 𝓤 ̇
has-minimal-element α = Σ a ꞉ ⟨ α ⟩ , ((x : ⟨ α ⟩) → a ≾⟨ α ⟩ x)

has-no-minimal-element : Ordinal 𝓤 → 𝓤 ̇
has-no-minimal-element α = ((a : ⟨ α ⟩) → ¬¬ (Σ x ꞉ ⟨ α ⟩ , x ≺⟨ α ⟩ a))

ordinal-with-no-minimal-element-is-empty : (α : Ordinal 𝓤)
                                         → has-no-minimal-element α
                                         → is-empty ⟨ α ⟩
ordinal-with-no-minimal-element-is-empty {𝓤} = transfinite-induction-on-OO P ϕ
 where
  P : Ordinal 𝓤 → 𝓤 ̇
  P α = has-no-minimal-element α → is-empty ⟨ α ⟩

  ϕ : (α : Ordinal 𝓤) → ((a : ⟨ α ⟩) → P (α ↓ a)) → P α
  ϕ α f g x = g x (f x h)
   where
    h : has-no-minimal-element (α ↓ x)
    h (y , l) u = g y (contrapositive k u)
     where
      k : ⟨ α ↓ y ⟩ → ⟨ (α ↓ x) ↓ (y , l) ⟩
      k (z , m) = (z , o) , m
       where
        o : z ≺⟨ α ⟩ x
        o = Transitivity α z y x m l

non-empty-classically-has-minimal-element : (α : Ordinal 𝓤)
                                          → is-nonempty ⟨ α ⟩
                                          → ¬¬ has-minimal-element α
non-empty-classically-has-minimal-element {𝓤} α n = iv
 where
  i : ¬ has-no-minimal-element α
  i = contrapositive (ordinal-with-no-minimal-element-is-empty α) n

  ii : ¬¬ (Σ a ꞉ ⟨ α ⟩ , ¬ (Σ x ꞉ ⟨ α ⟩ , x ≺⟨ α ⟩ a))
  ii = not-Π-not-not-implies-not-not-Σ-not i

  iii : (Σ a ꞉ ⟨ α ⟩ , ¬ (Σ x ꞉ ⟨ α ⟩ , x ≺⟨ α ⟩ a))
      → (Σ a ꞉ ⟨ α ⟩ , ((x : ⟨ α ⟩) → a ≾⟨ α ⟩ x))
  iii (a , n) = a , not-Σ-implies-Π-not n

  iv : ¬¬ (Σ a ꞉ ⟨ α ⟩ , ((x : ⟨ α ⟩) → a ≾⟨ α ⟩ x))
  iv = ¬¬-functor iii ii

NB-minimal : (α : Ordinal 𝓤) (a : ⟨ α ⟩)
           →  ((x : ⟨ α ⟩) → a ≾⟨ α ⟩ x)
           ↔  ((x : ⟨ α ⟩) → a ≼⟨ α ⟩ x)
NB-minimal α a = f , g
 where
  f : ((x : ⟨ α ⟩) → a ≾⟨ α ⟩ x) → ((x : ⟨ α ⟩) → a ≼⟨ α ⟩ x)
  f h x u l = 𝟘-elim (h u l)

  g : ((x : ⟨ α ⟩) → a ≼⟨ α ⟩ x) → ((x : ⟨ α ⟩) → a ≾⟨ α ⟩ x)
  g k x m = irrefl α x (k x x m)

\end{code}

Added 2nd May 2022.

\begin{code}

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
    A x = Σ n ꞉ ℕ , (g ^ n) x₀ ＝ x

    d : (x : ⟨ α ⟩) → A x → Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × A y
    d x (n , refl) = g x , δ n , succ n , refl

    κ : 𝟘
    κ = no-minimal-is-empty' (underlying-order α) (Well-foundedness α)
         A d (x₀ , 0 , refl)

open import UF.ExcludedMiddle

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

\end{code}

Added 7 November 2022 by Tom de Jong.

A consequence of the above constructions is that a simulation
preserves initial segments in the following sense:

\begin{code}

simulations-preserve-↓ : (α β : Ordinal 𝓤) ((f , _) : α ⊴ β)
                       → ((a : ⟨ α ⟩) → α ↓ a ＝ β ↓ f a)
simulations-preserve-↓ α β 𝕗 a = pr₂ (from-≼ (⊴-gives-≼ α β 𝕗) a)

\end{code}

Added 31 October 2022 by Tom de Jong.

We record the (computational) behaviour of transfinite induction on OO
for use in other constructions.

\begin{code}

transfinite-induction-on-OO-behaviour :
   (P : Ordinal 𝓤 → 𝓥 ̇ )
 → (f : (α : Ordinal 𝓤) → ((a : ⟨ α ⟩) → P (α ↓ a)) → P α)
 → (α : Ordinal 𝓤)
 → transfinite-induction-on-OO P f α
   ＝ f α (λ a → transfinite-induction-on-OO P f (α ↓ a))
transfinite-induction-on-OO-behaviour {𝓤} {𝓥} P f =
 Transfinite-induction-behaviour fe (OO 𝓤) P f'
  where
   f' : (α : Ordinal 𝓤)
      → ((α' : Ordinal 𝓤) → α' ⊲ α → P α')
      → P α
   f' α g = f α (λ a → g (α ↓ a) (a , refl))

transfinite-recursion-on-OO-behaviour :
   (X : 𝓥 ̇ )
 → (f : (α : Ordinal 𝓤) → (⟨ α ⟩ → X) → X)
 → (α : Ordinal 𝓤)
 → transfinite-recursion-on-OO X f α
   ＝ f α (λ a → transfinite-recursion-on-OO X f (α ↓ a))
transfinite-recursion-on-OO-behaviour X f =
 transfinite-induction-on-OO-behaviour (λ _ → X) f

\end{code}

Added 1st June 2023 by Martin Escardo.

\begin{code}

definition-by-transfinite-recursion-on-OO :
   (X : 𝓥 ̇ )
 → (f : (α : Ordinal 𝓤) → (⟨ α ⟩ → X) → X)
 → Σ h ꞉ (Ordinal 𝓤 → X) , (∀ α → h α ＝ f α (λ a → h (α ↓ a)))
definition-by-transfinite-recursion-on-OO X f =
 transfinite-recursion-on-OO X f  ,
 transfinite-recursion-on-OO-behaviour X f

definition-by-transfinite-induction-on-OO :
   (X : Ordinal 𝓤 → 𝓥 ̇ )
 → (f : (α : Ordinal 𝓤) → ((a : ⟨ α ⟩) → X (α ↓ a)) → X α)
 → Σ h ꞉ ((α : Ordinal 𝓤) → X α) , (∀ α → h α ＝ f α (λ a → h (α ↓ a)))
definition-by-transfinite-induction-on-OO X f =
 transfinite-induction-on-OO X f  ,
 transfinite-induction-on-OO-behaviour X f

\end{code}
