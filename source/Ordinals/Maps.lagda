Martin Escardo, August 2018

Various maps of ordinals, including equivalences.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence

module Ordinals.Maps where

open import MLTT.Spartan
open import Notation.CanonicalMap
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Yoneda

\end{code}

Maps of ordinals. A simulation gives a notion of embedding of
ordinals, making them into a poset, as proved below.

\begin{code}

is-order-preserving
 is-monotone
 is-order-reflecting
 is-order-embedding
 is-initial-segment
 is-simulation       : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇

is-order-preserving α β f = (x y : ⟨ α ⟩) → x ≺⟨ α ⟩ y → f x ≺⟨ β ⟩ f y

is-monotone         α β f = (x y : ⟨ α ⟩) → x ≼⟨ α ⟩ y → f x ≼⟨ β ⟩ f y

is-order-reflecting α β f = (x y : ⟨ α ⟩) → f x ≺⟨ β ⟩ f y → x ≺⟨ α ⟩ y

is-order-embedding  α β f = is-order-preserving α β f × is-order-reflecting α β f

is-initial-segment  α β f = (x : ⟨ α ⟩) (y : ⟨ β ⟩)
                          → y ≺⟨ β ⟩ f x
                          → Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ＝ y)

is-simulation       α β f = is-initial-segment α β f × is-order-preserving α β f

simulations-are-order-preserving : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                   (f : ⟨ α ⟩ → ⟨ β ⟩)
                                 → is-simulation α β f
                                 → is-order-preserving α β f
simulations-are-order-preserving α β f (i , p) = p

simulations-are-initial-segments : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                   (f : ⟨ α ⟩ → ⟨ β ⟩)
                                 → is-simulation α β f
                                 → is-initial-segment α β f
simulations-are-initial-segments α β f (i , p) = i

being-order-preserving-is-prop : Fun-Ext
                               → (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                 (f : ⟨ α ⟩ → ⟨ β ⟩)
                               → is-prop (is-order-preserving α β f)
being-order-preserving-is-prop fe α β f =
 Π₃-is-prop fe (λ x y l → Prop-valuedness β (f x) (f y))

being-order-reflecting-is-prop : Fun-Ext
                               → (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                 (f : ⟨ α ⟩ → ⟨ β ⟩)
                               → is-prop (is-order-reflecting α β f)
being-order-reflecting-is-prop fe α β f =
  Π₃-is-prop fe (λ x y l → Prop-valuedness α x y)

being-order-embedding-is-prop : Fun-Ext
                              → (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                (f : ⟨ α ⟩ → ⟨ β ⟩)
                              → is-prop (is-order-embedding α β f)
being-order-embedding-is-prop fe α β f =
 ×-is-prop
  (being-order-preserving-is-prop fe α β f)
  (being-order-reflecting-is-prop fe α β f)

order-reflecting-gives-inverse-order-preserving :
   (α : Ordinal 𝓤) (β : Ordinal 𝓥)
   (f : ⟨ α ⟩ → ⟨ β ⟩)
 → (e : is-equiv f)
 → is-order-reflecting α β f
 → is-order-preserving β α (inverse f e)
order-reflecting-gives-inverse-order-preserving α β f e r x y l = m
 where
  g : ⟨ β ⟩ → ⟨ α ⟩
  g = inverse f e

  l' : f (g x) ≺⟨ β ⟩ f (g y)
  l' = transport₂ (λ x y → x ≺⟨ β ⟩ y)
        ((inverses-are-sections f e x)⁻¹)
        ((inverses-are-sections f e y)⁻¹) l

  s : f (g x) ≺⟨ β ⟩ f (g y) → g x ≺⟨ α ⟩ g y
  s = r (g x) (g y)

  m : g x ≺⟨ α ⟩ g y
  m = s l'

inverse-order-reflecting-gives-order-preserving :
   (α : Ordinal 𝓤) (β : Ordinal 𝓥)
   (f : ⟨ α ⟩ → ⟨ β ⟩)
   (e : is-equiv f)
 → is-order-preserving β α (inverse f e)
 → is-order-reflecting α β f
inverse-order-reflecting-gives-order-preserving α β f e q x y l = r
 where
  g : ⟨ β ⟩ → ⟨ α ⟩
  g = inverse f e

  s : g (f x) ≺⟨ α ⟩ g (f y)
  s = q (f x) (f y) l

  r : x ≺⟨ α ⟩ y
  r = transport₂ (λ x y → x ≺⟨ α ⟩ y)
       (inverses-are-retractions f e x)
       (inverses-are-retractions f e y) s

simulations-are-lc : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                     (f : ⟨ α ⟩ → ⟨ β ⟩)
                   → is-simulation α β f
                   → left-cancellable f
simulations-are-lc α β f (i , p) = γ
 where
  φ : ∀ x y
    → is-accessible (underlying-order α) x
    → is-accessible (underlying-order α) y
    → f x ＝ f y
    → x ＝ y
  φ x y (acc s) (acc t) r = Extensionality α x y g h
   where
    g : (u : ⟨ α ⟩) → u ≺⟨ α ⟩ x → u ≺⟨ α ⟩ y
    g u l = d
     where
      a : f u ≺⟨ β ⟩ f y
      a = transport (λ - → f u ≺⟨ β ⟩ -) r (p u x l)

      b : Σ v ꞉ ⟨ α ⟩ , (v ≺⟨ α ⟩ y) × (f v ＝ f u)
      b = i y (f u) a

      c : u ＝ pr₁ b
      c = φ u (pr₁ b) (s u l) (t (pr₁ b) (pr₁ (pr₂ b))) ((pr₂ (pr₂ b))⁻¹)

      d : u ≺⟨ α ⟩ y
      d = transport (λ - → - ≺⟨ α ⟩ y) (c ⁻¹) (pr₁ (pr₂ b))

    h : (u : ⟨ α ⟩) → u ≺⟨ α ⟩ y → u ≺⟨ α ⟩ x
    h u l = d
     where
      a : f u ≺⟨ β ⟩ f x
      a = transport (λ - → f u ≺⟨ β ⟩ -) (r ⁻¹) (p u y l)

      b : Σ v ꞉ ⟨ α ⟩ , (v ≺⟨ α ⟩ x) × (f v ＝ f u)
      b = i x (f u) a

      c : pr₁ b ＝ u
      c = φ (pr₁ b) u (s (pr₁ b) (pr₁ (pr₂ b))) (t u l) (pr₂ (pr₂ b))

      d : u ≺⟨ α ⟩ x
      d = transport (λ - → - ≺⟨ α ⟩ x) c (pr₁ (pr₂ b))

  γ : left-cancellable f
  γ {x} {y} = φ x y (Well-foundedness α x) (Well-foundedness α y)

simulations-are-embeddings : FunExt
                           → (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                             (f : ⟨ α ⟩ → ⟨ β ⟩)
                           → is-simulation α β f
                           → is-embedding f
simulations-are-embeddings fe α β f s = lc-maps-into-sets-are-embeddings f
                                         (simulations-are-lc α β f s)
                                         (underlying-type-is-set fe β)

being-initial-segment-is-prop : Fun-Ext
                              → (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                (f : ⟨ α ⟩ → ⟨ β ⟩)
                              → is-order-preserving α β f
                              → is-prop (is-initial-segment α β f)
being-initial-segment-is-prop fe α β f p = prop-criterion γ
  where
   γ : is-initial-segment α β f → is-prop (is-initial-segment α β f)
   γ i = Π₃-is-prop fe (λ x z l → φ x z l)
    where
     φ : ∀ x y
       → y ≺⟨ β ⟩ f x
       → is-prop (Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ＝ y))
     φ x y l (x' , (m , r)) (x'' , (m' , r')) = to-Σ-＝ (a , b)
      where
       c : f x' ＝ f x''
       c = r ∙ r' ⁻¹

       j : is-simulation α β f
       j = (i , p)

       a : x' ＝ x''
       a = simulations-are-lc α β f j c

       k : is-prop ((x'' ≺⟨ α ⟩ x) × (f x'' ＝ y))
       k = ×-is-prop
            (Prop-valuedness α x'' x)
            (underlying-type-is-set (λ _ _ → fe) β)

       b : transport (λ - →  (- ≺⟨ α ⟩ x) × (f - ＝ y)) a (m , r) ＝ m' , r'
       b = k _ _

being-simulation-is-prop : Fun-Ext
                         → (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                           (f : ⟨ α ⟩ → ⟨ β ⟩)
                         → is-prop (is-simulation α β f)
being-simulation-is-prop fe α β f =
 ×-prop-criterion
  (being-initial-segment-is-prop fe α β f ,
   (λ _ → being-order-preserving-is-prop fe α β f))

lc-initial-segments-are-order-reflecting : (α β : Ordinal 𝓤)
                                           (f : ⟨ α ⟩ → ⟨ β ⟩)
                                         → is-initial-segment α β f
                                         → left-cancellable f
                                         → is-order-reflecting α β f
lc-initial-segments-are-order-reflecting α β f i c x y l = m
 where
  a : Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ y) × (f x' ＝ f x)
  a = i y (f x) l

  m : x ≺⟨ α ⟩ y
  m = transport (λ - → - ≺⟨ α ⟩ y) (c (pr₂ (pr₂ a))) (pr₁ (pr₂ a))

simulations-are-order-reflecting : (α β : Ordinal 𝓤)
                                   (f : ⟨ α ⟩ → ⟨ β ⟩)
                                 → is-simulation α β f
                                 → is-order-reflecting α β f
simulations-are-order-reflecting α β f (i , p) =
 lc-initial-segments-are-order-reflecting α β f i
  (simulations-are-lc α β f (i , p))

order-embeddings-are-lc : (α β : Ordinal 𝓤) (f : ⟨ α ⟩ → ⟨ β ⟩)
                        → is-order-embedding α β f
                        → left-cancellable f
order-embeddings-are-lc α β f (p , r) {x} {y} s = γ
 where
  a : (u : ⟨ α ⟩) → u ≺⟨ α ⟩ x → u ≺⟨ α ⟩ y
  a u l = r u y j
   where
    i : f u ≺⟨ β ⟩ f x
    i = p u x l

    j : f u ≺⟨ β ⟩ f y
    j = transport (λ - → f u ≺⟨ β ⟩ -) s i

  b : (u : ⟨ α ⟩) → u ≺⟨ α ⟩ y → u ≺⟨ α ⟩ x
  b u l = r u x j
   where
    i : f u ≺⟨ β ⟩ f y
    i = p u y l

    j : f u ≺⟨ β ⟩ f x

    j = transport⁻¹ (λ - → f u ≺⟨ β ⟩ -) s i


  γ : x ＝ y
  γ = Extensionality α x y a b

order-embedings-are-embeddings : FunExt
                               → (α β : Ordinal 𝓤)
                                 (f : ⟨ α ⟩ → ⟨ β ⟩)
                               → is-order-embedding α β f
                               → is-embedding f
order-embedings-are-embeddings fe α β f (p , r) =
  lc-maps-into-sets-are-embeddings f
   (order-embeddings-are-lc α β f (p , r))
   (underlying-type-is-set fe β)

simulations-are-monotone : (α β : Ordinal 𝓤)
                           (f : ⟨ α ⟩ → ⟨ β ⟩)
                         → is-simulation α β f
                         → is-monotone α β f
simulations-are-monotone α β f (i , p) = φ
 where
  φ : (x y : ⟨ α ⟩)
    → ((z : ⟨ α ⟩) → z ≺⟨ α ⟩ x → z ≺⟨ α ⟩ y)
    → (t : ⟨ β ⟩) → t ≺⟨ β ⟩ f x → t ≺⟨ β ⟩ f y
  φ x y ψ t l = transport (λ - → - ≺⟨ β ⟩ f y) b d
   where
    z : ⟨ α ⟩
    z = pr₁ (i x t l)

    a : z ≺⟨ α ⟩ x
    a = pr₁ (pr₂ (i x t l))

    b : f z ＝ t
    b = pr₂ (pr₂ (i x t l))

    c : z ≺⟨ α ⟩ y
    c = ψ z a

    d : f z ≺⟨ β ⟩ f y
    d = p z y c

at-most-one-simulation : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                         (f f' : ⟨ α ⟩ → ⟨ β ⟩)
                       → is-simulation α β f
                       → is-simulation α β f'
                       → f ∼ f'
at-most-one-simulation α β f f' (i , p) (i' , p') x = γ
 where
  φ : ∀ x
    → is-accessible (underlying-order α) x
    → f x ＝ f' x
  φ x (acc u) = Extensionality β (f x) (f' x) a b
   where
    IH : ∀ y → y ≺⟨ α ⟩ x → f y ＝ f' y
    IH y l = φ y (u y l)

    a : (z : ⟨ β ⟩) → z ≺⟨ β ⟩ f x → z ≺⟨ β ⟩ f' x
    a z l = transport (λ - → - ≺⟨ β ⟩ f' x) t m
     where
      s : Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × (f y ＝ z)
      s = i x z l

      y : ⟨ α ⟩
      y = pr₁ s

      m : f' y ≺⟨ β ⟩ f' x
      m = p' y x (pr₁ (pr₂ s))

      t : f' y ＝ z
      t = f' y  ＝⟨ (IH y (pr₁ (pr₂ s)))⁻¹ ⟩
          f y   ＝⟨ pr₂ (pr₂ s) ⟩
          z     ∎

    b : (z : ⟨ β ⟩) → z ≺⟨ β ⟩ f' x → z ≺⟨ β ⟩ f x
    b z l = transport (λ - → - ≺⟨ β ⟩ f x) t m
     where
      s : Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × (f' y ＝ z)
      s = i' x z l

      y : ⟨ α ⟩
      y = pr₁ s

      m : f y ≺⟨ β ⟩ f x
      m = p y x (pr₁ (pr₂ s))

      t : f y ＝ z
      t = f y  ＝⟨ IH y (pr₁ (pr₂ s)) ⟩
          f' y ＝⟨ pr₂ (pr₂ s) ⟩
          z    ∎

  γ : f x ＝ f' x
  γ = φ x (Well-foundedness α x)

\end{code}

Added 29th March 2022.

Simulations preserve least elements.

\begin{code}

initial-segments-preserve-least :
   (α : Ordinal 𝓤) (β : Ordinal 𝓥)
   (x : ⟨ α ⟩) (y : ⟨ β ⟩)
   (f : ⟨ α ⟩ → ⟨ β ⟩)
 → is-initial-segment α β f
 → is-least α x
 → is-least β y
 → f x ＝ y
initial-segments-preserve-least α β x y f i m n = c
 where
  a : f x ≼⟨ β ⟩ y
  a u l = IV
   where
    x' : ⟨ α ⟩
    x' = pr₁ (i x u l)

    I : x' ≺⟨ α ⟩ x
    I = pr₁ (pr₂ (i x u l))

    II : x ≼⟨ α ⟩ x'
    II = m x'

    III : x' ≺⟨ α ⟩ x'
    III = II x' I

    IV : u ≺⟨ β ⟩ y
    IV = 𝟘-elim (irrefl α x' III)

  b : y ≼⟨ β ⟩ f x
  b = n (f x)

  c : f x ＝ y
  c = Antisymmetry β (f x) y a b

simulations-preserve-least : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                             (x : ⟨ α ⟩) (y : ⟨ β ⟩)
                             (f : ⟨ α ⟩ → ⟨ β ⟩)
                           → is-simulation α β f
                           → is-least α x
                           → is-least β y
                           → f x ＝ y
simulations-preserve-least α β x y f (i , _) =
 initial-segments-preserve-least α β x y f i

\end{code}

Added in March 2022 by Tom de Jong:

Notice that we defined "is-initial-segment" using Σ (rather than ∃).
This is fine, because if f is a simulation from α to β, then for
every x : ⟨ α ⟩ and y : ⟨ β ⟩ with y ≺⟨ β ⟩ f x, the type
(Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ＝ y)) is a proposition. It
follows (see the proof above) that being a simulation is property.

However, for some purposes, notably for constructing suprema of
ordinals in OrdinalSupOfOrdinals.lagda, it is useful to formulate the
notion of initial segment and the notion of simulation using ∃, rather
than Σ.

Using the techniques that were used above to prove that being a simulation is
property, we show the definition of simulation with ∃ to be equivalent to the
original one.

\begin{code}

open import UF.PropTrunc

module _ (pt : propositional-truncations-exist)
         (fe : FunExt)
       where

 open PropositionalTruncation pt

 is-initial-segment' : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇
 is-initial-segment' α β f = (x : ⟨ α ⟩) (y : ⟨ β ⟩)
                           → y ≺⟨ β ⟩ f x
                           → ∃ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ＝ y)

 is-simulation' : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇
 is-simulation' α β f = is-initial-segment' α β f × is-order-preserving α β f

 simulations-are-lc' : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                       (f : ⟨ α ⟩ → ⟨ β ⟩)
                     → is-simulation' α β f
                     → left-cancellable f
 simulations-are-lc' α β f (i , p) = γ
  where
   φ : ∀ x y
     → is-accessible (underlying-order α) x
     → is-accessible (underlying-order α) y
     → f x ＝ f y
     → x ＝ y
   φ x y (acc s) (acc t) r = Extensionality α x y g h
    where
     g : (u : ⟨ α ⟩) → u ≺⟨ α ⟩ x → u ≺⟨ α ⟩ y
     g u l = ∥∥-rec (Prop-valuedness α u y) b (i y (f u) a)
      where
       a : f u ≺⟨ β ⟩ f y
       a = transport (λ - → f u ≺⟨ β ⟩ -) r (p u x l)

       b : (Σ v ꞉ ⟨ α ⟩ , (v ≺⟨ α ⟩ y) × (f v ＝ f u))
         → u ≺⟨ α ⟩ y
       b (v , k , e) = transport (λ - → - ≺⟨ α ⟩ y) (c ⁻¹) k
        where
         c : u ＝ v
         c = φ u v (s u l) (t v k) (e ⁻¹)

     h : (u : ⟨ α ⟩) → u ≺⟨ α ⟩ y → u ≺⟨ α ⟩ x
     h u l = ∥∥-rec (Prop-valuedness α u x) b (i x (f u) a)
      where
       a : f u ≺⟨ β ⟩ f x
       a = transport (λ - → f u ≺⟨ β ⟩ -) (r ⁻¹) (p u y l)

       b : (Σ v ꞉ ⟨ α ⟩ , (v ≺⟨ α ⟩ x) × (f v ＝ f u))
         → u ≺⟨ α ⟩ x
       b (v , k , e) = transport (λ - → - ≺⟨ α ⟩ x) c k
        where
         c : v ＝ u
         c = φ v u (s v k) (t u l) e

   γ : left-cancellable f
   γ {x} {y} = φ x y (Well-foundedness α x) (Well-foundedness α y)

 simulation-prime : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                    (f : ⟨ α ⟩ → ⟨ β ⟩)
                  → is-simulation α β f
                  → is-simulation' α β f
 simulation-prime α β f (i , p) = (j , p)
  where
   j : is-initial-segment' α β f
   j x y l = ∣ i x y l ∣

 simulation-unprime : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                      (f : ⟨ α ⟩ → ⟨ β ⟩)
                    → is-simulation' α β f
                    → is-simulation α β f
 simulation-unprime α β f (i , p) = (j , p)
  where
   j : is-initial-segment α β f
   j x y l = ∥∥-rec prp id (i x y l)
    where
     prp : is-prop (Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ＝ y))
     prp (z , l , e) (z' , l' , e') = to-subtype-＝ ⦅1⦆ ⦅2⦆
      where
       ⦅1⦆ : (x' : ⟨ α ⟩) → is-prop ((x' ≺⟨ α ⟩ x) × (f x' ＝ y))
       ⦅1⦆ x' = ×-is-prop (Prop-valuedness α x' x) (underlying-type-is-set fe β)

       ⦅2⦆ : z ＝ z'
       ⦅2⦆ = simulations-are-lc' α β f (i , p) (e ∙ e' ⁻¹)
\end{code}
