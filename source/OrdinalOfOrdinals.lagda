Martin Escardo, August 2018

The ordinal of ordinals. Based on the HoTT Book, with a few
modifications in some of the definitions and arguments.

This is an example where we are studying sets only, but the
univalence axiom is needed.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-Univalence

module OrdinalOfOrdinals
       (ua : Univalence)
       where

open import SpartanMLTT
open import OrdinalNotions
open import OrdinalsType
open import CanonicalMapNotation

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Embeddings
open import UF-FunExt
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-UA-FunExt
open import UF-Yoneda
open import UF-EquivalenceExamples

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

\end{code}

Maps of ordinals. A simulation gives a notion of embedding of
ordinals, making them into a poset, as proved below.

\begin{code}

is-monotone
 is-order-embedding
 is-initial-segment
 is-simulation       : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇

is-monotone         α β f = (x y : ⟨ α ⟩) → x ≼⟨ α ⟩ y → f x ≼⟨ β ⟩ f y

is-order-embedding  α β f = is-order-preserving α β f × is-order-reflecting α β f

is-initial-segment  α β f = (x : ⟨ α ⟩) (y : ⟨ β ⟩)
                          → y ≺⟨ β ⟩ f x
                          → Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ≡ y)

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


order-equivs-are-simulations : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                               (f : ⟨ α ⟩ → ⟨ β ⟩)
                             → is-order-equiv α β f
                             → is-simulation α β f
order-equivs-are-simulations α β f (p , e , q) = h (equivs-are-qinvs f e) q , p
 where
  h : (d : qinv f)
    → is-order-preserving β α (pr₁ d)
    → is-initial-segment α β f
  h (g , ε , η) q x y l = g y , r , η y
   where
    m : g y ≺⟨ α ⟩ g (f x)
    m = q y (f x) l

    r : g y ≺⟨ α ⟩ x
    r = transport (λ - → g y ≺⟨ α ⟩ -) (ε x) m

order-preservation-is-prop : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (f : ⟨ α ⟩ → ⟨ β ⟩)
                           → is-prop (is-order-preserving α β f)
order-preservation-is-prop {𝓤} {𝓥} α β f =
  Π₃-is-prop fe' (λ x y l → Prop-valuedness β (f x) (f y))

order-reflection-is-prop : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (f : ⟨ α ⟩ → ⟨ β ⟩)
                           → is-prop (is-order-reflecting α β f)
order-reflection-is-prop {𝓤} {𝓥} α β f =
  Π₃-is-prop fe' (λ x y l → Prop-valuedness α x y)

being-order-embedding-is-prop : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                (f : ⟨ α ⟩ → ⟨ β ⟩)
                              → is-prop (is-order-embedding α β f)
being-order-embedding-is-prop α β f = ×-is-prop
                                       (order-preservation-is-prop α β f)
                                       (order-reflection-is-prop α β f)

being-order-equiv-is-prop : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                            (f : ⟨ α ⟩ → ⟨ β ⟩)
                          → is-prop (is-order-equiv α β f)
being-order-equiv-is-prop α β f = ×-is-prop
                                   (order-preservation-is-prop α β f)
                                   (Σ-is-prop
                                      (being-equiv-is-prop fe f)
                                      (λ e → order-preservation-is-prop β α
                                                (inverse f e)))

simulations-are-lc : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                     (f : ⟨ α ⟩ → ⟨ β ⟩)
                   → is-simulation α β f
                   → left-cancellable f
simulations-are-lc α β f (i , p) = γ
 where
  φ : ∀ x y
    → is-accessible (underlying-order α) x
    → is-accessible (underlying-order α) y
    → f x ≡ f y
    → x ≡ y
  φ x y (next x s) (next y t) r = Extensionality α x y g h
   where
    g : (u : ⟨ α ⟩) → u ≺⟨ α ⟩ x → u ≺⟨ α ⟩ y
    g u l = d
     where
      a : f u ≺⟨ β ⟩ f y
      a = transport (λ - → f u ≺⟨ β ⟩ -) r (p u x l)

      b : Σ v ꞉ ⟨ α ⟩ , (v ≺⟨ α ⟩ y) × (f v ≡ f u)
      b = i y (f u) a

      c : u ≡ pr₁ b
      c = φ u (pr₁ b) (s u l) (t (pr₁ b) (pr₁ (pr₂ b))) ((pr₂ (pr₂ b))⁻¹)

      d : u ≺⟨ α ⟩ y
      d = transport (λ - → - ≺⟨ α ⟩ y) (c ⁻¹) (pr₁ (pr₂ b))

    h : (u : ⟨ α ⟩) → u ≺⟨ α ⟩ y → u ≺⟨ α ⟩ x
    h u l = d
     where
      a : f u ≺⟨ β ⟩ f x
      a = transport (λ - → f u ≺⟨ β ⟩ -) (r ⁻¹) (p u y l)

      b : Σ v ꞉ ⟨ α ⟩ , (v ≺⟨ α ⟩ x) × (f v ≡ f u)
      b = i x (f u) a

      c : pr₁ b ≡ u
      c = φ (pr₁ b) u (s (pr₁ b) (pr₁ (pr₂ b))) (t u l) (pr₂ (pr₂ b))

      d : u ≺⟨ α ⟩ x
      d = transport (λ - → - ≺⟨ α ⟩ x) c (pr₁ (pr₂ b))

  γ : left-cancellable f
  γ {x} {y} = φ x y (Well-foundedness α x) (Well-foundedness α y)

being-initial-segment-is-prop : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                (f : ⟨ α ⟩ → ⟨ β ⟩)
                              → is-order-preserving α β f
                              → is-prop (is-initial-segment α β f)
being-initial-segment-is-prop {𝓤} {𝓥} α β f p = prop-criterion γ
  where
   γ : is-initial-segment α β f → is-prop (is-initial-segment α β f)
   γ i = Π₃-is-prop fe' (λ x z l → φ x z l)
    where
     φ : ∀ x y → y ≺⟨ β ⟩ f x → is-prop (Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ≡ y))
     φ x y l (x' , (m , r)) (x'' , (m' , r')) = to-Σ-≡ (a , b)
      where
       c : f x' ≡ f x''
       c = r ∙ r' ⁻¹

       j : is-simulation α β f
       j = (i , p)

       a : x' ≡ x''
       a = simulations-are-lc α β f j c

       k : is-prop ((x'' ≺⟨ α ⟩ x) × (f x'' ≡ y))
       k = ×-is-prop
            (Prop-valuedness α x'' x)
            (underlying-type-is-set fe β)

       b : transport (λ - →  (- ≺⟨ α ⟩ x) × (f - ≡ y)) a (m , r) ≡ m' , r'
       b = k _ _

\end{code}

The simulations make the ordinals into a poset:

\begin{code}

being-simulation-is-prop : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                           (f : ⟨ α ⟩ → ⟨ β ⟩)
                         → is-prop (is-simulation α β f)
being-simulation-is-prop α β f = ×-prop-criterion
                                  (being-initial-segment-is-prop α β f ,
                                   (λ _ → order-preservation-is-prop α β f))

at-most-one-simulation : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                         (f f' : ⟨ α ⟩ → ⟨ β ⟩)
                       → is-simulation α β f
                       → is-simulation α β f'
                       → f ∼ f'
at-most-one-simulation α β f f' (i , p) (i' , p') x = γ
 where
  φ : ∀ x
    → is-accessible (underlying-order α) x
    → f x ≡ f' x
  φ x (next x u) = Extensionality β (f x) (f' x) a b
   where
    IH : ∀ y → y ≺⟨ α ⟩ x → f y ≡ f' y
    IH y l = φ y (u y l)

    a : (z : ⟨ β ⟩) → z ≺⟨ β ⟩ f x → z ≺⟨ β ⟩ f' x
    a z l = transport (λ - → - ≺⟨ β ⟩ f' x) t m
     where
      s : Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × (f y ≡ z)
      s = i x z l

      y : ⟨ α ⟩
      y = pr₁ s

      m : f' y ≺⟨ β ⟩ f' x
      m = p' y x (pr₁ (pr₂ s))

      t : f' y ≡ z
      t = f' y  ≡⟨ (IH y (pr₁ (pr₂ s)))⁻¹ ⟩
          f y   ≡⟨ pr₂ (pr₂ s) ⟩
          z     ∎

    b : (z : ⟨ β ⟩) → z ≺⟨ β ⟩ f' x → z ≺⟨ β ⟩ f x
    b z l = transport (λ - → - ≺⟨ β ⟩ f x) t m
     where
      s : Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × (f' y ≡ z)
      s = i' x z l

      y : ⟨ α ⟩
      y = pr₁ s

      m : f y ≺⟨ β ⟩ f x
      m = p y x (pr₁ (pr₂ s))

      t : f y ≡ z
      t = f y  ≡⟨ IH y (pr₁ (pr₂ s)) ⟩
          f' y ≡⟨ pr₂ (pr₂ s) ⟩
          z    ∎

  γ : f x ≡ f' x
  γ = φ x (Well-foundedness α x)

_⊴_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
α ⊴ β = Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-simulation α β f

⊴-is-prop-valued : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → is-prop (α ⊴ β)
⊴-is-prop-valued {𝓤} {𝓥} α β (f , s) (g , t) =
  to-subtype-≡ (being-simulation-is-prop α β)
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
    → Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (g (f x') ≡ z)
  k x z l = pr₁ b , pr₁ (pr₂ b) , (ap g (pr₂ (pr₂ b)) ∙ pr₂ (pr₂ a))
   where
    a : Σ y ꞉ ⟨ β ⟩ , (y ≺⟨ β ⟩ f x) × (g y ≡ z)
    a = j (f x) z l

    y : ⟨ β ⟩
    y = pr₁ a

    b : Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ≡ y)
    b = i x y (pr₁ (pr₂ a))

≃ₒ-gives-≃ : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
           → α ≃ₒ β → ⟨ α ⟩ ≃ ⟨ β ⟩
≃ₒ-gives-≃ α β (f , p , e , q) = (f , e)

≃ₒ-is-prop-valued : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                  → is-prop (α ≃ₒ β)
≃ₒ-is-prop-valued α β (f , p , e , q) (f' , p' , e' , q')  = γ
  where
   r : f ∼ f'
   r = at-most-one-simulation α β f f'
        (order-equivs-are-simulations α β f  (p  , e ,  q ))
        (order-equivs-are-simulations α β f' (p' , e' , q'))

   γ : (f , p , e , q) ≡ (f' , p' , e' , q')
   γ = to-subtype-≡
         (being-order-equiv-is-prop α β)
         (dfunext fe' r)

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

  η : (y : ⟨ β ⟩) → f (g y) ≡ y
  η = at-most-one-simulation β β (f ∘ g) id ηs (pr₂ (⊴-refl β))

  εs : is-simulation α α (g ∘ f)
  εs = pr₂ (⊴-trans α β α (f , s) (g , t))

  ε : (x : ⟨ α ⟩) → g (f x) ≡ x
  ε = at-most-one-simulation α α (g ∘ f) id εs (pr₂ (⊴-refl α))

  γ : α ≃ₒ β
  γ =  f , pr₂ s , qinvs-are-equivs f (g , ε , η) , pr₂ t

idtoeqₒ : (α β : Ordinal 𝓤) → α ≡ β → α ≃ₒ β
idtoeqₒ α α refl = ≃ₒ-refl α

eqtoidₒ : (α β : Ordinal 𝓤) → α ≃ₒ β → α ≡ β
eqtoidₒ {𝓤} α β (f , p , e , q) = γ
 where
  A : (Y : 𝓤 ̇ ) → ⟨ α ⟩ ≃ Y → 𝓤 ⁺ ̇
  A Y e = (σ : OrdinalStructure Y)
        → is-order-preserving α (Y , σ) ⌜ e ⌝
        → is-order-preserving (Y , σ) α ⌜ e ⌝⁻¹
        → α ≡ (Y , σ)

  a : A ⟨ α ⟩ (≃-refl ⟨ α ⟩)
  a σ φ ψ = g
   where
    b : ∀ x x' → (x ≺⟨ α ⟩ x') ≡ (x ≺⟨ ⟨ α ⟩ , σ ⟩ x')
    b x x' = univalence-gives-propext (ua 𝓤)
              (Prop-valuedness α x x')
              (Prop-valuedness (⟨ α ⟩ , σ) x x')
              (φ x x')
              (ψ x x')

    c : underlying-order α ≡ underlying-order (⟨ α ⟩ , σ)
    c = dfunext fe' (λ x → dfunext fe' (b x))

    d : structure α ≡ σ
    d = pr₁-lc (λ {_<_} → being-well-order-is-prop _<_ fe) c

    g : α ≡ (⟨ α ⟩ , σ)
    g = to-Σ-≡' d

  γ : α ≡ β
  γ = JEq (ua 𝓤) ⟨ α ⟩ A a ⟨ β ⟩ (f , e) (structure β) p q

UAₒ : (α β : Ordinal 𝓤) → is-equiv (idtoeqₒ α β)
UAₒ {𝓤} α = nats-with-sections-are-equivs α
             (idtoeqₒ α)
             (λ β → eqtoidₒ α β , η β)
 where
  η : (β : Ordinal 𝓤) (e : α ≃ₒ β)
    → idtoeqₒ α β (eqtoidₒ α β e) ≡ e
  η β e = ≃ₒ-is-prop-valued α β (idtoeqₒ α β (eqtoidₒ α β e)) e

the-type-of-ordinals-is-a-set : is-set (Ordinal 𝓤)
the-type-of-ordinals-is-a-set {𝓤} {α} {β} = equiv-to-prop
                                              (idtoeqₒ α β , UAₒ α β)
                                              (≃ₒ-is-prop-valued α β)

UAₒ-≃ : (α β : Ordinal 𝓤) → (α ≡ β) ≃ (α ≃ₒ β)
UAₒ-≃ α β = idtoeqₒ α β , UAₒ α β

\end{code}

One of the many applications of the univalence axiom is to manufacture
examples of types which are not sets. Here we have instead used it to
prove that a certain type is a set.

A corollary of the above is that the ordinal order _⊴_ is
antisymmetric.

\begin{code}

⊴-antisym : (α β : Ordinal 𝓤)
          → α ⊴ β
          → β ⊴ α
          → α ≡ β
⊴-antisym α β l m = eqtoidₒ α β (bisimilarity-gives-ordinal-equiv α β l m)

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
    f : ∀ x → is-accessible (underlying-order α) x → ∀ l → is-accessible _<_ (x , l)
    f x (next x s) l = next (x , l) (λ σ m → f (pr₁ σ) (s (pr₁ σ) m) (pr₂ σ))

  e : is-extensional _<_
  e (x , l) (y , m) f g =
    to-subtype-≡
      (λ z → Prop-valuedness α z a)
      (Extensionality α x y
        (λ u n → f (u , Transitivity α u x a n l) n)
        (λ u n → g (u , Transitivity α u y a n m) n))

  t : is-transitive _<_
  t (x , _) (y , _) (z , _) = Transitivity α x y z

segment-inclusion : (α : Ordinal 𝓤) (a : ⟨ α ⟩)
                  → ⟨ α ↓ a ⟩ → ⟨ α ⟩
segment-inclusion α a = pr₁

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
       → (α ↓ a) ⊴ (α ↓ b ) → a ≼⟨ α ⟩ b
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
  m = pr₂ (f (u , l))

  q : u ≡ v
  q = h (u , l)

  n : u ≺⟨ α ⟩ b
  n = transport⁻¹ (λ - → - ≺⟨ α ⟩ b) q m

↓-lc : (α : Ordinal 𝓤) (a b : ⟨ α ⟩)
     → α ↓ a ≡ α ↓ b → a ≡ b
↓-lc α a b p =
 Extensionality α a b
  (↓-⊴-lc α a b (transport      (λ - → (α ↓ a) ⊴ -) p (⊴-refl (α ↓ a))))
  (↓-⊴-lc α b a (transport⁻¹ (λ - → (α ↓ b) ⊴ -) p (⊴-refl (α ↓ b))))

\end{code}

We are now ready to make the type of ordinals into an ordinal.

\begin{code}

_⊲_ : Ordinal 𝓤 → Ordinal 𝓤 → 𝓤 ⁺ ̇
α ⊲ β = Σ b ꞉ ⟨ β ⟩ , α ≡ (β ↓ b)

⊲-is-prop-valued : (α β : Ordinal 𝓤) → is-prop (α ⊲ β)
⊲-is-prop-valued {𝓤} α β (b , p) (b' , p') = γ
 where
  q : (β ↓ b) ≡ (β ↓ b')
  q = (β ↓ b)  ≡⟨ p ⁻¹ ⟩
       α       ≡⟨ p' ⟩
      (β ↓ b') ∎

  r : b ≡ b'
  r = ↓-lc β b b' q

  γ : (b , p) ≡ (b' , p')
  γ = to-subtype-≡ (λ x → the-type-of-ordinals-is-a-set) r

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
⊲-is-equivalent-to-⊲⁻ α β = Σ-cong (λ (b : ⟨ β ⟩) → UAₒ-≃ α (β ↓ b))

\end{code}

Back to the past.

A lower set of a lower set is a lower set:

\begin{code}

iterated-↓ : (α : Ordinal 𝓤) (a b : ⟨ α ⟩) (l : b ≺⟨ α ⟩ a)
           → ((α ↓ a ) ↓ (b , l)) ≡ (α ↓ b)
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
      → Σ w' ꞉ ⟨ (α ↓ b) ↓ (u , l) ⟩ , (w' ≺⟨ (α ↓ b) ↓ (u , l) ⟩ w) × (f w' ≡ t)
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
      → Σ t' ꞉ ⟨ α ↓ u ⟩ , (t' ≺⟨ α ↓ u ⟩ t) × (f t' ≡ w)
    i (x , n) ((x' , m') , n') o = (x' , n') , (o , r)
     where
      r : ((x' , Transitivity α x' u b n' l) , n') ≡ (x' , m') , n'
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
  have : type-of l ≡ (u ≺⟨ α ⟩ b)
  have = refl

  q : (α ↓ a) ≡ (α ↓ u)
  q = (α ↓ a)             ≡⟨ p ⟩
      ((α ↓ b) ↓ (u , l)) ≡⟨ iterated-↓ α b u l ⟩
      (α ↓ u)             ∎

  r : a ≡ u
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
  f a (next .a s) = next (α ↓ a) g
   where
    IH : (b : ⟨ α ⟩) → b ≺⟨ α ⟩ a → is-accessible _⊲_ (α ↓ b)
    IH b l = f b (s b l)

    g : (β : Ordinal 𝓤) → β ⊲ (α ↓ a) → is-accessible _⊲_ β
    g β ((b , l) , p) = transport⁻¹ (is-accessible _⊲_) q (IH b l)
     where
      q : β ≡ (α ↓ b)
      q = p ∙ iterated-↓ α a b l

⊲-is-well-founded : is-well-founded (_⊲_ {𝓤})
⊲-is-well-founded {𝓤} α = next α g
 where
  g : (β : Ordinal 𝓤) → β ⊲ α → is-accessible _⊲_ β
  g β (b , p) = transport⁻¹ (is-accessible _⊲_) p (↓-accessible α b)

⊲-is-extensional : is-extensional (_⊲_ {𝓤})
⊲-is-extensional α β f g = ⊴-antisym α β
                           ((λ x → pr₁ (φ x)) , i , p)
                           ((λ y → pr₁ (γ y)) , j , q)
 where
  φ : (x : ⟨ α ⟩) → Σ y ꞉ ⟨ β ⟩ , α ↓ x ≡ β ↓ y
  φ x = f (α ↓ x) (x , refl)

  γ : (y : ⟨ β ⟩) → Σ x ꞉ ⟨ α ⟩ , β ↓ y ≡ α ↓ x
  γ y = g (β ↓ y) (y , refl)

  η : (x : ⟨ α ⟩) → pr₁ (γ (pr₁ (φ x))) ≡ x
  η x = (↓-lc α x (pr₁ (γ (pr₁ (φ x)))) a)⁻¹
   where
    a : (α ↓ x) ≡ (α ↓ pr₁ (γ (pr₁ (φ x))))
    a = pr₂ (φ x) ∙ pr₂ (γ (pr₁ (φ x)))

  ε : (y : ⟨ β ⟩) → pr₁ (φ (pr₁ (γ y))) ≡ y
  ε y = (↓-lc β y (pr₁ (φ (pr₁ (γ y)))) a)⁻¹
   where
    a : (β ↓ y) ≡ (β ↓ pr₁ (φ (pr₁ (γ y))))
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
  t : (q : β ≡ (φ ↓ b)) → (β ↓ a) ≡ ((φ ↓ b) ↓ transport ⟨_⟩ q a)
  t refl = refl

  u : ⟨ φ ↓ b ⟩
  u = transport (⟨_⟩) q a

  c : ⟨ φ ⟩
  c = pr₁ u

  l : c ≺⟨ φ ⟩ b
  l = pr₂ u

  r : α ≡ (φ ↓ c)
  r = α             ≡⟨ p ⟩
      (β ↓ a)       ≡⟨ t q ⟩
      ((φ ↓ b) ↓ u) ≡⟨ iterated-↓ φ b c l ⟩
      (φ ↓ c)       ∎

  γ : Σ c ꞉ ⟨ φ ⟩ , α ≡ (φ ↓ c)
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

  η : (σ : ⟨ OO 𝓤 ↓ α ⟩) → f (g σ) ≡ σ
  η (.(α ↓ x) , x , refl) = refl

  ε : (x : ⟨ α ⟩) → g (f x) ≡ x
  ε x = refl

  q : is-order-preserving (OO 𝓤 ↓ α) α g
  q (.(α ↓ x) , x , refl) (.(α ↓ x') , x' , refl) = ↓-reflects-order α x x'

\end{code}

Here are some additional observations about the various maps of
ordinals:

\begin{code}

lc-initial-segments-are-order-reflecting : (α β : Ordinal 𝓤)
                                           (f : ⟨ α ⟩ → ⟨ β ⟩)
                                         → is-initial-segment α β f
                                         → left-cancellable f
                                         → is-order-reflecting α β f
lc-initial-segments-are-order-reflecting α β f i c x y l = m
 where
  a : Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ y) × (f x' ≡ f x)
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


  γ : x ≡ y
  γ = Extensionality α x y a b

order-embedings-are-embeddings : (α β : Ordinal 𝓤) (f : ⟨ α ⟩ → ⟨ β ⟩)
                               → is-order-embedding α β f
                               → is-embedding f
order-embedings-are-embeddings α β f (p , r) =
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

    b : f z ≡ t
    b = pr₂ (pr₂ (i x t l))

    c : z ≺⟨ α ⟩ y
    c = ψ z a

    d : f z ≺⟨ β ⟩ f y
    d = p z y c

\end{code}

Example. Classically, the ordinals ω +ₒ 𝟙ₒ and ℕ∞ₒ are equal.
Constructively, we have (ω +ₒ 𝟙ₒ) ⊴ ℕ∞ₒ, but the inequality in the
other direction is equivalent to LPO.

\begin{code}

module ℕ∞-in-Ord where

 open import LPO fe
 open import OrdinalArithmetic fe
 open import GenericConvergentSequence
 open import NaturalsOrder

 fact : (ω +ₒ 𝟙ₒ) ⊴ ℕ∞ₒ
 fact = ι𝟙 , i , p
  where
   i : (x : ⟨ ω +ₒ 𝟙ₒ ⟩) (y : ⟨ ℕ∞ₒ ⟩)
     → y ≺⟨ ℕ∞ₒ ⟩ ι𝟙 x
     → Σ x' ꞉ ⟨ ω +ₒ 𝟙ₒ ⟩ , (x' ≺⟨ ω +ₒ 𝟙ₒ ⟩ x) × (ι𝟙 x' ≡ y)
   i (inl m) y (n , r , l) = inl n , ⊏-gives-< n m l , (r ⁻¹)
   i (inr *) y (n , r , l) = inl n , * , (r ⁻¹)

   p : (x y : ⟨ ω +ₒ 𝟙ₒ ⟩)
     → x ≺⟨ ω +ₒ 𝟙ₒ ⟩ y
     → ι𝟙 x ≺⟨ ℕ∞ₒ ⟩ ι𝟙 y
   p (inl n) (inl m) l = ι-order-preserving n m l
   p (inl n) (inr *) * = ∞-≺-largest n
   p (inr *) (inl m) l = 𝟘-elim l
   p (inr *) (inr *) l = 𝟘-elim l

 converse-fails-constructively : ℕ∞ₒ ⊴ (ω +ₒ 𝟙ₒ) → LPO
 converse-fails-constructively l = γ
  where
   b : (ω +ₒ 𝟙ₒ) ≃ₒ ℕ∞ₒ
   b = bisimilarity-gives-ordinal-equiv (ω +ₒ 𝟙ₒ) ℕ∞ₒ fact l

   e : is-equiv ι𝟙
   e = pr₂ (≃ₒ-gives-≃ (ω +ₒ 𝟙ₒ) ℕ∞ₒ b)

   γ : LPO
   γ = ι𝟙-has-section-gives-LPO (equivs-have-sections ι𝟙 e)

 converse-fails-constructively-converse : LPO → ℕ∞ₒ ⊴ (ω +ₒ 𝟙ₒ)
 converse-fails-constructively-converse lpo = (λ x → ι𝟙-inverse x (lpo x)) ,
                                              (λ x → i x (lpo x)) ,
                                              (λ x y → p x y (lpo x) (lpo y))
  where
   ι𝟙-inverse-inl : (u : ℕ∞) (d : decidable (Σ n ꞉ ℕ , u ≡ ι n))
                      → (m : ℕ) → u ≡ ι m → ι𝟙-inverse u d ≡ inl m
   ι𝟙-inverse-inl . (ι n) (inl (n , refl)) m q = ap inl (ℕ-to-ℕ∞-lc q)
   ι𝟙-inverse-inl u          (inr g)          m q = 𝟘-elim (g (m , q))

   i : (x : ℕ∞) (d : decidable (Σ n ꞉ ℕ , x ≡ ι n)) (y : ℕ + 𝟙)
     → y ≺⟨ ω +ₒ 𝟙ₒ ⟩ ι𝟙-inverse x d
     → Σ x' ꞉ ℕ∞ , (x' ≺⟨ ℕ∞ₒ ⟩ x) × (ι𝟙-inverse x' (lpo x') ≡ y)
   i .(ι n) (inl (n , refl)) (inl m) l =
     ι m ,
     ι-order-preserving m n l ,
     ι𝟙-inverse-inl (ι m) (lpo (ι m)) m refl
   i .(ι n) (inl (n , refl)) (inr *) l = 𝟘-elim l
   i x (inr g) (inl n) * =
     ι n ,
     transport (underlying-order ℕ∞ₒ (ι n))
               ((not-finite-is-∞ (fe 𝓤₀ 𝓤₀) (curry g)) ⁻¹)
               (∞-≺-largest n) ,
     ι𝟙-inverse-inl (ι n) (lpo (ι n)) n refl
   i x (inr g) (inr *) l = 𝟘-elim l

   p : (x y : ℕ∞)  (d : decidable (Σ n ꞉ ℕ , x ≡ ι n)) (e : decidable (Σ m ꞉ ℕ , y ≡ ι m))
     →  x ≺⟨ ℕ∞ₒ ⟩ y
     → ι𝟙-inverse x d ≺⟨ ω +ₒ 𝟙ₒ ⟩ ι𝟙-inverse y e
   p .(ι n) .(ι m) (inl (n , refl)) (inl (m , refl)) (k , r , l) =
    transport⁻¹ (λ - → - <ℕ m) (ℕ-to-ℕ∞-lc r) (⊏-gives-< k m l)
   p .(ι n) y (inl (n , refl)) (inr f) l = ⋆
   p x y (inr f) e (k , r , l) =
    𝟘-elim (∞-is-not-finite k ((not-finite-is-∞ (fe 𝓤₀ 𝓤₀) (curry f))⁻¹ ∙ r))

 corollary₁ : LPO → ℕ∞ₒ ≃ₒ (ω +ₒ 𝟙ₒ)
 corollary₁ lpo = bisimilarity-gives-ordinal-equiv
                   ℕ∞ₒ (ω +ₒ 𝟙ₒ)
                   (converse-fails-constructively-converse lpo) fact

 corollary₂ : LPO → ℕ∞ ≃ (ℕ + 𝟙)
 corollary₂ lpo = ≃ₒ-gives-≃ ℕ∞ₒ (ω +ₒ 𝟙ₒ) (corollary₁ lpo)

 corollary₃ : LPO → ℕ∞ₒ ≡ (ω +ₒ 𝟙ₒ)
 corollary₃ lpo = eqtoidₒ ℕ∞ₒ (ω +ₒ 𝟙ₒ) (corollary₁ lpo)

 corollary₄ : LPO → ℕ∞ ≡ (ℕ + 𝟙)
 corollary₄ lpo = eqtoid (ua 𝓤₀) ℕ∞ (ℕ + 𝟙) (corollary₂ lpo)

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
     → ((a : ⟨ α ⟩) → (α ↓ a) ⊲ β)
     → α ≼ β
to-≼ {𝓤} {α} {β} ϕ α' (a , p) = m
 where
  l : (α ↓ a) ⊲ β
  l = ϕ a

  m : α' ⊲ β
  m = transport (_⊲ β) (p ⁻¹) l

from-≼ : {α β : Ordinal 𝓤}
       → α ≼ β
       → (a : ⟨ α ⟩) → (α ↓ a) ⊲ β
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
    σ : Σ x ꞉ ⟨ α ⟩ , (x ≺⟨ α ⟩ a) × (f x ≡ y)
    σ = f-is-initial-segment a y m

  η : h ∘ g ∼ id
  η (x , l) = to-subtype-≡ (λ - → Prop-valuedness α - a) r
   where
    σ : Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ a) × (f x' ≡ f x)
    σ = f-is-initial-segment a (f x) (f-is-order-preserving x a l)

    x' = pr₁ σ

    have : pr₁ (h (g (x , l))) ≡ x'
    have = refl

    s : f x' ≡ f x
    s = pr₂ (pr₂ σ)

    r : x' ≡ x
    r = simulations-are-lc α β f f-is-simulation s

  ε : g ∘ h ∼ id
  ε (y , m) = to-subtype-≡ (λ - → Prop-valuedness β - (f a)) r
   where
    r : f (pr₁ (f-is-initial-segment a y m)) ≡ y
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

    s : f x ≡ y
    s = pr₂ (pr₂ σ)

    s' : f x' ≡ y'
    s' = pr₂ (pr₂ σ')

    t : f x ≺⟨ β ⟩ f x'
    t = transport₂ (λ y y' → y ≺⟨ β ⟩ y') (s ⁻¹) (s' ⁻¹) l

    o : x ≺⟨ α ⟩ x'
    o = simulations-are-order-reflecting α β f f-is-simulation x x' t

  q : (α ↓ a) ≡ (β ↓ f a)
  q = eqtoidₒ (α ↓ a) (β ↓ f a)
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

  f-property : (a : ⟨ α ⟩) → (α ↓ a) ≡ (β ↓ f a)
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
                       → Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ≡ y)
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

    p = (β ↓ y)              ≡⟨ pr₂ n ⟩
        ((α ↓ x) ↓ (x' , o)) ≡⟨ iterated-↓ α x x' o ⟩
        (α ↓ x')             ≡⟨ f-property x' ⟩
        (β ↓ f x')           ∎

    q : y ≡ f x'
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
  ii = not-Π-implies-not-not-Σ' i

  iii : (Σ a ꞉ ⟨ α ⟩ , ¬ (Σ x ꞉ ⟨ α ⟩ , x ≺⟨ α ⟩ a))
      → (Σ a ꞉ ⟨ α ⟩ , ((x : ⟨ α ⟩) → a ≾⟨ α ⟩ x))
  iii (a , n) = a , not-Σ-implies-Π-not n

  iv : ¬¬ (Σ a ꞉ ⟨ α ⟩ , ((x : ⟨ α ⟩) → a ≾⟨ α ⟩ x))
  iv = ¬¬-functor iii ii

NB-minimal : (α : Ordinal 𝓤) (a : ⟨ α ⟩)
           →  ((x : ⟨ α ⟩) → a ≾⟨ α ⟩ x)
           ⇔  ((x : ⟨ α ⟩) → a ≼⟨ α ⟩ x)
NB-minimal α a = f , g
 where
  f : ((x : ⟨ α ⟩) → a ≾⟨ α ⟩ x) → ((x : ⟨ α ⟩) → a ≼⟨ α ⟩ x)
  f h x u l = 𝟘-elim (h u l)

  g : ((x : ⟨ α ⟩) → a ≼⟨ α ⟩ x) → ((x : ⟨ α ⟩) → a ≾⟨ α ⟩ x)
  g k x m = irrefl α x (k x x m)

\end{code}

Added 29th March.

Simulations preserve minimal elements.

\begin{code}

is-least : (α : Ordinal 𝓤) → ⟨ α ⟩ → 𝓤 ̇
is-least α x = (y : ⟨ α ⟩) → x ≼⟨ α ⟩ y

initial-segments-preserve-least : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                  (x : ⟨ α ⟩) (y : ⟨ β ⟩)
                                  (f : ⟨ α ⟩ → ⟨ β ⟩)
                                → is-initial-segment α β f
                                → is-least α x
                                → is-least β y
                                → f x ≡ y
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

  c : f x ≡ y
  c = Antisymmetry β (f x) y a b

simulations-preserve-least : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                             (x : ⟨ α ⟩) (y : ⟨ β ⟩)
                             (f : ⟨ α ⟩ → ⟨ β ⟩)
                           → is-simulation α β f
                           → is-least α x
                           → is-least β y
                           → f x ≡ y
simulations-preserve-least α β x y f (i , _) =
 initial-segments-preserve-least α β x y f i

\end{code}

Added in March 2022 by Tom de Jong:

Notice that we defined "is-initial-segment" using Σ (rather than ∃). This is
fine, because if f is a simulation from α to β, then for every x : ⟨ α ⟩ and
y : ⟨ β ⟩ with y ≺⟨ β ⟩ f x, the type (Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ≡ y))
is a proposition. It follows (see the proof above) that being a simulation is
property.

However, for some purposes, notably for constructing suprema of ordinals in
OrdinalSupOfOrdinals.lagda, it is useful to formulate the notion of initial
segment and the notion of simulation using ∃, rather than Σ.

Using the techniques that were used above to prove that being a simulation is
property, we show the definition of simulation with ∃ to be equivalent to the
original one.

\begin{code}

open import UF-PropTrunc
module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 is-initial-segment' : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇
 is-initial-segment' α β f = (x : ⟨ α ⟩) (y : ⟨ β ⟩)
                           → y ≺⟨ β ⟩ f x
                           → ∃ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ≡ y)

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
     → f x ≡ f y
     → x ≡ y
   φ x y (next x s) (next y t) r = Extensionality α x y g h
    where
     g : (u : ⟨ α ⟩) → u ≺⟨ α ⟩ x → u ≺⟨ α ⟩ y
     g u l = ∥∥-rec (Prop-valuedness α u y) b (i y (f u) a)
      where
       a : f u ≺⟨ β ⟩ f y
       a = transport (λ - → f u ≺⟨ β ⟩ -) r (p u x l)
       b : (Σ v ꞉ ⟨ α ⟩ , (v ≺⟨ α ⟩ y) × (f v ≡ f u))
         → u ≺⟨ α ⟩ y
       b (v , k , e) = transport (λ - → - ≺⟨ α ⟩ y) (c ⁻¹) k
        where
         c : u ≡ v
         c = φ u v (s u l) (t v k) (e ⁻¹)
     h : (u : ⟨ α ⟩) → u ≺⟨ α ⟩ y → u ≺⟨ α ⟩ x
     h u l = ∥∥-rec (Prop-valuedness α u x) b (i x (f u) a)
      where
       a : f u ≺⟨ β ⟩ f x
       a = transport (λ - → f u ≺⟨ β ⟩ -) (r ⁻¹) (p u y l)
       b : (Σ v ꞉ ⟨ α ⟩ , (v ≺⟨ α ⟩ x) × (f v ≡ f u))
         → u ≺⟨ α ⟩ x
       b (v , k , e) = transport (λ - → - ≺⟨ α ⟩ x) c k
        where
         c : v ≡ u
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
     prp : is-prop (Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ≡ y))
     prp (z , l , e) (z' , l' , e') = to-subtype-≡ ⦅1⦆ ⦅2⦆
      where
       ⦅1⦆ : (x' : ⟨ α ⟩) → is-prop ((x' ≺⟨ α ⟩ x) × (f x' ≡ y))
       ⦅1⦆ x' = ×-is-prop (Prop-valuedness α x' x) (underlying-type-is-set fe β)
       ⦅2⦆ : z ≡ z'
       ⦅2⦆ = simulations-are-lc' α β f (i , p) (e ∙ e' ⁻¹)

\end{code}
