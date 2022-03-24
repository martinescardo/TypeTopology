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

open import UF-Base hiding (_≈_)
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
  n = back-transport (λ - → - ≺⟨ α ⟩ b) q m

↓-lc : (α : Ordinal 𝓤) (a b : ⟨ α ⟩)
     → α ↓ a ≡ α ↓ b → a ≡ b
↓-lc α a b p =
 Extensionality α a b
  (↓-⊴-lc α a b (transport      (λ - → (α ↓ a) ⊴ -) p (⊴-refl (α ↓ a))))
  (↓-⊴-lc α b a (back-transport (λ - → (α ↓ b) ⊴ -) p (⊴-refl (α ↓ b))))

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
  γ = back-transport (λ - → - ≺⟨ α ⟩ b) r l

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
    g β ((b , l) , p) = back-transport (is-accessible _⊲_) q (IH b l)
     where
      q : β ≡ (α ↓ b)
      q = p ∙ iterated-↓ α a b l

⊲-is-well-founded : is-well-founded (_⊲_ {𝓤})
⊲-is-well-founded {𝓤} α = next α g
 where
  g : (β : Ordinal 𝓤) → β ⊲ α → is-accessible _⊲_ β
  g β (b , p) = back-transport (is-accessible _⊲_) p (↓-accessible α b)

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

    j = back-transport (λ - → f u ≺⟨ β ⟩ -) s i


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

Example. Classically, the ordinals ℕₒ +ₒ 𝟙ₒ and ℕ∞ₒ are equal.
Constructively, we have (ℕₒ +ₒ 𝟙ₒ) ⊴ ℕ∞ₒ, but the inequality in the
other direction is equivalent to LPO.

\begin{code}

module example where

 open import LPO fe
 open import OrdinalArithmetic fe
 open import GenericConvergentSequence
 open import NaturalsOrder

 fact : (ℕₒ +ₒ 𝟙ₒ) ⊴ ℕ∞ₒ
 fact = ι𝟙 , i , p
  where
   i : (x : ⟨ ℕₒ +ₒ 𝟙ₒ ⟩) (y : ⟨ ℕ∞ₒ ⟩)
     → y ≺⟨ ℕ∞ₒ ⟩ ι𝟙 x
     → Σ x' ꞉ ⟨ ℕₒ +ₒ 𝟙ₒ ⟩ , (x' ≺⟨ ℕₒ +ₒ 𝟙ₒ ⟩ x) × (ι𝟙 x' ≡ y)
   i (inl m) y (n , r , l) = inl n , ⊏-gives-< n m l , (r ⁻¹)
   i (inr *) y (n , r , l) = inl n , * , (r ⁻¹)

   p : (x y : ⟨ ℕₒ +ₒ 𝟙ₒ ⟩)
     → x ≺⟨ ℕₒ +ₒ 𝟙ₒ ⟩ y
     → ι𝟙 x ≺⟨ ℕ∞ₒ ⟩ ι𝟙 y
   p (inl n) (inl m) l = ι-order-preserving n m l
   p (inl n) (inr *) * = ∞-≺-maximal n
   p (inr *) (inl m) l = 𝟘-elim l
   p (inr *) (inr *) l = 𝟘-elim l

 converse-fails-constructively : ℕ∞ₒ ⊴ (ℕₒ +ₒ 𝟙ₒ) → LPO
 converse-fails-constructively l = γ
  where
   b : (ℕₒ +ₒ 𝟙ₒ) ≃ₒ ℕ∞ₒ
   b = bisimilarity-gives-ordinal-equiv (ℕₒ +ₒ 𝟙ₒ) ℕ∞ₒ fact l

   e : is-equiv ι𝟙
   e = pr₂ (≃ₒ-gives-≃ (ℕₒ +ₒ 𝟙ₒ) ℕ∞ₒ b)

   γ : LPO
   γ = ι𝟙-has-section-gives-LPO (equivs-have-sections ι𝟙 e)

 converse-fails-constructively-converse : LPO → ℕ∞ₒ ⊴ (ℕₒ +ₒ 𝟙ₒ)
 converse-fails-constructively-converse lpo = (λ x → ι𝟙-inverse x (lpo x)) ,
                                              (λ x → i x (lpo x)) ,
                                              (λ x y → p x y (lpo x) (lpo y))
  where
   ι𝟙-inverse-inl : (u : ℕ∞) (d : decidable (Σ n ꞉ ℕ , u ≡ ι n))
                      → (m : ℕ) → u ≡ ι m → ι𝟙-inverse u d ≡ inl m
   ι𝟙-inverse-inl . (ι n) (inl (n , refl)) m q = ap inl (ℕ-to-ℕ∞-lc q)
   ι𝟙-inverse-inl u          (inr g)          m q = 𝟘-elim (g (m , q))

   i : (x : ℕ∞) (d : decidable (Σ n ꞉ ℕ , x ≡ ι n)) (y : ℕ + 𝟙)
     → y ≺⟨ ℕₒ +ₒ 𝟙ₒ ⟩ ι𝟙-inverse x d
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
               (∞-≺-maximal n) ,
     ι𝟙-inverse-inl (ι n) (lpo (ι n)) n refl
   i x (inr g) (inr *) l = 𝟘-elim l

   p : (x y : ℕ∞)  (d : decidable (Σ n ꞉ ℕ , x ≡ ι n)) (e : decidable (Σ m ꞉ ℕ , y ≡ ι m))
     →  x ≺⟨ ℕ∞ₒ ⟩ y
     → ι𝟙-inverse x d ≺⟨ ℕₒ +ₒ 𝟙ₒ ⟩ ι𝟙-inverse y e
   p .(ι n) .(ι m) (inl (n , refl)) (inl (m , refl)) (k , r , l) =
    back-transport (λ - → - <ℕ m) (ℕ-to-ℕ∞-lc r) (⊏-gives-< k m l)
   p .(ι n) y (inl (n , refl)) (inr f) l = ⋆
   p x y (inr f) e (k , r , l) =
    𝟘-elim (∞-is-not-finite k ((not-finite-is-∞ (fe 𝓤₀ 𝓤₀) (curry f))⁻¹ ∙ r))

 corollary₁ : LPO → ℕ∞ₒ ≃ₒ (ℕₒ +ₒ 𝟙ₒ)
 corollary₁ lpo = bisimilarity-gives-ordinal-equiv
                   ℕ∞ₒ (ℕₒ +ₒ 𝟙ₒ)
                   (converse-fails-constructively-converse lpo) fact

 corollary₂ : LPO → ℕ∞ ≃ (ℕ + 𝟙)
 corollary₂ lpo = ≃ₒ-gives-≃ ℕ∞ₒ (ℕₒ +ₒ 𝟙ₒ) (corollary₁ lpo)

 corollary₃ : is-univalent 𝓤₀ → LPO → ℕ∞ₒ ≡ (ℕₒ +ₒ 𝟙ₒ)
 corollary₃ ua lpo = eqtoidₒ ℕ∞ₒ (ℕₒ +ₒ 𝟙ₒ) (corollary₁ lpo)

 corollary₄ : is-univalent 𝓤₀ → LPO → ℕ∞ ≡ (ℕ + 𝟙)
 corollary₄ ua lpo = eqtoid ua ℕ∞ (ℕ + 𝟙) (corollary₂ lpo)

\end{code}

TODO.

Question. Do we have (finite or arbitrary) joins of ordinals? Probably not.

Conjecture. We have bounded joins. The construction would be to take
the joint image in any upper bound.

Added 19-20 January 2021.

The partial order _⊴_ is equivalent to _≼_.

We first observe that, almost tautologically, the relation α ≼ β is
logically equivalent to the condition (a : ⟨ α ⟩) → (α ↓ a) ⊲ β.

\begin{code}

_≼_ : Ordinal 𝓤 → Ordinal 𝓤 → 𝓤 ⁺ ̇
α ≼ β = α ≼⟨ OO _ ⟩ β

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

\end{code}


\begin{code}

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

Added in March 2022 by Tom de Jong.

Notice that we defined "is-initial-segment" using Σ (rather than ∃). This is
fine, because if f is a simulation from α to β, then for every x : ⟨ α ⟩ and
y : ⟨ β ⟩ with y ≺⟨ β ⟩ f x, the type (Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ≡ y))
is a proposition. It follows (see the proof above) that being a simulation is
property.

However, for some purposes, notably for constructing suprema of ordinals in
OrdinalSupOfOrdinals.lagda, it is useful to formulate being an initial segment
and the notion of simulation using ∃, rather than Σ.

Using the techniques that were used above to prove that being a simulation is
property, we show the definition of simulation with ∃ to be equivalent to the
original one.

\begin{code}

open import UF-PropTrunc
module simulation-∃ (pt : propositional-truncations-exist) where

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

--

-- module _
--         {I : 𝓤 ̇  }
--         (α : I → Ordinal 𝓤)
--        where

--  Σα : 𝓤 ̇
--  Σα = Σ i ꞉ I , ⟨ α i ⟩

--  _≈_ : Σα → Σα → 𝓤 ̇
--  (i , x) ≈ (j , y) = (α i ↓ x) ≃ₒ (α j ↓ y)

--  ≈-is-symmetric : symmetric _≈_
--  ≈-is-symmetric (i , x) (j , y) = ≃ₒ-sym (α i ↓ x) (α j ↓ y)

--  ≈-is-transitive : transitive _≈_
--  ≈-is-transitive (i , x) (j , y) (k , z) = ≃ₒ-trans (α i ↓ x) (α j ↓ y) (α k ↓ z)

--  ≈-is-reflexive : reflexive _≈_
--  ≈-is-reflexive (i , x) = ≃ₒ-refl (α i ↓ x)

--  ≈-is-prop-valued : is-prop-valued _≈_
--  ≈-is-prop-valued (i , x) (j , y) = ≃ₒ-is-prop-valued (α i ↓ x) (α j ↓ y)

--  _≺'_ : Σα → Σα → 𝓤 ⁺ ̇
--  (i , x) ≺' (j , y) = (α i ↓ x) ⊲ (α j ↓ y)

--  ≺'-is-prop-valued : is-prop-valued _≺'_
--  ≺'-is-prop-valued (i , x) (j , y) = ⊲-is-prop-valued (α i ↓ x) (α j ↓ y)

--  ≺'-is-transitive : transitive _≺'_
--  ≺'-is-transitive (i , x) (j , y) (k , z) =
--   ⊲-is-transitive (α i ↓ x) (α j ↓ y) (α k ↓ z)

--  ≺'-is-well-founded : is-well-founded _≺'_
--  ≺'-is-well-founded = transfinite-induction-converse _≺'_ goal
--   where
--    goal : Well-founded _≺'_
--    goal P IH (i , x) = lemma (α i ↓ x) i x refl
--     where
--      P̃ : Ordinal 𝓤 → 𝓤 ⁺ ̇
--      P̃ β = (i : I) (x : ⟨ α i ⟩) → β ≡ (α i ↓ x) → P (i , x)
--      lemma : (β : Ordinal 𝓤) → P̃ β
--      lemma = transfinite-induction _⊲_ ⊲-is-well-founded P̃ claim
--       where
--        claim : (β : Ordinal 𝓤) → ((γ : Ordinal 𝓤) → γ ⊲ β → P̃ γ) → P̃ β
--        claim β IH' i x refl = IH (i , x) subclaim
--         where
--          subclaim : ((j , y) : Σα) → (j , y) ≺' (i , x) → P (j , y)
--          subclaim (j , y) (z , e) = IH' ((α i ↓ x) ↓ z) (z , refl) j y (e ⁻¹)

--  ≺'-is-extensional-up-to-≈ : (p q : Σα)
--                            → ((r : Σα) → r ≺' p → r ≺' q)
--                            → ((r : Σα) → r ≺' q → r ≺' p)
--                            → p ≈ q
--  ≺'-is-extensional-up-to-≈ (i , x) (j , y) hyp₁ hyp₂ =
--   ⌜ UAₒ-≃ (α i ↓ x) (α j ↓ y) ⌝ goal
--    where
--     goal : (α i ↓ x) ≡ (α j ↓ y)
--     goal = ⊲-is-extensional (α i ↓ x) (α j ↓ y) ⦅1⦆ ⦅2⦆
--      where
--       ⦅1⦆ : (β : Ordinal 𝓤) → β ⊲ (α i ↓ x) → β ⊲ (α j ↓ y)
--       ⦅1⦆ β (p , refl) = goal₁
--        where
--         goal₁ : ((α i ↓ x) ↓ p) ⊲ (α j ↓ y)
--         goal₁ = back-transport (_⊲ (α j ↓ y)) claim₂ claim₁
--          where
--           x' : ⟨ α i ⟩
--           x' = pr₁ p
--           x'-below-x : x' ≺⟨ α i ⟩ x
--           x'-below-x = pr₂ p
--           claim₁ : (α i ↓ x') ⊲ (α j ↓ y)
--           claim₁ = hyp₁ (i , x') (↓-preserves-order (α i) x' x x'-below-x)
--           claim₂ : ((α i ↓ x) ↓ p) ≡ (α i ↓ x')
--           claim₂ = iterated-↓ (α i) x x' x'-below-x
--       ⦅2⦆ : (β : Ordinal 𝓤) → β ⊲ (α j ↓ y) → β ⊲ (α i ↓ x)
--       ⦅2⦆ β (p , refl) = goal₂
--        where
--         goal₂ : ((α j ↓ y) ↓ p) ⊲ (α i ↓ x)
--         goal₂ = back-transport (_⊲ (α i ↓ x)) claim₂ claim₁
--          where
--           y' : ⟨ α j ⟩
--           y' = pr₁ p
--           y'-below-y : y' ≺⟨ α j ⟩ y
--           y'-below-y = pr₂ p
--           claim₁ : (α j ↓ y') ⊲ (α i ↓ x)
--           claim₁ = hyp₂ (j , y') (↓-preserves-order (α j) y' y y'-below-y)
--           claim₂ : ((α j ↓ y) ↓ p) ≡ (α j ↓ y')
--           claim₂ = iterated-↓ (α j) y y' y'-below-y

--  to-Σα : (i : I) → ⟨ α i ⟩ → Σα
--  to-Σα i x = (i , x)

--  to-Σα-is-order-preserving : (i : I) (x y : ⟨ α i ⟩)
--                          → x ≺⟨ α i ⟩ y → to-Σα i x ≺' to-Σα i y
--  to-Σα-is-order-preserving i x y l = ↓-preserves-order (α i) x y l

--  to-Σα-is-initial-segment-up-to-≈ : (i : I) (x : ⟨ α i ⟩) ((j , y) : Σα)
--                                   → (j , y) ≺' to-Σα i x
--                                   → Σ x' ꞉ ⟨ α i ⟩ , (x' ≺⟨ α i ⟩ x)
--                                                    × (to-Σα i x' ≈ (j , y))
--  to-Σα-is-initial-segment-up-to-≈ i x (j , y) (p , e) = (x' , l , goal)
--   where
--    x' : ⟨ α i ⟩
--    x' = pr₁ p
--    l : x' ≺⟨ α i ⟩ x
--    l = pr₂ p
--    goal : (α i ↓ x') ≃ₒ (α j ↓ y)
--    goal = ⌜ UAₒ-≃ (α i ↓ x') (α j ↓ y) ⌝ (subgoal ⁻¹)
--     where
--      subgoal = (α j ↓ y)       ≡⟨ e ⟩
--                ((α i ↓ x) ↓ p) ≡⟨ iterated-↓ (α i) x x' l ⟩
--                (α i ↓ x')      ∎

--  module lowerbound-of-upperbounds-proof
--          (β : Ordinal 𝓤)
--          (β-is-upperbound : (i : I) → α i ⊴ β)
--         where

--   -- private
--   f : (i : I) → ⟨ α i ⟩ → ⟨ β ⟩
--   f i x = pr₁ (β-is-upperbound i) x

--   f-key-property : (i : I) (x : ⟨ α i ⟩) → α i ↓ x ≡ β ↓ (f i x)
--   f-key-property i x =
--    pr₂ (⊴-gives-≼ (α i) β (β-is-upperbound i) (α i ↓ x) (x , refl))

--   f̃ : Σα → ⟨ β ⟩
--   f̃ (i , x) = f i x

--   β-is-upperbound-≼ : (i : I) → α i ≼ β
--   β-is-upperbound-≼ i = ⊴-gives-≼ (α i) β (β-is-upperbound i)

--   f̃-respects-≈ : (p q : Σα) → p ≈ q → f̃ p ≡ f̃ q
--   f̃-respects-≈ (i , x) (j , y) e = ↓-lc β (f̃ (i , x)) (f̃ (j , y)) goal
--    where
--     goal = (β ↓ f̃ (i , x)) ≡⟨ ⦅1⦆ ⟩
--            (α i ↓ x)       ≡⟨ ⦅2⦆ ⟩
--            (α j ↓ y)       ≡⟨ ⦅3⦆ ⟩
--            (β ↓ f̃ (j , y)) ∎
--      where
--       ⦅1⦆ = (f-key-property i x) ⁻¹
--       ⦅2⦆ = ⌜ UAₒ-≃ (α i ↓ x) (α j ↓ y) ⌝⁻¹ e
--       ⦅3⦆ = f-key-property j y

--   f̃-is-order-preserving : (p q : Σα) → p ≺' q → f̃ p ≺⟨ β ⟩ f̃ q
--   f̃-is-order-preserving (i , x) (j , y) l =
--    ↓-reflects-order β (f̃ (i , x)) (f̃ (j , y)) goal
--     where
--      goal : (β ↓ f̃ (i , x)) ⊲ (β ↓ f̃ (j , y))
--      goal = transport₂ _⊲_ (f-key-property i x) (f-key-property j y) l

--   f̃-is-initial-segment : (p : Σα) (b : ⟨ β ⟩)
--                        → b ≺⟨ β ⟩ f̃ p
--                        → Σ q ꞉ Σα , (q ≺' p) × (f̃ q ≡ b)
--   f̃-is-initial-segment (i , x) b l = (i , x') , goal₁ , goal₂
--    where
--     lemma : Σ x' ꞉ ⟨ α i ⟩ , (x' ≺⟨ α i ⟩ x) × (f i x' ≡ b)
--     lemma = simulations-are-initial-segments (α i) β
--              (f i) (pr₂ (β-is-upperbound i))
--              x b l
--     x' : ⟨ α i ⟩
--     x' = pr₁ lemma
--     x'-below-x : x' ≺⟨ α i ⟩ x
--     x'-below-x = pr₁ (pr₂ lemma)

--     goal₁ : (α i ↓ x') ⊲ (α i ↓ x)
--     goal₁ = ↓-preserves-order (α i) x' x x'-below-x
--     goal₂ : f̃ (i , x') ≡ b
--     goal₂ = pr₂ (pr₂ lemma)

--  open import UF-PropTrunc
--  module _ (pt : propositional-truncations-exist)
--           (pe : Prop-Ext)
--         where

--   open import UF-ImageAndSurjection
--   open ImageAndSurjection pt
--   open PropositionalTruncation pt

--   module _
--           (α⁺ : 𝓤 ̇  )
--           (α⁺-is-set : is-set α⁺)
--           ([_] : Σα → α⁺)
--           ([]-respects-≈ : (p q : Σα) → p ≈ q → [ p ] ≡ [ q ])
--           ([]-is-surjection : is-surjection [_])
--           (quotient-universal-property : {𝓥 : Universe} (X : 𝓥 ̇  ) (g : Σα → X)
--                                        → is-set X
--                                        → ((p q : Σα) → p ≈ q → g p ≡ g q)
--                                        → Σ g̃ ꞉ (α⁺ → X) , g̃ ∘ [_] ∼ g)
--          where

--    quotient-induction : ∀ {𝓥} → imageInduction {𝓥} [_]
--    quotient-induction = surjection-induction [_] []-is-surjection

--    extend₂ : {𝓥 : Universe} (X : 𝓥 ̇  ) (g : Σα → Σα → X)
--            → is-set X
--            → ((p q₁ q₂ : Σα) → q₁ ≈ q₂ → g p q₁  ≡ g p q₂)
--            → ((p₁ p₂ q : Σα) → p₁ ≈ p₂ → g p₁ q  ≡ g p₂ q)
--            → Σ g̃ ꞉ (α⁺ → α⁺ → X) , ((p q : Σα) → g̃ [ p ] [ q ] ≡ g p q)
-    extend₂ {𝓥} X g X-is-set resp₁ resp₂ = g̃ , goal
--     where
--      g' : Σα → α⁺ → X
--      g' p = pr₁ (quotient-universal-property X (g p) X-is-set (resp₁ p))
--      g'-eq : (p : Σα) → g' p ∘ [_] ∼ g p
--      g'-eq p = pr₂ (quotient-universal-property X (g p) X-is-set (resp₁ p))
--      foofoo : Σ (λ g̃ → g̃ ∘ [_] ∼ g')
--      foofoo = quotient-universal-property (α⁺ → X) g' (Π-is-set (fe 𝓤 𝓥) (λ _ → X-is-set)) γ
--       where
--        γ : (p q : Σα) → p ≈ q → g' p ≡ g' q
--        γ p q e = dfunext (fe 𝓤 𝓥) h
--         where
--          h : g' p ∼ g' q
--          h = quotient-induction (λ z → g' p z ≡ g' q z) (λ _ → X-is-set)
--               blah
--           where
--            blah : (r : Σα) → g' p [ r ] ≡ g' q [ r ]
--            blah r = g' p [ r ] ≡⟨ g'-eq p r ⟩
--                     g  p   r   ≡⟨ resp₂ p q r e ⟩
--                     g  q   r   ≡⟨ (g'-eq q r) ⁻¹ ⟩
--                     g' q [ r ] ∎
--      g̃ : α⁺ → α⁺ → X
--      g̃ = pr₁ foofoo
--      foo : g̃ ∘ [_] ∼ g'
--      foo = pr₂ foofoo
--      goal : (p q : Σα) → g̃ [ p ] [ q ] ≡ g p q
--      goal p q = g̃ [ p ] [ q ] ≡⟨ happly (foo p) [ q ] ⟩
--                 g' p    [ q ] ≡⟨ g'-eq p q ⟩
--                 g  p      q   ∎

--    ≺'-congruence-right : (p q r : Σα) → p ≺' q → q ≈ r → p ≺' r
--    ≺'-congruence-right (i , x) (j , y) (k , z) u e =
--     transport ((α i ↓ x) ⊲_) e⁺ u
--      where
--       e⁺ : (α j ↓ y) ≡ (α k ↓ z)
--       e⁺ = ⌜ UAₒ-≃ (α j ↓ y) (α k ↓ z) ⌝⁻¹ e

--    ≺'-congruence-left : (p q r : Σα) → p ≺' r → p ≈ q → q ≺' r
--    ≺'-congruence-left (i , x) (j , y) (k , z) u e = transport (_⊲ (α k ↓ z)) e⁺ u
--     where
--      e⁺ : (α i ↓ x) ≡ (α j ↓ y)
--      e⁺ = ⌜ UAₒ-≃ (α i ↓ x) (α j ↓ y) ⌝⁻¹ e

--    ≺-setup : Σ g̃ ꞉ (α⁺ → α⁺ → Ω (𝓤 ⁺)) ,
--               ((p q : Σα) → g̃ [ p ] [ q ] ≡ (p ≺' q) , ≺'-is-prop-valued p q)
--    ≺-setup = extend₂ (Ω (𝓤 ⁺)) (λ p q → (p ≺' q) , (≺'-is-prop-valued p q))
--               (Ω-is-set (fe (𝓤 ⁺) (𝓤 ⁺)) pe)
--                 (λ p q₁ q₂ e → Ω-extensionality (fe (𝓤 ⁺) (𝓤 ⁺)) pe
--                                 (λ u → ≺'-congruence-right p q₁ q₂ u e)
--                                 (λ v → ≺'-congruence-right p q₂ q₁
--                                         v (≈-is-symmetric q₁ q₂ e)))
--                 λ p₁ p₂ q e → Ω-extensionality (fe (𝓤 ⁺) (𝓤 ⁺)) pe
--                                (λ u → ≺'-congruence-left p₁ p₂ q u e)
--                                (λ v → ≺'-congruence-left p₂ p₁ q v
--                                        (≈-is-symmetric p₁ p₂ e))

--    _≺[Ω]_ : α⁺ → α⁺ → Ω (𝓤 ⁺)
--    _≺[Ω]_ = pr₁ ≺-setup

--    _≺_ : α⁺ → α⁺ → 𝓤 ⁺ ̇
--    x ≺ y = (x ≺[Ω] y) holds

--    ≺-≡-≺' : (p q : Σα) → [ p ] ≺ [ q ] ≡ p ≺' q
--    ≺-≡-≺' p q = ap pr₁ (pr₂ ≺-setup p q)

--    quotient-induction₂ : (P : α⁺ → α⁺ → 𝓦 ̇ )
--                        → ((x y : α⁺) → is-prop (P x y))
--                        → ((p q : Σα) → P [ p ] [ q ])
--                        → (x y : α⁺) → P x y
--    quotient-induction₂ P P-is-prop-valued P-on-[] =
--     quotient-induction (λ x → (y : α⁺) → P x y)
--       (λ x → Π-is-prop (fe 𝓤 _) (λ y → P-is-prop-valued x y))
--       (λ p → quotient-induction (P [ p ]) (λ y → P-is-prop-valued [ p ] y)
--               (P-on-[] p))

--    quotient-induction₃ : (P : α⁺ → α⁺ → α⁺ → 𝓦 ̇ )
--                        → ((x y z : α⁺) → is-prop (P x y z))
--                        → ((p q r : Σα) → P [ p ] [ q ] [ r ])
--                        → (x y z : α⁺) → P x y z
--    quotient-induction₃ P P-is-prop-valued P-on-[] =
--     quotient-induction₂ (λ x y → (z : α⁺) → P x y z)
--                         (λ x y → Π-is-prop (fe 𝓤 _) (λ z → P-is-prop-valued x y z))
--                         (λ p q → quotient-induction (P [ p ] [ q ])
--                                   (λ z → P-is-prop-valued [ p ] [ q ] z)
--                                   (P-on-[] p q))

--    ≺-is-prop-valued : (x y : α⁺) → is-prop (x ≺ y)
--    ≺-is-prop-valued = quotient-induction₂ (λ x y → is-prop (x ≺ y))
--                        (λ x y → being-prop-is-prop (fe (𝓤 ⁺) (𝓤 ⁺)))
--                        (λ p q → back-transport is-prop (≺-≡-≺' p q) (≺'-is-prop-valued p q))

--    ≺-is-transitive : transitive _≺_
--    ≺-is-transitive = quotient-induction₃ (λ x y z → x ≺ y → y ≺ z → x ≺ z)
--                       (λ x y z → Π₂-is-prop (fe _ _) (λ _ _ → ≺-is-prop-valued x z))
--                       (λ p q r u v → Idtofun ((≺-≡-≺' p r) ⁻¹)
--                                       (≺'-is-transitive p q r (Idtofun (≺-≡-≺' p q) u)
--                                                               (Idtofun (≺-≡-≺' q r) v)))

--    ≺-is-extensional : is-extensional _≺_
--    ≺-is-extensional = quotient-induction₂
--      (λ x y → ((z : α⁺) → z ≺ x → z ≺ y) → ((z : α⁺) → z ≺ y → z ≺ x) → x ≡ y)
--      (λ x y → Π₂-is-prop (fe _ _) (λ _ _ → α⁺-is-set))
--      γ
--     where
--      γ : (p q : Σα)
--        → ((z : α⁺) → z ≺ [ p ] → z ≺ [ q ])
--        → ((z : α⁺) → z ≺ [ q ] → z ≺ [ p ])
--        → [ p ] ≡ [ q ]
--      γ p q u v = []-respects-≈ p q goal
--       where
--        goal : p ≈ q
--        goal = ≺'-is-extensional-up-to-≈ p q u' v'
--         where
--          u' : (r : Σα) → r ≺' p → r ≺' q
--          u' r l = Idtofun (≺-≡-≺' r q) (u [ r ] (Idtofun (≺-≡-≺' r p ⁻¹) l))
--          v' : (r : Σα) → r ≺' q → r ≺' p
--          v' r l = Idtofun (≺-≡-≺' r p) (v [ r ] (Idtofun (≺-≡-≺' r q ⁻¹) l))

--    ≺-is-well-founded : is-well-founded _≺_
--    ≺-is-well-founded = goal
--     where
--      goal' : (p : Σα) → is-accessible _≺_ [ p ]
--      goal' = transfinite-induction _≺'_ ≺'-is-well-founded
--               (λ p → is-accessible _≺_ [ p ])
--               γ
--       where
--        γ : (p : Σα)
--          → ((q : Σα) → q ≺' p → is-accessible _≺_ [ q ])
--          → is-accessible _≺_ [ p ]
--        γ p IH = next [ p ] IH'
--         where
--          IH' : (y : α⁺) → y ≺ [ p ] → is-accessible _≺_ y
--          IH' = quotient-induction (λ y → y ≺ [ p ] → is-accessible _≺_ y)
--                 (λ y → Π-is-prop (fe (𝓤 ⁺) (𝓤 ⁺)) (λ _ → accessibility-is-prop _≺_ fe y))
--                 (λ q u → IH q (Idtofun (≺-≡-≺' q p) u))
--      goal : (x : α⁺ ) → is-accessible _≺_ x
--      goal = quotient-induction (λ x → is-accessible _≺_ x)
--              (λ x → accessibility-is-prop _≺_ fe x)
--              goal'

--    ≺-is-well-order : is-well-order _≺_
--    ≺-is-well-order =
--     ≺-is-prop-valued , ≺-is-well-founded , ≺-is-extensional , ≺-is-transitive

--    _≺'⁻_ : Σα → Σα → 𝓤 ̇
--    (i , x) ≺'⁻ (j , y) = (α i ↓ x) ⊲⁻ (α j ↓ y)

--    ≺'-≃-≺'⁻ : (p q : Σα) → p ≺' q ≃ p ≺'⁻ q
--    ≺'-≃-≺'⁻ (i , x) (j , y) = ⊲-is-equivalent-to-⊲⁻ (α i ↓ x) (α j ↓ y)


--    open import UF-Size
--    ≺-has-small-values : (x y : α⁺) → is-small (x ≺ y)
--    ≺-has-small-values = quotient-induction₂ (λ x y → is-small (x ≺ y))
--      (λ x y → being-small-is-prop ua (x ≺ y) 𝓤)
--      (λ p q → (p ≺'⁻ q) , (p ≺'⁻ q ≃⟨ ≃-sym (≺'-≃-≺'⁻ p q) ⟩
--                            p ≺'  q ≃⟨ idtoeq (p ≺' q) ([ p ] ≺ [ q ]) ((≺-≡-≺' p q) ⁻¹) ⟩
--                            [ p ] ≺ [ q ] ■))

--    _≺⁻_ : α⁺ → α⁺ → 𝓤 ̇
--    x ≺⁻ y = pr₁ (≺-has-small-values x y)

--    ≺-≃-≺⁻ : {x y : α⁺} → x ≺ y ≃ x ≺⁻ y
--    ≺-≃-≺⁻ {x} {y} = ≃-sym (pr₂ (≺-has-small-values x y))


--    open import OrdinalsWellOrderTransport fe
--    open order-transfer-lemma₂ α⁺ _≺_ _≺⁻_ (λ x y → ≺-≃-≺⁻)

--    ≺⁻-is-transitive : transitive _≺⁻_
--    ≺⁻-is-transitive = is-transitive→ ≺-is-transitive

--    ≺⁻-is-prop-valued : is-prop-valued _≺⁻_
--    ≺⁻-is-prop-valued = is-prop-valued→ ≺-is-prop-valued

--    ≺⁻-is-extensional : is-extensional _≺⁻_
--    ≺⁻-is-extensional = is-extensional→ ≺-is-extensional

--    ≺⁻-is-well-founded : is-well-founded _≺⁻_
--    ≺⁻-is-well-founded = is-well-founded→ ≺-is-well-founded

--    ≺⁻-is-well-order : is-well-order _≺⁻_
--    ≺⁻-is-well-order =
--     ≺⁻-is-prop-valued , ≺⁻-is-well-founded , ≺⁻-is-extensional , ≺⁻-is-transitive

--    α⁺-Ord : Ordinal 𝓤
--    α⁺-Ord = α⁺ , _≺⁻_ , ≺⁻-is-well-order

--    ≺⁻-≃-≺' : {p q : Σα} → [ p ] ≺⁻ [ q ] ≃ p ≺' q
--    ≺⁻-≃-≺' {p} {q} = [ p ] ≺⁻ [ q ] ≃⟨ ≃-sym ≺-≃-≺⁻ ⟩
--                      [ p ] ≺  [ q ] ≃⟨ idtoeq ([ p ] ≺ [ q ]) (p ≺' q) (≺-≡-≺' p q) ⟩
--                      p     ≺'   q   ■

--    open simulation-∃ pt
--    α⁺-Ord-is-upperbound : (i : I) → α i ⊴ α⁺-Ord
--    α⁺-Ord-is-upperbound i = ([_] ∘ (to-Σα i) , γ)
--     where
--      γ : is-simulation (α i) α⁺-Ord (λ x → [ i , x ])
--      γ = simulation-unprime (α i) α⁺-Ord (λ x → [ i , x ]) σ
--       where
--        σ : is-simulation' (α i) α⁺-Ord (λ x → [ i , x ])
--        σ = init-seg , order-pres
--         where
--          order-pres : is-order-preserving (α i) α⁺-Ord (λ x → [ i , x ])
--          order-pres x y l = ⌜ ≺-≃-≺⁻ ⌝ (Idtofun ((≺-≡-≺' (i , x) (i , y)) ⁻¹)
--                              (to-Σα-is-order-preserving i x y l))
--          init-seg : is-initial-segment' (α i) α⁺-Ord (λ x → [ i , x ])
--          init-seg x = quotient-induction _ (λ y → Π-is-prop (fe 𝓤 𝓤) (λ _ → ∃-is-prop))
--                        claim
--           where
--            claim : (p : Σα) → [ p ] ≺⁻ [ i , x ]
--                  → ∃ y ꞉ ⟨ α i ⟩ , (y ≺⟨ α i ⟩ x) × ([ i , y ] ≡ [ p ])
--            claim p l = ∣ y , k , []-respects-≈ (i , y) p e ∣
--             where
--              abstract
--               lem : Σ y ꞉ ⟨ α i ⟩ , (y ≺⟨ α i ⟩ x) × ((i , y) ≈ p)
--               lem = to-Σα-is-initial-segment-up-to-≈ i x p
--                      (Idtofun (≺-≡-≺' p (i , x)) (⌜ ≺-≃-≺⁻ ⌝⁻¹ l))
--               y : ⟨ α i ⟩
--               y = pr₁ lem
--               k : y ≺⟨ α i ⟩ x
--               k = pr₁ (pr₂ lem)
--               e : (i , y) ≈ p
--               e = pr₂ (pr₂ lem)

--    module _
--            (β : Ordinal 𝓤)
--            (β-is-upperbound : (i : I) → α i ⊴ β)
--           where

--     open lowerbound-of-upperbounds-proof β β-is-upperbound

--     α⁺-is-lowerbound-of-upperbounds : α⁺-Ord ⊴ β
--     α⁺-is-lowerbound-of-upperbounds = f⁺ , f⁺-is-simulation
--      where
--       f⁺ : α⁺ → ⟨ β ⟩
--       f⁺ = pr₁ (quotient-universal-property ⟨ β ⟩ f̃
--                 (underlying-type-is-set fe β) f̃-respects-≈)
--       f⁺-≡-f̃ : (p : Σα) → f⁺ [ p ] ≡ f̃ p
--       f⁺-≡-f̃ = pr₂ (quotient-universal-property ⟨ β ⟩ f̃
--                      (underlying-type-is-set fe β) f̃-respects-≈)

--       f⁺-is-order-preserving : is-order-preserving α⁺-Ord β f⁺
--       f⁺-is-order-preserving =
--        quotient-induction₂ _ (λ x y → Π-is-prop (fe 𝓤 𝓤)
--                              (λ _ → Prop-valuedness β (f⁺ x) (f⁺ y)))
--                              lem
--         where
--          lem : (p q : Σα) → [ p ] ≺⁻ [ q ]
--              → f⁺ [ p ] ≺⟨ β ⟩ f⁺ [ q ]
--          lem p q u = transport₂ (λ -₁ -₂ → -₁ ≺⟨ β ⟩ -₂)
--                       ((f⁺-≡-f̃ p) ⁻¹) ((f⁺-≡-f̃ q) ⁻¹)
--                       (f̃-is-order-preserving p q (⌜ ≺⁻-≃-≺' ⌝ u))

--       f⁺-is-simulation : is-simulation α⁺-Ord β f⁺
--       f⁺-is-simulation = simulation-unprime α⁺-Ord β f⁺ σ
--        where
--         σ : is-simulation' α⁺-Ord β f⁺
--         σ = init-seg , f⁺-is-order-preserving
--          where
--           init-seg : is-initial-segment' α⁺-Ord β f⁺
--           init-seg = quotient-induction _ (λ x → Π₂-is-prop (fe _ _) (λ _ _ → ∃-is-prop))
--                       τ
--            where
--             τ : (p : Σα) (y : ⟨ β ⟩)
--               → y ≺⟨ β ⟩ f⁺ [ p ]
--               → ∃ x ꞉ α⁺ , (x ≺⁻ [ p ]) × (f⁺ x ≡ y)
--             τ p y l = ∣ [ q ] , k' , e' ∣
--              where
--               abstract
--                lem : Σ q ꞉ Σα , (q ≺' p) × (f̃ q ≡ y)
--                lem = f̃-is-initial-segment p y (transport (λ - → y ≺⟨ β ⟩ -)
--                       (f⁺-≡-f̃ p) l)
--                q : Σα
--                q = pr₁ lem
--                k : q ≺' p
--                k = pr₁ (pr₂ lem)
--                k' : [ q ] ≺⁻ [ p ]
--                k' = ⌜ ≺⁻-≃-≺' {q} {p} ⌝⁻¹ k
--                e : f̃ q ≡ y
--                e = pr₂ (pr₂ lem)
--                e' : f⁺ [ q ] ≡ y
--                e' = f⁺ [ q ] ≡⟨ f⁺-≡-f̃ q ⟩
--                     f̃    q   ≡⟨ e ⟩
--                     y        ∎

-- \end{code}
