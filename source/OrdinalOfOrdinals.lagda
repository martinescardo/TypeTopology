Martin Escardo, August 2018

The ordinal of ordinals. Based on the HoTT Book, with a few
modifications in some of the definitions and arguments.

This is an example where we are studying sets only, but the
univalence axiom is needed.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module OrdinalOfOrdinals
       (fe : FunExt)
       where

open import SpartanMLTT

open import OrdinalNotions hiding (_≤_)
open import OrdinalsType
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Retracts
open import UF-Embeddings
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Yoneda
open import UF-Univalence

\end{code}

Maps of ordinals. A simulation gives a notion of embedding of
ordinals, making them into a poset, as proved below.

\begin{code}

is-order-preserving
 is-monotone
 is-order-reflecting
 is-order-embedding
 is-order-equiv
 is-initial-segment
 is-simulation       : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇

is-order-preserving α β f = (x y : ⟨ α ⟩) → x ≺⟨ α ⟩ y → f x ≺⟨ β ⟩ f y

is-monotone α β f         = (x y : ⟨ α ⟩) → x ≼⟨ α ⟩ y → f x ≼⟨ β ⟩ f y

is-order-reflecting α β f = (x y : ⟨ α ⟩) → f x ≺⟨ β ⟩ f y → x ≺⟨ α ⟩ y

is-order-embedding  α β f = is-order-preserving α β f × is-order-reflecting α β f

is-order-equiv      α β f = is-order-preserving α β f
                          × (Σ e ꞉ is-equiv f , is-order-preserving β α (inverse f e))

is-initial-segment  α β f = (x : ⟨ α ⟩) (y : ⟨ β ⟩)
                          → y ≺⟨ β ⟩ f x → Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ≡ y)

is-simulation       α β f = is-initial-segment α β f × is-order-preserving α β f



order-equivs-are-simulations : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (f : ⟨ α ⟩ → ⟨ β ⟩)
                             → is-order-equiv α β f
                             → is-simulation α β f
order-equivs-are-simulations α β f (p , e , q) = h (equivs-are-qinvs f e) q , p
 where
  h : (d : qinv f)
    → is-order-preserving β α (pr₁ d)
    → is-initial-segment α β f
  h (g , ε , η) q x y l = g y , transport (λ - → g y ≺⟨ α ⟩ -) (ε x) m , η y
   where
    m : g y ≺⟨ α ⟩ g (f x)
    m = q y (f x) l

order-preservation-is-prop : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (f : ⟨ α ⟩ → ⟨ β ⟩)
                           → is-prop (is-order-preserving α β f)
order-preservation-is-prop {𝓤} {𝓥} α β f =
 Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥))
   (λ x → Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥))
             (λ y → Π-is-prop (fe 𝓤 𝓥)
                      (λ l → Prop-valuedness β (f x) (f y))))

order-reflection-is-prop : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (f : ⟨ α ⟩ → ⟨ β ⟩)
                           → is-prop (is-order-reflecting α β f)
order-reflection-is-prop {𝓤} {𝓥} α β f =
 Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥))
   (λ x → Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥))
             (λ y → Π-is-prop (fe 𝓥 𝓤)
                      (λ l → Prop-valuedness α x y)))

being-order-embedding-is-prop : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (f : ⟨ α ⟩ → ⟨ β ⟩)
                                → is-prop (is-order-embedding α β f)
being-order-embedding-is-prop α β f = ×-is-prop
                                       (order-preservation-is-prop α β f)
                                       (order-reflection-is-prop α β f)

being-order-equiv-is-prop : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (f : ⟨ α ⟩ → ⟨ β ⟩)
                          → is-prop (is-order-equiv α β f)
being-order-equiv-is-prop α β f = ×-is-prop
                                   (order-preservation-is-prop α β f)
                                   (Σ-is-prop
                                      (being-equiv-is-prop fe f)
                                      (λ e → order-preservation-is-prop β α
                                                (back-eqtofun (f , e))))

simulations-are-lc : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (f : ⟨ α ⟩ → ⟨ β ⟩)
                   → is-simulation α β f
                   → left-cancellable f
simulations-are-lc α β f (i , p) {x} {y} = φ x y (Well-foundedness α x) (Well-foundedness α y)
 where
  φ : ∀ x y → is-accessible (underlying-order α) x → is-accessible (underlying-order α) y
    → f x ≡ f y → x ≡ y
  φ x y (next .x s) (next .y t) r = Extensionality α x y g h
   where
    g : (u : ⟨ α ⟩) → u ≺⟨ α ⟩ x → u ≺⟨ α ⟩ y
    g u l = d
     where
      a : f u ≺⟨ β ⟩ f y
      a = transport (λ - → f u ≺⟨ β ⟩ -) r (p u x l)

      b : Σ v ꞉ ⟨ α ⟩ , (v ≺⟨ α ⟩ y) × (f v ≡ f u)
      b = i y (f u) a

      c : u ≡ pr₁ b
      c = φ u (pr₁ b) (s u l) (t (pr₁ b) (pr₁(pr₂ b))) ((pr₂ (pr₂ b))⁻¹)

      d : u ≺⟨ α ⟩ y
      d = transport (λ - → - ≺⟨ α ⟩ y) (c ⁻¹) (pr₁(pr₂ b))

    h : (u : ⟨ α ⟩) → u ≺⟨ α ⟩ y → u ≺⟨ α ⟩ x
    h u l = d
     where
      a : f u ≺⟨ β ⟩ f x
      a = transport (λ - → f u ≺⟨ β ⟩ -) (r ⁻¹) (p u y l)

      b : Σ v ꞉ ⟨ α ⟩ , (v ≺⟨ α ⟩ x) × (f v ≡ f u)
      b = i x (f u) a

      c : pr₁ b ≡ u
      c = φ (pr₁ b) u (s (pr₁ b) (pr₁(pr₂ b))) (t u l) (pr₂(pr₂ b))

      d : u ≺⟨ α ⟩ x
      d = transport (λ - → - ≺⟨ α ⟩ x) c (pr₁(pr₂ b))

being-initial-segment-is-prop : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (f : ⟨ α ⟩ → ⟨ β ⟩)
                              → is-order-preserving α β f
                              → is-prop (is-initial-segment α β f)
being-initial-segment-is-prop {𝓤} {𝓥} α β f p i =
 (Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥))
    λ x → Π-is-prop (fe 𝓥 (𝓤 ⊔ 𝓥))
            λ z → Π-is-prop (fe 𝓥 (𝓤 ⊔ 𝓥))
                    λ l → φ x z l) i
  where
   φ : ∀ x y → y ≺⟨ β ⟩ f x → is-prop (Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ≡ y))
   φ x y l (x' , (m , r)) (x'' , (m' , r')) = to-Σ-≡ (a , b)
    where
     c : f x' ≡ f x''
     c = r ∙ r' ⁻¹

     a : x' ≡ x''
     a = simulations-are-lc α β f (i , p) c

     b : transport (λ - →  (- ≺⟨ α ⟩ x) × (f - ≡ y)) a (m , r) ≡ m' , r'
     b = ×-is-prop
          (Prop-valuedness α x'' x)
          (extensionally-ordered-types-are-sets
            (underlying-order β) fe
            (Prop-valuedness β)
            (Extensionality β)) _ _

\end{code}

The simulations make the ordinals into a poset:

\begin{code}

being-simulation-is-prop : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (f : ⟨ α ⟩ → ⟨ β ⟩)
                         → is-prop (is-simulation α β f)
being-simulation-is-prop α β f = ×-prop-criterion
                                     (being-initial-segment-is-prop α β f ,
                                      λ _ → order-preservation-is-prop α β f)

at-most-one-simulation : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (f f' : ⟨ α ⟩ → ⟨ β ⟩)
                       → is-simulation α β f
                       → is-simulation α β f'
                       → f ∼ f'
at-most-one-simulation α β f f' (i , p) (i' , p') x = φ x (Well-foundedness α x)
 where
  φ : ∀ x → is-accessible (underlying-order α) x → f x ≡ f' x
  φ x (next .x u) = Extensionality β (f x) (f' x) a b
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
      m = p' y x (pr₁(pr₂ s))

      t : f' y ≡ z
      t = (IH y (pr₁(pr₂ s)))⁻¹ ∙ pr₂(pr₂ s)

    b : (z : ⟨ β ⟩) → z ≺⟨ β ⟩ f' x → z ≺⟨ β ⟩ f x
    b z l = transport (λ - → - ≺⟨ β ⟩ f x) t m
     where
      s : Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × (f' y ≡ z)
      s = i' x z l

      y : ⟨ α ⟩
      y = pr₁ s

      m : f y ≺⟨ β ⟩ f x
      m = p y x (pr₁(pr₂ s))

      t : f y ≡ z
      t = IH y (pr₁(pr₂ s)) ∙ pr₂(pr₂ s)

_⊴_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
α ⊴ β = Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-simulation α β f

⊴-prop-valued : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → is-prop (α ⊴ β)
⊴-prop-valued {𝓤} {𝓥} α β (f , s) (g , t) =
 to-Σ-≡ (dfunext (fe 𝓤 𝓥) (at-most-one-simulation α β f g s t) ,
         being-simulation-is-prop α β g _ _)

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
  k x z l = pr₁ b , pr₁(pr₂ b) , (ap g (pr₂(pr₂ b)) ∙ pr₂(pr₂ a))
   where
    a : Σ y ꞉ ⟨ β ⟩ , (y ≺⟨ β ⟩ f x) × (g y ≡ z)
    a = j (f x) z l

    y : ⟨ β ⟩
    y = pr₁ a

    b : Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ x) × (f x' ≡ y)
    b = i x y (pr₁ (pr₂ a))

_≃ₒ_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
α ≃ₒ β = Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-order-equiv α β f

≃ₒ-gives-≃ : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → α ≃ₒ β → ⟨ α ⟩ ≃ ⟨ β ⟩
≃ₒ-gives-≃ α β (f , p , e , q) = (f , e)

≃ₒ-prop-valued : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
               → is-prop (α ≃ₒ β)
≃ₒ-prop-valued {𝓤} {𝓥} α β (f , p , e , q) (f' , p' , e' , q')  =
  to-Σ-≡ (dfunext (fe 𝓤 𝓥) (at-most-one-simulation α β f f'
                           (order-equivs-are-simulations α β f  (p  , e ,  q))
                           (order-equivs-are-simulations α β f' (p' , e' , q'))) ,
          being-order-equiv-is-prop α β _ _ _)

ordinal-equiv-gives-bisimilarity : (α β : Ordinal 𝓤)
                                 → α ≃ₒ β → (α ⊴ β) × (β ⊴ α)
ordinal-equiv-gives-bisimilarity α β (f , p , e , q) =
 (f , order-equivs-are-simulations α β f (p , e , q)) ,
 (g , order-equivs-are-simulations β α g (q , d , p))
 where
  g : ⟨ β ⟩ → ⟨ α ⟩
  g = ⌜ ≃-sym (f , e) ⌝

  d : is-equiv g
  d = ⌜⌝-is-equiv (≃-sym (f , e))

bisimilarity-gives-ordinal-equiv : (α β : Ordinal 𝓤)
                                 → α ⊴ β → β ⊴ α → α ≃ₒ β
bisimilarity-gives-ordinal-equiv α β (f , s) (g , t) =
 f , pr₂ s , qinvs-are-equivs f (g , ε , η) , pr₂ t
 where
  ηs : is-simulation β β (f ∘ g)
  ηs = pr₂ (⊴-trans β α β (g , t) (f , s))

  η : (y : ⟨ β ⟩) → f (g y) ≡ y
  η = at-most-one-simulation β β (f ∘ g) id ηs (pr₂ (⊴-refl β))

  εs : is-simulation α α (g ∘ f)
  εs = pr₂ (⊴-trans α β α (f , s) (g , t))

  ε : (x : ⟨ α ⟩) → g (f x) ≡ x
  ε = at-most-one-simulation α α (g ∘ f) id εs (pr₂ (⊴-refl α))

≃ₒ-refl : (α : Ordinal 𝓤) → α ≃ₒ α
≃ₒ-refl α = id , (λ x y → id) , id-is-equiv ⟨ α ⟩ , (λ x y → id)

idtoeqₒ : (α β : Ordinal 𝓤) → α ≡ β → α ≃ₒ β
idtoeqₒ α .α refl = ≃ₒ-refl α

eqtoidₒ : is-univalent 𝓤 → (α β : Ordinal 𝓤)
        → α ≃ₒ β → α ≡ β
eqtoidₒ {𝓤} ua α β (f , p , e , q) = JEq ua ⟨ α ⟩ A a ⟨ β ⟩ (f , e) (structure β) p q
 where
  A : (Y : 𝓤 ̇ ) → ⟨ α ⟩ ≃ Y → 𝓤 ⁺ ̇
  A Y e = (σ : OrdinalStructure Y)
        → is-order-preserving α (Y , σ) ⌜ e ⌝
        → is-order-preserving (Y , σ) α (back-eqtofun e)
        → α ≡ (Y , σ)

  a : A ⟨ α ⟩ (≃-refl ⟨ α ⟩)
  a σ φ ψ = g
   where
    b : ∀ x x' → (x ≺⟨ α ⟩ x') ≡ (x ≺⟨ ⟨ α ⟩ , σ ⟩ x')
    b x x' = univalence-gives-propext ua
              (Prop-valuedness α x x')
              (Prop-valuedness (⟨ α ⟩ , σ) x x')
              (φ x x')
              (ψ x x')

    c : underlying-order α ≡ underlying-order (⟨ α ⟩ , σ)
    c = dfunext (fe 𝓤 (𝓤 ⁺)) (λ x → dfunext (fe 𝓤 (𝓤 ⁺)) (b x))

    d : structure α ≡ σ
    d = pr₁-lc (λ {_<_} → being-well-order-is-prop _<_ fe) c

    g : α ≡ (⟨ α ⟩ , σ)
    g = to-Σ-≡' d

UAₒ : is-univalent 𝓤
    → (α β : Ordinal 𝓤) → is-equiv (idtoeqₒ α β)
UAₒ {𝓤} ua α = nats-with-sections-are-equivs α
                 (idtoeqₒ α)
                 (λ β → eqtoidₒ ua α β , η β)
 where
  η : (β : Ordinal 𝓤) (e : α ≃ₒ β)
    → idtoeqₒ α β (eqtoidₒ ua α β e) ≡ e
  η β e = ≃ₒ-prop-valued α β (idtoeqₒ α β (eqtoidₒ ua α β e)) e

type-of-ordinals-is-set : is-univalent 𝓤 → is-set (Ordinal 𝓤)
type-of-ordinals-is-set {𝓤} ua {α} {β} = equiv-to-prop
                                             (idtoeqₒ α β , UAₒ ua α β)
                                             (≃ₒ-prop-valued α β)

UAₒ-≃ : is-univalent 𝓤
      → (α β : Ordinal 𝓤) → (α ≡ β) ≃ (α ≃ₒ β)
UAₒ-≃ ua α β = idtoeqₒ α β , UAₒ ua α β

\end{code}

One of the many applications of the univalence axiom is to manufacture
examples of types which are not sets. Here we have instead used it to
prove that a certain type is a set.

A corollary of the above is that the ordinal order _⊴_ is
antisymmetric.

\begin{code}

⊴-antisym : is-univalent 𝓤 → (α β : Ordinal 𝓤)
          → α ⊴ β → β ⊴ α → α ≡ β
⊴-antisym {𝓤} ua α β l m = eqtoidₒ ua α β (bisimilarity-gives-ordinal-equiv α β l m)

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
    f x (next .x s) l = next (x , l) (λ σ m → f (pr₁ σ) (s (pr₁ σ) m) (pr₂ σ))

  e : is-extensional _<_
  e (x , l) (y , m) f g =
   to-Σ-≡ (Extensionality α x y
             (λ u n → f (u , Transitivity α u x a n l) n)
             (λ u n → g (u , Transitivity α u y a n m) n) ,
          Prop-valuedness α y a _ _)

  t : is-transitive _<_
  t (x , _) (y , _) (z , _) l m = Transitivity α x y z l m

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
       → (α ↓ a)  ⊴  (α ↓ b ) → a ≼⟨ α ⟩ b
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
  (↓-⊴-lc α a b (transport (λ - → (α ↓ a) ⊴ -) p (⊴-refl (α ↓ a))))
  (↓-⊴-lc α b a (back-transport (λ - → (α ↓ b) ⊴ -) p (⊴-refl (α ↓ b))))

\end{code}

We are now ready to make the type of ordinals into an ordinal. We fix
a univalent universe U.

\begin{code}

module ordinal-of-ordinals {𝓤} (ua : is-univalent 𝓤) where

 _⊲_ : Ordinal 𝓤 → Ordinal 𝓤 → 𝓤 ⁺ ̇
 α ⊲ β = Σ b ꞉ ⟨ β ⟩ , α ≡ (β ↓ b)

 ⊲-prop-valued : (α β : Ordinal 𝓤) → is-prop (α ⊲ β)
 ⊲-prop-valued α β (b , p) (b' , p') = to-Σ-≡ (r , s)
  where
   r : b ≡ b'
   r = ↓-lc β b b' (p ⁻¹ ∙ p')

   s : transport (λ - → α ≡ (β ↓ -)) r p ≡ p'
   s = type-of-ordinals-is-set ua _ _

\end{code}

 NB. We could instead define α ⊲ β to mean that we have b with
 α ≃ₒ (β ↓ b), or with α ⊴ (β ↓ b) and (β ↓ b) ⊴ α, by antisymmetry,
 and these two alternative, equivalent, definitions make ⊲ to have
 values in the universe 𝓤 rather than the next universe 𝓤 ⁺.

 Added 23 December 2020. The previous observation turns out to be
 useful to resize down the relation _⊲_ in certain applications. So we
 make it official:

\begin{code}

 open import UF-EquivalenceExamples

 _⊲⁻_ : Ordinal 𝓤 → Ordinal 𝓤 → 𝓤 ̇
 α ⊲⁻ β = Σ b ꞉ ⟨ β ⟩ , α ≃ₒ (β ↓ b)

 ⊲-is-equivalent-to-⊲⁻ : (α β : Ordinal 𝓤) → (α ⊲ β) ≃ (α ⊲⁻ β)
 ⊲-is-equivalent-to-⊲⁻ α β = Σ-cong (λ (b : ⟨ β ⟩) → UAₒ-≃ ua α (β ↓ b))

\end{code}

 Back to the past.

 A lower set of a lower set is a lower set:

\begin{code}

 iterated-↓ : (α : Ordinal 𝓤) (a b : ⟨ α ⟩) (l : b ≺⟨ α ⟩ a)
            → ((α ↓ a ) ↓ (b , l)) ≡ (α ↓ b)
 iterated-↓ α a b l = ⊴-antisym ua ((α ↓ a) ↓ (b , l)) (α ↓ b) (φ α a b l) (ψ α a b l)
  where
   φ : (α : Ordinal 𝓤) (b u : ⟨ α ⟩) (l : u ≺⟨ α ⟩ b)
     → ((α ↓ b ) ↓ (u , l)) ⊴ (α ↓ u)
   φ α b u l = f , (i , p)
    where
     f : ⟨ (α ↓ b) ↓ (u , l) ⟩ → ⟨ α ↓ u ⟩
     f ((x , m) , n) = x , n

     i : (w : ⟨ (α ↓ b) ↓ (u , l) ⟩) (t : ⟨ α ↓ u ⟩)
       → t ≺⟨ α ↓ u ⟩ f w
       → Σ w' ꞉ ⟨ (α ↓ b) ↓ (u , l) ⟩ , (w' ≺⟨ (α ↓ b) ↓ (u , l) ⟩ w) × (f w' ≡ t)
     i ((x , m) , n) (x' , m') n' = ((x' , Transitivity α x' u b m' l) , m') ,
                                    (n' , refl)

     p : (w w' : ⟨ (α ↓ b) ↓ (u , l) ⟩) → w ≺⟨ (α ↓ b) ↓ (u , l) ⟩ w' → f w ≺⟨ α ↓ u ⟩ (f w')
     p w w' = id

   ψ : (α : Ordinal 𝓤) (b u : ⟨ α ⟩) (l : u ≺⟨ α ⟩ b)
     → (α ↓ u) ⊴ ((α ↓ b ) ↓ (u , l))
   ψ α b u l = f , (i , p)
    where
     f : ⟨ α ↓ u ⟩ → ⟨ (α ↓ b) ↓ (u , l) ⟩
     f (x , n) = ((x , Transitivity α x u b n l) , n)

     i : (t : ⟨ α ↓ u ⟩) (w : ⟨ (α ↓ b) ↓ (u , l) ⟩)
       → w ≺⟨ (α ↓ b) ↓ (u , l) ⟩ f t → Σ t' ꞉ ⟨ α ↓ u ⟩ , (t' ≺⟨ α ↓ u ⟩ t) × (f t' ≡ w)
     i (x , n) ((x' , m') , n') o = (x' , n') ,
                                    (o , to-Σ-≡ (to-Σ-≡' (Prop-valuedness α x' b _ _) ,
                                                 Prop-valuedness α x' u _ _))

     p : (t t' : ⟨ α ↓ u ⟩) → t ≺⟨ α ↓ u ⟩ t' → f t ≺⟨ (α ↓ b) ↓ (u , l) ⟩ f t'
     p t t' = id

\end{code}

 Therefore the map (α ↓ -) reflects and preserves order:

\begin{code}

 ↓-reflects-order : (α : Ordinal 𝓤) (a b : ⟨ α ⟩)
                  → (α ↓ a) ⊲ (α ↓ b) → a ≺⟨ α ⟩ b
 ↓-reflects-order α a b ((u , l) , p) = back-transport (λ - → - ≺⟨ α ⟩ b) r l
  where
   q : (α ↓ a) ≡ (α ↓ u)
   q = p ∙ iterated-↓ α b u l

   r : a ≡ u
   r = ↓-lc α a u q

 ↓-preserves-order : (α : Ordinal 𝓤) (a b : ⟨ α ⟩)
                   → a ≺⟨ α ⟩ b → (α ↓ a) ⊲ (α ↓ b)
 ↓-preserves-order α a b l = (a , l) , ((iterated-↓ α b a l)⁻¹)

\end{code}

 It remains to show that _⊲_ is a well-order:

\begin{code}

 ↓-accessible : (α : Ordinal 𝓤) (a : ⟨ α ⟩)
              → is-accessible _⊲_ (α ↓ a)
 ↓-accessible α a = f a (Well-foundedness α a)
  where
   f : (a : ⟨ α ⟩) → is-accessible (underlying-order α) a → is-accessible _⊲_ (α ↓ a)
   f a (next .a s) = next (α ↓ a) g
    where
     IH : (b : ⟨ α ⟩) → b ≺⟨ α ⟩ a → is-accessible _⊲_ (α ↓ b)
     IH b l = f b (s b l)

     g : (β : Ordinal 𝓤) → β ⊲ (α ↓ a) → is-accessible _⊲_ β
     g β ((b , l) , p) = back-transport (is-accessible _⊲_) q (IH b l)
      where
       q : β ≡ (α ↓ b)
       q = p ∙ iterated-↓ α a b l

 ⊲-well-founded : is-well-founded _⊲_
 ⊲-well-founded α = next α g
  where
   g : (β : Ordinal 𝓤) → β ⊲ α → is-accessible _⊲_ β
   g β (b , p) = back-transport (is-accessible _⊲_) p (↓-accessible α b)

 ⊲-extensional : is-extensional _⊲_
 ⊲-extensional α β f g = ⊴-antisym ua α β
                            ((λ x → pr₁(φ x)) , i , p)
                            ((λ y → pr₁(γ y)) , j , q)
  where
   φ : (x : ⟨ α ⟩) → Σ y ꞉ ⟨ β ⟩ , α ↓ x ≡ β ↓ y
   φ x = f (α ↓ x) (x , refl)

   γ : (y : ⟨ β ⟩) → Σ x ꞉ ⟨ α ⟩ , β ↓ y ≡ α ↓ x
   γ y = g (β ↓ y) (y , refl)

   η : (x : ⟨ α ⟩) → pr₁(γ (pr₁(φ x))) ≡ x
   η x = (↓-lc α x (pr₁(γ (pr₁(φ x)))) a)⁻¹
    where
     a : (α ↓ x) ≡ (α ↓ pr₁ (γ (pr₁ (φ x))))
     a = pr₂(φ x) ∙ pr₂(γ (pr₁(φ x)))

   ε : (y : ⟨ β ⟩) → pr₁(φ (pr₁(γ y))) ≡ y
   ε y = (↓-lc β y (pr₁(φ (pr₁(γ y)))) a)⁻¹
    where
     a : (β ↓ y) ≡ (β ↓ pr₁ (φ (pr₁ (γ y))))
     a = pr₂(γ y) ∙ pr₂(φ (pr₁(γ y)))

   p : is-order-preserving α β (λ x → pr₁(φ x))
   p x x' l = ↓-reflects-order β (pr₁ (φ x)) (pr₁ (φ x')) b
    where
     a : (α ↓ x) ⊲ (α ↓ x')
     a = ↓-preserves-order α x x' l

     b : (β ↓ pr₁ (φ x)) ⊲ (β ↓ pr₁ (φ x'))
     b = transport₂ _⊲_ (pr₂ (φ x)) (pr₂ (φ x')) a

   q : is-order-preserving β α (λ y → pr₁(γ y))
   q y y' l = ↓-reflects-order α (pr₁ (γ y)) (pr₁ (γ y')) b
    where
     a : (β ↓ y) ⊲ (β ↓ y')
     a = ↓-preserves-order β y y' l

     b : (α ↓ pr₁ (γ y)) ⊲ (α ↓ pr₁ (γ y'))
     b = transport₂ _⊲_ (pr₂ (γ y)) (pr₂ (γ y')) a

   i : is-initial-segment α β (λ x → pr₁(φ x))
   i x y l = pr₁(γ y) , transport (λ - → pr₁ (γ y) ≺⟨ α ⟩ -) (η x) a , ε y
    where
     a : pr₁ (γ y) ≺⟨ α ⟩ (pr₁ (γ (pr₁ (φ x))))
     a = q y (pr₁ (φ x)) l

   j : is-initial-segment β α (λ y → pr₁(γ y))
   j y x l = pr₁(φ x) , transport (λ - → pr₁ (φ x) ≺⟨ β ⟩ -) (ε y) a , η x
    where
     a : pr₁ (φ x) ≺⟨ β ⟩ (pr₁ (φ (pr₁ (γ y))))
     a = p x (pr₁ (γ y)) l

 ⊲-transitive : is-transitive _⊲_
 ⊲-transitive α β φ (a , p) (b , q) = pr₁ (transport (λ - → ⟨ - ⟩) q a) , (r ∙ s)
  where
   t : (ψ : Ordinal 𝓤) (q : β ≡ ψ) → (β ↓ a) ≡ ψ ↓ transport (λ - → ⟨ - ⟩) q a
   t ψ refl = refl

   r : α ≡ ((φ ↓ b) ↓ transport (λ - → ⟨ - ⟩) q a)
   r = p ∙ t (φ ↓ b) q

   s : ((φ ↓ b) ↓ transport (λ - → ⟨ - ⟩) q a) ≡ (φ ↓ pr₁ (transport (λ - → ⟨ - ⟩) q a))
   s = iterated-↓ φ b (pr₁(transport (λ - → ⟨ - ⟩) q a)) (pr₂(transport (λ - → ⟨ - ⟩) q a))

 ⊲-well-order : is-well-order _⊲_
 ⊲-well-order = ⊲-prop-valued , ⊲-well-founded , ⊲-extensional , ⊲-transitive

\end{code}

 We denote the ordinal of ordinals in the universe 𝓤 by O. It lives in
 the next universe 𝓤 ⁺.

\begin{code}

 O : Ordinal (𝓤 ⁺)
 O = Ordinal 𝓤 , _⊲_ , ⊲-well-order

\end{code}

 Any ordinal in O is embedded in O as an initial segment:

\begin{code}

 ordinals-in-O-are-embedded-in-O : (α : ⟨ O ⟩) → α ⊴ O
 ordinals-in-O-are-embedded-in-O α = (λ x → α ↓ x) , i , ↓-preserves-order α
  where
   i : is-initial-segment α O (λ x → α ↓ x)
   i x β ((u , l) , p) = u , l , ((p ∙ iterated-↓ α x u l)⁻¹)

\end{code}

 Any ordinal in O is a lower set of O:

\begin{code}

 ordinals-in-O-are-lowersets-of-O : (α : ⟨ O ⟩) → α ≃ₒ (O ↓ α)
 ordinals-in-O-are-lowersets-of-O α = f , p , ((g , η) , (g , ε)) , q
  where
   f : ⟨ α ⟩ → ⟨ O ↓ α ⟩
   f x = α ↓ x , x , refl

   p : is-order-preserving α (O ↓ α) f
   p x y l = (x , l) , ((iterated-↓ α y x l)⁻¹)

   g : ⟨ O ↓ α ⟩ → ⟨ α ⟩
   g (β , x , r) = x

   η : (σ : ⟨ O ↓ α ⟩) → f (g σ) ≡ σ
   η (.(α ↓ x) , x , refl) = refl

   ε : (x : ⟨ α ⟩) → g (f x) ≡ x
   ε x = refl

   q : is-order-preserving (O ↓ α) α g
   q (.(α ↓ x) , x , refl) (.(α ↓ x') , x' , refl) = ↓-reflects-order α x x'

\end{code}

Here are some additional observations about the various maps of
ordinals:

\begin{code}

lc-initial-segments-are-order-reflecting : (α β : Ordinal 𝓤) (f : ⟨ α ⟩ → ⟨ β ⟩)
                                         → is-initial-segment α β f
                                         → left-cancellable f
                                         → is-order-reflecting α β f
lc-initial-segments-are-order-reflecting α β f i c x y l = m
 where
  a : Σ x' ꞉ ⟨ α ⟩ , (x' ≺⟨ α ⟩ y) × (f x' ≡ f x)
  a = i y (f x) l
  m : x ≺⟨ α ⟩ y
  m = transport (λ - → - ≺⟨ α ⟩ y) (c (pr₂(pr₂ a))) (pr₁(pr₂ a))

simulations-are-order-reflecting : (α β : Ordinal 𝓤) (f : ⟨ α ⟩ → ⟨ β ⟩)
                                 → is-simulation α β f
                                 → is-order-reflecting α β f
simulations-are-order-reflecting α β f (i , p) = lc-initial-segments-are-order-reflecting α β f i
                                                   (simulations-are-lc α β f (i , p))

order-embeddings-are-lc : (α β : Ordinal 𝓤) (f : ⟨ α ⟩ → ⟨ β ⟩)
                        → is-order-embedding α β f
                        → left-cancellable f
order-embeddings-are-lc α β f (p , r) {x} {y} s = Extensionality α x y a b
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

order-embedings-are-embeddings : (α β : Ordinal 𝓤) (f : ⟨ α ⟩ → ⟨ β ⟩)
                               → is-order-embedding α β f
                               → is-embedding f
order-embedings-are-embeddings α β f (p , r) =
  lc-maps-into-sets-are-embeddings f
     (order-embeddings-are-lc α β f (p , r))
     (well-ordered-types-are-sets (underlying-order β) fe (is-well-ordered β))

simulations-are-monotone : (α β : Ordinal 𝓤) (f : ⟨ α ⟩ → ⟨ β ⟩)
                         → is-simulation α β f
                         → is-monotone α β f
simulations-are-monotone α β f (i , p) = φ
 where
  φ : (x y : ⟨ α ⟩) → ((z : ⟨ α ⟩) → z ≺⟨ α ⟩ x → z ≺⟨ α ⟩ y)
                    → (t : ⟨ β ⟩) → t ≺⟨ β ⟩ f x → t ≺⟨ β ⟩ f y
  φ x y ψ t l = transport (λ - → - ≺⟨ β ⟩ f y) b d
   where
    z : ⟨ α ⟩
    z = pr₁ (i x t l)

    a : z ≺⟨ α ⟩ x
    a = pr₁(pr₂(i x t l))

    b : f z ≡ t
    b = pr₂(pr₂(i x t l))

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
 fact = under𝟙 , i , p
  where
   i : (x : ⟨ ℕₒ +ₒ 𝟙ₒ ⟩) (y : ⟨ ℕ∞ₒ ⟩)
     → y ≺⟨ ℕ∞ₒ ⟩ under𝟙 x → Σ x' ꞉ ⟨ ℕₒ +ₒ 𝟙ₒ ⟩ , (x' ≺⟨ ℕₒ +ₒ 𝟙ₒ ⟩ x) × (under𝟙 x' ≡ y)
   i (inl m) y (n , r , l) = inl n , ⊏-gives-< n m l , (r ⁻¹)
   i (inr *) y (n , r , l) = inl n , * , (r ⁻¹)

   p : (x y : ⟨ ℕₒ +ₒ 𝟙ₒ ⟩) → x ≺⟨ ℕₒ +ₒ 𝟙ₒ ⟩ y → under𝟙 x ≺⟨ ℕ∞ₒ ⟩ under𝟙 y
   p (inl n) (inl m) l = under-order-preserving n m l
   p (inl n) (inr *) * = ∞-≺-maximal n
   p (inr *) (inl m) l = 𝟘-elim l
   p (inr *) (inr *) l = 𝟘-elim l

 converse-fails-constructively : ℕ∞ₒ ⊴ (ℕₒ +ₒ 𝟙ₒ) → LPO
 converse-fails-constructively l = has-section-under𝟙-gives-LPO (equivs-have-sections under𝟙 e)
  where
   b : (ℕₒ +ₒ 𝟙ₒ) ≃ₒ ℕ∞ₒ
   b = bisimilarity-gives-ordinal-equiv (ℕₒ +ₒ 𝟙ₒ) ℕ∞ₒ fact l

   e : is-equiv under𝟙
   e = pr₂(≃ₒ-gives-≃ (ℕₒ +ₒ 𝟙ₒ) ℕ∞ₒ b)

 converse-fails-constructively-converse : LPO → ℕ∞ₒ ⊴ (ℕₒ +ₒ 𝟙ₒ)
 converse-fails-constructively-converse lpo = (λ x → under𝟙-inverse x (lpo x)) ,
                                              (λ x → i x (lpo x)) ,
                                              (λ x y → p x y (lpo x) (lpo y))
  where
   under𝟙-inverse-inl : (u : ℕ∞) (d : decidable(Σ n ꞉ ℕ , u ≡ under n))
                      → (m : ℕ) → u ≡ under m → under𝟙-inverse u d ≡ inl m
   under𝟙-inverse-inl .(under n) (inl (n , refl)) m q = ap inl (under-lc q)
   under𝟙-inverse-inl u          (inr g)          m q = 𝟘-elim (g (m , q))

   i : (x : ℕ∞) (d : decidable(Σ n ꞉ ℕ , x ≡ under n)) (y : ℕ + 𝟙)
     → y ≺⟨ ℕₒ +ₒ 𝟙ₒ ⟩ under𝟙-inverse x d
     → Σ x' ꞉ ℕ∞ , (x' ≺⟨ ℕ∞ₒ ⟩ x) × (under𝟙-inverse x' (lpo x') ≡ y)
   i .(under n) (inl (n , refl)) (inl m) l =
     under m , under-order-preserving m n l , under𝟙-inverse-inl (under m) (lpo (under m)) m refl
   i .(under n) (inl (n , refl)) (inr *) l = 𝟘-elim l
   i x (inr g) (inl n) * =
     under n ,
     transport (underlying-order ℕ∞ₒ (under n)) ((not-finite-is-∞ (fe 𝓤₀ 𝓤₀) (curry g)) ⁻¹) (∞-≺-maximal n) ,
     under𝟙-inverse-inl (under n) (lpo (under n)) n refl
   i x (inr g) (inr *) l = 𝟘-elim l

   p : (x y : ℕ∞)  (d : decidable(Σ n ꞉ ℕ , x ≡ under n)) (e : decidable(Σ m ꞉ ℕ , y ≡ under m))
     →  x ≺⟨ ℕ∞ₒ ⟩ y → under𝟙-inverse x d ≺⟨ ℕₒ +ₒ 𝟙ₒ ⟩ under𝟙-inverse y e
   p .(under n) .(under m) (inl (n , refl)) (inl (m , refl)) (k , r , l) =
    back-transport (λ - → - < m) (under-lc r) (⊏-gives-< k m l)
   p .(under n) y (inl (n , refl)) (inr f) l = *
   p x y (inr f) e (k , r , l) =
    𝟘-elim (∞-is-not-finite k ((not-finite-is-∞ (fe 𝓤₀ 𝓤₀) (curry f))⁻¹ ∙ r))

 corollary₁ : LPO → ℕ∞ₒ ≃ₒ (ℕₒ +ₒ 𝟙ₒ)
 corollary₁ lpo = bisimilarity-gives-ordinal-equiv ℕ∞ₒ (ℕₒ +ₒ 𝟙ₒ) (converse-fails-constructively-converse lpo) fact

 corollary₂ : LPO → ℕ∞ ≃ (ℕ + 𝟙)
 corollary₂ lpo = ≃ₒ-gives-≃ ℕ∞ₒ (ℕₒ +ₒ 𝟙ₒ) (corollary₁ lpo)

 corollary₃ : is-univalent 𝓤₀ → LPO → ℕ∞ₒ ≡ (ℕₒ +ₒ 𝟙ₒ)
 corollary₃ ua lpo = eqtoidₒ ua ℕ∞ₒ (ℕₒ +ₒ 𝟙ₒ) (corollary₁ lpo)

 corollary₄ : is-univalent 𝓤₀ → LPO → ℕ∞ ≡ (ℕ + 𝟙)
 corollary₄ ua lpo = eqtoid ua ℕ∞ (ℕ + 𝟙) (corollary₂ lpo)

\end{code}

TODO.

Question. Do we have (finite or arbitrary) joins of ordinals? Probably not.

Conjecture. We have bounded joins. The construction would be to take
the joint image in any upper bound.
