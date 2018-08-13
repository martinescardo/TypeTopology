Martin Escardo, August 2018

The ordinal of ordinals. Based on the HoTT Book, with a few
modifications in some of the arguments.

This is an example where we are studying sets only, but the
univalence axiom is needed.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module OrdinalOfOrdinals
       (fe : ∀ U V → funext U V)
       where

open import SpartanMLTT
open import OrdinalNotions hiding (_≤_)
open import Ordinals fe
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Retracts
open import UF-Embedding
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Yoneda
open import UF-Univalence

\end{code}

Maps of ordinals. A simulation gives a notion of embedding of
ordinals, making them into a poset, as proved below.

\begin{code}

is-order-preserving
 is-order-reflecting
 is-order-embedding
 is-order-equiv
 is-initial-segment
 is-simulation
  : ∀ {U V} → (α : Ordinal U) (β : Ordinal V) → (⟨ α ⟩ → ⟨ β ⟩) → U ⊔ V ̇

is-order-preserving α β f = (x y : ⟨ α ⟩) → x ≺⟨ α ⟩ y → f x ≺⟨ β ⟩ f y
is-order-reflecting α β f = (x y : ⟨ α ⟩) → f x ≺⟨ β ⟩ f y → x ≺⟨ α ⟩ y
is-order-embedding  α β f = is-order-preserving α β f × is-order-reflecting α β f
is-order-equiv      α β f = is-order-preserving α β f
                          × Σ \(e : is-equiv f) → is-order-preserving β α (back-eqtofun (f , e))
is-initial-segment  α β f = (x : ⟨ α ⟩) (y : ⟨ β ⟩)
                           → y ≺⟨ β ⟩ f x → Σ \(x' : ⟨ α ⟩) → (x' ≺⟨ α ⟩ x) × (f x' ≡ y)
is-simulation       α β f = is-initial-segment α β f × is-order-preserving α β f

order-equiv-simulation : ∀ {U V} (α : Ordinal U) (β : Ordinal V) (f : ⟨ α ⟩ → ⟨ β ⟩)
                       → is-order-equiv α β f
                       → is-simulation α β f
order-equiv-simulation α β f (p , e , q) = h (is-equiv-qinv f e) q , p
 where
  h : (d : qinv f)
    → is-order-preserving β α (pr₁ d)
    → is-initial-segment α β f
  h (g , gf , fg) q x y l = g y , transport (λ - → g y ≺⟨ α ⟩ -) (gf x) m , fg y
   where
    m : g y ≺⟨ α ⟩ g (f x)
    m = q y (f x) l

is-order-preserving-is-prop : ∀ {U V} (α : Ordinal U) (β : Ordinal V) (f : ⟨ α ⟩ → ⟨ β ⟩)
                            → is-prop (is-order-preserving α β f)
is-order-preserving-is-prop {U} {V} α β f =
 Π-is-prop (fe U (U ⊔ V))
   (λ x → Π-is-prop (fe U (U ⊔ V))
             (λ y → Π-is-prop (fe U V)
                      (λ l → Prop-valuedness β (f x) (f y))))

is-order-reflecting-is-prop : ∀ {U V} (α : Ordinal U) (β : Ordinal V) (f : ⟨ α ⟩ → ⟨ β ⟩)
                            → is-prop (is-order-reflecting α β f)
is-order-reflecting-is-prop {U} {V} α β f =
 Π-is-prop (fe U (U ⊔ V))
   (λ x → Π-is-prop (fe U (U ⊔ V))
             (λ y → Π-is-prop (fe V U)
                      (λ l → Prop-valuedness α x y)))

is-order-embedding-is-prop : ∀ {U V} (α : Ordinal U) (β : Ordinal V) (f : ⟨ α ⟩ → ⟨ β ⟩)
                           → is-prop (is-order-embedding α β f)
is-order-embedding-is-prop α β f = ×-is-prop
                                     (is-order-preserving-is-prop α β f)
                                     (is-order-reflecting-is-prop α β f)

is-order-equiv-is-prop : ∀ {U V} (α : Ordinal U) (β : Ordinal V) (f : ⟨ α ⟩ → ⟨ β ⟩)
                       → is-prop (is-order-equiv α β f)
is-order-equiv-is-prop α β f = ×-is-prop
                                 (is-order-preserving-is-prop α β f)
                                 (Σ-is-prop
                                    (is-prop-is-equiv fe f)
                                    (λ e → is-order-preserving-is-prop β α
                                              (back-eqtofun (f , e))))

iplc : ∀ {U V} (α : Ordinal U) (β : Ordinal V) (f : ⟨ α ⟩ → ⟨ β ⟩)
     → is-simulation α β f
     → left-cancellable f
iplc α β f (i , p) {x} {y} = φ x y (Well-foundedness α x) (Well-foundedness α y)
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
      b : Σ \(v : ⟨ α ⟩) → (v ≺⟨ α ⟩ y) × (f v ≡ f u)
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
      b : Σ \(v : ⟨ α ⟩) → (v ≺⟨ α ⟩ x) × (f v ≡ f u)
      b = i x (f u) a
      c : pr₁ b ≡ u
      c = φ (pr₁ b) u (s (pr₁ b) (pr₁(pr₂ b))) (t u l) (pr₂(pr₂ b))
      d : u ≺⟨ α ⟩ x
      d = transport (λ - → - ≺⟨ α ⟩ x) c (pr₁(pr₂ b))

is-initial-segment-is-prop : ∀ {U V} (α : Ordinal U) (β : Ordinal V) (f : ⟨ α ⟩ → ⟨ β ⟩)
                           → is-order-preserving α β f
                           → is-prop (is-initial-segment α β f)
is-initial-segment-is-prop {U} {V} α β f p i =
 (Π-is-prop (fe U (U ⊔ V))
    λ x → Π-is-prop (fe V (U ⊔ V))
            λ z → Π-is-prop (fe V (U ⊔ V))
                    λ l → φ x z l) i
  where
   φ : ∀ x y → y ≺⟨ β ⟩ f x → is-prop(Σ \(x' : ⟨ α ⟩) → (x' ≺⟨ α ⟩ x) × (f x' ≡ y))
   φ x y l (x' , (m , r)) (x'' , (m' , r')) = to-Σ-≡ (a , b)
    where
     c : f x' ≡ f x''
     c = r ∙ r' ⁻¹
     a : x' ≡ x''
     a = iplc α β f (i , p) c
     b : transport (λ - →  (- ≺⟨ α ⟩ x) × (f - ≡ y)) a (m , r) ≡ m' , r'
     b = ×-is-prop
          (Prop-valuedness α x'' x)
          (extensional-gives-is-set
            (underlying-order β) fe
            (Prop-valuedness β)
            (Extensionality β)) _ _

\end{code}

The simulations make the ordinals into a poset:

\begin{code}

is-simulation-is-prop : ∀ {U V} (α : Ordinal U) (β : Ordinal V) (f : ⟨ α ⟩ → ⟨ β ⟩)
                      → is-prop (is-simulation α β f)
is-simulation-is-prop α β f = ×-prop-criterion
                                (is-initial-segment-is-prop α β f ,
                                 λ _ → is-order-preserving-is-prop α β f)

at-most-one-simulation : ∀ {U V} (α : Ordinal U) (β : Ordinal V) (f f' : ⟨ α ⟩ → ⟨ β ⟩)
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
      s : Σ \(y : ⟨ α ⟩) → (y ≺⟨ α ⟩ x) × (f y ≡ z)
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
      s : Σ \(y : ⟨ α ⟩) → (y ≺⟨ α ⟩ x) × (f' y ≡ z)
      s = i' x z l
      y : ⟨ α ⟩
      y = pr₁ s
      m : f y ≺⟨ β ⟩ f x
      m = p y x (pr₁(pr₂ s))
      t : f y ≡ z
      t = IH y (pr₁(pr₂ s)) ∙ pr₂(pr₂ s)

_⊴_ : ∀ {U V} → Ordinal U → Ordinal V → U ⊔ V ̇
α ⊴ β = Σ \(f : ⟨ α ⟩ → ⟨ β ⟩) → is-simulation α β f

⊴-prop-valued : ∀ {U V} (α : Ordinal U) (β : Ordinal V) → is-prop (α ⊴ β)
⊴-prop-valued {U} {V} α β (f , s) (g , t) =
 to-Σ-≡ (dfunext (fe U V) (at-most-one-simulation α β f g s t) ,
         is-simulation-is-prop α β g _ _)

⊴-refl : ∀ {U} (α : Ordinal U) → α ⊴ α
⊴-refl α = id ,
           (λ x z l → z , l , refl) ,
           (λ x y l → l)

⊴-trans : ∀ {U V W} (α : Ordinal U) (β : Ordinal V) (γ : Ordinal W)
        → α ⊴ β → β ⊴ γ → α ⊴ γ
⊴-trans α β γ (f , i , p) (g , j , q) =
 g ∘ f ,
 k ,
 (λ x y l → q (f x) (f y) (p x y l))
 where
  k : (x : ⟨ α ⟩) (z : ⟨ γ ⟩) →  z ≺⟨ γ ⟩ (g (f x))
    → Σ \(x' : ⟨ α ⟩) → (x' ≺⟨ α ⟩ x) × (g (f x') ≡ z)
  k x z l = pr₁ b , pr₁(pr₂ b) , (ap g (pr₂(pr₂ b)) ∙ pr₂(pr₂ a))
   where
    a : Σ \(y : ⟨ β ⟩) → (y ≺⟨ β ⟩ f x) × (g y ≡ z)
    a = j (f x) z l
    y : ⟨ β ⟩
    y = pr₁ a
    b : Σ \(x' : ⟨ α ⟩) → (x' ≺⟨ α ⟩ x) × (f x' ≡ y)
    b = i x y (pr₁ (pr₂ a))

_≃ₒ_ : ∀ {U V} → Ordinal U → Ordinal V → U ⊔ V ̇
α ≃ₒ β = Σ \(f : ⟨ α ⟩ → ⟨ β ⟩) → is-order-equiv α β f

≃ₒ-prop-valued : ∀ {U V} (α : Ordinal U) (β : Ordinal V)
               → is-prop (α ≃ₒ β)
≃ₒ-prop-valued {U} {V} α β (f , p , e , q) (f' , p' , e' , q')  =
  to-Σ-≡
    (dfunext (fe U V) (at-most-one-simulation α β f f'
                        (order-equiv-simulation α β f  (p  , e ,  q))
                        (order-equiv-simulation α β f' (p' , e' , q'))) ,
    is-order-equiv-is-prop α β _ _ _)

equiv-bisimilar : ∀ {U} (α β : Ordinal U)
                → α ≃ₒ β → (α ⊴ β) × (β ⊴ α)
equiv-bisimilar α β (f , p , e , q) = (f , order-equiv-simulation α β f (p , e , q)) ,
                                      (g , order-equiv-simulation β α g (q , d , p))
 where
  g : ⟨ β ⟩ → ⟨ α ⟩
  g = pr₁ (≃-sym (f , e))
  d : is-equiv g
  d = pr₂ (≃-sym (f , e))

bisimilar-equiv : ∀ {U} (α β : Ordinal U)
                → α ⊴ β → β ⊴ α → α ≃ₒ β
bisimilar-equiv α β (f , s) (g , t) = f , pr₂ s , qinv-is-equiv f (g , gf , fg) , pr₂ t
 where
  fgs : is-simulation β β (f ∘ g)
  fgs = pr₂ (⊴-trans β α β (g , t) (f , s))
  fg : (y : ⟨ β ⟩) → f (g y) ≡ y
  fg = at-most-one-simulation β β (f ∘ g) id fgs (pr₂ (⊴-refl β))
  gfs : is-simulation α α (g ∘ f)
  gfs = pr₂ (⊴-trans α β α (f , s) (g , t))
  gf : (x : ⟨ α ⟩) → g (f x) ≡ x
  gf = at-most-one-simulation α α (g ∘ f) id gfs (pr₂ (⊴-refl α))

≃ₒ-refl : ∀ {U} (α : Ordinal U) → α ≃ₒ α
≃ₒ-refl α = id , (λ x y → id) , pr₂ (ideq ⟨ α ⟩) , (λ x y → id)

idtoeqₒ : ∀ {U} (α β : Ordinal U) → α ≡ β → α ≃ₒ β
idtoeqₒ α .α refl = ≃ₒ-refl α

eqtoidₒ : ∀ {U} → is-univalent U → (α β : Ordinal U)
        → α ≃ₒ β → α ≡ β
eqtoidₒ {U} ua α β (f , p , e , q) = JEq ua ⟨ α ⟩ A a ⟨ β ⟩ (f , e) (structure β) p q
 where
  A : (Y : U ̇) → ⟨ α ⟩ ≃ Y → U ′ ̇
  A Y e = (σ : OS Y)
        → is-order-preserving α (Y , σ) (eqtofun e)
        → is-order-preserving (Y , σ) α (back-eqtofun e)
        → α ≡ (Y , σ)
  a : A ⟨ α ⟩ (ideq ⟨ α ⟩)
  a σ φ ψ = g
   where
    b : ∀ x x' → (x ≺⟨ α ⟩ x') ≡ (x ≺⟨ ⟨ α ⟩ , σ ⟩ x')
    b x x' = UA-gives-propext ua
              (Prop-valuedness α x x')
              (Prop-valuedness (⟨ α ⟩ , σ) x x')
              (φ x x')
              (ψ x x')
    c : underlying-order α ≡ underlying-order (⟨ α ⟩ , σ)
    c = dfunext (fe U (U ′)) (λ x → dfunext (fe U (U ′)) (b x))
    d : structure α ≡ σ
    d = pr₁-lc (λ {_<_} → ordinal-is-prop _<_ fe) c
    g : α ≡ (⟨ α ⟩ , σ)
    g = to-Σ-≡' d

UAₒ : ∀ {U} → is-univalent U → (α β : Ordinal U)
    → is-equiv (idtoeqₒ α β)
UAₒ {U} ua α = nat-retraction-is-equiv α
                 (idtoeqₒ α)
                 (λ β → eqtoidₒ ua α β , η β)
 where
  η : (β : Ordinal U) (e : α ≃ₒ β)
    → idtoeqₒ α β (eqtoidₒ ua α β e) ≡ e
  η β e = ≃ₒ-prop-valued α β (idtoeqₒ α β (eqtoidₒ ua α β e)) e

Ordinal-is-set : ∀ {U} → is-univalent U → is-set (Ordinal U)
Ordinal-is-set {U} ua {α} {β} = equiv-to-subsingleton
                                 (idtoeqₒ α β , UAₒ ua α β)
                                 (≃ₒ-prop-valued α β)
\end{code}

One of the many applications of the univalence axiom is to manufacture
examples of types which are not sets. Here we have instead used it to
prove that a certain type is a set.

A corollary of the above is that the ordinal order _⊴_ is
antisymmetric.

\begin{code}

⊴-antisym : ∀ {U} → is-univalent U → (α β : Ordinal U)
          → α ⊴ β → β ⊴ α → α ≡ β
⊴-antisym {U} ua α β l m = eqtoidₒ ua α β (bisimilar-equiv α β l m)

\end{code}

Any lower set α ↓ a of a point a : ⟨ α ⟩ forms a (sub-)ordinal:

\begin{code}

_↓_ : ∀ {U} (α : Ordinal U) → ⟨ α ⟩ → Ordinal U
α ↓ a = (Σ \(x : ⟨ α ⟩) → x ≺⟨ α ⟩ a) , _<_ , p , w , e , t
 where
  _<_ : (Σ \(x : ⟨ α ⟩) → x ≺⟨ α ⟩ a) → (Σ \(x : ⟨ α ⟩) → x ≺⟨ α ⟩ a) → _ ̇
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
   to-Σ-≡
    (Extensionality α x y
      (λ u n → f (u , Transitivity α u x a n l) n)
      (λ u n → g (u , Transitivity α u y a n m) n) ,
    Prop-valuedness α y a _ _)
  t : is-transitive _<_
  t (x , _) (y , _) (z , _) l m = Transitivity α x y z l m

segment-inclusion : ∀ {U} (α : Ordinal U) (a : ⟨ α ⟩)
                  → ⟨ α ↓ a ⟩ → ⟨ α ⟩
segment-inclusion α a = pr₁

segment-inclusion-is-simulation : ∀ {U} (α : Ordinal U) (a : ⟨ α ⟩)
                                → is-simulation (α ↓ a) α (segment-inclusion α a)
segment-inclusion-is-simulation α a = i , p
 where
  i : is-initial-segment (α ↓ a) α (segment-inclusion α a)
  i (x , l) y m = (y , Transitivity α y x a m l) , m , refl
  p : is-order-preserving (α ↓ a) α (segment-inclusion α a)
  p x x' = id

segment-⊴ : ∀ {U} (α : Ordinal U) (a : ⟨ α ⟩)
          → (α ↓ a) ⊴ α
segment-⊴ α a = segment-inclusion α a , segment-inclusion-is-simulation α a

↓-⊴-lc : ∀ {U} (α : Ordinal U) (a b : ⟨ α ⟩)
       → (α ↓ a)  ⊴  (α ↓ b ) → a ≼⟨ α ⟩ b
↓-⊴-lc {U} α a b (f , s) u l = n
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

↓-lc : ∀ {U} (α : Ordinal U) (a b : ⟨ α ⟩)
     → α ↓ a ≡ α ↓ b → a ≡ b
↓-lc α a b p =
 Extensionality α a b
  (↓-⊴-lc α a b (transport (λ - → (α ↓ a) ⊴ -) p (⊴-refl (α ↓ a))))
  (↓-⊴-lc α b a (back-transport (λ - → (α ↓ b) ⊴ -) p (⊴-refl (α ↓ b))))

\end{code}

We are now ready to make the type of ordinals into an ordinal. We fix
a univalent universe U.

\begin{code}

module ordinal-of-ordinals {U} (ua : is-univalent U) where

 _⊲_ : Ordinal U → Ordinal U → U ′ ̇
 α ⊲ β = Σ \(b : ⟨ β ⟩) → α ≡ (β ↓ b)

 ⊲-prop-valued : (α β : Ordinal U) → is-prop (α ⊲ β)
 ⊲-prop-valued α β (b , p) (b' , p') = to-Σ-≡ (r , s)
  where
   r : b ≡ b'
   r = ↓-lc β b b' (p ⁻¹ ∙ p')
   s : transport (λ - → α ≡ (β ↓ -)) r p ≡ p'
   s = Ordinal-is-set ua _ _

\end{code}

 NB. We could instead define α ⊲ β to mean that we have b with
 α ≃ₒ (β ↓ b), or with α ⊴ (β ↓ b) and (β ↓ b) ⊴ α, by antisymmetry,
 and these two alternative, equivalent, definitions make ⊲ to have
 values in the universe U rather than the next universe U ′.

 A lower set of a lower set is a lower set:

\begin{code}

 iterated-↓ : (α : Ordinal U) (a b : ⟨ α ⟩) (l : b ≺⟨ α ⟩ a)
            → ((α ↓ a ) ↓ (b , l)) ≡ (α ↓ b)
 iterated-↓ α a b l = ⊴-antisym ua ((α ↓ a) ↓ (b , l)) (α ↓ b) (φ α a b l) (ψ α a b l)
  where
   φ : (α : Ordinal U) (b u : ⟨ α ⟩) (l : u ≺⟨ α ⟩ b)
     → ((α ↓ b ) ↓ (u , l)) ⊴ (α ↓ u)
   φ α b u l = f , (i , p)
    where
     f : ⟨ (α ↓ b) ↓ (u , l) ⟩ → ⟨ α ↓ u ⟩
     f ((x , m) , n) = x , n
     i : (w : ⟨ (α ↓ b) ↓ (u , l) ⟩) (t : ⟨ α ↓ u ⟩)
       → t ≺⟨ α ↓ u ⟩ f w
       → Σ \(w' : ⟨ (α ↓ b) ↓ (u , l) ⟩) → (w' ≺⟨ (α ↓ b) ↓ (u , l) ⟩ w) × (f w' ≡ t)
     i ((x , m) , n) (x' , m') n' = ((x' , Transitivity α x' u b m' l) , m') ,
                                    (n' , refl)
     p : (w w' : ⟨ (α ↓ b) ↓ (u , l) ⟩) → w ≺⟨ (α ↓ b) ↓ (u , l) ⟩ w' → f w ≺⟨ α ↓ u ⟩ (f w')
     p w w' = id

   ψ : (α : Ordinal U) (b u : ⟨ α ⟩) (l : u ≺⟨ α ⟩ b)
     → (α ↓ u) ⊴ ((α ↓ b ) ↓ (u , l))
   ψ α b u l = f , (i , p)
    where
     f : ⟨ α ↓ u ⟩ → ⟨ (α ↓ b) ↓ (u , l) ⟩
     f (x , n) = ((x , Transitivity α x u b n l) , n)
     i : (t : ⟨ α ↓ u ⟩) (w : ⟨ (α ↓ b) ↓ (u , l) ⟩)
       → w ≺⟨ (α ↓ b) ↓ (u , l) ⟩ f t → Σ \(t' : ⟨ α ↓ u ⟩) → (t' ≺⟨ α ↓ u ⟩ t) × (f t' ≡ w)
     i (x , n) ((x' , m') , n') o = (x' , n') ,
                                    (o , to-Σ-≡
                                          (to-Σ-≡' (Prop-valuedness α x' b _ _) ,
                                          Prop-valuedness α x' u _ _))
     p : (t t' : ⟨ α ↓ u ⟩) → t ≺⟨ α ↓ u ⟩ t' → f t ≺⟨ (α ↓ b) ↓ (u , l) ⟩ f t'
     p t t' = id

\end{code}

 Therefore the map (α ↓ -) reflects and preserves order:

\begin{code}

 ↓-reflects-order : (α : Ordinal U) (a b : ⟨ α ⟩)
                  → (α ↓ a) ⊲ (α ↓ b) → a ≺⟨ α ⟩ b
 ↓-reflects-order α a b ((u , l) , p) = back-transport (λ - → - ≺⟨ α ⟩ b) r l
  where
   q : (α ↓ a) ≡ (α ↓ u)
   q = p ∙ iterated-↓ α b u l
   r : a ≡ u
   r = ↓-lc α a u q

 ↓-preserves-order : (α : Ordinal U) (a b : ⟨ α ⟩)
                   → a ≺⟨ α ⟩ b → (α ↓ a) ⊲ (α ↓ b)
 ↓-preserves-order α a b l = (a , l) , ((iterated-↓ α b a l)⁻¹)

\end{code}

 It remains to show that _⊲_ is a well-order:

\begin{code}

 ↓-accessible : (α : Ordinal U) (a : ⟨ α ⟩)
              → is-accessible _⊲_ (α ↓ a)
 ↓-accessible α a = f a (Well-foundedness α a)
  where
   f : (a : ⟨ α ⟩) → is-accessible (underlying-order α) a → is-accessible _⊲_ (α ↓ a)
   f a (next .a s) = next (α ↓ a) g
    where
     IH : (b : ⟨ α ⟩) → b ≺⟨ α ⟩ a → is-accessible _⊲_ (α ↓ b)
     IH b l = f b (s b l)
     g : (β : Ordinal U) → β ⊲ (α ↓ a) → is-accessible _⊲_ β
     g β ((b , l) , p) = back-transport (is-accessible _⊲_) q (IH b l)
      where
       q : β ≡ (α ↓ b)
       q = p ∙ iterated-↓ α a b l

 ⊲-well-founded : is-well-founded _⊲_
 ⊲-well-founded α = next α g
  where
   g : (β : Ordinal U) → β ⊲ α → is-accessible _⊲_ β
   g β (b , p) = back-transport (is-accessible _⊲_) p (↓-accessible α b)

 ⊲-extensional : is-extensional _⊲_
 ⊲-extensional α β f g = ⊴-antisym ua α β
                            ((λ x → pr₁(φ x)) , i , p)
                            ((λ y → pr₁(γ y)) , j , q)
  where
   φ : (x : ⟨ α ⟩) → Σ \(y : ⟨ β ⟩) → α ↓ x ≡ β ↓ y
   φ x = f (α ↓ x) (x , refl)
   γ : (y : ⟨ β ⟩) → Σ \(x : ⟨ α ⟩) → β ↓ y ≡ α ↓ x
   γ y = g (β ↓ y) (y , refl)
   γφ : (x : ⟨ α ⟩) → pr₁(γ (pr₁(φ x))) ≡ x
   γφ x = (↓-lc α x (pr₁(γ (pr₁(φ x)))) a)⁻¹
    where
     a : (α ↓ x) ≡ (α ↓ pr₁ (γ (pr₁ (φ x))))
     a = pr₂(φ x) ∙ pr₂(γ (pr₁(φ x)))
   φγ : (y : ⟨ β ⟩) → pr₁(φ (pr₁(γ y))) ≡ y
   φγ y = (↓-lc β y (pr₁(φ (pr₁(γ y)))) a)⁻¹
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
   i x y l = pr₁(γ y) , transport (λ - → pr₁ (γ y) ≺⟨ α ⟩ -) (γφ x) a , φγ y
    where
     a : pr₁ (γ y) ≺⟨ α ⟩ (pr₁ (γ (pr₁ (φ x))))
     a = q y (pr₁ (φ x)) l
   j : is-initial-segment β α (λ y → pr₁(γ y))
   j y x l = pr₁(φ x) , transport (λ - → pr₁ (φ x) ≺⟨ β ⟩ -) (φγ y) a , γφ x
    where
     a : pr₁ (φ x) ≺⟨ β ⟩ (pr₁ (φ (pr₁ (γ y))))
     a = p x (pr₁ (γ y)) l

 ⊲-transitive : is-transitive _⊲_
 ⊲-transitive α β φ (a , p) (b , q) = pr₁ (transport (λ - → ⟨ - ⟩) q a) , (r ∙ s)
  where
   t : (ψ : Ordinal U) (q : β ≡ ψ) → (β ↓ a) ≡ ψ ↓ transport (λ - → ⟨ - ⟩) q a
   t ψ refl = refl
   r : α ≡ ((φ ↓ b) ↓ transport (λ - → ⟨ - ⟩) q a)
   r = p ∙ t (φ ↓ b) q
   s : ((φ ↓ b) ↓ transport (λ - → ⟨ - ⟩) q a) ≡ (φ ↓ pr₁ (transport (λ - → ⟨ - ⟩) q a))
   s = iterated-↓ φ b (pr₁(transport (λ - → ⟨ - ⟩) q a)) (pr₂(transport (λ - → ⟨ - ⟩) q a))

 ⊲-well-order : is-well-order _⊲_
 ⊲-well-order = ⊲-prop-valued , ⊲-well-founded , ⊲-extensional , ⊲-transitive

\end{code}

 We denote the ordinal of ordinals in the universe U by O. It lives in
 the next universe U ′.

\begin{code}

 O : Ordinal (U ′)
 O = Ordinal U , _⊲_ , ⊲-well-order

\end{code}

 Any ordinal in O is embedded in O as an initial segment:

\begin{code}

 embedded-in-O : (α : ⟨ O ⟩) → α ⊴ O
 embedded-in-O α = (λ x → α ↓ x) , i , ↓-preserves-order α
  where
   i : is-initial-segment α O (λ x → α ↓ x)
   i x β ((u , l) , p) = u , l , ((p ∙ iterated-↓ α x u l)⁻¹)

\end{code}

 Any ordinal in O is a lower set of O:

\begin{code}

 lowerset-of-O : (α : ⟨ O ⟩) → α ≃ₒ (O ↓ α)
 lowerset-of-O α = f , p , ((g , fg) , (g , gf)) , q
  where
   f : ⟨ α ⟩ → ⟨ O ↓ α ⟩
   f x = α ↓ x , x , refl
   p : is-order-preserving α (O ↓ α) f
   p x y l = (x , l) , ((iterated-↓ α y x l)⁻¹)
   g : ⟨ O ↓ α ⟩ → ⟨ α ⟩
   g (β , x , r) = x
   fg : (σ : ⟨ O ↓ α ⟩) → f (g σ) ≡ σ
   fg (.(α ↓ x) , x , refl) = refl
   gf : (x : ⟨ α ⟩) → g (f x) ≡ x
   gf x = refl
   q : is-order-preserving (O ↓ α) α g
   q (.(α ↓ x) , x , refl) (.(α ↓ x') , x' , refl) = ↓-reflects-order α x x'

\end{code}

Here are some additional observations about the various maps of
ordinals:

\begin{code}

ilcr : ∀ {U} (α β : Ordinal U) (f : ⟨ α ⟩ → ⟨ β ⟩)
     → is-initial-segment α β f
     → left-cancellable f
     → is-order-reflecting α β f
ilcr α β f i c x y l = m
 where
  a : Σ \(x' : ⟨ α ⟩) → (x' ≺⟨ α ⟩ y) × (f x' ≡ f x)
  a = i y (f x) l
  m : x ≺⟨ α ⟩ y
  m = transport (λ - → - ≺⟨ α ⟩ y) (c (pr₂(pr₂ a))) (pr₁(pr₂ a))

ipr : ∀ {U} (α β : Ordinal U) (f : ⟨ α ⟩ → ⟨ β ⟩)
    → is-simulation α β f
    → is-order-reflecting α β f
ipr α β f (i , p) = ilcr α β f i (iplc α β f (i , p))

is-order-embedding-lc : ∀ {U} (α β : Ordinal U) (f : ⟨ α ⟩ → ⟨ β ⟩)
                      → is-order-embedding α β f
                      → left-cancellable f
is-order-embedding-lc α β f (p , r) {x} {y} s = Extensionality α x y a b
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

is-order-embedding-is-embedding : ∀ {U} (α β : Ordinal U) (f : ⟨ α ⟩ → ⟨ β ⟩)
                                → is-order-embedding α β f
                                → is-embedding f
is-order-embedding-is-embedding α β f (p , r) =
 lc-embedding f
  (is-order-embedding-lc α β f (p , r))
  (ordinal-gives-is-set (underlying-order β) fe (is-well-ordered β))

\end{code}
