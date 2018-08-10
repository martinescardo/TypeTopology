Martin Escardo, August 2018

The ordinal of ordinals. Based on the HoTT Book, with a few
modifications in some of the arguments.

This is an example where we are studyings sets only, but the
univalence axiom is needed.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module OrdinalOfOrdinals
       (fe : ∀ U V → funext U V)
       where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import OrdinalNotions hiding (_≤_)
open import UF-Embedding
open import Ordinals fe
open import UF-Univalence
open import UF-Equiv

\end{code}

Given an ordinal τ and a point x of its underlying set, any lower set
τ ↓ a of a point a : ⟨ τ ⟩ forms a (sub-)ordinal:

\begin{code}

_↓_ : ∀ {U} (τ : Ordinal U) → ⟨ τ ⟩ → Ordinal U
τ ↓ a = (Σ \(y : ⟨ τ ⟩) → y ≺⟨ τ ⟩ a) , _<_ , p , w , e , t
 where
  _<_ : (Σ \(x : ⟨ τ ⟩) → x ≺⟨ τ ⟩ a) → (Σ \(x : ⟨ τ ⟩) → x ≺⟨ τ ⟩ a) → _ ̇
  (y , _) < (z , _) = y ≺⟨ τ ⟩ z
  p : is-prop-valued _<_
  p (x , _) (y , _)  = Prop-valuedness τ x y
  w : is-well-founded _<_
  w (x , l) = γ x (Well-foundedness τ x) l
   where
    γ : ∀ x → is-accessible (underlying-order τ) x → ∀ l → is-accessible _<_ (x , l)
    γ x (next .x s) l = next (x , l) (λ σ m → γ (pr₁ σ) (s (pr₁ σ) m) (pr₂ σ))
  e : is-extensional _<_
  e (x , l) (y , m) f g =
   to-Σ-≡
    (Extensionality τ x y
      (λ u n → f (u , Transitivity τ u x a n l) n)
      (λ u n → g (u , Transitivity τ u y a n m) n) ,
    Prop-valuedness τ y a _ _)
  t : is-transitive _<_
  t (x , _) (y , _) (z , _) l m = Transitivity τ x y z l m

segment-inclusion : ∀ {U} (τ : Ordinal U) (a : ⟨ τ ⟩)
                  → ⟨ τ ↓ a ⟩ → ⟨ τ ⟩
segment-inclusion τ a = pr₁

\end{code}

Maps of ordinals.

\begin{code}

is-order-preserving
 is-order-reflecting
 is-order-embedding
 is-initial-segment
 is-simulation
  : ∀ {U} → (τ υ : Ordinal U) → (⟨ τ ⟩ → ⟨ υ ⟩) → U ̇

is-order-preserving τ υ f = (x y : ⟨ τ ⟩) → x ≺⟨ τ ⟩ y → f x ≺⟨ υ ⟩ f y
is-order-reflecting τ υ f = (x y : ⟨ τ ⟩) → f x ≺⟨ υ ⟩ f y → x ≺⟨ τ ⟩ y
is-order-embedding  τ υ f = is-order-preserving τ υ f × is-order-reflecting τ υ f
is-initial-segment  τ υ f = (x : ⟨ τ ⟩) (y : ⟨ υ ⟩)
                            → y ≺⟨ υ ⟩ f x → Σ \(x' : ⟨ τ ⟩) → (x' ≺⟨ τ ⟩ x) × (f x' ≡ y)
is-simulation       τ υ f = is-initial-segment  τ υ f × is-order-preserving τ υ f

is-order-preserving-is-prop : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                           → is-prop (is-order-preserving τ υ f)
is-order-preserving-is-prop {U} τ υ f =
 Π-is-prop (fe U U)
   (λ x → Π-is-prop (fe U U)
             (λ y → Π-is-prop (fe U U)
                      (λ l → Prop-valuedness υ (f x) (f y))))

is-order-reflecting-is-prop : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                           → is-prop (is-order-reflecting τ υ f)
is-order-reflecting-is-prop {U} τ υ f =
 Π-is-prop (fe U U)
   (λ x → Π-is-prop (fe U U)
             (λ y → Π-is-prop (fe U U)
                      (λ l → Prop-valuedness τ x y)))

iplc : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
    → is-simulation τ υ f
    → left-cancellable f
iplc τ υ f (i , p) {x} {y} = γ x y (Well-foundedness τ x) (Well-foundedness τ y)
 where
  γ : ∀ x y → is-accessible (underlying-order τ) x → is-accessible (underlying-order τ) y
    → f x ≡ f y → x ≡ y
  γ x y (next .x s) (next .y t) r = Extensionality τ x y g h
   where
    g : (u : ⟨ τ ⟩) → u ≺⟨ τ ⟩ x → u ≺⟨ τ ⟩ y
    g u l = d
     where
      a : f u ≺⟨ υ ⟩ f y
      a = transport (λ - → f u ≺⟨ υ ⟩ -) r (p u x l)
      b : Σ \(v : ⟨ τ ⟩) → (v ≺⟨ τ ⟩ y) × (f v ≡ f u)
      b = i y (f u) a
      c : u ≡ pr₁ b
      c = γ u (pr₁ b) (s u l) (t (pr₁ b) (pr₁(pr₂ b))) ((pr₂ (pr₂ b))⁻¹)
      d : u ≺⟨ τ ⟩ y
      d = transport (λ - → - ≺⟨ τ ⟩ y) (c ⁻¹) (pr₁(pr₂ b))
    h : (u : ⟨ τ ⟩) → u ≺⟨ τ ⟩ y → u ≺⟨ τ ⟩ x
    h u l = d
     where
      a : f u ≺⟨ υ ⟩ f x
      a = transport (λ - → f u ≺⟨ υ ⟩ -) (r ⁻¹) (p u y l)
      b : Σ \(v : ⟨ τ ⟩) → (v ≺⟨ τ ⟩ x) × (f v ≡ f u)
      b = i x (f u) a
      c : pr₁ b ≡ u
      c = γ (pr₁ b) u (s (pr₁ b) (pr₁(pr₂ b))) (t u l) (pr₂(pr₂ b))
      d : u ≺⟨ τ ⟩ x
      d = transport (λ - → - ≺⟨ τ ⟩ x) c (pr₁(pr₂ b))

is-initial-segment-is-prop : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                          → is-order-preserving τ υ f
                          → is-prop (is-initial-segment τ υ f)
is-initial-segment-is-prop {U} τ υ f p i =
 (Π-is-prop (fe U U)
    λ x → Π-is-prop (fe U U)
            λ z → Π-is-prop (fe U U)
                    λ l → γ x z l) i
  where
   γ : ∀ x z → z ≺⟨ υ ⟩ f x → is-prop(Σ \(y : ⟨ τ ⟩) → (y ≺⟨ τ ⟩ x) × (f y ≡ z))
   γ x z l (y , (m , r)) (y' , (m' , r')) = to-Σ-≡ (a , b)
    where
     c : f y ≡ f y'
     c = r ∙ r' ⁻¹
     a : y ≡ y'
     a = iplc τ υ f (i , p) c
     b : transport (λ - →  (- ≺⟨ τ ⟩ x) × (f - ≡ z)) a (m , r) ≡ m' , r'
     b = ×-is-prop
          (Prop-valuedness τ y' x)
          (extensional-gives-is-set
              (underlying-order υ) fe
              (Prop-valuedness υ)
              (Extensionality υ))
         (transport (λ - →  (- ≺⟨ τ ⟩ x) × (f - ≡ z)) a (m , r))
         (m' , r')

\end{code}

The is-simulations form a poset:

\begin{code}

is-simulation-is-prop : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                     → is-prop (is-simulation τ υ f)
is-simulation-is-prop τ υ f = ×-prop-criterion
                            (is-initial-segment-is-prop τ υ f ,
                             λ _ → is-order-preserving-is-prop τ υ f)

at-most-one-simulation : ∀ {U} (τ υ : Ordinal U) (f f' : ⟨ τ ⟩ → ⟨ υ ⟩)
                      → is-simulation τ υ f
                      → is-simulation τ υ f'
                      → f ∼ f'
at-most-one-simulation τ υ f f' (i , p) (i' , p') x =
 γ x (Well-foundedness τ x)
 where
  γ : ∀ x → is-accessible (underlying-order τ) x → f x ≡ f' x
  γ x (next .x u) = Extensionality υ (f x) (f' x) a b
   where
    IH : ∀ y → y ≺⟨ τ ⟩ x → f y ≡ f' y
    IH y l = γ y (u y l)
    a : (z : ⟨ υ ⟩) → z ≺⟨ υ ⟩ f x → z ≺⟨ υ ⟩ f' x
    a z l = transport (λ - → - ≺⟨ υ ⟩ f' x) t m
     where
      s : Σ \(y : ⟨ τ ⟩) → (y ≺⟨ τ ⟩ x) × (f y ≡ z)
      s = i x z l
      y : ⟨ τ ⟩
      y = pr₁ s
      m : f' y ≺⟨ υ ⟩ f' x
      m = p' y x (pr₁(pr₂ s))
      t : f' y ≡ z
      t = (IH y (pr₁(pr₂ s)))⁻¹ ∙ pr₂(pr₂ s)
    b : (z : ⟨ υ ⟩) → z ≺⟨ υ ⟩ f' x → z ≺⟨ υ ⟩ f x
    b z l = transport (λ - → - ≺⟨ υ ⟩ f x) t m
     where
      s : Σ \(y : ⟨ τ ⟩) → (y ≺⟨ τ ⟩ x) × (f' y ≡ z)
      s = i' x z l
      y : ⟨ τ ⟩
      y = pr₁ s
      m : f y ≺⟨ υ ⟩ f x
      m = p y x (pr₁(pr₂ s))
      t : f y ≡ z
      t = IH y (pr₁(pr₂ s)) ∙ pr₂(pr₂ s)

_⊴_ : ∀ {U} → Ordinal U → Ordinal U → U ̇
τ ⊴ υ = Σ \(f : ⟨ τ ⟩ → ⟨ υ ⟩) → is-simulation τ υ f

⊴-is-prop : ∀ {U} (τ υ : Ordinal U) → is-prop (τ ⊴ υ)
⊴-is-prop {U} τ υ (f , s) (g , t) =
 to-Σ-≡ (dfunext (fe U U) (at-most-one-simulation τ υ f g s t) ,
         is-simulation-is-prop τ υ g _ _)

⊴-refl : ∀ {U} (τ : Ordinal U) → τ ⊴ τ
⊴-refl τ = id ,
           (λ x z l → z , l , refl) ,
           (λ x y l → l)

⊴-trans : ∀ {U} (τ υ φ : Ordinal U) → τ ⊴ υ → υ ⊴ φ → τ ⊴ φ
⊴-trans τ υ φ (f , i , p) (g , j , q) =
 g ∘ f ,
 k ,
 (λ x y l → q (f x) (f y) (p x y l))
 where
  k : (x : ⟨ τ ⟩) (z : ⟨ φ ⟩) →  z ≺⟨ φ ⟩ (g (f x))
    → Σ \(x' : ⟨ τ ⟩) → (x' ≺⟨ τ ⟩ x) × (g (f x') ≡ z)
  k x z l = pr₁ b , pr₁(pr₂ b) , (ap g (pr₂(pr₂ b)) ∙ pr₂(pr₂ a))
   where
    a : Σ \(y : ⟨ υ ⟩) → (y ≺⟨ υ ⟩ f x) × (g y ≡ z)
    a = j (f x) z l
    y : ⟨ υ ⟩
    y = pr₁ a
    b : Σ \(x' : ⟨ τ ⟩) → (x' ≺⟨ τ ⟩ x) × (f x' ≡ y)
    b = i x y (pr₁ (pr₂ a))

\end{code}

A consequence of univalence is that this order is antisymmetric.
Without abstracting the implementation, the proof that the ordinals
form a set, given below, doesn't type check in feasible time (I am not
sure why).

\begin{code}

abstract
 ⊴-antisym : ∀ {U} → is-univalent U → (τ υ : Ordinal U)
           → τ ⊴ υ → υ ⊴ τ → τ ≡ υ
 ⊴-antisym {U} ua τ υ (f , s) (g , t) = to-Σ-≡ (p , q)
  where
   fgs : is-simulation υ υ (f ∘ g)
   fgs = pr₂ (⊴-trans υ τ υ (g , t) (f , s))
   fg : (y : ⟨ υ ⟩) → f (g y) ≡ y
   fg = at-most-one-simulation υ υ (f ∘ g) id fgs (pr₂ (⊴-refl υ))
   gfs : is-simulation τ τ (g ∘ f)
   gfs = pr₂ (⊴-trans τ υ τ (f , s) (g , t))
   gf : (x : ⟨ τ ⟩) → g (f x) ≡ x
   gf = at-most-one-simulation τ τ (g ∘ f) id gfs (pr₂ (⊴-refl τ))
   e : ⟨ τ ⟩ ≃ ⟨ υ ⟩
   e = (f , ((g , fg) , g , gf))
   p : ⟨ τ ⟩ ≡ ⟨ υ ⟩
   p = eqtoid ua ⟨ τ ⟩ ⟨ υ ⟩ e
   A : (X Y : U ̇) → X ≃ Y → U ′ ̇
   A X Y e = (ρ : Σ \(_<_ : X → X → U ̇) → is-well-order _<_) (σ : Σ \(_<_ : Y → Y → U ̇) → is-well-order _<_)
          → ((x x' : X) → pr₁ ρ x x' → pr₁ σ (equiv-to-fun e x) (equiv-to-fun e x'))
          → ((y y' : Y) → pr₁ σ y y' → pr₁ ρ (back-equiv-to-fun e y) (back-equiv-to-fun e y'))
          → transport (λ - → Σ \(_<_ : - → - → U ̇) → is-well-order _<_) (eqtoid ua X Y e) ρ ≡ σ
   b : ∀ X → A X X (ideq X)
   b X ρ σ φ ψ = γ
    where
     d : ∀ x x' → pr₁ ρ x x' ≡ pr₁ σ x x'
     d x x' = UA-gives-propext ua
              (prop-valuedness (pr₁ ρ) (pr₂ ρ) x x')
              (prop-valuedness (pr₁ σ) (pr₂ σ) x x')
              (φ x x')
              (ψ x x')
     c : pr₁ ρ ≡ pr₁ σ
     c = dfunext (fe U (U ′)) (λ x → dfunext (fe U (U ′)) (d x))
     a : ρ ≡ σ
     a = pr₁-lc (λ {_<_} → ordinal-is-prop _<_ fe) c
     r : eqtoid ua X X (idtoeq X X refl) ≡ refl
     r = eqtoid-idtoeq' ua X X refl
     γ : transport (λ - → Σ \(_<_ : - → - → U ̇) → is-well-order _<_) (eqtoid ua X X (ideq X)) ρ ≡ σ
     γ = back-transport (λ - → transport (λ - → Σ \(_<_ : - → - → U ̇) → is-well-order _<_) - ρ ≡ σ) r a
   h : ∀ X Y (e : X ≃ Y) → A X Y e
   h X = JEq ua X (A X) (b X)
   q : transport (λ - → Σ \(_<_ : - → - → U ̇) → is-well-order _<_) p (pr₂ τ) ≡ pr₂ υ
   q = h ⟨ τ ⟩ ⟨ υ ⟩ e (pr₂ τ) (pr₂ υ) (pr₂ s) (pr₂ t)

segment-inclusion-is-simulation : ∀ {U} (τ : Ordinal U) (a : ⟨ τ ⟩)
                               → is-simulation (τ ↓ a) τ (segment-inclusion τ a)
segment-inclusion-is-simulation τ a = i , p
 where
  i : is-initial-segment (τ ↓ a) τ (segment-inclusion τ a)
  i (x , l) z m = (z , Transitivity τ z x a m l) , m , refl
  p : is-order-preserving (τ ↓ a) τ (segment-inclusion τ a)
  p x y = id

segment-⊴ : ∀ {U} (τ : Ordinal U) (a : ⟨ τ ⟩)
          → (τ ↓ a) ⊴ τ
segment-⊴ τ a = segment-inclusion τ a , segment-inclusion-is-simulation τ a

\end{code}

One of the many applications of the univalence axiom is to manufacture
examples of types which are not sets. Here we use it to prove that a
certain type is a set.

\begin{code}

Ordinal-is-set : ∀ {U} → is-univalent U → is-set (Ordinal U)
Ordinal-is-set {U} ua = identification-collapsible-is-set pc
 where
  i : (τ υ : Ordinal U) → is-prop (τ ⊴ υ × υ ⊴ τ)
  i τ υ = ×-is-prop (⊴-is-prop τ υ) (⊴-is-prop υ τ)
  g : (τ υ : Ordinal U) → τ ≡ υ → τ ⊴ υ × υ ⊴ τ
  g τ υ p = transport (λ - → τ ⊴ -) p (⊴-refl τ) , back-transport (λ - → υ ⊴ -) p (⊴-refl υ)
  h : (τ υ : Ordinal U) → τ ⊴ υ × υ ⊴ τ → τ ≡ υ
  h τ υ (l , m) = ⊴-antisym {U} ua τ υ l m
  hc : (τ υ : Ordinal U) (w t : τ ⊴ υ × υ ⊴ τ) → h τ υ w ≡ h τ υ t
  hc τ υ w t = ap (h τ υ) (i τ υ w t)
  f  : (τ υ : Ordinal U) → τ ≡ υ → τ ≡ υ
  f τ υ p = h τ υ (g τ υ p)
  fc : (τ υ : Ordinal U) (p q : τ ≡ υ) → f τ υ p ≡ f τ υ q
  fc τ υ p q = hc τ υ (g τ υ p) (g τ υ q)
  pc : {τ υ : Ordinal U} → Σ \(f : τ ≡ υ → τ ≡ υ) → constant f
  pc {τ} {υ} = (f τ υ , fc τ υ)

↓-⊴-lc : ∀ {U} (τ : Ordinal U) (a b : ⟨ τ ⟩)
       → (τ ↓ a)  ⊴  (τ ↓ b )
       → a ≼⟨ τ ⟩ b
↓-⊴-lc {U} τ a b (f , s) u l = γ
 where
  h : segment-inclusion τ a ∼ segment-inclusion τ b ∘ f
  h = at-most-one-simulation (τ ↓ a) τ
        (segment-inclusion τ a)
        (segment-inclusion τ b ∘ f)
        (segment-inclusion-is-simulation τ a)
        (pr₂ (⊴-trans (τ ↓ a) (τ ↓ b) τ
                 (f , s)
                 (segment-⊴ τ b)))
  v : ⟨ τ ⟩
  v = segment-inclusion τ b (f (u , l))
  m : v ≺⟨ τ ⟩ b
  m = pr₂ (f (u , l))
  q : u ≡ v
  q = h (u , l)
  γ : u ≺⟨ τ ⟩ b
  γ = back-transport (λ - → - ≺⟨ τ ⟩ b) q m

↓-lc : ∀ {U} (τ : Ordinal U) (a b : ⟨ τ ⟩)
     → τ ↓ a ≡ τ ↓ b
     → a ≡ b
↓-lc τ a b p =
 Extensionality τ a b
  (↓-⊴-lc τ a b (transport (λ - → (τ ↓ a) ⊴ -) p (⊴-refl (τ ↓ a))))
  (↓-⊴-lc τ b a (back-transport (λ - → (τ ↓ b) ⊴ -) p (⊴-refl (τ ↓ b))))

\end{code}

We now ready to make the type of ordinals into an ordinal.

\begin{code}

_⊲_ : ∀ {U} → Ordinal U → Ordinal U → U ′ ̇
τ ⊲ υ = Σ \(b : ⟨ υ ⟩) → τ ≡ (υ ↓ b)

⊲-prop-valued : ∀ {U} → is-univalent U
               → (τ υ : Ordinal U) → is-prop (τ ⊲ υ)
⊲-prop-valued {U} ua τ υ  (b , p) (b' , p') = to-Σ-≡ (r , s)
 where
  r : b ≡ b'
  r = ↓-lc υ b b' (p ⁻¹ ∙ p')
  s : transport (λ - → τ ≡ (υ ↓ -)) r p ≡ p'
  s = Ordinal-is-set ua _ _

\end{code}

We could instead define τ ⊲ υ to mean that we have b with τ ⊴ (υ ↓ b)
and (υ ↓ b) ⊴ τ, by antisymetry, and this definition make ⊲ have
values in the universe U rather than the next universe U ′. We pause
briefly to record this observation.

\begin{code}

module alterative-⊲' where

    _⊲'_ : ∀ {U} → Ordinal U → Ordinal U → U ̇
    τ ⊲' υ = Σ \(b : ⟨ υ ⟩) → (τ ⊴ (υ ↓ b)) × ((υ ↓ b) ⊴ τ)

    ⊲'-prop-valued : ∀ {U} → is-univalent U
                  → (τ υ : Ordinal U) → is-prop (τ ⊲' υ)
    ⊲'-prop-valued {U} ua τ υ  (b , l , m) (b' , l' , m') =
     to-Σ-≡ (r , s)
     where
      r : b ≡ b'
      r = ↓-lc υ b b' (⊴-antisym ua (υ ↓ b) (υ ↓ b')
                         (⊴-trans (υ ↓ b) τ (υ ↓ b') m l')
                         (⊴-trans (υ ↓ b') τ (υ ↓ b) m' l))
      s : transport (λ - → (τ ⊴ (υ ↓ -)) × ((υ ↓ -) ⊴ τ)) r (l , m) ≡ l' , m'
      s = ×-is-prop (⊴-is-prop τ (υ ↓ b')) (⊴-is-prop (υ ↓ b') τ) _ _


    ⊲-gives-⊲' : ∀ {U} (τ υ : Ordinal U)
               → τ ⊲ υ → τ ⊲' υ
    ⊲-gives-⊲' τ υ (b , p) = b ,
                              transport (λ - → τ ⊴ -) p (⊴-refl τ) ,
                              back-transport (λ - → (υ ↓ b) ⊴ -) p (⊴-refl (υ ↓ b))

    ⊲'-gives-⊲ : ∀ {U} → is-univalent U → (τ υ : Ordinal U)
               → τ ⊲' υ → τ ⊲ υ
    ⊲'-gives-⊲ ua τ υ (b , l , m) = b , ⊴-antisym ua τ (υ ↓ b) l m

down : ∀ {U} (τ : Ordinal U) (b u : ⟨ τ ⟩) (l : u ≺⟨ τ ⟩ b)
    → ((τ ↓ b ) ↓ (u , l)) ⊴ (τ ↓ u)
down {U} τ b u l = f , (i , p)
 where
  f : ⟨ (τ ↓ b) ↓ (u , l) ⟩ → ⟨ τ ↓ u ⟩
  f ((x , m) , n) = x , n
  i : (w : ⟨ (τ ↓ b) ↓ (u , l) ⟩) (t : ⟨ τ ↓ u ⟩)
    → t ≺⟨ τ ↓ u ⟩ f w → Σ \(w' : ⟨ (τ ↓ b) ↓ (u , l) ⟩) → (w' ≺⟨ (τ ↓ b) ↓ (u , l) ⟩ w) × (f w' ≡ t)
  i ((x , m) , n) (x' , m') n' = ((x' , Transitivity τ x' u b m' l) , m') ,
                                 (n' , refl)
  p : (w w' : ⟨ (τ ↓ b) ↓ (u , l) ⟩) → w ≺⟨ (τ ↓ b) ↓ (u , l) ⟩ w' → f w ≺⟨ τ ↓ u ⟩ (f w')
  p w w' = id

up : ∀ {U} (τ : Ordinal U) (b u : ⟨ τ ⟩) (l : u ≺⟨ τ ⟩ b)
  → (τ ↓ u) ⊴ ((τ ↓ b ) ↓ (u , l))
up {U} τ b u l = f , (i , p)
 where
  f : ⟨ τ ↓ u ⟩ → ⟨ (τ ↓ b) ↓ (u , l) ⟩
  f (x , n) = ((x , Transitivity τ x u b n l) , n)
  i : (t : ⟨ τ ↓ u ⟩) (w : ⟨ (τ ↓ b) ↓ (u , l) ⟩)
    → w ≺⟨ (τ ↓ b) ↓ (u , l) ⟩ f t → Σ \(t' : ⟨ τ ↓ u ⟩) → (t' ≺⟨ τ ↓ u ⟩ t) × (f t' ≡ w)
  i (x , n) ((x' , m') , n') o = (x' , n') ,
                                 (o , to-Σ-≡
                                       (to-Σ-≡' (Prop-valuedness τ x' b _ _) ,
                                       Prop-valuedness τ x' u _ _))
  p : (t t' : ⟨ τ ↓ u ⟩) → t ≺⟨ τ ↓ u ⟩ t' → f t ≺⟨ (τ ↓ b) ↓ (u , l) ⟩ f t'
  p t t' = id

iterated-↓ : ∀ {U} → is-univalent U → (τ : Ordinal U) (a b : ⟨ τ ⟩) (l : b ≺⟨ τ ⟩ a)
          → ((τ ↓ a ) ↓ (b , l)) ≡ (τ ↓ b)
iterated-↓ ua τ a b l = ⊴-antisym ua ((τ ↓ a) ↓ (b , l)) (τ ↓ b) (down τ a b l) (up τ a b l)

↓-⊲-lc : ∀ {U} → is-univalent U → (τ : Ordinal U) (a b : ⟨ τ ⟩)
        → (τ ↓ a) ⊲ (τ ↓ b)
        → a ≺⟨ τ ⟩ b
↓-⊲-lc {U} ua τ a b ((u , l) , p) = back-transport (λ - → - ≺⟨ τ ⟩ b) r l
 where
  q : (τ ↓ a) ≡ (τ ↓ u)
  q = p ∙ iterated-↓ ua τ b u l
  r : a ≡ u
  r = ↓-lc τ a u q

↓-⊲-op : ∀ {U} → is-univalent U → (τ : Ordinal U) (a b : ⟨ τ ⟩)
        → a ≺⟨ τ ⟩ b
        → (τ ↓ a) ⊲ (τ ↓ b)
↓-⊲-op ua τ a b l = (a , l) , ((iterated-↓ ua τ b a l)⁻¹)

↓-accessible : ∀ {U} → is-univalent U → (τ : Ordinal U) (a : ⟨ τ ⟩)
             → is-accessible _⊲_ (τ ↓ a)
↓-accessible {U} ua τ a = γ a (Well-foundedness τ a)
 where
  γ : (a : ⟨ τ ⟩) → is-accessible (underlying-order τ) a → is-accessible _⊲_ (τ ↓ a)
  γ a (next .a s) = next (τ ↓ a) g
   where
    IH : (b : ⟨ τ ⟩) → b ≺⟨ τ ⟩ a → is-accessible _⊲_ (τ ↓ b)
    IH b l = γ b (s b l)
    g : (υ : Ordinal U) → υ ⊲ (τ ↓ a) → is-accessible _⊲_ υ
    g υ ((b , l) , p) = back-transport (is-accessible _⊲_) q (IH b l)
     where
      q : υ ≡ (τ ↓ b)
      q = p ∙ iterated-↓ ua τ a b l

⊲-well-founded : ∀ {U} → is-univalent U
               → is-well-founded (_⊲_ {U})
⊲-well-founded {U} ua τ = next τ g
 where
  g : (υ : Ordinal U) → υ ⊲ τ → is-accessible _⊲_ υ
  g υ (b , p) = back-transport (is-accessible _⊲_) p (↓-accessible ua τ b)

⊲-extensional : ∀ {U} → is-univalent U
              → is-extensional (_⊲_ {U})
⊲-extensional {U} ua τ υ f g = ⊴-antisym ua τ υ
                                 ((λ x → pr₁(φ x)) , i , p)
                                 ((λ y → pr₁(γ y)) , j , q)
 where
  φ : (x : ⟨ τ ⟩) → Σ \(y : ⟨ υ ⟩) → τ ↓ x ≡ υ ↓ y
  φ x = f (τ ↓ x) (x , refl)
  γ : (y : ⟨ υ ⟩) → Σ \(x : ⟨ τ ⟩) → υ ↓ y ≡ τ ↓ x
  γ y = g (υ ↓ y) (y , refl)
  γφ : (x : ⟨ τ ⟩) → pr₁(γ (pr₁(φ x))) ≡ x
  γφ x = (↓-lc τ x (pr₁(γ (pr₁(φ x)))) a)⁻¹
   where
    a : (τ ↓ x) ≡ (τ ↓ pr₁ (γ (pr₁ (φ x))))
    a = pr₂(φ x) ∙ pr₂(γ (pr₁(φ x)))
  φγ : (y : ⟨ υ ⟩) → pr₁(φ (pr₁(γ y))) ≡ y
  φγ y = (↓-lc υ y (pr₁(φ (pr₁(γ y)))) a)⁻¹
   where
    a : (υ ↓ y) ≡ (υ ↓ pr₁ (φ (pr₁ (γ y))))
    a = pr₂(γ y) ∙ pr₂(φ (pr₁(γ y)))
  p : is-order-preserving τ υ (λ x → pr₁(φ x))
  p x x' l = ↓-⊲-lc ua υ (pr₁ (φ x)) (pr₁ (φ x')) b
   where
    a : (τ ↓ x) ⊲ (τ ↓ x')
    a = ↓-⊲-op ua τ x x' l
    b : (υ ↓ pr₁ (φ x)) ⊲ (υ ↓ pr₁ (φ x'))
    b = transport₂ _⊲_ (pr₂ (φ x)) (pr₂ (φ x')) a
  q : is-order-preserving υ τ (λ y → pr₁(γ y))
  q y y' l = ↓-⊲-lc ua τ (pr₁ (γ y)) (pr₁ (γ y')) b
   where
    a : (υ ↓ y) ⊲ (υ ↓ y')
    a = ↓-⊲-op ua υ y y' l
    b : (τ ↓ pr₁ (γ y)) ⊲ (τ ↓ pr₁ (γ y'))
    b = transport₂ _⊲_ (pr₂ (γ y)) (pr₂ (γ y')) a
  i : is-initial-segment τ υ (λ x → pr₁(φ x))
  i x y l = pr₁(γ y) , transport (λ - → pr₁ (γ y) ≺⟨ τ ⟩ -) (γφ x) a , φγ y
   where
    a : pr₁ (γ y) ≺⟨ τ ⟩ (pr₁ (γ (pr₁ (φ x))))
    a = q y (pr₁ (φ x)) l
  j : is-initial-segment υ τ (λ y → pr₁(γ y))
  j y x l = pr₁(φ x) , transport (λ - → pr₁ (φ x) ≺⟨ υ ⟩ -) (φγ y) a , γφ x
   where
    a : pr₁ (φ x) ≺⟨ υ ⟩ (pr₁ (φ (pr₁ (γ y))))
    a = p x (pr₁ (γ y)) l

⊲-transitive : ∀ {U} → is-univalent U
             → is-transitive (_⊲_ {U})
⊲-transitive {U} ua τ υ φ (a , p) (b , q) = pr₁ (transport (λ - → ⟨ - ⟩) q a) , (r ∙ s)
 where
  t : (ψ : Ordinal U) (q : υ ≡ ψ) → (υ ↓ a) ≡ ψ ↓ transport (λ - → ⟨ - ⟩) q a
  t ψ refl = refl
  r : τ ≡ ((φ ↓ b) ↓ transport (λ - → ⟨ - ⟩) q a)
  r = p ∙ t (φ ↓ b) q
  s : ((φ ↓ b) ↓ transport (λ - → ⟨ - ⟩) q a) ≡ (φ ↓ pr₁ (transport (λ - → ⟨ - ⟩) q a))
  s = iterated-↓ ua φ b (pr₁(transport (λ - → ⟨ - ⟩) q a)) (pr₂(transport (λ - → ⟨ - ⟩) q a))

⊲-well-order : ∀ {U} → is-univalent U
             → is-well-order (_⊲_ {U})
⊲-well-order ua = ⊲-prop-valued ua , ⊲-well-founded ua , ⊲-extensional ua , ⊲-transitive ua

ordinal-of-ordinals : ∀ U → is-univalent U → Ordinal (U ′)
ordinal-of-ordinals U ua = Ordinal U , _⊲_ , ⊲-well-order ua

\end{code}

And here are some additional observations:

\begin{code}

ilcr : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
    → is-initial-segment τ υ f
    → left-cancellable f
    → is-order-reflecting τ υ f
ilcr τ υ f i c x y l = γ
 where
  a : Σ \(x' : ⟨ τ ⟩) → (x' ≺⟨ τ ⟩ y) × (f x' ≡ f x)
  a = i y (f x) l
  γ : x ≺⟨ τ ⟩ y
  γ = transport (λ - → - ≺⟨ τ ⟩ y) (c (pr₂(pr₂ a))) (pr₁(pr₂ a))

ipr : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
   → is-simulation τ υ f
   → is-order-reflecting τ υ f
ipr τ υ f (i , p) = ilcr τ υ f i (iplc τ υ f (i , p))

is-order-embedding-lc : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                  → is-order-embedding τ υ f
                  → left-cancellable f
is-order-embedding-lc τ υ f (p , r) {x} {y} s = Extensionality τ x y a b
 where
  a : (u : ⟨ τ ⟩) → u ≺⟨ τ ⟩ x → u ≺⟨ τ ⟩ y
  a u l = r u y j
   where
    i : f u ≺⟨ υ ⟩ f x
    i = p u x l
    j : f u ≺⟨ υ ⟩ f y
    j = transport (λ - → f u ≺⟨ υ ⟩ -) s i
  b : (u : ⟨ τ ⟩) → u ≺⟨ τ ⟩ y → u ≺⟨ τ ⟩ x
  b u l = r u x j
   where
    i : f u ≺⟨ υ ⟩ f y
    i = p u y l
    j : f u ≺⟨ υ ⟩ f x
    j = back-transport (λ - → f u ≺⟨ υ ⟩ -) s i

is-order-embedding-is-embedding : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                             → is-order-embedding τ υ f
                             → is-embedding f
is-order-embedding-is-embedding τ υ f (p , r) =
 lc-embedding f
  (is-order-embedding-lc τ υ f (p , r))
  (extensional-gives-is-set
    (underlying-order υ) fe
    (Prop-valuedness υ)
    (Extensionality υ))

\end{code}
