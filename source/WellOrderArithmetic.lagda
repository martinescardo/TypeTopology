Martin Escardo, 21 June 2018

TODO. Avoid the word "ordinal", reserving it to the module Ordinals.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module WellOrderArithmetic where

open import SpartanMLTT
open import OrdinalNotions hiding (_≤_)
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt

\end{code}

Any proposition is an ordinal under the empty ordering.

\begin{code}

module subsingleton
        {U V}
        (P : U ̇)
        (isp : is-prop P)
       where

 private _<_ : P → P → V ̇
 x < y = 𝟘

 order = _<_

 prop-valued : is-prop-valued _<_
 prop-valued x y = 𝟘-is-prop

 extensional : is-extensional _<_
 extensional x y f g = isp x y 

 transitive : is-transitive _<_
 transitive x y z ()

 well-founded : is-well-founded _<_
 well-founded x = next x (λ y ())

 well-order : is-well-order _<_
 well-order = prop-valued , well-founded , extensional , transitive

 topped : P → has-top _<_
 topped p = p , λ q l → 𝟘-elim l

\end{code}

Two particular cases are 𝟘 and 𝟙, of course.

The sum of two ordinals.

\begin{code}

module plus
        {U V W}
        {X : U ̇}
        {Y : V ̇}
        (_<_ : X → X → W ̇)
        (_≺_ : Y → Y → W ̇)
       where

 private
  _⊏_ : X + Y → X + Y → W ̇
  (inl x) ⊏ (inl x') = x < x'
  (inl x) ⊏ (inr y') = 𝟙
  (inr y) ⊏ (inl x') = 𝟘
  (inr y) ⊏ (inr y') = y ≺ y'

 order = _⊏_
  
 prop-valued : is-prop-valued _<_
            → is-prop-valued _≺_
            → is-prop-valued _⊏_
 prop-valued p p' (inl x) (inl x') l m = p x x' l m
 prop-valued p p' (inl x) (inr y') * * = refl
 prop-valued p p' (inr y) (inl x') () m
 prop-valued p p' (inr y) (inr y') l m = p' y y' l m

 extensional : is-well-founded _<_
            → is-extensional _<_
            → is-extensional _≺_
            → is-extensional _⊏_
 extensional w e e' (inl x) (inl x') f g = ap inl (e x x' (f ∘ inl) (g ∘ inl))
 extensional w e e' (inl x) (inr y') f g = 𝟘-elim (≤-refl _<_ x (w x) (g (inl x) *))
 extensional w e e' (inr y) (inl x') f g = 𝟘-elim (≤-refl _<_ x' (w x') (f (inl x') *))
 extensional w e e' (inr y) (inr y') f g = ap inr (e' y y' (f ∘ inr) (g ∘ inr))

 transitive : is-transitive _<_
           → is-transitive _≺_
           → is-transitive _⊏_
 transitive t t' (inl x) (inl x') (inl z) l m = t x x' z l m
 transitive t t' (inl x) (inl x') (inr z') l m = *
 transitive t t' (inl x) (inr y') (inl z) l ()
 transitive t t' (inl x) (inr y') (inr z') l m = *
 transitive t t' (inr y) (inl x') z () m
 transitive t t' (inr y) (inr y') (inl z') l ()
 transitive t t' (inr y) (inr y') (inr z') l m = t' y y' z' l m
  
 well-founded : is-well-founded _<_
              → is-well-founded _≺_
              → is-well-founded _⊏_
 well-founded w w' = g
  where
   φ : (x : X) → is-accessible _<_ x → is-accessible _⊏_ (inl x)
   φ x (next .x σ) = next (inl x) τ
    where
     τ : (s : X + Y) → s ⊏ inl x → is-accessible _⊏_ s
     τ (inl x') l = φ x' (σ x' l)
     τ (inr y') ()
   γ : (y : Y) → is-accessible _≺_ y → is-accessible _⊏_ (inr y)
   γ y (next .y σ) = next (inr y) τ
    where
     τ : (s : X + Y) → s ⊏ inr y → is-accessible _⊏_ s
     τ (inl x) l = φ x (w x)
     τ (inr y') l = γ y' (σ y' l)
   g : is-well-founded _⊏_
   g (inl x) = φ x (w x) 
   g (inr y) = γ y (w' y)

 well-order : is-well-order _<_
           → is-well-order _≺_
           → is-well-order _⊏_
 well-order (p , w , e , t) (p' , w' , e' , t') = prop-valued p p' ,
                                                  well-founded w w' ,
                                                  extensional w e e' ,
                                                  transitive t t'

 top-preservation : has-top _≺_ → has-top _⊏_
 top-preservation (y , f) = inr y , g
  where
   g : (z : X + Y) → ¬ (inr y ⊏ z)
   g (inl x) ()
   g (inr y') l = f y' l
   
\end{code}

Successor (probably get rid of it).

\begin{code}

module successor
        {U V}
        {X : U ̇}
        (_<_ : X → X → V ̇)
       where
  
  private
   _≺_ : 𝟙 → 𝟙 → V ̇
   _≺_ = subsingleton.order {U} 𝟙 𝟙-is-prop
   
   _<'_ : X + 𝟙 → X + 𝟙 → V ̇
   _<'_ = plus.order _<_ _≺_

  order = _<'_

  well-order : is-well-order _<_ → is-well-order _<'_
  well-order o = plus.well-order _<_ _≺_ o (subsingleton.well-order 𝟙 𝟙-is-prop)

  top : has-top _<'_
  top = inr * , g
   where
    g : (y : X + 𝟙) → ¬ (inr * <' y)
    g (inl x) ()
    g (inr *) ()

\end{code}

Multiplication. Cartesian product with the lexicographic order.

\begin{code}

module times
        {U V W T}
        {X : U ̇}
        {Y : V ̇}
        (_<_ : X → X → W ̇)
        (_≺_ : Y → Y → T ̇)
       where

 private
  _⊏_ : X × Y → X × Y → U ⊔ W ⊔ T ̇
  (a , b) ⊏ (x , y) = (a < x) + ((a ≡ x) × (b ≺ y))

 order = _⊏_

 well-founded : is-well-founded _<_
              → is-well-founded _≺_
              → is-well-founded _⊏_
 well-founded w w' (x , y) = φ x y
  where
   P : X × Y → U ⊔ V ⊔ W ⊔ T ̇
   P = is-accessible _⊏_
   γ : (x : X) → ((x' : X) → x' < x → (y' : Y) → P(x' , y')) → (y : Y) → P(x , y)
   γ x step = transfinite-induction _≺_ w' (λ y → P(x , y)) (λ y f → next (x , y) (ψ y f))
    where
     ψ : (y : Y) → ((y' : Y) → y' ≺ y → P (x , y')) → (z' : X × Y) → z' ⊏ (x , y) → P z'
     ψ y f (x' , y') (inl l) = step x' l y'
     ψ y f (x' , y') (inr (r , m)) = back-transport P p α
      where
       α : P(x , y')
       α = f y' m
       p : (x' , y') ≡ (x , y') 
       p = ×-≡ r refl 
   φ : (x : X) (y : Y) → P(x , y)
   φ = transfinite-induction _<_ w (λ x → (y : Y) → P(x , y)) γ

 transitive : is-transitive _<_
           → is-transitive _≺_
           → is-transitive _⊏_
 transitive t t' (a , b) (x , y) (u , v) = f
  where
   f : (a , b) ⊏ (x , y) → (x , y) ⊏ (u , v) → (a , b) ⊏ (u , v)
   f (inl l) (inl m) = inl (t _ _ _ l m)
   f (inl l) (inr (q , m)) = inl (transport (λ x → a < x) q l)
   f (inr (r , l)) (inl m) = inl (back-transport (λ x → x < u) r m)
   f (inr (r , l)) (inr (refl , m)) = inr (r , (t' _ _ _ l m))

 extensional : is-well-founded _<_
            → is-well-founded _≺_
            → is-extensional _<_
            → is-extensional _≺_
            → is-extensional _⊏_
 extensional w w' e e' (a , b) (x , y) f g = ×-≡ p q 
  where
   f' : (u : X) → u < a → u < x
   f' u l = cases
             (λ (m : u < x) → m)
             (λ (σ : (u ≡ x) × (y ≺ y)) → 𝟘-elim (≤-refl _≺_ y (w' y) (pr₂ σ)))
             (f (u , y) (inl l))
   g' : (u : X) → u < x → u < a
   g' u l = cases
             (λ (m : u < a) → m)
             (λ (σ : (u ≡ a) × (b ≺ b)) → 𝟘-elim (≤-refl _≺_ b (w' b) (pr₂ σ)))
             (g ((u , b)) (inl l))
   p : a ≡ x
   p = e a x f' g'
   f'' : (v : Y) → v ≺ b → v ≺ y
   f'' v l = Cases (f (a , v) (inr (refl , l)))
              (λ (m : a < x)
                 → 𝟘-elim (≤-refl _≺_ b (w' b)
                             (Cases (g (a , b) (inl m))
                              (λ (n : a < a) → 𝟘-elim (≤-refl _<_ a (w a) n))
                              (λ (σ : (a ≡ a) × (b ≺ b)) → 𝟘-elim (≤-refl _≺_ b (w' b) (pr₂ σ))))))
              (λ (σ : (a ≡ x) × (v ≺ y))
                 → pr₂ σ)
              
   g'' : (v : Y) → v ≺ y → v ≺ b
   g'' v l = Cases (g (x , v) (inr (refl , l)))
              (λ (m : x < a)
                 → Cases (f (x , y) (inl m))
                     (λ (m : x < x)
                        → 𝟘-elim (≤-refl _<_ x (w x) m))
                     (λ (σ : (x ≡ x) × (y ≺ y))
                        → 𝟘-elim (≤-refl _≺_ y (w' y) (pr₂ σ))))
              (λ (σ : (x ≡ a) × (v ≺ b))
                 → pr₂ σ)
   q : b ≡ y
   q = e' b y f'' g''

 well-order : (∀ U V → funext U V)
           → is-well-order _<_
           → is-well-order _≺_
           → is-well-order _⊏_
 well-order fe (p , w , e , t) (p' , w' , e' , t') = prop-valued ,
                                                     well-founded w w' ,
                                                     extensional w w' e e' ,
                                                     transitive t t'
  where
   prop-valued : is-prop-valued _⊏_
   prop-valued (a , b) (x , y) (inl l) (inl m) =
     ap inl (p a x l m)
   prop-valued (a , b) (x , y) (inl l) (inr (s , m)) =
     𝟘-elim (≤-refl _<_ x (w x) (transport (λ a → a < x) s l))
   prop-valued (a , b) (x , y) (inr (r , l)) (inl m) =
     𝟘-elim (≤-refl _<_ x (w x) (transport (λ a → a < x) r m))
   prop-valued (a , b) (x , y) (inr (r , l)) (inr (s , m)) =
     ap inr (×-≡ (ordinal-gives-is-set _<_ fe (p , w , e , t) r s) (p' b y l m))

 top-preservation : has-top _<_ → has-top _≺_ → has-top _⊏_
 top-preservation (x , f) (y , g) = (x , y) , h
  where
   h : (z : X × Y) → ¬ ((x , y) ⊏ z)
   h (x' , y') (inl l) = f x' l
   h (x' , y') (inr (r , l)) = g y' l

\end{code}

Added 27 June 2018. A product of ordinals indexed by a subsingleton is
an ordinal. Here "is" is used to indicate a construction, not a
proposition. We begin with a general lemma (and a corollary, which is
not used for our purposes).

\begin{code}

retract-accessible : ∀ {U V W T} {X : U ̇} {Y : V ̇} (_<_ : X → X → W ̇) (_≺_ : Y → Y → T ̇)
                       (r : X → Y) (s : Y → X)
                   → ((y : Y) → r(s y) ≡ y)
                   → ((x : X) (y : Y) → y ≺ r x → s y < x)
                   → (x : X) → is-accessible _<_ x → is-accessible _≺_ (r x)
retract-accessible {U} {V} {W} {T} {X} {Y} _<_ _≺_ r s η φ = transfinite-induction' _<_ P γ
 where
  P : (x : X) → V ⊔ T ̇
  P x = is-accessible _≺_ (r x)
  γ : (x : X) → ((x' : X) → x' < x → is-accessible _≺_ (r x')) → is-accessible _≺_ (r x)
  γ x τ = next (r x) σ
   where
    σ : (y : Y) → y ≺ r x → is-accessible _≺_ y
    σ y l = transport (is-accessible _≺_) (η y) m
     where
      m : is-accessible _≺_ (r (s y))
      m = τ (s y) (φ x y l)

retract-well-founded : ∀ {U V W T} {X : U ̇} {Y : V ̇} (_<_ : X → X → W ̇) (_≺_ : Y → Y → T ̇)
                       (r : X → Y) (s : Y → X)
                    → ((y : Y) → r(s y) ≡ y)
                    → ((x : X) (y : Y) → y ≺ r x → s y < x)
                    → is-well-founded _<_ → is-well-founded _≺_
retract-well-founded {U} {V} {W} {T} {X} {Y} _<_ _≺_ r s η φ w = w'
 where
  wr : (x : X) → is-accessible _≺_ (r x)
  wr x = retract-accessible _<_ _≺_ r s η φ x (w x)
  w' : (y : Y) → is-accessible _≺_ y
  w' y = transport (is-accessible _≺_) (η y) (wr (s y))

\end{code}

The product of a proposition-indexed family of ordinals (pip):

\begin{code}

module pip
        {U V W}
        (fe : funext U V)
        (P : U ̇)
        (isp : is-prop P)
        (X : P → V ̇)
        (_<_ : {p : P} → X p → X p → W ̇)
       where
 
\end{code}

We have the following families of equivalences indexed by P,
constructed in the module UF-PropIndexedPiSigma:

\begin{code}

 open import UF-Equiv
 open import UF-PropIndexedPiSigma
 
 private
  φ : (p : P) → Π X → X p
  φ p u = u p
 
  ψ : (p : P) → X p → Π X
  ψ p x q = transport X (isp p q) x

  η : (p : P) (u : Π X) → ψ p (φ p u) ≡ u
  η p = pr₂(pr₂(pr₂ (prop-indexed-product fe isp p)))

  ε : (p : P) (x : X p) → φ p (ψ p x) ≡ x
  ε p = pr₂(pr₁(pr₂ (prop-indexed-product fe isp p)))

\end{code}

The order on the product is constructed as follows from the order in
the components:

\begin{code}

 private
   _≺_ : Π X → Π X → U ⊔ W ̇
   u ≺ v = Σ \(p : P) → φ p u < φ p v

 order = _≺_

\end{code}

That it is subsingleton-valued depends only on the fact that the given
order _<_ {p} on the components of the product are
subsingleton-valued.

\begin{code}

 prop-valued : ((p : P) → is-prop-valued (_<_ {p}))
            → is-prop-valued _≺_
 prop-valued f u v = is-prop-closed-under-Σ isp (λ p → f p (φ p u) (φ p v))

\end{code}

The extensionality of the constructed order depends only on the fact
that φ is a retraction.

\begin{code}

 extensional : ((p : P) → is-extensional (_<_ {p}))
                 → is-extensional _≺_
 extensional e u v f g = dfunext fe γ
  where
   f' : (p : P) (x : X p) → x < φ p u → x < φ p v
   f' p x l = transport (λ x → x < φ p v) (ε p x) n'
    where
     l' : φ p (ψ p x) < φ p u
     l' = back-transport (λ x → x < φ p u) (ε p x) l
     a : ψ p x ≺ u
     a = p , l'
     m : ψ p x ≺ v
     m = f (ψ p x) a
     q : P
     q = pr₁ m
     n : φ q (ψ p x) < φ q v
     n = pr₂ m
     n' : φ p (ψ p x) < φ p v
     n' = transport (λ q → ψ p x q < φ q v) (isp q p) n
   g' : (p : P) (x : X p) → x < φ p v → x < φ p u
   g' p x l = transport (λ x → x < φ p u) (ε p x) n'
    where
     l' : φ p (ψ p x) < φ p v
     l' = back-transport (λ x → x < φ p v) (ε p x) l
     a : ψ p x ≺ v
     a = p , l'
     m : ψ p x ≺ u
     m = g (ψ p x) a
     q : P
     q = pr₁ m
     n : φ q (ψ p x) < φ q u
     n = pr₂ m
     n' : φ p (ψ p x) < φ p u
     n' = transport (λ q → ψ p x q < φ q u) (isp q p) n
   δ : (p : P) → φ p u ≡ φ p v
   δ p = e p (φ p u) (φ p v) (f' p) (g' p)
   γ : u ∼ v
   γ = δ

\end{code}

The transitivity of the constructed order depends only on the
transitivity of given order, using φ to transfer it, but not the fact
that it is an equivalence (or a retraction or a section).

\begin{code}

 transitive : ((p : P) → is-transitive (_<_ {p}))
               → is-transitive _≺_
 transitive t u v w (p , l) (q , m) = p , f l m'
  where
   f : φ p u < φ p v → φ p v < φ p w → φ p u < φ p w
   f = t p (φ p u) (φ p v) (φ p w)
   m' : φ p v < φ p w
   m' = transport (λ q → φ q v < φ q w) (isp q p) m

\end{code}

The well-foundedness of the constructed order uses the above
accessibility lemma for retracts. However, not only the fact that ψ is
a retraction is needed to apply the lemma, but also that it is a
section, to derive the order condition (given by f below) for the
lemma.

\begin{code}

 well-founded : ((p : P) → is-well-founded (_<_ {p}))
                 → is-well-founded _≺_
 well-founded w u = next u σ
  where
   σ : (v : Π X) → v ≺ u → is-accessible _≺_ v
   σ v (p , l) = d
    where
     b : is-accessible _<_ (φ p v)
     b = prev _<_ (φ p u) (w p (φ p u)) (φ p v) l
     c : is-accessible _≺_ (ψ p (φ p v))
     c = retract-accessible _<_ _≺_ (ψ p) (φ p) (η p) f (φ p v) b
      where
       f : (x : X p) (u : Π X) → u ≺ ψ p x → φ p u < x
       f x u (q , l) = transport (λ x → φ p u < x) (ε p x) l'
        where
         l' : u p < ψ p x p
         l' = transport (λ r → u r < ψ p x r) (isp q p) l
     d : is-accessible _≺_ v
     d = transport (is-accessible _≺_) (η p v) c

 well-order : ((p : P) → is-well-order (_<_ {p}))
           → is-well-order _≺_
 well-order o = prop-valued  (λ p → prop-valuedness _<_ (o p)) ,
                well-founded (λ p → well-foundedness _<_ (o p)) ,
                extensional  (λ p → extensionality _<_ (o p)) ,
                transitive   (λ p → transitivity _<_ (o p))

\end{code}

I am not sure this is going to be useful:

\begin{code}

 top-preservation : P → ((p : P) → has-top (_<_ {p})) → has-top _≺_
 top-preservation p f = (λ q → transport X (isp p q) (pr₁ (f p))) , g
  where
   g : (u : Π X) → ¬ ((λ q → transport X (isp p q) (pr₁ (f p))) ≺ u)
   g u (q , l) = h n
    where
     h : ¬(pr₁(f q) < u q)
     h = pr₂ (f q) (u q)
     m : transport X (isp q q) (pr₁ (f q)) < u q
     m = transport (λ p → transport X (isp p q) (pr₁ (f p)) < u q) (isp p q) l
     n : pr₁ (f q) < u q
     n = transport (λ r → transport X r (pr₁ (f q)) < u q) (prop-is-set isp (isp q q) refl) m
 
\end{code}

Sum of an ordinal-indexed family of ordinals. To show that
extensionality is preserved, our argument uses the assumption that
each ordinal in the family has a top element. Perhaps better
assumptions are possible. TODO: think about this.

This assumption is valid in our applications. 

\begin{code}

module sum
        (fe : (∀ U V → funext U V))
        {U V W T}
        {X : U ̇}
        {Y : X → V ̇}
        (_<_ : X → X → W ̇)
        (_≺_ : {x : X} → Y x → Y x → T ̇)
        (top : Π Y)
        (ist : (x : X) → is-top _≺_ (top x))
      where

 open import LexicographicOrder

 private
  _⊏_ : Σ Y → Σ Y → U ⊔ W ⊔ T ̇
  _⊏_ = slex-order _<_ _≺_

 order = _⊏_

 well-founded : is-well-founded _<_ 
             → ((x : X) → is-well-founded (_≺_ {x}))
             → is-well-founded _⊏_
 well-founded w w' (x , y) = φ x y
  where
   P : Σ Y → U ⊔ V ⊔ W ⊔ T ̇
   P = is-accessible _⊏_
   γ : (x : X) → ((x' : X) → x' < x → (y' : Y x') → P(x' , y')) → (y : Y x) → P(x , y)
   γ x step = transfinite-induction _≺_ (w' x) (λ y → P(x , y)) (λ y f → next (x , y) (ψ y f))
    where
     ψ : (y : Y x) → ((y' : Y x) → y' ≺ y → P (x , y')) → (z' : Σ Y) → z' ⊏ (x , y) → P z'
     ψ y f (x' , y') (inl l) = step x' l y'
     ψ y f (x' , y') (inr (r , m)) = back-transport P p α
      where
       α : P(x , transport Y r y')
       α = f (transport Y r y') m
       p : (x' , y') ≡ (x , transport Y r y') 
       p = to-Σ-≡ x' x y' (transport Y r y') r refl
   φ : (x : X) (y : Y x) → P(x , y)
   φ = transfinite-induction _<_ w (λ x → (y : Y x) → P(x , y)) γ

 transitive : is-transitive _<_
           → ((x : X) → is-transitive (_≺_ {x}))
           → is-transitive _⊏_
 transitive t t' (a , b) (x , y) (u , v) = f
  where
   f : (a , b) ⊏ (x , y) → (x , y) ⊏ (u , v) → (a , b) ⊏ (u , v)
   f (inl l) (inl m) = inl (t _ _ _ l m)
   f (inl l) (inr (q , m)) = inl (transport (λ x → a < x) q l)
   f (inr (r , l)) (inl m) = inl (back-transport (λ x → x < u) r m)
   f (inr (r , l)) (inr (refl , m)) = inr (r , (t' x _ _ _ l m))

\end{code}

Extensionality. Attempt to find a suitable hypothesis to get it. Don't
forget to remove spurious hypotheses when we finish.

\begin{code}

 private
  transport-top : (x : X) (y : Y x) → is-top _≺_ y
               → (x' : X) (r : x ≡ x') → is-top _≺_ (transport Y r y)
  transport-top x y ist .x refl = ist

  transport-order : (a x : X) (b : Y a) (v : Y x) (p : a ≡ x)
                 →  v ≺ transport Y p b
                 → back-transport Y p v ≺ b
  transport-order a .a b v refl = id

  transport-order' : (a x : X) (b : Y a) (v : Y x) (r : x ≡ a)
                  → transport Y r v ≺ b → v ≺ back-transport Y r b
  transport-order' a .a b v refl = id


 open import DiscreteAndSeparated

 extensional : is-prop-valued _<_
            → is-well-founded _<_
            → ((x : X) → is-well-founded (_≺_ {x}))
            → is-extensional _<_
            → ((x : X) → is-extensional (_≺_ {x}))
            → is-extensional _⊏_
 extensional ispv w w' e e' (a , b) (x , y) f g = to-Σ-≡'' (p , q)
  where
   f' : (u : X) → u < a → u < x
   f' u l = Cases (f (u , top u) (inl l))
             (λ (m : u < x)
                → m)
             (λ (σ : Σ \(r : u ≡ x) → transport Y r (top u) ≺ y)
                → 𝟘-elim (transport-top u (top u) (ist u) x (pr₁ σ) y (pr₂ σ)))
   g' : (u : X) → u < x → u < a
   g' u l = Cases (g (u , top u) (inl l))
             (λ (m : u < a)
                → m)
             (λ (σ : Σ \(r : u ≡ a) → transport Y r (top u) ≺ b)
                → 𝟘-elim (transport-top u (top u) (ist u) a (pr₁ σ) b (pr₂ σ)))
   p : a ≡ x
   p =  e a x f' g'
   f'' : (v : Y x) → v ≺ transport Y p b → v ≺ y
   f'' v l = Cases (f (x , v) (inr ((p ⁻¹) , transport-order a x b v p l)))
              (λ (l : x < x)
                 → 𝟘-elim (≤-refl _<_ x (w x) l))
              (λ (σ : Σ \(r : x ≡ x) → transport Y r v ≺ y)
                 → φ σ)
              where
               φ : (σ : Σ \(r : x ≡ x) → transport Y r v ≺ y) → v ≺ y
               φ (r , l) = transport
                            (λ r → transport Y r v ≺ y)
                            (extensional-gives-is-set _<_ fe ispv e r refl)
                            l
   g'' : (u : Y x) → u ≺ y → u ≺ transport Y p b
   g'' u m = Cases (g (x , u) (inr (refl , m)))
              (λ (l : x < a)
                 → 𝟘-elim (≤-refl _<_ x (w x) (transport (λ a → x < a) p l)))
              λ (σ : Σ \(r : x ≡ a) → transport Y r u ≺ b)
                 → transport
                     (λ q → u ≺ transport Y q b)
                     (extensional-gives-is-set _<_ fe ispv e ((pr₁ σ)⁻¹) p)
                     (transport-order' a x b u (pr₁ σ) (pr₂ σ))
   q : transport Y p b ≡ y
   q = e' x (transport Y p b) y f'' g''


 well-order : is-well-order _<_
            → ((x : X) → is-well-order (_≺_ {x}))
            → is-well-order _⊏_
 well-order (p , w , e , t) f = prop-valued ,
                                well-founded w (λ x → well-foundedness _≺_ (f x)) ,
                                extensional (prop-valuedness _<_ (p , w , e , t))
                                            w
                                            (λ x → well-foundedness _≺_ (f x))
                                            e
                                            (λ x → extensionality _≺_ (f x)) ,
                                transitive t (λ x → transitivity _≺_ (f x))
  where
   prop-valued : is-prop-valued _⊏_
   prop-valued (a , b) (x , y) (inl l) (inl m) =
     ap inl (p a x l m)
   prop-valued (a , b) (x , y) (inl l) (inr (s , m)) =
     𝟘-elim (≤-refl _<_ x (w x) (transport (λ a → a < x) s l))
   prop-valued (a , b) (x , y) (inr (r , l)) (inl m) =
     𝟘-elim (≤-refl _<_ x (w x) (transport (λ a → a < x) r m))
   prop-valued (a , b) (x , y) (inr (r , l)) (inr (s , m)) =
     ap inr (to-Σ-≡'' (ordinal-gives-is-set _<_ fe (p , w , e , t) r s ,
                       (prop-valuedness (_≺_ {x}) (f x) (transport Y s b) y _ m)))

 top-preservation : has-top _<_ → has-top _⊏_
 top-preservation (x , f) = (x , top x) , g
  where
   g : (σ : Σ Y) → ¬ ((x , top x) ⊏ σ)
   g (x' , y) (inl l) = f x' l
   g (x' , y) (inr (refl , l)) = ist x' y l

\end{code}

28 June 2018.

For a universe (and hence an injective type) W and an embedding
j : X → A, if every type in a family Y : X → W has the structure of an
ordinal, then so does every type in the extended family Y/j : A → W.

                   j
              X ------> A
               \       / 
                \     /
             Y   \   / Y/j
                  \ /
                   v
                   W

This is a direct application of the construction in the module
OrdinalArithmetic.prop-indexed-product-of-ordinals.

This assumes X : W, A : W, and that the given ordinal structure is
W-valued. More generally, we have the following typing, for which the
above triangle no longer makes sense, because Y / j : A → U ⊔ V ⊔ W,
but the constructions still work.

\begin{code}

open import UF-Embedding
open import UF-Equiv

module extension
        (fe : ∀ U V → funext U V)
        {U V W}
        {X : U ̇}
        {A : V ̇}
        (Y : X → W ̇)
        (j : X → A)
        (ise : is-embedding j)
        (_<_ : {x : X} → Y x → Y x → W ̇)        
        (a : A)
       where

 open import UF-InjectiveTypes (fe)

 private
  _≺_ : (Y / j) a → (Y / j) a → U ⊔ V ⊔ W ̇
  u ≺ v = Σ \(p : fiber j a) → u p < v p 

 order = _≺_

 well-order : ((x : X) → is-well-order (_<_ {x}))
           → is-well-order _≺_
 well-order o = pip.well-order 
              (fe (U ⊔ V) W) 
              (fiber j a)
              (ise a)
              (λ (p : fiber j a) → Y (pr₁ p))
              (λ {p : fiber j a} y y' → y < y')
              (λ (p : fiber j a) → o (pr₁ p))

 top-preservation : ((x : X) → has-top (_<_ {x})) → has-top _≺_
 top-preservation f = φ , g
   where
    φ : (p : fiber j a) → Y (pr₁ p)
    φ (x , r) = pr₁(f x)
    g : (ψ : (Y / j) a) → ¬ (φ ≺ ψ)
    g ψ ((x , r) , l) = pr₂ (f x) (ψ (x , r)) l

\end{code}

2011, 2013, 21 Jun 2018. Countable sum plus a top limit point, which,
constructively, is not the same thing as the sum plus one. This is
crucial to get searchability, but searchability is not addressed in
this module. We need to assume that each ordinal in the family has top
element.

This doesn't seem to be needed anymore, as it is subsumed by ∑¹ in the
module Ordinals:

\begin{code}

{- Delete this eventually:
module sum¹
        (fe : ∀ U V → funext U V)
        {U}
        (X : ℕ → U ̇)
        (_<_ : {n : ℕ} → X n → X n → U ̇)
        (o : (n : ℕ) → is-well-order (_<_ {n}))
        (t : (n : ℕ) → X n)
        (i : (n : ℕ) → is-top _<_ (t n))
       where

 open import LexicographicOrder
 open import GenericConvergentSequence
 open import ExtendedSumSearchable (fe)
 open import UF-InjectiveTypes (fe)
 open import SquashedSum (fe)
 open import UF-Embedding

 private
  fe₀ = fe U₀ U₀

  _◂_ : {w : ℕ∞} → (X / under) w → (X / under) w → U ̇
  _◂_ {w} = extension.order fe X under (under-embedding fe₀) _<_ w 

  well-order-◂ : (w : ℕ∞) → is-well-order (_◂_ {w})
  well-order-◂ w = extension.well-order fe X under (under-embedding fe₀) _<_ w o

  top : (u : ℕ∞) → (X / under) u
  top u (n , r) = t n
  
  ist : (u : ℕ∞) → is-top _◂_ (top u)
  ist u y ((n , r) , l) = i n (y (n , r)) l

  _◃_ : Σ¹ X → Σ¹ X → U ̇
  _◃_ = sum.order fe _≺_ _◂_ top ist

 order = _◃_

 well-order : is-well-order _◃_
 well-order = sum.well-order fe _≺_ _◂_ top ist (ℕ∞-ordinal fe₀) well-order-◂

 topped : has-top _◃_
 topped = sum.top-preservation fe _≺_ _◂_ top ist (∞ , ∞-top)

-}
 
\end{code}
