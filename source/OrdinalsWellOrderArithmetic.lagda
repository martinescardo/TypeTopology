Martin Escardo, 21 June 2018

Ordinals proper are defined in the module Ordinals, as types equipped
with well orders. This module forms the basis for that module. We
still use the terminology "ordinal" here.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module OrdinalsWellOrderArithmetic where

open import SpartanMLTT hiding (transitive)
open import OrdinalNotions

open import UF-Base
open import UF-Subsingletons
open import UF-FunExt

\end{code}

Any proposition (i.e. subsingleton) is an ordinal under the empty
ordering.

\begin{code}

module prop
        {𝓤 𝓥}
        (P : 𝓤 ̇ )
        (isp : is-prop P)
       where

 private
  _<_ : P → P → 𝓥 ̇
  x < y = 𝟘

 order = _<_

 prop-valued : is-prop-valued _<_
 prop-valued x y = 𝟘-is-prop

 extensional : is-extensional _<_
 extensional x y f g = isp x y

 transitive : is-transitive _<_
 transitive x y z a = 𝟘-elim a

 well-founded : is-well-founded _<_
 well-founded x = next x (λ y a → 𝟘-elim a)

 well-order : is-well-order _<_
 well-order = prop-valued , well-founded , extensional , transitive

 topped : P → has-top _<_
 topped p = p , λ q l → 𝟘-elim l

 trichotomous : is-trichotomous-order _<_
 trichotomous x y = inr (inl (isp x y))

\end{code}

Two particular cases are 𝟘 and 𝟙, of course.

The sum of two ordinals.

\begin{code}

module plus
        {𝓤 𝓥 𝓦}
        {X : 𝓤 ̇ }
        {Y : 𝓥 ̇ }
        (_<_ : X → X → 𝓦 ̇ )
        (_≺_ : Y → Y → 𝓦 ̇ )
       where

 private
  _⊏_ : X + Y → X + Y → 𝓦 ̇
  (inl x) ⊏ (inl x') = x < x'
  (inl x) ⊏ (inr y') = 𝟙
  (inr y) ⊏ (inl x') = 𝟘
  (inr y) ⊏ (inr y') = y ≺ y'

\end{code}

TODO. We would like to generalize _≺_ : Y → Y → 𝓣 ̇ with an arbitrary
universe 𝓣, and then _⊏_ : X + Y → X + Y → 𝓦 ⊔ 𝓣 ̇. In this case, we
would need to lift x < x' amd y ≺ y', in the above definition of _⊏_
and then adapt the following definitions.

\begin{code}

 order = _⊏_

 prop-valued : is-prop-valued _<_
             → is-prop-valued _≺_
             → is-prop-valued _⊏_
 prop-valued p p' (inl x) (inl x') l m = p x x' l m
 prop-valued p p' (inl x) (inr y') * * = refl
 prop-valued p p' (inr y) (inl x') a m = 𝟘-elim a
 prop-valued p p' (inr y) (inr y') l m = p' y y' l m

 extensional : is-well-founded _<_
             → is-extensional _<_
             → is-extensional _≺_
             → is-extensional _⊏_
 extensional w e e' (inl x) (inl x') f g = ap inl (e x x' (f ∘ inl) (g ∘ inl))
 extensional w e e' (inl x) (inr y') f g = 𝟘-elim (irreflexive _<_ x (w x) (g (inl x) ⋆))
 extensional w e e' (inr y) (inl x') f g = 𝟘-elim (irreflexive _<_ x' (w x') (f (inl x') ⋆))
 extensional w e e' (inr y) (inr y') f g = ap inr (e' y y' (f ∘ inr) (g ∘ inr))

 transitive : is-transitive _<_
            → is-transitive _≺_
            → is-transitive _⊏_
 transitive t t' (inl x) (inl x') (inl z)  l m = t x x' z l m
 transitive t t' (inl x) (inl x') (inr z') l m = ⋆
 transitive t t' (inl x) (inr y') (inl z)  l m = 𝟘-elim m
 transitive t t' (inl x) (inr y') (inr z') l m = ⋆
 transitive t t' (inr y) (inl x') _        l m = 𝟘-elim l
 transitive t t' (inr y) (inr y') (inl z') l m = 𝟘-elim m
 transitive t t' (inr y) (inr y') (inr z') l m = t' y y' z' l m

 well-founded : is-well-founded _<_
              → is-well-founded _≺_
              → is-well-founded _⊏_
 well-founded w w' = g
  where
   φ : (x : X) → is-accessible _<_ x → is-accessible _⊏_ (inl x)
   φ x (next x σ) = next (inl x) τ
    where
     τ : (s : X + Y) → s ⊏ inl x → is-accessible _⊏_ s
     τ (inl x') l = φ x' (σ x' l)
     τ (inr y') l = 𝟘-elim l

   γ : (y : Y) → is-accessible _≺_ y → is-accessible _⊏_ (inr y)
   γ y (next .y σ) = next (inr y) τ
    where
     τ : (s : X + Y) → s ⊏ inr y → is-accessible _⊏_ s
     τ (inl x)  l = φ x (w x)
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
   g (inl x)  l = 𝟘-elim l
   g (inr y') l = f y' l

 tricho-left : (x : X)
             → is-trichotomous-element _<_ x
             → is-trichotomous-element _⊏_ (inl x)
 tricho-left x t (inl x') = lemma (t x')
  where
   lemma : (x < x') + (x ≡ x') + (x' < x)
         → inl x ⊏ inl x' + (inl x ≡ inl x') + inl x' ⊏ inl x
   lemma (inl l)       = inl l
   lemma (inr (inl e)) = inr (inl (ap inl e))
   lemma (inr (inr k)) = inr (inr k)

 tricho-left x t (inr y)  = inl ⋆

 tricho-right : (y : Y)
              → is-trichotomous-element _≺_ y
              → is-trichotomous-element _⊏_ (inr y)
 tricho-right y u (inl x)  = inr (inr ⋆)
 tricho-right y u (inr y') = lemma (u y')
  where
   lemma : (y ≺ y') + (y ≡ y') + (y' ≺ y)
         → inr y ⊏ inr y' + (inr y ≡ inr y') + inr y' ⊏ inr y
   lemma (inl l)       = inl l
   lemma (inr (inl e)) = inr (inl (ap inr e))
   lemma (inr (inr k)) = inr (inr k)

 trichotomy-preservation : is-trichotomous-order _<_
                         → is-trichotomous-order _≺_
                         → is-trichotomous-order _⊏_
 trichotomy-preservation t u (inl x) = tricho-left  x (t x)
 trichotomy-preservation t u (inr y) = tricho-right y (u y)

\end{code}

Successor (probably get rid of it as we can do _+ₒ 𝟙ₒ):

\begin{code}

module successor
        {𝓤 𝓥}
        {X : 𝓤 ̇ }
        (_<_ : X → X → 𝓥 ̇ )
       where

  private
   _≺_ : 𝟙 → 𝟙 → 𝓥 ̇
   _≺_ = prop.order {𝓤} 𝟙 𝟙-is-prop

   _<'_ : X + 𝟙 → X + 𝟙 → 𝓥 ̇
   _<'_ = plus.order _<_ _≺_

  order = _<'_

  well-order : is-well-order _<_ → is-well-order _<'_
  well-order o = plus.well-order _<_ _≺_ o (prop.well-order 𝟙 𝟙-is-prop)

  top : has-top _<'_
  top = inr ⋆ , g
   where
    g : (y : X + 𝟙) → ¬ (inr ⋆ <' y)
    g (inl x) l = 𝟘-elim l
    g (inr ⋆) l = 𝟘-elim l

\end{code}

Multiplication. Cartesian product with the lexicographic order.

\begin{code}

module times
        {𝓤 𝓥 𝓦 𝓣}
        {X : 𝓤 ̇ }
        {Y : 𝓥 ̇ }
        (_<_ : X → X → 𝓦 ̇ )
        (_≺_ : Y → Y → 𝓣 ̇ )
       where

 private
  _⊏_ : X × Y → X × Y → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
  (a , b) ⊏ (x , y) = (a < x) + ((a ≡ x) × (b ≺ y))

 order = _⊏_

 well-founded : is-well-founded _<_
              → is-well-founded _≺_
              → is-well-founded _⊏_
 well-founded w w' (x , y) = φ x y
  where
   P : X × Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
   P = is-accessible _⊏_

   γ : (x : X) → ((x' : X) → x' < x → (y' : Y) → P (x' , y')) → (y : Y) → P (x , y)
   γ x step = transfinite-induction _≺_ w' (λ y → P (x , y)) (λ y f → next (x , y) (ψ y f))
    where
     ψ : (y : Y) → ((y' : Y) → y' ≺ y → P (x , y')) → (z' : X × Y) → z' ⊏ (x , y) → P z'
     ψ y f (x' , y') (inl l) = step x' l y'
     ψ y f (x' , y') (inr (r , m)) = transport⁻¹ P p α
      where
       α : P (x , y')
       α = f y' m

       p : (x' , y') ≡ (x , y')
       p = to-×-≡ r refl

   φ : (x : X) (y : Y) → P (x , y)
   φ = transfinite-induction _<_ w (λ x → (y : Y) → P (x , y)) γ

 transitive : is-transitive _<_
            → is-transitive _≺_
            → is-transitive _⊏_
 transitive t t' (a , b) (x , y) (u , v) = f
  where
   f : (a , b) ⊏ (x , y) → (x , y) ⊏ (u , v) → (a , b) ⊏ (u , v)
   f (inl l)       (inl m)          = inl (t _ _ _ l m)
   f (inl l)       (inr (q , m))    = inl (transport (λ - → a < -) q l)
   f (inr (r , l)) (inl m)          = inl (transport⁻¹ (λ - → - < u) r m)
   f (inr (r , l)) (inr (refl , m)) = inr (r , (t' _ _ _ l m))

 extensional : is-well-founded _<_
             → is-well-founded _≺_
             → is-extensional _<_
             → is-extensional _≺_
             → is-extensional _⊏_
 extensional w w' e e' (a , b) (x , y) f g = to-×-≡ p q
  where
   f' : (u : X) → u < a → u < x
   f' u l = Cases (f (u , y) (inl l))
             (λ (m : u < x) → m)
             (λ (σ : (u ≡ x) × (y ≺ y)) → 𝟘-elim (irreflexive _≺_ y (w' y) (pr₂ σ)))

   g' : (u : X) → u < x → u < a
   g' u l = Cases (g ((u , b)) (inl l))
             (λ (m : u < a) → m)
             (λ (σ : (u ≡ a) × (b ≺ b)) → 𝟘-elim (irreflexive _≺_ b (w' b) (pr₂ σ)))

   p : a ≡ x
   p = e a x f' g'

   f'' : (v : Y) → v ≺ b → v ≺ y
   f'' v l = Cases (f (a , v) (inr (refl , l)))
              (λ (m : a < x)
                 → 𝟘-elim (irreflexive _≺_ b (w' b)
                             (Cases (g (a , b) (inl m))
                              (λ (n : a < a) → 𝟘-elim (irreflexive _<_ a (w a) n))
                              (λ (σ : (a ≡ a) × (b ≺ b)) → 𝟘-elim (irreflexive _≺_ b (w' b) (pr₂ σ))))))
              (λ (σ : (a ≡ x) × (v ≺ y))
                 → pr₂ σ)

   g'' : (v : Y) → v ≺ y → v ≺ b
   g'' v l = Cases (g (x , v) (inr (refl , l)))
              (λ (m : x < a)
                 → Cases (f (x , y) (inl m))
                     (λ (m : x < x)
                        → 𝟘-elim (irreflexive _<_ x (w x) m))
                     (λ (σ : (x ≡ x) × (y ≺ y))
                        → 𝟘-elim (irreflexive _≺_ y (w' y) (pr₂ σ))))
              (λ (σ : (x ≡ a) × (v ≺ b))
                 → pr₂ σ)

   q : b ≡ y
   q = e' b y f'' g''

 well-order : FunExt
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
     𝟘-elim (irreflexive _<_ x (w x) (transport (λ - → - < x) s l))
   prop-valued (a , b) (x , y) (inr (r , l)) (inl m) =
     𝟘-elim (irreflexive _<_ x (w x) (transport (λ - → - < x) r m))
   prop-valued (a , b) (x , y) (inr (r , l)) (inr (s , m)) =
     ap inr (to-×-≡ (well-ordered-types-are-sets _<_ fe (p , w , e , t) r s) (p' b y l m))

 top-preservation : has-top _<_ → has-top _≺_ → has-top _⊏_
 top-preservation (x , f) (y , g) = (x , y) , h
  where
   h : (z : X × Y) → ¬ ((x , y) ⊏ z)
   h (x' , y') (inl l) = f x' l
   h (x' , y') (inr (r , l)) = g y' l

 tricho : {x : X} {y : Y}
        → is-trichotomous-element _<_ x
        → is-trichotomous-element _≺_ y
        → is-trichotomous-element _⊏_ (x , y)
 tricho {x} {y} t u (x' , y') =
  Cases (t x')
   (λ (l : x < x') → inl (inl l))
   (cases
     (λ (p : x ≡ x')
        → Cases (u y')
           (λ (l : y ≺ y')
              → inl (inr (p , l)))
           (cases
             (λ (q : y ≡ y')
                → inr (inl (to-×-≡ p q)))
             (λ (l : y' ≺ y) → inr (inr (inr ((p ⁻¹) , l))))))
     (λ (l : x' < x) → inr (inr (inl l))))

 trichotomy-preservation : is-trichotomous-order _<_
                         → is-trichotomous-order _≺_
                         → is-trichotomous-order _⊏_
 trichotomy-preservation t u (x , y) = tricho (t x) (u y)

\end{code}

Above trichotomy preservation added 20th April 2022.

Added 27 June 2018. A product of ordinals indexed by a prop is
an ordinal. Here "is" is used to indicate a construction, not a
proposition. We begin with a general lemma (and a corollary, which is
not used for our purposes).

\begin{code}

retract-accessible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     (_<_ : X → X → 𝓦 ̇ ) (_≺_ : Y → Y → 𝓣 ̇ )
                     (r : X → Y) (s : Y → X)
                   → ((y : Y) → r (s y) ≡ y)
                   → ((x : X) (y : Y) → y ≺ r x → s y < x)
                   → (x : X) → is-accessible _<_ x → is-accessible _≺_ (r x)
retract-accessible _<_ _≺_ r s η φ = transfinite-induction' _<_ P γ
 where
  P = λ x → is-accessible _≺_ (r x)

  γ : ∀ x → (∀ x' → x' < x → is-accessible _≺_ (r x')) → is-accessible _≺_ (r x)
  γ x τ = next (r x) σ
   where
    σ : ∀ y → y ≺ r x → is-accessible _≺_ y
    σ y l = transport (is-accessible _≺_) (η y) m
     where
      m : is-accessible _≺_ (r (s y))
      m = τ (s y) (φ x y l)

retract-well-founded : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                       (_<_ : X → X → 𝓦 ̇ ) (_≺_ : Y → Y → 𝓣 ̇ )
                       (r : X → Y) (s : Y → X)
                     → ((y : Y) → r (s y) ≡ y)
                     → ((x : X) (y : Y) → y ≺ r x → s y < x)
                     → is-well-founded _<_ → is-well-founded _≺_
retract-well-founded {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} _<_ _≺_ r s η φ w = w'
 where
  wr : (x : X) → is-accessible _≺_ (r x)
  wr x = retract-accessible _<_ _≺_ r s η φ x (w x)

  w' : (y : Y) → is-accessible _≺_ y
  w' y = transport (is-accessible _≺_) (η y) (wr (s y))

\end{code}

The product of a proposition-indexed family of ordinals (pip):

\begin{code}

module pip
        {𝓤 𝓥 𝓦}
        (fe : funext 𝓤 𝓥)
        (P : 𝓤 ̇ )
        (P-is-prop : is-prop P)
        (X : P → 𝓥 ̇ )
        (_<_ : {p : P} → X p → X p → 𝓦 ̇ )
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
  ψ p x q = transport X (P-is-prop p q) x

  η : (p : P) (u : Π X) → ψ p (φ p u) ≡ u
  η p = pr₂ (pr₂ (pr₂ (prop-indexed-product fe P-is-prop p)))

  ε : (p : P) (x : X p) → φ p (ψ p x) ≡ x
  ε p = pr₂ (pr₁ (pr₂ (prop-indexed-product fe P-is-prop p)))

\end{code}

The order on the product is constructed as follows from the order in
the components:

\begin{code}

 private
   _≺_ : Π X → Π X → 𝓤 ⊔ 𝓦 ̇
   u ≺ v = Σ p ꞉ P , φ p u < φ p v

 order = _≺_

\end{code}

That it is prop-valued depends only on the fact that the given order
_<_ {p} on the components of the product are prop-valued.

\begin{code}

 prop-valued : ((p : P) → is-prop-valued (_<_ {p}))
             → is-prop-valued _≺_
 prop-valued f u v = Σ-is-prop P-is-prop (λ p → f p (φ p u) (φ p v))

\end{code}

The extensionality of the constructed order depends only on the fact
that φ is a retraction.

\begin{code}

 extensional : ((p : P) → is-extensional (_<_ {p}))
             → is-extensional _≺_
 extensional e u v f g = dfunext fe γ
  where
   f' : (p : P) (x : X p) → x < φ p u → x < φ p v
   f' p x l = transport (λ - → - < φ p v) (ε p x) n'
    where
     l' : φ p (ψ p x) < φ p u
     l' = transport⁻¹ (λ - → - < φ p u) (ε p x) l

     a : ψ p x ≺ u
     a = p , l'

     m : ψ p x ≺ v
     m = f (ψ p x) a

     q : P
     q = pr₁ m

     n : φ q (ψ p x) < φ q v
     n = pr₂ m

     n' : φ p (ψ p x) < φ p v
     n' = transport (λ - → ψ p x - < φ - v) (P-is-prop q p) n

   g' : (p : P) (x : X p) → x < φ p v → x < φ p u
   g' p x l = transport (λ - → - < φ p u) (ε p x) n'
    where
     l' : φ p (ψ p x) < φ p v
     l' = transport⁻¹ (λ - → - < φ p v) (ε p x) l

     a : ψ p x ≺ v
     a = p , l'

     m : ψ p x ≺ u
     m = g (ψ p x) a

     q : P
     q = pr₁ m

     n : φ q (ψ p x) < φ q u
     n = pr₂ m

     n' : φ p (ψ p x) < φ p u
     n' = transport (λ - → ψ p x - < φ - u) (P-is-prop q p) n

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
   m' = transport (λ - → φ - v < φ - w) (P-is-prop q p) m

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
       f x u (q , l) = transport (λ - → φ p u < -) (ε p x) l'
        where
         l' : u p < ψ p x p
         l' = transport (λ - → u - < ψ p x -) (P-is-prop q p) l

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
 top-preservation p f = (λ q → transport X (P-is-prop p q) (pr₁ (f p))) , g
  where
   g : (u : Π X) → ¬ ((λ q → transport X (P-is-prop p q) (pr₁ (f p))) ≺ u)
   g u (q , l) = h n
    where
     h : ¬ (pr₁ (f q) < u q)
     h = pr₂ (f q) (u q)

     m : transport X (P-is-prop q q) (pr₁ (f q)) < u q
     m = transport (λ p → transport X (P-is-prop p q) (pr₁ (f p)) < u q) (P-is-prop p q) l

     n : pr₁ (f q) < u q
     n = transport (λ - → transport X - (pr₁ (f q)) < u q) (props-are-sets P-is-prop (P-is-prop q q) refl) m

\end{code}

Sum of an ordinal-indexed family of ordinals. To show that
extensionality is preserved, our argument uses the assumption that
each ordinal in the family has a top element or that the index type is
discrete.  (Perhaps better assumptions are possible. TODO: think about
this.) These assumptions are valid in our applications. We have three
sum submodules, the first one without assumptions.

\begin{code}

module sum
        {𝓤 𝓥 𝓦 𝓣}
        {X : 𝓤 ̇ }
        {Y : X → 𝓥 ̇ }
        (_<_ : X → X → 𝓦 ̇ )
        (_≺_ : {x : X} → Y x → Y x → 𝓣 ̇ )
      where

 open import LexicographicOrder

 private
  _⊏_ : Σ Y → Σ Y → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
  _⊏_ = slex-order _<_ _≺_

 order = _⊏_

 well-founded : is-well-founded _<_
              → ((x : X) → is-well-founded (_≺_ {x}))
              → is-well-founded _⊏_
 well-founded w w' (x , y) = φ x y
  where
   P : Σ Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
   P = is-accessible _⊏_

   γ : (x : X)
     → ((x' : X) → x' < x → (y' : Y x') → P (x' , y'))
     → (y : Y x) → P (x , y)
   γ x step = transfinite-induction _≺_ (w' x)
               (λ y → P (x , y))
               (λ y f → next (x , y) (ψ y f))
    where
     ψ : (y : Y x)
       → ((y' : Y x) → y' ≺ y → P (x , y'))
       → (z' : Σ Y) → z' ⊏ (x , y) → P z'
     ψ y f (x' , y') (inl l) = step x' l y'
     ψ y f (x' , y') (inr (r , m)) = transport⁻¹ P p α
      where
       α : P (x , transport Y r y')
       α = f (transport Y r y') m

       p : (x' , y') ≡ (x , transport Y r y')
       p = to-Σ-≡ (r , refl)

   φ : (x : X) (y : Y x) → P (x , y)
   φ = transfinite-induction _<_ w (λ x → (y : Y x) → P (x , y)) γ

 transitive : is-transitive _<_
            → ((x : X) → is-transitive (_≺_ {x}))
            → is-transitive _⊏_
 transitive t t' (a , b) (x , y) (u , v) = f
  where
   f : (a , b) ⊏ (x , y) → (x , y) ⊏ (u , v) → (a , b) ⊏ (u , v)
   f (inl l)       (inl m)          = inl (t _ _ _ l m)
   f (inl l)       (inr (q , m))    = inl (transport (λ - → a < -) q l)
   f (inr (r , l)) (inl m)          = inl (transport⁻¹ (λ - → - < u) r m)
   f (inr (r , l)) (inr (refl , m)) = inr (r , (t' x _ _ _ l m))

 prop-valued : FunExt
             → is-prop-valued _<_
             → is-well-founded _<_
             → is-extensional _<_
             → ((x : X) → is-prop-valued (_≺_ {x}))
             → is-prop-valued _⊏_
 prop-valued fe p w e f (a , b) (x , y) (inl l) (inl m) =
   ap inl (p a x l m)
 prop-valued fe p w e f (a , b) (x , y) (inl l) (inr (s , m)) =
   𝟘-elim (irreflexive _<_ x (w x) (transport (λ - → - < x) s l))
 prop-valued fe p w e f (a , b) (x , y) (inr (r , l)) (inl m) =
   𝟘-elim (irreflexive _<_ x (w x) (transport (λ - → - < x) r m))
 prop-valued fe p _ e f (a , b) (x , y) (inr (r , l)) (inr (s , m)) =
   ap inr (to-Σ-≡ (extensionally-ordered-types-are-sets _<_ fe p e r s ,
                     (f x (transport Y s b) y _ m)))

 tricho : {x : X} {y : Y x}
        → is-trichotomous-element _<_ x
        → is-trichotomous-element _≺_ y
        → is-trichotomous-element _⊏_ (x , y)
 tricho {x} {y} t u (x' , y') =
  Cases (t x')
   (λ (l : x < x') → inl (inl l))
   (cases
     (λ (p : x ≡ x')
        → Cases (u (transport⁻¹ Y p y'))
           (λ (l : y ≺ transport⁻¹ Y p y')
              → inl (inr (p , transport⁻¹-right-rel _≺_ x' x y' y p l)))
           (cases
             (λ (q : y ≡ transport⁻¹ Y p y')
                → inr (inl (to-Σ-≡
                             (p , (transport Y p y                    ≡⟨ ap (transport Y p) q ⟩
                                   transport Y p (transport⁻¹ Y p y') ≡⟨ back-and-forth-transport p ⟩
                                   y'                                 ∎
                                      )))))
             (λ (l : transport⁻¹ Y p y' ≺ y) → inr (inr (inr ((p ⁻¹) , l))))))
     (λ (l : x' < x) → inr (inr (inl l))))

 trichotomy-preservation : is-trichotomous-order _<_
                         → ((x : X) → is-trichotomous-order (_≺_ {x}))
                         → is-trichotomous-order _⊏_
 trichotomy-preservation t u (x , y) = tricho (t x) (u x y)

\end{code}

The above trichotomy preservation added 19th April 2022.

We know how to prove extensionality either assuming top elements or
assuming cotransitivity. We do this in the following two modules.

\begin{code}

module sum-top
        (fe : FunExt)
        {𝓤 𝓥 𝓦 𝓣}
        {X : 𝓤 ̇ }
        {Y : X → 𝓥 ̇ }
        (_<_ : X → X → 𝓦 ̇ )
        (_≺_ : {x : X} → Y x → Y x → 𝓣 ̇ )
        (top : Π Y)
        (ist : (x : X) → is-top _≺_ (top x))
      where

 open sum {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} _<_  _≺_ public

 private _⊏_ = order

 extensional : is-prop-valued _<_
             → is-well-founded _<_
             → ((x : X) → is-well-founded (_≺_ {x}))
             → is-extensional _<_
             → ((x : X) → is-extensional (_≺_ {x}))
             → is-extensional _⊏_
 extensional ispv w w' e e' (a , b) (x , y) f g = to-Σ-≡ (p , q)
  where
   f' : (u : X) → u < a → u < x
   f' u l = Cases (f (u , top u) (inl l))
             (λ (m : u < x)
                → m)
             (λ (σ : Σ r ꞉ u ≡ x , transport Y r (top u) ≺ y)
                → 𝟘-elim (transport-fam (is-top _≺_) u (top u)
                           (ist u) x (pr₁ σ) y (pr₂ σ)))

   g' : (u : X) → u < x → u < a
   g' u l = Cases (g (u , top u) (inl l))
             (λ (m : u < a)
                → m)
             (λ (σ : Σ r ꞉ u ≡ a , transport Y r (top u) ≺ b)
                → 𝟘-elim (transport-fam (is-top _≺_) u (top u)
                           (ist u) a (pr₁ σ) b (pr₂ σ)))

   p : a ≡ x
   p =  e a x f' g'

   f'' : (v : Y x) → v ≺ transport Y p b → v ≺ y
   f'' v l = Cases (f (x , v) (inr ((p ⁻¹) , transport-right-rel _≺_ a x b v p l)))
              (λ (l : x < x)
                 → 𝟘-elim (irreflexive _<_ x (w x) l))
              (λ (σ : Σ r ꞉ x ≡ x , transport Y r v ≺ y)
                 → φ σ)
              where
               φ : (σ : Σ r ꞉ x ≡ x , transport Y r v ≺ y) → v ≺ y
               φ (r , l) = transport
                            (λ - → transport Y - v ≺ y)
                            (extensionally-ordered-types-are-sets _<_ fe ispv e r refl)
                            l

   g'' : (u : Y x) → u ≺ y → u ≺ transport Y p b
   g'' u m = Cases (g (x , u) (inr (refl , m)))
              (λ (l : x < a)
                 → 𝟘-elim (irreflexive _<_ x (w x) (transport (λ - → x < -) p l)))
              (λ (σ : Σ r ꞉ x ≡ a , transport Y r u ≺ b)
                 → transport
                     (λ - → u ≺ transport Y - b)
                     (extensionally-ordered-types-are-sets _<_ fe ispv e ((pr₁ σ)⁻¹) p)
                     (transport-left-rel _≺_ a x b u (pr₁ σ) (pr₂ σ)))

   q : transport Y p b ≡ y
   q = e' x (transport Y p b) y f'' g''

 well-order : is-well-order _<_
            → ((x : X) → is-well-order (_≺_ {x}))
            → is-well-order _⊏_
 well-order (p , w , e , t) f = prop-valued fe p w e (λ x → prop-valuedness _≺_ (f x)) ,
                                well-founded w (λ x → well-foundedness _≺_ (f x)) ,
                                extensional
                                  (prop-valuedness _<_ (p , w , e , t))
                                     w
                                     (λ x → well-foundedness _≺_ (f x))
                                     e
                                     (λ x → extensionality _≺_ (f x)) ,
                                transitive t (λ x → transitivity _≺_ (f x))

 top-preservation : has-top _<_ → has-top _⊏_
 top-preservation (x , f) = (x , top x) , g
  where
   g : (σ : Σ Y) → ¬ ((x , top x) ⊏ σ)
   g (x' , y) (inl l)          = f x' l
   g (x' , y) (inr (refl , l)) = ist x' y l

\end{code}

\begin{code}

open import DiscreteAndSeparated

module sum-cotransitive
        (fe : FunExt)
        {𝓤 𝓥 𝓦 𝓣}
        {X : 𝓤 ̇ }
        {Y : X → 𝓥 ̇ }
        (_<_ : X → X → 𝓦 ̇ )
        (_≺_ : {x : X} → Y x → Y x → 𝓣 ̇ )
        (c : cotransitive _<_)
      where

 open sum {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} _<_  _≺_ public

 private _⊏_ = order

 extensional : is-prop-valued _<_
             → is-well-founded _<_
             → ((x : X) → is-well-founded (_≺_ {x}))
             → is-extensional _<_
             → ((x : X) → is-extensional (_≺_ {x}))
             → is-extensional _⊏_
 extensional ispv w w' e e' (a , b) (x , y) f g = to-Σ-≡ (p , q)
  where
   f' : (u : X) → u < a → u < x
   f' u l = Cases (c u a x l)
             (λ (m : u < x)
                → m)
             (λ (m : x < a)
                → let n : (x , y) ⊏ (x , y)
                      n = f (x , y) (inl m)
                  in 𝟘-elim (irreflexive _⊏_ (x , y)
                      (sum.well-founded _<_ _≺_ w w' (x , y)) n))

   g' : (u : X) → u < x → u < a
   g' u l = Cases (c u x a l)
             (λ (m : u < a)
                → m)
             (λ (m : a < x)
                → let n : (a , b) ⊏ (a , b)
                      n = g (a , b) (inl m)
                  in 𝟘-elim (irreflexive _⊏_ (a , b)
                      (sum.well-founded _<_ _≺_ w w' (a , b)) n))
   p : a ≡ x
   p =  e a x f' g'

   f'' : (v : Y x) → v ≺ transport Y p b → v ≺ y
   f'' v l = Cases (f (x , v) (inr ((p ⁻¹) , transport-right-rel _≺_ a x b v p l)))
              (λ (l : x < x)
                 → 𝟘-elim (irreflexive _<_ x (w x) l))
              (λ (σ : Σ r ꞉ x ≡ x , transport Y r v ≺ y)
                 → φ σ)
              where
               φ : (σ : Σ r ꞉ x ≡ x , transport Y r v ≺ y) → v ≺ y
               φ (r , l) = transport
                            (λ r → transport Y r v ≺ y)
                            (extensionally-ordered-types-are-sets _<_ fe
                              ispv e r refl)
                            l

   g'' : (u : Y x) → u ≺ y → u ≺ transport Y p b
   g'' u m = Cases (g (x , u) (inr (refl , m)))
              (λ (l : x < a)
                 → 𝟘-elim (irreflexive _<_ x (w x) (transport (λ - → x < -) p l)))
              (λ (σ : Σ r ꞉ x ≡ a , transport Y r u ≺ b)
                 → transport
                     (λ - → u ≺ transport Y - b)
                     (extensionally-ordered-types-are-sets _<_ fe
                       ispv e ((pr₁ σ)⁻¹) p)
                     (transport-left-rel _≺_ a x b u (pr₁ σ) (pr₂ σ)))

   q : transport Y p b ≡ y
   q = e' x (transport Y p b) y f'' g''

 well-order : is-well-order _<_
            → ((x : X) → is-well-order (_≺_ {x}))
            → is-well-order _⊏_
 well-order (p , w , e , t) f =
   prop-valued fe p w e (λ x → prop-valuedness _≺_ (f x)) ,
   well-founded w (λ x → well-foundedness _≺_ (f x)) ,
   extensional
     (prop-valuedness _<_ (p , w , e , t))
     w
     (λ x → well-foundedness _≺_ (f x))
     e
     (λ x → extensionality _≺_ (f x)) ,
   transitive t (λ x → transitivity _≺_ (f x))

\end{code}

28 June 2018.

For a universe (and hence an injective type) 𝓦 and an embedding
j : X → A, if every type in a family Y : X → 𝓦 has the structure of an
ordinal, then so does every type in the extended family Y/j : A → 𝓦.

                   j
              X ------> A
               \       /
                \     /
             Y   \   / Y/j
                  \ /
                   v
                   𝓦

This is a direct application of the construction in the module
OrdinalArithmetic.prop-indexed-product-of-ordinals.

This assumes X A : 𝓦, and that the given ordinal structure is
W-valued. More generally, we have the following typing, for which the
above triangle no longer makes sense, because Y / j : A → 𝓤 ⊔ 𝓥 ⊔ 𝓦,
but the constructions still work.

\begin{code}

open import UF-Embeddings
open import UF-Equiv

module extension
        (fe : FunExt)
        {𝓤 𝓥 𝓦}
        {X : 𝓤 ̇ }
        {A : 𝓥 ̇ }
        (Y : X → 𝓦 ̇ )
        (j : X → A)
        (j-is-embedding : is-embedding j)
        (_<_ : {x : X} → Y x → Y x → 𝓦 ̇ )
        (a : A)
       where

 open import InjectiveTypes fe

 private
  _≺_ : (Y / j) a → (Y / j) a → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  u ≺ v = Σ p ꞉ fiber j a , u p < v p

 order = _≺_

 well-order : ((x : X) → is-well-order (_<_ {x}))
            → is-well-order _≺_
 well-order o = pip.well-order
                 (fe (𝓤 ⊔ 𝓥) 𝓦)
                 (fiber j a)
                 (j-is-embedding a)
                 (λ (p : fiber j a) → Y (pr₁ p))
                 (λ {p : fiber j a} y y' → y < y')
                 (λ (p : fiber j a) → o (pr₁ p))

 top-preservation : ((x : X) → has-top (_<_ {x})) → has-top _≺_
 top-preservation f = φ , g
   where
    φ : (p : fiber j a) → Y (pr₁ p)
    φ (x , r) = pr₁ (f x)

    g : (ψ : (Y / j) a) → ¬ (φ ≺ ψ)
    g ψ ((x , r) , l) = pr₂ (f x) (ψ (x , r)) l

\end{code}
