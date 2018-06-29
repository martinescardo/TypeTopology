Martin Escardo, 21 June 2018

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module OrdinalArithmetic where

open import SpartanMLTT
open import Ordinals hiding (_≤_)
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt

\end{code}

Any proposition is an ordinal under the empty ordering.

\begin{code}

module subsingleton-ordinal
        {U V}
        (P : U ̇)
        (isp : is-prop P)
       where

 private _<_ : P → P → V ̇
 x < y = 𝟘

 order = _<_

 prop-valued : is-prop-valued-order _<_
 prop-valued x y = 𝟘-is-prop

 extensional : is-extensional _<_
 extensional x y f g = isp x y 

 transitive : is-transitive _<_
 transitive x y z ()

 well-founded : is-well-founded _<_
 well-founded x = next x (λ y ())

 ordinal : is-ordinal _<_
 ordinal = prop-valued , well-founded , extensional , transitive

\end{code}

Two particular cases are 𝟘 and 𝟙, of course.

The sum of two ordinals.

\begin{code}

module _ {U V W}
         {X : U ̇}
         (_<_ : X → X → W ̇)
         {Y : V ̇}
         (_≺_ : Y → Y → W ̇)
       where

 private
  _⊏_ : X + Y → X + Y → W ̇
  (inl x) ⊏ (inl x') = x < x'
  (inl x) ⊏ (inr y') = 𝟙
  (inr y) ⊏ (inl x') = 𝟘
  (inr y) ⊏ (inr y') = y ≺ y'

 addition = _⊏_
  
 addition-prop-valued : is-prop-valued-order _<_
                     → is-prop-valued-order _≺_
                     → is-prop-valued-order _⊏_
 addition-prop-valued p₀ p₁ (inl x) (inl x') l m = p₀ x x' l m
 addition-prop-valued p₀ p₁ (inl x) (inr y') * * = refl
 addition-prop-valued p₀ p₁ (inr y) (inl x') () m
 addition-prop-valued p₀ p₁ (inr y) (inr y') l m = p₁ y y' l m

 addition-extensional : is-well-founded _<_
                      → is-extensional _<_
                      → is-extensional _≺_
                      → is-extensional _⊏_
 addition-extensional w₀ e₀ e₁ (inl x) (inl x') f g = ap inl (e₀ x x' (f ∘ inl) (g ∘ inl))
 addition-extensional w₀ e₀ e₁ (inl x) (inr y') f g = 𝟘-elim (≤-refl _<_ x (w₀ x) (g (inl x) *))
 addition-extensional w₀ e₀ e₁ (inr y) (inl x') f g = 𝟘-elim (≤-refl _<_ x' (w₀ x') (f (inl x') *))
 addition-extensional w₀ e₀ e₁ (inr y) (inr y') f g = ap inr (e₁ y y' (f ∘ inr) (g ∘ inr))

 addition-transitive : is-transitive _<_
                     → is-transitive _≺_
                     → is-transitive _⊏_
 addition-transitive t₀ t₁ (inl x) (inl x') (inl z₀) l m = t₀ x x' z₀ l m
 addition-transitive t₀ t₁ (inl x) (inl x') (inr z₁) l m = *
 addition-transitive t₀ t₁ (inl x) (inr y') (inl z₀) l ()
 addition-transitive t₀ t₁ (inl x) (inr y') (inr z₁) l m = *
 addition-transitive t₀ t₁ (inr y) (inl x') z () m
 addition-transitive t₀ t₁ (inr y) (inr y') (inl z₁) l ()
 addition-transitive t₀ t₁ (inr y) (inr y') (inr z₁) l m = t₁ y y' z₁ l m
  
 addition-well-founded : is-well-founded _<_
                       → is-well-founded _≺_
                       → is-well-founded _⊏_
 addition-well-founded w₀ w₁ = g
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
     τ (inl x) l = φ x (w₀ x)
     τ (inr y') l = γ y' (σ y' l)
   g : is-well-founded _⊏_
   g (inl x) = φ x (w₀ x) 
   g (inr y) = γ y (w₁ y)

 addition-ordinal : is-ordinal _<_
                  → is-ordinal _≺_
                  → is-ordinal _⊏_
 addition-ordinal (p₀ , w₀ , e₀ , t₀) (p₁ , w₁ , e₁ , t₁) = addition-prop-valued p₀ p₁ ,
                                                            addition-well-founded w₀ w₁ ,
                                                            addition-extensional w₀ e₀ e₁ ,
                                                            addition-transitive t₀ t₁

\end{code}

Successor.

\begin{code}

module _ {U V}
         {X : U ̇}
         (_<_ : X → X → V ̇)
       where
  
  private
   _<[𝟙]_ : 𝟙 → 𝟙 → V ̇
   _<[𝟙]_ = subsingleton-ordinal.order {U} 𝟙 𝟙-is-prop

   _<'_ : X + 𝟙 → X + 𝟙 → V ̇
   _<'_ = addition _<_ _<[𝟙]_

  successor = _<'_

\end{code}

Multiplication. Cartesian product with the lexicographic order.

\begin{code}

module _ {U V W T}
         {X : U ̇}
         (_<_ : X → X → W ̇)
         {Y : V ̇}
         (_≺_ : Y → Y → T ̇)
       where

 private
  _⊏_ : X × Y → X × Y → U ⊔ W ⊔ T ̇
  (a , b) ⊏ (x , y) = (a < x) + ((a ≡ x) × (b ≺ y))

 multiplication = _⊏_

 multiplication-well-founded : is-well-founded _<_
                            → is-well-founded _≺_
                            → is-well-founded _⊏_
 multiplication-well-founded w w' (x , y) = φ x y
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

 multiplication-transitive : is-transitive _<_
                          → is-transitive _≺_
                          → is-transitive _⊏_
 multiplication-transitive t t' (a , b) (x , y) (u , v) = f
  where
   f : (a , b) ⊏ (x , y) → (x , y) ⊏ (u , v) → (a , b) ⊏ (u , v)
   f (inl l) (inl m) = inl (t _ _ _ l m)
   f (inl l) (inr (q , m)) = inl (transport (λ x → a < x) q l)
   f (inr (r , l)) (inl m) = inl (back-transport (λ x → x < u) r m)
   f (inr (r , l)) (inr (refl , m)) = inr (r , (t' _ _ _ l m))

 multiplication-extensional : is-well-founded _<_
                            → is-well-founded _≺_
                            → is-extensional _<_
                            → is-extensional _≺_
                            → is-extensional _⊏_
 multiplication-extensional w w' e e' (a , b) (x , y) f g = ×-≡ p q 
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
   f'' v l = cases
               (λ (m : a < x) → 𝟘-elim (≤-refl _≺_ b (w' b) (cases
                                                               (λ (n : a < a) → 𝟘-elim (≤-refl _<_ a (w a) n))
                                                               (λ (σ : (a ≡ a) × (b ≺ b)) → 𝟘-elim (≤-refl _≺_ b (w' b) (pr₂ σ)))
                                                               (g (a , b) (inl m)))))
              (λ (σ : (a ≡ x) × (v ≺ y)) → pr₂ σ)
              (f (a , v) (inr (refl , l)))
   g'' : (v : Y) → v ≺ y → v ≺ b
   g'' v l = cases
              (λ (m : x < a) → cases
                                 (λ (m : x < x) → 𝟘-elim (≤-refl _<_ x (w x) m))
                                 (λ (σ : (x ≡ x) × (y ≺ y)) → 𝟘-elim (≤-refl _≺_ y (w' y) (pr₂ σ)))
                                 (f (x , y) (inl m)))
              (λ (σ : (x ≡ a) × (v ≺ b)) → pr₂ σ)
              (g (x , v) (inr (refl , l)))
   q : b ≡ y
   q = e' b y f'' g''

 multiplication-ordinal : (∀ U V → funext U V) → is-ordinal _<_ → is-ordinal _≺_ → is-ordinal _⊏_
 multiplication-ordinal fe (p , w , e , t) (p' , w' , e' , t') =
   multiplication-prop-valued ,
   multiplication-well-founded w w' ,
   multiplication-extensional w w' e e' ,
   multiplication-transitive t t'
  where
   multiplication-prop-valued : is-prop-valued-order _⊏_
   multiplication-prop-valued (a , b) (x , y) (inl l) (inl m) = ap inl (p a x l m)
   multiplication-prop-valued (a , b) (x , y) (inl l) (inr (s , m)) =
     𝟘-elim (≤-refl _<_ x (w x) (transport (λ a → a < x) s l))
   multiplication-prop-valued (a , b) (x , y) (inr (r , l)) (inl m) =
     𝟘-elim (≤-refl _<_ x (w x) (transport (λ a → a < x) r m))
   multiplication-prop-valued (a , b) (x , y) (inr (r , l)) (inr (s , m)) =
    ap inr (×-≡ (ordinal-gives-is-set _<_ fe (p , w , e , t) r s) (p' b y l m))

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

module _ {U V W}
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

 pip = _≺_

\end{code}

That it is subsingleton-valued depends only on the fact that the given
order _<_ {p} on the components of the product are
subsingleton-valued.

\begin{code}

 pip-prop-valued : ((p : P) → is-prop-valued-order (_<_ {p}))
                → is-prop-valued-order _≺_
 pip-prop-valued f u v = is-prop-closed-under-Σ isp (λ p → f p (φ p u) (φ p v))

\end{code}

The extensionality of the constructed order depends only on the fact
that φ is a retraction.

\begin{code}

 pip-extensional : ((p : P) → is-extensional (_<_ {p}))
                 → is-extensional _≺_
 pip-extensional e u v f g = dfunext fe γ
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

 pip-transitive : ((p : P) → is-transitive (_<_ {p}))
               → is-transitive _≺_
 pip-transitive t u v w (p , l) (q , m) = p , f l m'
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

 pip-well-founded : ((p : P) → is-well-founded (_<_ {p}))
                 → is-well-founded _≺_
 pip-well-founded w u = next u σ
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
{-     
 pip-ordinal : is-ordinal _<_ → is-ordinal _≺_
 pip-ordinal o = pip-prop-valued ? , pip-well-founded ? , pip-extensional ? , pip-transitive ?
-}

 pip-ordinal : ((p : P) → is-ordinal (_<_ {p}))
             → is-ordinal _≺_
 pip-ordinal o = pip-prop-valued  (λ p → is-prop-valued-ordinal _<_ (o p)) ,
                 pip-well-founded (λ p → is-well-founded-ordinal _<_ (o p)) ,
                 pip-extensional  (λ p → is-extensional-ordinal _<_ (o p)) ,
                 pip-transitive   (λ p → is-transitive-ordinal _<_ (o p))
 
\end{code}

Could a proof using univalence be shorter?

Sum of an ordinal-indexed family of ordinals.

\begin{code}

open import Ordinals

module _
        {U V W T}
        {X : U ̇}
        {Y : X → V ̇}
        (_<_ : X → X → W ̇) (_≺_ : {x : X} → Y x → Y x → T ̇)
        
       where

 open import LexicographicOrder

 private
  _⊏_ : Σ Y → Σ Y → U ⊔ W ⊔ T ̇
  _⊏_ = slex-order _<_ _≺_

 sum = _⊏_

 sum-well-founded : is-well-founded _<_ 
                  → ({x : X} → is-well-founded (_≺_ {x}))
                  → is-well-founded _⊏_
 sum-well-founded w w' (x , y) = φ x y
  where
   P : Σ Y → U ⊔ V ⊔ W ⊔ T ̇
   P = is-accessible _⊏_
   γ : (x : X) → ((x' : X) → x' < x → (y' : Y x') → P(x' , y')) → (y : Y x) → P(x , y)
   γ x step = transfinite-induction _≺_ w' (λ y → P(x , y)) (λ y f → next (x , y) (ψ y f))
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

 sum-transitive : is-transitive _<_
           → ({x : X} → is-transitive (_≺_ {x}))
           → is-transitive _⊏_
 sum-transitive t t' (a , b) (x , y) (u , v) = f
  where
   f : (a , b) ⊏ (x , y) → (x , y) ⊏ (u , v) → (a , b) ⊏ (u , v)
   f (inl l) (inl m) = inl (t _ _ _ l m)
   f (inl l) (inr (q , m)) = inl (transport (λ x → a < x) q l)
   f (inr (r , l)) (inl m) = inl (back-transport (λ x → x < u) r m)
   f (inr (r , l)) (inr (refl , m)) = inr (r , (t' _ _ _ l m))

\end{code}

Extensionality. Attempt to find a suitable hypothesis to get it. Don't
forget to remove spurious hypotheses when we finish.

\begin{code}

{-
 preserve-top : (x : X) (y : Y x) → ((y' : Y x) → ¬(y ≺ y'))
     → (x' : X) (r : x ≡ x') (y'' : Y x') → ¬ (transport Y r y ≺ y'')
 preserve-top x y top .x refl v = top v

 preserve-bot : (x : X) (y : Y x) → ((y' : Y x) → ¬(y' ≺ y))
     → (x' : X) (r : x ≡ x') (y'' : Y x') → ¬ (y'' ≺ transport Y r y)
 preserve-bot x y bot .x refl v = bot v

 blah : (a x : X) (b : Y a) (v : Y x) (p : a ≡ x) →  v ≺ transport Y p b → back-transport Y p v ≺ b
 blah a .a b v refl l = l

 open import DiscreteAndSeparated

 sum-extensional : is-well-founded _<_ → ((x : X)
                → is-well-founded (_≺_ {x}))
                → (top : Π Y)
                → ((x : X) (y : Y x) → ¬(top x ≺ y))
                → (bot : Π Y)
                → ((x : X) (y : Y x) → ¬(y ≺ bot x))
                → ((x x' : X) → x < x' → isolated x)
                → is-extensional _<_ → ((x : X) → is-extensional (_≺_ {x})) → is-extensional _⊏_
 sum-extensional w w' top ist bot isb i e e' (a , b) (x , y) f g = to-Σ-≡'' (p , q)
  where
   f' : (u : X) → u < a → u < x
   f' u l = cases
             (λ (m : u < x) → m)
             (λ (σ : Σ \(r : u ≡ x) → transport Y r (top u) ≺ y) → 𝟘-elim (preserve-top u (top u) (ist u) x (pr₁ σ) y (pr₂ σ)))
             (f (u , top u) (inl l))

   g' : (u : X) → u < x → u < a
   g' u l = cases
             (λ (m : u < a) → m)
             (λ (σ : Σ \(r : u ≡ a) → transport Y r (top u) ≺ b) → 𝟘-elim (preserve-top u (top u) (ist u) a (pr₁ σ) b (pr₂ σ)))
             (g (u , top u) (inl l))

   p : a ≡ x
   p =  e a x f' g'
   f'' : (v : Y x) → v ≺ transport Y p b → v ≺ y
   f'' v l = cases
              (λ (l : x < x) → 𝟘-elim (≤-refl _<_ x (w x) l))
              (λ (σ : Σ \(r : x ≡ x) → transport Y r v ≺ y)  → φ σ)
              (f (x , v) (inr ((p ⁻¹) , blah a x b v p l)))
     where
      φ : (σ : Σ \(r : x ≡ x) → transport Y r v ≺ y) → v ≺ y
      φ (r , l) = {!!}
       where
        aaa : {!!}
        aaa = {!!}
      
   g'' : (u : Y x) → u ≺ y → u ≺ transport Y p b
   g'' u m = {!!}
   q : transport Y p b ≡ y
   q = e' x (transport Y p b) y f'' g''

-}

{-
 lex-order-ordinal : is-ordinal _<_ → ({x : X} → is-ordinal (_≺_ {x})) → is-ordinal _⊏_
 lex-order-ordinal (isp , w₀ , e₀ , t₀) f = sum-well-founded w₀ (λ {x} → pr₁ {!f!}) ,
                                     sum-extensional e₀ {!λ {x} → pr₁(f {x})!} ,
                                     sum-transitive t₀ {!λ {x} → pr₁(f {x})!}
-}

\end{code}
