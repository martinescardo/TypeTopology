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

module subsingleton-ordinal {U V} (P : U ̇) (isp : is-prop P) where

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

module _ {U V W} {X₀ : U ̇} (_<₀_ : X₀ → X₀ → W ̇) {X₁ : V ̇} (_<₁_ : X₁ → X₁ → W ̇) where

 private _<_ : X₀ + X₁ → X₀ + X₁ → W ̇
 (inl x₀) < (inl y₀) = x₀ <₀ y₀
 (inl x₀) < (inr y₁) = 𝟙
 (inr x₁) < (inl y₀) = 𝟘
 (inr x₁) < (inr y₁) = x₁ <₁ y₁

 addition = _<_
  
 addition-prop-valued : is-prop-valued-order _<₀_ → is-prop-valued-order _<₁_ → is-prop-valued-order _<_
 addition-prop-valued p₀ p₁ (inl x₀) (inl y₀) l m = p₀ x₀ y₀ l m
 addition-prop-valued p₀ p₁ (inl x₀) (inr y₁) * * = refl
 addition-prop-valued p₀ p₁ (inr x₁) (inl y₀) () m
 addition-prop-valued p₀ p₁ (inr x₁) (inr y₁) l m = p₁ x₁ y₁ l m

 addition-extensional : is-well-founded _<₀_ → is-extensional _<₀_ → is-extensional _<₁_ → is-extensional _<_
 addition-extensional w₀ e₀ e₁ (inl x₀) (inl y₀) f g = ap inl (e₀ x₀ y₀ (f ∘ inl) (g ∘ inl))
 addition-extensional w₀ e₀ e₁ (inl x₀) (inr y₁) f g = 𝟘-elim (≤-refl _<₀_ x₀ (w₀ x₀) (g (inl x₀) *))
 addition-extensional w₀ e₀ e₁ (inr x₁) (inl y₀) f g = 𝟘-elim (≤-refl _<₀_ y₀ (w₀ y₀) (f (inl y₀) *))
 addition-extensional w₀ e₀ e₁ (inr x₁) (inr y₁) f g = ap inr (e₁ x₁ y₁ (f ∘ inr) (g ∘ inr))

 addition-transitive : is-transitive _<₀_ → is-transitive _<₁_ → is-transitive _<_
 addition-transitive t₀ t₁ (inl x₀) (inl y₀) (inl z₀) l m = t₀ x₀ y₀ z₀ l m
 addition-transitive t₀ t₁ (inl x₀) (inl y₀) (inr z₁) l m = *
 addition-transitive t₀ t₁ (inl x₀) (inr y₁) (inl z₀) l ()
 addition-transitive t₀ t₁ (inl x₀) (inr y₁) (inr z₁) l m = *
 addition-transitive t₀ t₁ (inr x₁) (inl y₀) z () m
 addition-transitive t₀ t₁ (inr x₁) (inr y₁) (inl z₁) l ()
 addition-transitive t₀ t₁ (inr x₁) (inr y₁) (inr z₁) l m = t₁ x₁ y₁ z₁ l m
  
 addition-well-founded : is-well-founded _<₀_ → is-well-founded _<₁_ → is-well-founded _<_
 addition-well-founded w₀ w₁ = g
  where
   φ : (x₀ : X₀) → is-accessible _<₀_ x₀ → is-accessible _<_ (inl x₀)
   φ x₀ (next .x₀ σ) = next (inl x₀) τ
    where
     τ : (s : X₀ + X₁) → s < inl x₀ → is-accessible _<_ s
     τ (inl y₀) l = φ y₀ (σ y₀ l)
     τ (inr y₁) ()
   γ : (x₁ : X₁) → is-accessible _<₁_ x₁ → is-accessible _<_ (inr x₁)
   γ x₁ (next .x₁ σ) = next (inr x₁) τ
    where
     τ : (s : X₀ + X₁) → s < inr x₁ → is-accessible _<_ s
     τ (inl x₀) l = φ x₀ (w₀ x₀)
     τ (inr y₁) l = γ y₁ (σ y₁ l)
   g : is-well-founded _<_
   g (inl x₀) = φ x₀ (w₀ x₀) 
   g (inr x₁) = γ x₁ (w₁ x₁)

 addition-ordinal : is-ordinal _<₀_ → is-ordinal _<₁_ → is-ordinal _<_
 addition-ordinal (p₀ , w₀ , e₀ , t₀) (p₁ , w₁ , e₁ , t₁) = addition-prop-valued p₀ p₁ ,
                                                           addition-well-founded w₀ w₁ ,
                                                           addition-extensional w₀ e₀ e₁ ,
                                                           addition-transitive t₀ t₁

\end{code}

Successor.

\begin{code}

module _ {U V} {X : U ̇} (_<_ : X → X → V ̇) where

  _<[𝟙]_ : 𝟙 → 𝟙 → V ̇
  _<[𝟙]_ = subsingleton-ordinal.order {U} 𝟙 𝟙-is-prop
  
  private _<'_ : X + 𝟙 → X + 𝟙 → V ̇
  _<'_ = addition _<_ _<[𝟙]_

  successor = _<'_

\end{code}

Multiplication

\begin{code}

module _ {U V W T} {X : U ̇} (_<_ : X → X → W ̇) {Y : V ̇} (_≺_ : Y → Y → T ̇) where

 private _⊏_ : X × Y → X × Y → U ⊔ W ⊔ T ̇
 (a , b) ⊏ (x , y) = (a < x) + ((a ≡ x) × (b ≺ y))

 multiplication = _⊏_

 multiplication-well-founded : is-well-founded _<_ → is-well-founded _≺_ → is-well-founded _⊏_
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

 multiplication-transitive : is-transitive _<_ → is-transitive _≺_ → is-transitive _⊏_
 multiplication-transitive t t' (a , b) (x , y) (u , v) = f
  where
   f : (a , b) ⊏ (x , y) → (x , y) ⊏ (u , v) → (a , b) ⊏ (u , v)
   f (inl l) (inl m) = inl (t _ _ _ l m)
   f (inl l) (inr (q , m)) = inl (transport (λ x → a < x) q l)
   f (inr (r , l)) (inl m) = inl (back-transport (λ x → x < u) r m)
   f (inr (r , l)) (inr (refl , m)) = inr (r , (t' _ _ _ l m))

 multiplication-extensional : is-well-founded _<_ → is-well-founded _≺_
                            → is-extensional _<_ → is-extensional _≺_ → is-extensional _⊏_
 multiplication-extensional w w' e e' (a , b) (x , y) f g = ×-≡ p q 
  where
   f' : (u : X) → u < a → u < x
   f' u l = cases (λ (m : u < x) → m)
                  (λ (σ : (u ≡ x) × (y ≺ y)) → 𝟘-elim (≤-refl _≺_ y (w' y) (pr₂ σ)))
                  (f (u , y) (inl l))
   g' : (u : X) → u < x → u < a
   g' u l = cases (λ (m : u < a) → m)
                  (λ (σ : (u ≡ a) × (b ≺ b)) → 𝟘-elim (≤-refl _≺_ b (w' b) (pr₂ σ)))
                  (g ((u , b)) (inl l))
   p : a ≡ x
   p = e a x f' g'
   f'' : (v : Y) → v ≺ b → v ≺ y
   f'' v l = cases (λ (m : a < x) → 𝟘-elim (≤-refl _≺_ b (w' b) (cases (λ (n : a < a) → 𝟘-elim (≤-refl _<_ a (w a) n))
                                                                         (λ (σ : (a ≡ a) × (b ≺ b)) → 𝟘-elim (≤-refl _≺_ b (w' b) (pr₂ σ)))
                                                                         (g (a , b) (inl m)))))
                   (λ (σ : (a ≡ x) × (v ≺ y)) → pr₂ σ)
                   (f (a , v) (inr (refl , l)))
   g'' : (v : Y) → v ≺ y → v ≺ b
   g'' v l = cases (λ (m : x < a) → cases (λ (m : x < x) → 𝟘-elim (≤-refl _<_ x (w x) m))
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

module prop-indexed-product-of-ordinals
        {U V W}
        (P : U ̇)
        (isp : is-prop P)
        (X : P → V ̇)
        (isp : is-prop P)
        (_<_ : {p : P} → X p → X p → W ̇)
        (o : (p : P) → is-ordinal (_<_ {p}))
        (fe : funext U V)
       where

 open import UF-Equiv
 open import UF-PropIndexedPiSigma
 
 φ : (p : P) → Π X → X p
 φ p u = u p
 
 ψ : (p : P) → X p → Π X
 ψ p x q = transport X (isp p q) x

 η : (p : P) (u : Π X) → ψ p (φ p u) ≡ u
 η p = pr₂(pr₂(pr₂ (prop-indexed-product fe isp p)))

 ε : (p : P) (x : X p) → φ p (ψ p x) ≡ x
 ε p = pr₂(pr₁(pr₂ (prop-indexed-product fe isp p)))

 private _≺_ : Π X → Π X → U ⊔ W ̇
 u ≺ v = Σ \(p : P) → φ p u < φ p v

 order = _≺_

 prop-valued : is-prop-valued-order _≺_
 prop-valued u v = is-prop-closed-under-Σ isp
                     (λ p → is-prop-valued-ordinal (_<_ {p}) (o p) (φ p u) (φ p v))

 extensional : is-extensional _≺_
 extensional u v f g = dfunext fe γ
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
   δ p = is-extensional-ordinal (_<_ {p}) (o p) (u p) (v p) (f' p) (g' p)
   γ : u ∼ v
   γ = δ

 transitive : is-transitive _≺_
 transitive u v w (p , l) (q , m) = p , t l m'
  where
   t : φ p u < φ p v → φ p v < φ p w → φ p u < φ p w
   t = is-transitive-ordinal (_<_ {p}) (o p) (φ p u) (φ p v) (φ p w)
   m' : φ p v < φ p w
   m' = transport (λ q → φ q v < φ q w) (isp q p) m

 well-founded : is-well-founded _≺_
 well-founded u = next u σ
  where
   a : (p : P) (u : X p) → is-accessible _<_ u
   a p = is-well-founded-ordinal (_<_ {p}) (o p)
   σ : (v : Π X) → v ≺ u → is-accessible _≺_ v
   σ v (p , l) = d
    where
     b : is-accessible _<_ (φ p v)
     b = prev _<_ (φ p u) (a p (φ p u)) (φ p v) l
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
     
 ordinal : is-ordinal _≺_
 ordinal = prop-valued , well-founded , extensional , transitive

\end{code}

Could a proof using univalence be shorter?

