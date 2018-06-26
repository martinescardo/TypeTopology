Martin Escardo, 21 June 2018

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module OrdinalArithmetic where

open import SpartanMLTT hiding (_≤_)
open import Ordinals hiding (_≤_)
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt

\end{code}

Any proposition is an ordinal under the empty ordering.

\begin{code}

module subsingleton-ordinal {U V} (P : U ̇) (isp : is-prop P) where

 private _<_ : P → P → V ̇
 _<_ x y = 𝟘

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
    ap inr (×-≡ (ordinal-gives-is-set _<_ fe p (p , w , e , t) r s) (p' b y l m))

{- The following doesn't work without further assumptions:

 multiplication-cotransitive : cotransitive _<_ → cotransitive _≺_ → cotransitive _⊏_
 multiplication-cotransitive c c' (u , v) (a , b) (x , y) (inl l) = f(c u a x l)
  where
   f : (u < x) + (x < a) → ((u , v) ⊏ (x , y)) + ((x , y) ⊏ (a , b))
   f (inl m) = inl (inl m)
   f (inr m) = inr (inl m)
 multiplication-cotransitive c c' (u , v) (a , b) (x , y) (inr (r , l)) = f (c' v b y l)
   where
   f : (v ≺ y) + (y ≺ b) → ((u , v) ⊏ (x , y)) + ((x , y) ⊏ (a , b))
   f (inl m) = {!!}
   f (inr m) = inl {!!}
-}

\end{code}
