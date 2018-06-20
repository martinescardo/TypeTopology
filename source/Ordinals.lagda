Martin Escardo, April 2013, adapted to this development June 2018

Ordinals like in the HoTT book and variations.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (_≤_)
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-Subsingletons-FunExt

module Ordinals {U V : Universe}
                {X : U ̇}
                (_<_ : X → X → V ̇)
                where

prop-valued : U ⊔ V ̇
prop-valued = ({x y : X} → is-prop(x < y))

data is-accessible : X → U ⊔ V ̇ where
 next : (x : X) → ((y : X) → y < x → is-accessible y) → is-accessible x

accessible-induction : ∀ {W} (P : (x : X) → is-accessible x → W ̇)
                    → ((x : X) (σ : (y : X) → y < x → is-accessible y)
                        → ((y : X) (l : y < x) → P y (σ y l))
                        → P x (next x σ))
                    → (x : X) (a : is-accessible x) → P x a
accessible-induction P step = h
  where
   h : (x : X) (a : is-accessible x) → P x a
   h x (next .x σ) = step x σ (λ y l → h y (σ y l))

prev : (x : X) → is-accessible x → (y : X) → y < x → is-accessible y
prev = accessible-induction (λ x _ → (y : X) → y < x → is-accessible y)
                            (λ x σ f y l → σ y l)

prev-behaviour : (x : X) → ∀(a : is-accessible x) → next x (prev x a) ≡ a
prev-behaviour = accessible-induction _ (λ _ _ _ → refl)

transfinite-induction' :  ∀ {W} (P : X → W ̇)
                         → ((x : X) → (∀(y : X) → y < x → P y) → P x)
                         → (x : X) → is-accessible x → P x
transfinite-induction' P f = accessible-induction (λ x _ → P x)
                                                  (λ x _ → f x)

well-founded : U ⊔ V ̇
well-founded = (x : X) → is-accessible x

Well-founded : ∀ {W} → U ⊔ V ⊔ W ′ ̇
Well-founded {W} = (P : X → W ̇) → ((x : X) → ((y : X) → y < x → P y) → P x)
                                 → (x : X) → P x

transfinite-induction : well-founded → ∀ {W} → Well-founded {W}
transfinite-induction w P f x = transfinite-induction' P f x (w x)

transfinite-induction-converse : Well-founded {U ⊔ V} → well-founded
transfinite-induction-converse F = F is-accessible next

transfinite-recursion : well-founded → ∀ {W} {Y : W ̇}
                     → ((x : X) → ((y : X) → y < x → Y) → Y) → X → Y
transfinite-recursion w {W} {Y} = transfinite-induction w (λ x → Y)

transitive : U ⊔ V ̇
transitive = (x y z : X) → x < y → y < z → x < z

co-transitive : U ⊔ V ̇
co-transitive = {x y z : X} → x < y → x < z + x < y

_≼_ : X → X → U ⊔ V ̇
x ≼ y = ∀ u → u < x → u < y

≼-prop-valued : funext U V → funext V V
              → prop-valued
              → {x y : X} → is-prop(x ≼ y)
≼-prop-valued fe fe' isp = is-prop-exponential-ideal fe
                              (λ u → is-prop-exponential-ideal fe' (λ l → isp))

≼-refl : {x : X} → x ≼ x
≼-refl u l = l

≼-trans : {x y z : X} → x ≼ y → y ≼ z → x ≼ z
≼-trans f g u l = g u (f u l)

extensional : U ⊔ V ̇
extensional = {x y : X} → x ≼ y → y ≼ x → x ≡ y 

extensional' : U ⊔ V ̇
extensional' = {x y : X} → ((u : X) → (u < x) ⇔ (u < y)) → x ≡ y 

extensional-extensional' : extensional → extensional'
extensional-extensional' e {x} {y} f = e {x} {y} (λ u l → pr₁ (f u) l)
                                                 (λ u l → pr₂ (f u) l)

extensional'-extensional : extensional' → extensional
extensional'-extensional e' {x} {y} g h = e' (λ u → (g u , h u))

ordinal : U ⊔ V ̇
ordinal = well-founded × extensional × transitive

is-accessible-is-prop : funext U (U ⊔ V) → funext V (U ⊔ V)
                      → (x : X) → is-prop(is-accessible x)
is-accessible-is-prop fe fe' = accessible-induction P φ
 where
  P : (x : X) → is-accessible x → U ⊔ V ̇
  P x a = (b : is-accessible x) → a ≡ b

  φ : (x : X) (σ : (y : X) → y < x → is-accessible y)
    → ((y : X) (l : y < x) (a : is-accessible y) → σ y l ≡ a)
    → (b : is-accessible x) → next x σ ≡ b
  φ x σ IH b = next x σ ≡⟨ ap (λ f → next x f) (dfunext fe (λ y → dfunext fe' (h y))) ⟩
               next x τ ≡⟨ prev-behaviour x b ⟩
               b ∎
   where
    τ : (y : X) (l : y < x) → is-accessible y
    τ = prev x b
    h :  (y : X) (l : y < x) → σ y l ≡ τ y l
    h y l = IH y l (τ y l)

well-founded-is-prop : funext U (U ⊔ V) → funext V (U ⊔ V) → is-prop well-founded
well-founded-is-prop fe fe' = is-prop-exponential-ideal fe (is-accessible-is-prop fe fe')


extensional-gives-is-set : funext U V → funext V V → prop-valued
                         → extensional → is-set X
extensional-gives-is-set fe fe' isp e = identification-collapsible-is-set (f , κ)
 where
  f : {x y :  X} → x ≡ y → x ≡ y
  f {x} {y} p = e (transport (λ z → x ≼ z) p (≼-refl {x}))
                  (transport (λ z → z ≼ x) p (≼-refl {x}))
  ec : {x y : X} {l l' : x ≼ y} {m m' : y ≼ x} → e l m ≡ e l' m'
  ec {x} {y} {l} {l'} {m} {m'} = ap₂ e (≼-prop-valued fe fe' isp l l')
                                       (≼-prop-valued fe fe' isp m m')
  κ : {x y : X} → constant (f {x} {y})
  κ p q = ec
  
_≤_ : X → X → V ̇
x ≤ y = ¬(y < x)

<-gives-≤  : (x : X) → is-accessible x → ∀ y → y < x → y ≤ x
<-gives-≤ = transfinite-induction' (λ x → (y : X) → y < x → y ≤ x)
                                   (λ x f y l m → f y l x m l) 

≤-refl : (x : X) → is-accessible x → x ≤ x
≤-refl x a l = <-gives-≤ x a x l l

non-strict-trans : (z : X) → is-accessible z
                 → (x y : X) → x < y → y < z → x ≤ z
non-strict-trans = transfinite-induction' (λ z → (x y : X) → x < y → y < z → x ≤ z)
                                          (λ z f x y l m n → f y m z x n l m)

<-gives-≼ : transitive → {x y : X} → x < y → x ≼ y
<-gives-≼ t l u m = t _ _ _ m l

≼-gives-≤ : (y : X) → is-accessible y → (x : X) → x ≼ y → x ≤ y
≼-gives-≤ y a x f l = ≤-refl y a (f y l)

\end{code}

When do we get x ≤ y → x ≼ y (say for ordinals)? When do we get cotransitivity?

\begin{code}

no-minimal-is-empty : well-founded → ∀ {W} (P : X → W ̇)
                    → ((x : X) → P x → Σ \(y : X) → (y < x) × P y) → is-empty(Σ P)
no-minimal-is-empty w P s (x , p) = f s x p
 where
  f : ((x : X) → P x → Σ \(y : X) → (y < x) × P y) → (x : X) → ¬(P x)
  f s x p = g x (w x) p
   where
    g : (x : X) → is-accessible x → ¬(P x)
    g x (next .x σ) p = IH (pr₁ (s x p)) (pr₁(pr₂(s x p))) (pr₂(pr₂(s x p)))
     where
      IH : (y : X) → y < x → ¬(P y)
      IH y l = g y (σ y l)

  NB : Σ P → ¬((x : X) → P x → Σ \(y : X) → (y < x) × P y)
  NB (x , p) s = f s x p 

\end{code}

We will need the following weakening of well-foundedness (transfinite
induction for detachable subsets):

\begin{code}

Well-founded₂ : U ⊔ V ̇
Well-founded₂ = (p : X → 𝟚) → ((x : X) → ((y : X) → y < x → p y ≡ ₁) → p x ≡ ₁)
                             → (x : X) → p x ≡ ₁

well-founded-Wellfounded₂ : well-founded → Well-founded₂
well-founded-Wellfounded₂ w p = transfinite-induction w (λ x → p x ≡ ₁)

ordinal₂ : U ⊔ V ̇
ordinal₂ = Well-founded₂ × extensional × transitive

ordinal-ordinal₂ : ordinal → ordinal₂
ordinal-ordinal₂ (w , e , t) = (well-founded-Wellfounded₂ w , e , t)

\end{code}
