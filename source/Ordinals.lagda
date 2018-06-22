Martin Escardo, April 2013, adapted to this development June 2018,
with further additions.

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

is-prop-valued-order : U ⊔ V ̇
is-prop-valued-order = ({x y : X} → is-prop(x < y))

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
                            (λ x σ f → σ)

prev-behaviour : (x : X) → ∀(a : is-accessible x) → next x (prev x a) ≡ a
prev-behaviour = accessible-induction _ (λ _ _ _ → refl)

transfinite-induction' :  ∀ {W} (P : X → W ̇)
                         → ((x : X) → (∀(y : X) → y < x → P y) → P x)
                         → (x : X) → is-accessible x → P x
transfinite-induction' P f = accessible-induction (λ x _ → P x)
                                                  (λ x _ → f x)

is-well-founded : U ⊔ V ̇
is-well-founded = (x : X) → is-accessible x

Well-founded : ∀ {W} → U ⊔ V ⊔ W ′ ̇
Well-founded {W} = (P : X → W ̇) → ((x : X) → ((y : X) → y < x → P y) → P x)
                                 → (x : X) → P x

transfinite-induction : is-well-founded → ∀ {W} → Well-founded {W}
transfinite-induction w P f x = transfinite-induction' P f x (w x)

transfinite-induction-converse : Well-founded {U ⊔ V} → is-well-founded
transfinite-induction-converse F = F is-accessible next

transfinite-recursion : is-well-founded → ∀ {W} {Y : W ̇}
                     → ((x : X) → ((y : X) → y < x → Y) → Y) → X → Y
transfinite-recursion w {W} {Y} = transfinite-induction w (λ x → Y)

is-transitive : U ⊔ V ̇
is-transitive = (x y z : X) → x < y → y < z → x < z

_≼_ : X → X → U ⊔ V ̇
x ≼ y = ∀ u → u < x → u < y

≼-prop-valued-order : (∀ U V → funext U V) → is-prop-valued-order → {x y : X} → is-prop(x ≼ y)
≼-prop-valued-order fe isp = is-prop-exponential-ideal (fe U V)
                               (λ u → is-prop-exponential-ideal (fe V V) (λ l → isp))

≼-refl : {x : X} → x ≼ x
≼-refl u l = l

≼-trans : {x y z : X} → x ≼ y → y ≼ z → x ≼ z
≼-trans f g u l = g u (f u l)

is-extensional : U ⊔ V ̇
is-extensional = (x y : X) → x ≼ y → y ≼ x → x ≡ y 

is-extensional' : U ⊔ V ̇
is-extensional' = (x y : X) → ((u : X) → (u < x) ⇔ (u < y)) → x ≡ y 

extensional-extensional' : is-extensional → is-extensional'
extensional-extensional' e x y f = e x y (λ u l → pr₁ (f u) l)
                                         (λ u l → pr₂ (f u) l)

extensional'-extensional : is-extensional' → is-extensional
extensional'-extensional e' x y g h = e' x y (λ u → (g u , h u))

is-ordinal : U ⊔ V ̇
is-ordinal = is-well-founded × is-extensional × is-transitive

is-accessible-is-prop : (∀ U V → funext U V)
                      → (x : X) → is-prop(is-accessible x)
is-accessible-is-prop fe = accessible-induction P φ
 where
  P : (x : X) → is-accessible x → U ⊔ V ̇
  P x a = (b : is-accessible x) → a ≡ b

  φ : (x : X) (σ : (y : X) → y < x → is-accessible y)
    → ((y : X) (l : y < x) (a : is-accessible y) → σ y l ≡ a)
    → (b : is-accessible x) → next x σ ≡ b
  φ x σ IH b = next x σ ≡⟨ ap (next x)
                               (dfunext (fe U (U ⊔ V)) (λ y → dfunext (fe V (U ⊔ V)) (h y))) ⟩
               next x τ ≡⟨ prev-behaviour x b ⟩
               b ∎
   where
    τ : (y : X) (l : y < x) → is-accessible y
    τ = prev x b
    h :  (y : X) (l : y < x) → σ y l ≡ τ y l
    h y l = IH y l (τ y l)

well-founded-is-prop : (∀ U V → funext U V) → is-prop is-well-founded
well-founded-is-prop fe = is-prop-exponential-ideal (fe U (U ⊔ V)) (is-accessible-is-prop fe)

extensional-gives-is-set : (∀ U V → funext U V) → is-prop-valued-order
                         → is-extensional → is-set X
extensional-gives-is-set fe isp e = identification-collapsible-is-set (f , κ)
 where
  f : {x y :  X} → x ≡ y → x ≡ y
  f {x} {y} p = e x y (transport (λ z → x ≼ z) p (≼-refl {x}))
                      (transport (λ z → z ≼ x) p (≼-refl {x}))
  ec : {x y : X} {l l' : x ≼ y} {m m' : y ≼ x} → e x y l m ≡ e x y l' m'
  ec {x} {y} {l} {l'} {m} {m'} = ap₂ (e x y) (≼-prop-valued-order fe isp l l')
                                             (≼-prop-valued-order fe isp m m')
  κ : {x y : X} → constant (f {x} {y})
  κ p q = ec

extensional-is-prop : (∀ U V → funext U V) → is-prop-valued-order → is-prop is-extensional
extensional-is-prop fe isp e e' =
 dfunext (fe U (U ⊔ V))
   (λ x → dfunext (fe U (U ⊔ V))
             (λ y → is-prop-exponential-ideal (fe (U ⊔ V) (U ⊔ V))
                      (λ l → is-prop-exponential-ideal (fe (U ⊔ V) U)
                               (λ m → extensional-gives-is-set fe isp e))
                      (e x y)
                      (e' x y)))

transitive-is-prop : (∀ U V → funext U V) → is-prop-valued-order → is-prop is-transitive
transitive-is-prop fe isp =
 is-prop-exponential-ideal (fe U (U ⊔ V))
   (λ x → is-prop-exponential-ideal (fe U (U ⊔ V))
            (λ y → is-prop-exponential-ideal (fe U V)
                     (λ z → is-prop-exponential-ideal (fe V V)
                              (λ l → is-prop-exponential-ideal (fe V V)
                                       (λ m → isp {x} {z})))))

ordinal-is-prop : (∀ U V → funext U V) → is-prop-valued-order → is-prop is-ordinal
ordinal-is-prop fe isp = props-closed-× (well-founded-is-prop fe)
                                        (props-closed-× (extensional-is-prop fe isp)
                                                        (transitive-is-prop fe isp))

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

<-gives-≼ : is-transitive → {x y : X} → x < y → x ≼ y
<-gives-≼ t l u m = t _ _ _ m l

≼-gives-≤ : (y : X) → is-accessible y → (x : X) → x ≼ y → x ≤ y
≼-gives-≤ y a x f l = ≤-refl y a (f y l)

\end{code}

When do we get x ≤ y → x ≼ y (say for ordinals)? When do we get cotransitivity?

Or consider the truncated version of the following:

\begin{code}

cotransitive : U ⊔ V ̇
cotransitive = (x y z : X) → x < y → x < z + z < y

no-minimal-is-empty : is-well-founded → ∀ {W} (P : X → W ̇)
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

is-well-founded₂ : U ⊔ V ̇
is-well-founded₂ = (p : X → 𝟚) → ((x : X) → ((y : X) → y < x → p y ≡ ₁) → p x ≡ ₁)
                             → (x : X) → p x ≡ ₁

well-founded-Wellfounded₂ : is-well-founded → is-well-founded₂
well-founded-Wellfounded₂ w p = transfinite-induction w (λ x → p x ≡ ₁)

open import UF-SetExamples

well-founded₂-is-prop : (∀ U V → funext U V) → is-prop is-well-founded₂
well-founded₂-is-prop fe = is-prop-exponential-ideal (fe U (U ⊔ V))
                            (λ p → is-prop-exponential-ideal (fe (U ⊔ V) U)
                                     (λ s → is-prop-exponential-ideal (fe U U₀) (λ x → 𝟚-is-set)))

is-ordinal₂ : U ⊔ V ̇
is-ordinal₂ = is-well-founded₂ × is-extensional × is-transitive

ordinal-ordinal₂ : is-ordinal → is-ordinal₂
ordinal-ordinal₂ (w , e , t) = (well-founded-Wellfounded₂ w) , e , t

ordinal₂-is-prop : (∀ U V → funext U V) → is-prop-valued-order → is-prop is-ordinal₂
ordinal₂-is-prop fe isp = props-closed-× (well-founded₂-is-prop fe)
                                         (props-closed-× (extensional-is-prop fe isp)
                                                         (transitive-is-prop fe isp))

\end{code}
