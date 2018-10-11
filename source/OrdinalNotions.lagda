Martin Escardo, April 2013, adapted to this development June 2018,
with further additions.

Ordinals like in the HoTT book and variations.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-Subsingletons-FunExt

module OrdinalNotions
        {U V : Universe}
        {X : U ̇}
        (_<_ : X → X → V ̇)
       where

is-prop-valued : U ⊔ V ̇
is-prop-valued = ((x y : X) → is-prop(x < y))

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

prev-behaviour : (x : X) (a : is-accessible x) → next x (prev x a) ≡ a
prev-behaviour = accessible-induction _ (λ _ _ _ → refl)

prev-behaviour' : (x : X) (σ : (y : X) → y < x → is-accessible y) → prev x (next x σ) ≡ σ
prev-behaviour' x σ = refl

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
transfinite-induction-converse φ = φ is-accessible next

transfinite-recursion : is-well-founded → ∀ {W} {Y : W ̇}
                      → ((x : X) → ((y : X) → y < x → Y) → Y) → X → Y
transfinite-recursion w {W} {Y} = transfinite-induction w (λ x → Y)

is-transitive : U ⊔ V ̇
is-transitive = (x y z : X) → x < y → y < z → x < z

_≼_ : X → X → U ⊔ V ̇
x ≼ y = ∀ u → u < x → u < y

≼-prop-valued-order : (∀ U V → funext U V) → is-prop-valued → (x y : X) → is-prop(x ≼ y)
≼-prop-valued-order fe isp x y = Π-is-prop (fe U V)
                                  (λ u → Π-is-prop (fe V V) (λ l → isp u y))

≼-refl : {x : X} → x ≼ x
≼-refl u l = l

≼-trans : {x y z : X} → x ≼ y → y ≼ z → x ≼ z
≼-trans f g u l = g u (f u l)

is-extensional : U ⊔ V ̇
is-extensional = (x y : X) → x ≼ y → y ≼ x → x ≡ y

is-extensional' : U ⊔ V ̇
is-extensional' = (x y : X) → ((u : X) → (u < x) ⇔ (u < y)) → x ≡ y

extensional-gives-extensional' : is-extensional → is-extensional'
extensional-gives-extensional' e x y f = e x y (λ u l → pr₁ (f u) l)
                                         (λ u l → pr₂ (f u) l)

extensional'-gives-extensional : is-extensional' → is-extensional
extensional'-gives-extensional e' x y g h = e' x y (λ u → (g u , h u))

is-well-order : U ⊔ V ̇
is-well-order = is-prop-valued × is-well-founded × is-extensional × is-transitive

prop-valuedness : is-well-order → is-prop-valued
prop-valuedness (p , w , e , t) = p

well-foundedness : is-well-order → is-well-founded
well-foundedness (p , w , e , t) = w

extensionality : is-well-order → is-extensional
extensionality (p , w , e , t) = e

transitivity : is-well-order → is-transitive
transitivity (p , w , e , t) = t

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
well-founded-is-prop fe = Π-is-prop (fe U (U ⊔ V)) (is-accessible-is-prop fe)

extensional-gives-is-set : (∀ U V → funext U V) → is-prop-valued
                         → is-extensional → is-set X
extensional-gives-is-set fe isp e = identification-collapsible-is-set (f , κ)
 where
  f : {x y :  X} → x ≡ y → x ≡ y
  f {x} {y} p = e x y (transport (λ - → x ≼ -) p (≼-refl {x}))
                      (transport (λ - → - ≼ x) p (≼-refl {x}))
  ec : {x y : X} {l l' : x ≼ y} {m m' : y ≼ x} → e x y l m ≡ e x y l' m'
  ec {x} {y} {l} {l'} {m} {m'} = ap₂ (e x y) (≼-prop-valued-order fe isp x y l l')
                                             (≼-prop-valued-order fe isp y x m m')
  κ : {x y : X} → constant (f {x} {y})
  κ p q = ec

ordinal-gives-is-set : (∀ U V → funext U V) → is-well-order → is-set X
ordinal-gives-is-set fe (p , w , e , t) = extensional-gives-is-set fe p e

extensional-is-prop : (∀ U V → funext U V) → is-prop-valued → is-prop is-extensional
extensional-is-prop fe isp e e' =
 dfunext (fe U (U ⊔ V))
   (λ x → dfunext (fe U (U ⊔ V))
             (λ y → Π-is-prop (fe (U ⊔ V) (U ⊔ V))
                      (λ l → Π-is-prop (fe (U ⊔ V) U)
                               (λ m → extensional-gives-is-set fe isp e))
                      (e x y)
                      (e' x y)))

transitive-is-prop : (∀ U V → funext U V) → is-prop-valued → is-prop is-transitive
transitive-is-prop fe isp =
 Π-is-prop (fe U (U ⊔ V))
   (λ x → Π-is-prop (fe U (U ⊔ V))
            (λ y → Π-is-prop (fe U V)
                     (λ z → Π-is-prop (fe V V)
                              (λ l → Π-is-prop (fe V V)
                                       (λ m → isp x z)))))

ordinal-is-prop : (∀ U V → funext U V) → is-prop is-well-order
ordinal-is-prop fe o = ×-is-prop (Π-is-prop (fe U (U ⊔ V))
                                        λ x → Π-is-prop (fe U V)
                                                (λ y → is-prop-is-prop (fe V V)))
                        (×-is-prop (well-founded-is-prop fe)
                          (×-is-prop (extensional-is-prop fe (pr₁ o))
                                          (transitive-is-prop fe (pr₁ o))))
                       o


_≤_ : X → X → V ̇
x ≤ y = ¬(y < x)

is-top : X → U ⊔ V ̇
is-top x = (y : X) → y ≤ x

has-top : U ⊔ V ̇
has-top = Σ \(x : X) → is-top x

<-coarser-than-≤  : (x : X) → is-accessible x → ∀ y → y < x → y ≤ x
<-coarser-than-≤ = transfinite-induction'
                     (λ x → (y : X) → y < x → y ≤ x)
                     (λ x f y l m → f y l x m l)

≤-refl : (x : X) → is-accessible x → x ≤ x
≤-refl x a l = <-coarser-than-≤ x a x l l

non-strict-trans : (z : X) → is-accessible z
                 → (x y : X) → x < y → y < z → x ≤ z
non-strict-trans = transfinite-induction'
                    (λ z → (x y : X) → x < y → y < z → x ≤ z)
                    (λ z f x y l m n → f y m z x n l m)

<-coarser-than-≼ : is-transitive → {x y : X} → x < y → x ≼ y
<-coarser-than-≼ t {x} {y} l u m = t u x y m l

≼-coarser-than-≤ : (y : X) → is-accessible y → (x : X) → x ≼ y → x ≤ y
≼-coarser-than-≤ y a x f l = ≤-refl y a (f y l)

trichotomous : U ⊔ V ̇
trichotomous = (x y : X) → (x < y) + (x ≡ y) + (y < x)

\end{code}

When do we get x ≤ y → x ≼ y (say for ordinals)? When do we get
cotransitivity? Jean S. Josef observed that cotransitivity gives x ≤ y
→ x ≼ y if _<_ is an order. But cotransitivity alone is enough.

Or consider the truncated version of the following, if _<_ is
proposition valued.

\begin{code}

cotransitive : U ⊔ V ̇
cotransitive = (x y z : X) → x < y → x < z + z < y

cotransitive-≤-coarser-than-≼ : cotransitive → (x y : X) → x ≤ y → x ≼ y
cotransitive-≤-coarser-than-≼ c x y n u l = γ (c u x y l)
 where
  γ : (u < y) + (y < x) → u < y
  γ (inl l) = l
  γ (inr l) = 𝟘-elim (n l)

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

Originally we needed the following weakening of well-foundedness
(transfinite induction for detachable subsets), but now it is not
needed any longer:

\begin{code}

is-well-founded₂ : U ⊔ V ̇
is-well-founded₂ = (p : X → 𝟚) → ((x : X) → ((y : X) → y < x → p y ≡ ₁) → p x ≡ ₁)
                              → (x : X) → p x ≡ ₁

well-founded-Wellfounded₂ : is-well-founded → is-well-founded₂
well-founded-Wellfounded₂ w p = transfinite-induction w (λ x → p x ≡ ₁)

open import UF-Miscelanea

well-founded₂-is-prop : (∀ U V → funext U V) → is-prop is-well-founded₂
well-founded₂-is-prop fe = Π-is-prop (fe U (U ⊔ V))
                            (λ p → Π-is-prop (fe (U ⊔ V) U)
                                     (λ s → Π-is-prop (fe U U₀) (λ x → 𝟚-is-set)))

is-well-order₂ : U ⊔ V ̇
is-well-order₂ = is-prop-valued × is-well-founded₂ × is-extensional × is-transitive

is-well-order-gives-is-well-order₂ : is-well-order → is-well-order₂
is-well-order-gives-is-well-order₂ (p , w , e , t) = p , (well-founded-Wellfounded₂ w) , e , t

ordinal₂-is-prop : (∀ U V → funext U V) → is-prop-valued → is-prop is-well-order₂
ordinal₂-is-prop fe isp = ×-is-prop (Π-is-prop (fe U (U ⊔ V))
                                           (λ x → Π-is-prop (fe U V)
                                                     (λ y → is-prop-is-prop (fe V V))))
                             (×-is-prop (well-founded₂-is-prop fe)
                               (×-is-prop (extensional-is-prop fe isp)
                                               (transitive-is-prop fe isp)))

\end{code}

Experimental ideas. We don't truncate the Σ, at least not for the
moment, so x <₂ y won't be a proposition in general. However, given
𝟚-order-separation, this is logically equivalent to a proposition (has
split support).

\begin{code}

open import Two

_≺₂_ : X → X → U ⊔ V ̇
x ≺₂ y = Σ \(p : X → 𝟚) → (p x <₂ p y)
                          × ((u v : X) → (u < v → p u ≤₂ p v)
                                       × (p u <₂ p v → u < v))

≺₂-courser-than-< : (x y : X) → x ≺₂ y → x < y
≺₂-courser-than-< x y (p , l , φ) = pr₂(φ x y) l

𝟚-order-separated : U ⊔ V ̇
𝟚-order-separated = (x y : X) → x < y → x ≺₂ y

open import DiscreteAndSeparated

𝟚-order-separated-gives-cotransitive : 𝟚-order-separated → cotransitive
𝟚-order-separated-gives-cotransitive s x y z l = g (s x y l)
 where
  g : (Σ \(p : X → 𝟚) → (p x <₂ p y)
                          × ((u v : X) → (u < v → p u ≤₂ p v)
                                       × (p u <₂ p v → u < v)))
    → (x < z) + (z < y)
  g (p , (r , s) , φ) = Cases (𝟚-discrete (p z) ₀)
                         (λ (t : p z ≡ ₀)
                            → inr (pr₂ (φ z y) (t , s)))
                         (λ (t : ¬(p z ≡ ₀))
                            → inl (pr₂ (φ x z) (r , (Lemma[b≢₀→b≡₁] t))))

\end{code}

It seems that this is not going to be useful, because although ℕ∞
satisfies this property, the property doesn't seem to be preserved by
the lexicographic order (think about this).
