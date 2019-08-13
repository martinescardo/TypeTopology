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
        {𝓤 𝓥 : Universe}
        {X : 𝓤 ̇ }
        (_<_ : X → X → 𝓥 ̇ )
       where

is-prop-valued : 𝓤 ⊔ 𝓥 ̇
is-prop-valued = (x y : X) → is-prop(x < y)

data is-accessible : X → 𝓤 ⊔ 𝓥 ̇  where
 next : (x : X) → ((y : X) → y < x → is-accessible y) → is-accessible x

accessible-induction : (P : (x : X) → is-accessible x → 𝓦 ̇ )
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

transfinite-induction' :  (P : X → 𝓦 ̇ )
                       → ((x : X) → (∀(y : X) → y < x → P y) → P x)
                       → (x : X) → is-accessible x → P x
transfinite-induction' P f = accessible-induction (λ x _ → P x)
                                                  (λ x _ → f x)

is-well-founded : 𝓤 ⊔ 𝓥 ̇
is-well-founded = (x : X) → is-accessible x

Well-founded : 𝓤 ⊔ 𝓥 ⊔ 𝓦  ⁺ ̇
Well-founded {𝓦} = (P : X → 𝓦 ̇ ) → ((x : X) → ((y : X) → y < x → P y) → P x)
                                → (x : X) → P x

transfinite-induction : is-well-founded → ∀ {𝓦} → Well-founded {𝓦}
transfinite-induction w P f x = transfinite-induction' P f x (w x)

transfinite-induction-converse : Well-founded {𝓤 ⊔ 𝓥} → is-well-founded
transfinite-induction-converse φ = φ is-accessible next

transfinite-recursion : is-well-founded
                      → ∀ {𝓦} {Y : 𝓦 ̇ }
                      → ((x : X) → ((y : X) → y < x → Y) → Y) → X → Y
transfinite-recursion w {𝓦} {Y} = transfinite-induction w (λ x → Y)

is-transitive : 𝓤 ⊔ 𝓥 ̇
is-transitive = (x y z : X) → x < y → y < z → x < z

_≼_ : X → X → 𝓤 ⊔ 𝓥 ̇
x ≼ y = ∀ u → u < x → u < y

≼-prop-valued-order : FunExt → is-prop-valued → (x y : X) → is-prop(x ≼ y)
≼-prop-valued-order fe isp x y = Π-is-prop (fe 𝓤 𝓥)
                                  (λ u → Π-is-prop (fe 𝓥 𝓥) (λ l → isp u y))

≼-refl : {x : X} → x ≼ x
≼-refl u l = l

≼-trans : {x y z : X} → x ≼ y → y ≼ z → x ≼ z
≼-trans f g u l = g u (f u l)

is-extensional : 𝓤 ⊔ 𝓥 ̇
is-extensional = (x y : X) → x ≼ y → y ≼ x → x ≡ y

is-extensional' : 𝓤 ⊔ 𝓥 ̇
is-extensional' = (x y : X) → ((u : X) → (u < x) ⇔ (u < y)) → x ≡ y

extensional-gives-extensional' : is-extensional → is-extensional'
extensional-gives-extensional' e x y f = e x y (λ u l → pr₁ (f u) l)
                                               (λ u l → pr₂ (f u) l)

extensional'-gives-extensional : is-extensional' → is-extensional
extensional'-gives-extensional e' x y g h = e' x y (λ u → (g u , h u))

\end{code}

The HoTT Book additionally requires that the underlying type is a set
in the following definition, but this actually follows from the
extensionality condition (see below):

\begin{code}

is-well-order : 𝓤 ⊔ 𝓥 ̇
is-well-order = is-prop-valued × is-well-founded × is-extensional × is-transitive

prop-valuedness : is-well-order → is-prop-valued
prop-valuedness (p , w , e , t) = p

well-foundedness : is-well-order → is-well-founded
well-foundedness (p , w , e , t) = w

extensionality : is-well-order → is-extensional
extensionality (p , w , e , t) = e

transitivity : is-well-order → is-transitive
transitivity (p , w , e , t) = t

accessibility-is-a-prop : FunExt
                        → (x : X) → is-prop(is-accessible x)
accessibility-is-a-prop fe = accessible-induction P φ
 where
  P : (x : X) → is-accessible x → 𝓤 ⊔ 𝓥 ̇
  P x a = (b : is-accessible x) → a ≡ b

  φ : (x : X) (σ : (y : X) → y < x → is-accessible y)
    → ((y : X) (l : y < x) (a : is-accessible y) → σ y l ≡ a)
    → (b : is-accessible x) → next x σ ≡ b
  φ x σ IH b = next x σ ≡⟨ ap (next x)
                              (dfunext (fe 𝓤 (𝓤 ⊔ 𝓥)) (λ y → dfunext (fe 𝓥 (𝓤 ⊔ 𝓥)) (h y))) ⟩
               next x τ ≡⟨ prev-behaviour x b ⟩
               b ∎
   where
    τ : (y : X) (l : y < x) → is-accessible y
    τ = prev x b
    h :  (y : X) (l : y < x) → σ y l ≡ τ y l
    h y l = IH y l (τ y l)

well-foundedness-is-a-prop : FunExt → is-prop is-well-founded
well-foundedness-is-a-prop fe = Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥)) (accessibility-is-a-prop fe)

extensionally-ordered-types-are-sets : FunExt → is-prop-valued
                                     → is-extensional → is-set X
extensionally-ordered-types-are-sets fe isp e = Id-collapsibles-are-sets (f , κ)
 where
  f : {x y :  X} → x ≡ y → x ≡ y
  f {x} {y} p = e x y (transport (λ - → x ≼ -) p (≼-refl {x}))
                      (transport (λ - → - ≼ x) p (≼-refl {x}))
  ec : {x y : X} {l l' : x ≼ y} {m m' : y ≼ x} → e x y l m ≡ e x y l' m'
  ec {x} {y} {l} {l'} {m} {m'} = ap₂ (e x y) (≼-prop-valued-order fe isp x y l l')
                                             (≼-prop-valued-order fe isp y x m m')
  κ : {x y : X} → constant (f {x} {y})
  κ p q = ec

well-ordered-types-are-sets : FunExt → is-well-order → is-set X
well-ordered-types-are-sets fe (p , w , e , t) = extensionally-ordered-types-are-sets fe p e

extensionality-is-a-prop : FunExt → is-prop-valued → is-prop is-extensional
extensionality-is-a-prop fe isp e e' =
 dfunext (fe 𝓤 (𝓤 ⊔ 𝓥))
   (λ x → dfunext (fe 𝓤 (𝓤 ⊔ 𝓥))
             (λ y → Π-is-prop (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥))
                      (λ l → Π-is-prop (fe (𝓤 ⊔ 𝓥) 𝓤)
                               (λ m → extensionally-ordered-types-are-sets fe isp e))
                      (e x y)
                      (e' x y)))

transitivity-is-a-prop : FunExt → is-prop-valued → is-prop is-transitive
transitivity-is-a-prop fe isp =
 Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥))
   (λ x → Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥))
            (λ y → Π-is-prop (fe 𝓤 𝓥)
                     (λ z → Π-is-prop (fe 𝓥 𝓥)
                              (λ l → Π-is-prop (fe 𝓥 𝓥)
                                       (λ m → isp x z)))))

being-well-order-is-a-prop : FunExt → is-prop is-well-order
being-well-order-is-a-prop fe o = ×-is-prop (Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥))
                                                            λ x → Π-is-prop (fe 𝓤 𝓥)
                                                                    (λ y → being-a-prop-is-a-prop (fe 𝓥 𝓥)))
                                            (×-is-prop (well-foundedness-is-a-prop fe)
                                              (×-is-prop (extensionality-is-a-prop fe (pr₁ o))
                                                              (transitivity-is-a-prop fe (pr₁ o))))
                                            o

_≤_ : X → X → 𝓥 ̇
x ≤ y = ¬(y < x)

is-top : X → 𝓤 ⊔ 𝓥 ̇
is-top x = (y : X) → y ≤ x

has-top : 𝓤 ⊔ 𝓥 ̇
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

trichotomous : 𝓤 ⊔ 𝓥 ̇
trichotomous = (x y : X) → (x < y) + (x ≡ y) + (y < x)

\end{code}

When do we get x ≤ y → x ≼ y (say for ordinals)? When do we get
cotransitivity? Jean S. Josef observed that cotransitivity gives x ≤ y
→ x ≼ y if _<_ is an order. But cotransitivity alone is enough.

Or consider the truncated version of the following, if _<_ is
proposition valued.

\begin{code}

cotransitive : 𝓤 ⊔ 𝓥 ̇
cotransitive = (x y z : X) → x < y → x < z + z < y

cotransitive-≤-coarser-than-≼ : cotransitive → (x y : X) → x ≤ y → x ≼ y
cotransitive-≤-coarser-than-≼ c x y n u l = γ (c u x y l)
 where
  γ : (u < y) + (y < x) → u < y
  γ (inl l) = l
  γ (inr l) = 𝟘-elim (n l)

no-minimal-is-empty : is-well-founded
                    → ∀ {𝓦} (P : X → 𝓦 ̇ )
                    → ((x : X) → P x → Σ \(y : X) → (y < x) × P y)
                    → is-empty(Σ P)
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

is-well-founded₂ : 𝓤 ⊔ 𝓥 ̇
is-well-founded₂ = (p : X → 𝟚) → ((x : X) → ((y : X) → y < x → p y ≡ ₁) → p x ≡ ₁)
                               → (x : X) → p x ≡ ₁

well-founded-Wellfounded₂ : is-well-founded → is-well-founded₂
well-founded-Wellfounded₂ w p = transfinite-induction w (λ x → p x ≡ ₁)

open import UF-Miscelanea

being-well-founded₂-is-a-prop : FunExt → is-prop is-well-founded₂
being-well-founded₂-is-a-prop fe = Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥))
                                    (λ p → Π-is-prop (fe (𝓤 ⊔ 𝓥) 𝓤)
                                             (λ s → Π-is-prop (fe 𝓤 𝓤₀) (λ x → 𝟚-is-set)))

is-well-order₂ : 𝓤 ⊔ 𝓥 ̇
is-well-order₂ = is-prop-valued × is-well-founded₂ × is-extensional × is-transitive

is-well-order-gives-is-well-order₂ : is-well-order → is-well-order₂
is-well-order-gives-is-well-order₂ (p , w , e , t) = p , (well-founded-Wellfounded₂ w) , e , t

being-well-order₂-is-a-prop : FunExt → is-prop-valued → is-prop is-well-order₂
being-well-order₂-is-a-prop fe isp = ×-is-prop (Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥))
                                                             (λ x → Π-is-prop (fe 𝓤 𝓥)
                                                                       (λ y → being-a-prop-is-a-prop (fe 𝓥 𝓥))))
                                               (×-is-prop (being-well-founded₂-is-a-prop fe)
                                                 (×-is-prop (extensionality-is-a-prop fe isp)
                                                                 (transitivity-is-a-prop fe isp)))

\end{code}

Experimental ideas. We don't truncate the Σ, at least not for the
moment, so x <₂ y won't be a proposition (i.e. subsingleton) in
general. However, given 𝟚-order-separation, this is logically
equivalent to a proposition (has split support).

\begin{code}

open import Two-Properties

_≺₂_ : X → X → 𝓤 ⊔ 𝓥 ̇
x ≺₂ y = Σ \(p : X → 𝟚) → (p x <₂ p y)
                        × ((u v : X) → (u < v → p u ≤₂ p v)
                                     × (p u <₂ p v → u < v))

≺₂-courser-than-< : (x y : X) → x ≺₂ y → x < y
≺₂-courser-than-< x y (p , l , φ) = pr₂(φ x y) l

𝟚-order-separated : 𝓤 ⊔ 𝓥 ̇
𝟚-order-separated = (x y : X) → x < y → x ≺₂ y

open import DiscreteAndSeparated

𝟚-order-separated-gives-cotransitive : 𝟚-order-separated → cotransitive
𝟚-order-separated-gives-cotransitive s x y z l = g (s x y l)
 where
  g : (Σ \(p : X → 𝟚) → (p x <₂ p y)
                          × ((u v : X) → (u < v → p u ≤₂ p v)
                                       × (p u <₂ p v → u < v)))
    → (x < z) + (z < y)
  g (p , (r , s) , φ) = Cases (𝟚-is-discrete (p z) ₀)
                         (λ (t : p z ≡ ₀)
                            → inr (pr₂ (φ z y) (t , s)))
                         (λ (t : ¬(p z ≡ ₀))
                            → inl (pr₂ (φ x z) (r , (different-from-₀-equal-₁ t))))

\end{code}

It seems that this is not going to be useful, because although ℕ∞
satisfies this property, the property doesn't seem to be preserved by
the lexicographic order (think about this).
