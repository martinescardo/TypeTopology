Martin Escardo, April 2013.

Adapted to this development June 2018, with further additions.

Ordinals like in the HoTT book and variations.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import DiscreteAndSeparated

open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-Subsingletons-FunExt
open import UF-ExcludedMiddle

module OrdinalNotions
        {𝓤 𝓥 : Universe}
        {X : 𝓤 ̇ }
        (_<_ : X → X → 𝓥 ̇ )
       where

is-prop-valued : 𝓤 ⊔ 𝓥 ̇
is-prop-valued = (x y : X) → is-prop (x < y)

data is-accessible : X → 𝓤 ⊔ 𝓥 ̇ where
 next : (x : X) → ((y : X) → y < x → is-accessible y) → is-accessible x

accessible-induction : (P : (x : X) → is-accessible x → 𝓦 ̇ )
                     → ((x : X) (σ : (y : X) → y < x → is-accessible y)
                         → ((y : X) (l : y < x) → P y (σ y l))
                         → P x (next x σ))
                     → (x : X) (a : is-accessible x) → P x a
accessible-induction P f = h
  where
   h : (x : X) (a : is-accessible x) → P x a
   h x (next x σ) = f x σ (λ y l → h y (σ y l))

prev : (x : X)
     → is-accessible x
     → (y : X) → y < x → is-accessible y
prev = accessible-induction
        (λ x _ → (y : X) → y < x → is-accessible y)
        (λ x σ f → σ)

prev-behaviour : (x : X) (a : is-accessible x)
               → next x (prev x a) ≡ a
prev-behaviour = accessible-induction _ (λ _ _ _ → refl)

prev-behaviour' : (x : X) (σ : (y : X) → y < x → is-accessible y)
                → prev x (next x σ) ≡ σ
prev-behaviour' x σ = refl

transfinite-induction' :  (P : X → 𝓦 ̇ )
                       → ((x : X) → (∀(y : X) → y < x → P y) → P x)
                       → (x : X) → is-accessible x → P x
transfinite-induction' P f = accessible-induction
                              (λ x _ → P x)
                              (λ x _ → f x)

is-well-founded : 𝓤 ⊔ 𝓥 ̇
is-well-founded = (x : X) → is-accessible x

Well-founded : 𝓤 ⊔ 𝓥 ⊔ 𝓦  ⁺ ̇
Well-founded {𝓦} = (P : X → 𝓦 ̇ )
                 → ((x : X) → ((y : X) → y < x → P y) → P x)
                 → (x : X) → P x

transfinite-induction : is-well-founded → ∀ {𝓦} → Well-founded {𝓦}
transfinite-induction w P f x = transfinite-induction' P f x (w x)

transfinite-induction-converse : Well-founded {𝓤 ⊔ 𝓥} → is-well-founded
transfinite-induction-converse φ = φ is-accessible next

transfinite-recursion : is-well-founded
                      → ∀ {𝓦} {Y : 𝓦 ̇ }
                      → ((x : X) → ((y : X) → y < x → Y) → Y)
                      → X → Y
transfinite-recursion w {𝓦} {Y} = transfinite-induction w (λ x → Y)

is-transitive : 𝓤 ⊔ 𝓥 ̇
is-transitive = (x y z : X) → x < y → y < z → x < z

_≼_ : X → X → 𝓤 ⊔ 𝓥 ̇
x ≼ y = ∀ u → u < x → u < y

≼-is-prop-valued : FunExt
                 → is-prop-valued
                 → (x y : X) → is-prop (x ≼ y)
≼-is-prop-valued fe isp x y = Π₂-is-prop (λ {𝓤} {𝓥} → fe 𝓤 𝓥)
                                   (λ u l → isp u y)

≼-refl : {x : X} → x ≼ x
≼-refl u l = l

≼-trans : {x y z : X} → x ≼ y → y ≼ z → x ≼ z
≼-trans f g u l = g u (f u l)

is-extensional : 𝓤 ⊔ 𝓥 ̇
is-extensional = (x y : X) → x ≼ y → y ≼ x → x ≡ y

is-extensional' : 𝓤 ⊔ 𝓥 ̇
is-extensional' = (x y : X) → ((u : X) → (u < x) ⇔ (u < y)) → x ≡ y

extensional-gives-extensional' : is-extensional → is-extensional'
extensional-gives-extensional' e x y f = e x y
                                          (λ u l → pr₁ (f u) l)
                                          (λ u l → pr₂ (f u) l)

extensional'-gives-extensional : is-extensional' → is-extensional
extensional'-gives-extensional e' x y g h = e' x y (λ u → (g u , h u))

\end{code}

The HoTT Book additionally requires that the underlying type is a set
in the following definition, but this actually follows from the
extensionality condition (see below):

\begin{code}

is-well-order : 𝓤 ⊔ 𝓥 ̇
is-well-order = is-prop-valued
              × is-well-founded
              × is-extensional
              × is-transitive

prop-valuedness : is-well-order → is-prop-valued
prop-valuedness (p , w , e , t) = p

well-foundedness : is-well-order → is-well-founded
well-foundedness (p , w , e , t) = w

extensionality : is-well-order → is-extensional
extensionality (p , w , e , t) = e

transitivity : is-well-order → is-transitive
transitivity (p , w , e , t) = t

accessibility-is-prop : FunExt
                      → (x : X) → is-prop (is-accessible x)
accessibility-is-prop fe = accessible-induction P φ
 where
  P : (x : X) → is-accessible x → 𝓤 ⊔ 𝓥 ̇
  P x a = (b : is-accessible x) → a ≡ b

  φ : (x : X) (σ : (y : X) → y < x → is-accessible y)
    → ((y : X) (l : y < x) (a : is-accessible y) → σ y l ≡ a)
    → (b : is-accessible x) → next x σ ≡ b
  φ x σ IH b = next x σ ≡⟨ i ⟩
               next x τ ≡⟨ prev-behaviour x b ⟩
               b        ∎
   where
    τ : (y : X) → y < x → is-accessible y
    τ = prev x b

    h :  (y : X) (l : y < x) → σ y l ≡ τ y l
    h y l = IH y l (τ y l)

    i = ap (next x)
           (dfunext (fe 𝓤 (𝓤 ⊔ 𝓥)) (λ y → dfunext (fe 𝓥 (𝓤 ⊔ 𝓥)) (h y)))

well-foundedness-is-prop : FunExt → is-prop is-well-founded
well-foundedness-is-prop fe = Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥))
                               (accessibility-is-prop fe)

extensionally-ordered-types-are-sets : FunExt
                                     → is-prop-valued
                                     → is-extensional
                                     → is-set X
extensionally-ordered-types-are-sets fe isp e = γ
 where
  f : {x y :  X} → x ≡ y → x ≡ y
  f {x} {y} p = e x y (transport (x ≼_) p (≼-refl {x}))
                      (transport (_≼ x) p (≼-refl {x}))

  ec : {x y : X} {l l' : x ≼ y} {m m' : y ≼ x} → e x y l m ≡ e x y l' m'
  ec {x} {y} {l} {l'} {m} {m'} = ap₂ (e x y)
                                     (≼-is-prop-valued fe isp x y l l')
                                     (≼-is-prop-valued fe isp y x m m')

  κ : {x y : X} → wconstant (f {x} {y})
  κ p q = ec

  γ : is-set X
  γ = Id-collapsibles-are-sets (f , κ)

well-ordered-types-are-sets : FunExt → is-well-order → is-set X
well-ordered-types-are-sets fe (p , w , e , t) =
 extensionally-ordered-types-are-sets fe p e

extensionality-is-prop : FunExt → is-prop-valued → is-prop is-extensional
extensionality-is-prop fe isp e e' =
 dfunext (fe 𝓤 (𝓤 ⊔ 𝓥))
   (λ x → dfunext (fe 𝓤 (𝓤 ⊔ 𝓥))
           (λ y → Π₂-is-prop (λ {𝓤} {𝓥} → fe 𝓤 𝓥)
                    (λ l m → extensionally-ordered-types-are-sets fe isp e)
                    (e x y)
                    (e' x y)))

transitivity-is-prop : FunExt → is-prop-valued → is-prop is-transitive
transitivity-is-prop fe isp = Π₅-is-prop (λ {𝓤} {𝓥} → fe 𝓤 𝓥)
                               (λ x y z l m → isp x z)

being-well-order-is-prop : FunExt → is-prop is-well-order
being-well-order-is-prop fe = prop-criterion γ
 where
  γ : is-well-order → is-prop is-well-order
  γ o = ×₄-is-prop (Π₂-is-prop ((λ {𝓤} {𝓥} → fe 𝓤 𝓥))
                      (λ x y → being-prop-is-prop (fe 𝓥 𝓥)))
                   (well-foundedness-is-prop fe)
                   (extensionality-is-prop fe (prop-valuedness o))
                   (transitivity-is-prop fe (prop-valuedness o))

no-minimal-is-empty : is-well-founded
                    → ∀ {𝓦} (P : X → 𝓦 ̇ )
                    → ((x : X) → P x → Σ y ꞉ X , (y < x) × P y)
                    → is-empty (Σ P)
no-minimal-is-empty w P s (x , p) = γ
 where
  f : ((x : X) → P x → Σ y ꞉ X , (y < x) × P y) → (x : X) → ¬ (P x)
  f s x p = g x (w x) p
   where
    g : (x : X) → is-accessible x → ¬ (P x)
    g x (next x σ) p = IH (pr₁ (s x p)) (pr₁ (pr₂ (s x p))) (pr₂ (pr₂ (s x p)))
     where
      IH : (y : X) → y < x → ¬ (P y)
      IH y l = g y (σ y l)

  NB : Σ P → ¬ ((x : X) → P x → Σ y ꞉ X , (y < x) × P y)
  NB (x , p) s = f s x p

  γ : 𝟘
  γ = f s x p

_≾_ : X → X → 𝓥 ̇
x ≾ y = ¬ (y < x)

≾-is-prop-valued : funext 𝓥 𝓤₀ → is-prop-valued → (x y : X) → is-prop (x ≾ y)
≾-is-prop-valued fe p x y = ¬-is-prop fe

is-top : X → 𝓤 ⊔ 𝓥 ̇
is-top x = (y : X) → y ≾ x

has-top : 𝓤 ⊔ 𝓥 ̇
has-top = Σ x ꞉ X , is-top x

is-bottom : X → 𝓤 ⊔ 𝓥 ̇
is-bottom x = (y : X) → x ≾ y

<-coarser-than-≾  : (x : X)
                  → is-accessible x
                  → (y : X) → y < x → y ≾ x
<-coarser-than-≾ = transfinite-induction'
                     (λ x → (y : X) → y < x → y ≾ x)
                     (λ x f y l m → f y l x m l)

≾-refl : (x : X) → is-accessible x → x ≾ x
≾-refl x a l = <-coarser-than-≾ x a x l l

irreflexive : (x : X) → is-accessible x → ¬ (x < x)
irreflexive = ≾-refl

<-gives-≢ : is-well-founded
          → (x y : X) → x < y → x ≢ y
<-gives-≢ w x y l p = irreflexive y (w y) (transport (_< y) p l)

<-coarser-than-≼ : is-transitive → {x y : X} → x < y → x ≼ y
<-coarser-than-≼ t {x} {y} l u m = t u x y m l

≼-coarser-than-≾ : (y : X) → is-accessible y → (x : X) → x ≼ y → x ≾ y
≼-coarser-than-≾ y a x f l = ≾-refl y a (f y l)

\end{code}

The remainder of this file is not needed anywhere else (at least at
the time of writing, namely 11th January 2021).

\begin{code}

is-trichotomous : 𝓤 ⊔ 𝓥 ̇
is-trichotomous = (x y : X) → (x < y) + (x ≡ y) + (y < x)

\end{code}

Not all ordinals are trichotomous, in the absence of excluded middle
or even just LPO, because ℕ∞ is not discrete unless LPO holds, but its
natural order is well-founded, and types well-founded trichotomous
relations are discrete (have decidable equality):

\begin{code}

trichomous-gives-discrete : is-well-founded
                          → is-trichotomous
                          → is-discrete X
trichomous-gives-discrete w t x y = f (t x y)
 where
  f : (x < y) + (x ≡ y) + (y < x) → (x ≡ y) + (x ≢ y)
  f (inl l)       = inr (<-gives-≢ w x y l)
  f (inr (inl p)) = inl p
  f (inr (inr l)) = inr (≢-sym (<-gives-≢ w y x l))

\end{code}

The following proof that excluded middle gives trichotomy, added 11th
Jan 2021, is the same as that in the HoTT book, except that we
use negation instead of the assumption of existence of propositional
truncations to get a proposition to which we can apply excluded
middle.  But notice that, under excluded middle and function
extensionality, double negation is the same thing as propositional
truncation. Notice also that we need excluded middle for two
universes, and that we additionally need function extensionality as an
assumption (to know that the negation of a type is a proposition).

\begin{code}

trichotomy : EM 𝓥
           → EM (𝓤 ⊔ 𝓥)
           → funext (𝓤 ⊔ 𝓥) 𝓤₀
           → is-well-order
           → is-trichotomous
trichotomy em em' fe (p , w , e , t) = transfinite-induction w (λ x → ∀ y → P x y) ϕ
 where
  P : X → X → 𝓤 ⊔ 𝓥 ̇
  P x y = (x < y) + (x ≡ y) + (y < x)

  ϕ : (x : X)
    → ((x' : X) → x' < x → (y : X) → P x' y)
    → (y : X) → P x y
  ϕ x f = transfinite-induction w (λ y → P x y) ψ
   where
    ψ : (y : X)
      → ((y' : X) → y' < y → P x y')
      → P x y
    ψ y g = γ
     where
      A = Σ x' ꞉ X , (x' < x) × ((y < x') + (x' ≡ y))

      ¬¬A-gives-P : ¬¬ A → P x y
      ¬¬A-gives-P = b
       where
        a : A → y < x
        a (x' , l , inl m) = t y x' x m l
        a (x' , l , inr p) = transport (_< x) p l

        b : ¬¬ A → (x < y) + (x ≡ y) + (y < x)
        b = inr ∘ inr ∘ EM-gives-DNE em (y < x) (p y x) ∘ ¬¬-functor a

      ¬A-gives-≼ : ¬ A → x ≼ y
      ¬A-gives-≼ ν x' l = c
       where
        a : ¬ ((y < x') + (x' ≡ y))
        a k = ν (x' , l , k)

        IH : P x' y
        IH = f x' l y

        b : ¬ ((y < x') + (x' ≡ y)) → P x' y → x' < y
        b h (inl i)         = i
        b h (inr (inl ii))  = 𝟘-elim (h (inr ii))
        b h (inr (inr iii)) = 𝟘-elim (h (inl iii))

        c : x' < y
        c = b a IH

      B = Σ y' ꞉ X , (y' < y) × ((x < y') + (x ≡ y'))

      ¬¬B-gives-P : ¬¬ B → P x y
      ¬¬B-gives-P = b
       where
        a : B → x < y
        a (y' , l , inl m) = t x y' y m l
        a (y' , l , inr p) = transport (_< y) (p ⁻¹) l

        b : ¬¬ B → (x < y) + (x ≡ y) + (y < x)
        b = inl ∘ EM-gives-DNE em (x < y) (p x y) ∘ ¬¬-functor a

      ¬B-gives-≼ : ¬ B → y ≼ x
      ¬B-gives-≼ ν y' l = c
       where
        a : ¬ ((x < y') + (x ≡ y'))
        a k = ν (y' , l , k)

        IH : P x y'
        IH = g y' l

        b : ¬ ((x < y') + (x ≡ y')) → P x y' → y' < x
        b h (inl i)         = 𝟘-elim (h (inl i))
        b h (inr (inl ii))  = 𝟘-elim (h (inr ii))
        b h (inr (inr iii)) = iii

        c : y' < x
        c = b a IH

      ¬A-and-¬B-give-P : ¬ A → ¬ B → P x y
      ¬A-and-¬B-give-P ν ν' = b
       where
        a : ¬ A → ¬ B → x ≡ y
        a ν ν' = e x y (¬A-gives-≼ ν) (¬B-gives-≼ ν')

        b : (x < y) + (x ≡ y) + (y < x)
        b = inr (inl (a ν ν'))

      γ : P x y
      γ = Cases (em' (¬ A) (¬-is-prop fe))
           (λ (ν : ¬ A)
                 → Cases (em' (¬ B) (¬-is-prop fe))
                    (¬A-and-¬B-give-P ν)
                    ¬¬B-gives-P)
           ¬¬A-gives-P

\end{code}

When do we get x ≾ y → x ≼ y (say for ordinals)? When do we get
cotransitivity? Jean S. Josef observed that cotransitivity gives x ≾ y
→ x ≼ y if _<_ is an order. But cotransitivity alone is enough.

Or consider the truncated version of the following, if _<_ is
proposition valued.

\begin{code}

cotransitive : 𝓤 ⊔ 𝓥 ̇
cotransitive = (x y z : X) → x < y → (x < z) + (z < y)

cotransitive-≾-coarser-than-≼ : cotransitive → (x y : X) → x ≾ y → x ≼ y
cotransitive-≾-coarser-than-≼ c x y n u l = γ (c u x y l)
 where
  γ : (u < y) + (y < x) → u < y
  γ (inl l) = l
  γ (inr l) = 𝟘-elim (n l)

\end{code}

Originally, in 2011 (see my JSL publication), we needed to work with
the following weakening of well-foundedness (transfinite induction for
detachable subsets), but as of Summer 2018, it is not needed any
longer as we are able to show that our compact ordinals are
well-founded in the standard, stronger, sense.

\begin{code}

is-well-founded₂ : 𝓤 ⊔ 𝓥 ̇
is-well-founded₂ = (p : X → 𝟚) → ((x : X) → ((y : X) → y < x → p y ≡ ₁) → p x ≡ ₁)
                               → (x : X) → p x ≡ ₁

well-founded-Wellfounded₂ : is-well-founded → is-well-founded₂
well-founded-Wellfounded₂ w p = transfinite-induction w (λ x → p x ≡ ₁)

open import UF-Miscelanea

being-well-founded₂-is-prop : FunExt → is-prop is-well-founded₂
being-well-founded₂-is-prop fe = Π₃-is-prop (λ {𝓤} {𝓥} → fe 𝓤 𝓥)
                                   (λ p s x → 𝟚-is-set)

is-well-order₂ : 𝓤 ⊔ 𝓥 ̇
is-well-order₂ = is-prop-valued × is-well-founded₂ × is-extensional × is-transitive

is-well-order-gives-is-well-order₂ : is-well-order → is-well-order₂
is-well-order-gives-is-well-order₂ (p , w , e , t) = p , (well-founded-Wellfounded₂ w) , e , t

being-well-order₂-is-prop : FunExt → is-prop-valued → is-prop is-well-order₂
being-well-order₂-is-prop fe isp = ×₄-is-prop
                                     (Π₂-is-prop (λ {𝓤} {𝓥} → fe 𝓤 𝓥)
                                        (λ x y → being-prop-is-prop (fe 𝓥 𝓥)))
                                     (being-well-founded₂-is-prop fe)
                                     (extensionality-is-prop fe isp)
                                     (transitivity-is-prop fe isp)
\end{code}

Experimental ideas. We don't truncate the Σ, at least not for the
moment, so x <₂ y won't be a proposition (i.e. subsingleton) in
general. However, given 𝟚-order-separation, this is logically
equivalent to a proposition (has split support).

\begin{code}

open import Two-Properties

_≺₂_ : X → X → 𝓤 ⊔ 𝓥 ̇
x ≺₂ y = Σ p ꞉ (X → 𝟚) , (p x <₂ p y)
                       × ((u v : X) → (u < v → p u ≤₂ p v)
                                    × (p u <₂ p v → u < v))

≺₂-courser-than-< : (x y : X) → x ≺₂ y → x < y
≺₂-courser-than-< x y (p , l , φ) = pr₂ (φ x y) l

𝟚-order-separated : 𝓤 ⊔ 𝓥 ̇
𝟚-order-separated = (x y : X) → x < y → x ≺₂ y

𝟚-order-separated-gives-cotransitive : 𝟚-order-separated → cotransitive
𝟚-order-separated-gives-cotransitive s x y z l = g (s x y l)
 where
  g : (Σ p ꞉ (X → 𝟚) , (p x <₂ p y)
                     × ((u v : X) → (u < v → p u ≤₂ p v)
                                  × (p u <₂ p v → u < v)))
    → (x < z) + (z < y)
  g (p , (r , s) , φ) = Cases (𝟚-is-discrete (p z) ₀)
                         (λ (t : p z ≡ ₀)
                            → inr (pr₂ (φ z y) (t , s)))
                         (λ (t : ¬ (p z ≡ ₀))
                            → inl (pr₂ (φ x z) (r , (different-from-₀-equal-₁ t))))

\end{code}

It seems that this is not going to be useful, because although ℕ∞
satisfies this property, the property doesn't seem to be preserved by
the lexicographic order (think about this).
