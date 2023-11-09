Martin Escardo, April 2013.

Adapted to this development June 2018, with further additions.

Ordinals like in the HoTT book and variations.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Plus-Properties using (+-commutative)
open import MLTT.Spartan
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.Hedberg
open import UF.PropTrunc
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Ordinals.Notions
        {𝓤 𝓥 : Universe}
        {X : 𝓤 ̇ }
        (_<_ : X → X → 𝓥 ̇ )
       where

is-prop-valued : 𝓤 ⊔ 𝓥 ̇
is-prop-valued = (x y : X) → is-prop (x < y)

data is-accessible : X → 𝓤 ⊔ 𝓥 ̇ where
 acc : {x : X} → ((y : X) → y < x → is-accessible y) → is-accessible x

accessible-induction : (P : (x : X) → is-accessible x → 𝓦 ̇ )
                     → ((x : X) (σ : (y : X) → y < x → is-accessible y)
                         → ((y : X) (l : y < x) → P y (σ y l))
                         → P x (acc σ))
                     → (x : X) (a : is-accessible x) → P x a
accessible-induction P f = h
  where
   h : (x : X) (a : is-accessible x) → P x a
   h x (acc σ) = f x σ (λ y l → h y (σ y l))

prev : {x : X}
     → is-accessible x
     → (y : X) → y < x → is-accessible y
prev (acc a) = a

prev-behaviour : (x : X) (a : is-accessible x)
               → acc (prev a) ＝ a
prev-behaviour = accessible-induction _ (λ _ _ _ → refl)

transfinite-induction' :  (P : X → 𝓦 ̇ )
                       → ((x : X) → ((y : X) → y < x → P y) → P x)
                       → (x : X) → is-accessible x → P x
transfinite-induction' P f = accessible-induction
                              (λ x _ → P x)
                              (λ x _ → f x)

\end{code}

Added 31 October 2022 by Tom de Jong.
We record the (computational) behaviour of transfinite induction for use in
other constructions.

\begin{code}

transfinite-induction'-behaviour :
   (P : X → 𝓦 ̇ ) (f : (x : X) → ((y : X) → y < x → P y) → P x)
   (x : X) (a : is-accessible x)
 → transfinite-induction' P f x a
   ＝ f x (λ y l → transfinite-induction' P f y (prev a y l))
transfinite-induction'-behaviour P f x (acc σ) = refl

\end{code}

End of addition.

\begin{code}

is-well-founded : 𝓤 ⊔ 𝓥 ̇
is-well-founded = (x : X) → is-accessible x

is-Well-founded : 𝓤 ⊔ 𝓥 ⊔ 𝓦  ⁺ ̇
is-Well-founded {𝓦} = (P : X → 𝓦 ̇ )
                    → ((x : X) → ((x' : X) → x' < x → P x') → P x)
                    → (x : X) → P x

transfinite-induction : is-well-founded → ∀ {𝓦} → is-Well-founded {𝓦}
transfinite-induction w P f x = transfinite-induction' P f x (w x)

transfinite-induction-converse : is-Well-founded {𝓤 ⊔ 𝓥} → is-well-founded
transfinite-induction-converse φ = φ is-accessible (λ _ → acc)

transfinite-recursion : is-well-founded
                      → ∀ {𝓦} {Y : 𝓦 ̇ }
                      → ((x : X) → ((x' : X) → x' < x → Y) → Y)
                      → X → Y
transfinite-recursion w {𝓦} {Y} = transfinite-induction w (λ x → Y)

accessibility-is-prop : FunExt
                      → (x : X) → is-prop (is-accessible x)
accessibility-is-prop fe = accessible-induction P φ
 where
  P : (x : X) → is-accessible x → 𝓤 ⊔ 𝓥 ̇
  P x a = (b : is-accessible x) → a ＝ b

  φ : (x : X) (σ : (y : X) → y < x → is-accessible y)
    → ((y : X) (l : y < x) (a : is-accessible y) → σ y l ＝ a)
    → (b : is-accessible x) → acc σ ＝ b
  φ x σ IH b = acc σ ＝⟨ i ⟩
               acc τ ＝⟨ prev-behaviour x b ⟩
               b     ∎
   where
    τ : (y : X) → y < x → is-accessible y
    τ = prev b

    h :  (y : X) (l : y < x) → σ y l ＝ τ y l
    h y l = IH y l (τ y l)

    i = ap acc
           (dfunext (fe 𝓤 (𝓤 ⊔ 𝓥)) (λ y → dfunext (fe 𝓥 (𝓤 ⊔ 𝓥)) (h y)))

\end{code}

Added 31 October 2022 by Tom de Jong.
We record the (computational) behaviour of transfinite induction/recursion for
use in other constructions.

\begin{code}

transfinite-induction-behaviour : FunExt → (w : is-well-founded)
                                  {𝓦 : Universe} (P : X → 𝓦 ̇ )
                                  (f : (x : X) → ((y : X) → y < x → P y) → P x)
                                  (x : X)
                                → transfinite-induction w P f x
                                  ＝ f x (λ y l → transfinite-induction w P f y)
transfinite-induction-behaviour fe w {𝓦} P f x =
 transfinite-induction w P f x                               ＝⟨ I    ⟩
 f x (λ y l → transfinite-induction' P f y (prev (w x) y l)) ＝⟨ II   ⟩
 f x (λ y l → transfinite-induction' P f y (w y))            ＝⟨ refl ⟩
 f x (λ y l → transfinite-induction w P f y)                 ∎
  where
   I = transfinite-induction'-behaviour P f x (w x)
   II = ap (f x) (dfunext (fe 𝓤 (𝓥 ⊔ 𝓦))
                          (λ y → dfunext (fe 𝓥 𝓦)
                                         (λ l → ap (transfinite-induction' P f y) (e y l))))
    where
     e : (y : X) (l : y < x) → prev (w x) y l ＝ w y
     e y l = accessibility-is-prop fe y (prev (w x) y l) (w y)

transfinite-recursion-behaviour : FunExt
                                → (w : is-well-founded)
                                  {𝓦 : Universe} {Y : 𝓦 ̇ }
                                  (f : (x : X) → ((y : X) → y < x → Y) → Y)
                                  (x : X)
                                → transfinite-recursion w f x
                                  ＝ f x (λ y _ → transfinite-recursion w f y)
transfinite-recursion-behaviour fe w {𝓦} {Y} =
 transfinite-induction-behaviour fe w (λ _ → Y)

\end{code}

End of addition.

\begin{code}

is-transitive : 𝓤 ⊔ 𝓥 ̇
is-transitive = (x y z : X) → x < y → y < z → x < z

private
  _≼_ : X → X → 𝓤 ⊔ 𝓥 ̇
  x ≼ y = ∀ u → u < x → u < y

extensional-po = _≼_

extensional-po-is-prop-valued : FunExt
                              → is-prop-valued
                              → (x y : X) → is-prop (x ≼ y)
extensional-po-is-prop-valued fe isp x y =
  Π₂-is-prop (λ {𝓤} {𝓥} → fe 𝓤 𝓥) (λ u l → isp u y)

≼-refl : {x : X} → x ≼ x
≼-refl u l = l

≼-trans : {x y z : X} → x ≼ y → y ≼ z → x ≼ z
≼-trans f g u l = g u (f u l)

is-extensional : 𝓤 ⊔ 𝓥 ̇
is-extensional = (x y : X) → x ≼ y → y ≼ x → x ＝ y

is-extensional' : 𝓤 ⊔ 𝓥 ̇
is-extensional' = (x y : X) → ((u : X) → (u < x) ↔ (u < y)) → x ＝ y

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

well-foundedness-is-prop : FunExt → is-prop is-well-founded
well-foundedness-is-prop fe = Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥))
                               (accessibility-is-prop fe)

extensionally-ordered-types-are-sets : FunExt
                                     → is-prop-valued
                                     → is-extensional
                                     → is-set X
extensionally-ordered-types-are-sets fe isp e = γ
 where
  f : {x y :  X} → x ＝ y → x ＝ y
  f {x} {y} p = e x y (transport (x ≼_) p (≼-refl {x}))
                      (transport (_≼ x) p (≼-refl {x}))

  ec : {x y : X} {l l' : x ≼ y} {m m' : y ≼ x} → e x y l m ＝ e x y l' m'
  ec {x} {y} {l} {l'} {m} {m'} = ap₂ (e x y)
                                     (extensional-po-is-prop-valued fe isp x y l l')
                                     (extensional-po-is-prop-valued fe isp y x m m')

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

private
 _≾_ : X → X → 𝓥 ̇
 x ≾ y = ¬ (y < x)

≾-is-prop-valued : funext 𝓥 𝓤₀ → is-prop-valued → (x y : X) → is-prop (x ≾ y)
≾-is-prop-valued fe p x y = negations-are-props fe

<-gives-≾  : (x : X)
           → is-accessible x
           → (y : X) → y < x → y ≾ x
<-gives-≾ = transfinite-induction'
                     (λ x → (y : X) → y < x → y ≾ x)
                     (λ x f y l m → f y l x m l)

≾-refl : (x : X) → is-accessible x → x ≾ x
≾-refl x a l = <-gives-≾ x a x l l

irreflexive : (x : X) → is-accessible x → ¬ (x < x)
irreflexive = ≾-refl

<-gives-≠ : is-well-founded
          → (x y : X) → x < y → x ≠ y
<-gives-≠ w x y l p = irreflexive y (w y) (transport (_< y) p l)

<-gives-≼ : is-transitive → {x y : X} → x < y → x ≼ y
<-gives-≼ t {x} {y} l u m = t u x y m l

≼-coarser-than-≾ : (y : X) → is-accessible y → (x : X) → x ≼ y → x ≾ y
≼-coarser-than-≾ y a x f l = ≾-refl y a (f y l)

is-bot : X → 𝓤 ⊔ 𝓥 ̇
is-bot x = (y : X) → x ≾ y

is-bot' : X → 𝓤 ⊔ 𝓥 ̇
is-bot' x = (y : X) → x ≼ y

is-bot'-gives-is-bot : is-well-founded → (x : X) → is-bot' x → is-bot x
is-bot'-gives-is-bot w x i y = ≼-coarser-than-≾ y (w y) x (i y)

is-bot-gives-is-bot' : (x : X) → is-bot x → is-bot' x
is-bot-gives-is-bot' x i y z l = 𝟘-elim (i z l)

is-top : X → 𝓤 ⊔ 𝓥 ̇
is-top x = (y : X) → y ≾ x

is-top' : X → 𝓤 ⊔ 𝓥 ̇
is-top' x = (y : X) → y ≼ x

is-top'-gives-is-top : is-well-founded → (x : X) → is-top' x → is-top x
is-top'-gives-is-top w x i y = ≼-coarser-than-≾ x (w x) y (i y)

\end{code}

There is no hope of proving the converse constructively, because in
the ordinal of truth values any ¬¬-dense truth-value p satisfies
is-top p, and the only truth-value that satisfies is-top is ⊤. See the
module OrdinalOfTruthValues.

\begin{code}

has-top : 𝓤 ⊔ 𝓥 ̇
has-top = Σ x ꞉ X , is-top x

no-minimal-is-empty : is-well-founded
                    → ∀ {𝓦} (A : X → 𝓦 ̇ )
                    → ((x : X) → A x → is-nonempty (Σ y ꞉ X , (y < x) × A y))
                    → is-empty (Σ A)
no-minimal-is-empty w A s (x , a₀) = γ
 where
  g : (x : X) → is-accessible x → ¬ (A x)
  g x (acc σ) ν = δ
   where
    h : ¬¬ (Σ y ꞉ X , (y < x) × A y)
    h = s x ν

    IH : (y : X) → y < x → ¬ (A y)
    IH y l = g y (σ y l)

    k : ¬ (Σ y ꞉ X , (y < x) × A y)
    k (y , l , a) = IH y l a

    δ : 𝟘
    δ = h k

  f : ((x : X) → A x → ¬¬ (Σ y ꞉ X , (y < x) × A y))
    → (x : X) → ¬ (A x)
  f s x = g x (w x)

  γ : 𝟘
  γ = f s x a₀

no-minimal-is-empty' : is-well-founded
                     → ∀ {𝓦} (A : X → 𝓦 ̇ )
                     → ((x : X) → A x → Σ y ꞉ X , (y < x) × A y)
                     → is-empty (Σ A)
no-minimal-is-empty' w A s = no-minimal-is-empty w A (λ x a → ¬¬-intro (s x a))

\end{code}


The emptiness of the empty set doesn't play any special role in the
above argument, and can be replaced by any type - would that be
useful?

\begin{code}

in-trichotomy : (x y : X) → 𝓤 ⊔ 𝓥 ̇
in-trichotomy x y = (x < y) + (x ＝ y) + (y < x)

is-trichotomous-element : X → 𝓤 ⊔ 𝓥 ̇
is-trichotomous-element x = (y : X) → in-trichotomy x y

is-trichotomous-order : 𝓤 ⊔ 𝓥 ̇
is-trichotomous-order = (x : X) → is-trichotomous-element x

-- injections into in-trichotomy
>-implies-in-trichotomy : {x y : X} → (x < y) → in-trichotomy x y
>-implies-in-trichotomy = inl

＝-implies-in-trichotomy : {x y : X} → (x ＝ y) → in-trichotomy x y
＝-implies-in-trichotomy = inr ∘ inl

<-implies-in-trichotomy : {x y : X} → (y < x) → in-trichotomy x y
<-implies-in-trichotomy = inr ∘ inr

in-trichotomy-symm : {x y : X} → in-trichotomy x y → in-trichotomy y x
in-trichotomy-symm (inl x-lt-y) = inr (inr x-lt-y)
in-trichotomy-symm (inr (inl x-equiv-y)) = inr (inl (x-equiv-y ⁻¹))
in-trichotomy-symm (inr (inr y-lt-x)) = inl y-lt-x

_>_ : (x y : X) → 𝓥 ̇
x > y = y < x

_≦_ : (x y : X) → 𝓤 ⊔ 𝓥 ̇
x ≦ y = (x < y) + (y ＝ x)

_≧_ : (x y : X) → 𝓤 ⊔ 𝓥 ̇
x ≧ y = (x ＝ y) + (y < x)

≧-implies-≦ : {x y : X} → x ≧ y → y ≦ x
≧-implies-≦ x-geq-y = +-commutative x-geq-y

≦-implies-≧ : {x y : X} → x ≦ y → y ≧ x
≦-implies-≧ x-leq-y = +-commutative x-leq-y

≧-implies-in-trichotomy : {x y : X} → x ≧ y → in-trichotomy x y
≧-implies-in-trichotomy = inr

≦-implies-in-trichotomy : {x y : X} → x ≦ y → in-trichotomy x y
≦-implies-in-trichotomy = cases inl (＝-implies-in-trichotomy ∘ _⁻¹)

in-trichotomy-not->-implies-≦ : {x y : X} → in-trichotomy x y → ¬ (y < x) → x ≦ y
in-trichotomy-not->-implies-≦ (inl x-lt-y) y-not-lt-x = inl x-lt-y
in-trichotomy-not->-implies-≦ (inr (inl x-equals-y)) y-not-lt-x = inr (x-equals-y ⁻¹)
in-trichotomy-not->-implies-≦ (inr (inr y-lt-x)) y-not-lt-x = 𝟘-elim (y-not-lt-x y-lt-x)

in-trichotomy-not->-implies-≧ : {x y : X} → in-trichotomy x y → ¬ (x < y) → x ≧ y
in-trichotomy-not->-implies-≧ x-in-trichotomy-y y-not-lt-x =
  ≦-implies-≧ (in-trichotomy-not->-implies-≦
                 (in-trichotomy-symm x-in-trichotomy-y)
                 y-not-lt-x)

≧->-transitive : is-well-order → {x y z : X} → (x ≧ y) → (z < y) → z < x
≧->-transitive wo {x} {y} {z} (inl refl) y-gt-z = y-gt-z
≧->-transitive wo@(p , w , e , t) {x} {y} {z} (inr x-gt-y) y-gt-z = t z y x y-gt-z x-gt-y

>-≧-transitive : is-well-order → {x y z : X} → (y < x) → (y ≧ z) → z < x
>-≧-transitive wo {x} {y} {.y} x-gt-y (inl refl) = x-gt-y
>-≧-transitive wo@(p , w , e , t) {x} {y} {z} x-gt-y (inr y-gt-z) = t z y x y-gt-z x-gt-y

module _ (fe : FunExt) (wo : is-well-order) where
  private
    X-is-set : is-set X
    X-is-set = well-ordered-types-are-sets fe wo

  ≦-is-prop : (x y : X) → is-prop (x ≦ y)
  ≦-is-prop x y = sum-of-contradictory-props (prop-valuedness wo x y)
    X-is-set
    λ x-lt-y x-equals-y → irreflexive y (well-foundedness wo y)
      (transport (_< y) (x-equals-y ⁻¹) x-lt-y)

  ≧-is-prop : (x y : X) → is-prop (x ≧ y)
  ≧-is-prop x y = sum-of-contradictory-props
    (well-ordered-types-are-sets fe wo)
    (prop-valuedness wo y x)
    λ x-equals-y x-gt-y → irreflexive x (well-foundedness wo x)
      (transport (_< x) (x-equals-y ⁻¹) x-gt-y)

  in-trichotomy-is-prop : (x y : X) → is-prop (in-trichotomy x y)
  in-trichotomy-is-prop x y =
    sum-of-contradictory-props (prop-valuedness wo x y) (≧-is-prop x y)
      λ x-lt-y  x-geq-y → irreflexive x (well-foundedness wo x)
        (≧->-transitive wo x-geq-y x-lt-y)

  being-trichotomous-element-is-prop : (x : X) → is-prop (is-trichotomous-element x)
  being-trichotomous-element-is-prop x =
    Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥))
     (λ y → in-trichotomy-is-prop x y)

  trichotomy-is-prop : is-prop (is-trichotomous-order)
  trichotomy-is-prop = Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥))
                         being-trichotomous-element-is-prop

\end{code}

Not all ordinals are trichotomous, in the absence of excluded middle
or even just LPO, because ℕ∞ is not discrete unless LPO holds, but its
natural order is well-founded, and types with well-founded trichotomous
relations are discrete (have decidable equality):

\begin{code}

trichotomous-gives-discrete : is-well-founded
                            → is-trichotomous-order
                            → is-discrete X
trichotomous-gives-discrete w t x y = f (t x y)
 where
  f : (x < y) + (x ＝ y) + (y < x) → (x ＝ y) + (x ≠ y)
  f (inl l)       = inr (<-gives-≠ w x y l)
  f (inr (inl p)) = inl p
  f (inr (inr l)) = inr (≠-sym (<-gives-≠ w y x l))

\end{code}

The following proof that excluded middle gives trichotomy, added 11th
Jan 2021, is the same as that in the HoTT book, except that we use
negation instead of the assumption of existence of propositional
truncations to get a proposition to which we can apply excluded
middle.  But notice that, under excluded middle and function
extensionality, double negation is the same thing as propositional
truncation. Notice also we additionally need function extensionality
as an assumption (to know that the negation of a type is a
proposition).

There is also a shorter proof below that uses the existence of
propositional truncations (but seems different to the proof of the
HoTT book).

\begin{code}
trichotomy : funext (𝓤 ⊔ 𝓥) 𝓤₀
           → excluded-middle (𝓤 ⊔ 𝓥)
           → is-well-order
           → is-trichotomous-order
trichotomy fe em (p , w , e , t) = γ
 where
  P : X → X → 𝓤 ⊔ 𝓥 ̇
  P x y = (x < y) + (x ＝ y) + (y < x)

  γ : (x y : X) → P x y
  γ = transfinite-induction w (λ x → ∀ y → P x y) ϕ
   where
    ϕ : (x : X)
      → ((x' : X) → x' < x → (y : X) → P x' y)
      → (y : X) → P x y
    ϕ x IH-x = transfinite-induction w (λ y → P x y) ψ
     where
      ψ : (y : X)
        → ((y' : X) → y' < y → P x y')
        → P x y
      ψ y IH-y = δ
       where
        A = Σ x' ꞉ X , (x' < x) × ((y < x') + (x' ＝ y))

        ¬¬A-gives-P : ¬¬ A → P x y
        ¬¬A-gives-P = b
         where
          a : A → y < x
          a (x' , l , inl m) = t y x' x m l
          a (x' , l , inr p) = transport (_< x) p l

          b : ¬¬ A → (x < y) + (x ＝ y) + (y < x)
          b = inr ∘ inr ∘ EM-gives-DNE (lower-EM 𝓤 em) (y < x) (p y x) ∘ ¬¬-functor a

        ¬A-gives-≼ : ¬ A → x ≼ y
        ¬A-gives-≼ ν x' l = d
         where
          a : ¬ ((y < x') + (x' ＝ y))
          a f = ν (x' , l , f)

          b : P x' y
          b = IH-x x' l y

          c : ¬ ((y < x') + (x' ＝ y)) → P x' y → x' < y
          c g (inl i)         = i
          c g (inr (inl ii))  = 𝟘-elim (g (inr ii))
          c g (inr (inr iii)) = 𝟘-elim (g (inl iii))

          d : x' < y
          d = c a b

        B = Σ y' ꞉ X , (y' < y) × ((x < y') + (x ＝ y'))

        ¬¬B-gives-P : ¬¬ B → P x y
        ¬¬B-gives-P = b
         where
          a : B → x < y
          a (y' , l , inl m) = t x y' y m l
          a (y' , l , inr p) = transport (_< y) (p ⁻¹) l

          b : ¬¬ B → (x < y) + (x ＝ y) + (y < x)
          b = inl ∘ EM-gives-DNE (lower-EM 𝓤 em) (x < y) (p x y) ∘ ¬¬-functor a

        ¬B-gives-≼ : ¬ B → y ≼ x
        ¬B-gives-≼ ν y' l = d
         where
          a : ¬ ((x < y') + (x ＝ y'))
          a f = ν (y' , l , f)

          b : P x y'
          b = IH-y y' l

          c : ¬ ((x < y') + (x ＝ y')) → P x y' → y' < x
          c g (inl i)         = 𝟘-elim (g (inl i))
          c g (inr (inl ii))  = 𝟘-elim (g (inr ii))
          c g (inr (inr iii)) = iii

          d : y' < x
          d = c a b

        ¬A-and-¬B-give-P : ¬ A → ¬ B → P x y
        ¬A-and-¬B-give-P ν ν' = b
         where
          a : ¬ A → ¬ B → x ＝ y
          a ν ν' = e x y (¬A-gives-≼ ν) (¬B-gives-≼ ν')

          b : (x < y) + (x ＝ y) + (y < x)
          b = inr (inl (a ν ν'))

        δ : P x y
        δ = Cases (em (¬ A) (negations-are-props fe))
             (λ (ν : ¬ A)
                   → Cases (em (¬ B) (negations-are-props fe))
                      (¬A-and-¬B-give-P ν)
                      ¬¬B-gives-P)
             ¬¬A-gives-P
\end{code}

Added 09-04-2022 -- 04-05-2022 by Ohad Kammar.

We can give a shorter proof using `∃¬-gives-∀` and LEM, by deducing
that in a well-order, for every u and v, either u ≼ v or there is some
i < u for which ¬ (i < v).

Like the HoTT proof, we nest two inductions, the outer one that every
element is trichotomous, and the inner one that the currently
considered outer element u is in trichotomy with the currently
considered inner element v.

The crucial observation (`lemma`) is that, under the outer induction
hypothesis for u, the relations (_≼ u) and (_≦ u) coincide. We prove
this observation by appealing to LEM to get that either u ≼ x or there
is a witness i < u but ¬ (i < x). The former means (by extensionality)
that u ＝ x. In the latter case, the witness i satisfies the induction
hypothesis, and so is in trichotomy with x, which by elimination means
i >= x, so u > i >= x.

With this lemma, we can prove the inner induction step by LEM.  If v ≼
u, then by the lemma v <= u and so they are in trichotomy.  Otherwise,
there is a witness i < v , ¬ (i < u). By the induction hypothesis for
v, we have that i is in trichotomy with u, which by elimination means
i >= u, and so v > i >= u, and so u and v are again in trichotomy.

\begin{code}

induction-hypothesis : (P : X → 𝓦 ̇ ) → (x : X) → (𝓤 ⊔ 𝓥 ⊔ 𝓦) ̇
induction-hypothesis P x = (y : X) → y < x → P y

module _
        (f-e : Fun-Ext)
        (em : Excluded-Middle)
       where
 private
   pt : propositional-truncations-exist
   pt = fe-and-em-give-propositional-truncations (λ 𝓤 𝓥 → f-e {𝓤} {𝓥}) em

   fe : FunExt
   fe 𝓤 𝓥 = f-e

   open import UF.PropTrunc
   open PropositionalTruncation pt

   lem-consequence : is-well-order → (u v : X) → (∃ i ꞉ X , ((i < u) × ¬ (i < v))) + (u ≼ v)
   lem-consequence (p , _) u v = Cases
     (∃-not+Π pt em {Σ (λ i → i < u)}
        (λ (i , i-lt-u) → i < v)
        (λ (i , i-<-u) → p i v))
     (λ witness → inl ((∥∥-induction (λ s → ∃-is-prop)
       (λ ((i , i-lt-u) , i-not-lt-v) → ∣ i , i-lt-u , i-not-lt-v ∣) witness)))
     λ prf → inr (λ i i-lt-u → prf (i , i-lt-u))

 trichotomy₂ : is-well-order → is-trichotomous-order
 trichotomy₂ wo@(p , w , e , t) = transfinite-induction w is-trichotomous-element ϕ
  where
   ϕ : (x : X) → induction-hypothesis is-trichotomous-element x → is-trichotomous-element x
   ϕ u ih = -- now we proceed by induction on the inner argument
     transfinite-induction w (in-trichotomy u) λ v innerIH →
       -- use LEM to get either (∃i<v . i≯u) ∨ (v ≼ u)
       Cases (lem-consequence wo v u)
         (∥∥-induction (λ s → in-trichotomy-is-prop fe wo u v)
           λ (i , i-lt-v , i-not-lt-u) → inl -- show u < v
           let u-leq-i = in-trichotomy-not->-implies-≦ ((innerIH i i-lt-v)) i-not-lt-u in
           >-≧-transitive wo i-lt-v (≦-implies-≧ u-leq-i))
         λ v-below-u → in-trichotomy-symm (≦-implies-in-trichotomy (lemma v v-below-u))
    where
     lemma : (x : X) → (x ≼ u) → x ≦ u
     lemma x x-below-u = Cases (lem-consequence wo u x)
       (∥∥-induction (λ s → ≦-is-prop fe wo x u)
         λ (i , i-lt-u , i-not-lt-x) → inl -- show x < u
           let i-in-trichotomy-x = ih i i-lt-u x in
           (>-≧-transitive wo
             i-lt-u
             (in-trichotomy-not->-implies-≧ i-in-trichotomy-x i-not-lt-x)))
       λ u-below-x → inr ((e x u x-below-u u-below-x) ⁻¹)
\end{code}

End of proof added by Ohad Kammar.

The following fact and proof were communicated verbally by Paul Blain
Levy to Martin Escardo and Ohad Kammar on 16th November 2022, and it
is written down in Agda by Martin Escardo on the same date:

\begin{code}

is-decidable-order : 𝓤 ⊔ 𝓥 ̇
is-decidable-order = (x y : X) → is-decidable (x < y)

trichotomy-from-decidable-order : is-transitive
                                → is-extensional
                                → is-well-founded
                                → is-decidable-order
                                → is-trichotomous-order
trichotomy-from-decidable-order t e w d = γ
 where
  T : X → X → 𝓤 ⊔ 𝓥 ̇
  T x y = (x < y) + (x ＝ y) + (y < x)

  γ : (a b : X) → T a b
  γ = transfinite-induction w (λ a → (b : X) → T a b) ϕ
   where
    ϕ : (a : X) → ((x : X) → x < a → (b : X) → T x b) → (b : X) → T a b
    ϕ a IH-a = transfinite-induction w (T a) ψ
     where
      ψ : (b : X) → ((y : X) → y < b → T a y) → T a b
      ψ b IH-b = III
       where
        I : ¬ (a < b) → b ≼ a
        I ν y l = f (IH-b y l)
         where
          f : (a < y) + (a ＝ y) + (y < a) → y < a
          f (inl m)       = 𝟘-elim (ν (t a y b m l))
          f (inr (inl p)) = 𝟘-elim (ν (transport (_< b) (p ⁻¹) l))
          f (inr (inr m)) = m

        II : ¬ (b < a) → a ≼ b
        II ν x l = g (IH-a x l b)
         where
          g : (x < b) + (x ＝ b) + (b < x) → x < b
          g (inl m)       = m
          g (inr (inl p)) = 𝟘-elim (ν (transport (_< a) p l))
          g (inr (inr m)) = 𝟘-elim (ν (t b x a m l))

        III : T a b
        III = h (d a b) (d b a)
         where
          h : (a < b) + ¬ (a < b)
            → (b < a) + ¬ (b < a)
            → (a < b) + (a ＝ b) + (b < a)
          h (inl l) _       = inl l
          h (inr α) (inl l) = inr (inr l)
          h (inr α) (inr β) = inr (inl (e a b (II β) (I α)))

trichotomy₃ : excluded-middle 𝓥
            → is-well-order
            → is-trichotomous-order
trichotomy₃ em (p , w , e , t) = trichotomy-from-decidable-order
                                  t e w (λ x y → em (x < y) (p x y))

decidable-order-from-trichotomy : is-transitive
                                → is-well-founded
                                → is-trichotomous-order
                                → is-decidable-order
decidable-order-from-trichotomy t w τ = γ
 where
  γ : (x y : X) → is-decidable (x < y)
  γ x y = f (τ x y)
   where
    f : (x < y) + (x ＝ y) + (y < x) → (x < y) + ¬ (x < y)
    f (inl l)       = inl l
    f (inr (inl p)) = inr (λ (m : x < y) → irreflexive x (w x) (transport (x <_) (p ⁻¹) m))
    f (inr (inr l)) = inr (λ (m : x < y) → irreflexive x (w x) (t x y x m l))

decidable-order-iff-trichotomy : is-well-order
                               → is-trichotomous-order ↔ is-decidable-order
decidable-order-iff-trichotomy (_ , w , e , t) =
 decidable-order-from-trichotomy t w ,
 trichotomy-from-decidable-order t e w

\end{code}

Paul also remarks that the result can be strengthened as follows: A
transitive well-founded relation is trichotomous iff it is both
extensional and decidable. TODO. Write this down in Agda.

End of 16th November 2022 addition.

\begin{code}
not-<-gives-≼ : funext (𝓤 ⊔ 𝓥) 𝓤₀
              → excluded-middle (𝓤 ⊔ 𝓥)
              → is-well-order
              → (x y : X) → ¬ (x < y) → y ≼ x
not-<-gives-≼ fe em wo@(p , w , e , t) x y = γ (trichotomy fe em wo x y)
 where
  γ : (x < y) + (x ＝ y) + (y < x) → ¬ (x < y) → y ≼ x
  γ (inl l)       ν = 𝟘-elim (ν l)
  γ (inr (inl e)) ν = transport (_≼ x) e ≼-refl
  γ (inr (inr m)) ν = <-gives-≼ t m

≼-or-> : funext (𝓤 ⊔ 𝓥) 𝓤₀
       → excluded-middle (𝓤 ⊔ 𝓥)
       → is-well-order
       → (x y : X) → (x ≼ y) + y < x
≼-or-> fe em wo@(p , w , e , t) x y = γ (trichotomy fe em wo x y)
 where
  γ : (x < y) + (x ＝ y) + (y < x) → (x ≼ y) + (y < x)
  γ (inl l)       = inl (<-gives-≼ t l)
  γ (inr (inl e)) = inl (transport (x ≼_) e ≼-refl)
  γ (inr (inr m)) = inr m

\end{code}

Because we assume function extensionality and excluded middle in this
annonymous submodule, propositional truncations are available, and it
amounts to double negation.

\begin{code}

≾-gives-≼-under-trichotomy : is-transitive
                           → {a b : X}
                           → ((x : X) → in-trichotomy x b)
                           → a ≾ b
                           → a ≼ b
≾-gives-≼-under-trichotomy t {a} {b} τ ν x = γ (τ x)
 where
  γ : (x < b) + (x ＝ b) + (b < x)
    → x < a
    → x < b
  γ (inl m)       l = m
  γ (inr (inl p)) l = 𝟘-elim (ν (transport (_< a) p l))
  γ (inr (inr m)) l = 𝟘-elim (ν (t b x a m l))

≾-gives-≼-under-trichotomy' : is-transitive
                            → is-trichotomous-order
                            → {a b : X} → a ≾ b → a ≼ b
≾-gives-≼-under-trichotomy' t τ {a} {b} = ≾-gives-≼-under-trichotomy t (λ x → τ x b)


module _ (fe : Fun-Ext)
         (em : Excluded-Middle)
       where

 nonempty-has-minimal' : is-well-order
                       → (A : X → 𝓦 ̇ )
                       → ((x : X) → is-prop (A x))
                       → ¬¬ (Σ x ꞉ X , A x)
                       → Σ x ꞉ X , A x × ((y : X) → A y → x ≼ y)
 nonempty-has-minimal' {𝓦} W@(p , w , e , t) A A-is-prop-valued f = γ δ
  where
   Δ : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
   Δ = Σ x ꞉ X , A x × ((y : X) → A y → x ≾ y)

   g : ¬ ((x : X) → A x → ¬¬ (Σ y ꞉ X , (y < x) × A y))
   g = contrapositive (no-minimal-is-empty w A) f

   h : ¬¬ (Σ x ꞉ X , ¬ (A x → ¬¬ (Σ y ꞉ X , (y < x) × A y)))
   h = not-Π-implies-not-not-Σ
        (λ x → EM-gives-DNE em
                (A x → ¬¬ (Σ y ꞉ X , (y < x) × A y))
                (Π₂-is-prop fe (λ _ _ → 𝟘-is-prop)))
        g

   ϕ : (x : X)
     → ¬ (A x → ¬¬ (Σ y ꞉ X , (y < x) × A y))
     → A x × ((y : X) → A y → x ≾ y)
   ϕ x ψ = EM-gives-DNE em (A x)
             (A-is-prop-valued x)
             ((λ ν → ψ (λ a _ → ν a))) ,
           λ y a l → ψ (λ _ ν → ν (y , l , a))

   ν : ¬¬ Δ
   ν = ¬¬-functor (λ (x , f) → x , ϕ x f) h

   j : (x : X) → is-prop ((y : X) → A y → x ≾ y)
   j x = Π₃-is-prop fe (λ y a l → 𝟘-is-prop)

   i : (x : X) → is-prop (A x × ((y : X) → A y → x ≾ y))
   i x = ×-is-prop (A-is-prop-valued x) (j x)

   τ : is-trichotomous-order
   τ = trichotomy₃ em W

   Δ-is-prop : is-prop Δ
   Δ-is-prop (x , a , f) (x' , a' , f') = to-subtype-＝ i q
    where
     q : x ＝ x'
     q = k (τ x x')
      where
       k : (x < x') + (x ＝ x') + (x' < x) → x ＝ x'
       k (inl l)       = 𝟘-elim (f' x a l)
       k (inr (inl p)) = p
       k (inr (inr l)) = 𝟘-elim (f x' a' l)

   δ : Δ
   δ = EM-gives-DNE em Δ Δ-is-prop ν

   γ : Δ → Σ x ꞉ X , A x × ((y : X) → A y → x ≼ y)
   γ (x , a , h) = x , a , (λ y a → ≾-gives-≼-under-trichotomy' t τ {x} {y} (h y a))

 module _ (pt : propositional-truncations-exist) where

  open import UF.PropTrunc
  open PropositionalTruncation pt

  nonempty-has-minimal : is-well-order
                       → (A : X → 𝓦 ̇ )
                       → ((x : X) → is-prop (A x))
                       → ∃ x ꞉ X , A x
                       → Σ x ꞉ X , A x × ((y : X) → A y → x ≼ y)
  nonempty-has-minimal w A i e = nonempty-has-minimal' w A i (inhabited-is-nonempty e)

\end{code}

When do we get x ≾ y → x ≼ y (say for ordinals)? When do we get
cotransitivity? Jean S. Josef observed that cotransitivity gives x ≾ y
→ x ≼ y if _<_ is an order. But cotransitivity alone is enough.

Or consider the truncated version of the following, if _<_ is
proposition valued.

\begin{code}

cotransitive : 𝓤 ⊔ 𝓥 ̇
cotransitive = (x y z : X) → x < y → (x < z) + (z < y)

cotransitive-≾-gives-≼ : cotransitive → (x y : X) → x ≾ y → x ≼ y
cotransitive-≾-gives-≼ c x y n u l = γ (c u x y l)
 where
  γ : (u < y) + (y < x) → u < y
  γ (inl l) = l
  γ (inr l) = 𝟘-elim (n l)

tricho-gives-cotrans : is-transitive → is-trichotomous-order → cotransitive
tricho-gives-cotrans tra tri x y z l = γ (tri z y)
 where
  γ : (z < y) + (z ＝ y) + (y < z) → (x < z) + (z < y)
  γ (inl m)          = inr m
  γ (inr (inl refl)) = inl l
  γ (inr (inr m))    = inl (tra x y z l m)

em-gives-cotrans : FunExt → EM (𝓤 ⊔ 𝓥) → is-well-order → cotransitive
em-gives-cotrans fe em wo@(p , w , e , t) = tricho-gives-cotrans t
                                              (trichotomy (fe (𝓤 ⊔ 𝓥) 𝓤₀) em wo)
\end{code}

This is the end of the submodule with the assumption of excluded
middle.

Originally, in 2011 (see my JSL publication), we needed to work with
the following weakening of well-foundedness (transfinite induction for
detachable subsets), but as of Summer 2018, it is not needed any
longer as we are able to show that our compact ordinals are
well-founded in the standard, stronger, sense.

\begin{code}

is-well-founded₂ : 𝓤 ⊔ 𝓥 ̇
is-well-founded₂ = (p : X → 𝟚) → ((x : X) → ((y : X) → y < x → p y ＝ ₁) → p x ＝ ₁)
                               → (x : X) → p x ＝ ₁

well-founded-Wellfounded₂ : is-well-founded → is-well-founded₂
well-founded-Wellfounded₂ w p = transfinite-induction w (λ x → p x ＝ ₁)

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

open import MLTT.Two-Properties

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
  g (p , m , ϕ) = Cases (𝟚-is-discrete (p z) ₀)
                   (λ (t : p z ＝ ₀)
                            →  inr (pr₂ (ϕ z y) (Lemma[a＝₀→b<c→a<c] t m)))
                   (λ (t : ¬ (p z ＝ ₀))
                            → inl (pr₂ (ϕ x z) (Lemma[a<b→c≠₀→a<c] m t)))
\end{code}

It seems that this is not going to be useful, because although ℕ∞
satisfies this property, the property doesn't seem to be preserved by
the lexicographic order (think about this).
