Martin Escardo, 26 January 2018.

Moved from the file TypeTopology.TotallySeparated 22 August 2024.

Every apartness relation has a tight reflection, in the categorical
sense of reflection, where the morphisms are strongly extensional
functions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc

module Apartness.TightReflection
        (pt : propositional-truncations-exist)
       where

open import Apartness.Definition
open import Apartness.Morphisms
open import Apartness.Negation pt
open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.FunExt
open import UF.ImageAndSurjection pt
open import UF.Powerset hiding (𝕋)
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open PropositionalTruncation pt
open Apartness pt

module tight-reflection
        (fe : Fun-Ext)
        (pe : propext 𝓥)
        (X : 𝓤 ̇ )
        (_♯_ : X → X → 𝓥 ̇ )
        (♯p : is-prop-valued _♯_)
        (♯i : is-irreflexive _♯_)
        (♯s : is-symmetric _♯_)
        (♯c : is-cotransitive _♯_)
      where

\end{code}

We now name the standard equivalence relation induced by _♯_.

\begin{code}

 _~_ : X → X → 𝓥 ̇
 x ~ y = ¬ (x ♯ y)

\end{code}

 For certain purposes we need the apartness axioms packed into a
 single axiom.

\begin{code}

 ♯a : is-apartness _♯_
 ♯a = (♯p , ♯i , ♯s , ♯c)

\end{code}

Initially we tried to work with the function apart : X → (X → 𝓥 ̇ )
defined by apart = _♯_. However, at some point in the development
below it was difficult to proceed, when we need that the identity
type apart x = apart y is a proposition. This should be the case
because _♯_ is is-prop-valued. The most convenient way to achieve this
is to restrict the codomain of apart from 𝓥 to Ω, so that the
codomain of apart is a set.

\begin{code}

 α : X → (X → Ω 𝓥)
 α x y = x ♯ y , ♯p x y

\end{code}

The following is an immediate consequence of the fact that two
equivalent elements have the same apartness class, using functional
and propositional extensionality.

\begin{code}

 α-lemma : (x y : X) → x ~ y → α x ＝ α y
 α-lemma x y na = dfunext fe h
  where
   f : (z : X) → x ♯ z ↔ y ♯ z
   f = elements-that-are-not-apart-have-the-same-apartness-class x y _♯_ ♯a na

   g : (z : X) → x ♯ z ＝ y ♯ z
   g z = pe (♯p x z) (♯p y z) (pr₁ (f z)) (pr₂ (f z))

   h : (z : X) → α x z ＝ α y z
   h z = to-subtype-＝ (λ _ → being-prop-is-prop fe) (g z)

\end{code}

We now construct the tight reflection of (X,♯) to get (X',♯')
together with a universal strongly extensional map from X into tight
apartness types. We take X' to be the image of the map α.

\begin{code}

 X' : 𝓤 ⊔ 𝓥 ⁺ ̇
 X' = image α

\end{code}

The type X may or may not be a set, but its tight reflection is
necessarily a set, and we can see this before we define a tight
apartness on it.

\begin{code}

 X'-is-set : is-set X'
 X'-is-set = subsets-of-sets-are-sets (X → Ω 𝓥) _
              (powersets-are-sets'' fe fe pe) ∥∥-is-prop

 η : X → X'
 η = corestriction α

\end{code}

The following induction principle is our main tool. Its uses look
convoluted at times by the need to show that the property one is
doing induction over is proposition valued. Typically this involves
the use of the fact the propositions form an exponential ideal, and,
 more generally, are closed under products.

\begin{code}

 η-is-surjection : is-surjection η
 η-is-surjection = corestrictions-are-surjections α

 η-induction : (P : X' → 𝓦 ̇ )
             → ((x' : X') → is-prop (P x'))
             → ((x : X) → P (η x))
             → (x' : X') → P x'
 η-induction = surjection-induction η η-is-surjection

\end{code}

The apartness relation _♯'_ on X' is defined as follows.

\begin{code}

 _♯'_ : X' → X' → 𝓤 ⊔ 𝓥 ⁺ ̇
 (u , _) ♯' (v , _) = ∃ x ꞉ X , Σ y ꞉ X , (x ♯ y) × (α x ＝ u) × (α y ＝ v)

\end{code}

Then η preserves and reflects apartness.

\begin{code}

 η-preserves-apartness : preserves _♯_ _♯'_ η
 η-preserves-apartness {x} {y} a = ∣ x , y , a , refl , refl ∣

 η-is-strongly-extensional : is-strongly-extensional _♯_ _♯'_ η
 η-is-strongly-extensional x y = ∥∥-rec (♯p x y) g
  where
   g : (Σ x' ꞉ X , Σ y' ꞉ X , (x' ♯ y') × (α x' ＝ α x) × (α y' ＝ α y))
     → x ♯ y
   g (x' , y' , a , p , q) = ♯s _ _ (j (♯s _ _ (i a)))
    where
     i : x' ♯ y' → x ♯ y'
     i = idtofun _ _ (ap pr₁ (happly p y'))

     j : y' ♯ x → y ♯ x
     j = idtofun _ _ (ap pr₁ (happly q x))

\end{code}

Of course, we must check that _♯'_ is indeed an apartness
relation. We do this by η-induction. These proofs by induction need
routine proofs that some things are propositions.

\begin{code}

 ♯'p : is-prop-valued _♯'_
 ♯'p _ _ = ∥∥-is-prop

 ♯'i : is-irreflexive _♯'_
 ♯'i = by-induction
  where
   induction-step : ∀ x → ¬ (η x ♯' η x)
   induction-step x a = ♯i x (η-is-strongly-extensional x x a)

   by-induction = η-induction (λ x' → ¬ (x' ♯' x'))
                   (λ _ → Π-is-prop fe (λ _ → 𝟘-is-prop))
                   induction-step

 ♯'s : is-symmetric _♯'_
 ♯'s = by-nested-induction
  where
   induction-step : ∀ x y → η x ♯' η y → η y ♯' η x
   induction-step x y a = η-preserves-apartness
                           (♯s x y (η-is-strongly-extensional x y a))

   by-nested-induction =
     η-induction (λ x' → ∀ y' → x' ♯' y' → y' ♯' x')
      (λ x' → Π₂-is-prop fe (λ y' _ → ♯'p y' x'))
      (λ x → η-induction (λ y' → η x ♯' y' → y' ♯' η x)
               (λ y' → Π-is-prop fe (λ _ → ♯'p y' (η x)))
               (induction-step x))

 ♯'c : is-cotransitive _♯'_
 ♯'c = by-nested-induction
  where
   induction-step : ∀ x y z → η x ♯' η y → η x ♯' η z ∨ η y ♯' η z
   induction-step x y z a = ∥∥-functor c b
    where
     a' : x ♯ y
     a' = η-is-strongly-extensional x y a

     b : x ♯ z ∨ y ♯ z
     b = ♯c x y z a'

     c : (x ♯ z) + (y ♯ z) → (η x ♯' η z) + (η y ♯' η z)
     c (inl e) = inl (η-preserves-apartness e)
     c (inr f) = inr (η-preserves-apartness f)

   by-nested-induction =
     η-induction (λ x' → ∀ y' z' → x' ♯' y' → (x' ♯' z') ∨ (y' ♯' z'))
      (λ _ → Π₃-is-prop fe (λ _ _ _ → ∥∥-is-prop))
      (λ x → η-induction (λ y' → ∀ z' → η x ♯' y' → (η x ♯' z') ∨ (y' ♯' z'))
               (λ _ → Π₂-is-prop fe (λ _ _ → ∥∥-is-prop))
               (λ y → η-induction (λ z' → η x ♯' η y → (η x ♯' z') ∨ (η y ♯' z'))
                        (λ _ → Π-is-prop fe (λ _ → ∥∥-is-prop))
                        (induction-step x y)))

 ♯'a : is-apartness _♯'_
 ♯'a = (♯'p , ♯'i , ♯'s , ♯'c)

\end{code}

The tightness of _♯'_ cannot by proved by induction by reduction to
properties of _♯_, as above, because _♯_ is not (necessarily)
tight. We need to work with the definitions of X' and _♯'_ directly.

\begin{code}

 ♯'t : is-tight _♯'_
 ♯'t (u , e) (v , f) n = ∥∥-rec X'-is-set (λ σ → ∥∥-rec X'-is-set (h σ) f) e
  where
   h : (Σ x ꞉ X , α x ＝ u) → (Σ y ꞉ X , α y ＝ v) → (u , e) ＝ (v , f)
   h (x , p) (y , q) = to-Σ-＝ (t , ∥∥-is-prop _ _)
    where
     remark : ¬∃ x ꞉ X , Σ y ꞉ X , (x ♯ y) × (α x ＝ u) × (α y ＝ v)
     remark = n

     r : ¬ (x ♯ y)
     r a = n ∣ x , y , a , p , q ∣

     t : u ＝ v
     t = u   ＝⟨ p ⁻¹ ⟩
         α x ＝⟨ α-lemma x y r ⟩
         α y ＝⟨ q ⟩
         v   ∎

\end{code}

The tightness of _♯'_ gives that η maps equivalent elements to equal
elements, and its irreflexity gives that elements with the same η
image are equivalent.

\begin{code}

 η-equiv-gives-equal : {x y : X} → x ~ y → η x ＝ η y
 η-equiv-gives-equal = ♯'t _ _ ∘ contrapositive (η-is-strongly-extensional _ _)

 η-equal-gives-equiv : {x y : X} → η x ＝ η y → x ~ y
 η-equal-gives-equiv {x} {y} p a = ♯'i
                                    (η y)
                                    (transport (λ - → - ♯' η y)
                                    p
                                    (η-preserves-apartness a))

\end{code}

We now show that the above data provide the tight reflection, or
universal strongly extensional map from X to tight apartness types,
where unique existence is expressed by saying that a Σ type is a
singleton, as usual in univalent mathematics and homotopy type
theory. Notice the use of η-induction to avoid dealing directly with
the details of the constructions performed above.

\begin{code}

 module _
         {𝓦 𝓣 : Universe}
         (A : 𝓦 ̇ )
         (_♯ᴬ_ : A → A → 𝓣 ̇ )
         (♯ᴬa : is-apartness _♯ᴬ_)
         (♯ᴬt : is-tight _♯ᴬ_)
         (f : X → A)
         (f-is-strongly-extensional : is-strongly-extensional _♯_ _♯ᴬ_ f)
        where

  private
   A-is-set : is-set A
   A-is-set = tight-types-are-sets _♯ᴬ_ fe ♯ᴬa ♯ᴬt

   f-transforms-~-into-= : {x y : X} → x ~ y → f x ＝ f y
   f-transforms-~-into-= = ♯ᴬt _ _ ∘ contrapositive (f-is-strongly-extensional _ _)

  tr-lemma : (x' : X') → is-prop (Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ x') × (f x ＝ a))
  tr-lemma = η-induction _ p induction-step
    where
     p : (x' : X')
       → is-prop (is-prop (Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ x') × (f x ＝ a)))
     p x' = being-prop-is-prop fe

     induction-step : (y : X)
                    → is-prop (Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ η y) × (f x ＝ a))
     induction-step x (a , d) (b , e) = to-Σ-＝ (IV , ∥∥-is-prop _ _)
      where
       I : (Σ x' ꞉ X , (η x' ＝ η x) × (f x' ＝ a))
         → (Σ y' ꞉ X , (η y' ＝ η x) × (f y' ＝ b))
         → a ＝ b
       I (x' , r , s) (y' , t , u) =
        a    ＝⟨ s ⁻¹ ⟩
        f x' ＝⟨ f-transforms-~-into-= III ⟩
        f y' ＝⟨ u ⟩
        b    ∎
         where
           II : η x' ＝ η y'
           II = η x' ＝⟨ r ⟩
                η x  ＝⟨ t ⁻¹ ⟩
                η y' ∎

           III : x' ~ y'
           III = η-equal-gives-equiv II

       IV : a ＝ b
       IV = ∥∥-rec A-is-set (λ σ → ∥∥-rec A-is-set (I σ) e) d

  tr-construction : (x' : X') → Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ x') × (f x ＝ a)
  tr-construction = η-induction _ tr-lemma induction-step
   where
    induction-step : (y : X) → Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ η y) × (f x ＝ a)
    induction-step x = f x , ∣ x , refl , refl ∣

  mediating-map : X' → A
  mediating-map x' = pr₁ (tr-construction x')

  private
   f⁻ = mediating-map

  mediating-map-property : (y : X) → ∃ x ꞉ X , (η x ＝ η y) × (f x ＝ f⁻ (η y))
  mediating-map-property y = pr₂ (tr-construction (η y))

  mediating-triangle : f⁻ ∘ η ＝ f
  mediating-triangle = dfunext fe II
   where
    I : (y : X) → (Σ x ꞉ X , (η x ＝ η y) × (f x ＝ f⁻ (η y))) → f⁻ (η y) ＝ f y
    I y (x , p , q) =
     f⁻ (η y) ＝⟨ q ⁻¹ ⟩
     f x      ＝⟨ f-transforms-~-into-= (η-equal-gives-equiv p) ⟩
     f y      ∎

    II : (y : X) → f⁻ (η y) ＝ f y
    II y = ∥∥-rec A-is-set (I y) (mediating-map-property y)

  private
   c' : is-central
          (Σ f⁻ ꞉ (X' → A) , (f⁻ ∘ η ＝ f))
          (f⁻ , mediating-triangle)
   c' (f⁺ , f⁺-triangle) = IV
     where
      I : f⁻ ∘ η ∼ f⁺ ∘ η
      I = happly (f⁻ ∘ η  ＝⟨ mediating-triangle ⟩
                  f       ＝⟨ f⁺-triangle ⁻¹ ⟩
                  f⁺ ∘ η  ∎)

      II : f⁻ ＝ f⁺
      II = dfunext fe (η-induction _ (λ _ → A-is-set) I)

      triangle : f⁺ ∘ η ＝ f
      triangle = transport (λ - → - ∘ η ＝ f) II mediating-triangle

      III : triangle ＝ f⁺-triangle
      III = Π-is-set fe (λ _ → A-is-set) triangle f⁺-triangle

      IV : (f⁻ , mediating-triangle) ＝ (f⁺ , f⁺-triangle)
      IV = to-subtype-＝ (λ h → Π-is-set fe (λ _ → A-is-set)) II

  pre-tight-reflection : ∃! f⁻ ꞉ (X' → A) , (f⁻ ∘ η ＝ f)
  pre-tight-reflection = (f⁻ , mediating-triangle) , c'

  mediating-map-is-strongly-extensional : is-strongly-extensional _♯'_ _♯ᴬ_ f⁻
  mediating-map-is-strongly-extensional = V
   where
    I : (x y : X) → f⁻ (η x) ♯ᴬ f⁻ (η y) → η x ♯' η y
    I x y a = IV
     where
      II : f x ♯ᴬ f y
      II = transport₂ (_♯ᴬ_)
            (happly mediating-triangle x)
            (happly mediating-triangle y) a

      III : x ♯ y
      III = f-is-strongly-extensional x y II

      IV : η x ♯' η y
      IV = η-preserves-apartness III

    V : ∀ x' y' → f⁻ x' ♯ᴬ f⁻ y' → x' ♯' y'
    V = η-induction (λ x' → (y' : X') → f⁻ x' ♯ᴬ f⁻ y' → x' ♯' y')
          (λ x' → Π₂-is-prop fe (λ y' _ → ♯'p x' y'))
          (λ x → η-induction (λ y' → f⁻ (η x) ♯ᴬ f⁻ y' → η x ♯' y')
                  (λ y' → Π-is-prop fe (λ _ → ♯'p (η x) y'))
                  (I x))

  private
   c : is-central
        (Σ f⁻ ꞉ (X' → A) , (is-strongly-extensional _♯'_ _♯ᴬ_ f⁻) × (f⁻ ∘ η ＝ f))
        (f⁻ , mediating-map-is-strongly-extensional , mediating-triangle)
   c (f⁺ , f⁺-is-strongly-extensional , f⁺-triangle) =
    to-subtype-＝
      (λ h → ×-is-prop
               (being-strongly-extensional-is-prop fe _♯'_ _♯ᴬ_ ♯'p h)
               (Π-is-set fe (λ _ → A-is-set)))
      (ap pr₁ (c' (f⁺ , f⁺-triangle)))


  tight-reflection : ∃! f⁻ ꞉ (X' → A)
                           , (is-strongly-extensional _♯'_ _♯ᴬ_ f⁻)
                           × (f⁻ ∘ η ＝ f)
  tight-reflection = (f⁻ , mediating-map-is-strongly-extensional ,
                     mediating-triangle) ,
                     c

\end{code}

The following is an immediate consequence of the tight reflection,
by the usual categorical argument, using the fact that the identity
map is strongly extensional (with the identity function as the
proof). Notice that our construction of the reflection produces a
result in a universe higher than those where the starting data are,
to avoid impredicativity (aka propositional resizing). Nevertheless,
the usual categorical argument is applicable.

A direct proof that doesn't rely on the tight reflection is equally
short in this case, and is also included.

What the following construction says is that if _♯_ is tight, then
any element of X is uniquely determined by the set of elements apart
from it.

\begin{code}

 tight-η-equiv-abstract-nonsense : is-tight _♯_ → X ≃ X'
 tight-η-equiv-abstract-nonsense ♯t = η , (θ , happly p₄) , (θ , happly p₀)
  where
   u : ∃! θ ꞉ (X' → X), θ ∘ η ＝ id
   u = pre-tight-reflection X _♯_ ♯a ♯t id (λ _ _ a → a)

   v : ∃! ζ ꞉ (X' → X'), ζ ∘ η ＝ η
   v = pre-tight-reflection X' _♯'_ ♯'a ♯'t η η-is-strongly-extensional

   θ : X' → X
   θ = ∃!-witness u

   ζ : X' → X'
   ζ = ∃!-witness v

   φ : (ζ' : X' → X') → ζ' ∘ η ＝ η → ζ ＝ ζ'
   φ ζ' p = ap pr₁ (∃!-uniqueness' v (ζ' , p))

   p₀ : θ ∘ η ＝ id
   p₀ = ∃!-is-witness u

   p₁ : η ∘ θ ∘ η ＝ η
   p₁ = ap (η ∘_) p₀

   p₂ : ζ ＝ η ∘ θ
   p₂ = φ (η ∘ θ) p₁

   p₃ : ζ ＝ id
   p₃ = φ id refl

   p₄ = η ∘ θ ＝⟨ p₂ ⁻¹ ⟩
        ζ     ＝⟨ p₃ ⟩
        id    ∎

 tight-η-equiv-direct : is-tight _♯_ → X ≃ X'
 tight-η-equiv-direct t = (η , vv-equivs-are-equivs η cm)
  where
   lc : left-cancellable η
   lc {x} {y} p = j h
    where
     j : ¬ (η x ♯' η y) → x ＝ y
     j = t x y ∘ contrapositive (η-preserves-apartness {x} {y})

     h : ¬ (η x ♯' η y)
     h a = ♯'i (η y) (transport (λ - → - ♯' η y) p a)

   e : is-embedding η
   e = lc-maps-into-sets-are-embeddings η lc X'-is-set

   cm : is-vv-equiv η
   cm = surjective-embeddings-are-vv-equivs η e η-is-surjection

\end{code}

TODO.

* The tight reflection has the universal property of the quotient by
  _~_. Conversely, the quotient by _~_ gives the tight reflection.

* The tight reflection of ♯₂ has the universal property of the totally
  separated reflection.

* If a type Y has an apartness with y₀ ♯ y₁, then
  the function type (X → Y) has an apartness

    f ♯ g := ∃ x ꞉ X , f x ♯ g x

  that tells apart the constant functions with values y₀ and y₁
  respectively.
