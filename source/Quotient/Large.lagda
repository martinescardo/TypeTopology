Martin Escardo, August 2018.

Large set quotients in univalent mathematics in Agda notation.

This took place during the Dagstuhl meeting "Formalization of
Mathematics in Type Theory", because Dan Grayson wanted to see how
universe levels work in Agda and I thought that this would be a nice
example to illustrate that.

We assume, in addition to Spartan Martin-Löf type theory,

 * function extensionality
   (any two pointwise equal functions are equal),

 * propositional extensionality
   (any two logically equivalent propositions are equal),

 * propositional truncation
   (any type can be universally mapped into a prop in the same
   universe),

and no resizing axioms.

The K axiom is not used (the without-K option below). We also make
sure pattern matching corresponds to Martin-Löf eliminators, using the
option exact-split. With the option safe we make sure that nothing
is postulated - any non-MLTT axiom has to be an explicit assumption
(argument to a function or a module).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import Quotient.Type
open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.FunExt
open import UF.Hedberg
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Quotient.Large
        (pt  : propositional-truncations-exist)
        (fe  : Fun-Ext)
        (pe  : Prop-Ext)
       where

open PropositionalTruncation pt
open import UF.ImageAndSurjection pt

\end{code}

(NB. The Agda library uses the word "Level" for universes, and then
what we write "𝓤 ̇" here is written "Set 𝓤". This is not good for
univalent mathematics, because the types in 𝓤 ̇ need not be sets, and
also because it places emphasis on levels rather than universes
themselves.)

Now, using an anonymous module UF.with parameters (corresponding to a
section in Coq), we assume propositional truncations that stay in the
same universe, function extensionality for all universes, two
universes 𝓤 and 𝓥, propositional truncation for the universe 𝓥, a type
X : 𝓤 ̇, and an equivalence relation _≈_ with values in 𝓥 ̇.

\begin{code}

module large-quotient
       {𝓤 𝓥 : Universe}
       (X   : 𝓤 ̇ )
       (≋@(_≈_ , ≈p , ≈r , ≈s , ≈t) : EqRel {𝓤} {𝓥} X)
      where

\end{code}

Now, Ω 𝓥 is the type of subsingletons, or (univalent) propositions, or
h-propositions, or mere propositions, in the universe 𝓥, which lives
in the next universe 𝓥 ⁺.

From the relation _≈_ : X → (X → 𝓥 ̇ ) we define a relation
X → (X → Ω 𝓥), which of course is formally a function. We then take
the quotient X/≈ to be the image of this function.

Of course, it is for constructing the image that we need propositional
truncations.

\begin{code}

 equiv-rel : X → (X → Ω 𝓥)
 equiv-rel x y = x ≈ y , ≈p x y

\end{code}

Then the quotient lives in the least upper bound of 𝓤 and 𝓥 ⁺, where 𝓥 ⁺
is the successor of the universe 𝓥:

\begin{code}

 X/≈ : 𝓤 ⊔ (𝓥 ⁺) ̇
 X/≈ = image equiv-rel

 X/≈-is-set : is-set X/≈
 X/≈-is-set = subsets-of-sets-are-sets (X → Ω 𝓥) _
               (powersets-are-sets'' fe fe pe)
               ∥∥-is-prop

 η : X → X/≈
 η = corestriction equiv-rel

\end{code}

Then η is the universal solution to the problem of transforming
equivalence _≈_ into equality _＝_ (identity type).

By construction, η is a surjection, of course:

\begin{code}

 η-surjection : is-surjection η
 η-surjection = corestrictions-are-surjections equiv-rel

\end{code}

It is convenient to use the following induction principle for
reasoning about the image. Notice that the property we consider has
values in any universe 𝓦 we please:

\begin{code}

 quotient-induction : ∀ {𝓦} (P : X/≈ → 𝓦 ̇ )
                    → ((x' : X/≈) → is-prop (P x'))
                    → ((x : X) → P (η x))
                    → (x' : X/≈) → P x'
 quotient-induction = surjection-induction η η-surjection

\end{code}

The first part of the universal property of η says that equivalent
points are mapped to equal points:

\begin{code}

 η-identifies-related-points : {x y : X} → x ≈ y → η x ＝ η y
 η-identifies-related-points {x} {y} e =
   to-Σ-＝ (dfunext fe
          (λ z → to-Σ-＝ (pe (≈p x z) (≈p y z) (≈t y x z (≈s x y e)) (≈t x y z e) ,
                         being-prop-is-prop fe _ _)) ,
       ∥∥-is-prop _ _)

\end{code}

We also need the fact that η reflects equality into equivalence:

\begin{code}

 η-relates-identified-points : {x y : X} → η x ＝ η y → x ≈ y
 η-relates-identified-points {x} {y} p = equiv-rel-reflect (ap pr₁ p)
  where
   equiv-rel-reflect : equiv-rel x ＝ equiv-rel y → x ≈ y
   equiv-rel-reflect q = b (≈r y)
    where
     a : (y ≈ y) ＝ (x ≈ y)
     a = ap (λ - → pr₁ (- y)) (q ⁻¹)
     b : (y ≈ y) → (x ≈ y)
     b = Idtofun a

\end{code}

We are now ready to formulate and prove the universal property of the
quotient. What is noteworthy here, regarding universes, is that the
universal property says that we can eliminate into any set A of any
universe 𝓦.

                   η
              X ------> X/≈
               \       .
                \     .
               f \   . f'
                  \ .
                   v
                   A

\begin{code}

 universal-property : ∀ {𝓦} (A : 𝓦 ̇ )
                    → is-set A
                    → (f : X → A)
                    → ({x x' : X} → x ≈ x' → f x ＝ f x')
                    → ∃! f' ꞉ ( X/≈ → A), f' ∘ η ∼ f
 universal-property {𝓦} A iss f pr = ic
  where
   φ : (x' : X/≈) → is-prop (Σ a ꞉ A , ∃ x ꞉ X ,  (η x ＝ x') × (f x ＝ a))
   φ = quotient-induction _ γ induction-step
     where
      induction-step : (y : X) → is-prop (Σ a ꞉ A , ∃ x ꞉ X ,  (η x ＝ η y) × (f x ＝ a))
      induction-step x (a , d) (b , e) = to-Σ-＝ (p , ∥∥-is-prop _ _)
       where
        h : (Σ x' ꞉ X , (η x' ＝ η x) × (f x' ＝ a))
          → (Σ y' ꞉ X , (η y' ＝ η x) × (f y' ＝ b))
          → a ＝ b
        h (x' , r , s) (y' , t , u) = s ⁻¹ ∙ pr (η-relates-identified-points (r ∙ t ⁻¹)) ∙ u

        p : a ＝ b
        p = ∥∥-rec iss (λ σ → ∥∥-rec iss (h σ) e) d

      γ : (x' : X/≈) → is-prop (is-prop (Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ x') × (f x ＝ a)))
      γ x' = being-prop-is-prop fe

   k : (x' : X/≈) → Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ x') × (f x ＝ a)
   k = quotient-induction _ φ induction-step
    where
     induction-step : (y : X) → Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ η y) × (f x ＝ a)
     induction-step x = f x , ∣ x , refl , refl ∣

   f' : X/≈ → A
   f' x' = pr₁ (k x')

   r : f' ∘ η ∼ f
   r = h
    where
     g : (y : X) → ∃ x ꞉ X , (η x ＝ η y) × (f x ＝ f' (η y))
     g y = pr₂ (k (η y))

     j : (y : X) → (Σ x ꞉ X , (η x ＝ η y) × (f x ＝ f' (η y))) → f' (η y) ＝ f y
     j y (x , p , q) = q ⁻¹ ∙ pr (η-relates-identified-points p)

     h : (y : X) → f' (η y) ＝ f y
     h y = ∥∥-rec iss (j y) (g y)

   c : (σ : Σ f'' ꞉ (X/≈ → A), f'' ∘ η ∼ f) → (f' , r) ＝ σ
   c (f'' , s) = to-Σ-＝ (t , v) -- (t , v)
    where
     w : ∀ x → f' (η x) ＝ f'' (η x)
     w x = r x ∙ (s x)⁻¹

     t : f' ＝ f''
     t = dfunext fe (quotient-induction _ (λ _ → iss) w)

     u : f'' ∘ η ∼ f
     u = transport (λ - → - ∘ η ∼ f) t r

     v : u ＝ s
     v = dfunext fe (λ x → iss (u x) (s x))

   ic : ∃! f' ꞉ (X/≈ → A), f' ∘ η ∼ f
   ic = (f' , r) , c

\end{code}

Added 11 Sep 2023 by Martin Escardo. Package the above into the type
of existence of large effective set quotients.

\begin{code}

large-set-quotients : large-set-quotients-exist
large-set-quotients =
 record
  { _/_ = λ {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → large-quotient.X/≈ X
  ; η/ = λ {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } → large-quotient.η X
  ; η/-identifies-related-points = λ {𝓤 𝓥 : Universe} {X : 𝓤 ̇ }
                                 → large-quotient.η-identifies-related-points X
  ; /-is-set = λ {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } → large-quotient.X/≈-is-set X
  ; /-universality = λ {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } (≋ : EqRel {𝓤} {𝓥} X)
                       {𝓦 : Universe} {Y : 𝓦 ̇ }
                   → large-quotient.universal-property X ≋ Y
  }

large-effective-set-quotients : are-effective large-set-quotients
large-effective-set-quotients {𝓤} {𝓥} {X} ≋ {x} {y} =
 large-quotient.η-relates-identified-points X ≋

\end{code}
