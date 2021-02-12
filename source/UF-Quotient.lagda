Martin Escardo, August 2018.

Set quotients in univalent mathematics in Agda notation.

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

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-PropTrunc
open import UF-Base hiding (_≈_)
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-ImageAndSurjection

module UF-Quotient where

\end{code}

We define when a relation is subsingleton (or proposition) valued,
reflexive, transitive or an equivalence.

What is noteworthy, for the purpose of explaining universes in Agda to
Dan, is that X is in a universe 𝓤, and the value of the relation is in
a universe 𝓥, where 𝓤 and 𝓥 are arbitrary.

(NB. The Agda library uses the word "Level" for universes, and then
what we write "𝓤 ̇" here is written "Set 𝓤". This is not good for
univalent mathematics, because the types in 𝓤 ̇ need not be sets, and
also because it places emphasis on levels rather than universes
themselves.)

Then, for example, the function is-prop-valued defined below takes
values in the least upper bound of 𝓤 and 𝓥, which is denoted by 𝓤 ⊔ 𝓥.

We first define the type of five functions and then define them, where
_≈_ is a variable:

\begin{code}

is-prop-valued equiv-relation : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-prop-valued _≈_ = ∀ x y → is-prop (x ≈ y)
equiv-relation _≈_ = is-prop-valued _≈_ × reflexive _≈_ × symmetric _≈_ × transitive _≈_

\end{code}

Now, using an anonymous module with parameters (corresponding to a
section in Coq), we assume propositional truncations that stay in the
same universe, function extensionality for all universes, two
universes 𝓤 and 𝓥, propositional truncation for the universe 𝓥, a type
X : 𝓤 ̇, and an equivalence relation _≈_ with values in 𝓥 ̇.

\begin{code}

module quotient
       {𝓤 𝓥 : Universe}
       (pt  : propositional-truncations-exist)
       (fe  : FunExt)
       (pe  : propext 𝓥)
       (X   : 𝓤 ̇ )
       (_≈_ : X → X → 𝓥 ̇ )
       (≈p  : is-prop-valued _≈_)
       (≈r  : reflexive _≈_)
       (≈s  : symmetric _≈_)
       (≈t  : transitive _≈_)
      where

 open PropositionalTruncation pt
 open ImageAndSurjection pt

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
                (powersets-are-sets'' (fe 𝓤 (𝓥 ⁺)) (fe 𝓥 𝓥) pe)
                ∥∥-is-prop

 η : X → X/≈
 η = corestriction equiv-rel

\end{code}

Then η is the universal solution to the problem of transforming
equivalence _≈_ into equality _≡_ (in Agda the notation for the
identity type is _≡_ - we can't use _=_ because this is a reserved
symbol for definitional equality).

By construction, η is a surjection, of course:

\begin{code}

 η-surjection : is-surjection η
 η-surjection = corestriction-surjection equiv-rel

\end{code}

It is convenient to use the following induction principle for
reasoning about the image. Notice that the property we consider has
values in any universe 𝓦 we please:

\begin{code}

 η-induction : ∀ {𝓦} (P : X/≈ → 𝓦 ̇ )
             → ((x' : X/≈) → is-prop (P x'))
             → ((x : X) → P (η x))
             → (x' : X/≈) → P x'
 η-induction = surjection-induction η η-surjection

\end{code}

The first part of the universal property of η says that equivalent
points are mapped to equal points:

\begin{code}

 η-equiv-equal : {x y : X} → x ≈ y → η x ≡ η y
 η-equiv-equal {x} {y} e = to-Σ-≡ (dfunext (fe 𝓤 (𝓥 ⁺))
                                      (λ z → to-Σ-≡ (pe (≈p x z) (≈p y z) (≈t y x z (≈s x y e)) (≈t x y z e) ,
                                                     being-prop-is-prop (fe 𝓥 𝓥) _ _)) ,
                                   ∥∥-is-prop _ _)

\end{code}

We also need the fact that η reflects equality into equivalence:

\begin{code}

 η-equal-equiv : {x y : X} → η x ≡ η y → x ≈ y
 η-equal-equiv {x} {y} p = equiv-rel-reflect (ap pr₁ p)
  where
   equiv-rel-reflect : equiv-rel x ≡ equiv-rel y → x ≈ y
   equiv-rel-reflect q = b (≈r y)
    where
     a : (y ≈ y) ≡ (x ≈ y)
     a = ap (λ - → pr₁(- y)) (q ⁻¹)
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
                    → ({x x' : X} → x ≈ x' → f x ≡ f x')
                    → ∃! f' ꞉( X/≈ → A), f' ∘ η ≡ f
 universal-property {𝓦} A iss f pr = ic
  where
   φ : (x' : X/≈) → is-prop (Σ a ꞉ A , ∃ x ꞉ X ,  (η x ≡ x') × (f x ≡ a))
   φ = η-induction _ γ induction-step
     where
      induction-step : (y : X) → is-prop (Σ a ꞉ A , ∃ x ꞉ X ,  (η x ≡ η y) × (f x ≡ a))
      induction-step x (a , d) (b , e) = to-Σ-≡ (p , ∥∥-is-prop _ _)
       where
        h : (Σ x' ꞉ X , (η x' ≡ η x) × (f x' ≡ a))
          → (Σ y' ꞉ X , (η y' ≡ η x) × (f y' ≡ b))
          → a ≡ b
        h (x' , r , s) (y' , t , u) = s ⁻¹ ∙ pr (η-equal-equiv (r ∙ t ⁻¹)) ∙ u

        p : a ≡ b
        p = ∥∥-rec iss (λ σ → ∥∥-rec iss (h σ) e) d

      γ : (x' : X/≈) → is-prop (is-prop (Σ a ꞉ A , ∃ x ꞉ X , (η x ≡ x') × (f x ≡ a)))
      γ x' = being-prop-is-prop (fe (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦) (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦))

   k : (x' : X/≈) → Σ a ꞉ A , ∃ x ꞉ X , (η x ≡ x') × (f x ≡ a)
   k = η-induction _ φ induction-step
    where
     induction-step : (y : X) → Σ a ꞉ A , ∃ x ꞉ X , (η x ≡ η y) × (f x ≡ a)
     induction-step x = f x , ∣ x , refl , refl ∣

   f' : X/≈ → A
   f' x' = pr₁(k x')

   r : f' ∘ η ≡ f
   r = dfunext (fe 𝓤 𝓦) h
    where
     g : (y : X) → ∃ x ꞉ X , (η x ≡ η y) × (f x ≡ f' (η y))
     g y = pr₂(k(η y))

     j : (y : X) → (Σ x ꞉ X , (η x ≡ η y) × (f x ≡ f' (η y))) → f'(η y) ≡ f y
     j y (x , p , q) = q ⁻¹ ∙ pr (η-equal-equiv p)

     h : (y : X) → f'(η y) ≡ f y
     h y = ∥∥-rec iss (j y) (g y)

   c : (σ : Σ f'' ꞉ (X/≈ → A), f'' ∘ η ≡ f) → (f' , r) ≡ σ
   c (f'' , s) = to-Σ-≡ (t , v)
    where
     w : ∀ x → f'(η x) ≡ f''(η x)
     w = happly (r ∙ s ⁻¹)

     t : f' ≡ f''
     t = dfunext (fe (𝓤 ⊔ 𝓥 ⁺) 𝓦) (η-induction _ (λ _ → iss) w)

     u : f'' ∘ η ≡ f
     u = transport (λ - → - ∘ η ≡ f) t r

     v : u ≡ s
     v = Π-is-set (fe 𝓤 𝓦) (λ _ → iss) u s

   ic : ∃! f' ꞉ (X/≈ → A), f' ∘ η ≡ f
   ic = (f' , r) , c

\end{code}

Added 11th February 2021. We now repackage the above for convenient
use:

\begin{code}

module Quotient
        (𝓤 𝓥 : Universe)
        (pt  : propositional-truncations-exist)
        (fe  : FunExt)
        (pe  : propext 𝓥)
       where

 open quotient {𝓤} {𝓥} pt fe pe
 open ImageAndSurjection pt

 EqRel : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
 EqRel X = Σ R ꞉ (X → X → 𝓥 ̇ ) , equiv-relation R

 _≈[_]_ : {X : 𝓤 ̇ } → X → EqRel X → X → 𝓥 ̇
 x ≈[ _≈_ , _ ] y = x ≈ y

 _/_ : (X : 𝓤 ̇ ) → EqRel X → 𝓤 ⊔ (𝓥 ⁺) ̇
 X / (_≈_ , p , r , s , t) = X/≈ X _≈_ p r s t

 module _ {X : 𝓤 ̇ }
          ((_≈_ , ≈p , ≈r , ≈s , ≈t) : EqRel X)
        where

  private
   ≋ : EqRel X
   ≋ = (_≈_ , ≈p , ≈r , ≈s , ≈t)

  quotient-is-set : is-set (X / ≋)
  quotient-is-set = X/≈-is-set _ _≈_ ≈p ≈r ≈s ≈t

  η/ : X → X / ≋
  η/ = η X _≈_ ≈p ≈r ≈s ≈t

  η/-is-surjection : is-surjection η/
  η/-is-surjection = η-surjection X _≈_ ≈p ≈r ≈s ≈t

  η/-induction : ∀ {𝓦} (P : X / ≋ → 𝓦 ̇ )
               → ((x' : X / ≋) → is-prop (P x'))
               → ((x : X) → P (η/ x))
               → (x' : X / ≋) → P x'
  η/-induction = surjection-induction η/ η/-is-surjection

  identifies-related-points : {A : 𝓦 ̇ } → (X → A) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  identifies-related-points f = ∀ {x x'} → x ≈ x' → f x ≡ f x'

  η/-identifies-related-points : identifies-related-points η/
  η/-identifies-related-points = η-equiv-equal X _≈_ ≈p ≈r ≈s ≈t

  η/-relates-identified-points : {x y : X}
                              → η/ x ≡ η/ y
                              → x ≈ y
  η/-relates-identified-points = η-equal-equiv X _≈_ ≈p ≈r ≈s ≈t

  module _ {𝓦 : Universe}
           {A : 𝓦 ̇ }
         where

   universal-property/ : is-set A
                       → (f : X → A)
                       → identifies-related-points f
                       → ∃! f' ꞉ (X / ≋ → A), f' ∘ η/ ≡ f
   universal-property/ = universal-property X _≈_ ≈p ≈r ≈s ≈t A

   mediating-map/ : is-set A
                  → (f : X → A)
                  → identifies-related-points f
                  → X / ≋ → A
   mediating-map/ i f p = pr₁ (center (universal-property/ i f p))

   universality-triangle/≡ : (i : is-set A) (f : X → A)
                             (p : identifies-related-points f)
                           → mediating-map/ i f p ∘ η/ ≡ f
   universality-triangle/≡ i f p = pr₂ (center (universal-property/ i f p))


   universality-triangle/ : (i : is-set A) (f : X → A)
                            (p : identifies-related-points f)
                          → mediating-map/ i f p ∘ η/ ∼ f
   universality-triangle/ i f p = happly (universality-triangle/≡ i f p)


   at-most-one-mediating-map/ : is-set A
                              → (g h : X / ≋ → A)
                              → g ∘ η/ ≡ h ∘ η/
                              → g ≡ h
   at-most-one-mediating-map/ i g h p = q ⁻¹ ∙ r
    where
     f = g ∘ η/

     j : identifies-related-points f
     j e = ap g (η/-identifies-related-points e)

     q : mediating-map/ i f j ≡ g
     q = witness-uniqueness (λ f' → f' ∘ η/ ≡ f)
          (universal-property/ i f j)
          (mediating-map/ i f j) g (universality-triangle/≡ i f j)
          refl

     r : mediating-map/ i f j ≡ h
     r = witness-uniqueness (λ f' → f' ∘ η/ ≡ f)
          (universal-property/ i f j)
          (mediating-map/ i f j) h (universality-triangle/≡ i f j)
          (p ⁻¹)

\end{code}

Extending unary and binary operations to the quotient:

\begin{code}

  extension/ : (f : X → X / ≋)
             → identifies-related-points f
             → (X / ≋ → X / ≋)
  extension/ = mediating-map/ quotient-is-set

  extension-triangle/ : (f : X → X / ≋)
                        (i : identifies-related-points f)
                      → extension/ f i ∘ η/ ∼ f
  extension-triangle/ = universality-triangle/ quotient-is-set

  module _ (f : X → X)
           (p : {x y : X} → x ≈ y → f x ≈ f y)
         where

   abstract
    private
      π : identifies-related-points (η/ ∘ f)
      π e = η/-identifies-related-points (p e)

   extension₁/ : X / ≋ → X / ≋
   extension₁/ = extension/ (η/ ∘ f) π

   naturality/ : extension₁/ ∘ η/ ∼ η/ ∘ f
   naturality/ = universality-triangle/ quotient-is-set (η/ ∘ f) π

  module _ (f : X → X → X)
           (p : {x y x' y' : X} → x ≈ x' → y ≈ y' → f x y ≈ f x' y')
         where

   abstract
    private
     π : (x : X) → identifies-related-points (η/ ∘ f x)
     π x {y} {y'} e = η/-identifies-related-points (p {x} {y} {x} {y'} (≈r x) e)

     p' : (x : X) {y y' : X} → y ≈ y' → f x y ≈ f x y'
     p' x {x'} {y'} = p {x} {x'} {x} {y'} (≈r x)

     f₁ : X → X / ≋ → X / ≋
     f₁ x = extension₁/ (f x) (p' x)

     n/ : (x : X) → f₁ x ∘ η/ ∼ η/ ∘ f x
     n/ x = naturality/ (f x) (p' x)

     δ : {x x' : X} → x ≈ x' → (y : X) → f₁ x (η/ y) ≡ f₁ x' (η/ y)
     δ {x} {x'} e y =
       f₁ x (η/ y)   ≡⟨ naturality/ (f x) (p' x) y ⟩
       η/ (f x y)    ≡⟨ η/-identifies-related-points (p e (≈r y)) ⟩
       η/ (f x' y)   ≡⟨ (naturality/ (f x') (p' x') y)⁻¹ ⟩
       f₁ x' (η/ y)  ∎

     ρ : (b : X / ≋) {x x' : X} → x ≈ x' → f₁ x b ≡ f₁ x' b
     ρ b {x} {x'} e =  η/-induction (λ b → f₁ x b ≡ f₁ x' b)
                         (λ y → quotient-is-set) (δ e) b

     f₂ : X / ≋ → X / ≋ → X / ≋
     f₂ d e = extension/ (λ x → f₁ x e) (ρ e) d

   extension₂/ : X / ≋ → X / ≋ → X / ≋
   extension₂/ = f₂

   abstract
    naturality₂/ : (x y : X) → f₂ (η/ x) (η/ y) ≡ η/ (f x y)
    naturality₂/ x y =
     f₂ (η/ x) (η/ y) ≡⟨ extension-triangle/ (λ x → f₁ x (η/ y)) (ρ (η/ y)) x ⟩
     f₁ x (η/ y)      ≡⟨ naturality/ (f x) (p (≈r x)) y ⟩
     η/ (f x y)       ∎

\end{code}
