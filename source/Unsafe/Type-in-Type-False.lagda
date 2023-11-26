Martin Escardo, 28th September 2018, 11th October 2018.

This file has two parts.

Part 1 (11th October 2018) is based on a well-known argument,

 Thierry Coquand, The paradox of trees in type theory
 BIT Numerical Mathematics, March 1992, Volume 32, Issue 1, pp 10–14
 https://pdfs.semanticscholar.org/f2f3/30b27f1d7ca99c2550f96581a4400c209ef8.pdf

(see also http://www.cs.nott.ac.uk/~psztxa/g53cfr/l20.html/l20.html),
but phrased in terms of LFPT. See also the module See the module
LawvereFPT for a formulation and proof that doesn't assume
type-in-type.

Part 2 (28th September 2018) is based on a recent argument by Ingo
Blechschmidt. See also the module LawvereFPT.

\begin{code}

{-# OPTIONS --without-K --type-in-type #-}

module Unsafe.Type-in-Type-False where

module coquand where

 open import MLTT.Spartan
 open import Various.LawvereFPT

 Y : {X : Set} → (X → X) → X
 Y {X} f = pr₁ (γ f)
  where
   data 𝕎 : Set where
    sup : (T : Set) → (T → 𝕎) → 𝕎
   e : 𝕎 → 𝕎 → Set
   e (sup T φ) w = Σ t ꞉ T , φ t ＝ w

   R : 𝕎
   R = sup (Σ w ꞉ 𝕎 , (e w w → X)) pr₁

   A : Set
   A = e R R

   r : A → (A → X)
   r ((.R , f) , refl) = f

   s : (A → X) → A
   s f = (R , f) , refl

   rs : (f : A → X) → r (s f) ＝ f
   rs f = refl

   γ : (f : X → X) → Σ x ꞉ X , x ＝ f x
   γ = retract-version.LFPT (r , s , rs)

\end{code}

Then Y is a definitional fixed-point combinator (because the function
s is a definitional section of the function r):

\begin{code}

 Y-is-fp-combinator : {X : Set} (f : X → X) → f (Y f) ＝ Y f
 Y-is-fp-combinator f = refl

 Contradiction : 𝟘
 Contradiction = Y id

\end{code}

Part 2. As mentioned above, this is an application of work of Ingo
Blechschmidt (see the module LavwereFPT) to show that type-in-type,
Streicher's K-axiom, functional and propositional extensionality are
together impossible.

A universe closed under 𝟘, Π, Σ and identity type is enough to get
a contradiction.

In particular, W-types are not needed.

NB. We use the option without-K but then postulate K, so that the uses
of K can be seen explicitly.

postulate K-axiom : (X : Set) → is-set X
postulate funext  : {X : Set} {A : X → Set} {f g : Π A} → f ∼ g → f ＝ g
postulate propext : {P Q : Set} → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ＝ Q

NB. The universe of types is called Set in Agda. This terminology is
consistent with the K axiom.

We don't use any libraries, not even our own libraries, in order to
easily check which closure properties of the universe are needed.
This Agda file is self-contained.

\begin{code}

module blechschmidt where

\end{code}

 We first define 𝟘, Σ and the identity type (written _＝_), and name
 the predefined construction Π:

 \begin{code}

 data 𝟘 : Set where

 𝟘-elim : {A : Set} → 𝟘 → A
 𝟘-elim ()

 Π : {X : Set} (Y : X → Set) → Set
 Π Y = (x : _) → Y x

 record Σ {X : Set} (Y : X → Set) : Set where
   constructor _,_
   field
    pr₁ : X
    pr₂ : Y pr₁

 open Σ public

 Sigma : (X : Set) (Y : X → Set) → Set
 Sigma X Y = Σ Y

 syntax Sigma A (λ x → b) = Σ x ꞉ A , b

 infixr -1 Sigma


 _×_ : Set → Set → Set
 X × Y = Σ x ꞉ X , Y

 data _＝_ {X : Set} : X → X → Set where
   refl : {x : X} → x ＝ x

 \end{code}

 Function identity and composition:

 \begin{code}

 id : {X : Set} → X → X
 id x = x

 _∘_ : {X Y : Set} {Z : Y → Set}
     → ((y : Y) → Z y)
     → (f : X → Y) (x : X) → Z (f x)
 g ∘ f = λ x → g (f x)

 domain : {X : Set} {Y : Set} → (X → Y) → Set
 domain {X} {Y} f = X

 codomain : {X : Set} {Y : Set} → (X → Y) → Set
 codomain {X} {Y} f = Y

 \end{code}

 Equality basics:

 \begin{code}

 transport : {X : Set} (A : X → Set) {x y : X}
           → x ＝ y → A x → A y
 transport A refl = id

 ap : {X Y : Set} (f : X → Y) {x x' : X} → x ＝ x' → f x ＝ f x'
 ap f p = transport (λ - → f _ ＝ f -) p refl

 _⁻¹ : {X : Set} → {x y : X} → x ＝ y → y ＝ x
 p ⁻¹ = transport (λ - → - ＝ _) p refl

 _∙_ : {X : Set} {x y z : X} → x ＝ y → y ＝ z → x ＝ z
 p ∙ q = transport (λ x → _ ＝ x) q p

 to-Σ-＝ : {X : Set} {A : X → Set} {σ τ : Σ A}
        → (Σ p ꞉ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ)
        → σ ＝ τ
 to-Σ-＝ (refl , refl) = refl

 _∼_ : {X : Set} {A : X → Set} → Π A → Π A → Set
 f ∼ g = (x : _) → f x ＝ g x

 \end{code}

 Function extensionality axiom:

 \begin{code}

 postulate funext : {X : Set} {A : X → Set} {f g : Π A} → f ∼ g → f ＝ g

 \end{code}

 Propositions and sets and the K axiom:

 \begin{code}

 is-prop : Set → Set
 is-prop X = (x y : X) → x ＝ y

 is-set : Set → Set
 is-set X = {x y : X} → is-prop (x ＝ y)

 postulate K-axiom : (X : Set) → is-set X

 \end{code}

 Because we are using type-in-type:

 \begin{code}

 Set-is-set : is-set Set
 Set-is-set = K-axiom Set

 being-prop-is-prop : {X : Set} → is-prop (is-prop X)
 being-prop-is-prop {X} f g = funext (λ x → funext (c x))
  where
   c : (x y : X) → f x y ＝ g x y
   c x y = K-axiom X (f x y) (g x y)

 Π-is-prop : {X : Set} {A : X → Set}
           → ((x : X) → is-prop (A x)) → is-prop (Π A)
 Π-is-prop i f g = funext (λ x → i x (f x) (g x))

 \end{code}

 Propositional extensionality axiom:

 \begin{code}

 postulate propext : {P Q : Set} → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ＝ Q

 \end{code}

 Because we have type-in-type and function extensionality, we can
 define propositional truncations (following Voevodsky):

 \begin{code}

 ∥_∥ : Set → Set
 ∥ X ∥ = (P : Set) → is-prop P → (X → P) → P

 ∥∥-is-prop : {X : Set} → is-prop ∥ X ∥
 ∥∥-is-prop {X} = Π-is-prop (λ P → Π-is-prop (λ i → Π-is-prop (λ u → i)))

 ∣_∣ : {X : Set} → X → ∥ X ∥
 ∣ x ∣ = λ P _ u → u x

 ∥∥-rec : {X P : Set} → is-prop P → (X → P) → ∥ X ∥ → P
 ∥∥-rec {X} {P} isp φ s = s P isp φ

 Ω : Set
 Ω = Σ P ꞉ Set , is-prop P

 _holds : Ω → Set
 _holds = pr₁

 holds-is-prop : (p : Ω) → is-prop (p holds)
 holds-is-prop = pr₂

 𝟘-is-prop : is-prop 𝟘
 𝟘-is-prop x y = 𝟘-elim x

 ¬_ : Set → Set
 ¬ X = X → 𝟘

 not : Ω → Ω
 not (P , i) = (¬ P , Π-is-prop (λ x → 𝟘-is-prop))

 \end{code}

 Retracts and equivalences basics:

 \begin{code}

 has-section : {X Y : Set} → (X → Y) → Set
 has-section r = Σ s ꞉ (codomain r → domain r) , r ∘ s ∼ id

 retract_of_ : Set → Set → Set
 retract Y of X = Σ r ꞉ (X → Y) , has-section r

 retracts-compose : {X Y Z : Set} → retract Y of X → retract Z of Y → retract Z of X
 retracts-compose (r , (s , η)) (r' , (s' , η')) = r' ∘ r ,
                                                   (s ∘ s' ,
                                                   λ z → ap r' (η (s' z)) ∙ η' z)

 Id-retract : {X Y : Set} → X ＝ Y → retract Y of X
 Id-retract refl = id , id , (λ y → refl)

 is-section : {X Y : Set} → (X → Y) → Set
 is-section s = Σ r ꞉ (codomain s → domain s), r ∘ s ∼ id

 is-equiv : {X Y : Set} → (X → Y) → Set
 is-equiv f = has-section f × is-section f

 _≃_ : Set → Set → Set
 X ≃ Y = Σ f ꞉ (X → Y) , is-equiv f

 idtoeq : (X Y : Set) → X ＝ Y → X ≃ Y
 idtoeq X Y refl = id , (id , (λ (x : X) → refl)) , id , (λ (y : Y) → refl)

 equiv-retract : {X Y : Set} → X ≃ Y → retract Y of X
 equiv-retract (f , (g , fg) , (h , hf)) = f , g , fg

 \end{code}

 Having defined our basic type theory, postulated our axioms, and
 developed some minimal machinery, we are now ready to embark into our
 proof of false.

 Our main tool is Lawvere's fixed point theorem (formulated and proved
 for retractions rather than surjections, for simplicity, as this is
 enough for us):

 \begin{code}

 LFPT : {A : Set} {X : Set}
      → retract (A → X) of A
      → (f : X → X) → Σ x ꞉ X , x ＝ f x
 LFPT {A} {X} (r , (s , η)) f = x , p
  where
   g : A → X
   g a = f (r a a)

   x : X
   x = r (s g) (s g)

   p : x ＝ f x
   p = ap (λ - → - (s g)) (η g)

 LFPT-＝ : {A : Set} {X : Set}
        → A ＝ (A → X)
        → (f : X → X) → Σ x ꞉ X , x ＝ f x
 LFPT-＝ p = LFPT (Id-retract p)

 \end{code}

 A simple application is to show that negation doesn't have fixed
 points:

 \begin{code}

 not-no-fp : ¬ (Σ P ꞉ Ω , P ＝ not P)
 not-no-fp (P , p) = pr₁ (γ id)
  where
   q : P holds ＝ ¬ (P holds)
   q = ap _holds p

   γ : (f : 𝟘 → 𝟘) → Σ x ꞉ 𝟘 , x ＝ f x
   γ = LFPT-＝ q

 \end{code}

 It is here that we need proposition extensionality in a crucial way:

 \begin{code}

 Π-projection-has-section :
    {A : Set} {X : A → Set}
  → (A₀ : A) → has-section (λ (f : (A : A) → X A → Ω) → f A₀)
 Π-projection-has-section {A} {X} A₀ = s , η
  where
   s : (X A₀ → Ω) → ((A : A) → X A → Ω)
   s φ A x = ∥ (Σ p ꞉ A ＝ A₀ , φ (transport X p x) holds)∥ , ∥∥-is-prop

   η : (φ : X A₀ → Ω) → s φ A₀ ＝ φ
   η φ = funext γ
    where
     a : (x₀ : X A₀) → ∥(Σ p ꞉ A₀ ＝ A₀ , φ (transport X p x₀) holds)∥ → φ x₀ holds
     a x₀ = ∥∥-rec (holds-is-prop (φ x₀)) f
      where
       f : (Σ p ꞉ A₀ ＝ A₀ , φ (transport X p x₀) holds) → φ x₀ holds
       f (p , h) = transport _holds t h
        where
         r : p ＝ refl
         r = K-axiom A p refl

         t : φ (transport X p x₀) ＝ φ x₀
         t = ap (λ - → φ (transport X - x₀)) r

     b : (x₀ : X A₀) → φ x₀ holds → ∥(Σ p ꞉ A₀ ＝ A₀ , φ (transport X p x₀) holds)∥
     b x₀ h = ∣ refl , h ∣

     γ : (x₀ : X A₀) → (∥(Σ p ꞉ A₀ ＝ A₀ , φ (transport X p x₀) holds)∥ , ∥∥-is-prop) ＝ φ x₀
     γ x₀ = to-Σ-＝ (propext ∥∥-is-prop (holds-is-prop (φ x₀)) (a x₀) (b x₀) ,
                    being-prop-is-prop (holds-is-prop _) (holds-is-prop (φ x₀)) )

 \end{code}

 And here is the crucial use of LFPT:

 \begin{code}

 usr-lemma : {A : Set} (X : A → Set)
           → (a₀ : A)
           → retract ((a : A) → X a → Ω) of X a₀
           → (f : Ω → Ω) → Σ P ꞉ Ω , P ＝ f P
 usr-lemma {A} X a₀ retr = LFPT retr'
  where
   retr' : retract (X a₀ → Ω) of X a₀
   retr' = retracts-compose
            retr
            ((λ f → f a₀) , Π-projection-has-section a₀)

 \end{code}

 Using this, we see that for every family X : A → Set we can construct
 a type not in the image of X:

 \begin{code}

 universe-regular-≃ : (A : Set) (X : A → Set) → Σ B ꞉ Set , ((a : A) → ¬ (X a ≃ B))
 universe-regular-≃ A X = B , φ
   where
    B : Set
    B = (a : A) → X a → Ω

    φ : (a : A) → ¬ (X a ≃ B)
    φ a p = not-no-fp (γ not)
     where
      retr : retract B of (X a)
      retr = equiv-retract p

      γ : (f : Ω → Ω) → Σ P ꞉ Ω , P ＝ f P
      γ = usr-lemma {A} X a retr

 universe-regular : (A : Set) (X : A → Set) → Σ B ꞉ Set , ((a : A) → ¬ (X a ＝ B))
 universe-regular A X = γ (universe-regular-≃ A X)
  where
   γ : (Σ B ꞉ Set , ((a : A) → ¬ (X a ≃ B)))
     → (Σ B ꞉ Set , ((a : A) → ¬ (X a ＝ B)))
   γ (B , φ) = B , (λ a p → φ a (idtoeq (X a) B p))

 \end{code}

 And in particular we have that

 \begin{code}

 families-do-not-have-sections : (A : Set) (X : A → Set) → ¬ has-section X
 families-do-not-have-sections A X (s , η) = φ (s B) (η B)
  where
   B : Set
   B = pr₁ (universe-regular A X)

   φ : ∀ a → ¬ (X a ＝ B)
   φ = pr₂ (universe-regular A X)

 \end{code}

 We now consider A = Set and X = id to get the desired contradiction,
 as the identity function obviously does have a section, namely itself:

 \begin{code}

 contradiction : 𝟘
 contradiction = families-do-not-have-sections Set id (id , (λ X → refl))

 \end{code}

 Question: Without assuming type-in-type, can we instead derive a
 contradiction from the existence of a sufficiently large universe U
 with a type X: U such that X≃U?

 Fixities and precedences:

 \begin{code}

 infixl 5 _∘_
 infixr 4 _,_
 infixr 2 _×_
 infix  0 _＝_
 infix  4  _∼_
 infix  50 ¬_

 \end{code}
