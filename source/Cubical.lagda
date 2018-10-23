Adapted by Martin Escardo, 22 October 2018, from code
https://github.com/agda/cubical by

  Anders Mörtberg
  Andrea Vezzosi

This is a small cubical library.

* Users who want to use this module for the purposes of univalent
  mathematics can work with _≡_ , J , refl as black boxes, ignoring
  the cubical machinery. Function extensionality, univalence and
  propositional truncation formulated with respect to the identity
  type are provided.

* The identity type is denoted by _≡_. The computation rule for its
  induction principle J holds definitionally.

* The cubical path type is denoted by Path or _≡ᶜ_. The computation
  rule for its induction principle Jᶜ holds up to a path only.

  More generally, notions that are defined with respect to cubical
  path types rather than identity types are decorated by the
  superscript "ᶜ".

* We first develop the cubical machinery, which is needed in order to
  develop the HoTT/UF primitive constructions.

* At the moment this needs the development version of Agda.

This is still not fully adapted for our development

  http://www.cs.bham.ac.uk/~mhe/agda-new/
  https://github.com/martinescardo/TypeTopology

We need to reorganize our UF-* files and make them compatible with
this (and to replace the inductive definition of _≡_ with the
definition given here, which implies removing all pattern matching on
refl from those files, which is going to be a considerable amount of
work).

\begin{code}

{-# OPTIONS --cubical --exact-split #-}

module Cubical where

open import Universes public
open import Sigma public

open import Agda.Builtin.Cubical.Path public
     renaming (_≡_ to _≡ᶜ_)

open import Agda.Builtin.Cubical.Sub public

open import Agda.Primitive.Cubical public
     renaming ( primIMin       to _∧_  -- I → I → I
              ; primIMax       to _∨_  -- I → I → I
              ; primINeg       to ~_   -- I → I
              ; i0             to i₀
              ; i1             to i₁
              ; isOneEmpty     to empty-system
              ; primHComp      to hcomp
              ; primTransp     to transp
              ; IsOne          to is₁
              ; itIsOne        to i₁-is₁ )
     hiding (primComp) -- This should not be used.

open import Agda.Builtin.Cubical.Id public
  hiding ( primIdJ ;    -- This should not be used as it is using compCCHM.
           primIdFace ; -- These should probably be hidden from the user.
           primIdPath )

\end{code}

* The Interval lives in the universe Uω:
    I : Uω

  Endpoints, Connections, Reversal:
    i₀ i₁   : I
    _∧_ _∨_ : I → I → I
    ~_      : I → I

* Dependent path type. (Path over Path)

  Introduced with lambda abstraction and eliminated with application,
  just like function types.

    PathP : ∀ {U} (A : I → U ̇) → A i0 → A i₁ → U ̇

  Non dependent path types:

\begin{code}

Path : ∀ {U} (A : U ̇) → A → A → U ̇
Path A a b = PathP (λ _ → A) a b

\end{code}

PathP (\ i → A) x y amounts to x ≡ᶜ y when A does not mention i.
   _≡ᶜ_ : ∀ {U} {A : U ̇} → A → A → U ̇
   _≡ᶜ_ = PathP (λ _ → A)

* "is₁ r" represents the constraint "r = i₁".

  Often we will use "φ" for elements of I, when we intend to use them
  with is₁ (or Partial[P]).

    is₁ : I → U

  i₁ is indeed equal to i₁:

    i₁-is₁ : is₁ i₁

* Types of partial elements, and their dependent version.

  "Partial A φ" is a special version of "is₁ φ → A" with a more
  extensional judgmental equality.

  "PartialP φ A" allows "A" to be defined only on "φ".

    Partial : ∀ {U} → U ̇ → I → Uω
    PartialP : ∀ {U} → (φ : I) → Partial (U ̇) φ → Uω

Partial elements are introduced by pattern matching with (r = i0)
or (r = i₁) constraints, like so:

\begin{code}

private
  sys : ∀ i → Partial (i ∨ ~ i) (U₁ ̇)
  sys i (i = i₀) = U₀ ̇
  sys i (i = i₁) = U₀ ̇ → U₀ ̇

\end{code}

It also works with pattern matching lambdas:
http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.PatternMatchingLambdas

\begin{code}

  sys' : ∀ i → Partial (i ∨ ~ i) (U₁ ̇)
  sys' i = \ { (i = i₀) → U₀ ̇
             ; (i = i₁) → U₀ ̇ → U₀ ̇
             }

\end{code}

When the cases overlap they must agree:

\begin{code}

  sys2 : ∀ i j → Partial (i ∨ (i ∧ j)) (U₁ ̇)
  sys2 i j = \ { (i = i₁)          → U₀ ̇
               ; (i = i₁) (j = i₁) → U₀ ̇
               }

\end{code}

(i₀ = i₁) is absurd:

\begin{code}

  sys3 : Partial i₀ (U₁ ̇)
  sys3 = \ { () }

\end{code}

* There are cubical subtypes as in CCHM. Note that these are not
  fibrant (and hence are in Uω):

\begin{code}

_[_↦_] : ∀ {U} (A : U ̇) (φ : I) (u : Partial φ A) → Uω
A [ φ ↦ u ] = Sub A φ u

\end{code}

Any element u : A can be seen as an element of A [ φ ↦ u ] which
agrees with u on φ:

    inc : ∀ {U} {A : U ̇} {φ} (u : A) → A [ φ ↦ (λ _ → u) ]

One can also forget that an element agrees with u on φ:

\begin{code}

ouc : ∀ {U} {A : U ̇} {φ : I} {u : Partial φ A} → A [ φ ↦ u ] → A
ouc = primSubOut

\end{code}

* Composition operation according to [CCHM 18].  When calling "comp A
  φ u a" Agda makes sure that "a" agrees with "u i₀" on "φ".

    compCCHM : ∀ {U} (A : I → U ̇) (φ : I)
            → (∀ i → Partial (A i) φ) → A i₀ → A i₁

  Note. This is not recommended to use. Instead use the CHM
  primitives!  The reason is that these work with HITs and produce
  fewer empty systems.

* Generalized transport and homogeneous composition [CHM 18].

  When calling "transp A φ a" Agda makes sure that "A" is constant on
  "φ":

    transp : ∀ {U} (A : (i : I) → U ̇) (φ : I) (a : A i₀) → A i₁

  When calling "hcomp A φ u a" Agda makes sure that "a" agrees with "u
  i₀" on "φ".

    hcomp : ∀ {U} {A : U ̇} {φ : I} (u : I → Partial A φ) (a : A) → A

Homogeneous filling:

\begin{code}

hfill : ∀ {U} {A : U ̇} {φ : I}
          (u : ∀ i → Partial φ A)
          (u0 : A [ φ ↦ u i₀ ]) (i : I) → A
hfill {φ = φ} u u0 i =
  hcomp (λ j → \ { (φ = i₁) → u (i ∧ j) i₁-is₁
                 ; (i = i₀) → ouc u0 })
        (ouc u0)

\end{code}

Heterogeneous composition defined as in CHM:

\begin{code}

comp : ∀ {U} (A : I → U ̇) {φ : I}
         (u : ∀ i → Partial φ (A i))
         (u0 : A i₀ [ φ ↦ u i₀ ]) → A i₁
comp A {φ = φ} u u0 =
  hcomp (\ i → \ { (φ = i₁) → transp (\ j → A (i ∨ j)) i (u _ i₁-is₁) })
        (transp A i₀ (ouc u0))

\end{code}

Heterogeneous filling defined using comp:

\begin{code}

fill : ∀ {U} (A : I → U ̇) {φ : I}
         (u : ∀ i → Partial φ (A i))
         (u0 : A i₀ [ φ ↦ u i₀ ])
     → PathP A (ouc u0) (comp A u u0)
fill A {φ = φ} u u0 i =
  comp (λ j → A (i ∧ j))
       (λ j → \ { (φ = i₁) → u (i ∧ j) i₁-is₁
                ; (i = i₀) → ouc u0 })
       (inc {φ = φ ∨ (~ i)} (ouc {φ = φ} u0))

\end{code}

Direct definition of transport filler, note that we have to explicitly
tell Agda that the type is constant (like in CHM):

\begin{code}

transp-fill : ∀ {U} {A' : U ̇} (φ : I)
                (A : (i : I) → (U ̇) [ φ ↦ (\ _ → A') ])
                (u0 : ouc (A i₀))
            → PathP (λ i → ouc (A i)) u0 (transp (λ i → ouc (A i)) φ u0)
transp-fill φ A u0 i = transp (\ j → ouc (A (i ∧ j))) (~ i ∨ φ) u0

\end{code}

Basic theory of paths.

\begin{code}

module _ {U} {X : U ̇} where

  reflᶜ : {x : X} → x ≡ᶜ x
  reflᶜ {x} = λ _ → x

  symᶜ : {x y : X} → x ≡ᶜ y → y ≡ᶜ x
  symᶜ p = λ i → p (~ i)

  apᶜ : ∀ {V} {A : X → V ̇} {x y : X}
          (f : (x : X) → A x) (p : x ≡ᶜ y)
      → PathP (λ i → A (p i)) (f x) (f y)
  apᶜ f p = λ i → f (p i)

\end{code}

This is called path-comp and not transᶜ in order to avoid confusion
with transp:

\begin{code}

  path-comp : {x y z : X} → x ≡ᶜ y → y ≡ᶜ z → x ≡ᶜ z
  path-comp {x = x} p q i =
    hcomp (λ j → λ { (i = i₀) → x
                   ; (i = i₁) → q j }) (p i)

  _≡ᶜ⟨_⟩_ : (x : X) {y z : X} → x ≡ᶜ y → y ≡ᶜ z → x ≡ᶜ z
  _ ≡ᶜ⟨ p ⟩ q = path-comp p q

  _∎ᶜ : (x : X) → x ≡ᶜ x
  _∎ᶜ _ = reflᶜ

  infix  1 _∎ᶜ
  infixr 0 _≡ᶜ⟨_⟩_

module _ {U V} {A : U ̇} {B : A → V ̇} where
  transportᶜ : {a b : A} (p : a ≡ᶜ b) → B a → B b
  transportᶜ p pa = transp (λ i → B (p i)) i₀ pa

  transportᶜ-refl : {a : A} (pa : B a) → transportᶜ reflᶜ pa ≡ᶜ pa
  transportᶜ-refl {a = a} pa i = transp (λ _ → B a) i pa

  funextᶜ : {f g : (x : A) → B x} → ((x : A) → f x ≡ᶜ g x) → f ≡ᶜ g
  funextᶜ p i x = p x i

\end{code}

Transporting along a constant family is the identity function, up to a
path. If we had regularity this would be definitional:

\begin{code}

transp-refl : ∀ {U} (A : U ̇) (u0 : A)
            → PathP (λ _ → A) (transp (λ _ → A) i₀ u0) u0
transp-refl A u0 i = transp (λ _ → A) i u0

\end{code}

J for paths and its (non-definitional) computation rule:

\begin{code}

module _ {U V}
         {A : U ̇}
         {x : A}
         (P : ∀ y → x ≡ᶜ y → V ̇)
         (d : P x reflᶜ)
      where

  Jᶜ : {y : A} → (p : x ≡ᶜ y) → P y p
  Jᶜ p = transp (λ i → P (p i) (λ j → p (i ∧ j))) i₀ d

  Jᶜ-refl : Jᶜ reflᶜ ≡ᶜ d
  Jᶜ-refl i = transp (λ _ → P x reflᶜ) i d

module _ {U} {A : U ̇} where
  singletonᶜ : (a : A) → U ̇
  singletonᶜ a = Σ \(x : A) → a ≡ᶜ x

  singletonᶜ-is-contrᶜ : {a b : A} (p : a ≡ᶜ b) → Path (singletonᶜ a) (a , reflᶜ) (b , p)
  singletonᶜ-is-contrᶜ p i = (p i , λ j → p (i ∧ j))

\end{code}

Converting to and from a PathP:

\begin{code}

module _ {U} {A : I → U ̇} {x : A i₀} {y : A i₁} where

  to-PathP : transp A i₀ x ≡ᶜ y → PathP A x y
  to-PathP p i = hcomp (λ j → λ { (i = i₀) → x ; (i = i₁) → p j })
                      (transp (λ j → A (i ∧ j)) (~ i) x)

  from-PathP : PathP A x y → transp A i₀ x ≡ᶜ y
  from-PathP p i = transp (λ j → A (i ∨ j)) i (p i)

\end{code}

Lower h-levels defined in terms of paths:

\begin{code}

module _ {U} where

  is-contrᶜ : U ̇ → U ̇
  is-contrᶜ A = Σ \(x : A) → ∀ y → x ≡ᶜ y

  is-propᶜ : U ̇ → U ̇
  is-propᶜ A = (x y : A) → x ≡ᶜ y

  is-setᶜ : U ̇ → U ̇
  is-setᶜ A = (x y : A) → is-propᶜ (x ≡ᶜ y)

fiberᶜ : ∀ {U V} {A : U ̇} {B : V ̇} (f : A → B) (y : B) → U ⊔ V ̇
fiberᶜ {A = A} f y = Σ \(x : A) → y ≡ᶜ f x

is-equivᶜ : ∀ {U V} {A : U ̇} {B : V ̇} (f : A → B) → U ⊔ V ̇
is-equivᶜ f = ∀ y → is-contrᶜ (fiberᶜ f y)

infix 4 _≃ᶜ_

_≃ᶜ_ : ∀ {U V} (A : U ̇) (B : V ̇) → U ⊔ V ̇
A ≃ᶜ B = Σ \(f : A → B) → is-equivᶜ f

Eqᶜ-to-fun : ∀ {U V} {A : U ̇} {B : V ̇} → A ≃ᶜ B → A → B
Eqᶜ-to-fun = pr₁

Eqᶜ-to-fun-is-equivᶜ : ∀ {U V} {A : U ̇} {B : V ̇} (e : A ≃ᶜ B) → is-equivᶜ (Eqᶜ-to-fun e)
Eqᶜ-to-fun-is-equivᶜ = pr₂

Eqᶜ-to-fun-pointed-fibers : ∀ {U V} {A : U ̇} {B : V ̇} (e : A ≃ᶜ B) (y : B) → fiberᶜ (Eqᶜ-to-fun e) y
Eqᶜ-to-fun-pointed-fibers e y = pr₁ (pr₂ e y)

Eqᶜ-to-fun-contractible-fibers : ∀ {U V} {A : U ̇} {B : V ̇} (e : A ≃ᶜ B) (y : B)
                             → (v : fiberᶜ (Eqᶜ-to-fun e) y) → Eqᶜ-to-fun-pointed-fibers e y ≡ᶜ v
Eqᶜ-to-fun-contractible-fibers e y = pr₂ (pr₂ e y)

{-# BUILTIN EQUIV _≃ᶜ_ #-}
{-# BUILTIN EQUIVFUN  Eqᶜ-to-fun #-}

module GluePrims where
  primitive
    primGlue    : ∀ {U V} (A : U ̇) {φ : I}
      → (T : Partial φ (V ̇)) → (e : PartialP φ (λ o → T o ≃ᶜ A))
      → V ̇
    prim^glue   : ∀ {U V} {A : U ̇} {φ : I}
      → {T : Partial φ (V ̇)} → {e : PartialP φ (λ o → T o ≃ᶜ A)}
      → PartialP φ T → A → primGlue A T e
    prim^unglue : ∀ {U V} {A : U ̇} {φ : I}
      → {T : Partial φ (V ̇)} → {e : PartialP φ (λ o → T o ≃ᶜ A)}
      → primGlue A T e → A

open GluePrims public
  renaming ( primGlue to Glue
           ; prim^glue to glue
           ; prim^unglue to unglue)

≃ᶜ-refl : ∀ {U} → (A : U ̇) → A ≃ᶜ A
≃ᶜ-refl A = (λ a → a) , λ { y → (y , reflᶜ) , λ z → singletonᶜ-is-contrᶜ (pr₂ z) }

Eqᶜ-to-Path : ∀ {U} {A B : U ̇} → A ≃ᶜ B → A ≡ᶜ B
Eqᶜ-to-Path {_} {A} {B} e i =
  Glue B
       (λ {(i = i₀) → _ ; (i = i₁) → _})
       (λ {(i = i₀) → e ; (i = i₁) → ≃ᶜ-refl B})

unglue-is-equivᶜ : ∀ {U} (A : U ̇) (φ : I) (T : Partial φ (U ̇))
                  (f : PartialP φ (λ o → T o ≃ᶜ A))
                → is-equivᶜ {U} {U} {Glue A T f} (unglue {U} {U} {A} {φ})
unglue-is-equivᶜ A φ T f = λ (b : A) →
  let u : I → Partial φ A
      u i = λ{ (φ = i₁) → pr₂ (Eqᶜ-to-fun-pointed-fibers (f i₁-is₁) b) i }
      ctr : fiberᶜ (unglue {φ = φ}) b
      ctr = ( glue (λ { (φ = i₁) → pr₁(Eqᶜ-to-fun-pointed-fibers (f i₁-is₁) b) }) (hcomp u b)
            , λ j → hfill u (inc b) j)
  in ( ctr
     , λ (v : fiberᶜ (unglue {φ = φ}) b) i →
         let u' : I → Partial (φ ∨ ~ i ∨ i) A
             u' j = λ { (φ = i₁) → pr₂(Eqᶜ-to-fun-contractible-fibers (f i₁-is₁) b v i) j
                      ; (i = i₀) → hfill u (inc b) j
                      ; (i = i₁) → pr₂ v j }
         in ( glue (λ { (φ = i₁) → pr₁(Eqᶜ-to-fun-contractible-fibers (f i₁-is₁) b v i) }) (hcomp u' b)
            , λ j → hfill u' (inc b) j))

\end{code}

Any partial family of equivalences can be extended to a total one
from Glue [ φ ↦ (T,f) ] A to A:

\begin{code}

unglue-equiv : ∀ {U} (A : U ̇) (φ : I)
                (T : Partial φ (U ̇))
                (f : PartialP φ (λ o → T o ≃ᶜ A))
            → Glue A T f ≃ᶜ A
unglue-equiv A φ T f = unglue {φ = φ} , unglue-is-equivᶜ A φ T f

\end{code}

A form of the cubical univalence theorem:

\begin{code}

univalenceᶜ : ∀ {U} (A : U ̇) → is-contrᶜ (Σ \(T : U ̇) → T ≃ᶜ A)
univalenceᶜ {U} A = ( A , ≃ᶜ-refl A)
               , λ w i → let T : Partial (~ i ∨ i) (U ̇)
                             T = λ { (i = i₀) → A ; (i = i₁) → pr₁ w }
                             f : PartialP (~ i ∨ i) (λ x → T x ≃ᶜ A)
                             f = λ { (i = i₀) → ≃ᶜ-refl A ; (i = i₁) → pr₂ w }
                         in ( Glue A T f , unglue-equiv _ _ T f)


\end{code}

We now work with the identity type _≡_ instead of the path type _≡ᶜ_:

\begin{code}

{- BUILTIN ID Id -}

_≡_ : ∀ {U} {A : U ̇} → A → A → U ̇
_≡_ = Id

\end{code}

Version of the constructor for Id where the y is also explicit. This
is sometimes useful when it is needed for typechecking (see J below).

\begin{code}

conId : ∀ {U} {A : U ̇} {x : A} (φ : I) (y : A [ φ ↦ (λ _ → x) ])
     → (Path _ x (ouc y)) [ φ ↦ (λ { (φ = i₁) → λ _ → x}) ]
     → x ≡ ouc y
conId φ _ w = conid φ (ouc w)

refl : ∀ {U} {A : U ̇} {x : A} → x ≡ x
refl {U} {A} {x} = conid i₁ (λ _ → x)

\end{code}

Direct eliminator for Id:

\begin{code}

module IdPrims where
  primitive
    primIdElim : ∀ {U V} {A : U ̇} {x : A}
                   (P : ∀ (y : A) → x ≡ y → V ̇)
                   (h : ∀ (φ : I) (y : A [ φ ↦ (λ _ → x) ])
                          (w : (Path _ x (ouc y)) [ φ ↦ (λ { (φ = i₁) → λ _ → x}) ] ) →
                          P (ouc y) (conid φ (ouc w))) →
                   {y : A} (w' : x ≡ y) → P y w'

open IdPrims public renaming (primIdElim to elimId)

\end{code}

Definition of J for _≡_. Importantly, as opposed to Jᶜ for ≡ᶜ, the
computation rule holds definitionally for J:

\begin{code}

module _ {U V} {A : U ̇} {x : A} (P : ∀ (y : A) → Id x y → V ̇) (d : P x refl) where
  J : ∀ {y : A} (w : x ≡ y) → P y w
  J = elimId P (λ φ y w → comp (λ i → P _ (conId (φ ∨ ~ i) (inc (ouc w i))
                                                             (inc (λ j → ouc w (i ∧ j)))))
                                (λ i → λ { (φ = i₁) → d}) (inc d))

  J-computation : J refl ≡ d
  J-computation = refl

\end{code}

Basic theory of Id, proved using J:

\begin{code}

module _ {U} {X : U ̇} where

  transport : ∀ {V} (A : X → V ̇) {x y : X}
            → x ≡ y → A x → A y
  transport A {x} {y} p a = J (λ y p → A y) a p

  _∙_ : ∀ {x y z : X} → x ≡ y → y ≡ z → x ≡ z
  _∙_ {x} {y} {z} p q = transport (λ - → x ≡ -) q p

  _⁻¹ : {x y : X} → x ≡ y → y ≡ x
  _⁻¹ {x} p = transport (λ - → - ≡ x) p refl

  ap : ∀ {V} {A : V ̇} (f : X → A) → ∀ {x y : X} → x ≡ y → f x ≡ f y
  ap f {x} p = transport (λ - → f x ≡ f -) p refl

  _≡⟨_⟩_ : (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ p ⟩ q = p ∙ q

  _∎ : (x : X) → x ≡ x
  _∎ _ = refl

  infix  1 _∎
  infixr 0 _≡⟨_⟩_

\end{code}

Conversion between Path and Id:

\begin{code}

module _ {U} {X : U ̇} where

  Path-to-Id : ∀ {x y : X} → x ≡ᶜ y → x ≡ y
  Path-to-Id {x} = Jᶜ (λ y _ → x ≡ y) refl

  Path-to-Id-refl : ∀ {x} → Path-to-Id (λ _ → x) ≡ᶜ refl
  Path-to-Id-refl {x} = Jᶜ-refl (λ y _ → x ≡ y) refl

  Id-to-Path : {x y : X} → x ≡ y → x ≡ᶜ y
  Id-to-Path {x} = J (λ y _ → x ≡ᶜ y) (λ _ → x)

  Id-to-Path-refl : ∀ {x : X} → Id-to-Path {x} refl ≡ᶜ reflᶜ
  Id-to-Path-refl {x} _ _ = x

  Path-to-Id-η : ∀ {x y : X} (p : x ≡ᶜ y) → Id-to-Path (Path-to-Id p) ≡ᶜ p
  Path-to-Id-η {x} = Jᶜ (λ y p → Path _ (Id-to-Path (Path-to-Id p)) p)
                        (λ i → Id-to-Path (Path-to-Id-refl i))

  Path-to-Id-ε : ∀ {x y : X} (p : x ≡ y) → Path-to-Id (Id-to-Path p) ≡ᶜ p
  Path-to-Id-ε {x} = J (λ b p → Path _ (Path-to-Id (Id-to-Path p)) p) Path-to-Id-refl

\end{code}

We get function extensionality by going back and forth between Path
and Id:

\begin{code}

funext : ∀ {U V} {A : U ̇} {B : A → V ̇} {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g
funext p = Path-to-Id (λ i x → Id-to-Path (p x) i)

\end{code}

Equivalences expressed using the identity types _≡_ rather than path
types _≡ᶜ_:

\begin{code}

fiber : ∀ {U V} {A : U ̇} {B : V ̇} (f : A → B) (y : B) → U ⊔ V ̇
fiber f y = Σ \x  → y ≡ f x

module _ {U} where

  is-contr : U ̇ → U ̇
  is-contr A = Σ \(x : A) → ∀ y → x ≡ y

  is-prop : U ̇ → U ̇
  is-prop A = (x y : A) → x ≡ y

  is-set : U ̇ → U ̇
  is-set A = (x y : A) → is-prop (x ≡ y)

is-equiv : ∀ {U V} {A : U ̇} {B : V ̇} (f : A → B) → U ⊔ V ̇
is-equiv f = ∀ y → is-contr (fiber f y)

infix 4 _≃_

_≃_ : ∀ {U V} (A : U ̇) (B : V ̇) → U ⊔ V ̇
A ≃ B = Σ \(f : A → B) → is-equiv f

Eq-to-fun : ∀ {U V} {A : U ̇} {B : V ̇} → A ≃ B → A → B
Eq-to-fun = pr₁

Eq-to-fun-is-equiv : ∀ {U V} {A : U ̇} {B : V ̇} (e : A ≃ B) → is-equiv (Eq-to-fun e)
Eq-to-fun-is-equiv = pr₂

Eq-to-fun-pointed-fibers : ∀ {U V} {A : U ̇} {B : V ̇} (e : A ≃ B) (y : B) → fiber (Eq-to-fun e) y
Eq-to-fun-pointed-fibers e y = pr₁ (pr₂ e y)

\end{code}

Functions for going between the various definitions. This could also
be achieved by making lines in the universe and transporting back and
forth along them.

\begin{code}

fiberᶜ-to-fiber : ∀ {U V} {A : U ̇} {B : V ̇} {f : A → B} {y : B}
                → fiberᶜ f y → fiber f y
fiberᶜ-to-fiber (x , p) = (x , Path-to-Id p)

fiber-to-fiberᶜ : ∀ {U V} {A : U ̇} {B : V ̇} {f : A → B} {y : B}
                → fiber f y → fiberᶜ f y
fiber-to-fiberᶜ (x , p) = (x , Id-to-Path p)

fiber-ε : ∀ {U V} {A : U ̇} {B : V ̇} {f : A → B} {y : B} (p : fiber f y)
        → fiberᶜ-to-fiber (fiber-to-fiberᶜ p) ≡ᶜ p
fiber-ε (x , p) = λ i → x , Path-to-Id-ε p i

fiber-η : ∀ {U V} {A : U ̇} {B : V ̇} {f : A → B} {y : B} (p : fiberᶜ f y)
        → fiber-to-fiberᶜ (fiberᶜ-to-fiber p) ≡ᶜ p
fiber-η (x , p) = λ i → x , Path-to-Id-η p i

is-contrᶜ-to-is-contr : ∀ {U} {A : U ̇} → is-contrᶜ A → is-contr A
is-contrᶜ-to-is-contr (ctr , p) = (ctr , λ y → Path-to-Id (p y))

is-contr-to-is-contrᶜ : ∀ {U} {A : U ̇} → is-contr A → is-contrᶜ A
is-contr-to-is-contrᶜ (ctr , p) = (ctr , λ y → Id-to-Path (p y))

is-propᶜ-to-is-prop : ∀ {U} {A : U ̇} → is-propᶜ A → is-prop A
is-propᶜ-to-is-prop h x y = Path-to-Id (h x y)

is-prop-to-is-propᶜ : ∀ {U} {A : U ̇} → is-prop A → is-propᶜ A
is-prop-to-is-propᶜ h x y i = Id-to-Path (h x y) i

\end{code}

Specialized helper lemmas for going back and forth between
is-contrᶜ and is-contr:

\begin{code}

retract-of-contrᶜ : ∀ {U} {A B : U ̇} (r : A → B) (s : B → A)
                  → (∀ y → r (s y) ≡ᶜ y) → is-contrᶜ A → is-contr B
retract-of-contrᶜ r s h (x , p) =
  (r x , λ y → Path-to-Id (λ i → hcomp (λ j → λ { (i = i₀) → r x
                                              ; (i = i₁) → h y j })
                                     (r (p (s y) i))))

retract-of-contr : ∀ {U} {A B : U ̇} (s : A → B) (r : B → A)
                 → (∀ x → r (s x) ≡ᶜ x) → is-contr B → is-contrᶜ A
retract-of-contr {U} {A} s r h (y , p) = (r y , λ x → Id-to-Path (rem x))
  where
   rem : (x : A) → r y ≡ x
   rem x =
     r y     ≡⟨ ap r (p (s x)) ⟩
     r (s x) ≡⟨ Path-to-Id (h x) ⟩
     x       ∎

\end{code}

This proof is essentially the one for proving that is-contrᶜ is a
proposition, but as we are working with Id we have to insert a lot of
conversion functions. It is still nice that is works like this though.

\begin{code}

is-propᶜ-is-contr : ∀ {U} {A : U ̇} → is-propᶜ (is-contr A)
is-propᶜ-is-contr (a0 , p0) (a1 , p1) j =
   (Id-to-Path (p0 a1) j ,
    hcomp (λ i → λ { (j = i₀) →  λ x → Path-to-Id-ε (p0 x) i
                   ; (j = i₁) →  λ x → Path-to-Id-ε (p1 x) i })
          (λ x → Path-to-Id (λ i → hcomp (λ k → λ { (i = i₀) → Id-to-Path (p0 a1) j
                                                ; (i = i₁) → Id-to-Path (p0 x) (j ∨ k)
                                                ; (j = i₀) → Id-to-Path (p0 x) (i ∧ k)
                                                ; (j = i₁) → Id-to-Path (p1 x) i })
                                       (Id-to-Path (p0 (Id-to-Path (p1 x) i)) j))))

is-propᶜ-is-equiv : ∀ {U} {A : U ̇} {B : U ̇} → {f : A → B} → is-propᶜ (is-equiv f)
is-propᶜ-is-equiv {U} {A} {B} {f} h1 h2 i y = is-propᶜ-is-contr {U} {fiber f y} (h1 y) (h2 y) i

Eqᶜ-to-Eq : ∀ {U V} {A : U ̇} {B : V ̇} → A ≃ᶜ B → A ≃ B
Eqᶜ-to-Eq (f , p) = (f , λ y → retract-of-contrᶜ fiberᶜ-to-fiber fiber-to-fiberᶜ fiber-ε (p y) )

Eq-to-Eqᶜ : ∀ {U V} {A : U ̇} {B : V ̇} → A ≃ B → A ≃ᶜ B
Eq-to-Eqᶜ (f , p) = (f , λ y → retract-of-contr fiberᶜ-to-fiber fiber-to-fiberᶜ fiber-η (p y))

Eq-η : ∀ {U} {A : U ̇} {B : U ̇} → (p : A ≃ B) → Eqᶜ-to-Eq (Eq-to-Eqᶜ p) ≡ᶜ p
Eq-η (f , p) i = (f , is-propᶜ-is-equiv (λ y → retract-of-contrᶜ fiberᶜ-to-fiber fiber-to-fiberᶜ fiber-ε
                                               (retract-of-contr fiberᶜ-to-fiber fiber-to-fiberᶜ fiber-η (p y))) p i)

\end{code}

We can finally prove a form of univalence for the identity type from
univalence for the path type:

\begin{code}

univalence : ∀ {U} (A : U ̇) → is-contr (Σ \(T : U ̇) → T ≃ A)
univalence A = retract-of-contrᶜ r s rs (univalenceᶜ A)
  where
   r : ∀ {U} {A : U ̇} → (Σ \(T : U ̇) → T ≃ᶜ A) → Σ \(T : U ̇) → T ≃ A
   r (x , p) = x , Eqᶜ-to-Eq p

   s : ∀ {U} {A : U ̇} → (Σ \(T : U ̇) → T ≃ A) → Σ \(T : U ̇) → T ≃ᶜ A
   s (x , p) = x , Eq-to-Eqᶜ p

   rs : ∀ {U} {A : U ̇} → (y : Σ \(T : U ̇) → T ≃ A) → r (s y) ≡ᶜ y
   rs (x , p) = λ i → x , Eq-η p i

\end{code}

Propositional truncation as a higher inductive type:

\begin{code}

data ∥_∥ {U} (A : U ̇) : U ̇ where
  ∣_∣ : A → ∥ A ∥
  ∥∥-is-propᶜ : ∀ (x y : ∥ A ∥) → x ≡ᶜ y

∥∥-recursionᶜ : ∀ {U} {A : U ̇} {P : U ̇} → is-propᶜ P → (A → P) → ∥ A ∥ → P
∥∥-recursionᶜ _ f ∣ x ∣ = f x
∥∥-recursionᶜ h f (∥∥-is-propᶜ x y i) = h (∥∥-recursionᶜ h f x) (∥∥-recursionᶜ h f y) i

∥∥-inductionᶜ : ∀ {U} {A : U ̇} {P : ∥ A ∥ → U ̇} → ((a : ∥ A ∥) → is-propᶜ (P a))
             → ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
∥∥-inductionᶜ {P = P} h f a = ∥∥-recursionᶜ (h a) (λ x → transp (λ i → P (∥∥-is-propᶜ ∣ x ∣ a i)) i₀ (f x)) a

\end{code}

This also gives the truncation with respect to the identity type:

\begin{code}

∥∥-is-prop : ∀ {U} {A : U ̇} → is-prop ∥ A ∥
∥∥-is-prop x y = Path-to-Id (∥∥-is-propᶜ x y)

∥∥-recursion : ∀ {U} {A : U ̇} {P : U ̇} → is-prop P → (A → P) → ∥ A ∥ → P
∥∥-recursion h f x = ∥∥-recursionᶜ (is-prop-to-is-propᶜ h) f x

∥∥-induction : ∀ {U} {A : U ̇} {P : ∥ A ∥ → U ̇} → ((a : ∥ A ∥) → is-prop (P a))
             → ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
∥∥-induction h f x = ∥∥-inductionᶜ (λ a → is-prop-to-is-propᶜ (h a)) f x

\end{code}

This is from https://github.com/Saizan/cubical-demo/blob/master/src/Cubical/PushOut.agda

\begin{code}

postulate
  pushout   : ∀ {U} {A B C : U ̇} (f : C → A) (g : C → B) → U ̇
  pinl      : ∀ {U} {A B C : U ̇} {f : C → A} {g : C → B} → A → pushout f g
  pinr      : ∀ {U} {A B C : U ̇} {f : C → A} {g : C → B} → B → pushout f g
  pushᶜ     : ∀ {U} {A B C : U ̇} {f : C → A} {g : C → B}
            → (c : C) → pinl {U} {A} {B} {C} {f} {g} (f c) ≡ᶜ pinr (g c)

{-# BUILTIN PUSHOUT pushout #-}
{-# BUILTIN PUSHOUTINL pinl #-}
{-# BUILTIN PUSHOUTINR pinr #-}
{-# BUILTIN PUSHOUTPUSH pushᶜ #-}

primitive
  primPushOutHComp : ∀ {U} {A B C : U ̇} {f : C → A} {g : C → B} (φ : I) (u : (i : I) → Partial φ (pushout f g))
                   → Sub {U} (pushout f g) φ (u i₀) → pushout f g
  primPushOutForward : ∀ {U : I → Universe} {A B C : (i : I) → (U i)̇}
                         {f : ∀ i → C i → A i} {g : ∀ i → C i → B i}
                     → (r : I) (u : pushout (f r) (g r)) → pushout (f i₁) (g i₁)
  primPushOutElim : ∀ {U V} {A B C : U ̇} {f : C → A} {g : C → B} (M : pushout f g → V ̇)
                  → (il : ∀ a → M (pinl a)) (ir : ∀ b → M (pinr b))
                  → (p : ∀ c → PathP (\ i → M (pushᶜ c i)) (il (f c)) (ir (g c)))
                  → ∀ x → M x

\end{code}

Pushout with identity type:

\begin{code}

push : ∀ {U} {A B C : U ̇} {f : C → A} {g : C → B}
         → (c : C) → pinl {U} {A} {B} {C} {f} {g} (f c) ≡ pinr (g c)
push c = Path-to-Id (pushᶜ c)

\end{code}

TODO.     pushout-induction. Then expose the pushout machinery in Cubical-HoTT-UF.
QUESTION. Couldn't we instead define a higher-inductive type with 'data'?
