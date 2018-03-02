Martin Escardo, 28 February 2018.

    ---------------------------------------------------
    A self-contained, brief and complete formulation of
    Voevodsky's Univalence Axiom
    ---------------------------------------------------

1. Introduction
   ------------
   
In introductions to the subject for a general audience of
mathematicians or logicians, the univalence axiom is typically
explained by handwaving. This gives rise to several misconceptions,
which cannot be properly addressed in the absence of a precise
definition.

Here we give a complete formulation of the univalence axiom from
scratch,

 * first written informally but rigorously in mathematical English
   prose, and
 
 * then formally in Agda notation for Martin-Löf type theory.

(Search for "UnivalenceFromScratch" to jump to the formal version.)

The univalence axiom is not true or false in, say, ZFC or the internal
language of an elementary topos. It cannot even be formulated. As the
saying goes, it is not even wrong.

This is because

   univalence is a property of the *identity type*
   of a universe of types.

Nothing like Martin-Löf's identity type occurs in ZFC or topos logic,
although universes have of course been considered in both.

* Please contribute
  -----------------

The HoTT/UF community, and more generally the mathematical and logical
communities, are invited to create issues or propose pull requests to
improve these notes. However, the underlying idea of these notes is
that they should be as concise as possible (and not more). They are
not meant to be an Encyclopedia of Univalence (you may create a fork
for that).

The source code for this file is available at
https://github.com/martinescardo/TypeTopology/tree/master/source

2. Informal, rigorous construction of the univalence type
   ------------------------------------------------------

Univalence is a type, and the univalence axiom says that this type has
some inhabitant. It takes a number of steps to construct this type, in
addition to subtle decisions (e.g. to work with equivalences rather
than isomorphisms, as discussed below).

We first need to briefly introduce Martin-Löf type theory (MLTT). We
will not give a course in MLTT. Instead, we will mention which
constructs of MLTT are needed to give a complete definition of the
univalence type. This will be enough to illustrate the important fact
that in order to understand univalence we first need to understand
Martin-Löf type theory well.

* Types and their elements
  ------------------------

Types are the analogues of sets in ZFC and of objects in topos theory.

Types are constructed together with their elements, and not by
collecting some previously existing elements. When a type is
constructed, we get freshly new elements for it. We write

    x:X

to declare that the element x has type X. This is not something that
is true or false (like a membership relation x ∈ X in ZFC). For
example, if ℕ is the type of natural numbers, we may write

    17 : ℕ,
   (13,17) : ℕ × ℕ.

However, the following statements are nonsensical and syntactically
incorrect, rather than false:

    17 : ℕ × ℕ (nonsense),
   (13,17) : ℕ (nonsense).

* Products and sums of type families
  ----------------------------------

Given a family of types A(x) indexed by elements x of a type X, we can
form its product and sum:

    Π(x:X), A(x),
    Σ(x:X), A(x),

which we also write Π A and Σ A. An element of the type Π A is a
function that maps elements x:X to elements of A(x). An element of the
type Σ A is a pair (x,a) with x:X and a:A(x).

(We adopt the convention that Π and Σ scope over the whole rest of the
expression.)

We also have the type X→Y of functions from X to Y, which is the
particular case of Π with the constant family A(x):=Y.

We also have the cartesian product X×Y, whose elements are pairs. This
is the particular case of Σ, again with A(x):=Y. 

We also have the disjoint sum X+Y, the empty type 𝟘 and the
one-element type 𝟙, which will not be needed here.


* Quantifiers and logic
  ---------------------

There is no underlying logic in MLTT. Propositions are types, and Π
and Σ play the role of universal and existential quantifiers, via the
so-called Curry-Howard interpretation of logic. As for the
connectives, implication is given by the function-space construction
→, conjunction by the binary cartesian product ×, and disjunction by
the binary disjoint sum +.

The elements of a type correspond to proofs, and instead of saying
that a type A has a given element, it is common practice to say that A
holds, when the type A is understood as a proposition.

* The identity type
  -----------------

Given a type X and elements x,y:X, we have the identity type

    Id_X(x,y),

with the subscript X often elided. The idea is that Id(x,y) collects
the ways in which x and y are identified.

We have a function

    refl : Π(x:X), Id(x,x),

which identifies any element with itself. Without univalence, refl is
the only given way to construct elements of the identity type.

In addition to refl, we stipulate that for any given type family A(x,y,p)
indexed by elements x,y:X and p:Id(x,y) and any given function

    f : Π(x:X), A(x,x,refl(x)),

we have a function 

    J(A,f) : Π(x,y:X), Π(p:Id(x,y)), A(x,y,p),

such that

    J(A,f)(x,x,refl(x)) = f(x).

We will see examples of uses of J in the steps leading to the
construction of the univalence type.

With these requirements, the exact nature of the type Id(x,y) is
fairly under-specified. It is consistent that it is always a
subsingleton, which is known as the K axiom for the type X, in the
following sense:

   K(X) := Π(x,y:X), Π(p,q:Id(x,y)), Id(p,q).

The second identity type is that of the type Id(x,y). This is possible
because any type has an identity type, including the identity type
itself, and the identity type of the identity type, and so on, which
is the basis for univalent mathematics (but this is not discussed
here, as it is not needed in order to construct the univalence type).

On the other hand, the univalence axiom provides a means of
constructing elements other than refl(x), at least for some types.  It
will be the case that for some other types X, even in the presence of
univalence, K(X) "holds", meaning that we can construct an element of
it. Such types are called sets. The K axiom says that all types are
sets. The univalence axiom implies that some types are not sets (then
they will instead be 1-groupoids, or 2-groupoids, ..., or even
∞-groupoids, but we will not address this important aspect of
univalent mathematics here).

* Universes
  ---------

Our final ingredient is a "large" type of "small" types, called a
universe. It is common to assume a tower of universes U₀, U₁, U₂,
... of "larger and larger" types, with

   U₀ : U₁,
   U₁ : U₂,
   U₂ : U₃,
   ⋮

(It is sometimes assumed that these universes are cumulative in a
certain sense, but we will not need to assume (or reject) this.)

When we have universes, a type family A indexed by a type X:U may be
considered to be a function A:X→V for some universe V.

Universes are also used to construct types of mathematical structures,
such as the type of groups, whose definition starts like this:

 Grp := Σ(G:U), isSet(G) × Σ(e:G), Σ(_∙_:G×G→G), (Π(x:G), Id(e∙x,x)) × ⋯ 

Here isSet(G):=Π(x,y:G),Π(p,q:Id(x,y)),Id(p,q), as above. With
univalence, Grp itself will not be a set, but a 1-groupoid instead,
namely a type whose identity types are all sets. Moreover, if U
satisfies the univalence axiom, then for A,B:Grp, the identity type
Id(A,B) can be shown to be in bijection with the group isomorphisms of
A and B.

* Univalence
  ----------

Univalence is a property of the identity type Id_U of a universe U. It
takes a number of steps to define the univalence type.
  
We say that a type X is a singleton if we have an element c:X with
Id(c,x) for all x:X. In Curry-Howard logic, this is

    isSingleton(X) := Σ(c:X), Π(x:X), Id(c,x).

(Alternative terminology not used here: X is contractible.)

For a function f:X→Y and an element y:Y, its fiber is the type of
points x:X that are mapped to (a point identified with) y:

    f⁻¹(y) := Σ(x:X),Id(f(x),y).

The function f is called an equivalence if its is fibers are all
singletons:

    isEquiv(f) := Π(y:Y), isSingleton(f⁻¹(y)).

The type of equivalences from X:U to Y:U is

    Eq(X,Y) := Σ(f:X→Y), isEquiv(f).

Given x:X, we have the singleton type consisting of the elements y:Y
identified with x:

   singletonType(x) := Σ(y:X), Id(y,x).

We also have the element singleton(x) of this type:

   singleton(x) := (x, refl(x)).

We now need to *prove* that singleton types are singletons:

   Π(x:X), isSingleton(singletonType(x)).

In order to do that, we use J with the type family

  A(y,x,p) := Id(singleton(x), (y,p)),

and the function f : Π(x:X), A(x,x,refl(x)) defined by

  f(x) := refl(singleton(x)).

With this we get a function

  φ : Π(y,x:X), Π(p:Id(y,x)), Id(singleton(x), (y,p))
  φ := J(A,f).

(Notice the reversal of y and x.)

With this, we can in turn define a function

  g : Π(x:X), Π(σ:singletonType(x)), Id(singleton(x), σ)
  g(x,(y,p)) := φ(y,x,p).

Finally, using g we get our desired result, that singleton types are
singletons:

  h : Π(x:X), Σ(c:singletonType(x)), Π(σ:singletonType(x)), Id(c,σ)
  h(x) := (singleton(x) , g(x)).

Now, for any type X, its identity function Id_X, defined by

  id(x) := x,

is an equivalence. This is because the fiber id⁻¹(x) is simply the
singleton type defined above, which we proved to be a singleton. We
need to name this function, because it is needed in the formulation of
the univalence of U:

  idIsEquiv : Π(X:U), isEquiv(id_X).

Now we use J a second time to define a function

  IdToEq : Π(X,Y:U), Id(X,Y) → Eq(X,Y).

For X,Y:U and p:Id(X,Y), we set

  A(X,Y,p) := Eq(X,Y)
  
and

  f(X) := (id_X , idIsEquiv(X)),

and

  IdToEq := J(A,f).

Finally, we say that the universe U is univalent if the map
IdToEq(X,Y) is itself an equivalence:

  isUnivalent(U) := Π(X,Y:U), isEquiv(IdToEq(X,Y)).

The type isUnivalent(U) may or may not have an inhabitant. The
univalence axiom says that it does. Without the univalence axiom (or
some other axiom such as the assertion that K(U) has an inhabitant),
the inhabitedness of the type isUnivalent(U) is undecided.

* Notes
  -----

 0. The minimal Martin-Löf type theory needed to formulate univalence
    has

      Π, Σ, Id, U.

    One universe suffices (the one which univalence talks about).
  
 1. It can be shown, by a very complicated and interesting argument,
    that

     Π(u,v: isUnivalent(U)), Id(u,v).

    This says that univalence is a subsingleton type (any two of its
    elements are identified). In the first step we use u (or v) to get
    function extensionality (any two pointwise identified functions
    are identified), which is *not* provable in MLTT, but is provable
    from the assumption that U is univalent. Then, using this, one
    shows that being an equivalence is a subsingleton type. Finally,
    again using function extensionality, we get that a product of
    subsingletons is a subsingleton. But then Id(u,v) holds, which is
    what we wanted to show. But this of course omits the proof that
    univalence implies function extensionality (originally due to
    Voevodsky), which is fairly elaborate.

 2. For a function f:X→Y, consider the type

     Iso(f) := Σ(g:Y→X), (Π(x:X), Id(g(f(x)), x)) × (Π(y:Y), Id(f(g(y)), y)).

    We have functions r:Iso(f)→isEquiv(f) and
    s:isEquiv(f)→Iso(f). However, the type isEquiv(f) is always a
    subsingleton, assuming function extensionality, whereas the type
    Iso(f) need not be. What we do have is that the function r is a
    retraction with section s.

    Moreover, the univalence type formulated as above, but using
    Iso(f) rather than isEquiv(f) is provably empty. So, to have a
    consistent axiom, it is crucial to use the type isEquiv(f). It was
    Voevodsky's insight that not only a subsingleton version of Iso(f)
    is needed, but also how to construct it. The construction of
    isEquiv(f) is very simple and elegant, but very difficult to
    arrive at. It is motivated by homotopical models of the
    theory. But the univalence axiom can be understood without
    reference to homotopy theory.

 3. The fact (again proved by Voevodsky, with the model of simplicial
    sets) that MLTT is consistent with the univalence axiom shows
    that, before we postulate univalence, MLTT is "proto-univalent" in
    the sense that it cannot distinguish concrete isomorphic types
    such as X:=ℕ and Y:=ℕ×ℕ by a property P:U→U such that P(X) holds
    but P(Y) doesn't.  This is because, being isomorphic, X and Y are
    equivalent. But then univalence implies Id(X,Y), which in turn
    implies P(X)⇔P(Y) using J.  Because univalence is consistent, it
    follows that for any given concrete P:U→U, it is impossible to
    prove that P(X) holds but P(Y) doesn't.

    So MLTT is invariant under isomorphism in this doubly negative,
    meta-mathematical sense. With univalence, it becomes invariant
    under isomorphism in a positive, mathematical sense.

 4. Thus, we see that the formulation of univalence is far from
    direct, and has much more to it than the (in our opinion,
    misleading) slogan "isomorphic types are equal".

    What the consistency of the univalence axiom says is that one
    possible understanding of the identity type Id(X,Y) for X,Y:U is
    as precisely the type Eq(X,Y) of equivalences, in the sense of
    being in one-to-one correspondence with it. Without univalence,
    the nature of the identity type of the universe in MLTT is fairly
    under-specified. It is a remarkable property of MLTT that it is
    consistent with this understanding of the identity type of the
    universe, discovered by Vladimir Voevodsky (and foreseen by Martin
    Hofmann and Thomas Streicher (1996) in a particular case).

3. Formal construction of the univalence type in Agda
   --------------------------------------------------

We now give a symbolic rendering of the above construction of the
univalence type, in Agda notation. (Agda documentation is at
http://wiki.portal.chalmers.se/agda/pmwiki.php).

The fragment of Agda used here amounts to the subset of MLTT with
Π,Σ,Id and a tower of universes as discussed above. By default, Agda
has the K axiom, which, as discussed above, contradicts univalence,
and hence we disable it. Inductive definitions in Agda are given with
the keyword "data". Unlike Coq, Agda doesn't derive the induction
principles, and one has to do this manually, as we do in the
definition of J. Finally, notice that in Agda one constructs things by
first specifying their types and then giving a definition with the
equality sign.

The letters U, V, W range over universes, the successor of a universe
U is written U ′, and the first universe after the universes U and V
is written U ⊔ V, to avoid subscripts.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UnivalenceFromScratch where

open import Agda.Primitive using (_⊔_) renaming (lzero to U₀ ; lsuc to _′ ; Level to Universe)

_̇ : (U : Universe) → _
U ̇ = Set U -- This should be the only use of the Agda keyword 'Set' in this development.

infix  0 _̇

data Σ {U V : Universe} {X : U ̇} (Y : X → V ̇) : U ⊔ V ̇ where
  _,_ : (x : X) (y : Y x) → Σ Y

data Id {U : Universe} {X : U ̇} : X → X → U ̇ where
  refl : (x : X) → Id x x

J : {U V : Universe} {X : U ̇}
  → (A : (x y : X) → Id x y → V ̇)
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : Id x y) → A x y p
J A f x x (refl x) = f x

isSingleton : {U : Universe} → U ̇ → U ̇
isSingleton X = Σ \(c : X) → (x : X) → Id c x

fiber : {U V : Universe} {X : U ̇} {Y : V ̇} → (X → Y) → Y → U ⊔ V ̇
fiber f y = Σ \x → Id (f x) y

isEquiv : {U V : Universe} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
isEquiv f = (y : _) → isSingleton(fiber f y)

Eq : {U V : Universe} → U ̇ → V ̇ → U ⊔ V ̇
Eq X Y = Σ \(f : X → Y) → isEquiv f

singletonType : {U : Universe} {X : U ̇} → X → U ̇
singletonType x = Σ \y → Id y x

singleton : {U : Universe} {X : U ̇} (x : X) → singletonType x
singleton x = (x , refl x)

singletonTypesAreSingletons : {U : Universe} {X : U ̇} (x : X) → isSingleton(singletonType x)
singletonTypesAreSingletons {U} {X} = h
 where
  A : (y x : X) → Id y x → U ̇
  A y x p = Id (singleton x) (y , p)
  f : (x : X) → A x x (refl x)
  f x = refl (singleton x)
  φ : (y x : X) (p : Id y x) → Id (singleton x) (y , p)
  φ = J A f
  g : (x : X) (σ : singletonType x) → Id (singleton x) σ
  g x (y , p) = φ y x p
  h : (x : X) → Σ \(c : singletonType x) → (σ : singletonType x) → Id c σ
  h x = (singleton x , g x)

id : {U : Universe} (X : U ̇) → X → X
id X x = x

idIsEquiv : {U : Universe} (X : U ̇) → isEquiv(id X)
idIsEquiv X = g
 where
  g : (x : X) → isSingleton (fiber (id X) x)
  g = singletonTypesAreSingletons

IdToEq : {U : Universe} (X Y : U ̇) → Id X Y → Eq X Y
IdToEq {U} = J A f
 where
  A : (X Y : U ̇) → Id X Y → U ̇
  A X Y p = Eq X Y
  f : (X : U ̇) → A X X (refl X)
  f X = (id X , idIsEquiv X)

isUnivalent : (U : Universe) → U ′ ̇
isUnivalent U = (X Y : U ̇) → isEquiv(IdToEq X Y)

\end{code}

Thus, we see that even in its concise symbolic form, the formulation
of univalence is far from direct.

Using projections pr₁ and pr₂ rather than pattern matching on Σ types,
Agda calculates the following normal form for the term isUnivalent:

λ U → (X Y : Set U) (y : Σ (λ f → (y₁ : Y) → Σ (λ c →
(x : Σ (λ x₁ → Id (f x₁) y₁)) → Id c x))) →
Σ (λ c → (x : Σ (λ x₁ → Id (J (λ X₁ Y₁ p → Σ (λ f →
(y₁ : Y₁) → Σ (λ c₁ → (x₂ : Σ (λ x₃ → Id (f x₃) y₁)) → Id c₁ x₂)))
(λ X₁ → (λ x₂ → x₂) , (λ x₂ → (x₂ , refl x₂) , (λ yp → J (λ y₁ x₃ p →
Id (x₃ , refl x₃) (y₁ , p)) (λ x₃ → refl (x₃ , refl x₃))
(pr₁ yp) x₂ (pr₂ yp)))) X Y x₁) y)) → Id c x)

This is with lots of subterms elided. With all of them explicitly
given, the normal form of isUnivalent is

λ U → (X Y : U ̇) (y : Σ {U} {U} {X → Y} (λ f → (y₁ : Y) → Σ {U} {U}
{Σ {U} {U} {X} (λ x → Id {U} {Y} (f x) y₁)} (λ c → (x : Σ {U} {U} {X}
(λ x₁ → Id {U} {Y} (f x₁) y₁)) → Id {U} {Σ {U} {U} {X} (λ x₁ → Id {U} {Y}
(f x₁) y₁)} c x))) → Σ {U ′} {U ′} {Σ {U ′} {U} {Id {U ′} {U ̇} X Y}
(λ x → Id {U} {Σ {U} {U} {X → Y} (λ f → (y₁ : Y) → Σ {U} {U}
{Σ {U} {U} {X} (λ x₁ → Id {U} {Y} (f x₁) y₁)} (λ c → (x₁ : Σ {U} {U} {X}
(λ x₂ → Id {U} {Y} (f x₂) y₁)) → Id {U} {Σ {U} {U} {X} (λ x₂ → Id {U} {Y}
(f x₂) y₁)} c x₁))} (J {U ′} {U} {U ̇} (λ X₁ Y₁ p → Σ {U} {U} {X₁ → Y₁}
(λ f → (y₁ : Y₁) → Σ {U} {U} {Σ {U} {U} {X₁} (λ x₁ → Id {U} {Y₁} (f x₁) y₁)}
(λ c → (x₁ : Σ {U} {U} {X₁} (λ x₂ → Id {U} {Y₁} (f x₂) y₁)) → Id {U}
{Σ {U} {U} {X₁} (λ x₂ → Id {U} {Y₁} (f x₂) y₁)} c x₁))) (λ X₁ → (λ x₁ → x₁)
, (λ x₁ → (x₁ , refl x₁) , (λ yp → J {U} {U} {X₁} (λ y₁ x₂ p → Id {U}
{Σ {U} {U} {X₁} (λ y₂ → Id {U} {X₁} y₂ x₂)} (x₂ , refl x₂) (y₁ , p))
(λ x₂ → refl (x₂ , refl x₂)) (pr₁ yp) x₁ (pr₂ yp)))) X Y x) y)} (λ c →
(x : Σ {U ′} {U} {Id {U ′} {U ̇} X Y} (λ x₁ → Id {U} {Σ {U} {U} {X → Y}
(λ f → (y₁ : Y) → Σ {U} {U} {Σ {U} {U} {X} (λ x₂ → Id {U} {Y} (f x₂) y₁)}
(λ c₁ → (x₂ : Σ {U} {U} {X} (λ x₃ → Id {U} {Y} (f x₃) y₁)) → Id {U}
{Σ {U} {U} {X} (λ x₃ → Id {U} {Y} (f x₃) y₁)} c₁ x₂))} (J {U ′} {U} {U ̇}
(λ X₁ Y₁ p → Σ {U} {U} {X₁ → Y₁} (λ f → (y₁ : Y₁) → Σ {U} {U} {Σ {U} {U}
{X₁} (λ x₂ → Id {U} {Y₁} (f x₂) y₁)} (λ c₁ → (x₂ : Σ {U} {U} {X₁} (λ x₃ →
Id {U} {Y₁} (f x₃) y₁)) → Id {U} {Σ {U} {U} {X₁} (λ x₃ → Id {U} {Y₁} (f x₃)
y₁)} c₁ x₂))) (λ X₁ → (λ x₂ → x₂) , (λ x₂ → (x₂ , refl x₂) , (λ yp → J {U}
{U} {X₁} (λ y₁ x₃ p → Id {U} {Σ {U} {U} {X₁} (λ y₂ → Id {U} {X₁} y₂ x₃)}
(x₃ , refl x₃) (y₁ , p)) (λ x₃ → refl (x₃ , refl x₃)) (pr₁ yp) x₂ (pr₂ yp))))
X Y x₁) y)) → Id {U ′} {Σ {U ′} {U} {Id {U ′} {U ̇} X Y} (λ x₁ → Id {U}
{Σ {U} {U} {X → Y} (λ f → (y₁ : Y) → Σ {U} {U} {Σ {U} {U} {X} (λ x₂ →
Id {U} {Y} (f x₂) y₁)} (λ c₁ → (x₂ : Σ {U} {U} {X} (λ x₃ → Id {U} {Y} (f x₃)
y₁)) → Id {U} {Σ {U} {U} {X} (λ x₃ → Id {U} {Y} (f x₃) y₁)} c₁ x₂))}
(J {U ′} {U} {U ̇} (λ X₁ Y₁ p → Σ {U} {U} {X₁ → Y₁} (λ f → (y₁ : Y₁) →
Σ {U} {U} {Σ {U} {U} {X₁} (λ x₂ → Id {U} {Y₁} (f x₂) y₁)} (λ c₁ →
(x₂ : Σ {U} {U} {X₁} (λ x₃ → Id {U} {Y₁} (f x₃) y₁)) → Id {U} {Σ {U} {U} {X₁}
(λ x₃ → Id {U} {Y₁} (f x₃) y₁)} c₁ x₂))) (λ X₁ → (λ x₂ → x₂) , (λ x₂ → (x₂ ,
refl x₂) , (λ yp → J {U} {U} {X₁} (λ y₁ x₃ p → Id {U} {Σ {U} {U} {X₁}
(λ y₂ → Id {U} {X₁} y₂ x₃)} (x₃ , refl x₃) (y₁ , p)) (λ x₃ → refl (x₃ ,
refl x₃)) (pr₁ yp) x₂ (pr₂ yp)))) X Y x₁) y)} c x) 
