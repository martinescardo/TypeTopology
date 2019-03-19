---
layout: default
title : Introduction to Univalent Foundations of Mathematics with Agda
date : 2019-03-04
---
## <a name="lecturenotes">Introduction to Univalent Foundations of Mathematics with Agda</a>

[<sub>Table of contents ⇑</sub>](toc.html#contents)
## <a name="mlttinagda"></a> MLTT in Agda

### <a name="whatisagda"></a> What is Agda?

There are [two views](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html):

 1. Agda is a dependently-typed functional programming language.

 2. Agda is a language for defining mathematical notions (e.g. group
    or topological space), formulating constructions to be performed
    (e.g. a type of real numbers, a group structure on the integers, a
    topology on the reals), formulating theorems (e.g. a certain
    construction is indeed a group structure, there are infinitely
    many primes), and proving theorems (e.g. the infinitude of the
    collection of primes with Euclid's argument).

This doesn't mean that Agda has two sets of features, one for (1) and
the other for (2). The same set of features account simultaneously for
(1) and (2). Programs are mathematical constructions that happen not
to use non-constructive principles such as excluded middle.

In these notes we study a minimal univalent type theory and do
mathematics with it using a minimal subset of the computer language Agda
as a vehicle.

Agda allows one to construct proofs interactively, but we will not
discuss how to do this in these notes. Agda is not an automatic
theorem prover. We have to come up with our own proofs, which Agda
checks for correctness. We do get some form of interactive help to
input our proofs and render them as formal objects.

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="spartanmltt"></a> A spartan Martin-Löf type theory (MLTT)

Before embarking into a full definition of our Martin-Löf type
theory in Agda, we summarize the particular Martin-Löf type
theory that we will consider, by naming the concepts that we will
include. We will have:

   * An empty type [`𝟘`](MLTT-Agda.html#emptytype).

   * A one-element type [`𝟙`](MLTT-Agda.html#onepointtype).

   * A type of [`ℕ`](MLTT-Agda.html#naturalnumbers) natural numbers.

   * Type formers [`+`](MLTT-Agda.html#binarysum) (binary sum),
     [`Π`](MLTT-Agda.html#pitypes) (product),
     [`Σ`](MLTT-Agda.html#sigmatypes) (sum),
     [`Id`](MLTT-Agda.html#identitytype) (identity type).

   * [Universes](MLTT-Agda.html#universes) (types of types), ranged
     over by `𝓤,𝓥,𝓦`.

This is enough to do number theory, analysis, group theory, topology, category theory and more.

spartan
  /ˈspɑːt(ə)n/
  adjective:

      showing or characterized by austerity or a lack of comfort or
      luxury.

We will also be rather spartan with the subset of Agda that we choose
to discuss. Many things we do here can be written in more concise ways
using more advanced features. Here we introduce a minimal
subset of Agda where everything in our spartan `MLTT` can be expressed.

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="gettingstartedagda"></a> Getting started with Agda

We don't use any Agda library. For pedagogical purposes, we start from
scratch, and here is our first line of code:

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module MLTT-Agda where
\end{code}

 * The option `--without-K` disables [Streicher's `K` axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29), which we don't
   want for univalent mathematics.

 * The option `--exact-split` makes Agda to only accept definitions
   with the equality sign "`=`" that [behave like so-called judgmental
   equalities](https://agda.readthedocs.io/en/latest/language/function-definitions.html#case-trees).

 * The option `--safe` disables features [that may make Agda
   inconsistent](https://agda.readthedocs.io/en/latest/language/safe-agda.html#safe-agda),
   such as `--type-in-type`, postulates and more.

 * Every Agda file is a
  [module](https://agda.readthedocs.io/en/latest/language/module-system.html).
  These lecture notes are a set of Agda files, which is converted to
  html by Agda after it successfully checks the mathematical
  development for correctness.

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="universes"></a> Universes

A universe `𝓤` is a type of types.

 * One use of universes is to define families of types indexed by a
   type `X` as functions `X → 𝓤`.

 * Such a function is sometimes seen as a property of elements of `X`.

 * Another use of universes, as we shall see, is to define types of
   mathematical structures, such as
   [monoids](HoTT-UF-Agda.html#magmasandmonoids), groups, topological
   spaces, categories etc.

Sometimes we need more than one universe. For example, the type of
groups in a universe lives in a bigger universe, and given a category
in one universe, its presheaf category also lives in a larger universe.

We will work with a tower of type universes

   > `𝓤₀, 𝓤₁, 𝓤₂, 𝓤₃, ...`

These are actually universe names (also called levels). We reference
the universes themselves by a deliberately almost-invisible
superscript dot. For example, we will have

   > `𝟙 : 𝓤₀ ̇`

where `𝟙` is the one-point type to be defined shortly. We will sometimes
omit this superscript in our discussions, but are forced to write it
in Agda code. We have that the universe `𝓤₀` is a type in the universe
`𝓤₁`, which is a type in the universe 𝓤₂ and so on.

   > `𝓤₀ ̇` &nbsp;&nbsp;    `: 𝓤₁ ̇`

   > `𝓤₁ ̇` &nbsp;&nbsp;    `: 𝓤₂ ̇`

   > `𝓤₂ ̇` &nbsp;&nbsp;    `: 𝓤₃ ̇`

   > `       ⋮ `

The assumption that
`𝓤₀ : 𝓤₀` or that any universe is in itself or a smaller universe [gives
rise to a contradiction](https://link.springer.com/article/10.1007/BF01995104), similar to [Russell's Paradox](https://plato.stanford.edu/entries/russell-paradox/).

The least upper bound of two
universes `𝓤` and `𝓥` is written

   > `𝓤 ⊔ 𝓥`.

For example, if `𝓤` is `𝓤₀` and `𝓥` is `𝓤₁`, then `𝓤 ⊔ 𝓥` is `𝓤₁`.

We now bring our notation for universes by importing our Agda file
`Universes`. The Agda keyword
[`open`](https://agda.readthedocs.io/en/latest/language/module-system.html)
asks to make all definitions in the file `Universe` visible in our
file here. The Agda code in these notes has syntax highlighting and
html links, so that we can navigate to other modules, such as
`Universe` or to definitions in this file.

\begin{code}
open import Universes
\end{code}

We will refer to universes by letters `𝓤,𝓥,𝓦,𝓣`:

\begin{code}
variable
 𝓤 𝓥 𝓦 𝓣 : Universe
\end{code}

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="onepointtype"></a> The one-element type `𝟙`

We place it in the first universe, and we name its unique element
"`⋆`". We use the `data` declaration in Agda to introduce it:

\begin{code}
data 𝟙 : 𝓤₀ ̇  where
 ⋆ : 𝟙
\end{code}

It is important that the point `⋆` lives in the type `𝟙` and in no other
type. There isn't dual citizenship in our type theory. When we create
a type, we also create freshly new elements for it, in this case
"`⋆`". (However, Agda has a limited form of overloading, which allows
us to sometimes use the same name for different things.)

Next we want to give a mechanism to prove that all points of the
type `𝟙` satify a given property `A`.

  * The property is a function `A : 𝟙 → 𝓤` for some universe `𝓤`.

  * The type `A(x)`, which we will write simply `A x`, doesn't need to
    be a [truth value](HoTT-UF-Agda.html#subsingletonsandsets).  It can be
    any type. We will meet examples shortly.

  * Mathematical statements are types, such as

    > `Π (A : 𝟙 → 𝓤), A ⋆ → Π (x : 𝟙), A x`.

  * We read this in natural language as "for any given property `A` of
    elements of the type `𝟙`, if we can show that `A ⋆` holds, then it
    follows that `A x` holds for all `x : 𝟙`".


  * In Agda above `Π`-type is written as

    > `(A : 𝟙 → 𝓤 ̇ ) → A * → (x : 𝟙) → A x`.

    This is the type of functions with three arguments `A : 𝟙 → 𝓤 ̇` &nbsp;
    and `a : A ⋆` and `x : 𝟙`, with value in the type `A x`.

  * A proof of a mathematical statement rendered as a type is a
    construction of an element of the type.  In our example, we have
    to construct a function, which we will name `𝟙-induction`.

We do this as follows in Agda, where we first declare the type of the
function `𝟙-induction` with "`:`" and then define the function by an
equation:

\begin{code}
𝟙-induction : (A : 𝟙 → 𝓤 ̇ )
            → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a
\end{code}

Notice that we supply `A` and `a` as arbitrary arguments, but instead of
an arbitrary `x : X` we have written "`⋆`". Agda accepts this because it
knows from the definition of `𝟙` that "`⋆`" is the only element of the
type `𝟙`. This mechanism is called *pattern matching*.

A particular case of `𝟙-induction` occurs when the family `A` is constant
with value `B`, which can be written as variously as `A = λ (x : 𝟙) → B`,
or `A = λ x → B` if we want Agda to figure out the type of `x` by itself,
or `A = λ _ → B` if we don't want to name the argument of `A` because it
is not used. In usual mathematical practice, such a [lambda expression](https://plato.stanford.edu/entries/lambda-calculus/) is [often
written](https://en.wikipedia.org/wiki/Function_(mathematics)#Arrow_notation) `x ↦ B` (`x` is mapped to `B`) and so `A = (x ↦ B)`.
Given a type `B` and a point `b : B`, we construct the function `𝟙 → B`
that maps any given `x : 𝟙` to `b`.

\begin{code}
𝟙-induction' : (B : 𝓤 ̇ ) → B → (𝟙 → B)
𝟙-induction' B b x = 𝟙-induction (λ _ → B) b x
\end{code}

Not all types have to be seen as mathematical statements (for example
the type `ℕ` of natural numbers defined below). But the above definition
has a dual interpretation as a mathematical function, and as the
statement "`B` implies (*true* implies `B`)" where `𝟙` is the type encoding
the truth value *true*.

We will not use this induction principle directly, as we can
prove properties of `𝟙` by pattern matching on `⋆ : 𝟙`, just as we defined the
induction principle.

The unique function to `𝟙` will be named `!𝟙`. We define two versions
to illustrate [implicit
arguments](https://agda.readthedocs.io/en/language/implicit-arguments.html)
which correspond in mathematics to "subscripts that are omitted when
the reader can safely infer them", as for example for the identity
function of a set or the identity arrow of an object of a category.

\begin{code}
!𝟙' : (X : 𝓤 ̇ ) → X → 𝟙
!𝟙' X x = ⋆

!𝟙 : {X : 𝓤 ̇ } → X → 𝟙
!𝟙 x = ⋆
\end{code}

This means that when we write `!𝟙 x` we have to recover the (uniquely
determined) missing type `X` with `x : X` "from the context". When
Agda can't figure it out, we need to supply it and write `!𝟙 {𝓤} {X}
x`. This is because `𝓤` is also an implicit argument (all things
declared with the Agda keyword *variable* as above are implicit
arguments). There are
[other](https://agda.readthedocs.io/en/latest/language/implicit-arguments.html),
non-positional, ways to indicate `X` without having to indicate `𝓤`
too. Occasionally, people define variants of a function with different
choices of "implicitness", as above.

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="emptytype"></a> The empty type `𝟘`

It is defined like `𝟙`, except that no elements are listed for it:

\begin{code}
data 𝟘 : 𝓤₀ ̇  where
\end{code}

That's the complete definition. This has a dual interpretation,
mathematically as the empty set (we can actually prove that this type
is a set, once we know the definition of set - **exercise**), and
logically as the truth-value *false*. To prove that a property of
elements of the empty type holds for all elements of the empty type we
have to do nothing.

\begin{code}
𝟘-induction : (A : 𝟘 → 𝓤 ̇ )
            → (x : 𝟘) → A x
𝟘-induction A ()
\end{code}

When we write the pattern `()`, Agda checks if there is any case we
missed. If there is none, our definition is accepted.  The expression
`()` corresponds to the mathematical phrase [vacuously
true](https://en.wikipedia.org/wiki/Vacuous_truth). The unique
function from `𝟘` to any type is a particular case of `𝟘`-induction.

\begin{code}
!𝟘 : (A : 𝓤 ̇ ) → 𝟘 → A
!𝟘 A a = 𝟘-induction (λ _ → A) a
\end{code}

We give the two names `is-empty` and `¬` to the same function now:

\begin{code}
is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘
\end{code}

This says that a type is empty precisely when we have a function to
the empty type. Assuming [univalence](HoTT-UF-Agda.html#univalence),
once we have defined equality type former
[`_≡_`](MLTT-Agda.html#identitytype), we will be able to prove that
`(is-empty X) ≡ (X ≡ 𝟘)`. We will also be able to prove things like
`(2 + 2 ≡ 5) ≡ 𝟘` and `(2 + 2 ≡ 4) ≡ 𝟙`.

This is for *numbers*. If we define *types* `𝟚 = 𝟙 + 𝟙` and `𝟜 = 𝟚 +
𝟚` with two and four elements respectively, where we are anticipating
the definition of [`_+_`](MLTT-Agda.html#binarysum) for types, then we
will instead have that `𝟚 + 𝟚 ≡ 𝟜` is a type with `4!` elements, which
is [number of permutations](https://en.wikipedia.org/wiki/Factorial)
of a set with four elements, rather than a truth value `𝟘` or `𝟙`, as
a consequence of the univalence axiom. That is, we will have `(𝟚 + 𝟚 ≡
𝟜) ≡ (𝟜 + 𝟜 + 𝟜 + 𝟜 + 𝟜 + 𝟜)`, so that the type equality `𝟚 + 𝟚 ≡ 𝟜`
holds in [many more ways](https://arxiv.org/abs/math/9802029) than the
numerical equation `2 + 2 ≡ 4`.

The above is possible only because universes are genuine types and
hence their elements (that is, types) have identity types themselves,
so that writing `X ≡ Y` for types `X` and `Y` (inhabiting the same
universe) is allowed.


When we view `𝟘` as *false*, we can read the definition of
the *negation* `¬ X` as saying that "`X` implies *false*". With univalence
we will be able to show that "(*false* → *false*) `≡` *true*", which amounts
to `(𝟘 → 𝟘) ≡ 𝟙`, which in turn says that there is precisely one function
`𝟘 → 𝟘`, namely the (vacuous) identity function.

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="naturalnumbers"></a> The type `ℕ` of natural numbers

The definition is similar but not quite the same as the one via
[Peano Axioms](https://en.wikipedia.org/wiki/Peano_axioms).

We stipulate an element `zero : ℕ` and a successor function `ℕ → ℕ`,
and then define induction. Once we have defined equality `_≡_`, we
will [*prove*](HoTT-UF-Agda.html#naturalsset) the other peano axioms.

\begin{code}
data ℕ : 𝓤₀ ̇  where
 zero : ℕ
 succ : ℕ → ℕ
\end{code}

In general, declarations with `data` are inductive definitions. To write the number `5`, we have to write

   > `succ (succ (succ (succ (succ zero))))`

We can use the following Agda
[*pragma*](https://agda.readthedocs.io/en/latest/language/pragmas.html)
to be able to just write `5` as a shorthand:

\begin{code}
{-# BUILTIN NATURAL ℕ #-}
\end{code}

Apart from this notational effect, the above pragma doesn't play any
role in the Agda development of these lectures notes.

In the following, the type family `A` can be seen as playing the role
of a property of elements of `ℕ`, except that it doesn't need to be
necessarily
[subsingleton](HoTT-UF-Agda.html#subsingletonsandsets)-valued. When it
is, the *type* of the function gives the familiar [principle of
mathematical
induction](https://en.wikipedia.org/wiki/Mathematical_induction) for
natural numbers, whereas, in general, its definition says how to
compute with induction.

\begin{code}
ℕ-induction : (A : ℕ → 𝓤 ̇ )
            → A 0
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n
ℕ-induction A a₀ f = h
 where
  h : (n : ℕ) → A n
  h 0        = a₀
  h (succ n) = f n (h n)
\end{code}

The definition of `ℕ-induction` is itself by induction. It says that given a point `a₀ : A 0` and a function `f : (n : ℕ) → A n → A (succ n)`, in order to calculate an element of `A n` for a given `n : ℕ`, we just calculate `h n`, that is,

   > `f n (f (n-1) (f (n-2) (... (f 0 a₀)...)))`.

So the principle of induction is a construction that given a *base
case* `a₀ : A 0`, an *induction step* `f : (n : ℕ) → A n → A (succ n)` and a number `n`, says how to get
an element of the type `A n` by [primitive
recursion](https://www.encyclopediaofmath.org/index.php/Primitive_recursion).

Notice also that ℕ-induction is the dependently typed version of
primitive recursion, where the non-dependently type version is

\begin{code}
ℕ-recursion : (X : 𝓤 ̇ )
            → X
            → (ℕ → X → X)
            → ℕ → X
ℕ-recursion X = ℕ-induction (λ _ → X)
\end{code}

The following special case occurs often (and is related to the fact that `ℕ` is the [initial algebra](https://en.wikipedia.org/wiki/Initial_algebra) of the functor `𝟙 + (-)`):

\begin{code}
ℕ-iteration : (X : 𝓤 ̇ )
            → X
            → (X → X)
            → ℕ → X
ℕ-iteration A a f = ℕ-recursion A a (λ _ a → f a)
\end{code}

Agda checks that any recursive definition as above is well founded,
with recursive invokations with structurally smaller arguments
only. If it isn't, the definition is not accepted.

In official Martin-Löf type theories, we have to use the `ℕ-induction`
functional to define everything else with the natural numbers. But Agda
allows us to define functions by structural recursion, like we defined
`ℕ-induction`.


We now define addition and multiplication for the sake of illustration.
We first do it in Peano style. We will create a local [`module`](https://agda.readthedocs.io/en/latest/language/module-system.html#) so that the
definitions are not globally visible, as we want to have the symbols
`+` and `×` free for type operations of `MLTT` to be defined soon. The
things in the module are indented and are visible outside the module
only if we [`open`](https://agda.readthedocs.io/en/latest/language/module-system.html#) the module or if we write them as
e.g. `Arithmetic.+` in the following example.

\begin{code}
module Arithmetic where

  _+_  _×_  : ℕ → ℕ → ℕ

  x + 0      = x
  x + succ y = succ (x + y)

  x × 0      = 0
  x × succ y = x + x × y

  infixl 0 _+_
  infixl 1 _×_
\end{code}

The above `infix` operations allow us to indicate the precedences
(multiplication has higher precedence than addition) and their
associativity (here we take left-associativity as the convention, so that
e.g. `x+y+z` parses as `(x+y)+z`, but of course this doesn't matter as
both operations are
[associative](https://en.wikipedia.org/wiki/Associative_property)).

Equivalent definitions use `ℕ-induction` on the second argument `y`, via
`ℕ-iteration`:

\begin{code}
module Arithmetic' where

  _+_  _×_  : ℕ → ℕ → ℕ

  x + y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ x succ


  x × y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ 0 (x +_)

  infixl 0 _+_
  infixl 1 _×_
\end{code}

Here the expression "`x +_`" stands for the function `ℕ → ℕ` that adds
`x` to its argument. So to multiply `x` by `y`, we apply `y` times the
function "`x +_`" to `0`.

As another example, we define the less-than-or-equal relation by
nested induction, on the first argument and then the second, but we
use patern matching for the sake of readability.

*Exercise.* Write it using `ℕ-induction`, recursion or iteration, as
appropriate.

\begin{code}
module ℕ-order where

  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
  0      ≤ y      = 𝟙
  succ x ≤ 0      = 𝟘
  succ x ≤ succ y = x ≤ y

  x ≥ y = y ≤ x
\end{code}

*Exercise.* After you have learned [`Σ`](MLTT-Agda.html#sigmatypes)
 and [`_≡_`](MLTT-Agda.html#identitytype) explained below, prove that

   > `x ≤ y` if and only if `Σ \(z : ℕ) → x + z ≡ y`.

Later, when you have learned
[univalence](HoTT-UF-Agda.html#univalence) prove that in this case
this implies

   > `(x ≤ y) ≡ Σ \(z : ℕ) → x + z ≡ y`.

That bi-implication can be turned into equality only holds for types
that are [subsingletons](HoTT-UF-Agda.html#subsingletonsandsets).


If we are doing applied mathematics and want to actually compute, we
can define a type for binary notation, and of course people have done
that. Here we are not concerned with efficiency but only with
understanding how to codify mathematics in (univalent) type theory and
in Agda.

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="binarysum"></a> The binary sum type constructor `_+_`

We now define the disjoint sum of two types `X` and `Y`. The elements of
the type

   > `X + Y`

are stipulated to be of the forms

   > `inl x` and `inr y`

for `x : X` and `y : Y`. If `X : 𝓤` and `Y : 𝓥`, we stipulate that
`X + Y : 𝓤 ⊔ 𝓥 `, where

   > `𝓤 ⊔ 𝓥 `

is the [least upper bound](MLTT-Agda.html#universes) of the two universes `𝓤` and
`𝓥`.  In Agda we can define this as follows.

\begin{code}
data _+_ {𝓤 𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 inl : X → X + Y
 inr : Y → X + Y
\end{code}

To prove that a property `A` of the sum holds for all `z : X + Y`, it is enough to
prove that `A(inl x)` holds for all `x : X` and that `A(inr y)` holds for
all `y : Y`. This amounts to definition by cases:

\begin{code}
+-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X + Y → 𝓦 ̇ )
            → ((x : X) → A(inl x))
            → ((y : Y) → A(inr y))
            → (z : X + Y) → A z
+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y
\end{code}

When the types `A` and `B` are understood as mathematical statements,
the type `A + B` is understood as the statement "`A` or `B`", because
to prove "`A` or `B`" we have to prove one of `A` and `B`. When `A` and
`B` are simultaneously possible, we have two proofs, but sometimes we
want to deliberately ignore which one we get, when we want to get a
truth value rather than a possibly more general type, and in this case
we use the [truncation](Inhabitation.html#truncation) `∥ A + B ∥`.

But also `_+_` is used to construct mathematical objects. For example,
we can define a two-point type:

\begin{code}
𝟚 : 𝓤₀ ̇
𝟚 = 𝟙 + 𝟙
\end{code}

We can name the left and right points as follows, using patterns, so
that they can be used in pattern matching:

\begin{code}
pattern ₀ = inl ⋆
pattern ₁ = inr ⋆
\end{code}

We can define induction on 𝟚 directly by pattern matching:
\begin{code}
𝟚-induction : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁
\end{code}

Or can can prove it by induction on `_+_` and `𝟙`:
\begin{code}
𝟚-induction' : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction' A a₀ a₁ = +-induction A
                         (𝟙-induction (λ (x : 𝟙) → A (inl x)) a₀)
                         (𝟙-induction (λ (y : 𝟙) → A (inr y)) a₁)
\end{code}

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="sigmatypes"></a> `Σ`-types

Given universes `𝓤` and `𝓥`, a type

   > `X : 𝓤`

and a type family

   > `Y : X → 𝓥 `,

we want to construct its sum, which
is a type whose elements are of the form

   > `(x , y)`

with `x : X` and `y : Y x`. This sum type will live in the [least
upper bound](MLTT-Agda.html#universes)

   > `𝓤 ⊔ 𝓥`.

of the universes `𝓤` and `𝓥`. We will write this sum

   > `Σ Y`,

with `X`, as well as the universes, implicit. Often Agda, and people,
can figure out what the unwritten type `X` is, from the definition of `Y`. But
sometimes there may be either lack of enough information, or of
enough concentration power by people, or sufficiently powerful inference
algorithms in the implementation of Agda. In such cases we can write

   > `Σ λ(x : X) → Y x`,

because `Y = λ (x : X) → Y x` by a so-called η-rule. However, we will
often use the synonym `\` of `λ` for Σ, as if considering it as part
of the `Σ` syntax.

   > `Σ \(x : X) → Y x`.

In `MLTT` we would write this as `Σ (x : X), Y x` or
[similar](https://en.wikipedia.org/wiki/Summation), for example with
the indexing `x : X` written as a subscript of `Σ` or under it.


Or it may be that the name `Y` is not defined, and we work with a
nameless family defined on the fly, as in the exercise proposed above:

   > `Σ \(z : ℕ) → x + z ≡ y`,

where `Y z = (x + z ≡ y)` in this case, and where we haven't defined
the [identity type former](MLTT-Agda.html#identitytype) `_≡_` yet.

We can construct the `Σ` type former as follows in Agda:

\begin{code}
record Σ {𝓤 𝓥} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
  constructor _,_
  field
   x : X
   y : Y x
\end{code}

This says we are defining a binary operator `_,_` to construct the
elements of this type as `x , y`. The brackets are not needed, but we
will often write them to get the more familiar notation `(x , y)`. The
definition says that an element of `Σ Y` has two `fields`, giving the
types for them.

*Remark.* Beginners may safely ignore this remark: Normally people
will call these two fields something like `pr₁` and `pr₂`, or `fst`
and `snd`, for first and second projection), rather than `x` and `y`,
and then do `open Σ public` and have the projections available as
functions automatically. But we will deliberately not do that, and
instead define the projections ourselves, because this is confusing
for beginners, no matter how mathematically or computationally versed
they may be, in particular because it will not be immediately clear
that the projections have the following types.

\begin{code}
pr₁ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y
\end{code}

To prove that `A z` holds for all `z : Σ Y`, for a given
property `A`, we just prove that we have `A(x , y)` for all given `x :
X and for all y : Y x`.  This is called `Σ` induction or `Σ`
elimination, or `uncurry`, after [Haskell
Curry](https://en.wikipedia.org/wiki/Haskell_Curry).
\begin{code}
Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
            → ((x : X) (y : Y x) → A(x , y))
            → (z : Σ Y) → A z
Σ-induction g (x , y) = g x y
\end{code}

This function has an inverse:

\begin{code}
curry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
      → ((z : Σ Y) → A z)
      → ((x : X) (y : Y x) → A (x , y))
curry f x y = f (x , y)
\end{code}

An important particular case of the sum type is the binary cartesian
product, when the type family doesn't depend on the indexing family:

\begin{code}
_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ \(x : X) → Y
\end{code}

We have seen by way of examples that the function type symbol `→`
represents logical implication, and that a dependent function type
`(x : X) → A x` represents a universal quantification.

We have the following uses of `Σ`.

  * The binary cartesian product represents conjunction "and". If the
    types `A` and `B` stand for mathematical statements, then the mathematical
    statement "`A` and `B`" is codified as `A × B`. This is because to prove
    "`A` and `B`", we have to provide a pair `(a , b)` of proofs `a : A` and `b : B`.

    So notice that in type theory, proofs are mathematical objects,
    rather than meta-mathematical entities like in set theory. They are
    just elements of types.

  * The more general type `Σ \(x : X), A x`, if the type `X` stands
    for a mathematical object and `A` stands for a mathematical
    statement, represents *designated* existence "there is a
    designated `x : X` with `A x`".  To prove this, one has to provide
    a specific `x : X` and a proof `a : A x`, together in a pair
    `(x , a)`.

  * Later we will discuss *unspecified* existence `∃ \(x : X) → A x`,
    which will be obtained by a sort of quotient of `Σ \(x : X), A x`,
    written `∥ Σ \(x : X), A x ∥` that identifies all the elements of
    the type `Σ \(x : X), A x` in a single equivalence class, called
    its propositional or subsingleton
    [truncation](Inhabitation.html#truncation).

  * Another reading of `Σ \(x : X), A x` is as "the type of `x : X`
    with `A x`", similar to subset notation `{ x ∈ X | A x }` in set
    theory. But have to be careful because if there is more than one
    element in the type `A x`, then `x` is put more than once in this
    type. In such situations, if we don't want that, we have to be
    careful and either ensure that the type `A x` has at most one
    element for every `x : X`, or instead consider the truncated type
    `∥ A x ∥` and write `Σ \(x : X), ∥ A x ∥`.

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="pitypes"></a> `Π`-types

`Π`-types are builtin with a different notation in Agda, as discussed
above, but we can introduce the notation `Π` for them, similar to that for `Σ`:

\begin{code}
Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x
\end{code}

Notice that the function type `X → Y` is the particular case of the `Π`
type when the family `A` is constant with value `Y`.

We take the opportunity to define the identity function and function
composition:

\begin{code}
id : {X : 𝓤 ̇ } → X → X
id x = x
\end{code}

Usually the type of function composition `_∘_` is given as simply

   >  `(Y → Z) → (X → Y) → (X → Z)`.

With dependent functions, we can give it a more general type:

\begin{code}
_∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
g ∘ f = λ x → g (f x)
\end{code}

Notice that this type for the composition function can be read as a mathematical
statement: If `Z y` holds for all `y : Y`, then for any given `f : X →
Y` we have that `Z (f x)` holds for all `x : X`. And the non-dependent
one is just the transitivity of implication.

The following functions are sometimes useful when we are using
implicit arguments, in order to recover them explicitly without having
to list them as given arguments:

\begin{code}
domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

type-of : {X : 𝓤 ̇ } → X → 𝓤 ̇
type-of {𝓤} {X} x = X
\end{code}

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="identitytype"></a> The identity type former `Id`, also written `_≡_`

We now introduce the central type constructor of `MLTT` from the point
of view of univalent mathematics. In Agda we can define Martin-Löf's
identity type as follows:

\begin{code}
data Id {𝓤} (X : 𝓤 ̇ ) : X → X → 𝓤 ̇  where
 refl : (x : X) → Id X x x
\end{code}

Intuitively, the above definition would say that the only element
of the type `Id X x x` is something called `refl x` (for
reflexivity). But, as we shall see in a moment, this intuition turns
out to be incorrect.

Notice a crucial difference with the previous definitions using `data`
or induction: In the previous cases, we defined *types*, namely `𝟘`,
`𝟙`, `ℕ` , or a *type depending on parameters*, namely `_+_` , with `𝓤`
and `𝓥` fixed,

   > `_+_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇`

But here we are defining a *type family* indexed by the *elements* of
a give type, rather than a new type from old types. Given a type `X`
in a universe `𝓤`, we define a *function*

   > `Id X : X → X → 𝓤`

by some mysterious sort of induction. It is this that prevents us from
being able to prove that `refl x` would be the only element of the type `Id
X x x`, or that for `Id X x y` would have at most one element no
matter what `y : X` is. There is however, one interesting thing we
[can prove](HoTT-UF-Agda.html#retracts), namely that for any fixed `x : X`, the
type


   > `Σ \(y : Y) → Id X x y`

is always a [singleton](HoTT-UF-Agda.html#hlevel).

We will use the following alternative notation for the identity type
former `Id`, where the symbol "`_`" in the right-hand side of the
definition indicates that we ask Agda to infer which type we are
talking about (which is `X`, but this name is not available in the
scope of the *definiting equation* of `_≡_`):

\begin{code}
_≡_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≡ y = Id _ x y
\end{code}

Another intuition for this type family `_≡_ : X → X → 𝓤` is that it
gives the least reflexive relation on the type `X`, as indicated by
Martin-Löf's induction principle `J` discussed below.

Whereas we can make the intuition that `x ≡ x` has precisely one
element good by postulating a certain [`K`
axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) due to
Thomas Streicher, which comes with Agda by default but we have
[disabled above](MLTT-Agda.html#gettingstartedagda), we cannot *prove* that `refl x`
is the only element of `x ≡ x` for an arbitrary type `X`. This
non-provability result was established by [Hofmann and
Streicher](https://ieeexplore.ieee.org/document/316071), by giving a
model of type theory in which types are interpreted as
[groupoids](https://en.wikipedia.org/wiki/Groupoid).

However, for the elements of *some* types, such as `ℕ`, it is possible
to prove that any identity type `x ≡ y` has at most one element. Such
types are called [sets in univalent
mathematics](HoTT-UF-Agda.html#subsingletonsandsets).

If instead of `K` we adopt Voevodsky's
[univalence](HoTT-UF-Agda.html#univalence) axiom, we get [specific
examples](HoTT-UF-Agda.html#notsets) of objects `x` and `y` such that
the type `x ≡ y` has multiple elements, *within* the type theory.  It
follows that the identity type `x ≡ y` is fairly under-specified in
general, in that we can't prove or disprove that it has at most one
element.

There are two opposing ways to resolve the ambiguity or
underspecification of the identity types: (1) We can consider the `K`
axiom, which postulates that all types are sets, or (2) we can
consider the univalence axiom, arriving at univalent mathematics,
which gives rise to types that are more general than sets, the
`n`-gropoids and `∞`-groupoids.  In fact, the univalence axiom will
say, in particular, that for some types `X` and elements `x y : X`, the
identity type `x ≡ y` does have more than one element.

A possible way to understand the point `refl x` of the type `x ≡ x` is
as the "generic identification" between `x` and itself, but which is
by no means necessarily the *only* identitification in univalent
foundations. It is generic in the sense that to explain what happens
with all identifications `p : x ≡ y` between any two points `x` and
`y` of a type `X`, it suffices to explain what happens with the
identification `refl x : x ≡ x` for all points `x : X`. This
what the induction principle for identity given by Martin-Löf says,
which he called `J` (we could have called it `≡-induction`, but we
prefer to honour `MLTT` tradition):

\begin{code}
J : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ≡ y) → A x y p
J X A f x x (refl x) = f x
\end{code}

This is [related](http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html) to the [Yoneda
Lemma](https://en.wikipedia.org/wiki/Yoneda_lemma) in category theory,
if you are familiar with this subject, which says that certain natural
transformations are *uniquely determined* by their *action on the
identity arrows*, even if they are *defined for all arrows*. Similarly
here, `J` is uniquely determined by its action on reflexive
identifications, but is *defined for all identifications between any
two points*, not just reflexivities.

In summary, Martin-Löf's identity type is given by the data

  * `Id`,
  * `refl`,
  * `J`,
  * The above equation for `J`.

However, we will not use this induction principle, because we can
instead work with the instances we need by pattern matching on `refl`
(which is just what we did to define the principle itself) and there
is a [theorem by Jesper
Cockx](<https://dl.acm.org/citation.cfm?id=2628139) which says that
with the Agda option `without-K`, pattern matching on `refl` can
define/prove precisely what `J` can.

*Exercise*. Define
\begin{code}
H : {X : 𝓤 ̇ } (x : X) (B : (y : X) → x ≡ y → 𝓥 ̇ )
  → B x (refl x)
  → (y : X) (p : x ≡ y) → B y p
H x B b x (refl x) = b
\end{code}

Then we can define `J` from `H` as follows:

\begin{code}
J' : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
   → ((x : X) → A x x (refl x))
   → (x y : X) (p : x ≡ y) → A x y p
J' X A f x = H x (A x) (f x)

Js-agreement : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
               (f : (x : X) → A x x (refl x)) (x y : X) (p : x ≡ y)
             → J X A f x y p ≡ J' X A f x y p
Js-agreement X A f x x (refl x) = refl (f x)
\end{code}

Similarly define `H'` from `J` without using pattern matching on refl
and show that it coincides with `H` (possibly using pattern maatching
on `refl`). This is
[harder](http://www.cse.chalmers.se/~coquand/singl.pdf).

**Notational remark.** The symbols "`=`" and "`≡`" are swapped with
  respect to the [HoTT Book](https://homotopytypetheory.org/book/)
  convention for definitional/judgemental equality and typed-valued equality,
  and there is nothing we can do about that because "`=`" is a
  reserved Agda symbol for definitional equality. Irrespectively of
  this, it does make sense to use "`≡`" with a triple bar, if we
  understand this as indicating that there are multiple ways of
  identifying two things in general.

With this, we have concluded the rendering of our spartan `MLTT` in
Agda notation. Before embarking on the development of univalent
mathematics within our spartan `MLTT`, we pause to discuss some
basic examples of mathematics in Martin-Löf type theory.

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="basicidentity"></a> Basic constructions with the identity type

*Transport along an identification.*
\begin{code}
transport : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
          → x ≡ y → A x → A y
transport A (refl x) = id
\end{code}

We can equivalently define transport using `J` as follows:

\begin{code}
transportJ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
           → x ≡ y → A x → A y
transportJ {𝓤} {𝓥} {X} A {x} {y} = J X (λ x y _ → A x → A y) (λ x → id) x y
\end{code}

In the same way `ℕ`-recursion can be seen as the non-dependent special
case of `ℕ`-induction, the following transport function can be seen as
the non-dependent special case of the `≡`-induction principle `H` with
some of the arguments permuted and made implicit:

\begin{code}
nondep-H : {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
         → A x → (y : X) → x ≡ y → A y
nondep-H {𝓤} {𝓥} {X} x A = H x (λ y _ → A y)

transportH : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
           → x ≡ y → A x → A y
transportH {𝓤} {𝓥} {X} A {x} {y} p a = nondep-H x A a y p
\end{code}

All the above transports coincide:

\begin{code}
transports-agreement : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                     → (transportH A p ≡ transportH A p)
                     × (transportJ A p ≡ transportH A p)
transports-agreement A (refl x) = refl (transport A (refl x)) ,
                                  refl (transport A (refl x))
\end{code}



The following is for use when we want to recover implicit
arguments without mentioning them.

\begin{code}
lhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
rhs {𝓤} {X} {x} {y} p = y
\end{code}

*Composition of identifications.*
Given two identifications `p : x ≡ y` and `q : y ≡ z`, we can compose them
to get an identification `p ∙ q : x ≡ y`. This can also be seen as
transitivity of equality. Because the type of composition doesn't
mention `p` and `q`, we can use the non-dependent version of `≡`-induction.

\begin{code}
_∙_ : {X : 𝓤 ̇ } {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = transport (lhs p ≡_) q p
\end{code}

Here we are considering the family `A t = (x ≡ t)`, and using the
identification `q` to transport `A y` to `A z`, that is `x ≡ y` to `x
≡ z`.

*Exercise.* define an alternative version that uses `p` to
transport. Can you prove that the two versions give equal results?

When writing `p ∙ q`, we lose information on the lhs and the rhs of the
identification, which makes some definitions hard to read. We now
introduce notation to be able to write e.g.

   > `x ≡⟨ p ⟩`

   > `y ≡⟨ q ⟩`

   > `z ∎`

as a synonym of the expression `p ∙ q` with some of the implicit arguments of `_∙_` made
explicit. We have one ternary *mixfix* operator `_≡⟨_⟩_` and one unary
"postfix" operator _∎.

\begin{code}
_≡⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_∎ : {X : 𝓤 ̇ } (x : X) → x ≡ x
x ∎ = refl x
\end{code}

*Inversion of identifications.* Given an identification, we get an
  identification in the opposite direction:

\begin{code}
_⁻¹ : {X : 𝓤 ̇ } → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport (_≡ lhs p) p (refl (lhs p))
\end{code}

*Application of a function to an identification*.
Given an identification `p : x ≡ x'` we get an identification
`ap f p : f x ≡ f x'` for any `f : X → Y`:

\begin{code}
ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f p = transport (λ - → f (lhs p) ≡ f -) p (refl (f (lhs p)))
\end{code}

Notice that we have so far used the recursion principle `transport`
only. To reason about `transport`, `_∙_`, `_⁻¹` and `ap`, we [will
need](HoTT-UF-Agda.html#identitytypeuf) to use the full induction
principle `J`.

*Pointwise equality of functions*. We will work with pointwise
equality of functions, defined as follows, which, using univalence,
will be [equivalent to equality of functions](FunExt.html#hfunext).

\begin{code}
_∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ((x : X) → A x) → ((x : X) → A x) → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ≡ g x
\end{code}

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="negation"></a> Proofs involving negation

We first introduce notation for double and triple negation to avoid
the use of brackets.

\begin{code}
¬¬ ¬¬¬ : 𝓤 ̇ → 𝓤 ̇
¬¬  A = ¬(¬ A)
¬¬¬ A = ¬(¬¬ A)
\end{code}

To prove that `A → ¬¬ A`, that is, `A → ((A → 𝟘) → 𝟘)`, we start with
a hypothetical element `a : A` and a hypothetical function `u : A → 𝟘`
and the goal is to get an element of `𝟘`. All we need to do is to
apply the function `u` to `a`.

\begin{code}
dni : {A : 𝓤 ̇ } → A → ¬¬ A
dni a u = u a
\end{code}

The reasoning is similar for the following. We assume we are given
hypothetical `f : A → B`, `v : B → 𝟘` and `a : A` and our goal is to
get an element of `𝟘`.

\begin{code}
contrapositive : {A : 𝓤 ̇ } {B : 𝓤 ̇ } → (A → B) → (¬ B → ¬ A)
contrapositive f v a = v (f a)
\end{code}

And from this we get the three negations imply one:
\begin{code}
tno : {A : 𝓤 ̇ } → ¬¬¬ A → ¬ A
tno = contrapositive dni
\end{code}

We now define a symbol for the negation of identity equality.

\begin{code}
_≢_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≢ y = ¬(x ≡ y)
\end{code}

In the following proof, we have `u : x ≡ y → 𝟘` and need to define a
function `y ≡ x → 𝟘`. So all we need to do is to compose the function
that inverts identifications with `u`:

\begin{code}
≢-sym : {X : 𝓤 ̇ } {x y : X} → x ≢ y → y ≢ x
≢-sym {𝓤} {X} {x} {y} u = λ (p : y ≡ x) → u (p ⁻¹)
\end{code}

To show that the type `𝟙` is not equal to the type `𝟘`, we use that
`transport id` gives `𝟙 ≡ 𝟘 → id 𝟙 ≡ id 𝟘` where `id` is the [identity
function](MLTT-Agda.html#pitypes). So if we have a hypothetical
identification `p : 𝟙 ≡ 𝟘`, then we get a function `𝟙 → 𝟘`. We apply
this function to `⋆ : 𝟙` to conclude the proof.

\begin{code}
𝟙-is-not-𝟘 : ¬(𝟙 ≡ 𝟘)
𝟙-is-not-𝟘 p = f p ⋆
 where
  f : 𝟙 ≡ 𝟘 → 𝟙 → 𝟘
  f = transport id
\end{code}

To show that the elements `₁` and `₀` of the two-point type `𝟚` are
not equal, we reduce to the above case. We start with a hypothetical
identification `p : ₁ ≡ ₀`.

\begin{code}
₁-is-not-₀ : ¬(₁ ≡ ₀)
₁-is-not-₀ p = 𝟙-is-not-𝟘 q
 where
  f : 𝟚 → 𝓤₀ ̇
  f ₀ = 𝟘
  f ₁ = 𝟙
  q : 𝟙 ≡ 𝟘
  q = ap f p
\end{code}

*Remark.* Agda allows us to use a pattern `()` to get the following
quick proof.  However, this method of proof doesn't belong to the
realm of MLTT.

\begin{code}
₁-is-not-₀[not-an-MLTT-proof] : ¬(₁ ≡ ₀)
₁-is-not-₀[not-an-MLTT-proof] ()
\end{code}

Perhaps the following is sufficiently self-explanatory given the above:

\begin{code}
𝟚-has-decidable-equality : (m n : 𝟚) → (m ≡ n) + (m ≢ n)
𝟚-has-decidable-equality ₀ ₀ = inl (refl ₀)
𝟚-has-decidable-equality ₀ ₁ = inr (≢-sym ₁-is-not-₀)
𝟚-has-decidable-equality ₁ ₀ = inr ₁-is-not-₀
𝟚-has-decidable-equality ₁ ₁ = inl (refl ₁)
\end{code}

So we consider four cases. In the first and the last, we have equal
things and so we give an answer in the left-hand side of the sum. In
the middle two, we give an answer in the right-hand side, where we need
functions `₀ ≡ ₁ → 𝟘` and `₁ ≡ ₀ → 𝟘`, which we can take to be `≢-sym
₁-is-not-₀` and `₁-is-not-₀` respectively.

The following is more interesting. We consider the two possible cases
for `n`. The first one assumes a hypothetical function `f : ₀ ≡ ₀ →
𝟘`, from which we get `f (refl ₀) : 𝟘`, and then, using `!𝟘`, we get
an element of any type we like, which we choose to be `₀ ≡ ₁`, and we
are done. Of course, we will never be able to call the function
`not-zero-is-one` with such outrageous inputs. The other case `n = ₁`
doesn't need to use the hypothesis `f : ₁ ≡ ₀ → 𝟘`, because the
desired conclusion holds right away, as it is `₁ ≡ ₁`, which is proved
by `refl ₁`. But notice that there is nothing wrong with the
hypothesis `f : ₁ ≡ ₀ → 𝟘`. For example, we can call `not-zero-is-one`
with `n = ₀` and `f = ₁-is-not-₀`, so that the hypothesis can be
fulfilled in the second equation.

\begin{code}
not-zero-is-one : (n : 𝟚) → n ≢ ₀ → n ≡ ₁
not-zero-is-one ₀ f = !𝟘 (₀ ≡ ₁) (f (refl ₀))
not-zero-is-one ₁ f = refl ₁
\end{code}

The following generalizes `₁-is-not-₀`, both in its statement and its
proof (so we could have formulated it first and then used it to deduce
`₁-is-not-₀`):

\begin{code}
inl-inr-disjoint-images : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y} → inl x ≢ inr y
inl-inr-disjoint-images {𝓤} {𝓥} {X} {Y} p = 𝟙-is-not-𝟘 r
 where
  f : X + Y → 𝓤₀ ̇
  f (inl x) = 𝟙
  f (inr y) = 𝟘
  r : 𝟙 ≡ 𝟘
  r = ap f p
\end{code}

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="twinprime"></a> Example: formulation of the twin-prime conjecture

We illustrate the above constructs of `MLTT` to formulate this
conjecture.

\begin{code}
module twin-primes where

 open Arithmetic renaming (_×_ to _*_ ; _+_ to _∔_)
 open ℕ-order

 is-prime : ℕ → 𝓤₀ ̇
 is-prime n = (n ≥ 2) × ((x y : ℕ) → x * y ≡ n → (x ≡ 1) + (x ≡ n))

 twin-prime-conjecture : 𝓤₀ ̇
 twin-prime-conjecture = (n : ℕ) → Σ \(p : ℕ) → (p ≥ n) × is-prime p × is-prime (p ∔ 2)
\end{code}

Thus, can we write down not only definitions, constructions, theorems
and proofs, but also conjectures. They are just definitions of
types. Likewise, the univalence axiom, [to be formulated in due course](HoTT-UF-Agda.html#univalence),
is a type.

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="infix"></a> Operator fixities and precedences

Without the following the following list of operator precedence and
associativity (left or right), this agda file doesn't parse and is
rejected by Agda.

\begin{code}
infix  4  _∼_
infixr 4 _,_
infixr 2 _×_
infixr 1 _+_
infixl 5 _∘_
infix  0 _≡_
infixl 2 _∙_
infixr 0 _≡⟨_⟩_
infix  1 _∎
infix  3  _⁻¹
\end{code}

[<sub>Table of contents ⇑</sub>](toc.html#contents) [<sub>HoTT/UF ⇓</sub>](HoTT-UF-Agda.html)
