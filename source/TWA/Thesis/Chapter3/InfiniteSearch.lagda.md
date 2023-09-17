# Search over uniformly continuous decidable predicates on infinite collections of types

Todd Waugh Ambridge, 15th December 2021 and 1st February 2022

I explore, in the following two blog posts, two key concepts:
searchable types and closeness functions.

 - [Please click here to read Part I.](InfiniteSearch1.html)
 - [Please click here to read Part II.](InfiniteSearch2.html)

The blog posts are written in literate Agda, meaning that
everything is both explained in text and fully-foramlised
in Agda. I use Martín Escardó's Agda library [TypeTopology](https://www.cs.bham.ac.uk/~mhe/agda-new/)
as a framework.

## Introduction

```agda
module InfiniteSearch where
```

A type X is searchable if, given any predicate `p : X → {tt,ff}`,
we can find some `x : X` such that if there is some x₀ such that `p(x₀) ≡ tt`
then also `p(x) ≡ tt`.

In [Haskell](http://math.andrej.com/2007/09/28/seemingly-impossible-functional-programs/),
or [Agda with the termination checker
turned off](https://www.cs.bham.ac.uk/~mhe/agda/CountableTychonoff.html),
we can write a program that searches Cantor space
(infinitary binary sequences) ─ in fact, Martín Escardó wrote both programs,
in [2007](http://math.andrej.com/2007/09/28/seemingly-impossible-functional-programs/)
and [2011](https://www.cs.bham.ac.uk/~mhe/agda/CountableTychonoff.html)
respectively.

The latter program goes further than just the Cantor space,
it in fact shows that searchable types are closed under countable
(`ℕ`-indexed) products. Given that searchable types coincide 
with the topological notion of compact types,
this program -- along with the proof that it terminates
-- are tantamount to the Tychonoff theorem for searchable types.

The proofs that these programs terminate rely on classical logic;
they assume that the given predicates are continuous, and they
use classical logic to determine that they are uniformly continuous.
We wish to give a constructive formulation of the the Tychonoff theorem
for searchable types by explicitly restricting to uniformly continuous
predicates.

Intuitively, a predicate `p : X → {tt,ff}` is uniformly continuous if
there is some notion of precision `δ` such that, for all `x,y : X` that
are `δ`-close if `p(x) ≡ tt` then also `p(y) ≡ tt`.

We find it convenient to formulate uniform continuity using the notion
of a closeness function. If a type `X` has a closeness function
`c : X × X → ℕ∞`, where `ℕ∞` is the natural numbers extended with
a point at infinity, then we can define a version of uniform
continuity on predicates of that type. Using this version of uniform
continuity, the notion of precision is a natural number `δ : ℕ`, and two
elements `x,y : X` are `δ`-close if `δ ≼ c(x,y)`.

If a type has a canonical closeness function such that we
can search the type for the answer to any predicate that is
uniformly continuous with respect to the closeness function,
then it is called (uniformly) continuously searchable.

We prove the Tychonoff theorem for continuously searchable
types in constructive mathematics.

## Part I

```agda
open import InfiniteSearch1
```

In the first part, we introduce the type theory and the concepts of
closeness functions and continuously searchable types formally.

Then, we show that:
1. Every discrete type has a canonical closeness function,
and that every such type is continuously searchable with respect to
this closeness function if it is searchable in the traditional sense.
1. Every sequence type of discrete types has a canonical closness
function, and that every such type is continuously searchable with
respect to this closeness function.

[Please click here to read Part I.](InfiniteSearch1.html)

## Part II

```agda
open import InfiniteSearch2
```

In the second part, we show that types equipped with closeness functions
are closed under countable products. Further, and chiefly,
continuously searchable types themselves are closed under countable
products.

[Please click here to read Part II.](InfiniteSearch2.html)

## Further reading

     Escardo, Martin. (2007).
       Infinite sets that admit fast exhaustive search.
       Proceedings - Symposium on Logic in Computer Science (LICS 2007).
     
     Ghica, Dan R. and Waugh Ambridge, Todd. (2021).
       Global optimisation with constructive reals.
       Proceedings - Symposium on Logic in Computer Science (LICS 2021).
     
## Acknowledgements

Thank you to [Martín Escardó](https://www.cs.bham.ac.uk/~mhe/) for all the support,
[Tom de Jong](https://www.cs.bham.ac.uk/~txd880/) for feedback,
and [George Kaye](https://www.georgejkaye.com/) for help with
formatting the posts.
