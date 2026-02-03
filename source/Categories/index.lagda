Anna Williams, 17 October 2025

Formalisation of some 1-category theory with univalent foundations.
Included are definitions of wild categories, precategories,
(univalent) categories, functors and natural transformations.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Categories.index where

\end{code}

We follow the naming conventions of the HoTT Book [1] and [2]. The properties of
the different types of category are given in the table below.

[1] The Univalent Foundations Program (2013), Homotopy Type Theory: Univalent
Foundations of Mathematics. Institute for Advanced Study:
https://homotopytypetheory.org/book.

[2] Capriotti, Paolo and Nicolai Kraus (2017). Univalent Higher Categories via
Complete Semi-Segal Type. https://arxiv.org/abs/1707.03693.

                ┌──────┬──────┬────────────┐
                │ obj  │ hom  │ univalence │
┌───────────────┼──────┼──────┼────────────┤
│ wild-category │ type │ type │ no         │
├───────────────┼──────┼──────┼────────────┤
│ pre-category  │ type │ set  │ no         │
├───────────────┼──────┼──────┼────────────┤
│ category      │ type │ set  │ yes        │
└───────────────┴──────┴──────┴────────────┘

\begin{code}

import Categories.Wild
import Categories.Pre
import Categories.Univalent

import Categories.Functor
import Categories.Functor-Composition
import Categories.NaturalTransformation

\end{code}

Notation for working with categories, we use this so that we can write the
following and have the category fields be public.

`open WildCategoryNotation C`
`open PrecategoryNotation C`
`open CategoryNotation C`

`open FunctorNotation F renaming (functor-map to F')`

`open NaturalTNotation N`

We use this notation throughout the definitions, so for more concrete examples
please look there.

\begin{code}

import Categories.Notation.index

\end{code}
