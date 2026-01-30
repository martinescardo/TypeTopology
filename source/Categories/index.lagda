Anna Williams, 17 October 2025

Formalisation of some 1-category theory with univalent foundations.
Included are definitions of wild categories, precategories,
(univalent) categories, functors and natural transformations.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Categories.index where

\end{code}

Definitions of
 * wild category,
 * precategory, and
 * category.

We follow the naming conventions of the HoTT Book [1]. The properties of the
different types of category are given in the table below.

[[Add full reference to the HoTT Book, like HoTT Book [1], and the add the full reference
from here https://homotopytypetheory.org/book/]]


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

import Categories.Notation

import Categories.Functor
import Categories.NaturalTransformation

\end{code}
