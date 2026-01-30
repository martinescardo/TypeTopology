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

We follow the naming conventions of the HoTT Book [1] and [2]. The properties of the
different types of category are given in the table below.

[1] The Univalent Foundations Program (2013), Homotopy Type Theory: Univalent Foundations of Mathematics. Institute for Advanced Study: https://homotopytypetheory.org/book.

[2] Capriotti, Paolo and Nicolai Kraus (2017). Univalent Higher Categories via Complete Semi-Segal Type. https://arxiv.org/abs/1707.03693.

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

\end{code}

Notation for working with categories

\begin{code}

import Categories.Notation.index

import Categories.Functor
import Categories.NaturalTransformation

\end{code}
