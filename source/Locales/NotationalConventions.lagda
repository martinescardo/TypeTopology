
Ayberk Tosun, 13 September 2023

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import MLTT.Spartan
open import UF.Logic
open import UF.SubtypeClassifier
open import Slice.Family

module Locales.NotationalConventions (pt : propositional-truncations-exist)
                                     (fe : Fun-Ext) where

open import Locales.SmallBasis                 pt fe
open import Locales.Spectrality.SpectralLocale pt fe

\end{code}

\section{Data vs. property distinction}

As we work in Univalent Foundations, we maintain a careful distinction between
structures and properties.

To emphasise that we are working with the structural version of a definition
that has a version that is a property, we use the superscript `_ᴰ` (for "data").

For example, we have `spectralᴰ` which denotes the structure involved in
spectrality.

\begin{code}

_ = spectralᴰ

\end{code}

The version that is a property is called `is-spectral`.

\begin{code}

_ = is-spectral

\end{code}

\section{Locales vs. frames}

TODO
