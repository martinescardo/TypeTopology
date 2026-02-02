Ian Ray. August 2025–February 2026.

The structure identity principle (SIP), coined by Peter Aczel, allows an
treatment of identificiation in Univalent Foundations that, with much care,
escapes "transport hell". Many have formulated there own terminology and
approach to SIP (including Egbert Rijke in "Introduction to Homotopy Type
Theory" see doi:10.1017/9781108933568, arXiv:2212.11082; Martin Escardo in
files: UF/SIP, UF/Yoneda and UF/SigmaIdentity; as well as many others!) In
recent times, some have considered 'reflexive graphs' as a more modular
approach to SIP (see "Using Displayed Univalent Graphs to Formalize Higher
Groups in Univalent Foundations" by Johannes Schipp von Branitz and Ulrik
Buchholtz, https://ulrikbuchholtz.dk/durgs.pdf; and "Reflexive graph lenses
in univalent foundations" by Jonathan Sterling,
https://doi.org/10.48550/arXiv.2404.07854).

Here we will explore the foundation of the theory of (displayed) (univalent)
reflexive graphs following Sterling. We will also provide multiple examples
that outline the reflexive graph approach to SIP.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module ReflexiveGraphs.index where

import ReflexiveGraphs.Type

\end{code}
