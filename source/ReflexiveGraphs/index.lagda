Ian Ray. August 2025–June 2026.

The structure identity principle (SIP), coined by Peter Aczel, allows for a
treatment of identificiation in Univalent Foundations that, with much care,
escapes "transport hell". Many have formulated there own terminology and
approach to SIP (including Egbert Rijke in "Introduction to Homotopy Type
Theory" see doi:10.1017/9781108933568, arXiv:2212.11082; Martin Escardo in
files: UF/SIP, UF/Yoneda and UF/SigmaIdentity; as well as many others!) In
recent times, some have considered 'reflexive graphs' as a more modular
approach to SIP (see "Using Displayed Univalent Graphs to Formalize Higher
Groups in Univalent Foundations" by Johannes Schipp von Branitz and Ulrik
Buchholtz, https://ulrikbuchholtz.dk/durgs.pdf; and "Reflexive graph lenses
in univalent foundations" by Jonathan Sterling.)

Here we will explore the foundation of the theory of (displayed) (univalent)
reflexive graphs following Sterling. Sterling also introduces the notion of
a reflexive graph lens which may be described as a generic notion of transport
which leads to novel characterizations of indetity. We will provide multiple
examples that outline the reflexive graph approach to SIP, including the use
of lenses. Since Sterling is the primary source for this development we will
include a full reference to his work.

Jonathan Sterling. 'Reflexive graph lenses in univalent foundations'.
In: Mathematical Structures in Computer Science 36, e21 (2026), pp. 1–48.
DOI: 10.1017/S0960129526100565

\begin{code}

{-# OPTIONS --safe --without-K #-}

module ReflexiveGraphs.index where

import ReflexiveGraphs.Constructions
import ReflexiveGraphs.Displayed
import ReflexiveGraphs.DisplayedUnivalent
import ReflexiveGraphs.Examples
import ReflexiveGraphs.Lenses
import ReflexiveGraphs.Properties
import ReflexiveGraphs.Type
import ReflexiveGraphs.UnbiasedLenses
import ReflexiveGraphs.Univalent
import ReflexiveGraphs.UnivalentClosureProperties
import ReflexiveGraphs.UnivalentFamilies

\end{code}
