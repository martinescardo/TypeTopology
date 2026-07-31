Martin Escardo, July 2026.

This directory is a setoid-based Spartan MLTT counterpart to the
HoTT/UF files Groups.Free and Groups.Large.

We work with egroups, that is, groups whose underlying type of
elements is a setoid, with the group laws holding up to the
equivalence relation of the setoid rather than up to the identity
type.

We deliberately don't add as many comments as in the files Groups.Free
and Groups.Large when the ingredients are the same, reserving comments
mostly for the new ingredients developed here.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EGroups.index where

import EGroups.Setoid
import EGroups.Type
import EGroups.Size
import EGroups.ChurchRosserModulo
import EGroups.Reduction
import EGroups.Free
import EGroups.Large

\end{code}

 * Setoid

   A setoid is a type equipped with an equivalence relation given as
   data, not required to be proposition-valued in the sense of
   HoTT/UF, as here we work with propositions as types, rather than
   propositions as subsingletons. This module also collects general
   setoid infrastructure, including equational reasoning, setoid maps,
   setoid isomorphism, and the function setoid.

 * Type

   This module defines the type of egroups and develops homomorphisms,
   isomorphisms, and some minimal group theory up to the equivalence
   relation. An egroup is a setoid equipped with a compatible group
   structure, with the operation a congruence and the group laws
   holding up to the equivalence relation.

 * Size

   This module introduces size notions for setoids. A setoid is
   locally small when its equivalence relation is small-valued, and
   small when it is isomorphic to a setoid whose underlying type and
   equivalence relation are both small. The universe, with type
   equivalence as its relation, is locally small because X ≃ Y is
   small when X and Y are.

 * ChurchRosserModulo

   We state and prove the Church-Rosser property modulo an equivalence
   relation, for an abstract reduction whose reducts agree only up to
   the relation. When the reduction is confluent up to the relation,
   two convertible points have reducts that agree up to the relation.

 * Reduction

   This module sets up the reduction underlying the free egroup on a
   setoid, which cancels two adjacent generators when the second is
   related to the inverse of the first. We prove local confluence up
   to the relation and hence, via the previous module, the
   Church-Rosser property. A size reduction in the style of
   Groups.Free shows that the type of generators is small even when
   the setoid is large, using no decidable equality.

 * Free

   The free egroup on a setoid has as underlying type the words on the
   generators with polarity modulo convertibility, with multiplication
   given by concatenation. We prove its universal property, that a
   setoid map from the generators into an egroup has a unique
   extension to a homomorphism, up to the equivalence relation of that
   egroup. But notice that the universal property is not needed for
   the purposes of the next module.

 * Large

   The free egroup on a large, locally small setoid is large. No egroup
   whose underlying type and equivalence relation are both small is
   isomorphic to it. We then give the example we are after. The
   universe, taken as a setoid under type equivalence, is a large
   setoid, by the generalized Lawvere fixed-point theorem, and so there
   is a large egroup in the next universe, in a Spartan MLTT.
