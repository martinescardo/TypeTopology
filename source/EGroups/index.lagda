Martin Escardo, 15th July 2026.

Free groups in pure MLTT using setoids. More precisely, we work with
egroups, defined in EGroup.Type, briefly described below.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EGroups.index where

import EGroups.Setoid
import EGroups.Type
import EGroups.MediatingMap
import EGroups.FreeOnType
import EGroups.FreeOnSetoid
import EGroups.FromGroup

\end{code}

 * Setoid

   The notion of setoid (a type with an equivalence relation given as
   data, not required to be proposition-valued) and the generic setoid
   infrastructure: the relation-relative algebraic predicates,
   equational reasoning, setoid maps, setoid isomorphism, and the
   function setoid.

 * Type

   The type of egroups: setoids equipped with a compatible group
   structure, with the group laws holding up to the equivalence
   relation rather than up to the identity type. Homomorphisms and some
   minimal group theory up to the equivalence relation.

 * MediatingMap

   Defines the mediating map into a target egroup and proves its basic
   properties, with the target's laws holding up to an arbitrary
   equivalence relation. This is the map underlying the universal
   property; the word-level construction it acts on is imported from
   Groups.Free.

 * FreeOnType

   The free egroup on a type, its universal property, and the
   free-forgetful adjunction expressed as a setoid isomorphism of
   hom-setoids.

 * FreeOnSetoid

   The free egroup on a setoid, rather than on a type, and the
   free-forgetful adjunction between setoids and egroups, as a setoid
   isomorphism of hom-setoids.

 * FromGroup

   Every group, in the sense of Groups.Type, is an egroup, with the
   identity type as its equivalence relation.
