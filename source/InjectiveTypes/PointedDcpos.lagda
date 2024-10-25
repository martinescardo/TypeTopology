Tom de Jong and Martín Escardó, 18 January 2024.

The carrier of a pointed dcpo is an algebraically injective type.

More precisely, if 𝓓 is a poset with a least element and suprema for directed
families indexed by types in a universe 𝓥, then the carrier of 𝓓 is
algebraically injective with respect to embeddings of types in 𝓥.

We emphasize that this does *not* mean that pointed dcpos are injective in the
category of dcpos and continuous maps (which they are not). For this reason we
explicitly talk about the carrier of a pointed dcpo above.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.FunExt
open import UF.PropTrunc

module InjectiveTypes.PointedDcpos
        (fe : FunExt)
        (pt : propositional-truncations-exist)
        (𝓥 : Universe)
       where

private
 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import DomainTheory.Basics.Pointed pt fe' 𝓥
open import InjectiveTypes.Blackboard fe

pointed-dcpos-are-aflabby-types : (𝓓 : DCPO⊥ {𝓤} {𝓣}) → aflabby ⟪ 𝓓 ⟫ 𝓥
pointed-dcpos-are-aflabby-types 𝓓 P P-is-prop f = I , II
 where
  I : ⟪ 𝓓 ⟫
  I = ∐ˢˢ 𝓓 f P-is-prop
  II : (p : P) → I ＝ f p
  II p = ∐ˢˢ-＝-if-domain-holds 𝓓 P-is-prop p

pointed-dcpos-are-ainjective-types :
 (𝓓 : DCPO⊥ {𝓤} {𝓣}) → ainjective-type ⟪ 𝓓 ⟫ 𝓥 𝓥
pointed-dcpos-are-ainjective-types 𝓓 =
 aflabby-types-are-ainjective ⟪ 𝓓 ⟫ (pointed-dcpos-are-aflabby-types 𝓓)

\end{code}
