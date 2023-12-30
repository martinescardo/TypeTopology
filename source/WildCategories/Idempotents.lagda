Jon Sterling and Mike Shulman, September 2023.

\begin{code}
{-# OPTIONS --safe --without-K #-}

module WildCategories.Idempotents where

open import MLTT.Spartan
open import UF.Base
open import UF.Subsingletons

open import WildCategories.Base

module _ {𝓤 𝓥} (C : WildCategory 𝓤 𝓥) where
 open WildCategory C

 record QuasiIdempotence (x : ob) (m : hom x x) : 𝓥 ̇ where
  field
   Q0 : m << m ＝ m
   Q1 : assoc m m m ∙ ap (_<< m) Q0 ＝ ap (m <<_) Q0

 record Splitting (x : ob) (m : hom x x) : 𝓤 ⊔ 𝓥 ̇ where
  field
   mid : ob
   sec : hom mid x
   ret : hom x mid
   sec-is-section : ret << sec ＝ idn mid
   splitting : sec << ret ＝ m

 quasi-idempotents-split : 𝓤 ⊔ 𝓥 ̇
 quasi-idempotents-split =
  (x : ob) (m : hom x x)
  → QuasiIdempotence x m
  → Splitting x m

\end{code}
