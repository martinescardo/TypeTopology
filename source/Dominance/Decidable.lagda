Martin Escardo, January 2018, May 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import Dominance.Definition
open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Dominance.Decidable where

 open import NotionsOfDecidability.DecidableAndDetachable

 decidable-dominance : Fun-Ext → Dominance {𝓤} {𝓤}
 decidable-dominance fe = (λ P → is-prop P × decidable P) ,
                          (λ P → Σ-is-prop
                                    (being-prop-is-prop fe)
                                    (decidability-of-prop-is-prop fe)) ,
                          (λ X → pr₁) ,
                          (𝟙-is-prop , inl ⋆) ,
                          λ P Q dP dQ → Σ-is-prop (pr₁ dP) (λ p → pr₁ (dQ p)) ,
                                         decidable-closed-under-Σ
                                           (pr₁ dP) (pr₂ dP) λ p → pr₂ (dQ p)

\end{code}
