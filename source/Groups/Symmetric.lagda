Martin Escardo, 3rd November 2023.

The symmetric group on a set X, namely the group of automorphisms on X
under composition with the identity automorphism as the unit.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Groups.Symmetric (fe : Fun-Ext) where

open import Groups.Type
open import MLTT.Spartan
open import UF.Sets
open import UF.Equiv
open import UF.Equiv-FunExt

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

symmetric-group : (X : 𝓤 ̇ ) → is-set X → Group 𝓤
symmetric-group X X-is-set =
 Aut X ,
 _●_ ,
 ≃-is-set fe X-is-set ,
 (λ 𝕗 𝕘 𝕙 → (≃-assoc fe' 𝕗 𝕘 𝕙)⁻¹) ,
 𝕚𝕕 ,
 ≃-refl-left fe' ,
 ≃-refl-right fe' ,
 (λ 𝕗 → ≃-sym 𝕗 , ≃-sym-left-inverse fe' 𝕗 , ≃-sym-right-inverse fe' 𝕗)

\end{code}
