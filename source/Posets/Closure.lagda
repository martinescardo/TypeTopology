We define closure operators on a poset as a monotone increasing function 𝑓
such that 𝑓(𝑥) ≥ 𝑥 and 𝑓(𝑓(𝑥)) = 𝑓(𝑥).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Posets.Closure
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where
open import Posets.Poset fe

module Closure
        {D : 𝓤 ̇ }
        (_⊑_ : D → D → 𝓣 ̇ )
        (f : D → D)
       where
  closure-η = ∀ x → x ⊑ f x
  closure-μ = ∀ x → f (f x) ⊑ f x

  open PosetAxioms _⊑_  -- TODO bundle more things

  idempotent
    : closure-η
    → closure-μ
    → is-antisymmetric
    → ∀ x → f (f x) ＝ f x
  idempotent η μ a x = a _ _ (μ _) (η _)
\end{code}


If we have a closure operator on a suplattice, then the image is
also a suplattice.

\begin{code}
open import Posets.FreeSupLattice pt
-- TODO we don't want the "free" part, factor the definition out
module _ (𝕃 : SupLattice 𝓤 𝓥 𝓦) where
 module 𝕃 = SupLattice 𝕃
 open Closure 𝕃._⊑_

 module SupLattice-Closure
  {D : 𝓤 ̇ }
  (_⊑_ : D → D → 𝓣 ̇ )
  (f : 𝕃.L → D)
  (f-is-monotone : ∀ x y → x 𝕃.⊑ y → f x ⊑ f y)
  (ι : D → 𝕃.L)
  (ι-is-monotome : ∀ x y → x ⊑ y → ι x 𝕃.⊑ ι y)
  (ι∘f-closure-η : closure-η (ι ∘ f))
  (ι∘f-closure-μ : closure-μ (ι ∘ f)) where


\end{code}
