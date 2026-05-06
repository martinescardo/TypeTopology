Martin Escardo 2011, 2017, 2018, 2020.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TypeTopology.ExtensionTotallySeparated where

open import MLTT.Spartan
open import TypeTopology.TotallySeparated
open import UF.FunExt

\end{code}

Closure under /-extensions defined in the module
InjectiveTypes. Notice that j doesn't need to be an embedding (in
which case the extension is merely a Kan extension rather than a
proper extension).

\begin{code}

module _ (fe : FunExt)  where

 private
  fe' : Fun-Ext
  fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 open import InjectiveTypes.Blackboard fe

 /-is-totally-separated : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                          (j : X → A)
                          (Y : X → 𝓦 ̇ )
                        → ((x : X) → is-totally-separated (Y x))
                        → (a : A) → is-totally-separated ((Y / j) a)
 /-is-totally-separated {𝓤} {𝓥} {𝓦} j Y t a =
  Π-is-totally-separated fe' (λ (σ : fiber j a) → t (pr₁ σ))

\end{code}
