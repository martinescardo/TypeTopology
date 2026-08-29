\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Retracts-FunExt where

open import MLTT.Spartan
open import UF.Retracts
open import UF.FunExt

retract-variance : ∀ {𝓣} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {X' : 𝓦 ̇ } {Y' : 𝓣 ̇ }
                 → funext 𝓤 𝓣
                 → retract X of X'
                 → retract Y' of Y
                 → retract (X → Y') of (X' → Y)
retract-variance
 {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {X'} {Y'} fe (rx , sx , rsx) (ry , sy , rsy) = γ
 where
  r : (X' → Y) → X → Y'
  r f x = ry (f (sx x))

  s : (X → Y') → X' → Y
  s f' x' = sy (f' (rx x'))

  rs' : (f' : X → Y') (x : X) → ry (sy (f' (rx (sx x)))) ＝ f' x
  rs' f' x = rsy (f' (rx (sx x))) ∙ ap f' (rsx x)

  rs : (f' : X → Y') → r (s f') ＝ f'
  rs f' = dfunext fe (rs' f')

  γ : retract (X → Y') of (X' → Y)
  γ = (r , s , rs)

retract-covariance : funext 𝓤 𝓦
                   → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Y' : 𝓦 ̇ }
                   → retract Y' of Y
                   → retract (X → Y') of (X → Y)
retract-covariance fe = retract-variance fe identity-retraction

retract-contravariance : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {X' : 𝓦 ̇ }
                       → funext 𝓤 𝓥
                       → retract X of X'
                       → retract (X → Y) of (X' → Y)
retract-contravariance fe rx = retract-variance fe rx identity-retraction

codomain-is-retract-of-function-space-with-pointed-domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                                          → X
                                                          → retract Y of (X → Y)
codomain-is-retract-of-function-space-with-pointed-domain x =
 ((λ f → f x) , ((λ y x → y) , λ y → refl))

retracts-of-closed-under-exponentials : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {B : 𝓦 ̇ }
                                      → funext 𝓦 𝓦
                                      → X
                                      → retract B of X
                                      → retract B of Y
                                      → retract B of (X → Y)
retracts-of-closed-under-exponentials {𝓤} {𝓥} {𝓦} {X} {Y} {B} fe x rbx rby = ii
 where
  i : retract (B → B) of (X → Y)
  i = retract-variance fe rbx rby

  ii : retract B of (X → Y)
  ii = retracts-compose i (codomain-is-retract-of-function-space-with-pointed-domain (pr₁ rbx x))

\end{code}
