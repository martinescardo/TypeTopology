\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Retracts-FunExt where

open import SpartanMLTT
open import UF-Base
open import UF-Retracts
open import UF-FunExt

rexp : ∀ {𝓣} {X : 𝓤 ̇ } {Y : 𝓥 ̇} {X' : 𝓦 ̇} {Y' : 𝓣 ̇} → funext 𝓤 𝓣
    → retract X of X' → retract Y' of Y → retract (X → Y') of (X' → Y)
rexp {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {X'} {Y'} fe (rx , (sx , rsx)) (ry , (sy , rsy)) = (r , (s , rs))
 where
  r : (X' → Y) → X → Y'
  r f x = ry (f (sx x))
  s : (X → Y') → X' → Y
  s f' x' = sy (f' (rx x'))
  rs' : (f' : X → Y') (x : X) → ry (sy (f' (rx (sx x)))) ≡ f' x
  rs' f' x = rsy (f' (rx (sx x))) ∙ ap f' (rsx x)
  rs : (f' : X → Y') → r (s f') ≡ f'
  rs f' = dfunext fe (rs' f')

rpe : {X : 𝓤 ̇ } {Y : 𝓥 ̇} {Y' : 𝓦 ̇} → funext 𝓤 𝓦
    → retract Y' of Y → retract (X → Y') of (X → Y)
rpe fe = rexp fe identity-retraction

crpe : {X : 𝓤 ̇ } {Y : 𝓥 ̇} {X' : 𝓦 ̇} → funext 𝓤 𝓥
    → retract X of X' → retract (X → Y) of (X' → Y)
crpe fe rx = rexp fe rx identity-retraction

pdrc : {X : 𝓤 ̇ } {Y : 𝓥 ̇} → X → retract Y of (X → Y)
pdrc x = ((λ f → f x) , ((λ y x → y) , λ y → refl))

retracts-of-closed-under-exponentials : {X : 𝓤 ̇ } {Y : 𝓥 ̇} {B : 𝓦 ̇} → funext 𝓦 𝓦
                                      → X → retract B of X → retract B of Y → retract B of (X → Y)
retracts-of-closed-under-exponentials {𝓤} {𝓥} {𝓦} {X} {Y} {B} fe x rbx rby = rbxy
 where
  rbbxy : retract (B → B) of (X → Y)
  rbbxy = rexp fe rbx rby
  rbxy : retract B of (X → Y)
  rbxy = retracts-compose rbbxy (pdrc (pr₁ rbx x))

\end{code}

TODO. Several retractions here are actually equivalences. So some code
should be generalized and moved to an equivalences module. Similarly,
some retracts proved here are also shown as equivalences in other
modules, and hence there is some amount of repetition that should be
removed. This is the result of (1) merging initially independent
developments, and (2) work over many years with uncontrolled growth.
