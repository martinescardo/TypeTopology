Martin Escardo

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Sets-Properties where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.Hedberg
open import UF.LeftCancellable
open import UF.Retracts
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

subtypes-of-sets-are-sets' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
                           → left-cancellable m
                           → is-set Y
                           → is-set X
subtypes-of-sets-are-sets' {𝓤} {𝓥} {X} m i h = Id-collapsibles-are-sets (f , g)
 where
  f : {x x' : X} → x ＝ x' → x ＝ x'
  f r = i (ap m r)

  g : {x x' : X} (r s : x ＝ x') → f r ＝ f s
  g r s = ap i (h (ap m r) (ap m s))

retract-of-set : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → retract X of Y
               → is-set Y
               → is-set X
retract-of-set {𝓤} {𝓥} {X} (r , s , rs) =
 subtypes-of-sets-are-sets' s (sections-are-lc s (r , rs))

subsets-of-sets-are-sets : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
                         → is-set X
                         → ({x : X} → is-prop (Y x))
                         → is-set (Σ x ꞉ X , Y x)
subsets-of-sets-are-sets X Y h p = subtypes-of-sets-are-sets' pr₁ (pr₁-lc p) h

Π-is-set : funext 𝓤 𝓥
         → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
         → ((x : X) → is-set (A x))
         → is-set (Π A)
Π-is-set {𝓤} {𝓥} fe {X} {A} isa {f} {g} = b
 where
  a : is-prop (f ∼ g)
  a p q = dfunext fe λ x → isa x (p x) (q x)

  b : is-prop (f ＝ g)
  b = left-cancellable-reflects-is-prop
       happly
       (section-lc happly (pr₂ (fe f g)))
       a

equiv-to-set : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → X ≃ Y
             → is-set Y
             → is-set X
equiv-to-set e = subtypes-of-sets-are-sets' ⌜ e ⌝
                  (equivs-are-lc ⌜ e ⌝ (⌜⌝-is-equiv e))

\end{code}

The crucial lemma of the following proof is being-set-is-prop'. The
rest of the code is to deal with implicit arguments in conjunction
with function extensionality. The solution is not ideal. Ideally,
functions with implicit parameters should be the same as their
versions with explicit parameters.

\begin{code}

being-set-is-prop : funext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-prop (is-set X)
being-set-is-prop {𝓤} fe {X} = h
 where
  is-set' : 𝓤 ̇ → 𝓤 ̇
  is-set' X = (x y : X) → is-prop (x ＝ y)

  being-set-is-prop' : {X : 𝓤 ̇ } → funext 𝓤 𝓤 → is-prop (is-set' X)
  being-set-is-prop' fe = Π-is-prop fe
                           (λ x → Π-is-prop fe
                           (λ y → being-prop-is-prop fe))

  f : {X : 𝓤 ̇ } → is-set' X → is-set X
  f s {x} {y} = s x y

  g : {X : 𝓤 ̇ } → is-set X → is-set' X
  g s x y = s {x} {y}

  h : is-prop (is-set X)
  h = subtypes-of-props-are-props' g (ap f) (being-set-is-prop' fe)

Σ-is-set : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
         → is-set X
         → ((x : X) → is-set (A x))
         → is-set (Σ A)
Σ-is-set {𝓤} {𝓥} {X} {A} i j {σ} {τ} = γ
 where
  S = Σ p ꞉ pr₁ σ ＝ pr₁ τ , transport A p (pr₂ σ) ＝ pr₂ τ

  a : is-prop S
  a = Σ-is-prop i (λ p → j (pr₁ τ))

  b : retract (σ ＝ τ) of S
  b = to-Σ-＝ , from-Σ-＝ , tofrom-Σ-＝

  γ : is-prop (σ ＝ τ)
  γ = retract-of-prop b a

\end{code}
