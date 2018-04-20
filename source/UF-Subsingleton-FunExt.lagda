In univalent logic, as opposed to Curry-Howard logic, a proposition is
a subsingleton or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

About (sub)singletons using function extensionality.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Subsingleton-FunExt where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-FunExt
open import UF-LeftCancellable
open import UF-Equiv

isProp-exponential-ideal : ∀ {U V} → FunExt U V → {X : U ̇} {A : X → V ̇} 
                        → ((x : X) → isProp(A x)) → isProp(Π A) 
isProp-exponential-ideal {U} {V} fe {X} {A} isa f g = funext fe (λ x → isa x (f x) (g x))

isProp-isProp : ∀ {U} {X : U ̇} → FunExt U U → isProp(isProp X)
isProp-isProp {U} {X} fe f g = claim₁
 where
  lemma : isSet X
  lemma = prop-isSet f
  claim : (x y : X) → f x y ≡ g x y
  claim x y = lemma (f x y) (g x y)
  claim₀ : (x : X) → f x ≡ g x 
  claim₀ x = funext fe (claim x) 
  claim₁ : f ≡ g
  claim₁  = funext fe claim₀

isProp-isSingleton : ∀ {U} {X : U ̇} → FunExt U U → isProp(isSingleton X)
isProp-isSingleton {U} {X} fe (x , φ) (y , γ) = to-Σ-≡'' (φ y , funext fe λ z → iss {y} {z} _ _)
 where
  isp : isProp X
  isp = isSingleton-isProp (y , γ)
  iss : isSet X
  iss = prop-isSet isp

isSet-exponential-ideal : ∀ {U V} → FunExt U V → {X : U ̇} {A : X → V ̇} 
                        → ((x : X) → isSet(A x)) → isSet(Π A) 
isSet-exponential-ideal {U} {V} fe {X} {A} isa {f} {g} = b
 where
  a : isProp (f ∼ g)
  a p q = funext fe λ x → isa x (p x) (q x)
  b : isProp(f ≡ g)
  b = left-cancellable-reflects-isProp happly (section-lc happly (pr₂ (fe f g))) a

isProp-isVoevodskyEquiv : (∀ U V → FunExt U V) → ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                        → isProp(isVoevodskyEquiv f)
isProp-isVoevodskyEquiv fe {U} {V} f = isProp-exponential-ideal
                                         (fe V (U ⊔ V))
                                         (λ x → isProp-isSingleton (fe (U ⊔ V) (U ⊔ V)))

\end{code}

The following code is used to make Agda work with the constructions we
have given. We make the implicit arguments explicit in the definition
of isSet.

\begin{code}

isSet' : ∀ {U} → U ̇ → U ̇
isSet' X = (x y : X) → isProp(x ≡ y)

isSet'-isSet : ∀ {U} {X : U ̇} → isSet' X → isSet X
isSet'-isSet s {x} {y} = s x y

isSet-isSet' : ∀ {U} {X : U ̇} → isSet X → isSet' X
isSet-isSet' s x y = s {x} {y}

isProp-isSet' : ∀ {U} {X : U ̇} → FunExt U U → isProp (isSet' X)
isProp-isSet' fe = isProp-exponential-ideal fe
                    (λ x → isProp-exponential-ideal fe
                              (λ y → isProp-isProp fe))

\end{code}

\begin{code}

sum-of-contradictory-props : ∀ {U V} {P : U ̇} {Q : V ̇}
                           → isProp P → isProp Q → (P → Q → 𝟘) → isProp(P + Q)
sum-of-contradictory-props {U} {V} {P} {Q} isp isq f = go
  where
   go : (x y : P + Q) → x ≡ y
   go (inl p) (inl p') = ap inl (isp p p')
   go (inl p) (inr q)  = 𝟘-elim (f p q)
   go (inr q) (inl p)  = 𝟘-elim (f p q)
   go (inr q) (inr q') = ap inr (isq q q')

decidable-isProp : ∀ {U} {P : U ̇} → FunExt U U₀ → isProp P → isProp(P + ¬ P)
decidable-isProp fe₀ isp = sum-of-contradictory-props
                             isp
                             (isProp-exponential-ideal fe₀ λ _ → 𝟘-isProp)
                             (λ p u → u p)

\end{code}
