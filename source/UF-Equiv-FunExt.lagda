Properties of equivalences depending on function extensionality.

(Not included in UF-Equiv because the module FunExt defines function
extensionality as the equivalence of happly for suitable parameters.)

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Equiv-FunExt where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Retracts
open import UF-Subsingletons-Retracts
open import UF-FunExt
open import UF-Equiv

isProp-isVoevodskyEquiv : (∀ U V → FunExt U V) → ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                        → isProp(isVoevodskyEquiv f)
isProp-isVoevodskyEquiv fe {U} {V} f = isProp-exponential-ideal
                                         (fe V (U ⊔ V))
                                         (λ x → isProp-isSingleton (fe (U ⊔ V) (U ⊔ V)))

qinv-post : (∀ U V → FunExt U V) → ∀ {U} {V} {W} {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → Y)
          → qinv f → qinv (λ (h : A → X) → f ∘ h)
qinv-post fe {U} {V} {W} {X} {Y} {A} f (g , η , ε) = (g' , η' , ε')
 where
  f' : (A → X) → (A → Y)
  f' h = f ∘ h
  g' : (A → Y) → (A → X)
  g' k = g ∘ k
  η' : (h : A → X) → g' (f' h) ≡ h
  η' h = funext (fe W U) (η ∘ h)
  ε' : (k : A → Y) → f' (g' k) ≡ k
  ε' k = funext (fe W V) (ε ∘ k)
  
qinv-pre : (∀ U V → FunExt U V) → ∀ {U} {V} {W} {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → Y)
         → qinv f → qinv (λ (h : Y → A) → h ∘ f)
qinv-pre fe {U} {V} {W} {X} {Y} {A} f (g , η , ε) = (g' , η' , ε')
 where
  f' : (Y → A) → (X → A)
  f' h = h ∘ f
  g' : (X → A) → (Y → A)
  g' k = k ∘ g
  η' : (h : Y → A) → g' (f' h) ≡ h
  η' h = funext (fe V W) (λ y → ap h (ε y))
  ε' : (k : X → A) → f' (g' k) ≡ k
  ε' k = funext (fe U W) (λ x → ap k (η x))

hasr-isprop-hass : (∀ U V → FunExt U V) → ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
                 → hasRetraction f → isProp(hasSection f)
hasr-isprop-hass fe {U} {V} {X} {Y} f (g , gf) (h , fh) = isSingleton-isProp c (h , fh)
 where
  a : qinv f
  a = isEquiv-qinv f ((h , fh) , g , gf)
  b : isSingleton(fiber (λ h →  f ∘ h) id)
  b = qinv-isVoevodsky (λ h →  f ∘ h) (qinv-post fe f a) id
  r : fiber (λ h →  f ∘ h) id → hasSection f
  r (h , p) = (h , happly' (f ∘ h) id p)
  s : hasSection f → fiber (λ h →  f ∘ h) id
  s (h , η) = (h , funext (fe V V) η)
  rs : (σ : hasSection f) → r (s σ) ≡ σ
  rs (h , η) = ap (λ η → (h , η)) q
   where
    q : happly' (f ∘ h) id (funext (fe V V) η) ≡ η
    q = happly-funext (fe V V) (f ∘ h) id η
  c : isSingleton (hasSection f)
  c = retract-of-singleton r (s , rs) b

hass-isprop-hasr : (∀ U V → FunExt U V) → ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
                 → hasSection f → isProp(hasRetraction f)
hass-isprop-hasr fe {U} {V} {X} {Y} f (g , fg) (h , hf) = isSingleton-isProp c (h , hf)
 where
  a : qinv f
  a = isEquiv-qinv f ((g , fg) , (h , hf))
  b : isSingleton(fiber (λ h →  h ∘ f) id)
  b = qinv-isVoevodsky (λ h →  h ∘ f) (qinv-pre fe f a) id
  r : fiber (λ h →  h ∘ f) id → hasRetraction f
  r (h , p) = (h , happly' (h ∘ f) id p)
  s : hasRetraction f → fiber (λ h →  h ∘ f) id
  s (h , η) = (h , funext (fe U U) η) 
  rs : (σ : hasRetraction f) → r (s σ) ≡ σ
  rs (h , η) = ap (λ η → (h , η)) q
   where
    q : happly' (h ∘ f) id (funext (fe U U) η) ≡ η
    q = happly-funext (fe U U) (h ∘ f) id η
  c : isSingleton (hasRetraction f)
  c = retract-of-singleton r (s , rs) b

isEquiv-isProp : (∀ U V → FunExt U V) → ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y)
               → isProp(isEquiv f)
isEquiv-isProp fe f = ×-prop-criterion (hasr-isprop-hass fe f , hass-isprop-hasr fe f)

\end{code}
