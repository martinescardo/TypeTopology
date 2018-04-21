This is superseeded and not used any more.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Historic where

open import UF-Base
open import UF-Subsingletons
open import UF-Yoneda
open import UF-Retracts
open import UF-Subsingletons-Retracts
open import UF-Subsingletons-Equiv
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-LeftCancellable
open import UF-FunExt
open import UF-Univalence
open import UF-Embedding
open import UF-Subsingletons-FunExt
open import UF-Prop
open import UF-PropTrunc

ip-ie-idtofun : ∀ {U} (fe : FunExt U U) (X Y : U ̇) (p : X ≡ Y) → isProp(isEquiv(idtofun X Y p))
ip-ie-idtofun {U} fe X = Jbased X B go
 where
   B : (Y : U ̇) → X ≡ Y → U ̇
   B Y p = isProp(isEquiv(idtofun X Y p))
   A = Σ \(f : X → X) → f ≡ id
   a : isProp A
   a = isSingleton-isProp (paths-to-contractible id)
   A' = Σ \(f : X → X) → f ∼ id
   η : (f : X → X) → f ∼ id → f ≡ id
   η f = funext fe
   η-lc : (f : X → X) → left-cancellable(η f)
   η-lc f = funext-lc fe f id
   h : A' → A
   h = NatΣ η
   h-lc : left-cancellable h
   h-lc = NatΣ-lc (X → X) (λ f → f ∼ id) (λ f → f ≡ id) η η-lc
   b : isProp A'
   b = left-cancellable-reflects-isProp h h-lc a
   go : isProp(A' × A')
   go = props-closed-× b b

jip : ∀ {U} → isUnivalent U → FunExt U U → {X Y : U ̇} 
   → (f : X → Y) → isProp(isEquiv f) 
jip {U} ua fe {X} {Y} f ije = h ije
  where
    e : X ≃ Y
    e = (f , ije)
    p : X ≡ Y
    p = eqtoid ua X Y e
    f' : X → Y
    f' = idtofun X Y p
    h' : isProp(isEquiv f')
    h' = ip-ie-idtofun fe X Y p
    ije' : isEquiv f'
    ije' = idtofun-isEquiv X Y p
    e' : X ≃ Y
    e' = f' , ije'
    q : e' ≡ e
    q = idtoeq-eqtoid ua X Y e
    q₁ : f' ≡ f
    q₁ = ap pr₁ q
    h : isProp(isEquiv f)
    h = yoneda-nat (λ f → isProp(isEquiv f)) h' f q₁

\end{code}
