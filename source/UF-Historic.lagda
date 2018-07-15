This is superseeded and not used any more.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Historic where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Yoneda
open import UF-Subsingletons-Equiv
open import UF-Equiv
open import UF-LeftCancellable
open import UF-FunExt
open import UF-Univalence
open import UF-PropTrunc

ip-ie-idtofun : ∀ {U} (fe : funext U U) (X Y : U ̇) (p : X ≡ Y) → is-prop(is-equiv(idtofun X Y p))
ip-ie-idtofun {U} fe X = Jbased X B go
 where
   B : (Y : U ̇) → X ≡ Y → U ̇
   B Y p = is-prop(is-equiv(idtofun X Y p))
   A = Σ \(f : X → X) → f ≡ id
   a : is-prop A
   a = is-singleton-is-prop (identifications-to-singleton id)
   A' = Σ \(f : X → X) → f ∼ id
   η : (f : X → X) → f ∼ id → f ≡ id
   η f = dfunext fe
   η-lc : (f : X → X) → left-cancellable(η f)
   η-lc f = funext-lc fe f id
   h : A' → A
   h = NatΣ η
   h-lc : left-cancellable h
   h-lc = NatΣ-lc (X → X) (λ f → f ∼ id) (λ f → f ≡ id) η η-lc
   b : is-prop A'
   b = left-cancellable-reflects-is-prop h h-lc a
   go : is-prop(A' × A')
   go = props-closed-× b b

jip : ∀ {U} → is-univalent U → funext U U → {X Y : U ̇}
   → (f : X → Y) → is-prop(is-equiv f)
jip {U} ua fe {X} {Y} f ije = h ije
  where
    e : X ≃ Y
    e = (f , ije)
    p : X ≡ Y
    p = eqtoid ua X Y e
    f' : X → Y
    f' = idtofun X Y p
    h' : is-prop(is-equiv f')
    h' = ip-ie-idtofun fe X Y p
    ije' : is-equiv f'
    ije' = Idtofun-is-equiv X Y p
    e' : X ≃ Y
    e' = f' , ije'
    q : e' ≡ e
    q = idtoeq-eqtoid ua X Y e
    q₁ : f' ≡ f
    q₁ = ap pr₁ q
    h : is-prop(is-equiv f)
    h = yoneda-nat f' (λ f → is-prop(is-equiv f)) h' f q₁

\end{code}
