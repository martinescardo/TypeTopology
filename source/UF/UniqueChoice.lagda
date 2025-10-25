Ian Ray, 24 October 2025.

We prove the principle of unique choice in the presence of function
extensionality.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.UniqueChoice where

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

\end{code}

TypeTopology has a clever formulation of unique existence but we show it
is equivalent to a more niave notion when the family is propositional and
function extensionality is assumed.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 ∃!-implies-∃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇}
              → ∃! A → ∃ A
 ∃!-implies-∃ (c , C) = ∣ c ∣

 ∃'! : {X : 𝓤 ̇ }
     → (A : X → 𝓥 ̇)
     → 𝓤 ⊔ 𝓥 ̇
 ∃'! {_} {_} {X} A = ∃ A × ∥ ((x x' : X) → A x → A x' → x ＝ x') ∥

 ∃'!-is-prop : {X : 𝓤 ̇ } {A : X → 𝓥 ̇} 
             → is-prop (∃'! A)
 ∃'!-is-prop {_} {_} {_} {_} 
  = ×-is-prop ∃-is-prop ∥∥-is-prop

 ∃!-to-∃'! : {X : 𝓤 ̇ } {A : X → 𝓥 ̇}
           → ∃! A → ∃'! A 
 ∃!-to-∃'! {_} {_} {_} {A} x
  = ∃!-implies-∃ x , ∣ witness-uniqueness A x ∣

 ∃'!-to-∃! : {X : 𝓤 ̇ } {A : X → 𝓥 ̇} {p : (x : X) → is-prop (A x)}
           → Fun-Ext
           → ∃'! A → ∃! A
 ∃'!-to-∃! {_} {_} {X} {A} {p} fe
  = uncurry (∥∥-rec₂ (being-singleton-is-prop fe) I)
  where
   I : Σ A → ((x x' : X) → A x → A x' → x ＝ x') → ∃! A
   I (x , a) u = ((x , a) , II)
    where
     II : is-central (Σ A) (x , a)
     II (x' , a') = to-subtype-＝ p (u x x' a a')

 ∃!-≃-∃'! : {X : 𝓤 ̇ } {A : X → 𝓥 ̇} {p : (x : X) → is-prop (A x)}
          → Fun-Ext
          → ∃! A ≃ ∃'! A
 ∃!-≃-∃'! {_} {_} {_} {_} {p} fe
  = logically-equivalent-props-are-equivalent (being-singleton-is-prop fe)
     ∃'!-is-prop ∃!-to-∃'! (∃'!-to-∃! {_} {_} {_} {_} {p} fe)

\end{code}

We establish an analog of the "set-theoretic principle of unique choice" from
function extensionality.

\begin{code}

PUC : (X : 𝓤 ̇) (Y : 𝓥 ̇) (R : X → Y → 𝓣 ̇) (p : (x : X) (y : Y) → is-prop (R x y))
    → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
PUC X Y R p
 = ((x : X) → ∃! y ꞉ Y , R x y) → ∃! f ꞉ (X → Y) , ((x : X) → R x (f x))

puc : {X : 𝓤 ̇} {Y : 𝓥 ̇} {R : X → Y → 𝓣 ̇} {p : (x : X) (y : Y) → is-prop (R x y)}
    → FunExt
    → PUC X Y R p
puc {_} {_} {_} {X} {Y} {R} {p} fe m = ((f , r) , G)
 where
  f : X → Y
  f x = ∃!-witness (m x)
  r : (x : X) → R x (f x)
  r x = ∃!-is-witness (m x)
  C : (x : X) (y : Y) (a : R x y) → (f x , r x) ＝ (y , a)
  C x = ∃!-uniqueness (m x)
  G : ((g , s) : (Σ g ꞉ (X → Y) , ((x : X) → R x (g x))))
    → (f , r) ＝ (g , s)
  G (g , s) = to-subtype-＝ II (dfunext (fe _ _) I)
   where
    I : f ∼ g
    I x = ap pr₁ (C x (g x) (s x))
    II : (h : X → Y) → is-prop ((x : X) → R x (h x))
    II = λ h → Π-is-prop (fe _ _) (λ x → p x (h x))
    
\end{code}
