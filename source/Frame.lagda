Ayberk Tosun
Ported from `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-PropTrunc
open import UF-FunExt
open import UF-PropTrunc

module Frame
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

\end{code}

\section{Preliminaries}

By Fam_𝓤(A), we denote the type of families on type A with index types
living in universe 𝓤.

\begin{code}

private
  variable
    𝓤′ 𝓥′ 𝓦′ : Universe

Fam : (𝓤 : Universe) → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
Fam 𝓤 A = Σ I ꞉ (𝓤 ̇) , (I → A)

fmap-syntax : {A : 𝓤 ̇} {B : 𝓥 ̇}
            → (A → B) → Fam 𝓦 A → Fam 𝓦 B
fmap-syntax h (I , f) = I , h ∘ f

infix 2 fmap-syntax

syntax fmap-syntax (λ x → e) U = ⁅ e ∣ x ε U ⁆

infixr 4 _∧_

_∧_ : Ω 𝓤 → Ω 𝓥 → Ω (𝓤 ⊔ 𝓥)
P ∧ Q = (P holds × Q holds) , γ
 where
  γ = ×-is-prop (holds-is-prop P) (holds-is-prop Q)

infix 3 forall-syntax

forall-syntax : (I : 𝓤 ̇) → (I → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
forall-syntax I P = ((i : I) → P i holds) , γ
 where
 γ : is-prop ((i : I) → P i holds)
 γ = Π-is-prop fe (holds-is-prop ∘ P)

forall₂-syntax : (I : 𝓤 ̇) → (I × I → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
forall₂-syntax I P =
 forall-syntax I λ i → forall-syntax I λ j → P (i , j)

syntax forall-syntax I (λ i → e) = ∀[ i ∶ I ] e

\end{code}

We define two projections for families: (1) for the index type,
and (2) for the enumeration function.

\begin{code}

index : {A : 𝓤 ̇} → Fam 𝓥 A → 𝓥 ̇
index (I , _) = I

_[_] : {A : 𝓤 ̇} → (U : Fam 𝓥 A) → index U → A
(_ , f) [ i ] = f i

infixr 9 _[_]

\end{code}

We define some order-theoretic notions that are also defined in the
`Dcpo` module. Ideally, this should be factored out into a standalone
module to be imported by both this module and the `Dcpo` module.

\begin{code}

is-reflexive : {A : 𝓤 ̇} → (A → A → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
is-reflexive {A = A} _≤_ = ((x : A) → (x ≤ x) holds) , γ
 where
  γ : is-prop ((x : A) → (x ≤ x) holds)
  γ = Π-is-prop fe λ x → holds-is-prop (x ≤ x)

is-transitive : {A : 𝓤 ̇} → (A → A → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
is-transitive {A = A} _≤_ = P , γ
 where
  P = (x y z : A) → (x ≤ y) holds → (y ≤ z) holds → (x ≤ z) holds

  γ : is-prop P
  γ = Π-is-prop fe λ x →
       Π-is-prop fe λ _ →
        Π-is-prop fe λ z →
         Π-is-prop fe λ _ →
          Π-is-prop fe λ _ → holds-is-prop (x ≤ z)

is-antisymmetric : ((A , _) : hSet 𝓤) → (A → A → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
is-antisymmetric {𝓤 = 𝓤} {𝓥} (A , iss) _≤_ = P , γ
 where
  P : 𝓤 ⊔ 𝓥 ̇
  P = (x y z : A) → (x ≤ y) holds → (y ≤ x) holds → x ≡ y

  γ : is-prop P
  γ = Π-is-prop fe λ _ →
       Π-is-prop fe λ _ →
        Π-is-prop fe λ _ →
         Π-is-prop fe λ _ →
          Π-is-prop fe λ _ → iss

is-partial : ((A , _) : hSet 𝓤) → (A → A → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
is-partial {_} {_} A _≤_ =
 is-reflexive _≤_ ∧ is-transitive _≤_ ∧ is-antisymmetric A _≤_

\end{code}

\section{Definition of poset}

A (𝓤, 𝓥)-poset is a poset whose

  - carrier lives in universe 𝓤, and
  - whose relation lives in universe 𝓥.

\begin{code}

poset-structure : (𝓥 : Universe) → hSet 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
poset-structure 𝓥 (A , iss) =
 Σ _≤_ ꞉ (A → A → Ω 𝓥) , (is-partial (A , iss) _≤_ holds)

poset : (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
poset 𝓤 𝓥 = Σ A ꞉ hSet 𝓤 , poset-structure 𝓥 A

∣_∣ₚ : poset 𝓤 𝓥 → 𝓤 ̇
∣ (A , _) , _ ∣ₚ = A

rel-syntax : (P : poset 𝓤 𝓥)  → ∣ P ∣ₚ → ∣ P ∣ₚ → Ω 𝓥
rel-syntax (_ , _≤_ , _) = _≤_

syntax rel-syntax P x y = x ≤[ P ] y

≤-is-transitive : (P : poset 𝓤 𝓥)
                → is-transitive (λ x y → x ≤[ P ] y) holds
≤-is-transitive (_ , _ , (_ , t , _)) = t

≤-is-reflexive : (P : poset 𝓤 𝓥)
               → is-reflexive (λ x y → x ≤[ P ] x) holds
≤-is-reflexive (_ , _ , (r , _ , _)) = r

carrier-of-[_]-is-set : (P : poset 𝓤 𝓥) → is-set ∣ P ∣ₚ
carrier-of-[_]-is-set ((_ , iss) , _)= iss

\end{code}

Some convenient syntax for reasoning with posets.

\begin{code}

module PosetNotation (P : poset 𝓤 𝓥) where

  _≤_ : ∣ P ∣ₚ → ∣ P ∣ₚ → Ω 𝓥
  x ≤ y = x ≤[ P ] y

  infixr 4 _≤_

module PosetReasoning (P : poset 𝓤 𝓥) where

 open PosetNotation P using (_≤_)

 _≤⟨_⟩_ : (x : ∣ P ∣ₚ) {y z : ∣ P ∣ₚ}
        → (x ≤ y) holds → (y ≤ z) holds → (x ≤ z) holds
 x ≤⟨ p ⟩ q = ≤-is-transitive P _ _ _ p q

 _■ : (x : ∣ P ∣ₚ) → (x ≤ x) holds
 _■ = ≤-is-reflexive P

 infixr 0 _≤⟨_⟩_
 infix  1 _■

module HSetNotation ((A , iss) : hSet 𝓤) where

 infix 1 _≣_

 _≣_ : A → A → Ω 𝓤
 x ≣ y = (x ≡ y) , iss

\end{code}

\section{Meets}

\begin{code}

module Meets {A : 𝓤 ̇} (_≤_ : A → A → Ω 𝓥) where

 is-top : A → Ω (𝓤 ⊔ 𝓥)
 is-top t = ((x : A) → (x ≤ t) holds) , γ
   where
   γ : is-prop ((x : A) → (x ≤ t) holds)
   γ = Π-is-prop fe λ x → holds-is-prop (x ≤ t)

 _is-a-lower-bound-of_ : A → A × A → Ω 𝓥
 l is-a-lower-bound-of (x , y) = (l ≤ x) ∧ (l ≤ y)

 lower-bound : A × A → 𝓤 ⊔ 𝓥 ̇
 lower-bound (x , y) =
   Σ l ꞉ A , (l is-a-lower-bound-of (x , y)) holds

 _is-glb-of_ : A → A × A → Ω (𝓤 ⊔ 𝓥)
 l is-glb-of (x , y) = l is-a-lower-bound-of (x , y)
                     ∧ (∀[ (l′ , _) ∶ lower-bound (x , y) ] (l′ ≤ l))

\end{code}

\section{Joins}

\begin{code}

module Joins {A : 𝓤 ̇} (_≤_ : A → A → Ω 𝓥) where

 _is-an-upper-bound-of_ : A → Fam 𝓦 A → Ω (𝓥 ⊔ 𝓦)
 u is-an-upper-bound-of U = Q , γ
  where
   Q = (i : index U) → ((U [ i ]) ≤ u) holds
   γ = Π-is-prop fe λ i → holds-is-prop ((U [ i ]) ≤ u)

 upper-bound : Fam 𝓦 A → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 upper-bound U = Σ u ꞉ A , (u is-an-upper-bound-of U) holds

 _is-lub-of_ : A → Fam 𝓦 A → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
 u is-lub-of U = (u is-an-upper-bound-of U)
               ∧ (∀[ (u′ , _) ∶ upper-bound U ] (u ≤ u′))

module JoinNotation {A : 𝓤 ̇} (⋁_ : Fam 𝓦 A → A) where

 join-syntax : (I : 𝓦 ̇) → (I → A) → A
 join-syntax I f = ⋁ (I , f)

 ⋁⟨⟩-syntax : {I : 𝓦 ̇} → (I → A) → A
 ⋁⟨⟩-syntax {I = I} f = join-syntax I f

 infix 2 join-syntax
 infix 2 ⋁⟨⟩-syntax

 syntax join-syntax I (λ i → e) = ⋁⟨ i ∶ I ⟩ e
 syntax ⋁⟨⟩-syntax    (λ i → e) = ⋁⟨ i ⟩ e

\end{code}

\section{Definition of frame}

A (𝓤, 𝓥, 𝓦)-frame is a frame whose

  - carrier lives in universe 𝓤,
  - order lives in universe 𝓥, and
  - index types live in universe 𝓦.

\begin{code}

frame-data : (𝓥 𝓦 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
frame-data 𝓥 𝓦 A = (A → A → Ω 𝓥)   -- order
                 × A               -- top element
                 × (A → A → A)     -- binary meets
                 × (Fam 𝓦 A → A)   -- arbitrary joins
                 × is-set A        -- carrier is a set

satisfies-frame-laws : {A : 𝓤 ̇} → frame-data 𝓥 𝓦 A → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
satisfies-frame-laws {𝓦 = 𝓦} {A = A}  (_≤_ , 𝟏 , _⊓_ , ⊔_ , iss) =
 partial ∧ top ∧ meets ∧ joins ∧ distributivity
 where
  open HSetNotation (A , iss)
  open Meets _≤_
  open Joins _≤_
  open JoinNotation ⊔_

  partial        = is-partial (A , iss) _≤_
  top            = is-top 𝟏
  meets          = ∀[ (x , y) ∶ (A × A) ] ((x ⊓ y) is-glb-of (x , y))
  joins          = ∀[ U ∶ Fam 𝓦 A ] (⊔ U) is-lub-of U
  distributivity = ∀[ (x , U) ∶ A × Fam 𝓦 A ]
                    (x ⊓ (⋁⟨ i ⟩ U [ i ]) ≣ ⋁⟨ i ⟩ x ⊓ (U [ i ]) )

frame-structure : (𝓥 𝓦 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
frame-structure 𝓥 𝓦 A =
  Σ d ꞉ (frame-data 𝓥 𝓦 A) , satisfies-frame-laws d holds

\end{code}

The type of (𝓤, 𝓥, 𝓦)-frames is then defined as:

\begin{code}

frame : (𝓤 𝓥 𝓦 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
frame 𝓤 𝓥 𝓦 = Σ A ꞉ (𝓤 ̇) , frame-structure 𝓥 𝓦 A 

\end{code}

The underlying poset of a frame:

\begin{code}

poset-of : frame 𝓤 𝓥 𝓦 → poset 𝓤 𝓥
poset-of (A , (_≤_ , _ , _ , _ , iss) , p , _) = (A , iss) , _≤_ , p

\end{code}
