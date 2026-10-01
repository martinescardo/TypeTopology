Ayberk Tosun, 8 March 2021.

Ported from `ayberkt/formal-topology-in-UF`.

 * Frames.
 * Frame homomorphisms.
 * Frame bases.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import MLTT.List hiding ([_])

module Locales.Frame
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Slice.Family
open import UF.HedbergApplications
open import UF.Logic
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties

open AllCombinators pt fe

\end{code}

\section{Preliminaries}

\begin{code}

private
  variable
    𝓤′ 𝓥′ 𝓦′ 𝓤′′ 𝓥′′ : Universe

\end{code}

We define some order-theoretic notions that are also defined in the
`Dcpo` module. Ideally, this should be factored out into a standalone
module to be imported by both this module and the `Dcpo` module.

\begin{code}

is-reflexive : {A : 𝓤 ̇ } → (A → A → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
is-reflexive {A = A} _≤_ = Ɐ x ꞉ A , x ≤ x

is-transitive : {A : 𝓤 ̇ } → (A → A → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
is-transitive {A = A} _≤_ =
 Ɐ x ꞉ A , Ɐ y ꞉ A , Ɐ z ꞉ A , x ≤ y ⇒ y ≤ z ⇒ x ≤ z

is-preorder : {A : 𝓤 ̇ } → (A → A → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
is-preorder {A = A} _≤_ = is-reflexive _≤_ ∧ is-transitive _≤_

\end{code}

Antisymmetry is not propositional unless A is a set. We will always
work with sets but the fact they are sets will be a corollary of their
equipment with an antisymmetric order so they are not sets a priori.

\begin{code}

is-antisymmetric : {A : 𝓤 ̇ } → (A → A → Ω 𝓥) → (𝓤 ⊔ 𝓥) ̇
is-antisymmetric {A = A} _≤_ = {x y : A} → (x ≤ y) holds → (y ≤ x) holds → x ＝ y

being-antisymmetric-is-prop : {A : 𝓤 ̇ } (_≤_ : A → A → Ω 𝓥)
                            → is-set A
                            → is-prop (is-antisymmetric _≤_)
being-antisymmetric-is-prop {𝓤} {A} _≤_ A-is-set =
         implicit-Π-is-prop fe
  (λ x → implicit-Π-is-prop fe
  (λ y → Π₂-is-prop fe (λ _ _ → A-is-set {x} {y})))

is-partial-order : (A : 𝓤 ̇ )→ (A → A → Ω 𝓥) → 𝓤 ⊔ 𝓥 ̇
is-partial-order A _≤_ = is-preorder _≤_ holds ×  is-antisymmetric _≤_

being-partial-order-is-prop : (A : 𝓤 ̇ )(_≤_ : A → A → Ω 𝓥)
                            → is-prop (is-partial-order A _≤_)
being-partial-order-is-prop A _≤_ = prop-criterion γ
 where
  γ : is-partial-order A _≤_ → is-prop (is-partial-order A _≤_)
  γ (p , a) = ×-is-prop
               (holds-is-prop (is-preorder _≤_))
               (being-antisymmetric-is-prop _≤_ i)
   where
    i : is-set A
    i = type-with-prop-valued-refl-antisym-rel-is-set
         (λ x y → (x ≤ y) holds)
         (λ x y → holds-is-prop (x ≤ y))
         (pr₁ p)
         (λ x y → a {x} {y})

\end{code}

\section{Definition of poset}

A (𝓤, 𝓥)-poset is a poset whose

  - carrier lives in universe 𝓤, and
  - whose relation lives in universe 𝓥.

\begin{code}

poset-structure : (𝓥 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ̇
poset-structure 𝓥 A =
 Σ _≤_ ꞉ (A → A → Ω 𝓥) , (is-partial-order A _≤_)

Poset : (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
Poset 𝓤 𝓥 = Σ A ꞉ 𝓤 ̇ , poset-structure 𝓥 A

∣_∣ₚ : Poset 𝓤 𝓥 → 𝓤 ̇
∣ A , _ ∣ₚ = A

rel-syntax : (P : Poset 𝓤 𝓥)  → ∣ P ∣ₚ → ∣ P ∣ₚ → Ω 𝓥
rel-syntax (_ , _≤_ , _) = _≤_

infix 5 rel-syntax

syntax rel-syntax P x y = x ≤[ P ] y

poset-eq-syntax : (P : Poset 𝓤 𝓥) → ∣ P ∣ₚ → ∣ P ∣ₚ → Ω 𝓥
poset-eq-syntax P x y = x ≤[ P ] y ∧ y ≤[ P ] x

syntax poset-eq-syntax P x y = x ≣[ P ] y

≤-is-reflexive : (P : Poset 𝓤 𝓥)
               → is-reflexive (λ x y → x ≤[ P ] x) holds
≤-is-reflexive (_ , _ , ((r , _) , _)) = r

≣-is-reflexive : (P : Poset 𝓤 𝓥) → is-reflexive (λ x y → x ≣[ P ] x) holds
≣-is-reflexive P x = ≤-is-reflexive P x , ≤-is-reflexive P x

reflexivity+ : (P : Poset 𝓤 𝓥)
             → {x y : pr₁ P} → x ＝ y → (x ≤[ P ] y) holds
reflexivity+ P {x} {y} p =
 transport (λ - → (x ≤[ P ] -) holds) p (≤-is-reflexive P x)

≤-is-transitive : (P : Poset 𝓤 𝓥)
                → is-transitive (λ x y → x ≤[ P ] y) holds
≤-is-transitive (_ , _ , ((_ , t) , _)) = t

≤-is-antisymmetric : (P : Poset 𝓤 𝓥)
                   → is-antisymmetric (λ x y → x ≤[ P ] y)
≤-is-antisymmetric (_ , _ , (_ , a)) = a

carrier-of-[_]-is-set : (P : Poset 𝓤 𝓥) → is-set ∣ P ∣ₚ
carrier-of-[_]-is-set P@ (A , _)=
 type-with-prop-valued-refl-antisym-rel-is-set
  (λ x y → (x ≤[ P ] y) holds)
  (λ x y → holds-is-prop (x ≤[ P ] y))
  (≤-is-reflexive P)
  (λ x y → ≤-is-antisymmetric P {x} {y})

\end{code}

Some convenient syntax for reasoning with posets.

\begin{code}

module PosetNotation (P : Poset 𝓤 𝓥) where

 _≤_ : ∣ P ∣ₚ → ∣ P ∣ₚ → Ω 𝓥
 x ≤ y = x ≤[ P ] y

 infix 4 _≤_

 _≣_ : ∣ P ∣ₚ → ∣ P ∣ₚ → Ω 𝓥
 x ≣ y = x ≣[ P ] y

module PosetReasoning (P : Poset 𝓤 𝓥) where

 open PosetNotation P using (_≤_)

 _≤⟨_⟩_ : (x : ∣ P ∣ₚ) {y z : ∣ P ∣ₚ}
        → (x ≤ y) holds → (y ≤ z) holds → (x ≤ z) holds
 x ≤⟨ p ⟩ q = ≤-is-transitive P _ _ _ p q

 _＝⟨_⟩ₚ_ : (x : ∣ P ∣ₚ) {y z : ∣ P ∣ₚ}
         → x ＝ y → (y ≤ z) holds → (x ≤ z) holds
 x ＝⟨ p ⟩ₚ q = transport (λ - → (- ≤ _) holds) (p ⁻¹) q

 _■ : (x : ∣ P ∣ₚ) → (x ≤ x) holds
 _■ = ≤-is-reflexive P

 infixr 0 _≤⟨_⟩_
 infixr 0 _＝⟨_⟩ₚ_
 infix  1 _■

infix 1 _＝[_]＝_

_＝[_]＝_ : {A : 𝓤 ̇ } → A → is-set A → A → Ω 𝓤
x ＝[ iss ]＝ y = (x ＝ y) , iss

\end{code}

\section{Meets}

\begin{code}

module Meets {A : 𝓤 ̇ } (_≤_ : A → A → Ω 𝓥) where

 is-top : A → Ω (𝓤 ⊔ 𝓥)
 is-top t = Ɐ x ꞉ A , (x ≤ t)

 _is-a-lower-bound-of_ : A → A × A → Ω 𝓥
 l is-a-lower-bound-of (x , y) = (l ≤ x) ∧ (l ≤ y)

 lower-bound : A × A → 𝓤 ⊔ 𝓥 ̇
 lower-bound (x , y) =
   Σ l ꞉ A , (l is-a-lower-bound-of (x , y)) holds

 _is-glb-of_ : A → A × A → Ω (𝓤 ⊔ 𝓥)
 l is-glb-of (x , y) = l is-a-lower-bound-of (x , y)
                     ∧ (Ɐ (l′ , _) ꞉ lower-bound (x , y) , (l′ ≤ l))

 glb-is-an-upper-bound₁ : {x y z : A} → (z is-glb-of (x , y) ⇒ z ≤ x) holds
 glb-is-an-upper-bound₁ ((p₁ , _) , _) = p₁

 glb-is-an-upper-bound₂ : {x y z : A} → (z is-glb-of (x , y) ⇒ z ≤ y) holds
 glb-is-an-upper-bound₂ ((_ , p₂) , _) = p₂

 glb-is-greatest : {x y z w : A}
                 → (z is-glb-of (x , y)) holds
                 → (w is-a-lower-bound-of (x , y) ⇒ w ≤ z) holds
 glb-is-greatest {_} {_} {_} {w} (_ , q) υ = q (w , υ)

\end{code}

\section{Joins}

\begin{code}

module Joins {A : 𝓤 ̇ } (_≤_ : A → A → Ω 𝓥) where

 is-least : A → Ω (𝓤 ⊔ 𝓥)
 is-least x = Ɐ y ꞉ A , x ≤ y

 _is-an-upper-bound-of_ : A → Fam 𝓦 A → Ω (𝓥 ⊔ 𝓦)
 u is-an-upper-bound-of U = Ɐ i ꞉ index U , (U [ i ]) ≤ u

 _is-an-upper-bound-of₂_ : A → A × A → Ω 𝓥
 u is-an-upper-bound-of₂ (v , w) = (v ≤ u) ∧ (w ≤ u)

 upper-bound : Fam 𝓦 A → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 upper-bound U = Σ u ꞉ A , (u is-an-upper-bound-of U) holds

 upper-bound₂ : A × A → 𝓤 ⊔ 𝓥 ̇
 upper-bound₂ (x , y) = Σ u ꞉ A , (u is-an-upper-bound-of₂ (x , y)) holds

 _is-lub-of_ : A → Fam 𝓦 A → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
 u is-lub-of U = (u is-an-upper-bound-of U)
               ∧ (Ɐ (u′ , _) ꞉ upper-bound U , (u ≤ u′))

 _is-lub-of₂_ : A → A × A → Ω (𝓤 ⊔ 𝓥)
 u is-lub-of₂ (v , w) = (u is-an-upper-bound-of₂ (v , w))
                      ∧ (Ɐ (u′ , _) ꞉ upper-bound₂ (v , w) , (u ≤ u′))

 lub₂-is-an-upper-bound₁ : {x y z : A} → (z is-lub-of₂ (x , y) ⇒ x ≤ z) holds
 lub₂-is-an-upper-bound₁ ((p₁ , _) , _) = p₁

 lub₂-is-an-upper-bound₂ : {x y z : A} → (z is-lub-of₂ (x , y) ⇒ y ≤ z) holds
 lub₂-is-an-upper-bound₂ ((_ , p₂) , _) = p₂

 lub₂-is-least : {x y z w : A}
               → (z is-lub-of₂ (x , y)) holds
               → (w is-an-upper-bound-of₂ (x , y) ⇒ z ≤ w) holds
 lub₂-is-least {_} {_} {_} {w} (_ , q) υ = q (w , υ)

module JoinNotation {A : 𝓤 ̇ } (⋁_ : Fam 𝓦 A → A) where

 join-syntax : (I : 𝓦 ̇ )→ (I → A) → A
 join-syntax I f = ⋁ (I , f)

 ⋁⟨⟩-syntax : {I : 𝓦 ̇ } → (I → A) → A
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

satisfies-frame-laws : {A : 𝓤 ̇ } → frame-data 𝓥 𝓦 A → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
satisfies-frame-laws {𝓤 = 𝓤} {𝓥} {𝓦} {A = A}  (_≤_ , 𝟏 , _⊓_ , ⊔_) =
 Σ p ꞉ is-partial-order A _≤_ , rest p holds
 where
  open Meets _≤_
  open Joins _≤_
  open JoinNotation ⊔_

  rest : is-partial-order A _≤_ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
  rest p = β ∧ γ ∧ δ ∧ ε
   where
    P : Poset 𝓤 𝓥
    P = A , _≤_ , p

    iss : is-set A
    iss = carrier-of-[ P ]-is-set

    β = is-top 𝟏
    γ = Ɐ (x , y) ꞉ (A × A) , ((x ⊓ y) is-glb-of (x , y))
    δ = Ɐ U ꞉ Fam 𝓦 A , (⊔ U) is-lub-of U
    ε = Ɐ (x , U) ꞉ A × Fam 𝓦 A ,
        (x ⊓ (⋁⟨ i ⟩ U [ i ]) ＝[ iss ]＝ ⋁⟨ i ⟩ x ⊓ (U [ i ]))

\end{code}

The proof `satisfying-frame-laws-is-prop` has been added on 2024-04-15.

\begin{code}

satisfying-frame-laws-is-prop : {A : 𝓤 ̇ } (d : frame-data 𝓥 𝓦 A)
                              → is-prop (satisfies-frame-laws d)
satisfying-frame-laws-is-prop {𝓤} {𝓥} {𝓦} {A} d@(_≤_ , 𝟏 , _⊓_ , ⊔_) =
 Σ-is-prop (being-partial-order-is-prop A _≤_) †
  where
   open Meets _≤_
   open Joins _≤_
   open JoinNotation ⊔_

   β = is-top 𝟏
   γ = Ɐ (x , y) ꞉ (A × A) , ((x ⊓ y) is-glb-of (x , y))
   δ = Ɐ U ꞉ Fam 𝓦 A , (⊔ U) is-lub-of U

   ε : is-set A → Ω (𝓤 ⊔ 𝓦 ⁺)
   ε σ = Ɐ (x , U) ꞉ A × Fam 𝓦 A ,
          (x ⊓ (⋁⟨ i ⟩ U [ i ]) ＝[ σ ]＝ ⋁⟨ i ⟩ x ⊓ (U [ i ]))

   ‡ : (p : is-partial-order A _≤_) (σ : is-set A)
     → is-prop ((β ∧ γ ∧ δ ∧ ε σ) holds)
   ‡ p σ = holds-is-prop (β ∧ γ ∧ δ ∧ ε σ)

   χ : is-partial-order A _≤_ → is-set A
   χ p = carrier-of-[ (A , _≤_ , p) ]-is-set

   † : (p : is-partial-order A _≤_) → is-prop ((β ∧ γ ∧ δ ∧ ε (χ p)) holds)
   † p = ‡ p (χ p)

frame-structure : (𝓥 𝓦 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
frame-structure 𝓥 𝓦 A = Σ d ꞉ frame-data 𝓥 𝓦 A , satisfies-frame-laws d

\end{code}

The type of (𝓤, 𝓥, 𝓦)-frames is then defined as:

\begin{code}

Frame : (𝓤 𝓥 𝓦 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
Frame 𝓤 𝓥 𝓦 = Σ A ꞉ (𝓤 ̇ ), frame-structure 𝓥 𝓦 A

\end{code}

The underlying poset of a frame:

\begin{code}

poset-of : Frame 𝓤 𝓥 𝓦 → Poset 𝓤 𝓥
poset-of (A , (_≤_ , _ , _ , _) , p , _) = A , _≤_ , p

\end{code}

Some projections.

\begin{code}

⟨_⟩ : Frame 𝓤 𝓥 𝓦 → 𝓤 ̇
⟨ (A , (_≤_ , _ , _ , _) , p , _) ⟩ = A

𝟏[_] : (F : Frame 𝓤 𝓥 𝓦) →  ⟨ F ⟩
𝟏[ (A , (_ , 𝟏 , _ , _) , p , _) ] = 𝟏

is-top : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥)
is-top F t = Ɐ x ꞉ ⟨ F ⟩ , x ≤[ poset-of F ] t

𝟏-is-top : (F : Frame 𝓤 𝓥 𝓦) → (is-top F 𝟏[ F ]) holds
𝟏-is-top (A , _ , _ , p , _) = p

𝟏-is-unique : (F : Frame 𝓤 𝓥 𝓦) → (t : ⟨ F ⟩) → is-top F t holds → t ＝ 𝟏[ F ]
𝟏-is-unique F t t-top = ≤-is-antisymmetric (poset-of F) β γ
 where
  β : (t ≤[ poset-of F ] 𝟏[ F ]) holds
  β = 𝟏-is-top F t

  γ : (𝟏[ F ] ≤[ poset-of F ] t) holds
  γ = t-top 𝟏[ F ]

only-𝟏-is-above-𝟏 : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩)
                  → (𝟏[ F ] ≤[ poset-of F ] x) holds → x ＝ 𝟏[ F ]
only-𝟏-is-above-𝟏 F x p =
 𝟏-is-unique F x λ y → y ≤⟨ 𝟏-is-top F y ⟩ 𝟏[ F ] ≤⟨ p ⟩ x ■
  where
   open PosetReasoning (poset-of F)

meet-of : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → ⟨ F ⟩
meet-of (_ , (_ , _ , _∧_ , _) , _ , _) x y = x ∧ y

infixl 4 meet-of

syntax meet-of F x y = x ∧[ F ] y

join-of : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → ⟨ F ⟩
join-of (_ , (_ , _ , _ , ⋁_) , _ , _) = ⋁_

infix 4 join-of

syntax join-of F U = ⋁[ F ] U

\end{code}

\begin{code}

∧[_]-is-glb : (A : Frame 𝓤 𝓥 𝓦) (x y : ⟨ A ⟩)
            → let
               open Meets (λ x y → x ≤[ poset-of A ] y)
              in
               ((x ∧[ A ] y) is-glb-of (x , y)) holds
∧[_]-is-glb (A , _ , _ , (_ , γ , _ , _)) x y = γ (x , y)

∧[_]-is-glb⋆ : (A : Frame 𝓤 𝓥 𝓦) {x y z : ⟨ A ⟩}
             → let
                open Meets (λ x y → x ≤[ poset-of A ] y)
               in
                z ＝ x ∧[ A ] y → (z is-glb-of (x , y)) holds
∧[_]-is-glb⋆ L@(A , _ , _ , (_ , γ , _ , _)) {x} {y} {z} p =
 transport (λ - → (- is-glb-of (x , y)) holds) (p ⁻¹) (∧[ L ]-is-glb x y)
  where
   open Meets (λ x y → x ≤[ poset-of L ] y)

∧[_]-lower₁ : (A : Frame 𝓤 𝓥 𝓦) (x y : ⟨ A ⟩)
            → ((x ∧[ A ] y) ≤[ poset-of A ] x) holds
∧[_]-lower₁ (A , _ , _ , (_ , γ , _ , _)) x y = pr₁ (pr₁ (γ (x , y)))

∧[_]-lower₂ : (A : Frame 𝓤 𝓥 𝓦) (x y : ⟨ A ⟩)
            → ((x ∧[ A ] y) ≤[ poset-of A ] y) holds
∧[_]-lower₂ (A , _ , _ , (_ , γ , _ , _)) x y = pr₂ (pr₁ (γ (x , y)))

∧[_]-greatest : (A : Frame 𝓤 𝓥 𝓦) (x y : ⟨ A ⟩)
              → (z : ⟨ A ⟩)
              → (z ≤[ poset-of A ] x) holds
              → (z ≤[ poset-of A ] y) holds
              → (z ≤[ poset-of A ] (x ∧[ A ] y)) holds
∧[_]-greatest (A , _ , _ , (_ , γ , _ , _)) x y z p q =
  pr₂ (γ (x , y)) (z , p , q)

\end{code}

\begin{code}

𝟏-right-unit-of-∧ : (F : Frame 𝓤 𝓥 𝓦)
                  → (x : ⟨ F ⟩) → x ∧[ F ] 𝟏[ F ] ＝ x
𝟏-right-unit-of-∧ F x = ≤-is-antisymmetric (poset-of F) β γ
 where
  β : ((x ∧[ F ] 𝟏[ F ]) ≤[ poset-of F ] x) holds
  β = ∧[ F ]-lower₁ x 𝟏[ F ]

  γ : (x ≤[ poset-of F ] (x ∧[ F ] 𝟏[ F ])) holds
  γ = ∧[ F ]-greatest x 𝟏[ F ] x (≤-is-reflexive (poset-of F) x) (𝟏-is-top F x)

\end{code}

\begin{code}

⋁[_]-upper : (A : Frame 𝓤 𝓥 𝓦) (U : Fam 𝓦 ⟨ A ⟩) (i : index U)
        → ((U [ i ]) ≤[ poset-of A ] (⋁[ A ] U)) holds
⋁[_]-upper (A , _ , _ , (_ , _ , c , _)) U i = pr₁ (c U) i

⋁[_]-least : (A : Frame 𝓤 𝓥 𝓦) → (U : Fam 𝓦 ⟨ A ⟩)
           → let open Joins (λ x y → x ≤[ poset-of A ] y)
             in ((u , _) : upper-bound U) → ((⋁[ A ] U) ≤[ poset-of A ] u) holds
⋁[_]-least (A , _ , _ , (_ , _ , c , _)) U = pr₂ (c U)

\end{code}

\begin{code}

𝟚 : (𝓤 : Universe) → 𝓤 ̇
𝟚 𝓤 = 𝟙 {𝓤} + 𝟙 {𝓤}

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

and₂ : {𝓤 : Universe} → 𝟚 𝓤 → 𝟚 𝓤 → 𝟚 𝓤
and₂ (inl ⋆) _ = inl ⋆
and₂ (inr ⋆) y = y

binary-family : {A : 𝓤 ̇ } → (𝓦 : Universe) → A → A → Fam 𝓦 A
binary-family {A = A} 𝓦 x y = 𝟚 𝓦  , α
 where
  α : 𝟚 𝓦 → A
  α (inl *) = x
  α (inr *) = y

binary-family-syntax : {A : 𝓤 ̇ } {𝓦 : Universe} → A → A → Fam 𝓦 A
binary-family-syntax {𝓦 = 𝓦} x y = binary-family 𝓦 x y

syntax binary-family-syntax x y = ⁅ x , y ⁆

fmap-binary-family : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                   → (𝓦 : Universe)
                   → (f : A → B)
                   → (x y : A)
                   → ⁅ f z ∣ z ε (binary-family 𝓦 x y) ⁆
                   ＝ binary-family 𝓦 (f x) (f y)
fmap-binary-family 𝓦 f x y = ap (λ - → 𝟚 𝓦 , -) (dfunext fe γ)
 where
  γ : ⁅ f z ∣ z ε binary-family 𝓦 x y ⁆ [_] ∼ binary-family 𝓦 (f x) (f y) [_]
  γ (inl *) = refl
  γ (inr *) = refl


binary-join : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → ⟨ F ⟩
binary-join {𝓦 = 𝓦} F x y = ⋁[ F ] binary-family 𝓦 x y

infix 3 binary-join
syntax binary-join F x y = x ∨[ F ] y

∨[_]-least : (F : Frame 𝓤 𝓥 𝓦)
           → let open Joins (λ x y → x ≤[ poset-of F ] y) in
             {x y z : ⟨ F ⟩}
           → (x ≤[ poset-of F ] z) holds
           → (y ≤[ poset-of F ] z) holds
           → ((x ∨[ F ] y) ≤[ poset-of F ] z) holds
∨[_]-least {𝓦 = 𝓦} F {x} {y} {z} x≤z y≤z =
 ⋁[ F ]-least (binary-family 𝓦 x y) (z , γ)
  where
   γ : _
   γ (inl *) = x≤z
   γ (inr *) = y≤z

∨[_]-upper₁ : (F : Frame 𝓤 𝓥 𝓦)
            → let open Joins (λ x y → x ≤[ poset-of F ] y) in
              (x y : ⟨ F ⟩) → (x ≤[ poset-of F ] (x ∨[ F ] y)) holds
∨[_]-upper₁ {𝓦 = 𝓦} F x y = ⋁[ F ]-upper (binary-family 𝓦 x y) (inl ⋆)

∨[_]-upper₂ : (F : Frame 𝓤 𝓥 𝓦)
            → let open Joins (λ x y → x ≤[ poset-of F ] y) in
              (x y : ⟨ F ⟩) → (y ≤[ poset-of F ] (x ∨[ F ] y)) holds
∨[_]-upper₂ {𝓦 = 𝓦} F x y = ⋁[ F ]-upper (binary-family 𝓦 x y) (inr ⋆)

∨[_]-is-commutative : (F : Frame 𝓤 𝓥 𝓦)
                    → (x y : ⟨ F ⟩)
                    → (x ∨[ F ] y) ＝ (y ∨[ F ] x)
∨[_]-is-commutative F x y =
 ≤-is-antisymmetric (poset-of F) β γ
  where
   open PosetNotation  (poset-of F)
   open PosetReasoning (poset-of F)

   β : ((x ∨[ F ] y) ≤ (y ∨[ F ] x)) holds
   β = ∨[ F ]-least (∨[ F ]-upper₂ y x) (∨[ F ]-upper₁ y x)

   γ : ((y ∨[ F ] x) ≤ (x ∨[ F ] y)) holds
   γ = ∨[ F ]-least (∨[ F ]-upper₂ x y) (∨[ F ]-upper₁ x y)

∨[_]-assoc : (F : Frame 𝓤 𝓥 𝓦)
           → (x y z : ⟨ F ⟩)
           → (x ∨[ F ] y) ∨[ F ] z ＝ x ∨[ F ] (y ∨[ F ] z)
∨[_]-assoc F x y z =
 ≤-is-antisymmetric (poset-of F) (∨[ F ]-least β γ) (∨[ F ]-least δ ε)
 where
  open PosetNotation  (poset-of F)
  open PosetReasoning (poset-of F)

  η : (y ≤ ((x ∨[ F ] y) ∨[ F ] z)) holds
  η = y                     ≤⟨ ∨[ F ]-upper₂ x y            ⟩
      x ∨[ F ] y            ≤⟨ ∨[ F ]-upper₁ (x ∨[ F ] y) z ⟩
      (x ∨[ F ] y) ∨[ F ] z ■

  θ : (y ≤ (x ∨[ F ] (y ∨[ F ] z))) holds
  θ = y                     ≤⟨ ∨[ F ]-upper₁ y z            ⟩
      y ∨[ F ] z            ≤⟨ ∨[ F ]-upper₂ x (y ∨[ F ] z) ⟩
      x ∨[ F ] (y ∨[ F ] z) ■

  δ : (x ≤ ((x ∨[ F ] y) ∨[ F ] z)) holds
  δ = x                     ≤⟨ ∨[ F ]-upper₁ x y            ⟩
      x ∨[ F ] y            ≤⟨ ∨[ F ]-upper₁ (x ∨[ F ] y) z ⟩
      (x ∨[ F ] y) ∨[ F ] z ■

  ε : ((y ∨[ F ] z) ≤ ((x ∨[ F ] y) ∨[ F ] z)) holds
  ε = ∨[ F ]-least η (∨[ F ]-upper₂ (x ∨[ F ] y) z)

  β : ((x ∨[ F ] y) ≤ (x ∨[ F ] (y ∨[ F ] z))) holds
  β = ∨[ F ]-least (∨[ F ]-upper₁ x (y ∨[ F ] z)) θ

  γ : (z ≤ (x ∨[ F ] (y ∨[ F ] z))) holds
  γ = z                      ≤⟨ ∨[ F ]-upper₂ y z            ⟩
      y ∨[ F ] z             ≤⟨ ∨[ F ]-upper₂ x (y ∨[ F ] z) ⟩
      x ∨[ F ] (y ∨[ F ] z)  ■

\end{code}

By fixing the left or right argument of `_∨_` to anything, we get a monotonic
map.

\begin{code}

∨[_]-left-monotone : (F : Frame 𝓤 𝓥 𝓦)
               → {x y z : ⟨ F ⟩}
               → (x ≤[ poset-of F ] y) holds
               → ((x ∨[ F ] z) ≤[ poset-of F ] (y ∨[ F ] z)) holds
∨[_]-left-monotone F {x = x} {y} {z} p = ∨[ F ]-least γ (∨[ F ]-upper₂ y z)
 where
  open PosetNotation  (poset-of F) using (_≤_)
  open PosetReasoning (poset-of F)

  γ : (x ≤ (y ∨[ F ] z)) holds
  γ = x ≤⟨ p ⟩ y ≤⟨ ∨[ F ]-upper₁ y z ⟩ y ∨[ F ] z ■

∨[_]-right-monotone : (F : Frame 𝓤 𝓥 𝓦)
                → {x y z : ⟨ F ⟩}
                → (x ≤[ poset-of F ] y) holds
                → ((z ∨[ F ] x) ≤[ poset-of F ] (z ∨[ F ] y)) holds
∨[_]-right-monotone F {x} {y} {z} p =
 z ∨[ F ] x  ＝⟨ ∨[ F ]-is-commutative z x ⟩ₚ
 x ∨[ F ] z  ≤⟨ ∨[ F ]-left-monotone p    ⟩
 y ∨[ F ] z  ＝⟨ ∨[ F ]-is-commutative y z ⟩ₚ
 z ∨[ F ] y  ■
  where
   open PosetReasoning (poset-of F)

\end{code}

\begin{code}

∅ : {A : 𝓤 ̇ } → (𝓦 : Universe) → Fam 𝓦 A
∅ 𝓦 = 𝟘 {𝓦} , 𝟘-elim

𝟎[_] : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩
𝟎[ F ] = ⋁[ F ] (∅ _)

is-bottom : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥)
is-bottom F b = Ɐ x ꞉ ⟨ F ⟩ , (b ≤[ poset-of F ] x)

𝟎-is-bottom : (F : Frame 𝓤 𝓥 𝓦)
            → (x : ⟨ F ⟩) → (𝟎[ F ] ≤[ poset-of F ] x) holds
𝟎-is-bottom F x = ⋁[ F ]-least (𝟘 , 𝟘-elim) (x , 𝟘-induction)

only-𝟎-is-below-𝟎 : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩)
                  → (x ≤[ poset-of F ] 𝟎[ F ]) holds → x ＝ 𝟎[ F ]
only-𝟎-is-below-𝟎 F x p =
 ≤-is-antisymmetric (poset-of F) p (𝟎-is-bottom F x)

𝟎-is-unique : (F : Frame 𝓤 𝓥 𝓦) (b : ⟨ F ⟩)
            → ((x : ⟨ F ⟩) → (b ≤[ poset-of F ] x) holds) → b ＝ 𝟎[ F ]
𝟎-is-unique F b φ = only-𝟎-is-below-𝟎 F b (φ 𝟎[ F ])

𝟎-right-unit-of-∨ : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩) → 𝟎[ F ] ∨[ F ] x ＝ x
𝟎-right-unit-of-∨ {𝓦 = 𝓦} F x = ≤-is-antisymmetric (poset-of F) β γ
 where
  open PosetNotation (poset-of F)

  β : ((𝟎[ F ] ∨[ F ] x) ≤ x) holds
  β = ∨[ F ]-least (𝟎-is-bottom F x) (≤-is-reflexive (poset-of F) x)

  γ : (x ≤ (𝟎[ F ] ∨[ F ] x)) holds
  γ = ⋁[ F ]-upper (binary-family 𝓦 𝟎[ F ] x) (inr ⋆)

𝟎-left-unit-of-∨ : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩) → x ∨[ F ] 𝟎[ F ] ＝ x
𝟎-left-unit-of-∨ {𝓦 = 𝓦} F x =
 x ∨[ F ] 𝟎[ F ]  ＝⟨ ∨[ F ]-is-commutative x 𝟎[ F ] ⟩
 𝟎[ F ] ∨[ F ] x  ＝⟨ 𝟎-right-unit-of-∨ F x          ⟩
 x                ∎
\end{code}

\begin{code}

distributivity : (F : Frame 𝓤 𝓥 𝓦)
               → (x : ⟨ F ⟩)
               → (U : Fam 𝓦 ⟨ F ⟩)
               → let open JoinNotation (λ - → ⋁[ F ] -) in
                 x ∧[ F ] (⋁⟨ i ⟩ (U [ i ]))
               ＝ ⋁⟨ i ⟩ (x ∧[ F ] (U [ i ]))
distributivity (_ , _ , _ , (_ , _ , _ , d)) x U = d (x , U)

\end{code}

\section{Scott-continuity}

\begin{code}

is-directed : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓥 ⊔ 𝓦)
is-directed F (I , β) =
   ∥ I ∥Ω
 ∧ (Ɐ i ꞉ I , Ɐ j ꞉ I , (Ǝ k ꞉ I , ((β i ≤ β k) ∧ (β j ≤ β k)) holds))
  where open PosetNotation (poset-of F)

directedness-entails-inhabitation : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ⟨ F ⟩)
                                  → (is-directed F S ⇒ ∥ index S ∥Ω) holds
directedness-entails-inhabitation F S = pr₁

is-scott-continuous : (F : Frame 𝓤  𝓥  𝓦)
                    → (G : Frame 𝓤′ 𝓥′ 𝓦)
                    → (f : ⟨ F ⟩ → ⟨ G ⟩)
                    → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ⊔ 𝓤′ ⊔ 𝓥′)
is-scott-continuous {𝓦 = 𝓦} F G f =
 Ɐ S ꞉ Fam 𝓦 ⟨ F ⟩ , is-directed F S ⇒ f (⋁[ F ] S) is-lub-of ⁅ f s ∣ s ε S ⁆
  where
   open Joins (λ x y → x ≤[ poset-of G ] y) using (_is-lub-of_)

id-is-scott-continuous : (F : Frame 𝓤 𝓥 𝓦) → is-scott-continuous F F id holds
id-is-scott-continuous F S δ = ⋁[ F ]-upper S , ⋁[ F ]-least S
 where
  open Joins (λ x y → x ≤[ poset-of F ] y)

\end{code}

\section{Frame homomorphisms}

\begin{code}

is-monotonic : (P : Poset 𝓤 𝓥) (Q : Poset 𝓤′ 𝓥′)
             → (pr₁ P → pr₁ Q) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓥′)
is-monotonic P Q f =
 Ɐ (x , y) ꞉ (pr₁ P × pr₁ P) , ((x ≤[ P ] y) ⇒ f x ≤[ Q ] f y)

_─m→_ : (P : Poset 𝓤 𝓥) (Q : Poset 𝓤′ 𝓥′) → 𝓤 ⊔ 𝓥 ⊔ 𝓤′ ⊔ 𝓥′ ̇
P ─m→ Q = Σ f ꞉ (∣ P ∣ₚ → ∣ Q ∣ₚ) , (is-monotonic P Q f) holds

monotone-image-on-directed-family-is-directed : (F : Frame 𝓤  𝓥  𝓦)
                                              → (G : Frame 𝓤′ 𝓥′ 𝓦)
                                              → (S : Fam 𝓦 ⟨ F ⟩)
                                              → is-directed F S holds
                                              → (f : ⟨ F ⟩ → ⟨ G ⟩)
                                              → is-monotonic (poset-of F) (poset-of G) f holds
                                              → is-directed G ⁅ f s ∣ s ε S ⁆ holds
monotone-image-on-directed-family-is-directed F G S (ι , υ) f μ = ι , γ
 where
  open PropositionalTruncation pt

  I = index S

  γ : (Ɐ i ꞉ I , Ɐ j ꞉ I ,
        (Ǝ k ꞉ I ,
          ((f (S [ i ]) ≤[ poset-of G ] f (S [ k ]))
         ∧ (f (S [ j ]) ≤[ poset-of G ] f (S [ k ]))) holds)) holds
  γ i j = ∥∥-rec ∥∥-is-prop β (υ i j)
   where
    β : (Σ k ꞉ I , (((S [ i ]) ≤[ poset-of F ] (S [ k ]))
                  ∧ ((S [ j ]) ≤[ poset-of F ] (S [ k ]))) holds)
      → (∃ k ꞉ I , ((f (S [ i ]) ≤[ poset-of G ] f (S [ k ]))
                  ∧ (f (S [ j ]) ≤[ poset-of G ] f (S [ k ]))) holds)
    β (k , p , q) = ∣ k , μ (S [ i ] , S [ k ]) p , μ (S [ j ] , S [ k ]) q ∣



is-join-preserving : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤' 𝓥' 𝓦)
                   → (⟨ F ⟩ → ⟨ G ⟩) → Ω (𝓤 ⊔ 𝓤' ⊔ 𝓦 ⁺)
is-join-preserving {𝓦 = 𝓦} F G f =
 Ɐ S ꞉ Fam 𝓦 ⟨ F ⟩ , f (⋁[ F ] S) ＝[ iss ]＝ ⋁[ G ] ⁅ f s ∣ s ε S ⁆
  where
   iss = carrier-of-[ poset-of G ]-is-set

join-preserving-implies-scott-continuous : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤' 𝓥' 𝓦)
                                         → (f : ⟨ F ⟩ → ⟨ G ⟩)
                                         → is-join-preserving F G f holds
                                         → is-scott-continuous F G f holds
join-preserving-implies-scott-continuous F G f φ S _ = γ
 where
  open Joins (λ x y → x ≤[ poset-of G ] y)

  γ : (f (⋁[ F ] S) is-lub-of ⁅ f s ∣ s ε S ⁆) holds
  γ = transport
       (λ - → (- is-lub-of (fmap-syntax (λ s → f s)) S) holds)
       (φ S ⁻¹)
       (⋁[ G ]-upper ⁅ f s ∣ s ε S ⁆ , ⋁[ G ]-least ⁅ f s ∣ s ε S ⁆)

\end{code}

\section{Some properties of frames}

\begin{code}

∧[_]-unique : (F : Frame 𝓤 𝓥 𝓦) {x y z : ⟨ F ⟩}
            → let open Meets (λ x y → x ≤[ poset-of F ] y) in
              (z is-glb-of (x , y)) holds → z ＝ (x ∧[ F ] y)
∧[ F ]-unique {x} {y} {z} (p , q) = ≤-is-antisymmetric (poset-of F) β γ
 where
  β : (z ≤[ poset-of F ] (x ∧[ F ] y)) holds
  β = ∧[ F ]-greatest x y z (pr₁ p) (pr₂ p)

  γ : ((x ∧[ F ] y) ≤[ poset-of F ] z) holds
  γ = q ((x ∧[ F ] y) , ∧[ F ]-lower₁ x y , ∧[ F ]-lower₂ x y)

\end{code}

\begin{code}

⋁[_]-unique : (F : Frame 𝓤 𝓥 𝓦) (U : Fam 𝓦 ⟨ F ⟩) (u : ⟨ F ⟩)
         → let open Joins (λ x y → x ≤[ poset-of F ] y) in
           (u is-lub-of U) holds → u ＝ ⋁[ F ] U
⋁[_]-unique F U u (p , q) = ≤-is-antisymmetric (poset-of F) γ β
 where
  open PosetNotation (poset-of F)

  γ : (u ≤ (⋁[ F ] U)) holds
  γ = q ((⋁[ F ] U) , ⋁[ F ]-upper U)

  β : ((⋁[ F ] U) ≤ u) holds
  β = ⋁[ F ]-least U (u , p)

connecting-lemma₁ : (F : Frame 𝓤 𝓥 𝓦) {x y : ⟨ F ⟩}
                  → (x ≤[ poset-of F ] y) holds
                  → x ＝ x ∧[ F ] y
connecting-lemma₁ F {x} {y} p = ∧[ F ]-unique (β , γ)
 where
  open Meets (λ x y → x ≤[ poset-of F ] y)

  β : (x is-a-lower-bound-of (x , y)) holds
  β = ≤-is-reflexive (poset-of F) x , p

  γ : (Ɐ (z , _) ꞉ lower-bound (x , y) , z ≤[ poset-of F ] x) holds
  γ (z , q , _) = q

connecting-lemma₂ : (F : Frame 𝓤 𝓥 𝓦) {x y : ⟨ F ⟩}
                  → x ＝ x ∧[ F ] y
                  → (x ≤[ poset-of F ] y) holds
connecting-lemma₂ F {x} {y} p = x ＝⟨ p ⟩ₚ x ∧[ F ] y ≤⟨ ∧[ F ]-lower₂ x y ⟩ y ■
 where
  open PosetReasoning (poset-of F)

connecting-lemma₃ : (F : Frame 𝓤 𝓥 𝓦) {x y : ⟨ F ⟩}
                  → y ＝ x ∨[ F ] y
                  → (x ≤[ poset-of F ] y) holds
connecting-lemma₃ F {x} {y} p =
 x ≤⟨ ∨[ F ]-upper₁ x y ⟩ x ∨[ F ] y ＝⟨ p ⁻¹ ⟩ₚ y ■
  where
   open PosetReasoning (poset-of F)

connecting-lemma₄ : (F : Frame 𝓤 𝓥 𝓦) {x y : ⟨ F ⟩}
                  → (x ≤[ poset-of F ] y) holds
                  → y ＝ x ∨[ F ] y
connecting-lemma₄ F {x} {y} p = ≤-is-antisymmetric (poset-of F) β γ
 where
  β : (y ≤[ poset-of F ] (x ∨[ F ] y)) holds
  β = ∨[ F ]-upper₂ x y

  γ : ((x ∨[ F ] y) ≤[ poset-of F ] y) holds
  γ = ∨[ F ]-least p (≤-is-reflexive (poset-of F) y)

yoneda : (F : Frame 𝓤 𝓥 𝓦)
       → (x y : ⟨ F ⟩)
       → ((z : ⟨ F ⟩) → ((z ≤[ poset-of F ] x) ⇒ (z ≤[ poset-of F ] y)) holds)
       → (x ≤[ poset-of F ] y) holds
yoneda F x y φ = φ x (≤-is-reflexive (poset-of F) x)

scott-continuous-implies-monotone : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤′ 𝓥′ 𝓦)
                                  → (f : ⟨ F ⟩ → ⟨ G ⟩)
                                  → is-scott-continuous F G f holds
                                  → is-monotonic (poset-of F) (poset-of G) f holds
scott-continuous-implies-monotone {𝓦 = 𝓦} F G f φ (x , y) p =
 f x                                       ≤⟨ i   ⟩
 f x ∨[ G ] f y                            ＝⟨ ii  ⟩ₚ
 ⋁[ G ] ⁅ f z ∣ z ε binary-family 𝓦 x y ⁆  ＝⟨ iii ⟩ₚ
 f (x ∨[ F ] y)                            ＝⟨ iv  ⟩ₚ
 f y                                       ■
  where
   open PosetReasoning (poset-of G)
   open PropositionalTruncation pt

   δ : is-directed F (binary-family 𝓦 x y) holds
   δ = ∣ inr ⋆ ∣ , †
        where
         rx : (x ≤[ poset-of F ] x) holds
         rx = ≤-is-reflexive (poset-of F) x

         ry : (y ≤[ poset-of F ] y) holds
         ry = ≤-is-reflexive (poset-of F) y

         † : _
         † (inl ⋆) (inl ⋆) = ∣ inl ⋆ , rx , rx ∣
         † (inl ⋆) (inr ⋆) = ∣ inr ⋆ , p  , ry ∣
         † (inr ⋆) (inl ⋆) = ∣ inr ⋆ , ry , p  ∣
         † (inr ⋆) (inr ⋆) = ∣ inr ⋆ , ry , ry ∣

   i   = ∨[ G ]-upper₁ (f x) (f y)
   ii  = ap (λ - → ⋁[ G ] -) (fmap-binary-family 𝓦 f x y ⁻¹)
   iii = (⋁[ G ]-unique
           ⁅ f z ∣ z ε binary-family 𝓦 x y ⁆
           (f (⋁[ F ] ⁅ x , y ⁆))
           (φ ⁅ x , y ⁆ δ)) ⁻¹
   iv  = ap f (connecting-lemma₄ F p) ⁻¹


scott-continuous-join-eq : (F : Frame 𝓤  𝓥  𝓦)
                         → (G : Frame 𝓤′ 𝓥′ 𝓦)
                         → (f : ⟨ F ⟩ → ⟨ G ⟩)
                         → is-scott-continuous F G f holds
                         → (S : Fam 𝓦 ⟨ F ⟩)
                         → is-directed F S holds
                         → f (⋁[ F ] S) ＝ ⋁[ G ] ⁅ f s ∣ s ε S ⁆
scott-continuous-join-eq F G f ζ S δ =
 ⋁[ G ]-unique ⁅ f s ∣ s ε S ⁆ (f (⋁[ F ] S)) (ζ S δ)

∘-of-scott-cont-is-scott-cont : (F : Frame 𝓤   𝓥   𝓦)
                                (G : Frame 𝓤′  𝓥′  𝓦)
                                (H : Frame 𝓤′′ 𝓥′′ 𝓦)
                              → (g : ⟨ G ⟩ → ⟨ H ⟩)
                              → (f : ⟨ F ⟩ → ⟨ G ⟩)
                              → is-scott-continuous G H g holds
                              → is-scott-continuous F G f holds
                              → is-scott-continuous F H (g ∘ f) holds
∘-of-scott-cont-is-scott-cont F G H g f ζg ζf S δ =
 β , γ
  where
   open Joins (λ x y → x ≤[ poset-of H ] y)
   open PosetReasoning (poset-of H)

   μf : is-monotonic (poset-of F) (poset-of G) f holds
   μf = scott-continuous-implies-monotone F G f ζf

   μg : is-monotonic (poset-of G) (poset-of H) g holds
   μg = scott-continuous-implies-monotone G H g ζg

   † : is-directed G ⁅ f s ∣ s ε  S ⁆ holds
   † = monotone-image-on-directed-family-is-directed F G S δ f μf

   β : (g (f (⋁[ F ] S)) is-an-upper-bound-of ⁅ g (f s) ∣ s ε S ⁆) holds
   β k = g (f (S [ k ]))              ≤⟨ i   ⟩
         ⋁[ H ] ⁅ g (f s) ∣ s ε S ⁆   ≤⟨ ii  ⟩
         g (⋁[ G ] ⁅ f s ∣ s ε S ⁆)   ＝⟨ iii ⟩ₚ
         g (f (⋁[ F ] S))             ■
          where
           i   = ⋁[ H ]-upper ⁅ g (f s) ∣ s ε S ⁆ k
           ii  = ⋁[ H ]-least
                  ⁅ g (f s) ∣ s ε S ⁆
                  (g (⋁[ G ] ⁅ f s ∣ s ε S ⁆) , pr₁ (ζg ⁅ f s ∣ s ε S ⁆ †))
           iii = ap g (scott-continuous-join-eq F G f ζf S δ ⁻¹)

   γ : (Ɐ (u , _) ꞉ upper-bound ⁅ g (f s) ∣ s ε S ⁆ ,
         (g (f (⋁[ F ] S)) ≤[ poset-of H ] u)) holds
   γ (u , p) = g (f (⋁[ F ] S))              ≤⟨ i   ⟩
               g (⋁[ G ] ⁅ f s ∣ s ε S ⁆)    ＝⟨ ii  ⟩ₚ
               ⋁[ H ] ⁅ g (f s) ∣ s ε S ⁆    ≤⟨ iii ⟩
               u                             ■
                where
                 ※ : (f (⋁[ F ] S) ≤[ poset-of G ] (⋁[ G ] ⁅ f s ∣ s ε S ⁆)) holds
                 ※ = pr₂ (ζf S δ) ((⋁[ G ] ⁅ f s ∣ s ε S ⁆)
                                  , ⋁[ G ]-upper (⁅ f s ∣ s ε S ⁆))

                 i   = μg (f (⋁[ F ] S) , ⋁[ G ] ⁅ f s ∣ s ε S ⁆) ※
                 ii  = scott-continuous-join-eq G H g ζg ⁅ f s ∣ s ε S ⁆ †
                 iii = ⋁[ H ]-least ⁅ g (f s) ∣ s ε S ⁆ (u , p)

\end{code}

\begin{code}

∧[_]-is-commutative : (F : Frame 𝓤 𝓥 𝓦) (x y : ⟨ F ⟩)
                 → x ∧[ F ] y ＝ y ∧[ F ] x
∧[ F ]-is-commutative x y = ∧[ F ]-unique (β , γ)
 where
  open Meets (λ x y → x ≤[ poset-of F ] y)
  open PosetNotation (poset-of F) using (_≤_)

  β : ((x ∧[ F ] y) is-a-lower-bound-of (y , x)) holds
  β = (∧[ F ]-lower₂ x y) , (∧[ F ]-lower₁ x y)

  γ : (Ɐ (l , _) ꞉ lower-bound (y , x) , l ≤ (x ∧[ F ] y)) holds
  γ (l , p , q) = ∧[ F ]-greatest x y l q p

∧[_]-is-associative : (F : Frame 𝓤 𝓥 𝓦) (x y z : ⟨ F ⟩)
                    → x ∧[ F ] (y ∧[ F ] z) ＝ (x ∧[ F ] y) ∧[ F ] z
∧[ F ]-is-associative x y z = ≤-is-antisymmetric (poset-of F) β γ
 where
  open PosetReasoning (poset-of F)

  abstract
   β : ((x ∧[ F ] (y ∧[ F ] z)) ≤[ poset-of F ] ((x ∧[ F ] y) ∧[ F ] z)) holds
   β = ∧[ F ]-greatest (x ∧[ F ] y) z (x ∧[ F ] (y ∧[ F ] z)) δ ε
    where
     δ : ((x ∧[ F ] (y ∧[ F ] z)) ≤[ poset-of F ] (x ∧[ F ] y)) holds
     δ = ∧[ F ]-greatest x y (x ∧[ F ] (y ∧[ F ] z)) δ₁ δ₂
      where
       δ₁ : ((x ∧[ F ] (y ∧[ F ] z)) ≤[ poset-of F ] x) holds
       δ₁ = ∧[ F ]-lower₁ x (y ∧[ F ] z)

       δ₂ : ((x ∧[ F ] (y ∧[ F ] z)) ≤[ poset-of F ] y) holds
       δ₂ = x ∧[ F ] (y ∧[ F ] z) ≤⟨ ∧[ F ]-lower₂ x (y ∧[ F ] z) ⟩
            y ∧[ F ] z            ≤⟨ ∧[ F ]-lower₁ y z            ⟩
            y                     ■

     ε : ((x ∧[ F ] (y ∧[ F ] z)) ≤[ poset-of F ] z) holds
     ε = x ∧[ F ] (y ∧[ F ] z)  ≤⟨ ∧[ F ]-lower₂ x (y ∧[ F ] z) ⟩
         y ∧[ F ] z             ≤⟨ ∧[ F ]-lower₂ y z            ⟩
         z                      ■

   γ : (((x ∧[ F ] y) ∧[ F ] z) ≤[ poset-of F ] (x ∧[ F ] (y ∧[ F ] z))) holds
   γ = ∧[ F ]-greatest x (y ∧[ F ] z) ((x ∧[ F ] y) ∧[ F ] z) ζ η
    where
     ζ : (((x ∧[ F ] y) ∧[ F ] z) ≤[ poset-of F ] x) holds
     ζ = (x ∧[ F ] y) ∧[ F ] z     ≤⟨ ∧[ F ]-lower₁ (x ∧[ F ] y) z ⟩
         x ∧[ F ] y                ≤⟨ ∧[ F ]-lower₁ x y            ⟩
         x                         ■

     η : (((x ∧[ F ] y) ∧[ F ] z) ≤[ poset-of F ] (y ∧[ F ] z)) holds
     η = ∧[ F ]-greatest y z ((x ∧[ F ] y) ∧[ F ] z) η₀ η₁
      where
       η₀ : (((x ∧[ F ] y) ∧[ F ] z) ≤[ poset-of F ] y) holds
       η₀ = (x ∧[ F ] y) ∧[ F ] z  ≤⟨ ∧[ F ]-lower₁ (x ∧[ F ] y) z ⟩
            x ∧[ F ] y             ≤⟨ ∧[ F ]-lower₂ x y            ⟩
            y                      ■

       η₁ : (((x ∧[ F ] y) ∧[ F ] z) ≤[ poset-of F ] z) holds
       η₁ = ∧[ F ]-lower₂ (x ∧[ F ] y) z

\end{code}

\begin{code}

∧[_]-left-monotone : (F : Frame 𝓤 𝓥 𝓦)
                   → {x y z : ⟨ F ⟩}
                   → (x ≤[ poset-of F ] y) holds
                   → ((x ∧[ F ] z) ≤[ poset-of F ] (y ∧[ F ] z)) holds
∧[ F ]-left-monotone {x} {y} {z} p = ∧[ F ]-greatest y z (x ∧[ F ] z) β γ
 where
  open PosetReasoning (poset-of F)

  β : ((x ∧[ F ] z) ≤[ poset-of F ] y) holds
  β = x ∧[ F ] z ≤⟨ ∧[ F ]-lower₁ x z ⟩ x ≤⟨ p ⟩ y ■

  γ : ((x ∧[ F ] z) ≤[ poset-of F ] z) holds
  γ = ∧[ F ]-lower₂ x z

∧[_]-right-monotone : (F : Frame 𝓤 𝓥 𝓦)
                    → {x y z : ⟨ F ⟩}
                    → (x ≤[ poset-of F ] y) holds
                    → ((z ∧[ F ] x) ≤[ poset-of F ] (z ∧[ F ] y)) holds
∧[ F ]-right-monotone {x} {y} {z} p =
 z ∧[ F ] x  ＝⟨ ∧[ F ]-is-commutative z x ⟩ₚ
 x ∧[ F ] z  ≤⟨ ∧[ F ]-left-monotone p    ⟩
 y ∧[ F ] z  ＝⟨ ∧[ F ]-is-commutative y z ⟩ₚ
 z ∧[ F ] y  ■
  where
   open PosetReasoning (poset-of F)

\end{code}

\begin{code}

𝟎-right-annihilator-for-∧ : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩)
                          → x ∧[ F ] 𝟎[ F ] ＝ 𝟎[ F ]
𝟎-right-annihilator-for-∧ F x =
 only-𝟎-is-below-𝟎 F (x ∧[ F ] 𝟎[ F ]) (∧[ F ]-lower₂ x 𝟎[ F ])

𝟎-left-annihilator-for-∧ : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩)
                         → 𝟎[ F ] ∧[ F ] x ＝ 𝟎[ F ]
𝟎-left-annihilator-for-∧ F x =
 𝟎[ F ] ∧[ F ] x  ＝⟨ ∧[ F ]-is-commutative 𝟎[ F ] x ⟩
 x ∧[ F ] 𝟎[ F ]  ＝⟨ 𝟎-right-annihilator-for-∧ F x  ⟩
 𝟎[ F ]           ∎

𝟏-right-annihilator-for-∨ : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩)
                          → x ∨[ F ] 𝟏[ F ] ＝ 𝟏[ F ]
𝟏-right-annihilator-for-∨ F x =
 only-𝟏-is-above-𝟏 F (x ∨[ F ] 𝟏[ F ]) (∨[ F ]-upper₂ x 𝟏[ F ])

𝟏-left-annihilator-for-∨ : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩)
                         → 𝟏[ F ] ∨[ F ] x ＝ 𝟏[ F ]
𝟏-left-annihilator-for-∨ F x =
 𝟏[ F ] ∨[ F ] x  ＝⟨ ∨[ F ]-is-commutative 𝟏[ F ] x ⟩
 x ∨[ F ] 𝟏[ F ]  ＝⟨ 𝟏-right-annihilator-for-∨ F x  ⟩
 𝟏[ F ]           ∎


𝟏-left-unit-of-∧ : (F : Frame 𝓤 𝓥 𝓦)
                 → (x : ⟨ F ⟩) → 𝟏[ F ] ∧[ F ] x ＝ x
𝟏-left-unit-of-∧ F x = 𝟏[ F ] ∧[ F ] x   ＝⟨ ∧[ F ]-is-commutative 𝟏[ F ] x ⟩
                       x ∧[ F ] 𝟏[ F ]   ＝⟨ 𝟏-right-unit-of-∧ F x          ⟩
                       x                 ∎

\end{code}

\begin{code}

distributivity′ : (F : Frame 𝓤 𝓥 𝓦)
                → (x : ⟨ F ⟩)
                → (S : Fam 𝓦 ⟨ F ⟩)
                → let open JoinNotation (λ - → ⋁[ F ] -) in
                  x ∧[ F ] (⋁⟨ i ⟩ (S [ i ]))
                ＝ ⋁⟨ i ⟩ ((S [ i ]) ∧[ F ] x)
distributivity′ F x S =
 x ∧[ F ] (⋁⟨ i ⟩ S [ i ])    ＝⟨ distributivity F x S ⟩
 ⋁⟨ i ⟩ (x ∧[ F ] (S [ i ]))  ＝⟨ †                    ⟩
 ⋁⟨ i ⟩ (S [ i ]) ∧[ F ] x    ∎
  where
   open PosetReasoning (poset-of F)
   open JoinNotation (λ - → ⋁[ F ] -)

   ‡ = ∧[ F ]-is-commutative x ∘ (_[_] S)
   † = ap (λ - → join-of F (index S , -)) (dfunext fe ‡)

distributivity′-right : (F : Frame 𝓤 𝓥 𝓦)
                      → (x : ⟨ F ⟩)
                      → (S : Fam 𝓦 ⟨ F ⟩)
                      → let open JoinNotation (λ - → ⋁[ F ] -) in
                         (⋁⟨ i ⟩ (S [ i ])) ∧[ F ] x ＝ ⋁⟨ i ⟩ ((S [ i ]) ∧[ F ] x)
distributivity′-right F x S =
 (⋁⟨ i ⟩ (S [ i ])) ∧[ F ] x  ＝⟨ †                     ⟩
 x ∧[ F ] (⋁⟨ i ⟩ (S [ i ]))  ＝⟨ distributivity′ F x S ⟩
 ⋁⟨ i ⟩ (S [ i ] ∧[ F ] x)    ∎
  where
   open JoinNotation (λ - → ⋁[ F ] -)

   † = ∧[ F ]-is-commutative (⋁⟨ i ⟩ (S [ i ])) x

absorption-right : (F : Frame 𝓤 𝓥 𝓦) (x y : ⟨ F ⟩)
                 → x ∨[ F ] (x ∧[ F ] y) ＝ x
absorption-right F x y = ≤-is-antisymmetric (poset-of F) β γ
 where
  β : ((x ∨[ F ] (x ∧[ F ] y)) ≤[ poset-of F ] x) holds
  β = ∨[ F ]-least (≤-is-reflexive (poset-of F) x) (∧[ F ]-lower₁ x y)

  γ : (x ≤[ poset-of F ] (x ∨[ F ] (x ∧[ F ] y))) holds
  γ = ∨[ F ]-upper₁ x (x ∧[ F ] y)

absorption-left : (F : Frame 𝓤 𝓥 𝓦) (x y : ⟨ F ⟩)
                → x ∨[ F ] (y ∧[ F ] x) ＝ x
absorption-left F x y =
 x ∨[ F ] (y ∧[ F ] x) ＝⟨ ap (λ - → x ∨[ F ] -) (∧[ F ]-is-commutative y x) ⟩
 x ∨[ F ] (x ∧[ F ] y) ＝⟨ absorption-right F x y                            ⟩
 x                     ∎

absorptionᵒᵖ-right : (F : Frame 𝓤 𝓥 𝓦) → (x y : ⟨ F ⟩) → x ∧[ F ] (x ∨[ F ] y) ＝ x
absorptionᵒᵖ-right F x y = ≤-is-antisymmetric (poset-of F) β γ
 where
  β : ((x ∧[ F ] (x ∨[ F ] y)) ≤[ poset-of F ] x) holds
  β = ∧[ F ]-lower₁ x (x ∨[ F ] y)

  γ : (x ≤[ poset-of F ] (x ∧[ F ] (x ∨[ F ] y))) holds
  γ = ∧[ F ]-greatest x (x ∨[ F ] y) x
       (≤-is-reflexive (poset-of F) x)
       (∨[ F ]-upper₁ x y)

absorptionᵒᵖ-left : (F : Frame 𝓤 𝓥 𝓦) (x y : ⟨ F ⟩)
                  → x ∧[ F ] (y ∨[ F ] x) ＝ x
absorptionᵒᵖ-left F x y =
 x ∧[ F ] (y ∨[ F ] x)  ＝⟨ ap (λ - → x ∧[ F ] -) (∨[ F ]-is-commutative y x) ⟩
 x ∧[ F ] (x ∨[ F ] y)  ＝⟨ absorptionᵒᵖ-right F x y                          ⟩
 x                      ∎

binary-distributivity : (F : Frame 𝓤 𝓥 𝓦)
                      → (x y z : ⟨ F ⟩)
                      → x ∧[ F ] (y ∨[ F ] z) ＝ (x ∧[ F ] y) ∨[ F ] (x ∧[ F ] z)
binary-distributivity {𝓦 = 𝓦} F x y z =
 x ∧[ F ] (y ∨[ F ] z)                            ＝⟨ † ⟩
 ⋁[ F ] ⁅ x ∧[ F ] w ∣ w ε binary-family 𝓦 y z ⁆  ＝⟨ ‡ ⟩
 (x ∧[ F ] y) ∨[ F ] (x ∧[ F ] z)                 ∎
  where
   † = distributivity F x (binary-family 𝓦 y z)
   ‡ = ap (λ - → join-of F -) (fmap-binary-family 𝓦 (λ - → x ∧[ F ] -) y z)

binary-distributivity-right : (F : Frame 𝓤 𝓥 𝓦)
                            → {x y z : ⟨ F ⟩}
                            → (x ∨[ F ] y) ∧[ F ] z ＝ (x ∧[ F ] z) ∨[ F ] (y ∧[ F ] z)
binary-distributivity-right F {x} {y} {z} =
 (x ∨[ F ] y) ∧[ F ] z             ＝⟨ Ⅰ ⟩
 z ∧[ F ] (x ∨[ F ] y)             ＝⟨ Ⅱ ⟩
 (z ∧[ F ] x) ∨[ F ] (z ∧[ F ] y)  ＝⟨ Ⅲ ⟩
 (x ∧[ F ] z) ∨[ F ] (z ∧[ F ] y)  ＝⟨ Ⅳ ⟩
 (x ∧[ F ] z) ∨[ F ] (y ∧[ F ] z)  ∎
  where
   Ⅰ = ∧[ F ]-is-commutative (x ∨[ F ] y) z
   Ⅱ = binary-distributivity F z x y
   Ⅲ = ap (λ - → - ∨[ F ] (z ∧[ F ] y)) (∧[ F ]-is-commutative z x)
   Ⅳ = ap (λ - → (x ∧[ F ] z) ∨[ F ] -) (∧[ F ]-is-commutative z y)

binary-distributivity-op : (F : Frame 𝓤 𝓥 𝓦) (x y z : ⟨ F ⟩)
                         → x ∨[ F ] (y ∧[ F ] z) ＝ (x ∨[ F ] y) ∧[ F ] (x ∨[ F ] z)
binary-distributivity-op F x y z =
 x ∨[ F ] (y ∧[ F ] z)                                   ＝⟨ †    ⟩
 x ∨[ F ] ((z ∧[ F ] x) ∨[ F ] (z ∧[ F ] y))             ＝⟨ I    ⟩
 x ∨[ F ] (z ∧[ F ] (x ∨[ F ] y))                        ＝⟨ II   ⟩
 x ∨[ F ] ((x ∨[ F ] y) ∧[ F ] z)                        ＝⟨ III  ⟩
 (x ∧[ F ] (x ∨[ F ] y)) ∨[ F ] ((x ∨[ F ] y) ∧[ F ] z)  ＝⟨ IV   ⟩
 ((x ∨[ F ] y) ∧[ F ] x) ∨[ F ] ((x ∨[ F ] y) ∧[ F ] z)  ＝⟨ V    ⟩
 (x ∨[ F ] y) ∧[ F ] (x ∨[ F ] z)                        ∎
  where
   w   = (x ∨[ F ] y) ∧[ F ] z

   I   = ap (λ - → x ∨[ F ] -) ((binary-distributivity F z x y) ⁻¹)
   II  = ap (λ - → x ∨[ F ] -) (∧[ F ]-is-commutative z (x ∨[ F ] y))
   III = ap (λ - → - ∨[ F ] w) (absorptionᵒᵖ-right F x y) ⁻¹
   IV  = ap (λ - → - ∨[ F ] w) (∧[ F ]-is-commutative x (x ∨[ F ] y))
   V   = (binary-distributivity F (x ∨[ F ] y) x z) ⁻¹

   † : x ∨[ F ] (y ∧[ F ] z) ＝ x ∨[ F ] ((z ∧[ F ] x) ∨[ F ] (z ∧[ F ] y))
   † = x ∨[ F ] (y ∧[ F ] z)                        ＝⟨ i    ⟩
       (x ∨[ F ] (z ∧[ F ] x)) ∨[ F ] (y ∧[ F ] z)  ＝⟨ ii   ⟩
       (x ∨[ F ] (z ∧[ F ] x)) ∨[ F ] (z ∧[ F ] y)  ＝⟨ iii  ⟩
       x ∨[ F ] ((z ∧[ F ] x) ∨[ F ] (z ∧[ F ] y))  ∎
        where
         i   = ap (λ - → - ∨[ F ] (y ∧[ F ] z)) (absorption-left F x z) ⁻¹
         ii  = ap (λ - → (x ∨[ F ] (z ∧[ F ] x)) ∨[ F ] -) (∧[ F ]-is-commutative y z)
         iii = ∨[ F ]-assoc x (z ∧[ F ] x) (z ∧[ F ] y)

\end{code}

\begin{code}

⋁[_]-iterated-join : (F : Frame 𝓤 𝓥 𝓦) (I : 𝓦 ̇ )(J : I → 𝓦 ̇ )
                → (f : (i : I) → J i → ⟨ F ⟩)
                → ⋁[ F ] ((Σ i ꞉ I , J i) , uncurry f)
                ＝ ⋁[ F ] ⁅ ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ∣ i ∶ I ⁆
⋁[ F ]-iterated-join I J f = ⋁[ F ]-unique _ _ (β , γ)
 where
  open Joins (λ x y → x ≤[ poset-of F ] y)
  open PosetReasoning (poset-of F) renaming (_■ to _QED)

  β : ((⋁[ F ] (Σ J , uncurry f))
      is-an-upper-bound-of
      ⁅ ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ∣ i ∶ I ⁆) holds
  β i = ⋁[ F ]-least _ (_ , λ jᵢ → ⋁[ F ]-upper _ (i , jᵢ))

  γ : (Ɐ (u , _) ꞉ upper-bound ⁅ ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ∣ i ∶ I ⁆ ,
       (⋁[ F ] (Σ J , uncurry f)) ≤[ poset-of F ] _ ) holds
  γ (u , p) = ⋁[ F ]-least (Σ J , uncurry f) (_ , δ)
   where
    δ : (u is-an-upper-bound-of (Σ J , uncurry f)) holds
    δ  (i , j) = f i j                      ≤⟨ ⋁[ F ]-upper _ j ⟩
                 ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ≤⟨ p i              ⟩
                 u                          QED

\end{code}

\begin{code}

∧[_]-is-idempotent : (F : Frame 𝓤 𝓥 𝓦)
                   → (x : ⟨ F ⟩) → x ＝ x ∧[ F ] x
∧[ F ]-is-idempotent x = ≤-is-antisymmetric (poset-of F) β γ
 where
  α : (x ≤[ poset-of F ] x) holds
  α = ≤-is-reflexive (poset-of F) x

  β : (x ≤[ poset-of F ] (x ∧[ F ] x)) holds
  β = ∧[ F ]-greatest x x x α α

  γ : ((x ∧[ F ] x) ≤[ poset-of F ] x) holds
  γ = ∧[ F ]-lower₁ x x

∨[_]-is-idempotent : (F : Frame 𝓤 𝓥 𝓦)
                   → (x : ⟨ F ⟩) → x ＝ x ∨[ F ] x
∨[ F ]-is-idempotent x = ≤-is-antisymmetric (poset-of F) † ‡
 where
  † : (x ≤[ poset-of F ] (x ∨[ F ] x)) holds
  † = ∨[ F ]-upper₁ x x

  ‡ : ((x ∨[ F ] x) ≤[ poset-of F ] x) holds
  ‡ = ∨[ F ]-least (≤-is-reflexive (poset-of F) x) (≤-is-reflexive (poset-of F) x)

\end{code}

\begin{code}

distributivity+ : (F : Frame 𝓤 𝓥 𝓦)
                → let open JoinNotation (λ - → ⋁[ F ] -) in
                  (U@(I , _) V@(J , _) : Fam 𝓦 ⟨ F ⟩)
                → (⋁⟨ i ⟩ (U [ i ])) ∧[ F ] (⋁⟨ j ⟩ (V [ j ]))
                ＝ (⋁⟨ (i , j) ∶ (I × J)  ⟩ ((U [ i ]) ∧[ F ] (V [ j ])))
distributivity+ F U@(I , _) V@(J , _) =
 (⋁⟨ i ⟩ (U [ i ])) ∧[ F ] (⋁⟨ j ⟩ (V [ j ]))     ＝⟨ i   ⟩
 (⋁⟨ j ⟩ (V [ j ])) ∧[ F ] (⋁⟨ i ⟩ (U [ i ]))     ＝⟨ ii  ⟩
 (⋁⟨ i ⟩ (⋁⟨ j ⟩ (V [ j ])) ∧[ F ] (U [ i ]))     ＝⟨ iii ⟩
 (⋁⟨ i ⟩ (U [ i ] ∧[ F ] (⋁⟨ j ⟩ (V [ j ]))))     ＝⟨ iv  ⟩
 (⋁⟨ i ⟩ (⋁⟨ j ⟩ (U [ i ] ∧[ F ] V [ j ])))       ＝⟨ v   ⟩
 (⋁⟨ (i , j) ∶ I × J  ⟩ (U [ i ] ∧[ F ] V [ j ])) ∎
 where
  open JoinNotation (λ - → ⋁[ F ] -)

  i   = ∧[ F ]-is-commutative (⋁⟨ i ⟩ (U [ i ])) (⋁⟨ j ⟩ (V [ j ]))
  ii  = distributivity F (⋁⟨ j ⟩ (V [ j ])) U
  iii = ap
         (λ - → ⋁[ F ] (I , -))
         (dfunext fe λ i → ∧[ F ]-is-commutative (⋁⟨ j ⟩ V [ j ]) (U [ i ]))
  iv  = ap
         (λ - → join-of F (I , -))
         (dfunext fe λ i → distributivity F (U [ i ]) V)
  v   = ⋁[ F ]-iterated-join I (λ _ → J) (λ i j → U [ i ] ∧[ F ] V [ j ]) ⁻¹

\end{code}

\section{Bases of frames}

We first define the notion of a “small” basis for a frame. Given a
(𝓤, 𝓥, 𝓦)-frame, a small basis for it is a 𝓦-family, which has a
further subfamily covering any given element of the frame.

\begin{code}

is-basis-for : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) ̇
is-basis-for {𝓦 = 𝓦} F (I , β) =
 (x : ⟨ F ⟩) → Σ J ꞉ Fam 𝓦 I , (x is-lub-of ⁅ β j ∣ j ε J ⁆) holds
  where
   open Joins (λ x y → x ≤[ poset-of F ] y)

\end{code}

A 𝓦-frame has a (small) basis iff there exists a 𝓦-family
that forms a basis for it. Having a basis should be a property and
not a structure so this is important.

\begin{code}

has-basis : (F : Frame 𝓤 𝓥 𝓦) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
has-basis {𝓦 = 𝓦} F = ∥ Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ , is-basis-for F ℬ ∥Ω

covering-index-family : (F : Frame 𝓤 𝓥 𝓦) (ℬ : Fam 𝓦 ⟨ F ⟩) (b : is-basis-for F ℬ)
                      → ⟨ F ⟩ → Fam 𝓦 (index ℬ)
covering-index-family F ℬ p x = pr₁ (p x)

covers : (F : Frame 𝓤 𝓥 𝓦) (ℬ : Fam 𝓦 ⟨ F ⟩) (b : is-basis-for F ℬ)
       → (x : ⟨ F ⟩) → let
                         ℐ = covering-index-family F ℬ b x
                       in
                         x ＝ ⋁[ F ] ⁅ ℬ [ i ] ∣ i ε ℐ ⁆
covers F ℬ b x = ⋁[ F ]-unique ⁅ ℬ [ i ] ∣ i ε ℐ ⁆ x (pr₂ (b x))
 where
  ℐ = covering-index-family F ℬ b x

\end{code}

We also have the notion of a directed basis, in which every covering
family is directed.

\begin{code}

is-directed-basis : (F : Frame 𝓤 𝓥 𝓦) (ℬ : Fam 𝓦 ⟨ F ⟩)
                  → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
is-directed-basis {𝓦 = 𝓦} F ℬ =
 Σ b ꞉ is-basis-for F ℬ ,
  Π x ꞉ ⟨ F ⟩ , let
                 𝒥 = covering-index-family F ℬ b x
                in
                 is-directed F ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ holds

has-directed-basis₀ : (F : Frame 𝓤 𝓥 𝓦) → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) ̇
has-directed-basis₀ {𝓦 = 𝓦} F =
 Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ , is-directed-basis F ℬ

has-directed-basis : (F : Frame 𝓤 𝓥 𝓦) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
has-directed-basis {𝓦 = 𝓦} F = ∥ has-directed-basis₀ F ∥Ω

directed-cover : (F : Frame 𝓤 𝓥 𝓦) → has-directed-basis₀ F → ⟨ F ⟩ → Fam 𝓦 ⟨ F ⟩
directed-cover F (ℬ , β) U = ⁅ ℬ [ i ] ∣ i ε pr₁ (pr₁ β U) ⁆

covers-are-directed : (F : Frame 𝓤 𝓥 𝓦)
                    → (b : has-directed-basis₀ F)
                    → (U : ⟨ F ⟩)
                    → is-directed F (directed-cover F b U) holds
covers-are-directed F (ℬ , β) U = pr₂ β U

\end{code}

The main development in this section is that every small basis can be
extended to a directed one whilst keeping it small.

\begin{code}

join-in-frame : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ⟨ F ⟩) → List (index S) → ⟨ F ⟩
join-in-frame F S = foldr (λ i - → (S [ i ]) ∨[ F ] -) 𝟎[ F ]

directify : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Fam 𝓦 ⟨ F ⟩
directify F (I , α) = List I , (foldr (λ i - → α i ∨[ F ] -) 𝟎[ F ])
 where open PosetNotation (poset-of F)

\end{code}

We could have defined `directify` in an alternative way, using the auxiliary
`join-list` function:

\begin{code}

join-list : (F : Frame 𝓤 𝓥 𝓦) → List ⟨ F ⟩ → ⟨ F ⟩
join-list F = foldr (binary-join F) 𝟎[ F ]

infix 3 join-list

syntax join-list F xs = ⋁ₗ[ F ] xs

join-in-frame′ : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ⟨ F ⟩) → List (index S) → ⟨ F ⟩
join-in-frame′ F (I , α) = join-list F ∘ map α

directify′ : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Fam 𝓦 ⟨ F ⟩
directify′ F (I , α) = List I , join-in-frame′ F (I , α)

\end{code}

However, the direct definition given in `directify` turns out to be more
convenient for some purposes, so we avoid using `directify′` as the default
definition. It is a trivial fact that `directify` is the same as `directify′`.

\begin{code}

join-in-frame-equality : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ⟨ F ⟩)
                       → join-in-frame F S ∼ join-in-frame′ F S
join-in-frame-equality F S []       = refl
join-in-frame-equality F S (i ∷ is) =
 join-in-frame F S (i ∷ is)              ＝⟨refl⟩
 (S [ i ]) ∨[ F ] join-in-frame  F S is  ＝⟨ †    ⟩
 (S [ i ]) ∨[ F ] join-in-frame′ F S is  ＝⟨refl⟩
 join-in-frame′ F S (i ∷ is)             ∎
  where
   † = ap (λ - → (S [ i ]) ∨[ F ] -) (join-in-frame-equality F S is)

\end{code}

Note that `directify` is a monoid homomorphism from the free monoid on I
to (_∨_, 𝟎).

\begin{code}

directify-functorial : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ⟨ F ⟩)
                     → (is js : List (index S))
                     → directify F S [ is ++ js ]
                     ＝ directify F S [ is ] ∨[ F ] directify F S [ js ]
directify-functorial F S@(I , α) = γ
 where
  γ : (is js : List I)
    → directify F S [ is ++ js ]
    ＝ directify F S [ is ] ∨[ F ] directify F S [ js ]
  γ []       js = directify F S [ [] ++ js ]          ＝⟨refl⟩
                  directify F S [ js ]                ＝⟨ †    ⟩
                  𝟎[ F ]  ∨[ F ] directify F S [ js ] ∎
                   where
                    † = 𝟎-right-unit-of-∨ F (directify F S [ js ]) ⁻¹
  γ (i ∷ is) js =
   directify F S [ (i ∷ is) ++ js ]                              ＝⟨refl⟩
   α i ∨[ F ] directify F S [ is ++ js ]                         ＝⟨ †    ⟩
   α i ∨[ F ] (directify F S [ is ] ∨[ F ] directify F S [ js ]) ＝⟨ ‡    ⟩
   (α i ∨[ F ] directify F S [ is ]) ∨[ F ] directify F S [ js ] ＝⟨refl⟩
   directify F S [ i ∷ is ] ∨[ F ] directify F S [ js ]          ∎
    where
     † = ap (λ - → binary-join F (α i) -) (γ is js)
     ‡ = ∨[ F ]-assoc (α i) (directify F S [ is ]) (directify F S [ js ]) ⁻¹

\end{code}

`directify` does what it is supposed to do: the family it gives is a
directed one.

\begin{code}

directify-is-directed : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ⟨ F ⟩)
                      → is-directed F (directify F S) holds
directify-is-directed F S@(I , α) = ∣ [] ∣ , υ
 where
  open PropositionalTruncation pt
  open PosetNotation (poset-of F)

  υ : (Ɐ is ꞉ List I
     , Ɐ js ꞉ List I
     , (Ǝ ks ꞉ List I
      , (((directify F S [ is ] ≤ directify F S [ ks ])
        ∧ (directify F S [ js ] ≤ directify F S [ ks ])) holds))) holds
  υ is js = ∣ (is ++ js) , β , γ ∣
    where
     open PosetReasoning (poset-of F)

     ‡ = directify-functorial F S is js ⁻¹

     β : (directify F S [ is ] ≤ directify F S [ is ++ js ]) holds
     β = directify F S [ is ]                             ≤⟨ † ⟩
         directify F S [ is ] ∨[ F ] directify F S [ js ] ＝⟨ ‡ ⟩ₚ
         directify F S [ is ++ js ]                       ■
          where
           † = ∨[ F ]-upper₁ (directify F S [ is ]) (directify F S [ js ])

     γ : (directify F S [ js ] ≤ directify F S [ is ++ js ]) holds
     γ = directify F S [ js ]                             ≤⟨ † ⟩
         directify F S [ is ] ∨[ F ] directify F S [ js ] ＝⟨ ‡ ⟩ₚ
         directify F S [ is ++ js ] ■
          where
           † = ∨[ F ]-upper₂ (directify F S [ is ]) (directify F S [ js ])

closed-under-binary-joins : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
closed-under-binary-joins {𝓦 = 𝓦} F S =
 Ɐ i ꞉ index S , Ɐ j ꞉ index S ,
  Ǝ k ꞉ index S , ((S [ k ]) is-lub-of (binary-family 𝓦 (S [ i ]) (S [ j ]))) holds
   where
    open Joins (λ x y → x ≤[ poset-of F ] y)

contains-bottom : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
contains-bottom F U =  Ǝ i ꞉ index U , is-bottom F (U [ i ]) holds

closed-under-finite-joins : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
closed-under-finite-joins F S =
 contains-bottom F S ∧ closed-under-binary-joins F S

closed-under-fin-joins-implies-directed : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ⟨ F ⟩)
                                        → (closed-under-finite-joins F S
                                        ⇒ is-directed F S) holds
closed-under-fin-joins-implies-directed F S (i₀ , ð) =
 ∥∥-rec (holds-is-prop (is-directed F S)) γ i₀
  where
   open PropositionalTruncation pt
   open PosetNotation (poset-of F)
   open Joins (λ x y → x ≤[ poset-of F ] y)

   γ : (Σ i ꞉ index S , is-bottom F (S [ i ]) holds)
     → is-directed F S holds
   γ (i , _) = ∣ i ∣ , δ
    where
     δ : (m n : index S)
       → (Ǝ o ꞉ index S , ((S [ m ] ≤ S [ o ]) ∧ (S [ n ] ≤ S [ o ])) holds) holds
     δ m n = ∥∥-rec ∃-is-prop ϵ (ð m n)
      where
       ϵ : Σ o ꞉ index S , ((S [ o ]) is-lub-of (binary-family 𝓦 (S [ m ]) (S [ n ]))) holds
         → (Ǝ o ꞉ index S , ((S [ m ] ≤ S [ o ]) ∧ (S [ n ] ≤ S [ o ])) holds) holds
       ϵ (o , ψ , _) = ∣ o , ψ (inl ⋆) , ψ (inr ⋆) ∣

directify-is-closed-under-fin-joins : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ⟨ F ⟩)
                                    → closed-under-finite-joins F (directify F S) holds
directify-is-closed-under-fin-joins F S = † , ‡
 where
  open PropositionalTruncation pt

  † : contains-bottom F (directify F S) holds
  † = ∣ [] , 𝟎-is-bottom F ∣

  ‡ : closed-under-binary-joins F (directify F S) holds
  ‡ is js = ∣ (is ++ js) , ♠ , ♣ ∣
   where
    open Joins (λ x y → x ≤[ poset-of F ] y)
    open PosetReasoning (poset-of F)

    Ͱ = directify-functorial F S is js ⁻¹

    ♠ : ((directify F S [ is ++ js ])
         is-an-upper-bound-of
         ⁅ directify F S [ is ] , directify F S [ js ] ⁆) holds
    ♠ (inl p) = directify F S [ is ]                                ≤⟨ Ⅰ ⟩
                directify F S [ is ] ∨[ F ] directify F S [ js ]    ＝⟨ Ͱ ⟩ₚ
                directify F S [ is ++ js ]                          ■
                 where
                  Ⅰ = ∨[ F ]-upper₁ (directify F S [ is ]) (directify F S [ js ])
    ♠ (inr p) = directify F S [ js ]                              ≤⟨ Ⅰ ⟩
                directify F S [ is ] ∨[ F ] directify F S [ js ]  ＝⟨ Ͱ ⟩ₚ
                directify F S [ is ++ js ]                        ■
                 where
                  Ⅰ = ∨[ F ]-upper₂ (directify F S [ is ]) (directify F S [ js ])

    ♣ : ((u , _) : upper-bound ⁅ directify F S [ is ] , directify F S [ js ] ⁆)
      → ((directify F S [ is ++ js ]) ≤[ poset-of F ] u) holds
    ♣ (u , ζ) =
     directify F S [ is ++ js ]                          ＝⟨ Ͱ ⁻¹ ⟩ₚ
     directify F S [ is ] ∨[ F ] directify F S [ js ]    ≤⟨ ※ ⟩
     u                                                   ■
      where
       ※ = ∨[ F ]-least (ζ (inl ⋆) ) (ζ (inr ⋆))

\end{code}

`directify` also preserves the join while doing what it is supposed to
do.

\begin{code}

directify-preserves-joins : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ⟨ F ⟩)
                          → ⋁[ F ] S ＝ ⋁[ F ] directify F S
directify-preserves-joins F S = ≤-is-antisymmetric (poset-of F) β γ
 where
  open PosetNotation  (poset-of F)
  open PosetReasoning (poset-of F)

  β : ((⋁[ F ] S) ≤ (⋁[ F ] directify F S)) holds
  β = ⋁[ F ]-least S ((⋁[ F ] (directify F S)) , ν)
   where
    ν : (i : index S) → (S [ i ] ≤ (⋁[ F ] directify F S)) holds
    ν i =
     S [ i ]                   ＝⟨ 𝟎-right-unit-of-∨ F (S [ i ]) ⁻¹       ⟩ₚ
     𝟎[ F ] ∨[ F ] S [ i ]     ＝⟨ ∨[ F ]-is-commutative 𝟎[ F ] (S [ i ]) ⟩ₚ
     S [ i ] ∨[ F ] 𝟎[ F ]     ＝⟨ refl                                   ⟩ₚ
     directify F S [ i ∷ [] ]  ≤⟨ ⋁[ F ]-upper (directify F S) (i ∷ [])  ⟩
     ⋁[ F ] directify F S      ■

  γ : ((⋁[ F ] directify F S) ≤[ poset-of F ] (⋁[ F ] S)) holds
  γ = ⋁[ F ]-least (directify F S) ((⋁[ F ] S) , κ)
   where
    κ : (is : List (index S)) → ((directify F S [ is ]) ≤ (⋁[ F ] S)) holds
    κ []       = 𝟎-is-bottom F (⋁[ F ] S)
    κ (i ∷ is) = S [ i ] ∨[ F ] directify F S [ is ] ≤⟨ † ⟩
                 ⋁[ F ] S                              ■
                  where
                   † = ∨[ F ]-least (⋁[ F ]-upper S i) (κ is)

directify-preserves-joins₀ : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ⟨ F ⟩)
                           → let open Joins (λ x y → x ≤[ poset-of F ] y) in
                             (x : ⟨ F ⟩)
                           → (x is-lub-of S ⇒ x is-lub-of directify F S) holds
directify-preserves-joins₀ F S x p =
 transport (λ - → (- is-lub-of directify F S) holds) (q ⁻¹)
  (⋁[ F ]-upper (directify F S) , ⋁[ F ]-least (directify F S))
 where
  open Joins (λ x y → x ≤[ poset-of F ] y)

  abstract
   q : x ＝ ⋁[ F ] directify F S
   q = x                    ＝⟨ ⋁[ F ]-unique S x p           ⟩
       ⋁[ F ] S             ＝⟨ directify-preserves-joins F S ⟩
       ⋁[ F ] directify F S ∎

\end{code}

\begin{code}

directified-basis-is-basis : (F : Frame 𝓤 𝓥 𝓦)
                           → (ℬ : Fam 𝓦 ⟨ F ⟩)
                           → is-basis-for F ℬ
                           → is-basis-for F (directify F ℬ)
directified-basis-is-basis {𝓦 = 𝓦} F ℬ β = β↑
 where
  open PosetNotation (poset-of F)
  open Joins (λ x y → x ≤ y)

  ℬ↑ = directify F ℬ

  𝒥 : ⟨ F ⟩ → Fam 𝓦 (index ℬ)
  𝒥 x = pr₁ (β x)

  𝒦 : ⟨ F ⟩ → Fam 𝓦 (List (index ℬ))
  𝒦 x = List (index (𝒥 x)) , (λ - → 𝒥 x [ - ]) <$>_

  abstract
   φ : (x : ⟨ F ⟩)
     → (is : List (index (𝒥 x)))
     → directify F ℬ [ (λ - → 𝒥 x [ - ]) <$> is ]
     ＝ directify F ⁅ ℬ [ j ] ∣ j ε 𝒥 x ⁆ [ is ]
   φ x []       = refl
   φ x (i ∷ is) = ap (λ - → (_ ∨[ F ] -)) (φ x is)

  ψ : (x : ⟨ F ⟩)
    → ⁅ directify F ℬ [ is ] ∣ is ε 𝒦 x ⁆ ＝ directify F ⁅ ℬ [ j ] ∣ j ε 𝒥 x ⁆
  ψ x = to-Σ-＝ (refl , dfunext fe (φ x))

  β↑ : (x : ⟨ F ⟩)
     → Σ J ꞉ Fam 𝓦 (index ℬ↑) , (x is-lub-of ⁅ ℬ↑ [ j ] ∣ j ε J ⁆) holds
  β↑ x = 𝒦 x , transport (λ - → (x is-lub-of -) holds) (ψ x ⁻¹) δ
    where
    p : (x is-lub-of ⁅ ℬ [ j ] ∣ j ε 𝒥 x ⁆) holds
    p = pr₂ (β x)

    δ : (x is-lub-of directify F ⁅ ℬ [ j ] ∣ j ε 𝒥 x ⁆) holds
    δ = directify-preserves-joins₀ F ⁅ ℬ [ j ] ∣ j ε 𝒥 x ⁆ x p

  δ : (x : ⟨ F ⟩)
    → is-directed F ⁅ directify F ℬ [ is ] ∣ is ε 𝒦 x ⁆ holds
  δ x = transport (λ - → is-directed F - holds) (ψ x ⁻¹) ε
    where
    ε = directify-is-directed F ⁅ ℬ [ j ] ∣ j ε 𝒥 x ⁆

covers-of-directified-basis-are-directed : (F : Frame 𝓤 𝓥 𝓦)
                                         → (ℬ : Fam 𝓦 ⟨ F ⟩)
                                         → (β : is-basis-for F ℬ)
                                         → (x : ⟨ F ⟩)
                                         → let
                                            ℬ↑ = directify F ℬ
                                            β↑ = directified-basis-is-basis F ℬ β
                                            𝒥↑ = pr₁ (β↑ x)
                                           in
                                            is-directed F ⁅ ℬ↑ [ i ] ∣ i ε 𝒥↑ ⁆ holds
covers-of-directified-basis-are-directed {𝓦 = 𝓦} F ℬ β x =
 transport (λ - → is-directed F - holds) (ψ ⁻¹) ε
  where
   𝒥 = pr₁ (β x)

   𝒦 : Fam 𝓦 (List (index ℬ))
   𝒦 = ⁅ (λ - → 𝒥 [ - ]) <$> is ∣ is ∶ List (index 𝒥) ⁆

   abstract
    φ : (is : List (index 𝒥))
      → directify F ℬ [ (λ - → 𝒥 [ - ]) <$> is ]
      ＝ directify F ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ [ is ]
    φ []       = refl
    φ (i ∷ is) = ap (λ - → (_ ∨[ F ] -)) (φ is)

    ψ : ⁅ directify F ℬ [ is ] ∣ is ε 𝒦 ⁆ ＝ directify F ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆
    ψ = to-Σ-＝ (refl , dfunext fe φ)

    ε : is-directed F (directify F ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆) holds
    ε = directify-is-directed F ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆

directify-basis : (F : Frame 𝓤 𝓥 𝓦)
                → (has-basis F ⇒ has-directed-basis F) holds
directify-basis {𝓦 = 𝓦} F = ∥∥-rec (holds-is-prop (has-directed-basis F)) γ
 where
  open PropositionalTruncation pt
  open PosetNotation (poset-of F)
  open Joins (λ x y → x ≤ y)

  γ : Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ , is-basis-for F ℬ → has-directed-basis F holds
  γ (ℬ , β) = ∣ directify F ℬ , (directified-basis-is-basis F ℬ β) , δ ∣
   where
    𝒥 : ⟨ F ⟩ → Fam 𝓦 (index ℬ)
    𝒥 x = pr₁ (β x)

    𝒦 : ⟨ F ⟩ → Fam 𝓦 (List (index ℬ))
    𝒦 x = List (index (𝒥 x)) , (λ - → 𝒥 x [ - ]) <$>_

    φ : (x : ⟨ F ⟩)
      → (is : List (index (𝒥 x)))
      → directify F ℬ [ (λ - → 𝒥 x [ - ]) <$> is ]
      ＝ directify F ⁅ ℬ [ j ] ∣ j ε 𝒥 x ⁆ [ is ]
    φ x []       = refl
    φ x (i ∷ is) = ap (λ - → (_ ∨[ F ] -)) (φ x is)

    ψ : (x : ⟨ F ⟩)
      → ⁅ directify F ℬ [ is ] ∣ is ε 𝒦 x ⁆ ＝ directify F ⁅ ℬ [ j ] ∣ j ε 𝒥 x ⁆
    ψ x = to-Σ-＝ (refl , dfunext fe (φ x))

    δ : (x : ⟨ F ⟩)
      → is-directed F ⁅ directify F ℬ [ is ] ∣ is ε 𝒦 x ⁆ holds
    δ x = transport (λ - → is-directed F - holds) (ψ x ⁻¹) ε
     where
      ε = directify-is-directed F ⁅ ℬ [ j ] ∣ j ε 𝒥 x ⁆

\end{code}

\section{Locale notation}

A _locale_ is a type that has a frame of opens.

\begin{code}

record Locale (𝓤 𝓥 𝓦 : Universe) : 𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇ where
 field
  ⟨_⟩ₗ         : 𝓤 ̇
  frame-str-of : frame-structure 𝓥 𝓦 ⟨_⟩ₗ

 𝒪 : Frame 𝓤 𝓥 𝓦
 𝒪 = ⟨_⟩ₗ , frame-str-of

to-locale-＝ : (X Y : Locale 𝓤 𝓥 𝓦) → Locale.𝒪 X ＝ Locale.𝒪 Y → X ＝ Y
to-locale-＝ X Y refl = refl

\end{code}

\section{Cofinality}

\begin{code}

cofinal-in : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Fam 𝓦 ⟨ F ⟩ → Ω (𝓥 ⊔ 𝓦)
cofinal-in F R S =
 Ɐ i ꞉ index R , Ǝ j ꞉ index S , ((R [ i ]) ≤[ poset-of F ] (S [ j ])) holds

cofinal-implies-join-covered : (F : Frame 𝓤 𝓥 𝓦) (R S : Fam 𝓦 ⟨ F ⟩)
                             → cofinal-in F R S holds
                             → ((⋁[ F ] R) ≤[ poset-of F ] (⋁[ F ] S)) holds
cofinal-implies-join-covered F R S φ = ⋁[ F ]-least R ((⋁[ F ] S) , β)
 where
  open PosetReasoning (poset-of F)
  open PropositionalTruncation pt

  β : (i : index R) → ((R [ i ]) ≤[ poset-of F ] (⋁[ F ] S)) holds
  β i = ∥∥-rec (holds-is-prop ((R [ i ]) ≤[ poset-of F ] (⋁[ F ] S))) γ (φ i)
   where
    γ : Σ j ꞉ index S , (R [ i ] ≤[ poset-of F ] (S [ j ])) holds
        → (R [ i ] ≤[ poset-of F ] (⋁[ F ] S)) holds
    γ (j , p) = R [ i ] ≤⟨ p ⟩ S [ j ] ≤⟨ ⋁[ F ]-upper S j ⟩ ⋁[ F ] S ■

bicofinal-implies-same-join : (F : Frame 𝓤 𝓥 𝓦) (R S : Fam 𝓦 ⟨ F ⟩)
                            → cofinal-in F R S holds
                            → cofinal-in F S R holds
                            → ⋁[ F ] R ＝ ⋁[ F ] S
bicofinal-implies-same-join F R S φ ψ =
 ≤-is-antisymmetric
  (poset-of F)
  (cofinal-implies-join-covered F R S φ)
  (cofinal-implies-join-covered F S R ψ)

bicofinal-with-directed-family-implies-directed : (F : Frame 𝓤 𝓥 𝓦)
                                                  (R S : Fam 𝓦 ⟨ F ⟩)
                                                → cofinal-in F R S holds
                                                → cofinal-in F S R holds
                                                → is-directed F R holds
                                                → is-directed F S holds
bicofinal-with-directed-family-implies-directed F R S φ ψ (δ₁ , δ₂) = † , ‡
 where
  open PropositionalTruncation pt
  open PosetNotation (poset-of F)

  † : ∥ index S ∥Ω holds
  † = ∥∥-rec (holds-is-prop ∥ index S ∥Ω) †₁ δ₁
   where
    †₁ : index R → ∥ index S ∥Ω holds
    †₁ i = ∥∥-rec (holds-is-prop ∥ index S ∥Ω) †₂ (φ i)
     where
      †₂ : Σ j ꞉ index S , (R [ i ] ≤ S [ j ]) holds
         → ∥ index S ∥Ω holds
      †₂ = ∣_∣ ∘ pr₁

  ‡ : (j₁ j₂ : index S)
    → (Ǝ j ꞉ index S , (S [ j₁ ] ≤ S [ j ]) holds
                     × (S [ j₂ ] ≤ S [ j ]) holds) holds
  ‡ j₁ j₂ = ∥∥-rec₂ ∃-is-prop ‡₁ (ψ j₁) (ψ j₂)
   where
    ‡₁ : Σ i₁ ꞉ index R , (S [ j₁ ] ≤ R [ i₁ ]) holds
       → Σ i₂ ꞉ index R , (S [ j₂ ] ≤ R [ i₂ ]) holds
       → (Ǝ j ꞉ index S , (S [ j₁ ] ≤ S [ j ]) holds
                        × (S [ j₂ ] ≤ S [ j ]) holds) holds
    ‡₁ (i₁ , p₁) (i₂ , p₂) = ∥∥-rec ∃-is-prop ‡₂ (δ₂ i₁ i₂)
     where
      ‡₂ : Σ i ꞉ index R , (R [ i₁ ] ≤ R [ i ]) holds
                         × (R [ i₂ ] ≤ R [ i ]) holds
         → (Ǝ j ꞉ index S , (S [ j₁ ] ≤ S [ j ]) holds
                          × (S [ j₂ ] ≤ S [ j ]) holds) holds
      ‡₂ (i , q₁ , q₂) = ∥∥-rec ∃-is-prop ‡₃ (φ i)
       where
        ‡₃ : Σ j ꞉ (index S) , (R [ i ] ≤ S [ j ]) holds
           → (Ǝ j ꞉ index S , (S [ j₁ ] ≤ S [ j ]) holds
                            × (S [ j₂ ] ≤ S [ j ]) holds) holds
        ‡₃ (j , p) = ∣ j , r₁ , r₂ ∣
         where
          open PosetReasoning (poset-of F)

          r₁ : (S [ j₁ ] ≤ S [ j ]) holds
          r₁ = S [ j₁ ] ≤⟨ p₁ ⟩ R [ i₁ ] ≤⟨ q₁ ⟩ R [ i ] ≤⟨ p ⟩ S [ j ] ■

          r₂ : (S [ j₂ ] ≤ S [ j ]) holds
          r₂ = S [ j₂ ] ≤⟨ p₂ ⟩ R [ i₂ ] ≤⟨ q₂ ⟩ R [ i ] ≤⟨ p ⟩ S [ j ] ■

open PropositionalTruncation pt

∨[_]-iterated-join : (F : Frame 𝓤 𝓥 𝓦) (S₁ S₂ : Fam 𝓦 ⟨ F ⟩)
                   → ∥ index S₁ ∥
                   → ∥ index S₂ ∥
                   → (⋁[ F ] S₁) ∨[ F ] (⋁[ F ] S₂)
                   ＝ ⋁[ F ] ⁅ (S₁ [ i ]) ∨[ F ] (S₂ [ j ]) ∣ (i , j) ∶ (index S₁ × index S₂) ⁆
∨[_]-iterated-join {𝓦 = 𝓦} F S₁ S₂ i₁ i₂ =
 ≤-is-antisymmetric (poset-of F) † ‡
  where
   open PosetReasoning (poset-of F)
   open Joins (λ x y → x ≤[ poset-of F ] y)

   fam-lhs : Fam 𝓦 ⟨ F ⟩
   fam-lhs = binary-family 𝓦 (⋁[ F ] S₁) (⋁[ F ] S₂)

   fam-rhs : Fam 𝓦 ⟨ F ⟩
   fam-rhs = ⁅ (S₁ [ i ]) ∨[ F ] (S₂ [ j ]) ∣ (i , j) ∶ (index S₁ × index S₂) ⁆

   † : ((⋁[ F ] fam-lhs) ≤[ poset-of F ] (⋁[ F ] fam-rhs)) holds
   † = ∨[ F ]-least †₁ †₂
    where
     ♠ : ((⋁[ F ] fam-rhs) is-an-upper-bound-of S₁) holds
     ♠ i = ∥∥-rec (holds-is-prop (_ ≤[ poset-of F ] _)) ♣ i₂
      where
       ♣ : index S₂
         → ((S₁ [ i ]) ≤[ poset-of F ] (⋁[ F ] fam-rhs)) holds
       ♣ j =
        S₁ [ i ]                       ≤⟨ Ⅰ ⟩
        (S₁ [ i ]) ∨[ F ] (S₂ [ j ])   ≤⟨ Ⅱ ⟩
        ⋁[ F ] fam-rhs                 ■
         where
          Ⅰ = ∨[ F ]-upper₁ (S₁ [ i ]) (S₂ [ j ])

          Ⅱ : (((S₁ [ i ]) ∨[ F ] (S₂ [ j ])) ≤[ poset-of F ] (⋁[ F ] fam-rhs)) holds
          Ⅱ = ⋁[ F ]-upper fam-rhs (i , j)

     †₁ : ((⋁[ F ] S₁) ≤[ poset-of F ] (⋁[ F ] fam-rhs)) holds
     †₁ = ⋁[ F ]-least S₁ ((⋁[ F ] fam-rhs) , ♠)

     ♥ : ((⋁[ F ] fam-rhs) is-an-upper-bound-of S₂) holds
     ♥ j = ∥∥-rec (holds-is-prop (_ ≤[ poset-of F ] _)) ♢ i₁
      where
       ♢ : index S₁ → ((S₂ [ j ]) ≤[ poset-of F ] (⋁[ F ] fam-rhs)) holds
       ♢ i =
        S₂ [ j ]                        ≤⟨ Ⅰ ⟩
        (S₁ [ i ]) ∨[ F ] (S₂ [ j ])    ≤⟨ Ⅱ ⟩
        ⋁[ F ] fam-rhs                  ■
         where
          Ⅰ : ((S₂ [ j ]) ≤[ poset-of F ] (S₁ [ i ] ∨[ F ] S₂ [ j ])) holds
          Ⅰ = ∨[ F ]-upper₂ (S₁ [ i ]) (S₂ [ j ])

          Ⅱ : ((S₁ [ i ] ∨[ F ] S₂ [ j ]) ≤[ poset-of F ] (⋁[ F ] fam-rhs)) holds
          Ⅱ = ⋁[ F ]-upper fam-rhs (i , j)

     †₂ : ((⋁[ F ] S₂) ≤[ poset-of F ] (⋁[ F ] fam-rhs)) holds
     †₂ = ⋁[ F ]-least S₂ ((⋁[ F ] fam-rhs) , ♥)

   ‡ : ((⋁[ F ] fam-rhs) ≤[ poset-of F ] (⋁[ F ] fam-lhs)) holds
   ‡ = ⋁[ F ]-least fam-rhs ((⋁[ F ] fam-lhs) , ‡₁)
    where
     ‡₁ : ((⋁[ F ] fam-lhs) is-an-upper-bound-of fam-rhs) holds
     ‡₁ (i , j) =
      (S₁ [ i ])  ∨[ F ] (S₂ [ j ])   ≤⟨ Ⅰ    ⟩
      (⋁[ F ] S₁) ∨[ F ] (S₂ [ j ])   ≤⟨ Ⅱ    ⟩
      (⋁[ F ] S₁) ∨[ F ] (⋁[ F ] S₂)  ＝⟨ Ⅲ   ⟩ₚ
      ⋁[ F ] fam-lhs                  ■
       where
        Ⅰ = ∨[ F ]-left-monotone  (⋁[ F ]-upper S₁ i)
        Ⅱ = ∨[ F ]-right-monotone (⋁[ F ]-upper S₂ j)
        Ⅲ = refl

\end{code}

If a function preserves (1) binary joins and (2) directed joins then it
preserves arbitrary joins.

\begin{code}

sc-and-∨-preserving-⇒-⋁-preserving : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤′ 𝓥′ 𝓦)
                                   → (h : ⟨ F ⟩ → ⟨ G ⟩)
                                   → is-scott-continuous F G h holds
                                   → (h 𝟎[ F ] ＝ 𝟎[ G ])
                                   → (((x y : ⟨ F ⟩) → h (x ∨[ F ] y) ＝ h x ∨[ G ] h y))
                                   → is-join-preserving F G h holds
sc-and-∨-preserving-⇒-⋁-preserving F G h ζ ψ φ S =
 h (⋁[ F ] S)              ＝⟨ ap h p ⟩
 h (⋁[ F ] S↑)             ＝⟨ ♠      ⟩
 ⋁[ G ] ⁅ h x⃗ ∣ x⃗ ε S↑ ⁆   ＝⟨ ♥      ⟩
 ⋁[ G ] ⁅ h x ∣ x ε S ⁆    ∎
  where
   open PropositionalTruncation pt
   open PosetReasoning (poset-of G)

   S↑ = directify F S

   δ : is-directed F S↑ holds
   δ = directify-is-directed F S

   p : ⋁[ F ] S ＝ ⋁[ F ] S↑
   p = directify-preserves-joins F S

   ♠ = ⋁[ G ]-unique ⁅ h x ∣ x ε S↑ ⁆ (h (⋁[ F ] S↑)) (ζ S↑ δ)

   open Joins (λ x y → x ≤[ poset-of G ] y)

   lemma : ((⋁[ G ] ⁅ h x ∣ x ε S ⁆) is-an-upper-bound-of ⁅ h x⃗ ∣ x⃗ ε S↑ ⁆) holds
   lemma [] =
    h 𝟎[ F ]                  ＝⟨ ψ ⟩ₚ
    𝟎[ G ]                    ≤⟨ 𝟎-is-bottom G (⋁[ G ] ⁅ h x ∣ x ε S ⁆) ⟩
    ⋁[ G ] ⁅ h x ∣ x ε S ⁆    ■
   lemma (i ∷ i⃗) =
    h ((S [ i ]) ∨[ F ] directify F S [ i⃗ ])    ＝⟨ φ _ _ ⟩ₚ
    h (S [ i ]) ∨[ G ] h (directify F S [ i⃗ ])  ≤⟨ †     ⟩
    ⋁[ G ] ⁅ h x ∣ x ε S ⁆                      ■
     where
      †₀ : (h (S [ i ]) ≤[ poset-of G ] (⋁[ G ] ⁅ h x ∣ x ε S ⁆)) holds
      †₀ = ⋁[ G ]-upper ⁅ h x ∣ x ε S ⁆ i

      †₁ : (h (directify F S [ i⃗ ]) ≤[ poset-of G ] (⋁[ G ] ⁅ h x ∣ x ε S ⁆)) holds
      †₁ = lemma i⃗

      †  = ∨[ G ]-least †₀ †₁

   ♥₁ : ((⋁[ G ] ⁅ h x⃗ ∣ x⃗ ε S↑ ⁆) ≤[ poset-of G ] (⋁[ G ] ⁅ h x ∣ x ε S ⁆)) holds
   ♥₁ = ⋁[ G ]-least ⁅ h x⃗ ∣ x⃗ ε S↑ ⁆ ((⋁[ G ] ⁅ h x ∣ x ε S ⁆) , lemma)

   ♥₂ : ((⋁[ G ] ⁅ h x ∣ x ε S ⁆) ≤[ poset-of G ] (⋁[ G ] ⁅ h x⃗ ∣ x⃗ ε S↑ ⁆)) holds
   ♥₂ = ⋁[ G ]-least ⁅ h x ∣ x ε S ⁆ ((⋁[ G ] ⁅ h x⃗ ∣ x⃗ ε S↑ ⁆) , †)
    where
     † : ((⋁[ G ] ⁅ h x⃗ ∣ x⃗ ε S↑ ⁆) is-an-upper-bound-of ⁅ h x ∣ x ε S ⁆) holds
     † i = h (S [ i ])                ＝⟨ ap h (𝟎-left-unit-of-∨ F (S [ i ]) ⁻¹) ⟩ₚ
           h (S [ i ] ∨[ F ] 𝟎[ F ])  ＝⟨ refl ⟩ₚ
           h (S↑ [ i ∷ [] ])          ≤⟨ ‡ ⟩
           ⋁[ G ] ⁅ h x⃗ ∣ x⃗ ε S↑ ⁆    ■
            where
             ‡ = ⋁[ G ]-upper ⁅ h x⃗ ∣ x⃗ ε S↑ ⁆ (i ∷ [])

   ♥ = ≤-is-antisymmetric (poset-of G) ♥₁ ♥₂

join-𝟎-lemma₁ : (F : Frame 𝓤 𝓥 𝓦)
              → {x y : ⟨ F ⟩}
              → x ∨[ F ] y ＝ 𝟎[ F ]
              → x ＝ 𝟎[ F ]
join-𝟎-lemma₁ F {x} {y} p = only-𝟎-is-below-𝟎 F x †
 where
  open PosetReasoning (poset-of F)

  † : (x ≤[ poset-of F ] 𝟎[ F ]) holds
  † = x ≤⟨ ∨[ F ]-upper₁ x y ⟩ x ∨[ F ] y ＝⟨ p ⟩ₚ 𝟎[ F ] ■

join-𝟎-lemma₂ : (F : Frame 𝓤 𝓥 𝓦)
              → {x y : ⟨ F ⟩}
              → x ∨[ F ] y ＝ 𝟎[ F ]
              → y ＝ 𝟎[ F ]
join-𝟎-lemma₂ F {x} {y} p = only-𝟎-is-below-𝟎 F y †
 where
  open PosetReasoning (poset-of F)

  † : (y ≤[ poset-of F ] 𝟎[ F ]) holds
  † = y ≤⟨ ∨[ F ]-upper₂ x y ⟩ x ∨[ F ] y ＝⟨ p ⟩ₚ 𝟎[ F ] ■

\end{code}

The proofs `order-is-set`, `frame-data-is-set`, and `frame-structure-is-set`
below have been been added on 2024-04-17.

\begin{code}

order-is-set : {𝓥 : Universe} (pe : propext 𝓥) (A : 𝓤 ̇ ) → is-set (A → A → Ω 𝓥)
order-is-set {𝓥} pe A {_≤₁_} {_≤₂_} =
 Π-is-set fe λ x → Π-is-set fe λ y → Ω-is-set fe pe

frame-data-is-set : (A : 𝓤 ̇ ) (σ : is-set A) (𝓥 𝓦 : Universe) → propext 𝓥 → is-set (frame-data 𝓥 𝓦 A)
frame-data-is-set A σ 𝓥 𝓦 pe =
 Σ-is-set (order-is-set pe A) λ _≤_ →
  ×-is-set
   σ
   (×-is-set (Π-is-set fe λ _ → Π-is-set fe λ _ → σ) (Π-is-set fe λ _ → σ))

frame-structure-is-set : {𝓤 : Universe}
                       → (A : 𝓤 ̇ ) (𝓥 𝓦 : Universe)
                       → propext 𝓥
                       → is-set (frame-structure 𝓥 𝓦 A)
frame-structure-is-set A 𝓥 𝓦 pe {(d₁ , p₁)} {(d₂ , p₂)} =
 Σ-is-set
  (frame-data-is-set A σ 𝓥 𝓦 pe)
  (λ d → props-are-sets (satisfying-frame-laws-is-prop d))
   where
    σ : is-set A
    σ = carrier-of-[ poset-of (A , (d₁ , p₁)) ]-is-set

\end{code}

Added on 2024-08-18.

\begin{code}

open import UF.Equiv using (_≃_; logically-equivalent-props-are-equivalent)
open import UF.Size using (_is_small)

local-smallness-of-frame-gives-local-smallness-of-carrier
 : (F : Frame 𝓤 𝓥 𝓦)
 → (x y : ⟨ F ⟩)
 → (x ＝ y) is 𝓥 small
local-smallness-of-frame-gives-local-smallness-of-carrier F x y =
 (x ≣[ poset-of F ] y) holds , e
  where
   open PosetNotation (poset-of F) using (_≤_)

   s : (x ≣[ poset-of F ] y) holds → x ＝ y
   s = uncurry (≤-is-antisymmetric (poset-of F))

   r : x ＝ y → (x ≣[ poset-of F ] y) holds
   r p = reflexivity+ (poset-of F) p , reflexivity+ (poset-of F) (p ⁻¹)

   e : (x ≣[ poset-of F ] y) holds ≃ (x ＝ y)
   e = logically-equivalent-props-are-equivalent
        (holds-is-prop (x ≣[ poset-of F ] y))
        carrier-of-[ poset-of F ]-is-set
        s
        r

local-smallness-of-carrier-gives-local-smallness-of-frame
 : (F : Frame 𝓤 𝓥 𝓦)
 → (x y : ⟨ F ⟩)
 → (x ≤[ poset-of F ] y) holds is 𝓤 small
local-smallness-of-carrier-gives-local-smallness-of-frame F x y =
 (x ∧[ F ] y ＝ x) , e
  where
   open PosetNotation (poset-of F) using (_≤_)

   s : x ∧[ F ] y ＝ x → (x ≤ y) holds
   s p = connecting-lemma₂ F (p ⁻¹)

   r : (x ≤ y) holds → x ∧[ F ] y ＝ x
   r p = connecting-lemma₁ F p ⁻¹

   e : (x ∧[ F ] y ＝ x) ≃ (x ≤ y) holds
   e = logically-equivalent-props-are-equivalent
        carrier-of-[ poset-of F ]-is-set
        (holds-is-prop (x ≤ y))
        s
        r

\end{code}
