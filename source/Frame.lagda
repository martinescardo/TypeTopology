Ayberk Tosun, 8 March 2021.

Ported from `ayberkt/formal-topology-in-UF`.

 * Frames.
 * Frame homomorphisms.
 * Frame bases.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT hiding (𝟚)
open import UF-Base
open import UF-PropTrunc
open import UF-FunExt
open import UF-PropTrunc
open import List hiding ([_])

module Frame
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import UF-Subsingletons
open import UF-Subsingleton-Combinators
open import UF-Subsingletons-FunExt

open AllCombinators pt fe

\end{code}

\section{Preliminaries}

By Fam_𝓤(A), we denote the type of families on type A with index types
living in universe 𝓤.

\begin{code}

private
  variable
    𝓤′ 𝓥′ 𝓦′ 𝓤′′ 𝓥′′ : Universe

Fam : (𝓤 : Universe) → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
Fam 𝓤 A = Σ I ꞉ (𝓤 ̇) , (I → A)

fmap-syntax : {A : 𝓤 ̇} {B : 𝓥 ̇}
            → (A → B) → Fam 𝓦 A → Fam 𝓦 B
fmap-syntax h (I , f) = I , h ∘ f

infix 2 fmap-syntax

syntax fmap-syntax (λ x → e) U = ⁅ e ∣ x ε U ⁆

compr-syntax : {A : 𝓤 ̇} (I : 𝓦 ̇) → (I → A) → Fam 𝓦 A
compr-syntax I f = I , f

infix 2 compr-syntax

syntax compr-syntax I (λ x → e) = ⁅ e ∣ x ∶ I ⁆

\end{code}

We define two projections for families: (1) for the index type,
and (2) for the enumeration function.

\begin{code}

index : {A : 𝓤 ̇} → Fam 𝓥 A → 𝓥 ̇
index (I , _) = I

_[_] : {A : 𝓤 ̇} → (U : Fam 𝓥 A) → index U → A
(_ , f) [ i ] = f i

infix 9 _[_]

\end{code}

We define some order-theoretic notions that are also defined in the
`Dcpo` module. Ideally, this should be factored out into a standalone
module to be imported by both this module and the `Dcpo` module.

\begin{code}

is-reflexive : {A : 𝓤 ̇} → (A → A → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
is-reflexive {A = A} _≤_ = Ɐ x ∶ A , x ≤ x

is-transitive : {A : 𝓤 ̇} → (A → A → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
is-transitive {A = A} _≤_ =
 Ɐ x ∶ A , Ɐ y ∶ A , Ɐ z ∶ A , x ≤ y ⇒ y ≤ z ⇒ x ≤ z

is-preorder : {A : 𝓤 ̇} → (A → A → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
is-preorder {A = A} _≤_ = is-reflexive _≤_ ∧ is-transitive _≤_

\end{code}

Antisymmetry is not propositional unless A is a set. We will always
work with sets but the fact they are sets will be a corollary of their
equipment with an antisymmetric order so they are not sets a priori.

\begin{code}

is-antisymmetric : {A : 𝓤 ̇} → (A → A → Ω 𝓥) → (𝓤 ⊔ 𝓥) ̇
is-antisymmetric {A = A} _≤_ = {x y : A} → (x ≤ y) holds → (y ≤ x) holds → x ≡ y

being-antisymmetric-is-prop : {A : 𝓤 ̇} (_≤_ : A → A → Ω 𝓥)
                            → is-set A
                            → is-prop (is-antisymmetric _≤_)
being-antisymmetric-is-prop {𝓤} {A} _≤_ A-is-set =
 Π-is-prop' fe (λ x → Π-is-prop' fe (λ y → Π₂-is-prop fe (λ _ _ → A-is-set {x} {y})))

is-partial-order : (A : 𝓤 ̇) → (A → A → Ω 𝓥) → 𝓤 ⊔ 𝓥 ̇
is-partial-order A _≤_ = is-preorder _≤_ holds ×  is-antisymmetric _≤_

being-partial-order-is-prop : (A : 𝓤 ̇) (_≤_ : A → A → Ω 𝓥)
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

syntax rel-syntax P x y = x ≤[ P ] y

poset-eq-syntax : (P : Poset 𝓤 𝓥) → ∣ P ∣ₚ → ∣ P ∣ₚ → Ω 𝓥
poset-eq-syntax P x y = x ≤[ P ] y ∧ y ≤[ P ] x

syntax poset-eq-syntax P x y = x ≣[ P ] y

≤-is-reflexive : (P : Poset 𝓤 𝓥)
               → is-reflexive (λ x y → x ≤[ P ] x) holds
≤-is-reflexive (_ , _ , ((r , _) , _)) = r

reflexivity+ : (P : Poset 𝓤 𝓥)
             → {x y : pr₁ P} → x ≡ y → (x ≤[ P ] y) holds
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

 _≡⟨_⟩ₚ_ : (x : ∣ P ∣ₚ) {y z : ∣ P ∣ₚ}
         → x ≡ y → (y ≤ z) holds → (x ≤ z) holds
 x ≡⟨ p ⟩ₚ q = transport (λ - → (- ≤ _) holds) (p ⁻¹) q

 _■ : (x : ∣ P ∣ₚ) → (x ≤ x) holds
 _■ = ≤-is-reflexive P

 infixr 0 _≤⟨_⟩_
 infixr 0 _≡⟨_⟩ₚ_
 infix  1 _■

infix 1 _≡[_]≡_

_≡[_]≡_ : {A : 𝓤 ̇} → A → is-set A → A → Ω 𝓤
x ≡[ iss ]≡ y = (x ≡ y) , iss

\end{code}

\section{Meets}

\begin{code}

module Meets {A : 𝓤 ̇} (_≤_ : A → A → Ω 𝓥) where

 is-top : A → Ω (𝓤 ⊔ 𝓥)
 is-top t = Ɐ x ∶ A , (x ≤ t)

 _is-a-lower-bound-of_ : A → A × A → Ω 𝓥
 l is-a-lower-bound-of (x , y) = (l ≤ x) ∧ (l ≤ y)

 lower-bound : A × A → 𝓤 ⊔ 𝓥 ̇
 lower-bound (x , y) =
   Σ l ꞉ A , (l is-a-lower-bound-of (x , y)) holds

 _is-glb-of_ : A → A × A → Ω (𝓤 ⊔ 𝓥)
 l is-glb-of (x , y) = l is-a-lower-bound-of (x , y)
                     ∧ (Ɐ (l′ , _) ∶ lower-bound (x , y) , (l′ ≤ l))

\end{code}

\section{Joins}

\begin{code}

module Joins {A : 𝓤 ̇} (_≤_ : A → A → Ω 𝓥) where

 _is-an-upper-bound-of_ : A → Fam 𝓦 A → Ω (𝓥 ⊔ 𝓦)
 u is-an-upper-bound-of U = Ɐ i ∶ index U , (U [ i ]) ≤ u

 upper-bound : Fam 𝓦 A → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 upper-bound U = Σ u ꞉ A , (u is-an-upper-bound-of U) holds

 _is-lub-of_ : A → Fam 𝓦 A → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
 u is-lub-of U = (u is-an-upper-bound-of U)
               ∧ (Ɐ (u′ , _) ∶ upper-bound U , (u ≤ u′))

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

satisfies-frame-laws : {A : 𝓤 ̇} → frame-data 𝓥 𝓦 A → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
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
    γ = Ɐ (x , y) ∶ (A × A) , ((x ⊓ y) is-glb-of (x , y))
    δ = Ɐ U ∶ Fam 𝓦 A , (⊔ U) is-lub-of U
    ε = Ɐ (x , U) ∶ A × Fam 𝓦 A ,
        (x ⊓ (⋁⟨ i ⟩ U [ i ]) ≡[ iss ]≡ ⋁⟨ i ⟩ x ⊓ (U [ i ]))

frame-structure : (𝓥 𝓦 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
frame-structure 𝓥 𝓦 A =
  Σ d ꞉ (frame-data 𝓥 𝓦 A) , satisfies-frame-laws d

\end{code}

The type of (𝓤, 𝓥, 𝓦)-frames is then defined as:

\begin{code}

Frame : (𝓤 𝓥 𝓦 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
Frame 𝓤 𝓥 𝓦 = Σ A ꞉ (𝓤 ̇) , frame-structure 𝓥 𝓦 A

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
is-top F t = Ɐ x ∶ ⟨ F ⟩ , x ≤[ poset-of F ] t

𝟏-is-top : (F : Frame 𝓤 𝓥 𝓦) → (is-top F 𝟏[ F ]) holds
𝟏-is-top (A , _ , _ , p , _) = p

𝟏-is-unique : (F : Frame 𝓤 𝓥 𝓦) → (t : ⟨ F ⟩) → is-top F t holds → t ≡ 𝟏[ F ]
𝟏-is-unique F t t-top = ≤-is-antisymmetric (poset-of F) β γ
 where
  β : (t ≤[ poset-of F ] 𝟏[ F ]) holds
  β = 𝟏-is-top F t

  γ : (𝟏[ F ] ≤[ poset-of F ] t) holds
  γ = t-top 𝟏[ F ]

only-𝟏-is-above-𝟏 : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩)
                  → (𝟏[ F ] ≤[ poset-of F ] x) holds → x ≡ 𝟏[ F ]
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
                  → (x : ⟨ F ⟩) → x ∧[ F ] 𝟏[ F ] ≡ x
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
                   ≡ binary-family 𝓦 (f x) (f y)
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
                    → (x ∨[ F ] y) ≡ (y ∨[ F ] x)
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
           → (x ∨[ F ] y) ∨[ F ] z ≡ x ∨[ F ] (y ∨[ F ] z)
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
 z ∨[ F ] x  ≡⟨ ∨[ F ]-is-commutative z x ⟩ₚ
 x ∨[ F ] z  ≤⟨ ∨[ F ]-left-monotone p    ⟩
 y ∨[ F ] z  ≡⟨ ∨[ F ]-is-commutative y z ⟩ₚ
 z ∨[ F ] y  ■
  where
   open PosetReasoning (poset-of F)

\end{code}

\begin{code}

𝟎[_] : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩
𝟎[ F ] = ⋁[ F ] 𝟘 , λ ()

𝟎-is-bottom : (F : Frame 𝓤 𝓥 𝓦)
            → (x : ⟨ F ⟩) → (𝟎[ F ] ≤[ poset-of F ] x) holds
𝟎-is-bottom F x = ⋁[ F ]-least (𝟘 , λ ()) (x , λ ())

only-𝟎-is-below-𝟎 : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩)
                  → (x ≤[ poset-of F ] 𝟎[ F ]) holds → x ≡ 𝟎[ F ]
only-𝟎-is-below-𝟎 F x p =
 ≤-is-antisymmetric (poset-of F) p (𝟎-is-bottom F x)

𝟎-is-unique : (F : Frame 𝓤 𝓥 𝓦) (b : ⟨ F ⟩)
            → ((x : ⟨ F ⟩) → (b ≤[ poset-of F ] x) holds) → b ≡ 𝟎[ F ]
𝟎-is-unique F b φ = only-𝟎-is-below-𝟎 F b (φ 𝟎[ F ])

𝟎-right-unit-of-∨ : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩) → 𝟎[ F ] ∨[ F ] x ≡ x
𝟎-right-unit-of-∨ {𝓦 = 𝓦} F x = ≤-is-antisymmetric (poset-of F) β γ
 where
  open PosetNotation (poset-of F)

  β : ((𝟎[ F ] ∨[ F ] x) ≤ x) holds
  β = ∨[ F ]-least (𝟎-is-bottom F x) (≤-is-reflexive (poset-of F) x)

  γ : (x ≤ (𝟎[ F ] ∨[ F ] x)) holds
  γ = ⋁[ F ]-upper (binary-family 𝓦 𝟎[ F ] x) (inr ⋆)

𝟎-left-unit-of-∨ : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩) → x ∨[ F ] 𝟎[ F ] ≡ x
𝟎-left-unit-of-∨ {𝓦 = 𝓦} F x =
 x ∨[ F ] 𝟎[ F ]  ≡⟨ ∨[ F ]-is-commutative x 𝟎[ F ] ⟩
 𝟎[ F ] ∨[ F ] x  ≡⟨ 𝟎-right-unit-of-∨ F x          ⟩
 x                ∎

\end{code}

\begin{code}

distributivity : (F : Frame 𝓤 𝓥 𝓦)
               → (x : ⟨ F ⟩)
               → (U : Fam 𝓦 ⟨ F ⟩)
               → let open JoinNotation (λ - → ⋁[ F ] -) in
                 x ∧[ F ] (⋁⟨ i ⟩ (U [ i ]))
               ≡ ⋁⟨ i ⟩ (x ∧[ F ] (U [ i ]))
distributivity (_ , _ , _ , (_ , _ , _ , d)) x U = d (x , U)

\end{code}

\section{Scott-continuity}

\begin{code}

is-directed : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓥 ⊔ 𝓦)
is-directed F (I , β) =
   ∥ I ∥Ω
 ∧ (Ɐ i ∶ I , Ɐ j ∶ I , (Ǝ k ∶ I , ((β i ≤ β k) ∧ (β j ≤ β k)) holds))
  where open PosetNotation (poset-of F)

is-scott-continuous : (F : Frame 𝓤  𝓥  𝓦)
                    → (G : Frame 𝓤′ 𝓥′ 𝓦)
                    → (f : ⟨ F ⟩ → ⟨ G ⟩)
                    → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ⊔ 𝓤′ ⊔ 𝓥′)
is-scott-continuous {𝓦 = 𝓦} F G f =
 Ɐ S ∶ Fam 𝓦 ⟨ F ⟩ , is-directed F S ⇒ f (⋁[ F ] S) is-lub-of ⁅ f s ∣ s ε S ⁆
  where
   open Joins (λ x y → x ≤[ poset-of G ] y) using (_is-lub-of_)

id-is-scott-continuous : (F : Frame 𝓤 𝓥 𝓦) → is-scott-continuous F F id holds
id-is-scott-continuous F S δ = ⋁[ F ]-upper S , ⋁[ F ]-least S
 where
  open Joins (λ x y → x ≤[ poset-of F ] y)

\end{code}

\section{Frame homomorphisms}

\begin{code}

preserves-binary-meets : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤′ 𝓥′ 𝓦)
                → (⟨ F ⟩ → ⟨ G ⟩) → Ω (𝓤 ⊔ 𝓤′)
preserves-binary-meets F G h =
 Ɐ x ∶ ⟨ F ⟩ , Ɐ y ∶ ⟨ F ⟩ , (h (x ∧[ F ] y) ≡[ ψ ]≡ h x ∧[ G ] h y)
  where
   ψ : is-set ⟨ G ⟩
   ψ = carrier-of-[ poset-of G ]-is-set

is-a-frame-homomorphism : (F : Frame 𝓤  𝓥  𝓦)
                          (G : Frame 𝓤′ 𝓥′ 𝓦)
                        → (⟨ F ⟩ → ⟨ G ⟩)
                        → Ω (𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓤′ ⊔ 𝓥′)
is-a-frame-homomorphism {𝓦 = 𝓦} F G f = α ∧ β ∧ γ
 where
  P = poset-of G

  iss : is-set ⟨ G ⟩
  iss = carrier-of-[ P ]-is-set

  open Joins (λ x y → x ≤[ P ] y)

  α = f 𝟏[ F ] ≡[ iss ]≡ 𝟏[ G ]
  β = preserves-binary-meets F G f
  γ = Ɐ U ∶ Fam 𝓦 ⟨ F ⟩ , f (⋁[ F ] U) is-lub-of ⁅ f x ∣ x ε U ⁆

_─f→_ : Frame 𝓤 𝓥 𝓦 → Frame 𝓤′ 𝓥′ 𝓦 → 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓤′ ⊔ 𝓥′ ̇
F ─f→ G =
 Σ f ꞉ (⟨ F ⟩ → ⟨ G ⟩) , is-a-frame-homomorphism F G f holds

is-monotonic : (P : Poset 𝓤 𝓥) (Q : Poset 𝓤′ 𝓥′)
             → (pr₁ P → pr₁ Q) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓥′)
is-monotonic P Q f =
 Ɐ (x , y) ∶ (pr₁ P × pr₁ P) , ((x ≤[ P ] y) ⇒ f x ≤[ Q ] f y)

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

  γ : (Ɐ i ∶ I , Ɐ j ∶ I ,
        (Ǝ k ∶ I ,
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
 Ɐ S ∶ Fam 𝓦 ⟨ F ⟩ , f (⋁[ F ] S) ≡[ iss ]≡ ⋁[ G ] ⁅ f s ∣ s ε S ⁆
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
              (z is-glb-of (x , y)) holds → z ≡ (x ∧[ F ] y)
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
           (u is-lub-of U) holds → u ≡ ⋁[ F ] U
⋁[_]-unique F U u (p , q) = ≤-is-antisymmetric (poset-of F) γ β
 where
  open PosetNotation (poset-of F)

  γ : (u ≤ (⋁[ F ] U)) holds
  γ = q ((⋁[ F ] U) , ⋁[ F ]-upper U)

  β : ((⋁[ F ] U) ≤ u) holds
  β = ⋁[ F ]-least U (u , p)

connecting-lemma₁ : (F : Frame 𝓤 𝓥 𝓦) {x y : ⟨ F ⟩}
                  → (x ≤[ poset-of F ] y) holds
                  → x ≡ x ∧[ F ] y
connecting-lemma₁ F {x} {y} p = ∧[ F ]-unique (β , γ)
 where
  open Meets (λ x y → x ≤[ poset-of F ] y)

  β : (x is-a-lower-bound-of (x , y)) holds
  β = ≤-is-reflexive (poset-of F) x , p

  γ : (Ɐ (z , _) ∶ lower-bound (x , y) , z ≤[ poset-of F ] x) holds
  γ (z , q , _) = q

connecting-lemma₂ : (F : Frame 𝓤 𝓥 𝓦) {x y : ⟨ F ⟩}
                  → x ≡ x ∧[ F ] y
                  → (x ≤[ poset-of F ] y) holds
connecting-lemma₂ F {x} {y} p = x ≡⟨ p ⟩ₚ x ∧[ F ] y ≤⟨ ∧[ F ]-lower₂ x y ⟩ y ■
 where
  open PosetReasoning (poset-of F)

connecting-lemma₃ : (F : Frame 𝓤 𝓥 𝓦) {x y : ⟨ F ⟩}
                  → y ≡ x ∨[ F ] y
                  → (x ≤[ poset-of F ] y) holds
connecting-lemma₃ F {x} {y} p =
 x ≤⟨ ∨[ F ]-upper₁ x y ⟩ x ∨[ F ] y ≡⟨ p ⁻¹ ⟩ₚ y ■
  where
   open PosetReasoning (poset-of F)

connecting-lemma₄ : (F : Frame 𝓤 𝓥 𝓦) {x y : ⟨ F ⟩}
                  → (x ≤[ poset-of F ] y) holds
                  → y ≡ x ∨[ F ] y
connecting-lemma₄ F {x} {y} p = ≤-is-antisymmetric (poset-of F) β γ
 where
  β : (y ≤[ poset-of F ] (x ∨[ F ] y)) holds
  β = ∨[ F ]-upper₂ x y

  γ : ((x ∨[ F ] y) ≤[ poset-of F ] y) holds
  γ = ∨[ F ]-least p (≤-is-reflexive (poset-of F) y)

frame-morphisms-are-monotonic : (F : Frame 𝓤  𝓥  𝓦)
                                (G : Frame 𝓤′ 𝓥′ 𝓦)
                              → (f : ⟨ F ⟩ → ⟨ G ⟩)
                              → is-a-frame-homomorphism F G f holds
                              → is-monotonic (poset-of F) (poset-of G) f holds
frame-morphisms-are-monotonic F G f (_ , ψ , _) (x , y) p =
 f x            ≤⟨ i                         ⟩
 f (x ∧[ F ] y) ≤⟨ ii                        ⟩
 f x ∧[ G ] f y ≤⟨ ∧[ G ]-lower₂ (f x) (f y) ⟩
 f y            ■
  where
   open PosetReasoning (poset-of G)

   i  = reflexivity+ (poset-of G) (ap f (connecting-lemma₁ F p))
   ii = reflexivity+ (poset-of G) (ψ x y)

scott-continuous-implies-monotone : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤′ 𝓥′ 𝓦)
                                  → (f : ⟨ F ⟩ → ⟨ G ⟩)
                                  → is-scott-continuous F G f holds
                                  → is-monotonic (poset-of F) (poset-of G) f holds
scott-continuous-implies-monotone {𝓦 = 𝓦} F G f φ (x , y) p =
 f x                                       ≤⟨ i   ⟩
 f x ∨[ G ] f y                            ≡⟨ ii  ⟩ₚ
 ⋁[ G ] ⁅ f z ∣ z ε binary-family 𝓦 x y ⁆  ≡⟨ iii ⟩ₚ
 f (x ∨[ F ] y)                            ≡⟨ iv  ⟩ₚ
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


meet-preserving-implies-monotone : (F : Frame 𝓤 𝓥 𝓦) (G : Frame 𝓤′ 𝓥′ 𝓦)
                                 → (h : ⟨ F ⟩ → ⟨ G ⟩)
                                 → preserves-binary-meets F G h holds
                                 → is-monotonic (poset-of F) (poset-of G) h holds
meet-preserving-implies-monotone F G h μ (x , y) p =
 h x              ≡⟨ i   ⟩ₚ
 h (x ∧[ F ] y)   ≡⟨ ii  ⟩ₚ
 h x ∧[ G ] h y   ≤⟨ iii ⟩
 h y              ■
  where
   open PosetReasoning (poset-of G)

   i   = ap h (connecting-lemma₁ F p)
   ii  = μ x y
   iii = ∧[ G ]-lower₂ (h x) (h y)

scott-continuous-join-eq : (F : Frame 𝓤  𝓥  𝓦)
                         → (G : Frame 𝓤′ 𝓥′ 𝓦)
                         → (f : ⟨ F ⟩ → ⟨ G ⟩)
                         → is-scott-continuous F G f holds
                         → (S : Fam 𝓦 ⟨ F ⟩)
                         → is-directed F S holds
                         → f (⋁[ F ] S) ≡ ⋁[ G ] ⁅ f s ∣ s ε S ⁆
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
         g (⋁[ G ] ⁅ f s ∣ s ε S ⁆)   ≡⟨ iii ⟩ₚ
         g (f (⋁[ F ] S))             ■
          where
           i   = ⋁[ H ]-upper ⁅ g (f s) ∣ s ε S ⁆ k
           ii  = ⋁[ H ]-least
                  ⁅ g (f s) ∣ s ε S ⁆
                  (g (⋁[ G ] ⁅ f s ∣ s ε S ⁆) , pr₁ (ζg ⁅ f s ∣ s ε S ⁆ †))
           iii = ap g (scott-continuous-join-eq F G f ζf S δ ⁻¹)

   γ : (Ɐ (u , _) ∶ upper-bound ⁅ g (f s) ∣ s ε S ⁆ ,
         (g (f (⋁[ F ] S)) ≤[ poset-of H ] u)) holds
   γ (u , p) = g (f (⋁[ F ] S))              ≤⟨ i   ⟩
               g (⋁[ G ] ⁅ f s ∣ s ε S ⁆)    ≡⟨ ii  ⟩ₚ
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
                 → x ∧[ F ] y ≡ y ∧[ F ] x
∧[ F ]-is-commutative x y = ∧[ F ]-unique (β , γ)
 where
  open Meets (λ x y → x ≤[ poset-of F ] y)
  open PosetNotation (poset-of F) using (_≤_)

  β : ((x ∧[ F ] y) is-a-lower-bound-of (y , x)) holds
  β = (∧[ F ]-lower₂ x y) , (∧[ F ]-lower₁ x y)

  γ : (Ɐ (l , _) ∶ lower-bound (y , x) , l ≤ (x ∧[ F ] y)) holds
  γ (l , p , q) = ∧[ F ]-greatest x y l q p

∧[_]-is-associative : (F : Frame 𝓤 𝓥 𝓦) (x y z : ⟨ F ⟩)
                    → x ∧[ F ] (y ∧[ F ] z) ≡ (x ∧[ F ] y) ∧[ F ] z
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
 z ∧[ F ] x  ≡⟨ ∧[ F ]-is-commutative z x ⟩ₚ
 x ∧[ F ] z  ≤⟨ ∧[ F ]-left-monotone p    ⟩
 y ∧[ F ] z  ≡⟨ ∧[ F ]-is-commutative y z ⟩ₚ
 z ∧[ F ] y  ■
  where
   open PosetReasoning (poset-of F)

\end{code}

\begin{code}

𝟎-right-annihilator-for-∧ : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩)
                          → x ∧[ F ] 𝟎[ F ] ≡ 𝟎[ F ]
𝟎-right-annihilator-for-∧ F x =
 only-𝟎-is-below-𝟎 F (x ∧[ F ] 𝟎[ F ]) (∧[ F ]-lower₂ x 𝟎[ F ])

𝟎-left-annihilator-for-∧ : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩)
                         → 𝟎[ F ] ∧[ F ] x ≡ 𝟎[ F ]
𝟎-left-annihilator-for-∧ F x =
 𝟎[ F ] ∧[ F ] x  ≡⟨ ∧[ F ]-is-commutative 𝟎[ F ] x ⟩
 x ∧[ F ] 𝟎[ F ]  ≡⟨ 𝟎-right-annihilator-for-∧ F x  ⟩
 𝟎[ F ]           ∎

𝟏-right-annihilator-for-∨ : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩)
                          → x ∨[ F ] 𝟏[ F ] ≡ 𝟏[ F ]
𝟏-right-annihilator-for-∨ F x =
 only-𝟏-is-above-𝟏 F (x ∨[ F ] 𝟏[ F ]) (∨[ F ]-upper₂ x 𝟏[ F ])

𝟏-left-annihilator-for-∨ : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩)
                         → 𝟏[ F ] ∨[ F ] x ≡ 𝟏[ F ]
𝟏-left-annihilator-for-∨ F x =
 𝟏[ F ] ∨[ F ] x  ≡⟨ ∨[ F ]-is-commutative 𝟏[ F ] x ⟩
 x ∨[ F ] 𝟏[ F ]  ≡⟨ 𝟏-right-annihilator-for-∨ F x  ⟩
 𝟏[ F ] ∎

\end{code}

\begin{code}

distributivity′ : (F : Frame 𝓤 𝓥 𝓦)
                → (x : ⟨ F ⟩)
                → (S : Fam 𝓦 ⟨ F ⟩)
                → let open JoinNotation (λ - → ⋁[ F ] -) in
                  x ∧[ F ] (⋁⟨ i ⟩ (S [ i ]))
                ≡ ⋁⟨ i ⟩ ((S [ i ]) ∧[ F ] x)
distributivity′ F x S =
 x ∧[ F ] (⋁⟨ i ⟩ S [ i ])    ≡⟨ distributivity F x S ⟩
 ⋁⟨ i ⟩ (x ∧[ F ] (S [ i ]))  ≡⟨ †                    ⟩
 ⋁⟨ i ⟩ (S [ i ]) ∧[ F ] x    ∎
  where
   open PosetReasoning (poset-of F)
   open JoinNotation (λ - → ⋁[ F ] -)

   ‡ = ∧[ F ]-is-commutative x ∘ (_[_] S)
   † = ap (λ - → join-of F (index S , -)) (dfunext fe ‡)

absorption-right : (F : Frame 𝓤 𝓥 𝓦) (x y : ⟨ F ⟩)
                 → x ∨[ F ] (x ∧[ F ] y) ≡ x
absorption-right F x y = ≤-is-antisymmetric (poset-of F) β γ
 where
  β : ((x ∨[ F ] (x ∧[ F ] y)) ≤[ poset-of F ] x) holds
  β = ∨[ F ]-least (≤-is-reflexive (poset-of F) x) (∧[ F ]-lower₁ x y)

  γ : (x ≤[ poset-of F ] (x ∨[ F ] (x ∧[ F ] y))) holds
  γ = ∨[ F ]-upper₁ x (x ∧[ F ] y)

absorption-left : (F : Frame 𝓤 𝓥 𝓦) (x y : ⟨ F ⟩)
                → x ∨[ F ] (y ∧[ F ] x) ≡ x
absorption-left F x y =
 x ∨[ F ] (y ∧[ F ] x) ≡⟨ ap (λ - → x ∨[ F ] -) (∧[ F ]-is-commutative y x) ⟩
 x ∨[ F ] (x ∧[ F ] y) ≡⟨ absorption-right F x y                            ⟩
 x                     ∎

absorptionᵒᵖ-right : (F : Frame 𝓤 𝓥 𝓦) → (x y : ⟨ F ⟩) → x ∧[ F ] (x ∨[ F ] y) ≡ x
absorptionᵒᵖ-right F x y = ≤-is-antisymmetric (poset-of F) β γ
 where
  β : ((x ∧[ F ] (x ∨[ F ] y)) ≤[ poset-of F ] x) holds
  β = ∧[ F ]-lower₁ x (x ∨[ F ] y)

  γ : (x ≤[ poset-of F ] (x ∧[ F ] (x ∨[ F ] y))) holds
  γ = ∧[ F ]-greatest x (x ∨[ F ] y) x
       (≤-is-reflexive (poset-of F) x)
       (∨[ F ]-upper₁ x y)

absorptionᵒᵖ-left : (F : Frame 𝓤 𝓥 𝓦) (x y : ⟨ F ⟩)
                  → x ∧[ F ] (y ∨[ F ] x) ≡ x
absorptionᵒᵖ-left F x y =
 x ∧[ F ] (y ∨[ F ] x)  ≡⟨ ap (λ - → x ∧[ F ] -) (∨[ F ]-is-commutative y x) ⟩
 x ∧[ F ] (x ∨[ F ] y)  ≡⟨ absorptionᵒᵖ-right F x y                          ⟩
 x                      ∎

binary-distributivity : (F : Frame 𝓤 𝓥 𝓦)
                      → (x y z : ⟨ F ⟩)
                      → x ∧[ F ] (y ∨[ F ] z) ≡ (x ∧[ F ] y) ∨[ F ] (x ∧[ F ] z)
binary-distributivity {𝓦 = 𝓦} F x y z =
 x ∧[ F ] (y ∨[ F ] z)                            ≡⟨ † ⟩
 ⋁[ F ] ⁅ x ∧[ F ] w ∣ w ε binary-family 𝓦 y z ⁆  ≡⟨ ‡ ⟩
 (x ∧[ F ] y) ∨[ F ] (x ∧[ F ] z)                 ∎
  where
   † = distributivity F x (binary-family 𝓦 y z)
   ‡ = ap (λ - → join-of F -) (fmap-binary-family 𝓦 (λ - → x ∧[ F ] -) y z)

binary-distributivity-op : (F : Frame 𝓤 𝓥 𝓦) (x y z : ⟨ F ⟩)
                         → x ∨[ F ] (y ∧[ F ] z) ≡ (x ∨[ F ] y) ∧[ F ] (x ∨[ F ] z)
binary-distributivity-op F x y z =
 x ∨[ F ] (y ∧[ F ] z)                                   ≡⟨ †    ⟩
 x ∨[ F ] ((z ∧[ F ] x) ∨[ F ] (z ∧[ F ] y))             ≡⟨ I    ⟩
 x ∨[ F ] (z ∧[ F ] (x ∨[ F ] y))                        ≡⟨ II   ⟩
 x ∨[ F ] ((x ∨[ F ] y) ∧[ F ] z)                        ≡⟨ III  ⟩
 (x ∧[ F ] (x ∨[ F ] y)) ∨[ F ] ((x ∨[ F ] y) ∧[ F ] z)  ≡⟨ IV   ⟩
 ((x ∨[ F ] y) ∧[ F ] x) ∨[ F ] ((x ∨[ F ] y) ∧[ F ] z)  ≡⟨ V    ⟩
 (x ∨[ F ] y) ∧[ F ] (x ∨[ F ] z)                        ∎
  where
   w   = (x ∨[ F ] y) ∧[ F ] z

   I   = ap (λ - → x ∨[ F ] -) ((binary-distributivity F z x y) ⁻¹)
   II  = ap (λ - → x ∨[ F ] -) (∧[ F ]-is-commutative z (x ∨[ F ] y))
   III = ap (λ - → - ∨[ F ] w) (absorptionᵒᵖ-right F x y) ⁻¹
   IV  = ap (λ - → - ∨[ F ] w) (∧[ F ]-is-commutative x (x ∨[ F ] y))
   V   = (binary-distributivity F (x ∨[ F ] y) x z) ⁻¹

   † : x ∨[ F ] (y ∧[ F ] z) ≡ x ∨[ F ] ((z ∧[ F ] x) ∨[ F ] (z ∧[ F ] y))
   † = x ∨[ F ] (y ∧[ F ] z)                        ≡⟨ i    ⟩
       (x ∨[ F ] (z ∧[ F ] x)) ∨[ F ] (y ∧[ F ] z)  ≡⟨ ii   ⟩
       (x ∨[ F ] (z ∧[ F ] x)) ∨[ F ] (z ∧[ F ] y)  ≡⟨ iii  ⟩
       x ∨[ F ] ((z ∧[ F ] x) ∨[ F ] (z ∧[ F ] y))  ∎
        where
         i   = ap (λ - → - ∨[ F ] (y ∧[ F ] z)) (absorption-left F x z) ⁻¹
         ii  = ap (λ - → (x ∨[ F ] (z ∧[ F ] x)) ∨[ F ] -) (∧[ F ]-is-commutative y z)
         iii = ∨[ F ]-assoc x (z ∧[ F ] x) (z ∧[ F ] y)

\end{code}

\begin{code}

⋁[_]-iterated-join : (F : Frame 𝓤 𝓥 𝓦) (I : 𝓦 ̇) (J : I → 𝓦 ̇)
                → (f : (i : I) → J i → ⟨ F ⟩)
                → ⋁[ F ] ((Σ i ꞉ I , J i) , uncurry f)
                ≡ ⋁[ F ] ⁅ ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ∣ i ∶ I ⁆
⋁[ F ]-iterated-join I J f = ⋁[ F ]-unique _ _ (β , γ)
 where
  open Joins (λ x y → x ≤[ poset-of F ] y)
  open PosetReasoning (poset-of F) renaming (_■ to _QED)

  β : ((⋁[ F ] (Σ J , uncurry f))
      is-an-upper-bound-of
      ⁅ ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ∣ i ∶ I ⁆) holds
  β i = ⋁[ F ]-least _ (_ , λ jᵢ → ⋁[ F ]-upper _ (i , jᵢ))

  γ : (Ɐ (u , _) ∶ upper-bound ⁅ ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ∣ i ∶ I ⁆ ,
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
                   → (x : ⟨ F ⟩) → x ≡ x ∧[ F ] x
∧[ F ]-is-idempotent x = ≤-is-antisymmetric (poset-of F) β γ
 where
  α : (x ≤[ poset-of F ] x) holds
  α = ≤-is-reflexive (poset-of F) x

  β : (x ≤[ poset-of F ] (x ∧[ F ] x)) holds
  β = ∧[ F ]-greatest x x x α α

  γ : ((x ∧[ F ] x) ≤[ poset-of F ] x) holds
  γ = ∧[ F ]-lower₁ x x

\end{code}

\begin{code}

distributivity+ : (F : Frame 𝓤 𝓥 𝓦)
                → let open JoinNotation (λ - → ⋁[ F ] -) in
                  (U@(I , _) V@(J , _) : Fam 𝓦 ⟨ F ⟩)
                → (⋁⟨ i ⟩ (U [ i ])) ∧[ F ] (⋁⟨ j ⟩ (V [ j ]))
                ≡ (⋁⟨ (i , j) ∶ (I × J)  ⟩ ((U [ i ]) ∧[ F ] (V [ j ])))
distributivity+ F U@(I , _) V@(J , _) =
 (⋁⟨ i ⟩ (U [ i ])) ∧[ F ] (⋁⟨ j ⟩ (V [ j ]))     ≡⟨ i   ⟩
 (⋁⟨ j ⟩ (V [ j ])) ∧[ F ] (⋁⟨ i ⟩ (U [ i ]))     ≡⟨ ii  ⟩
 (⋁⟨ i ⟩ (⋁⟨ j ⟩ (V [ j ])) ∧[ F ] (U [ i ]))     ≡⟨ iii ⟩
 (⋁⟨ i ⟩ (U [ i ] ∧[ F ] (⋁⟨ j ⟩ (V [ j ]))))     ≡⟨ iv  ⟩
 (⋁⟨ i ⟩ (⋁⟨ j ⟩ (U [ i ] ∧[ F ] V [ j ])))       ≡⟨ v   ⟩
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
 (x : ⟨ F ⟩) → Σ J ꞉ (Fam 𝓦 I) , (x is-lub-of ⁅ β j ∣ j ε J ⁆) holds
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
                         x ≡ ⋁[ F ] ⁅ ℬ [ i ] ∣ i ε ℐ ⁆
covers F ℬ b x = ⋁[ F ]-unique ⁅ ℬ [ i ] ∣ i ε ℐ ⁆ x (pr₂ (b x))
 where
  ℐ = covering-index-family F ℬ b x

\end{code}

We also have the notion of a directed basis, in which every covering
family is directed.

\begin{code}

has-directed-basis₀ : (F : Frame 𝓤 𝓥 𝓦) → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) ̇ 
has-directed-basis₀ {𝓦 = 𝓦} F =
 Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ ,
  Σ b ꞉ is-basis-for F ℬ ,
   Π x ꞉ ⟨ F ⟩ , is-directed F (⁅ ℬ [ i ] ∣ i ε pr₁ (b x) ⁆) holds

has-directed-basis : (F : Frame 𝓤 𝓥 𝓦) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
has-directed-basis {𝓦 = 𝓦} F = ∥ has-directed-basis₀ F ∥Ω

\end{code}

The main development in this section is that every small basis can be
extended to a directed one whilst keeping it small.

\begin{code}

directify : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Fam 𝓦 ⟨ F ⟩
directify F (I , α) = List I , (foldr (λ i - → α i ∨[ F ] -) 𝟎[ F ])
 where open PosetNotation (poset-of F)

\end{code}

Note that `directify` is a monoid homomorphism from the free monoid on I
to (_∨_, 𝟎).

\begin{code}

directify-functorial : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ⟨ F ⟩)
                     → (is js : List (index S))
                     → directify F S [ is ++ js ]
                     ≡ directify F S [ is ] ∨[ F ] directify F S [ js ]
directify-functorial F S@(I , α) = γ
 where
  γ : (is js : List I)
    → directify F S [ is ++ js ]
    ≡ directify F S [ is ] ∨[ F ] directify F S [ js ]
  γ []       js = directify F S [ [] ++ js ]          ≡⟨ refl ⟩
                  directify F S [ js ]                ≡⟨ †    ⟩
                  𝟎[ F ]  ∨[ F ] directify F S [ js ] ∎
                   where
                    † = 𝟎-right-unit-of-∨ F (directify F S [ js ]) ⁻¹
  γ (i ∷ is) js =
   directify F S [ (i ∷ is) ++ js ]                              ≡⟨ refl ⟩
   α i ∨[ F ] directify F S [ is ++ js ]                         ≡⟨ †    ⟩
   α i ∨[ F ] (directify F S [ is ] ∨[ F ] directify F S [ js ]) ≡⟨ ‡    ⟩
   (α i ∨[ F ] directify F S [ is ]) ∨[ F ] directify F S [ js ] ≡⟨ refl ⟩
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

  υ : (Ɐ is ∶ List I
     , Ɐ js ∶ List I
     , (Ǝ ks ∶ List I
      , (((directify F S [ is ] ≤ directify F S [ ks ])
        ∧ (directify F S [ js ] ≤ directify F S [ ks ])) holds))) holds
  υ is js = ∣ (is ++ js) , β , γ ∣
    where
     open PosetReasoning (poset-of F)

     ‡ = directify-functorial F S is js ⁻¹

     β : (directify F S [ is ] ≤ directify F S [ is ++ js ]) holds
     β = directify F S [ is ]                             ≤⟨ † ⟩
         directify F S [ is ] ∨[ F ] directify F S [ js ] ≡⟨ ‡ ⟩ₚ
         directify F S [ is ++ js ]                       ■
          where
           † = ∨[ F ]-upper₁ (directify F S [ is ]) (directify F S [ js ])

     γ : (directify F S [ js ] ≤ directify F S [ is ++ js ]) holds
     γ = directify F S [ js ]                             ≤⟨ † ⟩
         directify F S [ is ] ∨[ F ] directify F S [ js ] ≡⟨ ‡ ⟩ₚ
         directify F S [ is ++ js ] ■
          where
           † = ∨[ F ]-upper₂ (directify F S [ is ]) (directify F S [ js ])

\end{code}

`directify` also preserves the join while doing what it is supposed to
do.

\begin{code}

directify-preserves-joins : (F : Frame 𝓤 𝓥 𝓦) (S : Fam 𝓦 ⟨ F ⟩)
                          → ⋁[ F ] S ≡ ⋁[ F ] directify F S
directify-preserves-joins F S = ≤-is-antisymmetric (poset-of F) β γ
 where
  open PosetNotation  (poset-of F)
  open PosetReasoning (poset-of F)

  β : ((⋁[ F ] S) ≤ (⋁[ F ] directify F S)) holds
  β = ⋁[ F ]-least S ((⋁[ F ] (directify F S)) , ν)
   where
    ν : (i : index S) → (S [ i ] ≤ (⋁[ F ] directify F S)) holds
    ν i =
     S [ i ]                   ≡⟨ 𝟎-right-unit-of-∨ F (S [ i ]) ⁻¹       ⟩ₚ
     𝟎[ F ] ∨[ F ] S [ i ]     ≡⟨ ∨[ F ]-is-commutative 𝟎[ F ] (S [ i ]) ⟩ₚ
     S [ i ] ∨[ F ] 𝟎[ F ]     ≡⟨ refl                                   ⟩ₚ
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

  q : x ≡ ⋁[ F ] directify F S
  q = x                    ≡⟨ ⋁[ F ]-unique S x p           ⟩
      ⋁[ F ] S             ≡⟨ directify-preserves-joins F S ⟩
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

  φ : (x : ⟨ F ⟩)
    → (is : List (index (𝒥 x)))
    → directify F ℬ [ (λ - → 𝒥 x [ - ]) <$> is ]
    ≡ directify F ⁅ ℬ [ j ] ∣ j ε 𝒥 x ⁆ [ is ]
  φ x []       = refl
  φ x (i ∷ is) = ap (λ - → (_ ∨[ F ] -)) (φ x is)

  ψ : (x : ⟨ F ⟩)
    → ⁅ directify F ℬ [ is ] ∣ is ε 𝒦 x ⁆ ≡ directify F ⁅ ℬ [ j ] ∣ j ε 𝒥 x ⁆
  ψ x = to-Σ-≡ (refl , dfunext fe (φ x))

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
                                            is-directed F (⁅ ℬ↑ [ i ] ∣ i ε 𝒥↑ ⁆) holds
covers-of-directified-basis-are-directed {𝓦 = 𝓦} F ℬ β x =
 transport (λ - → is-directed F - holds) (ψ ⁻¹) ε
  where
   𝒥 = pr₁ (β x)

   𝒦 : Fam 𝓦 (List (index ℬ))
   𝒦 = ⁅ (λ - → 𝒥 [ - ]) <$> is ∣ is ∶ List (index 𝒥) ⁆

   φ : (is : List (index 𝒥))
     → directify F ℬ [ (λ - → 𝒥 [ - ]) <$> is ]
     ≡ directify F ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ [ is ]
   φ []       = refl
   φ (i ∷ is) = ap (λ - → (_ ∨[ F ] -)) (φ is)

   ψ : ⁅ directify F ℬ [ is ] ∣ is ε 𝒦 ⁆ ≡ directify F ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆
   ψ = to-Σ-≡ (refl , dfunext fe φ)

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
      ≡ directify F ⁅ ℬ [ j ] ∣ j ε 𝒥 x ⁆ [ is ]
    φ x []       = refl
    φ x (i ∷ is) = ap (λ - → (_ ∨[ F ] -)) (φ x is)

    ψ : (x : ⟨ F ⟩)
      → ⁅ directify F ℬ [ is ] ∣ is ε 𝒦 x ⁆ ≡ directify F ⁅ ℬ [ j ] ∣ j ε 𝒥 x ⁆
    ψ x = to-Σ-≡ (refl , dfunext fe (φ x))

    δ : (x : ⟨ F ⟩)
      → is-directed F ⁅ directify F ℬ [ is ] ∣ is ε 𝒦 x ⁆ holds
    δ x = transport (λ - → is-directed F - holds) (ψ x ⁻¹) ε
     where
      ε = directify-is-directed F ⁅ ℬ [ j ] ∣ j ε 𝒥 x ⁆

\end{code}

\section{Locale notation}

A _locale_ is a type that has a frame of opens.

\begin{code}

record Locale (𝓤 𝓥 𝓦 : Universe) : 𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇  where
 field
  ⟨_⟩ₗ         : 𝓤 ̇
  frame-str-of : frame-structure 𝓥 𝓦 ⟨_⟩ₗ

 𝒪 : Frame 𝓤 𝓥 𝓦
 𝒪 = ⟨_⟩ₗ , frame-str-of


\end{code}

The type of continuous maps from locale `X` to locale `Y`:

\begin{code}

open Locale

_─c→_ : Locale 𝓤 𝓥 𝓦 → Locale 𝓤′ 𝓥′ 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ⊔ 𝓤′ ̇
X ─c→ Y = (𝒪 Y) ─f→ (𝒪 X)

\end{code}
