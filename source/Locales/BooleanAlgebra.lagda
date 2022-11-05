Ayberk Tosun, 8 March 2021.

Ported from `ayberkt/formal-topology-in-UF`.

 * Frames.
 * Frame homomorphisms.
 * Frame bases.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.PropTrunc
open import MLTT.List hiding ([_])

module Locales.BooleanAlgebra
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators
open import UF.Subsingletons-FunExt

open AllCombinators pt fe

open import Locales.Frame pt fe

open PropositionalTruncation pt

\end{code}

\section{Definition of a Boolean algebra}

\begin{code}

private
  variable
    𝓤′ 𝓥′ 𝓦′ 𝓤′′ 𝓥′′ : Universe

ba-data : {𝓤 : Universe} → (𝓥 : Universe) → 𝓤  ̇ → 𝓤 ⊔ 𝓥 ⁺  ̇
ba-data 𝓥 A = (A → A → Ω 𝓥 )  -- order
            × A               -- top element
            × (A → A → A)     -- binary meets
            × A               -- bottom element
            × (A → A → A)     -- binary joins
            × (A → A)         -- negation

\end{code}

\begin{code}

module Complementation {A : 𝓤  ̇} (iss : is-set A) (𝟎 𝟏 : A) (_⋏_ _⋎_ : A → A → A) where

 _complements_ : A → A → Ω 𝓤
 x′ complements x = (x ⋏ x′ ＝[ iss ]＝ 𝟎) ∧ (x ⋎ x′ ＝[ iss ]＝ 𝟏)

\end{code}

\begin{code}

satisfies-ba-laws : {A : 𝓤  ̇} → ba-data 𝓥 A → 𝓤 ⊔ 𝓥  ̇
satisfies-ba-laws {𝓤 = 𝓤} {𝓥 = 𝓥} {A = A} (_≤_ , 𝟏 , _⊓_ , 𝟎 , _⋎_ , ¬_) =
 Σ p ꞉ is-partial-order A _≤_ , rest p holds
  where
   open Meets (λ x y → x ≤ y)
   open Joins (λ x y → x ≤ y)

   rest : is-partial-order A _≤_ → Ω (𝓤 ⊔ 𝓥)
   rest p = β ∧ γ ∧ δ ∧ ϵ ∧ ζ
    where
     P : Poset 𝓤 𝓥
     P = A , _≤_ , p

     iss : is-set A
     iss = carrier-of-[ P ]-is-set

     open Complementation iss 𝟎 𝟏 _⊓_ _⋎_

     β : Ω (𝓤 ⊔ 𝓥)
     β = Ɐ x ∶ A , Ɐ y ∶ A , (x ⊓ y) is-glb-of (x , y)

     γ : Ω (𝓤 ⊔ 𝓥)
     γ = Ɐ x ∶ A , x ≤ 𝟏

     δ : Ω (𝓤 ⊔ 𝓥)
     δ = Ɐ x ∶ A , Ɐ y ∶ A , _is-lub-of₂_ (x ⋎ y) (x , y)

     ϵ : Ω (𝓤 ⊔ 𝓥)
     ϵ = Ɐ x ∶ A , 𝟎 ≤ x

     ζ : Ω (𝓤 ⊔ 𝓤)
     ζ = Ɐ x ∶ A , Ɐ y ∶ A , Ɐ z ∶ A , x ⊓ (y ⋎ z) ＝[ iss ]＝ (x ⊓ y) ⋎ (x ⊓ z)

     η : Ω (𝓤 ⊔ 𝓤)
     η = Ɐ x ∶ A , (¬ x) complements x

\end{code}

\begin{code}

ba-structure : (𝓥 : Universe) → 𝓤  ̇ → 𝓤 ⊔ 𝓥 ⁺  ̇
ba-structure 𝓥 A = Σ d ꞉ ba-data 𝓥 A , satisfies-ba-laws d

BooleanAlgebra : (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺  ̇
BooleanAlgebra 𝓤 𝓥 = Σ A ꞉ 𝓤  ̇ , ba-structure 𝓥 A

\end{code}

\begin{code}

⟪_⟫ : BooleanAlgebra 𝓤 𝓥 → 𝓤  ̇
⟪ A , _ ⟫ = A

poset-of-ba : BooleanAlgebra 𝓤 𝓥 → Poset 𝓤 𝓥
poset-of-ba (A , ((_≤_ , _) , (φ , _))) = A , _≤_ , φ

carrier-of-ba-is-set : (B : BooleanAlgebra 𝓤 𝓥) → is-set ⟪ B ⟫
carrier-of-ba-is-set B = carrier-of-[ poset-of-ba B ]-is-set

meet-of-ba : (B : BooleanAlgebra 𝓤 𝓥) → ⟪ B ⟫ → ⟪ B ⟫ → ⟪ B ⟫
meet-of-ba (_ , (_ , _ , _⋏_ , _) , _) = _⋏_

infixl 4 meet-of-ba

syntax meet-of-ba B x y = x ⋏[ B ] y

join-of-ba : (B : BooleanAlgebra 𝓤 𝓥) → ⟪ B ⟫ → ⟪ B ⟫ → ⟪ B ⟫
join-of-ba (_ , (_ , _ , _ , _ , _⋎_ , _) , _) = _⋎_

infixl 3 join-of-ba

syntax join-of-ba B x y = x ⋎[ B ] y

⊤[_] : (B : BooleanAlgebra 𝓤 𝓥) → ⟪ B ⟫
⊤[ (_ , (_ , ⊤ , _ , _ , _ , _) , _) ] = ⊤

⊥[_] : (B : BooleanAlgebra 𝓤 𝓥) → ⟪ B ⟫
⊥[ (_ , (_ , _ , _ , ⊥ , _ , _) , _) ] = ⊥

\end{code}

\begin{code}

is-lattice-homomorphism : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
                        → (⟪ B ⟫ → ⟨ L ⟩) → Ω (𝓤′ ⊔ 𝓤)
is-lattice-homomorphism {𝓤′} {𝓥′} {𝓤} {𝓥} B L η = β ∧ γ ∧ δ ∧ ϵ
 where
  iss : is-set ⟨ L ⟩
  iss = carrier-of-[ poset-of L ]-is-set

  β : Ω 𝓤
  β = η ⊤[ B ] ＝[ iss ]＝ 𝟏[ L ]

  γ : Ω (𝓤′ ⊔ 𝓤)
  γ = Ɐ x ∶ ⟪ B ⟫ , Ɐ y ∶ ⟪ B ⟫ , η (x ⋏[ B ] y) ＝[ iss ]＝ η x ∧[ L ] η y

  δ : Ω 𝓤
  δ = η ⊥[ B ] ＝[ iss ]＝ 𝟎[ L ]

  ϵ : Ω (𝓤′ ⊔ 𝓤)
  ϵ = Ɐ x ∶ ⟪ B ⟫ , Ɐ y ∶ ⟪ B ⟫ , η (x ⋎[ B ] y) ＝[ iss ]＝ η x ∨[ L ] η y

is-embedding : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦) → (⟪ B ⟫ → ⟨ L ⟩) → Ω (𝓤′ ⊔ 𝓤)
is-embedding {𝓤′} {𝓥′} {𝓤} {𝓥} {𝓦} B L η =
 ι ∧ is-lattice-homomorphism B L η
  where
   iss : is-set ⟨ L ⟩
   iss = carrier-of-[ poset-of L ]-is-set

   iss₀ : is-set ⟪ B ⟫
   iss₀ = carrier-of-[ poset-of-ba B ]-is-set

   ι : Ω (𝓤′ ⊔ 𝓤)
   ι = Ɐ x ∶ ⟪ B ⟫ , Ɐ y ∶ ⟪ B ⟫ , (η x ＝[ iss ]＝ η y) ⇒ (x ＝[ iss₀ ]＝ y)

\end{code}

\begin{code}

_is-sublattice-of_ : BooleanAlgebra 𝓤′ 𝓥′ → Frame 𝓤 𝓥 𝓦 → Ω (𝓤′ ⊔ 𝓤)
_is-sublattice-of_ B L = Ǝ η ∶ (⟪ B ⟫ → ⟨ L ⟩) , is-embedding B L η holds

\end{code}

\begin{code}

is-generated-by : (L : Frame 𝓤 𝓥 𝓦) → (B : BooleanAlgebra 𝓤′ 𝓥′)
                → (⟪ B ⟫ → ⟨ L ⟩) → Ω (𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓤′)
is-generated-by {𝓦 = 𝓦} L B η =
 Ɐ x ∶ ⟨ L ⟩ , Ǝ W ∶ Fam 𝓦 ⟪ B ⟫ , x ＝ ⋁[ L ] ⁅ η w ∣ w ε W ⁆

\end{code}

\begin{code}

extension-lemma : (B : BooleanAlgebra 𝓦 𝓥) (L L′ : Frame 𝓤 𝓦 𝓦)
                → (η : ⟪ B ⟫ → ⟨ L ⟩)
                → is-embedding B L η holds
                → is-generated-by L B η holds
                → (h : ⟪ B ⟫ → ⟨ L′ ⟩)
                → is-lattice-homomorphism B L′ h holds
                → is-contr
                   (Σ h₀ ꞉ (⟨ L ⟩ → ⟨ L′ ⟩) ,
                    (is-a-frame-homomorphism L L′ h₀ holds) × (h ＝ h₀ ∘ η))
extension-lemma {𝓦} {𝓤} B L L′ η e γ h (♠₀ , ♠₁ , _) = (h⁻ , φ , {!!}) , {!!}
 where
  ↓↓_ : ⟨ L ⟩ → Fam 𝓦 ⟨ L′ ⟩
  ↓↓ x = ⁅ h b ∣ (b , _) ∶ Σ b ꞉ ⟪ B ⟫ , (η b ≤[ poset-of L ] x) holds  ⁆

  h⁻ : ⟨ L ⟩ → ⟨ L′ ⟩
  h⁻ x = ⋁[ L′ ] ↓↓ x

\end{code}

We first show that `h⁻` preserves the top element.

\begin{code}

  φ₀ : h⁻ 𝟏[ L ] ＝ 𝟏[ L′ ]
  φ₀ = only-𝟏-is-above-𝟏 L′ (h⁻ 𝟏[ L ]) †
   where
    ♥₀ = pr₁ (pr₂ e)

    ‡ = ⋁[ L′ ]-upper _ (⊤[ B ] , reflexivity+ (poset-of L) ♥₀)

--   open Meets (λ x y → x ≤[ poset-of L ] y)

--   iss : is-set ⟨ L ⟩
--   iss = carrier-of-[ poset-of L ]-is-set

--   β : Ω (𝓤 ⊔ 𝓤)
--   β = Ɐ x ∶ ⟨ L ⟩ , Ɐ y ∶ ⟨ L ⟩ , x ∧[ L ] y ＝[ iss ]＝ x ⋏[ B ] y

--   γ : Ω 𝓤
--   γ = Ɐ x ∶ ⟨ L ⟩ , Ɐ y ∶ ⟨ L ⟩ , x ∨[ L ] y ＝[ iss ]＝ x ⋎[ B ] y

\end{code}
