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
open import Locales.CompactRegular pt fe

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

is-spectral′ : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
            → (f : ⟪ B ⟫ → ⟨ L ⟩) → Ω (𝓤′ ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-spectral′ B L f = Ɐ x ∶ ⟪ B ⟫ , is-compact-open L (f x)

\end{code}

\begin{code}

_is-sublattice-of_ : BooleanAlgebra 𝓤′ 𝓥′ → Frame 𝓤 𝓥 𝓦 → Ω (𝓤′ ⊔ 𝓤)
_is-sublattice-of_ B L = Ǝ η ∶ (⟪ B ⟫ → ⟨ L ⟩) , is-embedding B L η holds

\end{code}

\begin{code}

embedding-is-order-isomorphism : (B : BooleanAlgebra 𝓤 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
                               → (η : ⟪ B ⟫ → ⟨ L ⟩)
                               → (μ : is-embedding B L η holds)
                               → (x y : ⟪ B ⟫)
                               → (x ≤[ poset-of-ba B ] y
                               ↔ η x ≤[ poset-of L ] η y) holds
embedding-is-order-isomorphism B L η μ x y = † , ‡
 where
  open PosetReasoning (poset-of L)

  † : (x ≤[ poset-of-ba B ] y ⇒ η x ≤[ poset-of L ] η y) holds
  † p = η x              ＝⟨ ap η (※ ⁻¹) ⟩ₚ
        η (x ⋏[ B ] y)   ＝⟨ {!!} ⟩ₚ
        η x ∧[ L ] η y   ＝⟨ {!!} ⟩ₚ
        η y              ■
   where
    ※ : x ⋏[ B ] y ＝ x
    ※ = ≤-is-antisymmetric (poset-of-ba B) ※₁ ※₂
     where
      ※₁ : ((x ⋏[ B ] y) ≤[ poset-of-ba B ] x) holds
      ※₁ = {!!}

      ※₂ : (x ≤[ poset-of-ba B ] (x ⋏[ B ] y)) holds
      ※₂ = {!!}

  η-meet-preserving : (x y : ⟪ B ⟫) → η (x ⋏[ B ] y) ＝ η x ∧[ L ] η y
  η-meet-preserving = {!!}

  ‡ : (η x ≤[ poset-of L ] η y ⇒ x ≤[ poset-of-ba B ] y) holds
  ‡ = {!!}

embeddings-lemma : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
                 → (η : ⟪ B ⟫ → ⟨ L ⟩)
                 → is-embedding B L η holds
                 → (x : ⟪ B ⟫) (y : ⟨ L ⟩) → η x ＝ 𝟎[ L ] → x ＝ ⊥[ B ]
embeddings-lemma B L η e x y p =
 ≤-is-antisymmetric (poset-of-ba B) † {!⊥[ B ]-is-bottom!}
  where
   † : (x ≤[ poset-of-ba B ] ⊥[ B ]) holds
   † = {!!}

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
                → is-spectral′ B L η holds
                → is-generated-by L B η holds
                → (h : ⟪ B ⟫ → ⟨ L′ ⟩)
                → is-lattice-homomorphism B L′ h holds
                → is-contr
                   (Σ h₀ ꞉ (⟨ L ⟩ → ⟨ L′ ⟩) ,
                    (is-a-frame-homomorphism L L′ h₀ holds) × (h ＝ h₀ ∘ η))
extension-lemma {𝓦} {𝓤} B L L′ η e@(_ , _ , _ , _ , ♥₂) s γ h (♠₀ , ♠₁ , ♠₂ , ♠₃) = (h⁻ , φ , {!!}) , {!!}
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

    open PosetReasoning (poset-of L′)

    † : (𝟏[ L′ ] ≤[ poset-of L′ ] h⁻ 𝟏[ L ]) holds
    † = 𝟏[ L′ ]      ＝⟨ ♠₀ ⁻¹ ⟩ₚ
        h ⊤[ B ]     ≤⟨ ‡ ⟩
        h⁻ 𝟏[ L ]    ■

  φ₃ : h⁻ 𝟎[ L ] ＝ 𝟎[ L′ ]
  φ₃ = only-𝟎-is-below-𝟎 L′ (h⁻ 𝟎[ L ]) †
   where
    open PosetReasoning (poset-of L′)
    open Joins (λ x y → x ≤[ poset-of L′ ] y)

    † : (h⁻ 𝟎[ L ] ≤[ poset-of L′ ] 𝟎[ L′ ]) holds
    † = h⁻ 𝟎[ L ]              ＝⟨ refl ⟩ₚ
        ⋁[ L′ ] (↓↓ 𝟎[ L ])    ≤⟨ ‡ ⟩
        h ⊥[ B ]               ＝⟨ ♠₂ ⟩ₚ
        𝟎[ L′ ]                ■
         where
          ‡ : (𝟎[ L′ ] is-an-upper-bound-of (↓↓ 𝟎[ L ])) holds
          ‡ (b , q) = h b ≤⟨ {!!} ⟩ {!!} ■

          ♥ : η ⊥[ B ] ＝ 𝟎[ L ]
          ♥ = pr₁ (pr₂ (pr₂ (pr₂ e)))

          ※ : (h ⊥[ B ] is-an-upper-bound-of (↓↓ 𝟎[ L ])) holds
          ※ (b , q) = h b ＝⟨ ap h {!q!} ⟩ₚ h ⊥[ B ] ■

          ‡ = ⋁[ L′ ]-least (↓↓ 𝟎[ L ]) (h ⊥[ B ] , ※)

\end{code}

The function `h⁻` also preserves meets.

\begin{code}

  φ₁ : (x y : ⟨ L ⟩) → h⁻ (x ∧[ L ] y) ＝ h⁻ x ∧[ L′ ] h⁻ y
  φ₁ x y = ≤-is-antisymmetric (poset-of L′) † ‡
   where
    † : (h⁻ (x ∧[ L ] y) ≤[ poset-of L′ ] (h⁻ x ∧[ L′ ] h⁻ y)) holds
    † = ∧[ L′ ]-greatest (h⁻ x) (h⁻ y) (h⁻ (x ∧[ L ] y)) I II
     where
      open PosetReasoning (poset-of L)

      δ₁ : cofinal-in L′ (↓↓ (x ∧[ L ] y)) (↓↓ x) holds
      δ₁ (b , p) = ∣ (b , (η b ≤⟨ p ⟩ x ∧[ L ] y ≤⟨ ∧[ L ]-lower₁ x y ⟩ x ■))
                 , ≤-is-reflexive (poset-of L′) (h b) ∣

      δ₂ : cofinal-in L′ (↓↓ (x ∧[ L ] y)) (↓↓ y) holds
      δ₂ (b , p) = ∣ (b , (η b ≤⟨ p ⟩ x ∧[ L ] y ≤⟨ ∧[ L ]-lower₂ x y ⟩ y ■))
                   , ≤-is-reflexive (poset-of L′) (h b) ∣

      I : (h⁻ (x ∧[ L ] y) ≤[ poset-of L′ ] h⁻ x) holds
      I = cofinal-implies-join-covered L′ _ _ δ₁

      II : (h⁻ (x ∧[ L ] y) ≤[ poset-of L′ ] h⁻ y) holds
      II = cofinal-implies-join-covered L′ _ _ δ₂

    ℱ : Fam 𝓦 ⟨ L′ ⟩
    ℱ = ⁅ (h b₁) ∧[ L′ ] (h b₂)
         ∣ ((b₁ , _) , (b₂ , _))
            ∶ (Σ b₁ ꞉ ⟪ B ⟫ , (η b₁ ≤[ poset-of L ] x) holds)
            × ((Σ b₂ ꞉ ⟪ B ⟫ , (η b₂ ≤[ poset-of L ] y) holds)) ⁆

    ‡ : ((h⁻ x ∧[ L′ ] h⁻ y) ≤[ poset-of L′ ] h⁻ (x ∧[ L ] y)) holds
    ‡ =
     h⁻ x ∧[ L′ ] h⁻ y                        ＝⟨ refl ⟩ₚ
     (⋁[ L′ ] ↓↓ x) ∧[ L′ ] (⋁[ L′ ] ↓↓ y)    ＝⟨ distributivity+ L′ (↓↓ x) (↓↓ y) ⟩ₚ
     ⋁[ L′ ] ℱ                                ≤⟨ ※ ⟩
     h⁻ (x ∧[ L ] y)                          ■
      where
       open PosetReasoning (poset-of L′)
       open Joins (λ x y → x ≤[ poset-of L′ ] y)


       β : (h⁻ (x ∧[ L ] y) is-an-upper-bound-of ℱ) holds
       β ((b₁ , ϕ₁) , (b₂ , ϕ₂)) = h b₁ ∧[ L′ ] h b₂     ＝⟨ ♠₁ b₁ b₂ ⁻¹ ⟩ₚ
                                   h (b₁ ⋏[ B ] b₂)      ≤⟨ ζ ⟩
                                   h⁻ (x ∧[ L ] y)       ■
        where
         ξ : (η (b₁ ⋏[ B ] b₂) ≤[ poset-of L ] (x ∧[ L ] y)) holds
         ξ = η (b₁ ⋏[ B ] b₂)      ＝⟨ pr₁ (pr₂ (pr₂ e)) b₁ b₂ ⟩L
             η b₁ ∧[ L ] η b₂      ≤⟨ ∧[ L ]-left-monotone ϕ₁ ⟩L
             x ∧[ L ] η b₂         ≤⟨ ∧[ L ]-right-monotone ϕ₂ ⟩L
             x ∧[ L ] y            ■L
              where
               open PosetReasoning (poset-of L)
                renaming (_≤⟨_⟩_ to _≤⟨_⟩L_; _■ to _■L; _＝⟨_⟩ₚ_ to _＝⟨_⟩L_)

         ζ : (h (b₁ ⋏[ B ] b₂) ≤[ poset-of L′ ] (⋁[ L′ ] ↓↓ (x ∧[ L ] y))) holds
         ζ = ⋁[ L′ ]-upper (↓↓ (x ∧[ L ] y)) ((b₁ ⋏[ B ] b₂) , ξ)

       ※ = ⋁[ L′ ]-least _ (h⁻ (x ∧[ L ] y) , β)

\end{code}

\begin{code}

  h⁻-is-monotone : is-monotonic (poset-of L) (poset-of L′) h⁻ holds
  h⁻-is-monotone = meet-preserving-implies-monotone L L′ h⁻ φ₁

\end{code}

\begin{code}

  open Joins (λ x y → x ≤[ poset-of L′ ] y)

  ζ⁻ : is-scott-continuous L L′ h⁻ holds
  ζ⁻ = {!!}

  h⁻-preserves-∨ : (x y : ⟨ L ⟩) → h⁻ (x ∨[ L ] y) ＝ h⁻ x ∨[ L′ ] h⁻ y
  h⁻-preserves-∨ x y = ≤-is-antisymmetric (poset-of L′) † ‡
   where
    open PosetReasoning (poset-of L′)

    ※₁ : (h⁻ x ≤[ poset-of L′ ] h⁻ (x ∨[ L ] y)) holds
    ※₁ = h⁻-is-monotone (x , (x ∨[ L ] y)) (∨[ L ]-upper₁ x y)

    ※₂ : (h⁻ y ≤[ poset-of L′ ] h⁻ (x ∨[ L ] y)) holds
    ※₂ = h⁻-is-monotone (y , (x ∨[ L ] y)) (∨[ L ]-upper₂ x y)

    † : (h⁻ (x ∨[ L ] y) ≤[ poset-of L′ ] (h⁻ x ∨[ L′ ] h⁻ y)) holds
    † = h⁻ (x ∨[ L ] y) ≤⟨ {!!} ⟩ {!!} ≤⟨ {!!} ⟩ {!!} ■

    ‡ : ((h⁻ x ∨[ L′ ] h⁻ y) ≤[ poset-of L′ ] h⁻ (x ∨[ L ] y)) holds
    ‡ = ∨[ L′ ]-least ‡₁ ‡₂
     where
      ‡₁ : (h⁻ x ≤[ poset-of L′ ] h⁻ (x ∨[ L ] y)) holds
      ‡₁ = ⋁[ L′ ]-least (↓↓ x) (h⁻ (x ∨[ L ] y) , ♣₁)
       where
        ♣₁ : (h⁻ (x ∨[ L ] y) is-an-upper-bound-of (↓↓ x)) holds
        ♣₁ (b , p) = h b             ≤⟨ ⋁[ L′ ]-upper (↓↓ x) (b , p) ⟩
                     h⁻ x            ≤⟨ ※₁                           ⟩
                     h⁻ (x ∨[ L ] y) ■

      ‡₂ : (h⁻ y ≤[ poset-of L′ ] h⁻ (x ∨[ L ] y)) holds
      ‡₂ = ⋁[ L′ ]-least (↓↓ y) (h⁻ (x ∨[ L ] y) , ♣₂)
       where
        ♣₂ : (h⁻ (x ∨[ L ] y) is-an-upper-bound-of (↓↓ y)) holds
        ♣₂ (b , p) = h b                ≤⟨ ⋁[ L′ ]-upper (↓↓ y) (b , p) ⟩
                     ⋁[ L′ ] (↓↓ y)     ≤⟨ ※₂                           ⟩
                     h⁻ (x ∨[ L ] y)    ■

  φ₂ : (S : Fam 𝓦 ⟨ L ⟩) → (h⁻ (⋁[ L ] S) is-lub-of ⁅ h⁻ x ∣ x ε S ⁆) holds
  φ₂ S@(I , 𝓎) =
   transport (λ - → (- is-lub-of ⁅ h⁻ x ∣ x ε S ⁆) holds) († ⁻¹) ‡
    where
     † : h⁻ (⋁[ L ] S) ＝ ⋁[ L′ ] ⁅ h⁻ x ∣ x ε S ⁆
     † = sc-and-∨-preserving-⇒-⋁-preserving L L′ h⁻ ζ⁻ φ₃ h⁻-preserves-∨ S

     ‡ : ((⋁[ L′ ] ⁅ h⁻ x ∣ x ε S ⁆) is-lub-of ⁅ h⁻ x ∣ x ε S ⁆) holds
     ‡ = ⋁[ L′ ]-upper ⁅ h⁻ x ∣ x ε S ⁆ , ⋁[ L′ ]-least ⁅ h⁻ x ∣ x ε S ⁆

\end{code}

\begin{code}

  φ : is-a-frame-homomorphism L L′ h⁻ holds
  φ = φ₀ , φ₁ , φ₂

\end{code}
