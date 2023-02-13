Ayberk Tosun, completed 30 November 2022.

The main result needed in this module is the extension lemma.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe --auto-inline --lossy-unification #-}

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
open import UF.Logic
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

\end{code}

Since the order is derivable from the meets (or the joins), it might be room for
further work to define the order using the meets. However, the universes will
change if we do this so it is not clear what it will result in.

\begin{code}

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

⋏[_]-is-lower₁ : (B : BooleanAlgebra 𝓤 𝓥)
               → (x y : ⟪ B ⟫) → ((x ⋏[ B ] y) ≤[ poset-of-ba B ] x) holds
⋏[_]-is-lower₁ B@(_ , _ , (_ , φ , _ , _)) x y = pr₁ (pr₁ (φ x y))

⋏[_]-is-lower₂ : (B : BooleanAlgebra 𝓤 𝓥)
               → (x y : ⟪ B ⟫) → ((x ⋏[ B ] y) ≤[ poset-of-ba B ] y) holds
⋏[_]-is-lower₂ B@(_ , _ , (_ , φ , _ , _)) x y = pr₂ (pr₁ (φ x y))

⋏[_]-is-greatest : (B : BooleanAlgebra 𝓤 𝓥) {x y l : ⟪ B ⟫}
                 → (l ≤[ poset-of-ba B ] x) holds
                 → (l ≤[ poset-of-ba B ] y) holds
                 → (l ≤[ poset-of-ba B ] (x ⋏[ B ] y)) holds
⋏[_]-is-greatest B@(_ , _ , (_ , φ , _ , _)) {x} {y} {l} p q =
 pr₂ (φ x y) (l , p , q)

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

⊥[_]-is-bottom : (B : BooleanAlgebra 𝓤 𝓥)
               → (b : ⟪ B ⟫) → (⊥[ B ] ≤[ poset-of-ba B ] b) holds
⊥[ _ , _ , φ ]-is-bottom = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ φ))))

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

lattice-homomorphisms-are-monotone : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
                                    → (h : ⟪ B ⟫ → ⟨ L ⟩)
                                    → is-lattice-homomorphism B L h holds
                                    → (x y : ⟪ B ⟫)
                                    → (x ≤[ poset-of-ba B ] y) holds
                                    → (h x ≤[ poset-of L ] h y) holds
lattice-homomorphisms-are-monotone B L h (β , γ , _) x y p =
 h x ＝⟨ † ⁻¹ ⟩ₚ h x ∧[ L ] h y ≤⟨ ∧[ L ]-lower₂ (h x) (h y) ⟩ h y ■
  where
   open PosetReasoning (poset-of L)

   ‡ : x ⋏[ B ] y ＝ x
   ‡ = ≤-is-antisymmetric (poset-of-ba B)
        (⋏[ B ]-is-lower₁ x y)
        (⋏[ B ]-is-greatest (≤-is-reflexive (poset-of-ba B) x) p)

   † : h x ∧[ L ] h y ＝ h x
   † = h x ∧[ L ] h y      ＝⟨ γ x y ⁻¹  ⟩
       h (x ⋏[ B ] y)      ＝⟨ ap h ‡    ⟩
       h x                 ∎

is-embedding : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
             → (⟪ B ⟫ → ⟨ L ⟩) → Ω (𝓤′ ⊔ 𝓤)
is-embedding {𝓤′} {𝓥′} {𝓤} {𝓥} {𝓦} B L η =
 ι ∧ is-lattice-homomorphism B L η
  where
   iss : is-set ⟨ L ⟩
   iss = carrier-of-[ poset-of L ]-is-set

   iss₀ : is-set ⟪ B ⟫
   iss₀ = carrier-of-[ poset-of-ba B ]-is-set

   ι : Ω (𝓤′ ⊔ 𝓤)
   ι = Ɐ x ∶ ⟪ B ⟫ , Ɐ y ∶ ⟪ B ⟫ , (η x ＝[ iss ]＝ η y) ⇒ (x ＝[ iss₀ ]＝ y)

embedding-preserves-meets : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
                          → (η : ⟪ B ⟫ → ⟨ L ⟩)
                          → is-embedding B L η holds
                          → (x y : ⟪ B ⟫) → η (x ⋏[ B ] y) ＝ η x ∧[ L ] η y
embedding-preserves-meets B L η (_ , (_ , ξ , _)) = ξ

embedding-injective : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
                    → (η : ⟪ B ⟫ → ⟨ L ⟩)
                    → is-embedding B L η holds
                    → (x y : ⟪ B ⟫) → η x ＝ η y → x ＝ y
embedding-injective B L η (ι , _) = ι

is-spectral′ : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
            → (f : ⟪ B ⟫ → ⟨ L ⟩) → Ω (𝓤′ ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-spectral′ B L f = Ɐ x ∶ ⟪ B ⟫ , is-compact-open L (f x)

\end{code}

\begin{code}

_is-sublattice-of_ : BooleanAlgebra 𝓤′ 𝓥′ → Frame 𝓤 𝓥 𝓦 → Ω (𝓤′ ⊔ 𝓤)
_is-sublattice-of_ B L = Ǝ η ∶ (⟪ B ⟫ → ⟨ L ⟩) , is-embedding B L η holds

\end{code}

\begin{code}

embedding-preserves-and-reflects-order : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
                                       → (η : ⟪ B ⟫ → ⟨ L ⟩)
                                       → (μ : is-embedding B L η holds)
                                       → (x y : ⟪ B ⟫)
                                       → (x ≤[ poset-of-ba B ] y
                                       ↔ η x ≤[ poset-of L ] η y) holds
embedding-preserves-and-reflects-order B L η μ x y = † , ‡
 where
  η-meet-preserving : (x y : ⟪ B ⟫) → η (x ⋏[ B ] y) ＝ η x ∧[ L ] η y
  η-meet-preserving = embedding-preserves-meets B L η μ

  † : (x ≤[ poset-of-ba B ] y ⇒ η x ≤[ poset-of L ] η y) holds
  † p = η x              ＝⟨ ap η (※ ⁻¹)              ⟩ₚ
        η (x ⋏[ B ] y)   ＝⟨ η-meet-preserving x y    ⟩ₚ
        η x ∧[ L ] η y   ≤⟨ ∧[ L ]-lower₂ (η x) (η y) ⟩
        η y              ■
   where
    open PosetReasoning (poset-of L)

    ※ : x ⋏[ B ] y ＝ x
    ※ = ≤-is-antisymmetric (poset-of-ba B) ※₁ ※₂
     where
      ※₁ : ((x ⋏[ B ] y) ≤[ poset-of-ba B ] x) holds
      ※₁ = ⋏[ B ]-is-lower₁ x y

      ※₂ : (x ≤[ poset-of-ba B ] (x ⋏[ B ] y)) holds
      ※₂ = ⋏[ B ]-is-greatest (≤-is-reflexive (poset-of-ba B) x) p

  ‡ : (η x ≤[ poset-of L ] η y ⇒ x ≤[ poset-of-ba B ] y) holds
  ‡ p = x ＝⟨ ♠ ⁻¹ ⟩ₚ x ⋏[ B ] y ≤⟨ ⋏[ B ]-is-lower₂ x y ⟩ y ■
   where
    open PosetReasoning (poset-of-ba B)

    ♥ : η (x ⋏[ B ] y) ＝ η x
    ♥ = η (x ⋏[ B ] y)     ＝⟨ embedding-preserves-meets B L η μ x y ⟩
        η x ∧[ L ] η y     ＝⟨ connecting-lemma₁ L p ⁻¹              ⟩
        η x                ∎

    ♠ : x ⋏[ B ] y ＝ x
    ♠ = embedding-injective B L η μ (x ⋏[ B ] y) x ♥

embeddings-lemma : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
                 → (η : ⟪ B ⟫ → ⟨ L ⟩)
                 → is-embedding B L η holds
                 → (x : ⟪ B ⟫) → (η x ≤[ poset-of L ] 𝟎[ L ]) holds → x ＝ ⊥[ B ]
embeddings-lemma B L η (ι , _ , (_ , ξ , _)) x p = ι x ⊥[ B ] †
 where
  † : η x ＝ η ⊥[ B ]
  † = η x ＝⟨ only-𝟎-is-below-𝟎 L (η x) p ⟩ 𝟎[ L ] ＝⟨ ξ ⁻¹   ⟩ η ⊥[ B ] ∎

\end{code}

\begin{code}

is-generated-by : (L : Frame 𝓤 𝓦 𝓦) → (B : BooleanAlgebra 𝓦 𝓥)
                → (⟪ B ⟫ → ⟨ L ⟩) → Ω 𝓤
is-generated-by {𝓦 = 𝓦} L B η =
 Ɐ x ∶ ⟨ L ⟩ , x ＝[ σ ]＝ (⋁[ L ] ⁅ η b ∣ (b , _) ∶ (Σ b ꞉ ⟪ B ⟫ , η b ≤ x) ⁆)
  where
   σ : is-set ⟨ L ⟩
   σ = carrier-of-[ poset-of L ]-is-set

   _≤_ = λ x y → (x ≤[ poset-of L ] y) holds

contains-compact-opens : (L : Frame 𝓤 𝓦 𝓦) (B : BooleanAlgebra 𝓦 𝓥)
                       → (⟪ B ⟫ → ⟨ L ⟩) → Ω (𝓤 ⊔ 𝓦 ⁺)
contains-compact-opens L B η =
 Ɐ x ∶ ⟨ L ⟩ , is-compact-open L x ⇒ (Ǝ b ∶ ⟪ B ⟫ , η b ＝ x)

\end{code}

\begin{code}

extension-lemma : (B : BooleanAlgebra 𝓦 𝓥) (L L′ : Frame 𝓤 𝓦 𝓦)
                → (η : ⟪ B ⟫ → ⟨ L ⟩)
                → is-embedding B L η holds
                → is-spectral L holds
                → is-spectral L′ holds
                → is-spectral′ B L η holds
                → is-generated-by L B η holds
                → contains-compact-opens L B η holds
                → (h : ⟪ B ⟫ → ⟨ L′ ⟩)
                → is-lattice-homomorphism B L′ h holds
                → ∃! h₀ ꞉ (⟨ L ⟩ → ⟨ L′ ⟩) ,
                   is-a-frame-homomorphism L L′ h₀ holds × (h ＝ h₀ ∘ η)
extension-lemma {𝓦} {𝓤} B L L′ η e@(_ , _ , _ , ♥₁ , ♥₂) σ σ′ s γ 𝕜 h μ@(♠₀ , ♠₁ , ♠₂ , ♠₃) =
 (h⁻ , φ , ψ) , ϑ
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
        ⋁[ L′ ] (↓↓ 𝟎[ L ])    ≤⟨ Ⅰ     ⟩
        h ⊥[ B ]               ＝⟨ ♠₂   ⟩ₚ
        𝟎[ L′ ]                ■
         where
          ♥ : η ⊥[ B ] ＝ 𝟎[ L ]
          ♥ = pr₁ (pr₂ (pr₂ (pr₂ e)))

          ※ : (h ⊥[ B ] is-an-upper-bound-of (↓↓ 𝟎[ L ])) holds
          ※ (b , q) = h b         ＝⟨ ap h (embeddings-lemma B L η e b q) ⟩ₚ
                      h ⊥[ B ]    ■

          Ⅰ = ⋁[ L′ ]-least (↓↓ 𝟎[ L ]) (h ⊥[ B ] , ※)

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
     (⋁[ L′ ] ↓↓ x) ∧[ L′ ] (⋁[ L′ ] ↓↓ y)    ＝⟨ Ⅰ ⟩ₚ
     ⋁[ L′ ] ℱ                                ≤⟨ Ⅱ ⟩
     h⁻ (x ∧[ L ] y)                          ■
      where
       open PosetReasoning (poset-of L′)
       open Joins (λ x y → x ≤[ poset-of L′ ] y)

       Ⅰ = distributivity+ L′ (↓↓ x) (↓↓ y)

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

       Ⅱ = ⋁[ L′ ]-least _ (h⁻ (x ∧[ L ] y) , β)

\end{code}

\begin{code}

  h⁻-is-monotone : is-monotonic (poset-of L) (poset-of L′) h⁻ holds
  h⁻-is-monotone = meet-preserving-implies-monotone L L′ h⁻ φ₁

\end{code}

\begin{code}

  open Joins (λ x y → x ≤[ poset-of L′ ] y)

  ψ₁ : h ∼ h⁻ ∘ η
  ψ₁ b = ≤-is-antisymmetric (poset-of L′) (χ b) (ϕ b)
   where
    open PosetReasoning (poset-of L′)

    χ : (b : ⟪ B ⟫) → (h b ≤[ poset-of L′ ] h⁻ (η b)) holds
    χ b = ⋁[ L′ ]-upper (↓↓ (η b)) (b , ≤-is-reflexive (poset-of L) (η b))

    ϕ : (b : ⟪ B ⟫) → (h⁻ (η b) ≤[ poset-of L′ ] h b) holds
    ϕ b = ⋁[ L′ ]-least (↓↓ (η b)) (h b , ϕ₁)
     where
      ϕ₁ : (h b is-an-upper-bound-of (↓↓ η b)) holds
      ϕ₁ (bᵢ , p) = lattice-homomorphisms-are-monotone B L′ h μ bᵢ b ϕ₂
       where
        ϕ₂ : (bᵢ ≤[ poset-of-ba B ] b) holds
        ϕ₂ = pr₂ (embedding-preserves-and-reflects-order B L η e bᵢ b) p

  ψ : h ＝ h⁻ ∘ η
  ψ = dfunext fe ψ₁

\end{code}

\begin{code}

  ζ⁻ : is-scott-continuous L L′ h⁻ holds
  ζ⁻ S δ = transport (λ - → (- is-lub-of ⁅ h⁻ x ∣ x ε S ⁆) holds) (※ ⁻¹) ♣
   where
    † : (h⁻ (⋁[ L ] S) ≤[ poset-of L′ ] (⋁[ L′ ] ⁅ h⁻ x ∣ x ε S ⁆)) holds
    † = ⋁[ L′ ]-least (↓↓ (⋁[ L ] S)) ((⋁[ L′ ] ⁅ h⁻ x ∣ x ε S ⁆) , †₁)
     where
      open PosetReasoning (poset-of L′)

      †₁ : ((⋁[ L′ ] ⁅ h⁻ x ∣ x ε S ⁆) is-an-upper-bound-of (↓↓ (⋁[ L ] S))) holds
      †₁ (b , p) =
       h b                          ＝⟨ ψ₁ b ⟩ₚ
       h⁻ (η b)                     ≤⟨ †₂ ⟩
       ⋁[ L′ ] ⁅ h⁻ x ∣ x ε S ⁆     ■
        where
         †₃ : (Σ k ꞉ index S , ((η b ≤[ poset-of L ] (S [ k ])) holds))
            → (h⁻ (η b) ≤[ poset-of L′ ] (⋁[ L′ ] (⁅ h⁻ x ∣ x ε S ⁆))) holds
         †₃ (k , q) =
          h⁻ (η b)                   ≤⟨ h⁻-is-monotone (η b , S [ k ]) q ⟩
          h⁻ (S [ k ])               ≤⟨ ⋁[ L′ ]-upper ⁅ h⁻ x ∣ x ε S ⁆ k ⟩
          ⋁[ L′ ] ⁅ h⁻ x ∣ x ε S ⁆   ■

         †₂ : (h⁻ (η b) ≤[ poset-of L′ ] (⋁[ L′ ] (⁅ h⁻ x ∣ x ε S ⁆))) holds
         †₂ = ∥∥-rec (holds-is-prop (_ ≤[ poset-of L′ ] _)) †₃ (s b S δ p)

    ‡ : ((⋁[ L′ ] ⁅ h⁻ x ∣ x ε S ⁆) ≤[ poset-of L′ ] h⁻ (⋁[ L ] S)) holds
    ‡ = ⋁[ L′ ]-least ⁅ h⁻ x ∣ x ε S ⁆ (h⁻ (⋁[ L ] S) , ‡₁)
     where
      ‡₁ : (h⁻ (⋁[ L ] S) is-an-upper-bound-of ⁅ h⁻ x ∣ x ε S ⁆) holds
      ‡₁ i = h⁻-is-monotone ((S [ i ]) , ⋁[ L ] S) (⋁[ L ]-upper S i)

    ※ : h⁻ (⋁[ L ] S) ＝ ⋁[ L′ ] ⁅ h⁻ x ∣ x ε S ⁆
    ※ = ≤-is-antisymmetric (poset-of L′) † ‡

    ♣ : ((⋁[ L′ ] ⁅ h⁻ x ∣ x ε S ⁆) is-lub-of ⁅ h⁻ x ∣ x ε S ⁆) holds
    ♣ = ⋁[ L′ ]-upper ⁅ h⁻ x ∣ x ε S ⁆ , ⋁[ L′ ]-least ⁅ h⁻ x ∣ x ε S ⁆

  h⁻-preserves-∨ : (x y : ⟨ L ⟩) → h⁻ (x ∨[ L ] y) ＝ h⁻ x ∨[ L′ ] h⁻ y
  h⁻-preserves-∨ x y = ≤-is-antisymmetric (poset-of L′) † ‡
   where
    ※₁ : (h⁻ x ≤[ poset-of L′ ] h⁻ (x ∨[ L ] y)) holds
    ※₁ = h⁻-is-monotone (x , (x ∨[ L ] y)) (∨[ L ]-upper₁ x y)

    ※₂ : (h⁻ y ≤[ poset-of L′ ] h⁻ (x ∨[ L ] y)) holds
    ※₂ = h⁻-is-monotone (y , (x ∨[ L ] y)) (∨[ L ]-upper₂ x y)

    † : (h⁻ (x ∨[ L ] y) ≤[ poset-of L′ ] (h⁻ x ∨[ L′ ] h⁻ y)) holds
    † = ⋁[ L′ ]-least (↓↓ (x ∨[ L ] y)) ((h⁻ x ∨[ L′ ] h⁻ y) , †₁)
     where
      †₁ : ((h⁻ x ∨[ L′ ] h⁻ y) is-an-upper-bound-of (↓↓ (x ∨[ L ] y))) holds
      †₁ (b , p) = ∥∥-rec
                    (holds-is-prop (h b ≤[ poset-of L′ ] (h⁻ x ∨[ L′ ] h⁻ y)))
                    †₂
                    ॐ
       where
        ॐ : (Ǝ (c , d) ∶ (⟨ L ⟩ × ⟨ L ⟩) ,
                (is-compact-open L c holds)
              × (is-compact-open L d holds)
              × (η b ≤[ poset-of L ] (c ∨[ L ] d)) holds
              × (c ≤[ poset-of L ] x) holds
              × (d ≤[ poset-of L ] y) holds)
             holds
        ॐ = compact-join-lemma L σ x y (η b) (s b) p

        †₂ : Σ (c , d) ꞉ (⟨ L ⟩ × ⟨ L ⟩) ,
                (is-compact-open L c holds)
             × (is-compact-open L d holds)
             × (η b ≤[ poset-of L ] (c ∨[ L ] d)) holds
             × (c ≤[ poset-of L ] x) holds
             × (d ≤[ poset-of L ] y) holds
           → (h b ≤[ poset-of L′ ] (h⁻ x ∨[ L′ ] h⁻ y)) holds
        †₂ ((c , d) , κc , κd , ϑ , χ , ξ) =
         h b                  ＝⟨ ψ₁ b ⟩ₚ
         h⁻ (η b)             ≤⟨ Ⅰ   ⟩
         h⁻ (c ∨[ L ] d)      ≤⟨ Ⅱ   ⟩
         h⁻ c ∨[ L′ ] h⁻ d    ≤⟨ Ⅴ   ⟩
         h⁻ c ∨[ L′ ] h⁻ y    ≤⟨ Ⅵ   ⟩
         h⁻ x ∨[ L′ ] h⁻ y    ■
          where
           open PosetReasoning (poset-of L′)

           Ⅰ = h⁻-is-monotone (η b , (c ∨[ L ] d)) ϑ

           Ⅱ : (h⁻ (c ∨[ L ] d) ≤[ poset-of L′ ] ((h⁻ c) ∨[ L′ ] (h⁻ d))) holds
           Ⅱ = h⁻ (c ∨[ L ] d) ≤⟨ ♣ ⟩ 𝓇𝒽𝓈 ＝⟨ ※ ⁻¹ ⟩ₚ h⁻ c ∨[ L′ ] h⁻ d ■
            where
             open PosetReasoning (poset-of L)
              renaming (_≤⟨_⟩_ to _≤⟨_⟩ₗ_; _■ to _𝔔𝔈𝔇; _＝⟨_⟩ₚ_ to _＝⟨_⟩ₗ_)

             𝓇𝒽𝓈 =
              ⋁[ L′ ]
               ⁅ h b₁ ∨[ L′ ] h b₂
                 ∣ ((b₁ , _) , (b₂ , _))
                    ∶ (Σ b₁ ꞉ ⟪ B ⟫ , (η b₁ ≤[ poset-of L ] c) holds)
                    × (Σ b₂ ꞉ ⟪ B ⟫ , (η b₂ ≤[ poset-of L ] d) holds) ⁆

             ※ : h⁻ c ∨[ L′ ] h⁻ d
               ＝ ⋁[ L′ ]
                   ⁅ h b₁ ∨[ L′ ] h b₂
                     ∣ ((b₁ , _) , (b₂ , _))
                        ∶ (Σ b₁ ꞉ ⟪ B ⟫ , (η b₁ ≤[ poset-of L ] c) holds)
                        × (Σ b₂ ꞉ ⟪ B ⟫ , (η b₂ ≤[ poset-of L ] d) holds) ⁆
             ※ = ∨[ L′ ]-iterated-join (↓↓ c) (↓↓ d) ∣ i₁ ∣ ∣ i₂ ∣
              where
               i₁ : index (↓↓ c)
               i₁ = ⊥[ B ] , (η ⊥[ B ]    ＝⟨ ♥₁             ⟩ₗ
                              𝟎[ L ]      ≤⟨ 𝟎-is-bottom L c ⟩ₗ
                              c           𝔔𝔈𝔇)

               i₂ : index (↓↓ d)
               i₂ = ⊥[ B ] , (η ⊥[ B ]    ＝⟨ ♥₁             ⟩ₗ
                              𝟎[ L ]      ≤⟨ 𝟎-is-bottom L d ⟩ₗ
                              d           𝔔𝔈𝔇)

             ♣₁ : (𝓇𝒽𝓈 is-an-upper-bound-of (↓↓ (c ∨[ L ] d))) holds
             ♣₁ (b , q) =
              ∥∥-rec₂ (holds-is-prop (h b ≤[ poset-of L′ ] 𝓇𝒽𝓈)) ♣₂ (𝕜 c κc) (𝕜 d κd)
               where
                ♣₂ : (Σ b₁ ꞉ ⟪ B ⟫ , η b₁ ＝ c)
                   → (Σ b₂ ꞉ ⟪ B ⟫ , η b₂ ＝ d)
                   → (h b ≤[ poset-of L′ ] 𝓇𝒽𝓈) holds
                ♣₂ (b₁ , r₁) (b₂ , r₂) =
                 h b                     ≤⟨ Ⅰ₀ ⟩
                 h (b₁ ⋎[ B ] b₂)        ＝⟨ ♠₃ b₁ b₂ ⟩ₚ
                 (h b₁) ∨[ L′ ] (h b₂)   ≤⟨ ᕯ ⟩
                 𝓇𝒽𝓈                     ■
                  where
                   ᕯ₁ = reflexivity+ (poset-of L) r₁
                   ᕯ₂ = reflexivity+ (poset-of L) r₂
                   ᕯ  = ⋁[ L′ ]-upper _ ((b₁ , ᕯ₁), (b₂ , ᕯ₂))

                   ν : (η b ≤[ poset-of L ] η (b₁ ⋎[ B ] b₂)) holds
                   ν = η b                    ≤⟨ q ⟩ₗ
                       c ∨[ L ] d             ＝⟨ ϟ ⟩ₗ
                       (η b₁) ∨[ L ] d        ＝⟨ ϡ ⟩ₗ
                       (η b₁) ∨[ L ] (η b₂)   ＝⟨ ͱ ⟩ₗ
                       η (b₁ ⋎[ B ] b₂)       𝔔𝔈𝔇
                        where
                         ϟ = ap (λ - → - ∨[ L ] d) (r₁ ⁻¹)
                         ϡ = ap (λ - → (η b₁) ∨[ L ] -) (r₂ ⁻¹)
                         ͱ = ♥₂ b₁ b₂ ⁻¹

                   υ : (b ≤[ poset-of-ba B ] (b₁ ⋎[ B ] b₂)) holds
                   υ = pr₂ (embedding-preserves-and-reflects-order B L η e b _) ν

                   Ⅰ₀ = lattice-homomorphisms-are-monotone B L′ h μ b _ υ

             ♣ = ⋁[ L′ ]-least (↓↓ (c ∨[ L ] d)) (𝓇𝒽𝓈 , ♣₁)

           Ⅴ = ∨[ L′ ]-right-monotone (h⁻-is-monotone (d , y) ξ)
           Ⅵ = ∨[ L′ ]-left-monotone (h⁻-is-monotone (c , x) χ)

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
                      where
                       open PosetReasoning (poset-of L′)

      ‡₂ : (h⁻ y ≤[ poset-of L′ ] h⁻ (x ∨[ L ] y)) holds
      ‡₂ = ⋁[ L′ ]-least (↓↓ y) (h⁻ (x ∨[ L ] y) , ♣₂)
       where
        ♣₂ : (h⁻ (x ∨[ L ] y) is-an-upper-bound-of (↓↓ y)) holds
        ♣₂ (b , p) = h b                ≤⟨ ⋁[ L′ ]-upper (↓↓ y) (b , p) ⟩
                     ⋁[ L′ ] (↓↓ y)     ≤⟨ ※₂                           ⟩
                     h⁻ (x ∨[ L ] y)    ■
                      where
                       open PosetReasoning (poset-of L′)

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

The map `h⁻` is the _unique_ map making the diagram commute.

\begin{code}

  ϑ : is-central
       (Σ h⁻₀ ꞉ (⟨ L ⟩ → ⟨ L′ ⟩) ,
         is-a-frame-homomorphism L L′ h⁻₀ holds × (h ＝ h⁻₀ ∘ η) )
       (h⁻ , (φ , ψ))
  ϑ (h⁻₀ , φ′@(φ′₁ , φ′₂ , φ′₃) , ψ′) = to-subtype-＝ † (dfunext fe ϑ₁)
   where
    _≤L_ = λ x y → (x ≤[ poset-of L ] y) holds

    † : (h′ : ⟨ L ⟩ → ⟨ L′ ⟩)
      → is-prop (is-a-frame-homomorphism L L′ h′ holds × (h ＝ h′ ∘ η))
    † h′ = ×-is-prop
            (holds-is-prop (is-a-frame-homomorphism L L′ h′))
            (Π-is-set fe λ _ → carrier-of-[ poset-of L′ ]-is-set)

    ϑ₁ : (x : ⟨ L ⟩) → h⁻ x ＝ h⁻₀ x
    ϑ₁ x =
     h⁻ x                                                      ＝⟨ refl ⟩
     ⋁[ L′ ] (↓↓ x)                                            ＝⟨ refl ⟩
     ⋁[ L′ ] ⁅ h b ∣ (b , _) ∶ Σ b ꞉ ⟪ B ⟫ , η b ≤L x  ⁆       ＝⟨ Ⅰ    ⟩
     ⋁[ L′ ] ⁅ h⁻₀ (η b) ∣ (b , _) ∶ Σ b ꞉ ⟪ B ⟫ , η b ≤L x  ⁆ ＝⟨ Ⅱ    ⟩
     h⁻₀ (⋁[ L ] ⁅ η b ∣ (b , _) ∶ Σ b ꞉ ⟪ B ⟫ , η b ≤L x  ⁆)  ＝⟨ Ⅲ    ⟩
     h⁻₀ x                                                     ∎
      where
       ψ′′ : (b : ⟪ B ⟫) → h b ＝ h⁻₀ (η b)
       ψ′′ b = ap (λ - → - b) ψ′

       Ⅰ = ap
            (λ - → ⋁[ L′ ] (index (↓↓ x) , -))
            (dfunext fe λ { (b , _) → ψ′′ b })

       Ⅱ = ⋁[ L′ ]-unique _ _ (φ′₃ ⁅ η b ∣ (b , _) ∶ Σ b ꞉ ⟪ B ⟫ , η b ≤L x  ⁆) ⁻¹

       Ⅲ = ap h⁻₀ (γ x ⁻¹ )

\end{code}
