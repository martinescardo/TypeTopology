Ayberk Tosun, completed 30 November 2022.

The main result needed in this module is the extension lemma.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import Slice.Family
open import UF.Base
open import UF.Equiv hiding (_■)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier

module Locales.BooleanAlgebra
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import UF.Logic
open import UF.Subsingletons

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

module Complementation {A : 𝓤  ̇ } (iss : is-set A) (𝟎 𝟏 : A) (_⋏_ _⋎_ : A → A → A) where

 _complements_ : A → A → Ω 𝓤
 x′ complements x = (x ⋏ x′ ＝[ iss ]＝ 𝟎) ∧ (x ⋎ x′ ＝[ iss ]＝ 𝟏)

\end{code}

\begin{code}

satisfies-ba-laws : {A : 𝓤  ̇ } → ba-data 𝓥 A → 𝓤 ⊔ 𝓥  ̇
satisfies-ba-laws {𝓤 = 𝓤} {𝓥 = 𝓥} {A = A} (_≤_ , 𝟏 , _⊓_ , 𝟎 , _⋎_ , ¬_) =
 Σ p ꞉ is-partial-order A _≤_ , rest p holds
  where
   open Meets (λ x y → x ≤ y)
   open Joins (λ x y → x ≤ y)

   rest : is-partial-order A _≤_ → Ω (𝓤 ⊔ 𝓥)
   rest p = β ∧ γ ∧ δ ∧ ϵ ∧ ζ ∧ η
    where
     P : Poset 𝓤 𝓥
     P = A , _≤_ , p

     iss : is-set A
     iss = carrier-of-[ P ]-is-set

     open Complementation iss 𝟎 𝟏 _⊓_ _⋎_

     β : Ω (𝓤 ⊔ 𝓥)
     β = Ɐ x ꞉ A , Ɐ y ꞉ A , (x ⊓ y) is-glb-of (x , y)

     γ : Ω (𝓤 ⊔ 𝓥)
     γ = Ɐ x ꞉ A , x ≤ 𝟏

     δ : Ω (𝓤 ⊔ 𝓥)
     δ = Ɐ x ꞉ A , Ɐ y ꞉ A , _is-lub-of₂_ (x ⋎ y) (x , y)

     ϵ : Ω (𝓤 ⊔ 𝓥)
     ϵ = Ɐ x ꞉ A , 𝟎 ≤ x

     ζ : Ω (𝓤 ⊔ 𝓤)
     ζ = Ɐ x ꞉ A , Ɐ y ꞉ A , Ɐ z ꞉ A , x ⊓ (y ⋎ z) ＝[ iss ]＝ (x ⊓ y) ⋎ (x ⊓ z)

     η : Ω (𝓤 ⊔ 𝓤)
     η = Ɐ x ꞉ A , (¬ x) complements x

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

⋎[_]-is-upper₁ : (B : BooleanAlgebra 𝓤 𝓥)
               → (x y : ⟪ B ⟫) → (x ≤[ poset-of-ba B ] (x ⋎[ B ] y)) holds
⋎[_]-is-upper₁ (_ , _ , (_ , _ , _ , φ , _)) x y = pr₁ (pr₁ (φ x y))

⋎[_]-is-upper₂ : (B : BooleanAlgebra 𝓤 𝓥)
               → (x y : ⟪ B ⟫) → (y ≤[ poset-of-ba B ] (x ⋎[ B ] y)) holds
⋎[_]-is-upper₂ (_ , _ , (_ , _ , _ , φ , _)) x y = pr₂ (pr₁ (φ x y))

⋎[_]-is-least : (B : BooleanAlgebra 𝓤 𝓥)
              → {u x y : ⟪ B ⟫}
              → (x ≤[ poset-of-ba B ] u) holds
              → (y ≤[ poset-of-ba B ] u) holds
              → ((x ⋎[ B ] y) ≤[ poset-of-ba B ] u) holds
⋎[_]-is-least (_ , _ , (_ , _ , _ , φ , _)) {u} {x} {y} p q =
 pr₂ (φ x y) (u , p , q)

⊤[_] : (B : BooleanAlgebra 𝓤 𝓥) → ⟪ B ⟫
⊤[ (_ , (_ , ⊤ , _ , _ , _ , _) , _) ] = ⊤

⊤[_]-is-top : (B : BooleanAlgebra 𝓤 𝓥)
            → (b : ⟪ B ⟫) → (b ≤[ poset-of-ba B ] ⊤[ B ]) holds
⊤[ _ , _ , φ ]-is-top = pr₁ (pr₂ (pr₂ φ))

⊥[_] : (B : BooleanAlgebra 𝓤 𝓥) → ⟪ B ⟫
⊥[ (_ , (_ , _ , _ , ⊥ , _ , _) , _) ] = ⊥

⊥[_]-is-bottom : (B : BooleanAlgebra 𝓤 𝓥)
               → (b : ⟪ B ⟫) → (⊥[ B ] ≤[ poset-of-ba B ] b) holds
⊥[ _ , _ , φ ]-is-bottom = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ φ))))

¬[_]_ : (B : BooleanAlgebra 𝓤 𝓥) → ⟪ B ⟫ → ⟪ B ⟫
¬[ B ] x = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (pr₁ (pr₂ B)))))) x

¬[_]-is-complement : (B : BooleanAlgebra 𝓤 𝓥)
                   → let
                      σ = carrier-of-[ poset-of-ba B ]-is-set
                      open Complementation σ ⊥[ B ] ⊤[ B ] (meet-of-ba B) (join-of-ba B)
                     in
                      (x : ⟪ B ⟫) → ((¬[ B ] x) complements x) holds
¬[_]-is-complement (_ , _ , (_ , _ , _ , _ , _ , _ , φ)) = φ

⋏-distributes-over-⋎ : (B : BooleanAlgebra 𝓤 𝓥)
                     → (x y z : ⟪ B ⟫)
                     → x ⋏[ B ] (y ⋎[ B ] z) ＝ (x ⋏[ B ] y) ⋎[ B ] (x ⋏[ B ] z)
⋏-distributes-over-⋎ (_ , _ , (_ , _ , _ , _ , _ , φ , _)) = φ

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
  γ = Ɐ x ꞉ ⟪ B ⟫ , Ɐ y ꞉ ⟪ B ⟫ , η (x ⋏[ B ] y) ＝[ iss ]＝ η x ∧[ L ] η y

  δ : Ω 𝓤
  δ = η ⊥[ B ] ＝[ iss ]＝ 𝟎[ L ]

  ϵ : Ω (𝓤′ ⊔ 𝓤)
  ϵ = Ɐ x ꞉ ⟪ B ⟫ , Ɐ y ꞉ ⟪ B ⟫ , η (x ⋎[ B ] y) ＝[ iss ]＝ η x ∨[ L ] η y

is-ba-homomorphism : (B₁ : BooleanAlgebra 𝓤 𝓥) (B₂ : BooleanAlgebra 𝓤' 𝓥')
                   → (f : ⟪ B₁ ⟫ → ⟪ B₂ ⟫) → Ω (𝓤 ⊔ 𝓤')
is-ba-homomorphism {𝓤} {𝓥} {𝓤'} {𝓥'} B₁ B₂ f = β ∧ γ ∧ δ ∧ ϵ
 where
  σ : is-set ⟪ B₂ ⟫
  σ = carrier-of-[ poset-of-ba B₂ ]-is-set

  β : Ω 𝓤'
  β = f ⊤[ B₁ ] ＝[ σ ]＝ ⊤[ B₂ ]

  γ : Ω (𝓤 ⊔ 𝓤')
  γ = Ɐ x ꞉ ⟪ B₁ ⟫ , Ɐ y ꞉ ⟪ B₁ ⟫ , f (x ⋏[ B₁ ] y) ＝[ σ ]＝ f x ⋏[ B₂ ] f y

  δ : Ω 𝓤'
  δ = f ⊥[ B₁ ] ＝[ σ ]＝ ⊥[ B₂ ]

  ϵ : Ω (𝓤 ⊔ 𝓤')
  ϵ = Ɐ x ꞉ ⟪ B₁ ⟫ , Ɐ y ꞉ ⟪ B₁ ⟫ , f (x ⋎[ B₁ ] y) ＝[ σ ]＝ f x ⋎[ B₂ ] f y

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

is-ba-embedding : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
             → (⟪ B ⟫ → ⟨ L ⟩) → Ω (𝓤′ ⊔ 𝓤)
is-ba-embedding {𝓤′} {𝓥′} {𝓤} {𝓥} {𝓦} B L η =
 ι ∧ is-lattice-homomorphism B L η
  where
   iss : is-set ⟨ L ⟩
   iss = carrier-of-[ poset-of L ]-is-set

   iss₀ : is-set ⟪ B ⟫
   iss₀ = carrier-of-[ poset-of-ba B ]-is-set

   ι : Ω (𝓤′ ⊔ 𝓤)
   ι = Ɐ x ꞉ ⟪ B ⟫ , Ɐ y ꞉ ⟪ B ⟫ , (η x ＝[ iss ]＝ η y) ⇒ (x ＝[ iss₀ ]＝ y)

embedding-preserves-meets : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
                          → (η : ⟪ B ⟫ → ⟨ L ⟩)
                          → is-ba-embedding B L η holds
                          → (x y : ⟪ B ⟫) → η (x ⋏[ B ] y) ＝ η x ∧[ L ] η y
embedding-preserves-meets B L η (_ , (_ , ξ , _)) = ξ

embedding-injective : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
                    → (η : ⟪ B ⟫ → ⟨ L ⟩)
                    → is-ba-embedding B L η holds
                    → (x y : ⟪ B ⟫) → η x ＝ η y → x ＝ y
embedding-injective B L η (ι , _) = ι

is-spectral′ : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
            → (f : ⟪ B ⟫ → ⟨ L ⟩) → Ω (𝓤′ ⊔ 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-spectral′ B L f = Ɐ x ꞉ ⟪ B ⟫ , is-compact-open L (f x)

\end{code}

\begin{code}

_is-sublattice-of_ : BooleanAlgebra 𝓤′ 𝓥′ → Frame 𝓤 𝓥 𝓦 → Ω (𝓤′ ⊔ 𝓤)
_is-sublattice-of_ B L = Ǝ η ꞉ (⟪ B ⟫ → ⟨ L ⟩) , is-ba-embedding B L η holds

\end{code}

\begin{code}

embedding-preserves-and-reflects-order : (B : BooleanAlgebra 𝓤′ 𝓥′) (L : Frame 𝓤 𝓥 𝓦)
                                       → (η : ⟪ B ⟫ → ⟨ L ⟩)
                                       → (μ : is-ba-embedding B L η holds)
                                       → (x y : ⟪ B ⟫)
                                       → (x ≤[ poset-of-ba B ] y
                                       ⇔ η x ≤[ poset-of L ] η y) holds
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
                 → is-ba-embedding B L η holds
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
 Ɐ x ꞉ ⟨ L ⟩ , x ＝[ σ ]＝ (⋁[ L ] ⁅ η b ∣ (b , _) ∶ (Σ b ꞉ ⟪ B ⟫ , η b ≤ x) ⁆)
  where
   σ : is-set ⟨ L ⟩
   σ = carrier-of-[ poset-of L ]-is-set

   _≤_ = λ x y → (x ≤[ poset-of L ] y) holds

contains-compact-opens : (L : Frame 𝓤 𝓦 𝓦) (B : BooleanAlgebra 𝓦 𝓥)
                       → (⟪ B ⟫ → ⟨ L ⟩) → Ω (𝓤 ⊔ 𝓦 ⁺)
contains-compact-opens L B η =
 Ɐ x ꞉ ⟨ L ⟩ , is-compact-open L x ⇒ (Ǝ b ꞉ ⟪ B ⟫ , η b ＝ x)

\end{code}

\begin{code}

extension-lemma : (B : BooleanAlgebra 𝓦 𝓦) (L L′ : Frame 𝓤 𝓦 𝓦)
                → (η : ⟪ B ⟫ → ⟨ L ⟩)
                → is-ba-embedding B L η holds
                → is-spectral L holds
                → is-spectral′ B L η holds
                → is-generated-by L B η holds
                → contains-compact-opens L B η holds
                → (h : ⟪ B ⟫ → ⟨ L′ ⟩)
                → is-lattice-homomorphism B L′ h holds
                → ∃! h₀ ꞉ (⟨ L ⟩ → ⟨ L′ ⟩) ,
                   is-a-frame-homomorphism L L′ h₀ holds × (h ＝ h₀ ∘ η)
extension-lemma {𝓦} {𝓤} B L L′ η e@(_ , _ , _ , ♥₁ , ♥₂) σ s γ 𝕜 h μ@(♠₀ , ♠₁ , ♠₂ , ♠₃) =
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
        ॐ : (Ǝ (c , d) ꞉ (⟨ L ⟩ × ⟨ L ⟩) ,
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

\section{Transport}

Given a Boolean algebra `L` on some set `X : 𝓤` that has a copy in universe `𝓥`,
then `L` itself has a copy in universe `𝓥`

\begin{code}

transport-ba-structure : (X : 𝓤  ̇) (Y : 𝓤'  ̇) (f : X → Y)
                       → is-equiv f
                       → (b : ba-structure 𝓥 X)
                       → Σ b′ ꞉ ba-structure 𝓥 Y ,
                          (is-ba-homomorphism (X , b) (Y , b′) f holds)
transport-ba-structure {𝓤} {𝓤'} {𝓥} X Y f e b = (d , †) , f-is-hom
 where
  B₁ : BooleanAlgebra 𝓤 𝓥
  B₁ = X , b

  P₁ : Poset 𝓤 𝓥
  P₁ = poset-of-ba B₁

  open PosetNotation P₁

  g : Y → X
  g = inverse f e

  _≼ᵢ_ : Y → Y → Ω 𝓥
  y₁ ≼ᵢ y₂ = g y₁ ≤[ P₁ ] g y₂

  η : f ∘ g ∼ id
  η = inverses-are-sections f e

  ε : g ∘ f ∼ id
  ε = inverses-are-retractions f e

  f-reflects-order : {x₁ x₂ : X} → (f x₁ ≼ᵢ f x₂ ⇒ x₁ ≤ x₂) holds
  f-reflects-order {x₁} {x₂} = transport _holds †
   where
    † : f x₁ ≼ᵢ f x₂ ＝ x₁ ≤ x₂
    † = f x₁ ≼ᵢ f x₂         ＝⟨ refl                           ⟩
        g (f x₁) ≤ g (f x₂)  ＝⟨ ap (λ - → - ≤ g (f x₂)) (ε x₁) ⟩
        x₁ ≤ g (f x₂)        ＝⟨ ap (λ - → x₁ ≤ -) (ε x₂)       ⟩
        x₁ ≤ x₂              ∎

  ≼ᵢ-is-reflexive : is-reflexive _≼ᵢ_ holds
  ≼ᵢ-is-reflexive = ≤-is-reflexive (poset-of-ba B₁) ∘ g

  ≼ᵢ-is-transitive : is-transitive _≼ᵢ_ holds
  ≼ᵢ-is-transitive x y z p q =
   ≤-is-transitive (poset-of-ba B₁) (g x) (g y) (g z) † ‡
    where
     † : (g x ≤ g y) holds
     † = f-reflects-order
          (transport₂ (λ a b → (a ≤ b) holds) (ap g (η x) ⁻¹) (ap g (η y) ⁻¹) p)

     ‡ : (g y ≤ g z) holds
     ‡ = f-reflects-order
          (transport₂ (λ a b → (a ≤ b) holds) (ap g (η y) ⁻¹) (ap g (η z) ⁻¹) q)

  ≼ᵢ-is-antisymmetric : is-antisymmetric _≼ᵢ_
  ≼ᵢ-is-antisymmetric {x} {y} p q =
   x ＝⟨ η x ⁻¹ ⟩ f (g x) ＝⟨ ap f † ⟩ f (g y) ＝⟨ η y ⟩ y ∎
    where
     † : g x ＝ g y
     † = ≤-is-antisymmetric (poset-of-ba B₁) p q

  𝟏ᵢ : Y
  𝟏ᵢ = f ⊤[ B₁ ]

  𝟎ᵢ : Y
  𝟎ᵢ = f ⊥[ B₁ ]

  _⋏ᵢ_ : Y → Y → Y
  y₁ ⋏ᵢ y₂ = f (g y₁ ⋏[ B₁ ] g y₂)

  _⋎ᵢ_ : Y → Y → Y
  y₁ ⋎ᵢ y₂ = f (g y₁ ⋎[ B₁ ] g y₂)

  ¬ᵢ_ : Y → Y
  ¬ᵢ y = f (¬[ B₁ ] g y)

  g-preserves-meets : {y₁ y₂ : Y} → g (y₁ ⋏ᵢ y₂) ＝ g y₁ ⋏[ B₁ ] g y₂
  g-preserves-meets {y₁} {y₂} = ε (g y₁ ⋏[ B₁ ] g y₂)

  g-preserves-joins : {y₁ y₂ : Y} → g (y₁ ⋎ᵢ y₂) ＝ g y₁ ⋎[ B₁ ] g y₂
  g-preserves-joins {y₁} {y₂} = ε (g y₁ ⋎[ B₁ ] g y₂)

  d : ba-data 𝓥 Y
  d = _≼ᵢ_ , f ⊤[ B₁ ] , _⋏ᵢ_ , f ⊥[ B₁ ] , _⋎ᵢ_ , ¬ᵢ_

  open Meets (λ x y → x ≼ᵢ y)
  open Joins (λ x y → x ≼ᵢ y)

  ρ : is-partial-order Y _≼ᵢ_
  ρ = (≼ᵢ-is-reflexive , ≼ᵢ-is-transitive) , ≼ᵢ-is-antisymmetric

  P₂ : Poset 𝓤' 𝓥
  P₂ = Y , (_≼ᵢ_ , ρ)

  𝟏ᵢ-is-top : (y : Y) → (y ≼ᵢ 𝟏ᵢ) holds
  𝟏ᵢ-is-top y = g y    ≤⟨ ⊤[ B₁ ]-is-top (g y) ⟩
               ⊤[ B₁ ] ＝⟨ ε ⊤[ B₁ ] ⁻¹ ⟩ₚ
               g (f ⊤[ B₁ ]) ■
   where
    open PosetReasoning P₁

  𝟎ᵢ-is-bottom : (y : Y) → (𝟎ᵢ ≼ᵢ y) holds
  𝟎ᵢ-is-bottom y = g 𝟎ᵢ           ＝⟨ refl                   ⟩ₚ
                   g (f ⊥[ B₁ ])  ＝⟨ ε ⊥[ B₁ ]              ⟩ₚ
                   ⊥[ B₁ ]        ≤⟨ ⊥[ B₁ ]-is-bottom (g y) ⟩
                   g y            ■
   where
    open PosetReasoning P₁

  ⋏ᵢ-is-glb : (y₁ y₂ : Y) → ((y₁ ⋏ᵢ y₂) is-glb-of (y₁ , y₂)) holds
  ⋏ᵢ-is-glb y₁ y₂ = † , ‡
   where
    open PosetReasoning P₁

    †₁ : ((y₁ ⋏ᵢ y₂) ≼ᵢ y₁) holds
    †₁ = g (y₁ ⋏ᵢ y₂)       ＝⟨ g-preserves-meets ⟩ₚ
         g y₁ ⋏[ B₁ ] g y₂  ≤⟨ ⋏[ B₁ ]-is-lower₁ (g y₁) (g y₂) ⟩
         g y₁               ■

    †₂ : ((y₁ ⋏ᵢ y₂) ≼ᵢ y₂) holds
    †₂ = g (y₁ ⋏ᵢ y₂)       ＝⟨ g-preserves-meets ⟩ₚ
         g y₁ ⋏[ B₁ ] g y₂  ≤⟨ ⋏[ B₁ ]-is-lower₂ (g y₁) (g y₂) ⟩
         g y₂               ■

    † : ((y₁ ⋏ᵢ y₂) is-a-lower-bound-of (y₁ , y₂)) holds
    † = †₁ , †₂

    ‡ : ((𝓁 , _) : lower-bound (y₁ , y₂)) → (g 𝓁 ≤[ P₁ ] g (y₁ ⋏ᵢ y₂)) holds
    ‡ (𝓁 , p , q) = g 𝓁               ≤⟨ ⋏[ B₁ ]-is-greatest p q ⟩
                    g y₁ ⋏[ B₁ ] g y₂ ＝⟨ g-preserves-meets ⁻¹   ⟩ₚ
                    g (y₁ ⋏ᵢ y₂)      ■

  ⋎ᵢ-is-lub : (y₁ y₂ : Y) → ((y₁ ⋎ᵢ y₂) is-lub-of₂ (y₁ , y₂)) holds
  ⋎ᵢ-is-lub y₁ y₂ = † , ‡
   where
    open PosetReasoning P₁

    † : ((y₁ ⋎ᵢ y₂) is-an-upper-bound-of₂ (y₁ , y₂)) holds
    † = †₁ , †₂
     where
      †₁ : (y₁ ≼ᵢ (y₁ ⋎ᵢ y₂)) holds
      †₁ = g y₁                 ≤⟨ ⋎[ B₁ ]-is-upper₁ (g y₁) (g y₂) ⟩
           g y₁ ⋎[ B₁ ] g y₂    ＝⟨ g-preserves-joins ⁻¹           ⟩ₚ
           g (y₁ ⋎ᵢ y₂)         ■

      †₂ : (y₂ ≼ᵢ (y₁ ⋎ᵢ y₂)) holds
      †₂ = g y₂                ≤⟨ ⋎[ B₁ ]-is-upper₂ (g y₁) (g y₂) ⟩
           g y₁ ⋎[ B₁ ] g y₂   ＝⟨ g-preserves-joins ⁻¹ ⟩ₚ
           g (y₁ ⋎ᵢ y₂)        ■

    ‡ : ((𝓊 , _) : upper-bound₂ (y₁ , y₂)) → (g (y₁ ⋎ᵢ y₂) ≤[ P₁ ] g 𝓊) holds
    ‡ (u , p , q) = g (y₁ ⋎ᵢ y₂)      ＝⟨ g-preserves-joins   ⟩ₚ
                    g y₁ ⋎[ B₁ ] g y₂ ≤⟨ ⋎[ B₁ ]-is-least p q ⟩
                    g u               ■

  distributivityᵢ : (y₁ y₂ y₃ : Y) → y₁ ⋏ᵢ (y₂ ⋎ᵢ y₃) ＝ (y₁ ⋏ᵢ y₂) ⋎ᵢ (y₁ ⋏ᵢ y₃)
  distributivityᵢ y₁ y₂ y₃ =
   y₁ ⋏ᵢ (y₂ ⋎ᵢ y₃)                                        ＝⟨ refl ⟩
   f (g y₁ ⋏[ B₁ ] g (y₂ ⋎ᵢ y₃))                           ＝⟨ Ⅰ    ⟩
   f (g y₁ ⋏[ B₁ ] (g y₂ ⋎[ B₁ ] g y₃))                    ＝⟨ Ⅱ    ⟩
   f ((g y₁ ⋏[ B₁ ] g y₂) ⋎[ B₁ ] (g y₁ ⋏[ B₁ ] g y₃))     ＝⟨ Ⅲ    ⟩
   f (g (y₁ ⋏ᵢ y₂) ⋎[ B₁ ] g (y₁ ⋏ᵢ y₃))                   ＝⟨ refl ⟩
   (y₁ ⋏ᵢ y₂) ⋎ᵢ (y₁ ⋏ᵢ y₃)                                ∎
    where
     ※ = λ x y → g-preserves-meets {x} {y} ⁻¹
     Ⅰ = ap (λ - → f (g y₁ ⋏[ B₁ ] -)) g-preserves-joins
     Ⅱ = ap f (⋏-distributes-over-⋎ B₁ (g y₁) (g y₂) (g y₃))
     Ⅲ = ap₂ (λ a b → f (a ⋎[ B₁ ] b)) (※ y₁ y₂) (※ y₁ y₃)

  σ = carrier-of-[ P₂ ]-is-set

  open Complementation σ 𝟎ᵢ 𝟏ᵢ _⋏ᵢ_ _⋎ᵢ_

  ¬ᵢ-is-complement : (y : Y) → ((¬ᵢ y) complements y) holds
  ¬ᵢ-is-complement y = † , ‡
   where
    † : f (g y ⋏[ B₁ ] g (f (¬[ B₁ ] g y))) ＝ f ⊥[ B₁ ]
    † = f (g y ⋏[ B₁ ] g (f (¬[ B₁ ] g y)))    ＝⟨ Ⅰ ⟩
        f (g y ⋏[ B₁ ] ¬[ B₁ ] g y)            ＝⟨ Ⅱ ⟩
        f ⊥[ B₁ ]                              ∎
         where
          Ⅰ = ap (λ - → f (g y ⋏[ B₁ ] -)) (ε (¬[ B₁ ] g y))
          Ⅱ = ap f (pr₁ (¬[ B₁ ]-is-complement (g y)))

    ‡ : f (g y ⋎[ B₁ ] g (f (¬[ B₁ ] g y)) ) ＝ f ⊤[ B₁ ]
    ‡ = f (g y ⋎[ B₁ ] g (f (¬[ B₁ ] g y)) )   ＝⟨ Ⅰ ⟩
        f (g y ⋎[ B₁ ] ¬[ B₁ ] g y)            ＝⟨ Ⅱ ⟩
        f ⊤[ B₁ ]                              ∎
         where
          Ⅰ = ap (λ - → f (g y ⋎[ B₁ ] -)) (ε (¬[ B₁ ] g y))
          Ⅱ = ap f (pr₂ (¬[ B₁ ]-is-complement (g y)))

  † : satisfies-ba-laws d
  † = ρ
    , ⋏ᵢ-is-glb , 𝟏ᵢ-is-top , ⋎ᵢ-is-lub , 𝟎ᵢ-is-bottom
    , distributivityᵢ , ¬ᵢ-is-complement

  f-is-hom : is-ba-homomorphism (X , b) (Y , d , †) f holds
  f-is-hom = refl , γ , refl , ϵ
   where
    γ : (x₁ x₂ : X) → f (x₁ ⋏[ B₁ ] x₂) ＝ f x₁ ⋏ᵢ f x₂
    γ x₁ x₂ = f (x₁ ⋏[ B₁ ] x₂)               ＝⟨ Ⅰ    ⟩
              f (g (f x₁) ⋏[ B₁ ] x₂)         ＝⟨ Ⅱ    ⟩
              f (g (f x₁) ⋏[ B₁ ] g (f x₂))   ＝⟨ Ⅲ    ⟩
              f (g (f x₁ ⋏ᵢ f x₂))            ＝⟨ Ⅳ    ⟩
              f (g (f x₁) ⋏[ B₁ ] g (f x₂))   ＝⟨ refl ⟩
              f x₁ ⋏ᵢ f x₂                    ∎
               where
                Ⅰ = ap (λ - → f (-        ⋏[ B₁ ] x₂)) (ε x₁ ⁻¹)
                Ⅱ = ap (λ - → f (g (f x₁) ⋏[ B₁ ] -))  (ε x₂ ⁻¹)
                Ⅲ = ap f g-preserves-meets ⁻¹
                Ⅳ = η (f x₁ ⋏ᵢ f x₂)

    ϵ : (x₁ x₂ : X) → f (x₁ ⋎[ B₁ ] x₂) ＝ f x₁ ⋎ᵢ f x₂
    ϵ x₁ x₂ = f (x₁ ⋎[ B₁ ] x₂)               ＝⟨ Ⅰ ⟩
              f (g (f x₁) ⋎[ B₁ ] x₂)         ＝⟨ Ⅱ ⟩
              f (g (f x₁) ⋎[ B₁ ] g (f x₂))   ＝⟨ Ⅲ ⟩
              f (g (f x₁ ⋎ᵢ f x₂))            ＝⟨ Ⅳ ⟩
              f x₁ ⋎ᵢ f x₂                    ∎
               where
                Ⅰ = ap (λ - → f (- ⋎[ B₁ ] x₂))       (ε x₁ ⁻¹)
                Ⅱ = ap (λ - → f (g (f x₁) ⋎[ B₁ ] -)) (ε x₂ ⁻¹)
                Ⅲ = ap f (g-preserves-joins ⁻¹ )
                Ⅳ = η (f x₁ ⋎ᵢ f x₂)

\end{code}
