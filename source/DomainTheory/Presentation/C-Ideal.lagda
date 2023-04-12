

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}
open import MLTT.Spartan hiding (J)

open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module DomainTheory.Presentation.C-Ideal
  (pt : propositional-truncations-exist)
  (fe : Fun-Ext)
  (pe : Prop-Ext)
  {𝓤 𝓣 𝓥 𝓦 : Universe}
 where

open import UF.Retracts
open import UF.Powerset
open PropositionalTruncation pt
open import UF.ImageAndSurjection pt
open import Posets.Poset fe
open PosetAxioms
open import Posets.FreeSupLattice pt

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Presentation.Type pt fe {𝓤} {𝓣} {𝓥} {𝓦}


-- TODO put this at the right place
Conjunction : (I : 𝓤' ̇) → (I → Ω 𝓥') → Ω (𝓤' ⊔ 𝓥')
pr₁ (Conjunction I ps) = ∀ i → ps i holds
pr₂ (Conjunction I ps) = Π-is-prop fe λ _ → holds-is-prop (ps _)

syntax Conjunction I (λ i → p) = ⋀ i ꞉ I , p

module C-Ideal
  (G : 𝓤 ̇)
  (_≲_ : G → G → 𝓣 ̇)
  (_◃_ : Cover-set G _≲_)
 where

  is-C-ideal : (G → Ω 𝓣') → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓣' ̇
  is-C-ideal ℑ = downward-closed × cover-closed
   where
    downward-closed = ∀ x y → x ≲ y
      → x ∈ ℑ → y ∈ ℑ
    cover-closed = ∀ I x (U : I → G) → (x ◃ U) holds
      → (∀ y → y ∈image U → y ∈ ℑ)
      → x ∈ ℑ

  being-C-ideal-is-prop : (ℑ : G → Ω 𝓣') → is-prop (is-C-ideal ℑ)
  being-C-ideal-is-prop ℑ =
   ×-is-prop
    (Π₄-is-prop fe λ _ _ _ _ → ∈-is-prop ℑ _)
    (Π₅-is-prop fe λ _ _ _ _ _ → ∈-is-prop ℑ _)

  intersection-is-C-ideal
   : {I : 𝓥' ̇} (ℑs : I → G → Ω 𝓣')
   → (∀ i → is-C-ideal (ℑs i))
   → is-C-ideal λ g → ⋀ i ꞉ _ , ℑs i g
  intersection-is-C-ideal ℑs ιs = dc , cc
   where
    dc = λ x y x≲y x∈ℑs i → pr₁ (ιs i) x y x≲y (x∈ℑs i)
    cc = λ J g U g◃U c i → pr₂ (ιs i) J g U g◃U λ g' g'∈U → c g' g'∈U i

  C-Idl : ∀ 𝓣' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓣' ⁺ ̇
  C-Idl 𝓣' = Σ (is-C-ideal {𝓣' = 𝓣'})

  module _ {𝓣' : Universe} where
   carrier : C-Idl 𝓣' → G → Ω 𝓣'
   carrier (ℑ , _) = ℑ

   C-ideality : (𝓘 : C-Idl 𝓣') → is-C-ideal (carrier 𝓘)
   C-ideality (_ , ι) = ι

   _⊑_ : C-Idl 𝓣' → C-Idl 𝓣' → 𝓤 ⊔ 𝓣' ̇
   (ℑ , _) ⊑ (𝔍 , _) = ℑ ⊆ 𝔍

  -- Characterize the equality of C-ideals
  to-C-ideal-＝ : (I J : C-Idl 𝓣') → carrier I ＝ carrier J → I ＝ J
  to-C-ideal-＝ (ℑ , _) (𝔍 , υ) p = to-Σ-＝
   (p , being-C-ideal-is-prop 𝔍 _ _)

  -- The impredicatively generated C-ideal from a set
  Generated : ∀ 𝓣' → (G → Ω 𝓥') → C-Idl (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓥' ⊔ 𝓣' ⁺)
  Generated 𝓣' S = (λ g → ⋀ ((ℑ , _) , _) ꞉  -- Too messy
   (Σ (ℑ , _) ꞉ C-Idl 𝓣' , S ⊆ ℑ), ℑ g) ,
   intersection-is-C-ideal (pr₁ ∘ pr₁) (pr₂ ∘ pr₁)

  Generated-contains : (S : G → Ω 𝓥') → S ⊆ carrier (Generated 𝓣' S)
  Generated-contains S g g∈S ((ℑ , ι), S⊆ℑ) = S⊆ℑ g g∈S

  -- Universal property
  private module SL = SupLattice

  -- C-Ideals form a suplattice
  -- TODO clean up fe and pe assumptions
  C-Idl-SupLattice : ∀ 𝓣' 𝓦' → SupLattice 𝓦' _ _
  SL.L (C-Idl-SupLattice 𝓣' 𝓦') =
   C-Idl (𝓤 ⊔ 𝓣 ⊔ (𝓥 ⁺) ⊔ 𝓦 ⊔ (𝓣' ⁺) ⊔ 𝓦')

  SL.L-is-set (C-Idl-SupLattice 𝓣' 𝓦') =
   Σ-is-set (Π-is-set fe λ _ → Ω-is-set fe pe) λ ℑ →
    props-are-sets (being-C-ideal-is-prop ℑ)

  SL._⊑_ (C-Idl-SupLattice 𝓣' 𝓦') (ℑ , ι) (𝔍 , υ) =
   ℑ ⊆ 𝔍

  SL.⊑-is-prop-valued (C-Idl-SupLattice 𝓣' 𝓦') _ 𝔍 =
   Π₂-is-prop fe λ g _ → holds-is-prop (carrier 𝔍 g)

  SL.⊑-is-reflexive (C-Idl-SupLattice 𝓣' 𝓦') _ _ =
   id

  SL.⊑-is-transitive (C-Idl-SupLattice 𝓣' 𝓦') _ _ _ ℑ⊆𝔍 𝔍⊆𝔎 u i∈ℑ =
   𝔍⊆𝔎 u (ℑ⊆𝔍 u i∈ℑ)

  SL.⊑-is-antisymmetric (C-Idl-SupLattice 𝓣' 𝓦') (ℑ , ι) (𝔍 , υ) ℑ⊆𝔍 𝔍⊆ℑ =
   to-C-ideal-＝ _ _ (dfunext fe (λ g → to-Σ-＝
    (pe (pr₂ (ℑ g)) (pr₂ (𝔍 g)) (ℑ⊆𝔍 g) (𝔍⊆ℑ g) ,
     being-prop-is-prop fe _ _)))
      -- This needs to-Ω-＝ somewhere in the library

  SL.⋁ (C-Idl-SupLattice 𝓣' 𝓦') ℑs =
   Generated 𝓣' λ g →
   (∃ i ꞉ _ , g ∈ carrier (ℑs i)) , ∃-is-prop

  SL.⋁-is-upperbound (C-Idl-SupLattice 𝓣' 𝓦') I i g g∈Ii ((𝔍 , _ , _) , ℑ⊆𝔍) =
   ℑ⊆𝔍 g ∣ i , g∈Ii ∣

  SL.⋁-is-lowerbound-of-upperbounds (C-Idl-SupLattice 𝓣' 𝓦')
    I (𝔍 , υ) Ii⊆𝔍 g g∈SupI = 𝔍'→𝔍 g (g∈SupI ((𝔍' , υ') ,
      λ g → ∥∥-rec (holds-is-prop (𝔍' g)) λ (i , e) → 𝔍→𝔍' g (Ii⊆𝔍 i g e)))
      where
        𝔍' : G → Ω 𝓣'
        𝔍' = {!   !}  -- requires resizing

        𝔍'→𝔍 : ∀ g → 𝔍' g holds → 𝔍 g holds
        𝔍'→𝔍 = {!   !}

        𝔍→𝔍' : ∀ g → 𝔍 g holds → 𝔍' g holds
        𝔍→𝔍' = {!   !}

        υ' : is-C-ideal 𝔍'
        υ' = {!   !}  -- deducible from propositional equivalence
\end{code}
