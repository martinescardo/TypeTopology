Tom de Jong, July 2024.

This file corresponds to the paper

   "Domain Theory in Univalent Foundations I:
    Directed complete posets and Scott’s D∞"
   Tom de Jong
   2024
   https://arxiv.org/abs/TODO

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt
open import UF.Subsingletons
open import UF.PropTrunc

module DomainTheory.Part-I
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import MLTT.Spartan

open import UF.Base
open import UF.Equiv
open import UF.Powerset-MultiUniverse
open import UF.Sets
open import UF.Size hiding (is-locally-small)
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Univalence

open import OrderedTypes.Poset fe

{- Section 2 -}

Definition-2-1 : (𝓤 : Universe) (X : 𝓥 ̇  ) → 𝓤 ⁺ ⊔ 𝓥 ̇
Definition-2-1 𝓤 X = X is 𝓤 small

Definition-2-2 : (𝓤 : Universe) → 𝓤 ⁺ ̇
Definition-2-2 𝓤 = Ω 𝓤

Definition-2-3 : (𝓥 : Universe) (X : 𝓤 ̇  ) → 𝓥 ⁺ ⊔ 𝓤 ̇
Definition-2-3 𝓥 X = 𝓟 {𝓥} X

Definition-2-4 : (𝓥 : Universe) (X : 𝓤 ̇  )
               → (X → 𝓟 {𝓥} X → 𝓥 ̇  )
               × (𝓟 {𝓥} X → 𝓟 {𝓥} X → 𝓥 ⊔ 𝓤 ̇  )
Definition-2-4 𝓥 X = _∈_ , _⊆_

{- Section 3 -}

module _
        (P : 𝓤 ̇  ) (_⊑_ : P → P → 𝓣 ̇  )
       where

 open PosetAxioms

 Definition-3-1 : 𝓤 ⊔ 𝓣 ̇
 Definition-3-1 = is-prop-valued _⊑_
                × is-reflexive _⊑_
                × is-transitive _⊑_

 Definition-3-2 : 𝓤 ⊔ 𝓣 ̇
 Definition-3-2 = Definition-3-1 × is-antisymmetric _⊑_

 Lemma-3-3 : is-prop-valued _⊑_
           → is-reflexive _⊑_
           → is-antisymmetric _⊑_
           → is-set P
 Lemma-3-3 = posets-are-sets _⊑_

 module _ (𝓥 : Universe) where
  open import DomainTheory.Basics.Dcpo pt fe 𝓥

  Definition-3-4 : {I : 𝓥 ̇  } → (I → P) → (𝓥 ⊔ 𝓣 ̇  ) × (𝓥 ⊔ 𝓣 ̇  )
  Definition-3-4 {I} α = is-semidirected _⊑_ α , is-directed _⊑_ α

  Remark-3-5 : {I : 𝓥 ̇  } (α : I → P)
             → is-directed _⊑_ α
             ＝ ∥ I ∥ × ((i j : I) → ∥ Σ k ꞉ I , (α i ⊑ α k) × (α j ⊑ α k) ∥)
  Remark-3-5 α = refl

  Definition-3-6 : {I : 𝓥 ̇  } → P → (I → P) → (𝓥 ⊔ 𝓣 ̇  ) × (𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇  )
  Definition-3-6 {I} x α = (is-upperbound _⊑_ x α) , is-sup _⊑_ x α

  Definition-3-6-ad : poset-axioms _⊑_
                    → {I : 𝓥 ̇  } (α : I → P)
                    → {x y : P} → is-sup _⊑_ x α → is-sup _⊑_ y α → x ＝ y
  Definition-3-6-ad pa {I} α = sups-are-unique _⊑_ pa α

  Definition-3-7 : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  Definition-3-7 = is-directed-complete _⊑_

  Definition-3-7-ad : (𝓓 : DCPO {𝓤} {𝓣}) {I : 𝓥 ̇}
                      {α : I → ⟨ 𝓓 ⟩} → is-Directed 𝓓 α → ⟨ 𝓓 ⟩
  Definition-3-7-ad = ∐

  Remark-3-8 : poset-axioms _⊑_
             → {I : 𝓥 ̇  } (α : I → P)
             → is-prop (has-sup _⊑_ α)
  Remark-3-8 = having-sup-is-prop _⊑_

module _ (𝓥 : Universe) where
 open import DomainTheory.Basics.Dcpo pt fe 𝓥

 Definition-3-9 : {𝓤 𝓣 : Universe} → (𝓤 ⊔ 𝓥 ⊔ 𝓣) ⁺ ̇
 Definition-3-9 {𝓤} {𝓣} = DCPO {𝓤} {𝓣}

 -- Remark-3-10: No formalisable content.

 open import DomainTheory.Basics.Pointed pt fe 𝓥
 open import DomainTheory.Basics.Miscelanea pt fe 𝓥

 Definition-3-11 : {𝓤 𝓣 : Universe} → (𝓥 ⊔ 𝓤 ⊔ 𝓣) ⁺ ̇
 Definition-3-11 {𝓤} {𝓣} = DCPO⊥ {𝓤} {𝓣}

 Definition-3-12 : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 Definition-3-12 𝓓 = is-locally-small' 𝓓

 Lemma-3-13 : (𝓓 : DCPO {𝓤} {𝓣})
            → is-locally-small 𝓓 ≃ is-locally-small' 𝓓
 Lemma-3-13 𝓓 = local-smallness-equivalent-definitions 𝓓

 open import DomainTheory.Examples.Omega pt fe pe 𝓥

 Example-3-14 : DCPO⊥ {𝓥 ⁺} {𝓥}
 Example-3-14 = Ω-DCPO⊥

 module _
         (X : 𝓤 ̇  )
         (X-is-set : is-set X)
        where

  open import DomainTheory.Examples.Powerset pt fe pe X-is-set

  Example-3-15 :  DCPO⊥ {𝓥 ⁺ ⊔ 𝓤} {𝓥 ⊔ 𝓤}
  Example-3-15 = generalized-𝓟-DCPO⊥ 𝓥

 module _
         (X : 𝓥 ̇  )
         (X-is-set : is-set X)
        where

  open import DomainTheory.Examples.Powerset pt fe pe X-is-set

  Example-3-15-ad :  DCPO⊥ {𝓥 ⁺} {𝓥}
  Example-3-15-ad = 𝓟-DCPO⊥

 Proposition-3-16 : (𝓓 : DCPO {𝓤} {𝓣})
                  → is-ω-complete (underlying-order 𝓓)
 Proposition-3-16 = dcpos-are-ω-complete

{- Section 4 -}

 Definition-4-1 : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
                → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
 Definition-4-1 𝓓 𝓔 f = is-continuous 𝓓 𝓔 f

 -- Remark-4-2: Note that the parameter 𝓥 in the type DCPO is fixed.

 module _
         (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
        where

  Lemma-4-3 : (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
            → is-prop (is-continuous 𝓓 𝓔 f)
  Lemma-4-3 = being-continuous-is-prop 𝓓 𝓔

  Lemma-4-3-ad : (f g : DCPO[ 𝓓 , 𝓔 ])
               → underlying-function 𝓓 𝓔 f ＝ underlying-function 𝓓 𝓔 g
               → f ＝ g
  Lemma-4-3-ad f g e = to-continuous-function-＝ 𝓓 𝓔 (happly e)

  Lemma-4-4 : (f : DCPO[ 𝓓 , 𝓔 ])
            → is-monotone 𝓓 𝓔 [ 𝓓 , 𝓔 ]⟨ f ⟩
  Lemma-4-4 = monotone-if-continuous 𝓓 𝓔

  Lemma-4-5 : {f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩} → is-monotone 𝓓 𝓔 f
            → {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
            → is-Directed 𝓓 α
            → is-Directed 𝓔 (f ∘ α)
  Lemma-4-5 = image-is-directed 𝓓 𝓔

  Lemma-4-6 : (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
              (δ : is-Directed 𝓓 α)
            → [ 𝓓 , 𝓔 ]⟨ f ⟩ (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩
              ∐ 𝓔 (image-is-directed' 𝓓 𝓔 f δ)
  Lemma-4-6 = continuous-∐-⊑ 𝓓 𝓔

  Lemma-4-6-ad : (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) (m : is-monotone 𝓓 𝓔 f)
               → ((I : 𝓥 ̇ ) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                     → f (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ ∐ 𝓔 (image-is-directed 𝓓 𝓔 m δ))
               → is-continuous 𝓓 𝓔 f
  Lemma-4-6-ad = continuity-criterion 𝓓 𝓔

 Remark-4-7 : Σ 𝓓 ꞉ DCPO {𝓥 ⁺} {𝓥} ,
              Σ f ꞉ (⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩) , ¬ is-continuous 𝓓 𝓓 f
 Remark-4-7 = Ω-DCPO , ν , II
  where
   ν : Ω 𝓥 → Ω 𝓥
   ν P = ¬ (P holds) , negations-are-props fe
   I : ¬ (is-monotone Ω-DCPO Ω-DCPO ν)
   I m = m (𝟘 , 𝟘-is-prop) (𝟙 , 𝟙-is-prop) (λ _ → ⋆) 𝟘-elim ⋆
   II : ¬ (is-continuous Ω-DCPO Ω-DCPO ν)
   II c = I (monotone-if-continuous Ω-DCPO Ω-DCPO (ν , c))

 Definition-4-8 : (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
                → (⟪ 𝓓 ⟫ → ⟪ 𝓔 ⟫) → 𝓤' ̇
 Definition-4-8 𝓓 𝓔 f = is-strict 𝓓 𝓔 f

 Lemma-4-9 : (𝓓 : DCPO⊥ {𝓤} {𝓣})
             {I : 𝓥 ̇  } {α : I → ⟪ 𝓓 ⟫}
           → is-semidirected (underlying-order (𝓓 ⁻)) α
           → has-sup (underlying-order (𝓓 ⁻)) α
 Lemma-4-9 = semidirected-complete-if-pointed

 Lemma-4-9-ad₁ : (𝓓 : DCPO {𝓤} {𝓣})
               → ({I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
                     → is-semidirected (underlying-order 𝓓) α
                     → has-sup (underlying-order 𝓓) α)
               → has-least (underlying-order 𝓓)
 Lemma-4-9-ad₁ = pointed-if-semidirected-complete

 Lemma-4-9-ad₂ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
                 (f : ⟪ 𝓓 ⟫ → ⟪ 𝓔 ⟫)
               → is-continuous (𝓓 ⁻) (𝓔 ⁻) f
               → is-strict 𝓓 𝓔 f
               → {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
               → (σ : is-semidirected (underlying-order (𝓓 ⁻)) α)
               → is-sup (underlying-order (𝓔 ⁻)) (f (∐ˢᵈ 𝓓 σ)) (f ∘ α)
 Lemma-4-9-ad₂ = preserves-semidirected-sups-if-continuous-and-strict

 Proposition-4-10-i : (𝓓 : DCPO {𝓤} {𝓣}) → is-continuous 𝓓 𝓓 id
 Proposition-4-10-i = id-is-continuous

 Proposition-4-10-i-ad : (𝓓 : DCPO⊥ {𝓤} {𝓣}) → is-strict 𝓓 𝓓 id
 Proposition-4-10-i-ad 𝓓 = refl

 module _
         (𝓓 : DCPO {𝓤} {𝓣})
         (𝓔 : DCPO {𝓤'} {𝓣'})
        where

  Proposition-4-10-ii : (y : ⟨ 𝓔 ⟩) → is-continuous 𝓓 𝓔 (λ _ → y)
  Proposition-4-10-ii _ = constant-functions-are-continuous 𝓓 𝓔

  Proposition-4-10-iii : {𝓤'' 𝓣'' : Universe}
                         (𝓔' : DCPO {𝓤''} {𝓣''})
                         (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) (g : ⟨ 𝓔 ⟩ → ⟨ 𝓔' ⟩)
                       → is-continuous 𝓓 𝓔 f
                       → is-continuous 𝓔 𝓔' g
                       → is-continuous 𝓓 𝓔' (g ∘ f)
  Proposition-4-10-iii = ∘-is-continuous 𝓓 𝓔

 Proposition-4-10-iii-ad : {𝓤'' 𝓣'' : Universe}
                           (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
                           (𝓔' : DCPO⊥ {𝓤''} {𝓣''})
                           (f : ⟪ 𝓓 ⟫ → ⟪ 𝓔 ⟫) (g : ⟪ 𝓔 ⟫ → ⟪ 𝓔' ⟫)
                         → is-strict 𝓓 𝓔 f
                         → is-strict 𝓔 𝓔' g
                         → is-strict 𝓓 𝓔' (g ∘ f)
 Proposition-4-10-iii-ad = ∘-is-strict

 Definition-4-11 : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'} → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
 Definition-4-11 𝓓 𝓔 = 𝓓 ≃ᵈᶜᵖᵒ 𝓔

 Lemma-4-12 : (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
            → (𝓓 ⁻) ≃ᵈᶜᵖᵒ (𝓔 ⁻) → 𝓓 ≃ᵈᶜᵖᵒ⊥ 𝓔
 Lemma-4-12 = ≃ᵈᶜᵖᵒ-to-≃ᵈᶜᵖᵒ⊥

 Definition-4-13 : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'} → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
 Definition-4-13 𝓓 𝓔 = 𝓓 continuous-retract-of 𝓔

 Lemma-4-14 : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
            → 𝓓 continuous-retract-of 𝓔
            → is-locally-small 𝓔
            → is-locally-small 𝓓
 Lemma-4-14 = local-smallness-preserved-by-continuous-retract

{- Section 5 -}

module _ where
 open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
 open import DomainTheory.Basics.Miscelanea pt fe 𝓤₀
 open import DomainTheory.Taboos.ClassicalLiftingOfNaturalNumbers pt fe
 open import Taboos.LPO (λ 𝓤 𝓥 → fe)

 Proposition-5-1 : is-ω-complete _⊑_ → LPO
 Proposition-5-1 = ℕ⊥-is-ω-complete-gives-LPO

 Proposition-5-1-ad : is-directed-complete _⊑_ → LPO
 Proposition-5-1-ad = ℕ⊥-is-directed-complete-gives-LPO

 -- Remark-5-2: No formalisable content.


module _ (𝓥 : Universe) where

 open import Lifting.Construction 𝓥 renaming (⊥ to ⊥𝓛)
 open import Lifting.IdentityViaSIP 𝓥
 open import Lifting.Monad 𝓥
 open import Lifting.Miscelanea-PropExt-FunExt 𝓥 pe fe

 Definition-5-3 : (X : 𝓤 ̇  ) → 𝓥 ⁺ ⊔ 𝓤 ̇
 Definition-5-3 X = 𝓛 X

 Definition-5-4 : {X : 𝓤 ̇  } → X → 𝓛 X
 Definition-5-4 = η

 Definition-5-5 : {X : 𝓤 ̇  } → 𝓛 X
 Definition-5-5 = ⊥𝓛

 Definition-5-6 : {X : 𝓤 ̇  } → 𝓛 X → Ω 𝓥
 Definition-5-6 l = is-defined l , being-defined-is-prop l

 Definition-5-6-ad : {X : 𝓤 ̇  } (l : 𝓛 X) → is-defined l → X
 Definition-5-6-ad = value

 open import UF.ClassicalLogic
 Proposition-5-7 : (X : 𝓤 ̇) → EM 𝓥 → 𝓛 X ≃ 𝟙 + X
 Proposition-5-7 = EM-gives-classical-lifting

 Proposition-5-7-ad : ((X : 𝓤 ̇) → 𝓛 X ≃ 𝟙 + X) → EM 𝓥
 Proposition-5-7-ad = classical-lifting-gives-EM

 module _ {X : 𝓤 ̇  } where

  Lemma-5-8 : {l m : 𝓛 X} → (l ⋍ m → l ＝ m) × (l ＝ m → l ⋍ m)
  Lemma-5-8 = ⋍-to-＝ , ＝-to-⋍

  Remark-5-9 : is-univalent 𝓥 → (l m : 𝓛 X)
             → (l ＝ m) ≃ (l ⋍· m)
  Remark-5-9 ua = 𝓛-Id· ua fe

  Theorem-5-10 : {Y : 𝓦 ̇  } → (f : X → 𝓛 Y) → 𝓛 X → 𝓛 Y
  Theorem-5-10 f = f ♯

  Theorem-5-10-i : η ♯ ∼ id {_} {𝓛 X}
  Theorem-5-10-i l = ⋍-to-＝ (Kleisli-Law₀ l)

  Theorem-5-10-ii : {Y : 𝓦 ̇  } (f : X → 𝓛 Y)
                  → f ♯ ∘ η ∼ f
  Theorem-5-10-ii f l = ⋍-to-＝ (Kleisli-Law₁ f l)

  Theorem-5-10-iii : {Y : 𝓦 ̇  } {Z : 𝓣 ̇  }
                     (f : X → 𝓛 Y) (g : Y → 𝓛 Z)
                   → (g ♯ ∘ f) ♯ ∼ g ♯ ∘ f ♯
  Theorem-5-10-iii f g l = (⋍-to-＝ (Kleisli-Law₂ f g l)) ⁻¹

  Remark-5-11 : type-of (𝓛 X) ＝ 𝓥 ⁺ ⊔ 𝓤 ̇
  Remark-5-11 = refl

  -- Remark-5-12: Note that we did not to assume that X is a set in the above.

  Definition-5-13 : {Y : 𝓥 ̇  }
                  → (X → Y) → 𝓛 X → 𝓛 Y
  Definition-5-13 f = 𝓛̇ f

  Definition-5-13-ad : {Y : 𝓥 ̇  } (f : X → Y)
                     → (η ∘ f) ♯ ∼ 𝓛̇ f
  Definition-5-13-ad f = 𝓛̇-♯-∼ f

  Proposition-5-14 : 𝓛 X → 𝓛 X → 𝓥 ⁺ ⊔ 𝓤 ̇
  Proposition-5-14 = _⊑'_

  Proposition-5-14-ad₁ : (is-set X → {l m : 𝓛 X} → is-prop (l ⊑' m))
                       × ({l : 𝓛 X} → l ⊑' l)
                       × ({l m n : 𝓛 X} → l ⊑' m → m ⊑' n → l ⊑' n)
                       × ({l m : 𝓛 X} → l ⊑' m → m ⊑' l → l ＝ m)
  Proposition-5-14-ad₁ = ⊑'-prop-valued ,
                         ⊑'-is-reflexive ,
                         ⊑'-is-transitive ,
                         ⊑'-is-antisymmetric

  open import Lifting.UnivalentPrecategory 𝓥 X
  Proposition-5-14-ad₂ : {l m : 𝓛 X} → (l ⊑ m → l ⊑' m) × (l ⊑' m → l ⊑ m)
  Proposition-5-14-ad₂ = ⊑-to-⊑' , ⊑'-to-⊑

 open import DomainTheory.Basics.Dcpo pt fe 𝓥
 open import DomainTheory.Basics.Pointed pt fe 𝓥
 open import DomainTheory.Basics.Miscelanea pt fe 𝓥

 module _ where
  open import DomainTheory.Lifting.LiftingSet pt fe 𝓥 pe

  Proposition-5-15 : {X : 𝓤 ̇  } → is-set X → DCPO⊥ {𝓥 ⁺ ⊔ 𝓤} {𝓥 ⁺ ⊔ 𝓤}
  Proposition-5-15 = 𝓛-DCPO⊥

  Proposition-5-15-ad : {X : 𝓥 ̇  } (s : is-set X) → is-locally-small (𝓛-DCPO s)
  Proposition-5-15-ad {X} s =
   record { _⊑ₛ_ = _⊑_ ;
            ⊑ₛ-≃-⊑ = λ {l m} → logically-equivalent-props-are-equivalent
                                (⊑-prop-valued fe fe s l m)
                                (⊑'-prop-valued s)
                                ⊑-to-⊑'
                                ⊑'-to-⊑ }
   where
    open import Lifting.UnivalentPrecategory 𝓥 X

 module _
         {X : 𝓤 ̇  }
         (s : is-set X)
        where

  open import DomainTheory.Lifting.LiftingSet pt fe 𝓥 pe


  Proposition-5-16 : {Y : 𝓦 ̇  } (t : is-set Y)
                     (f : X → 𝓛 Y)
                  → is-continuous (𝓛-DCPO s) (𝓛-DCPO t) (f ♯)
  Proposition-5-16 t f = ♯-is-continuous s t f

  Lemma-5-17 : (l : 𝓛 X)
             → l ＝ ∐ˢˢ (𝓛-DCPO⊥ s) (η ∘ value l) (being-defined-is-prop l)
  Lemma-5-17 = all-partial-elements-are-subsingleton-sups s

  Theorem-5-18 : (𝓓 : DCPO⊥ {𝓤'} {𝓣'}) → (f : X → ⟪ 𝓓 ⟫)
               → ∃! f̅ ꞉ (𝓛 X → ⟪ 𝓓 ⟫) , is-continuous (𝓛-DCPO s) (𝓓 ⁻) f̅
                                       × is-strict (𝓛-DCPO⊥ s) 𝓓 f̅
                                       × (f̅ ∘ η ＝ f)
  Theorem-5-18 = let open lifting-is-free-pointed-dcpo-on-set s in
                 𝓛-gives-the-free-pointed-dcpo-on-a-set

 module _
         (𝓓 : DCPO {𝓤} {𝓣})
        where

  open import DomainTheory.Lifting.LiftingDcpo pt fe 𝓥 pe
  open freely-add-⊥ 𝓓

  Proposition-5-19 : 𝓛D → 𝓛D → 𝓥 ⊔ 𝓣 ̇
  Proposition-5-19 = _⊑_

  Proposition-5-19-ad : ((k l : 𝓛D) → is-prop (k ⊑ l))
                      × ((l : 𝓛D) → l ⊑ l)
                      × ((k l m : 𝓛D) → k ⊑ l → l ⊑ m → k ⊑ m)
                      × ((k l : 𝓛D) → k ⊑ l → l ⊑ k → k ＝ l)
  Proposition-5-19-ad = ⊑-is-prop-valued ,
                        ⊑-is-reflexive ,
                        ⊑-is-transitive ,
                        ⊑-is-antisymmetric

  Proposition-5-20 : DCPO⊥ {𝓥 ⁺ ⊔ 𝓤} {𝓥 ⊔ 𝓣}
  Proposition-5-20 = 𝓛-DCPO⊥

  Proposition-5-20-ad : is-locally-small 𝓓 → is-locally-small 𝓛-DCPO
  Proposition-5-20-ad = 𝓛-DCPO-is-locally-small

  Theorem-5-21 : (𝓔 : DCPO⊥ {𝓤'} {𝓣'}) (f : ⟨ 𝓓 ⟩ → ⟪ 𝓔 ⟫)
               → is-continuous 𝓓 (𝓔 ⁻) f
               → ∃! f̅ ꞉ (𝓛D → ⟪ 𝓔 ⟫) , is-continuous (𝓛-DCPO⊥ ⁻) (𝓔 ⁻) f̅
                                      × is-strict 𝓛-DCPO⊥ 𝓔 f̅ × (f̅ ∘ η ＝ f)
  Theorem-5-21 = 𝓛-gives-the-free-pointed-dcpo-on-a-dcpo

{- Section 6 -}

module _ (𝓥 : Universe) where

 open import DomainTheory.Basics.Curry pt fe 𝓥
 open import DomainTheory.Basics.Dcpo pt fe 𝓥
 open import DomainTheory.Basics.FunctionComposition pt fe 𝓥
 open import DomainTheory.Basics.Pointed pt fe 𝓥
 open import DomainTheory.Basics.Products pt fe
 open DcpoProductsGeneral 𝓥
 open import DomainTheory.Basics.ProductsContinuity pt fe 𝓥
 open import DomainTheory.Basics.Exponential pt fe 𝓥

 Definition-6-1 : DCPO {𝓤} {𝓣}
                → DCPO {𝓤'} {𝓣'}
                → DCPO {𝓤 ⊔ 𝓤'} {𝓣 ⊔ 𝓣'}
 Definition-6-1 𝓓 𝓔 = 𝓓 ×ᵈᶜᵖᵒ 𝓔

 Definition-6-1-ad : DCPO⊥ {𝓤} {𝓣}
                   → DCPO⊥ {𝓤'} {𝓣'}
                   → DCPO⊥ {𝓤 ⊔ 𝓤'} {𝓣 ⊔ 𝓣'}
 Definition-6-1-ad 𝓓 𝓔 = 𝓓 ×ᵈᶜᵖᵒ⊥ 𝓔

 Remark-6-2 : DCPO {𝓤} {𝓣}
            → DCPO {𝓤} {𝓣}
            → DCPO {𝓤} {𝓣}
 Remark-6-2 𝓓 𝓔 = 𝓓 ×ᵈᶜᵖᵒ 𝓔

 Proposition-6-3 : {!!} -- TODO
 Proposition-6-3 = {!!}

 module _
         (𝓓₁ : DCPO {𝓤} {𝓤'})
         (𝓓₂ : DCPO {𝓣} {𝓣'})
         (𝓔 : DCPO {𝓦} {𝓦'})
         (f : ⟨ 𝓓₁ ×ᵈᶜᵖᵒ 𝓓₂ ⟩ → ⟨ 𝓔 ⟩)
        where

  Lemma-6-4 : ((e : ⟨ 𝓓₂ ⟩) → is-continuous 𝓓₁ 𝓔 (λ d → f (d , e)))
            → ((d : ⟨ 𝓓₁ ⟩) → is-continuous 𝓓₂ 𝓔 (λ e → f (d , e)))
            → is-continuous (𝓓₁ ×ᵈᶜᵖᵒ 𝓓₂) 𝓔 f
  Lemma-6-4 = continuous-in-arguments→continuous 𝓓₁ 𝓓₂ 𝓔 f

  Lemma-6-4-ad : is-continuous (𝓓₁ ×ᵈᶜᵖᵒ 𝓓₂) 𝓔 f
               → ((e : ⟨ 𝓓₂ ⟩) → is-continuous 𝓓₁ 𝓔 (λ d → f (d , e)))
               × ((d : ⟨ 𝓓₁ ⟩) → is-continuous 𝓓₂ 𝓔 (λ e → f (d , e)))
  Lemma-6-4-ad c =
   (λ e → pr₂ (continuous→continuous-in-pr₁ 𝓓₁ 𝓓₂ 𝓔 (f , c) e)) ,
   (λ d → pr₂ (continuous→continuous-in-pr₂ 𝓓₁ 𝓓₂ 𝓔 (f , c) d))

 Definition-6-5 : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                → DCPO {𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓤' ⊔ 𝓣 ⊔ 𝓣'} {𝓤 ⊔ 𝓣'}
 Definition-6-5 𝓓 𝓔 = 𝓓 ⟹ᵈᶜᵖᵒ 𝓔

 Definition-6-5-ad : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
                   → DCPO⊥ {𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓤' ⊔ 𝓣 ⊔ 𝓣'} {𝓤 ⊔ 𝓣'}
 Definition-6-5-ad 𝓓 𝓔 = 𝓓 ⟹ᵈᶜᵖᵒ⊥' 𝓔

 Remark-6-6 : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
            → type-of (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ＝ DCPO {𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓤' ⊔ 𝓣 ⊔ 𝓣'} {𝓤 ⊔ 𝓣'}
 Remark-6-6 𝓓 𝓔 = refl

 Proposition-6-7 : {!!} -- TODO
 Proposition-6-7 = {!!}

 open import DomainTheory.Basics.LeastFixedPoint pt fe 𝓥

 module _ (𝓓 : DCPO⊥ {𝓤} {𝓣}) where

  Theorem-6-8 : DCPO[ ((𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻) , (𝓓 ⁻) ]
  Theorem-6-8 = μ 𝓓

  Theorem-6-8-i : (f : DCPO[ 𝓓 ⁻ , 𝓓 ⁻ ])
                → [ (𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻ , 𝓓 ⁻ ]⟨ μ 𝓓 ⟩ f
                ＝ [ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ f ⟩ ([ (𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻ , 𝓓 ⁻ ]⟨ μ 𝓓 ⟩ f)
  Theorem-6-8-i = μ-gives-a-fixed-point 𝓓

  Theorem-6-8-ii : (f : DCPO[ (𝓓 ⁻) , (𝓓 ⁻) ])
                   (x : ⟪ 𝓓 ⟫)
                 → [ 𝓓 ⁻ , 𝓓 ⁻ ]⟨ f ⟩ x  ⊑⟪ 𝓓 ⟫ x
                 → [ (𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓) ⁻ , 𝓓 ⁻ ]⟨ μ 𝓓 ⟩ f ⊑⟪ 𝓓 ⟫ x
  Theorem-6-8-ii = μ-gives-lowerbound-of-fixed-points 𝓓

{- Section 7 -}

\end{code}