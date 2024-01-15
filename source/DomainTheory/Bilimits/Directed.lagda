Tom de Jong, 5 May 2020 - 10 May 2020

We construct bilimits of diagrams indexed by directed posets in the category of
dcpos as objects and embedding-projection pairs as morphisms.

This formalization is based on Scott's "Continuous lattices"
(doi:10.1007/BFB0073967), specifically pages 124--126, but generalizes it from
ℕ-indexed diagrams to diagrams indexed by a directed poset.

We specialize to ℕ-indexed diagrams in Sequential.lagda.

We also prove that taking the bilmit preserves local smallness and that it is
closed under structural continuity/algebraicity and having a small (compact) basis.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

\end{code}

We use the flag --lossy-unification to speed up the type-checking.

This flag was kindly implemented by Andrea Vezzosi upon request.

Documentation for the flag (written by Andrea Vezzosi) can be found here:
https://agda.readthedocs.io/en/latest/language/lossy-unification.html

The most important takeaway from the documentation is that the flag is sound:

  "[...] if Agda accepts code with the flag enabled it should also accept it
  without the flag (with enough resources, and possibly needing extra type
  annotations)."

A related issue (originally opened by Wolfram Kahl in 2015) can be found here:
https://github.com/agda/agda/issues/1625

\begin{code}

open import MLTT.Spartan hiding (J)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties

module DomainTheory.Bilimits.Directed
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe)
        (𝓤 𝓣 : Universe)
       where

open PropositionalTruncation pt

open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Hedberg
open import UF.ImageAndSurjection pt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import OrderedTypes.Poset fe

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Exponential pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.WayBelow pt fe 𝓥

open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓥
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓥

module Diagram
        {I : 𝓥 ̇ }
        (_⊑_ : I → I → 𝓦 ̇ )
        (⊑-refl : {i : I} → i ⊑ i)
        (⊑-trans : {i j k : I} → i ⊑ j → j ⊑ k → i ⊑ k)
        (⊑-prop-valued : (i j : I) → is-prop (i ⊑ j))
        (I-inhabited : ∥ I ∥)
        (I-semidirected : (i j : I) → ∃ k ꞉ I , i ⊑ k × j ⊑ k)
        (𝓓 : I → DCPO {𝓤} {𝓣})
        (ε : {i j : I} → i ⊑ j → ⟨ 𝓓 i ⟩ → ⟨ 𝓓 j ⟩)
        (π : {i j : I} → i ⊑ j → ⟨ 𝓓 j ⟩ → ⟨ 𝓓 i ⟩)
        (επ-deflation : {i j : I} (l : i ⊑ j) (x : ⟨ 𝓓 j ⟩)
                      → ε l (π l x) ⊑⟨ 𝓓 j ⟩ x )
        (ε-section-of-π : {i j : I} (l : i ⊑ j) → π l ∘ ε l ∼ id )
        (ε-is-continuous : {i j : I} (l : i ⊑ j)
                         → is-continuous (𝓓 i) (𝓓 j) (ε {i} {j} l))
        (π-is-continuous : {i j : I} (l : i ⊑ j)
                         → is-continuous (𝓓 j) (𝓓 i) (π {i} {j} l))
        (ε-id : (i : I ) → ε (⊑-refl {i}) ∼ id)
        (π-id : (i : I ) → π (⊑-refl {i}) ∼ id)
        (ε-comp : {i j k : I} (l : i ⊑ j) (m : j ⊑ k)
                → ε m ∘ ε l ∼ ε (⊑-trans l m))
        (π-comp : {i j k : I} (l : i ⊑ j) (m : j ⊑ k)
                → π l ∘ π m ∼ π (⊑-trans l m))
       where

 𝓓∞-carrier : 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 𝓓∞-carrier =
  Σ σ ꞉ ((i : I) → ⟨ 𝓓 i ⟩) , ((i j : I) (l : i ⊑ j) → π l (σ j) ＝ σ i)

 ⦅_⦆ : 𝓓∞-carrier → (i : I) → ⟨ 𝓓 i ⟩
 ⦅_⦆ = pr₁

 π-equality : (σ : 𝓓∞-carrier) {i j : I} (l : i ⊑ j) → π l (⦅ σ ⦆ j) ＝ ⦅ σ ⦆ i
 π-equality σ {i} {j} l = pr₂ σ i j l

 to-𝓓∞-＝ : {σ τ : 𝓓∞-carrier} → ((i : I) → ⦅ σ ⦆ i ＝ ⦅ τ ⦆ i) → σ ＝ τ
 to-𝓓∞-＝ h =
  to-subtype-＝ (λ σ → Π₃-is-prop fe (λ i j l → sethood (𝓓 i))) (dfunext fe h)

 family-at-ith-component : {𝓐 : 𝓥 ̇ } (α : 𝓐 → 𝓓∞-carrier) (i : I) → 𝓐 → ⟨ 𝓓 i ⟩
 family-at-ith-component α i a = ⦅ α a ⦆ i

 _≼_ : 𝓓∞-carrier → 𝓓∞-carrier → 𝓥 ⊔ 𝓣 ̇
 σ ≼ τ = (i : I) → ⦅ σ ⦆ i ⊑⟨ 𝓓 i ⟩ ⦅ τ ⦆ i

 family-at-ith-component-is-directed : {𝓐 : 𝓥 ̇ } (α : 𝓐 → 𝓓∞-carrier)
                                       (δ : is-directed _≼_ α) (i : I)
                                     → is-Directed (𝓓 i)
                                        (family-at-ith-component α i)
 family-at-ith-component-is-directed {𝓐} α δ i =
  (inhabited-if-directed _≼_ α δ) , γ
   where
    β : (i : I) → 𝓐 → ⟨ 𝓓 i ⟩
    β = family-at-ith-component α
    γ : is-semidirected (underlying-order (𝓓 i)) (β i)
    γ a₁ a₂ = ∥∥-functor g (semidirected-if-directed _≼_ α δ a₁ a₂)
     where
      g : (Σ a ꞉ 𝓐 , (α a₁ ≼ α a) × (α a₂ ≼ α a))
        → (Σ a ꞉ 𝓐 , (β i a₁ ⊑⟨ 𝓓 i ⟩ β i a) × (β i a₂ ⊑⟨ 𝓓 i ⟩ β i a))
      g (a , l₁ , l₂) = a , l₁ i , l₂ i

 𝓓∞-∐ : {𝓐 : 𝓥 ̇ } (α : 𝓐 → 𝓓∞-carrier) (δ : is-directed _≼_ α) → 𝓓∞-carrier
 𝓓∞-∐ {𝓐} α δ = (λ i → ∐ (𝓓 i) (δ' i)) , φ
  where
   β : (i : I) → 𝓐 → ⟨ 𝓓 i ⟩
   β = family-at-ith-component α
   δ' : (i : I) → is-Directed (𝓓 i) (β i)
   δ' = family-at-ith-component-is-directed α δ
   φ : (i j : I) (l : i ⊑ j) → π l (∐ (𝓓 j) (δ' j)) ＝ ∐ (𝓓 i) (δ' i)
   φ i j l = π l (∐ (𝓓 j) (δ' j))       ＝⟨ eq₁ ⟩
             ∐ (𝓓 i) {𝓐} {π l ∘ β j} δ₁ ＝⟨ eq₂ ⟩
             ∐ (𝓓 i) {𝓐} {β i} δ₂       ＝⟨ eq₃ ⟩
             ∐ (𝓓 i) {𝓐} {β i} (δ' i)   ∎
    where
     δ₁ : is-Directed (𝓓 i) (π l ∘ β j)
     δ₁ = image-is-directed' (𝓓 j) (𝓓 i) ((π l) , (π-is-continuous l)) (δ' j)
     h : π l ∘ β j ＝ β i
     h = dfunext fe (λ a → π-equality (α a) l)
     δ₂ : is-Directed (𝓓 i) (β i)
     δ₂ = transport (is-Directed (𝓓 i)) h δ₁
     eq₁ = continuous-∐-＝ (𝓓 j) (𝓓 i) ((π l) , (π-is-continuous l)) (δ' j)
     eq₂ = ∐-family-＝ (𝓓 i) h δ₁
     eq₃ = ∐-independent-of-directedness-witness (𝓓 i) δ₂ (δ' i)

 𝓓∞ : DCPO {𝓥 ⊔ 𝓤 ⊔ 𝓦} {𝓥 ⊔ 𝓣}
 𝓓∞ = (𝓓∞-carrier , _≼_ , pa , dc)
  where
   pa : PosetAxioms.poset-axioms _≼_
   pa = sl , pv , r , t , a
    where
     open PosetAxioms {𝓥 ⊔ 𝓤 ⊔ 𝓦} {𝓥 ⊔ 𝓣} {𝓓∞-carrier} _≼_
     sl : is-set 𝓓∞-carrier
     sl = subsets-of-sets-are-sets _ _
           (Π-is-set fe (λ i → sethood (𝓓 i)))
           (Π₃-is-prop fe (λ i j l → sethood (𝓓 i)))
     pv : is-prop-valued
     pv σ τ = Π-is-prop fe (λ i → prop-valuedness (𝓓 i) (⦅ σ ⦆ i) (⦅ τ ⦆ i))
     r : is-reflexive
     r σ i = reflexivity (𝓓 i) (⦅ σ ⦆ i)
     t : is-transitive
     t σ τ ρ l k i = transitivity (𝓓 i) (⦅ σ ⦆ i) (⦅ τ ⦆ i) (⦅ ρ ⦆ i) (l i) (k i)
     a : is-antisymmetric
     a σ τ l k =
      to-𝓓∞-＝ (λ i → antisymmetry (𝓓 i) (⦅ σ ⦆ i) (⦅ τ ⦆ i) (l i) (k i))
   dc : is-directed-complete _≼_
   dc 𝓐 α δ = (𝓓∞-∐ α δ) , ub , lb-of-ubs
    where
     δ' : (i : I) → is-Directed (𝓓 i) (family-at-ith-component α i)
     δ' = family-at-ith-component-is-directed α δ
     ub : (a : 𝓐) → α a ≼ (𝓓∞-∐ α δ)
     ub a i = ∐-is-upperbound (𝓓 i) (δ' i) a
     lb-of-ubs : is-lowerbound-of-upperbounds _≼_ (𝓓∞-∐ α δ) α
     lb-of-ubs τ ub i = ∐-is-lowerbound-of-upperbounds (𝓓 i) (δ' i) (⦅ τ ⦆ i)
                        (λ a → ub a i)

 π∞ : (i : I) → ⟨ 𝓓∞ ⟩ → ⟨ 𝓓 i ⟩
 π∞ i (σ , _) = σ i

 π∞-commutes-with-πs : (i j : I) (l : i ⊑ j) → π l ∘ π∞ j ∼ π∞ i
 π∞-commutes-with-πs i j l σ = π-equality σ l

 κ : {i j : I} → ⟨ 𝓓 i ⟩ → (Σ k ꞉ I , i ⊑ k × j ⊑ k) → ⟨ 𝓓 j ⟩
 κ x (k , lᵢ , lⱼ) = π lⱼ (ε lᵢ x)

 κ-wconstant : (i j : I) (x : ⟨ 𝓓 i ⟩) → wconstant (κ x)
 κ-wconstant i j x (k , lᵢ , lⱼ) (k' , lᵢ' , lⱼ') =
  ∥∥-rec (sethood (𝓓 j)) γ (I-semidirected k k')
   where
    γ : (Σ m ꞉ I , k ⊑ m × k' ⊑ m)
      → κ x (k , lᵢ , lⱼ) ＝ κ x (k' , lᵢ' , lⱼ')
    γ (m , u , u') = π lⱼ (ε lᵢ x)                           ＝⟨ e₁ ⟩
                     π lⱼ (π u (ε u (ε lᵢ x)))               ＝⟨ e₂ ⟩
                     π (⊑-trans lⱼ u) (ε u (ε lᵢ x))         ＝⟨ e₃ ⟩
                     π (⊑-trans lⱼ u) (ε (⊑-trans lᵢ u) x)   ＝⟨ e₄ ⟩
                     π (⊑-trans lⱼ u) (ε (⊑-trans lᵢ' u') x) ＝⟨ e₅ ⟩
                     π (⊑-trans lⱼ u) (ε u' (ε lᵢ' x))       ＝⟨ e₆ ⟩
                     π (⊑-trans lⱼ' u') (ε u' (ε lᵢ' x))     ＝⟨ e₇ ⟩
                     π lⱼ' (π u' (ε u' (ε lᵢ' x)))           ＝⟨ e₈ ⟩
                     π lⱼ' (ε lᵢ' x)                         ∎
     where
      e₁ = ap (π lⱼ) (ε-section-of-π u (ε lᵢ x) ⁻¹)
      e₂ = π-comp lⱼ u (ε u (ε lᵢ x))
      e₃ = ap (π (⊑-trans lⱼ u)) (ε-comp lᵢ u x)
      e₄ = ap (π (⊑-trans lⱼ u)) (ap (λ - → ε - x)
           (⊑-prop-valued i m (⊑-trans lᵢ u) (⊑-trans lᵢ' u')))
      e₅ = ap (π (⊑-trans lⱼ u)) ((ε-comp lᵢ' u' x) ⁻¹)
      e₆ = ap (λ - → π - _) (⊑-prop-valued j m (⊑-trans lⱼ u) (⊑-trans lⱼ' u'))
      e₇ = (π-comp lⱼ' u' (ε u' (ε lᵢ' x))) ⁻¹
      e₈ = ap (π lⱼ') (ε-section-of-π u' (ε lᵢ' x))

 ρ : (i j : I) → ⟨ 𝓓 i ⟩ → ⟨ 𝓓 j ⟩
 ρ i j x = pr₁ (wconstant-map-to-set-factors-through-truncation-of-domain
                 (sethood (𝓓 j)) (κ x) (κ-wconstant i j x))
               (I-semidirected i j)

 ρ-in-terms-of-κ : {i j k : I} (lᵢ : i ⊑ k) (lⱼ : j ⊑ k) (x : ⟨ 𝓓 i ⟩)
                 → ρ i j x ＝ κ x (k , lᵢ , lⱼ)
 ρ-in-terms-of-κ {i} {j} {k} lᵢ lⱼ x =
  ρ i j x                 ＝⟨ refl ⟩
  ν (I-semidirected i j)  ＝⟨ p ⟩
  ν ∣ (k , lᵢ , lⱼ) ∣     ＝⟨ q ⟩
  κ x (k , lᵢ , lⱼ)       ∎
   where
    s : is-set ⟨ 𝓓 j ⟩
    s = sethood (𝓓 j)
    ω : wconstant (κ x)
    ω = κ-wconstant i j x
    φ : Σ r ꞉ ((∃ k' ꞉ I , i ⊑ k' × j ⊑ k') → ⟨ 𝓓 j ⟩) , κ x ∼ r ∘ ∣_∣
    φ = wconstant-map-to-set-factors-through-truncation-of-domain s (κ x) ω
    ν : (∃ k' ꞉ I , i ⊑ k' × j ⊑ k') → ⟨ 𝓓 j ⟩
    ν = pr₁ φ
    p = ap ν (∥∥-is-prop (I-semidirected i j) ∣ k , lᵢ , lⱼ ∣)
    q = (pr₂ φ (k , lᵢ , lⱼ)) ⁻¹

 ε∞ : (i : I) → ⟨ 𝓓 i ⟩ → ⟨ 𝓓∞ ⟩
 ε∞ i x = σ , φ
  where
   σ : (j : I) → ⟨ 𝓓 j ⟩
   σ j = ρ i j x
   φ : (j₁ j₂ : I) (l : j₁ ⊑ j₂) → π l (σ j₂) ＝ σ j₁
   φ j₁ j₂ l = ∥∥-rec (sethood (𝓓 j₁)) γ (I-semidirected i j₂)
    where
     γ : (Σ k ꞉ I , i ⊑ k × j₂ ⊑ k) → π l (σ j₂) ＝ σ j₁
     γ (k , lᵢ , l₂) = π l (σ j₂)                  ＝⟨ refl ⟩
                       π l (ρ i j₂ x)              ＝⟨ e₁   ⟩
                       π l (κ x (k , lᵢ , l₂))     ＝⟨ refl ⟩
                       π l (π l₂ (ε lᵢ x))         ＝⟨ e₂   ⟩
                       π (⊑-trans l l₂) (ε lᵢ x)   ＝⟨ refl ⟩
                       π (⊑-trans l l₂) (ε lᵢ x)   ＝⟨ refl ⟩
                       κ x (k , lᵢ , ⊑-trans l l₂) ＝⟨ e₃   ⟩
                       ρ i j₁ x                    ＝⟨ refl ⟩
                       σ j₁                        ∎
      where
       e₁ = ap (π l) (ρ-in-terms-of-κ lᵢ l₂ x)
       e₂ = π-comp l l₂ (ε lᵢ x)
       e₃ = (ρ-in-terms-of-κ lᵢ (⊑-trans l l₂) x) ⁻¹

 ε∞-commutes-with-εs : (i j : I) (l : i ⊑ j) → ε∞ j ∘ ε l ∼ ε∞ i
 ε∞-commutes-with-εs i j l x = to-𝓓∞-＝ γ
  where
   γ : (k : I) → ⦅ ε∞ j (ε l x) ⦆ k ＝ ⦅ ε∞ i x ⦆ k
   γ k = ∥∥-rec (sethood (𝓓 k)) g (I-semidirected j k)
    where
     g : (Σ m ꞉ I , j ⊑ m × k ⊑ m) → ⦅ ε∞ j (ε l x) ⦆ k ＝ ⦅ ε∞ i x ⦆ k
     g (m , lⱼ , lₖ) =
      ⦅ ε∞ j (ε l x) ⦆ k          ＝⟨ refl ⟩
      ρ j k (ε l x)               ＝⟨ ρ-in-terms-of-κ lⱼ lₖ (ε l x) ⟩
      κ (ε l x) (m , lⱼ , lₖ)     ＝⟨ refl ⟩
      π lₖ (ε lⱼ (ε l x))         ＝⟨ ap (π lₖ) (ε-comp l lⱼ x) ⟩
      π lₖ (ε (⊑-trans l lⱼ) x)   ＝⟨ refl ⟩
      κ x (m , ⊑-trans l lⱼ , lₖ) ＝⟨ (ρ-in-terms-of-κ (⊑-trans l lⱼ) lₖ x) ⁻¹ ⟩
      ρ i k x                     ＝⟨ refl ⟩
      ⦅ ε∞ i x ⦆ k                ∎

 ε∞-section-of-π∞ : {i : I} → π∞ i ∘ ε∞ i ∼ id
 ε∞-section-of-π∞ {i} x =
  π∞ i (ε∞ i x)  ＝⟨ refl ⟩
  ⦅ ε∞ i x ⦆ i              ＝⟨ refl ⟩
  ρ i i x                   ＝⟨ ρ-in-terms-of-κ ⊑-refl ⊑-refl x ⟩
  κ x (i , ⊑-refl , ⊑-refl) ＝⟨ refl ⟩
  π ⊑-refl (ε ⊑-refl x)     ＝⟨ ε-section-of-π ⊑-refl x ⟩
  x                         ∎

 ε∞π∞-deflation : {i : I} (σ : ⟨ 𝓓∞ ⟩) → ε∞ i (π∞ i σ) ⊑⟨ 𝓓∞ ⟩ σ
 ε∞π∞-deflation {i} σ j =
  ∥∥-rec (prop-valuedness (𝓓 j) (⦅ ε∞ i (π∞ i σ) ⦆ j) (⦅ σ ⦆ j)) γ
   (I-semidirected i j)
   where
    γ : (Σ k ꞉ I , i ⊑ k × j ⊑ k)
      → ⦅ ε∞ i (π∞ i σ) ⦆ j ⊑⟨ 𝓓 j ⟩ ⦅ σ ⦆ j
    γ (k , lᵢ , lⱼ) = ⦅ ε∞ i (π∞ i σ) ⦆ j          ⊑⟨ 𝓓 j ⟩[ reflexivity (𝓓 j) _ ]
                      ρ i j (⦅ σ ⦆ i)              ⊑⟨ 𝓓 j ⟩[ u₁ ]
                      κ (⦅ σ ⦆ i) (k , lᵢ , lⱼ)    ⊑⟨ 𝓓 j ⟩[ reflexivity (𝓓 j) _ ]
                      π lⱼ (ε lᵢ (⦅ σ ⦆ i))        ⊑⟨ 𝓓 j ⟩[ u₂ ]
                      π lⱼ (ε lᵢ (π lᵢ (⦅ σ ⦆ k))) ⊑⟨ 𝓓 j ⟩[ u₃ ]
                      π lⱼ (⦅ σ ⦆ k)               ⊑⟨ 𝓓 j ⟩[ u₄ ]
                      ⦅ σ ⦆ j                      ∎⟨ 𝓓 j ⟩
     where
      u₁ = ＝-to-⊑ (𝓓 j) (ρ-in-terms-of-κ lᵢ lⱼ (⦅ σ ⦆ i))
      u₂ = ＝-to-⊒ (𝓓 j) (ap (π lⱼ ∘ ε lᵢ) (π-equality σ lᵢ))
      u₃ = monotone-if-continuous (𝓓 k) (𝓓 j) (π lⱼ , π-is-continuous lⱼ)
            (ε lᵢ (π lᵢ (⦅ σ ⦆ k))) (⦅ σ ⦆ k) (επ-deflation lᵢ (⦅ σ ⦆ k))
      u₄ = ＝-to-⊑ (𝓓 j) (π-equality σ lⱼ)

 π∞-is-continuous : (i : I) → is-continuous 𝓓∞ (𝓓 i) (π∞ i)
 π∞-is-continuous i 𝓐 α δ = ub , lb-of-ubs
  where
   δ' : (j : I) → is-Directed (𝓓 j) (family-at-ith-component α j)
   δ' = family-at-ith-component-is-directed α δ
   ub : (a : 𝓐) → π∞ i (α a) ⊑⟨ 𝓓 i ⟩ π∞ i (∐ 𝓓∞ {𝓐} {α} δ)
   ub a = π∞ i (α a)            ⊑⟨ 𝓓 i ⟩[ reflexivity (𝓓 i) _ ]
          ⦅ α a ⦆ i             ⊑⟨ 𝓓 i ⟩[ ∐-is-upperbound (𝓓 i) (δ' i) a ]
          ∐ (𝓓 i) (δ' i)        ⊑⟨ 𝓓 i ⟩[ reflexivity (𝓓 i) _ ]
          ⦅ ∐ 𝓓∞ {𝓐} {α} δ ⦆ i  ⊑⟨ 𝓓 i ⟩[ reflexivity (𝓓 i) _ ]
          π∞ i (∐ 𝓓∞ {𝓐} {α} δ) ∎⟨ 𝓓 i ⟩
   lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 i))
                 (π∞ i (∐ 𝓓∞ {𝓐} {α} δ)) (π∞ i ∘ α)
   lb-of-ubs x ub = π∞ i (∐ 𝓓∞ {𝓐} {α} δ) ⊑⟨ 𝓓 i ⟩[ reflexivity (𝓓 i) _ ]
                    ∐ (𝓓 i) (δ' i)        ⊑⟨ 𝓓 i ⟩[ l ]
                    x                     ∎⟨ 𝓓 i ⟩
    where
     l = ∐-is-lowerbound-of-upperbounds (𝓓 i) (δ' i) x ub

 π∞' : (i : I) → DCPO[ 𝓓∞ , 𝓓 i ]
 π∞' i = π∞ i , π∞-is-continuous i

 ε∞-is-monotone : (i : I) → is-monotone (𝓓 i) 𝓓∞ (ε∞ i)
 ε∞-is-monotone i x y l j =
  ∥∥-rec (prop-valuedness (𝓓 j) (⦅ ε∞ i x ⦆ j) (⦅ ε∞ i y ⦆ j))
   γ (I-semidirected i j)
    where
     γ : (Σ k ꞉ I , i ⊑ k × j ⊑ k)
       → ⦅ ε∞ i x ⦆ j ⊑⟨ 𝓓 j ⟩ ⦅ ε∞ i y ⦆ j
     γ (k , lᵢ , lⱼ) = ⦅ ε∞ i x ⦆ j      ⊑⟨ 𝓓 j ⟩[ u₁ ]
                       ρ i j x           ⊑⟨ 𝓓 j ⟩[ u₂ ]
                       κ x (k , lᵢ , lⱼ) ⊑⟨ 𝓓 j ⟩[ u₃ ]
                       π lⱼ (ε lᵢ x)     ⊑⟨ 𝓓 j ⟩[ u₄ ]
                       π lⱼ (ε lᵢ y)     ⊑⟨ 𝓓 j ⟩[ u₅ ]
                       κ y (k , lᵢ , lⱼ) ⊑⟨ 𝓓 j ⟩[ u₆ ]
                       ρ i j y           ⊑⟨ 𝓓 j ⟩[ u₇ ]
                       ⦅ ε∞ i y ⦆ j      ∎⟨ 𝓓 j ⟩
      where
       u₁ = reflexivity (𝓓 j) (⦅ ε∞ i x ⦆ j)
       u₂ = ＝-to-⊑ (𝓓 j) (ρ-in-terms-of-κ lᵢ lⱼ x)
       u₃ = reflexivity (𝓓 j) (κ x (k , lᵢ , lⱼ))
       u₄ = mπ (ε lᵢ x) (ε lᵢ y) (mε x y l)
        where
         mε : is-monotone (𝓓 i) (𝓓 k) (ε lᵢ)
         mε = monotone-if-continuous (𝓓 i) (𝓓 k)
               ((ε lᵢ) , (ε-is-continuous lᵢ))
         mπ : is-monotone (𝓓 k) (𝓓 j) (π lⱼ)
         mπ = monotone-if-continuous (𝓓 k) (𝓓 j)
               ((π lⱼ) , (π-is-continuous lⱼ))
       u₅ = reflexivity (𝓓 j) (π lⱼ (ε lᵢ y))
       u₆ = ＝-to-⊒ (𝓓 j) (ρ-in-terms-of-κ lᵢ lⱼ y)
       u₇ = reflexivity (𝓓 j) (ρ i j y)

 ε∞-is-continuous : (i : I) → is-continuous (𝓓 i) 𝓓∞ (ε∞ i)
 ε∞-is-continuous i = continuity-criterion' (𝓓 i) 𝓓∞ (ε∞ i) (ε∞-is-monotone i) γ
  where
   γ : (𝓐 : 𝓥 ̇ )(α : 𝓐 → ⟨ 𝓓 i ⟩) (δ : is-Directed (𝓓 i) α)
     → is-lowerbound-of-upperbounds (underlying-order 𝓓∞)
        (ε∞ i (∐ (𝓓 i) δ)) (ε∞ i ∘ α)
   γ 𝓐 α δ σ ub j =
    ∥∥-rec (prop-valuedness (𝓓 j) (⦅ ε∞ i (∐ (𝓓 i) δ) ⦆ j) (⦅ σ ⦆ j))
     g (I-semidirected i j)
      where
       g : (Σ k ꞉ I , i ⊑ k × j ⊑ k)
         → ⦅ ε∞ i (∐ (𝓓 i) δ) ⦆ j ⊑⟨ 𝓓 j ⟩ ⦅ σ ⦆ j
       g (k , lᵢ , lⱼ) =
        ⦅ ε∞ i (∐ (𝓓 i) δ) ⦆ j                  ⊑⟨ 𝓓 j ⟩[ u₁ ]
        ρ i j (∐ (𝓓 i) δ)                       ⊑⟨ 𝓓 j ⟩[ u₂ ]
        κ (∐ (𝓓 i) δ) (k , lᵢ , lⱼ)             ⊑⟨ 𝓓 j ⟩[ u₃ ]
        π lⱼ (ε lᵢ (∐ (𝓓 i) δ))                 ⊑⟨ 𝓓 j ⟩[ u₄ ]
        ∐ (𝓓 j) {𝓐} {πε ∘ α} δ₁                 ⊑⟨ 𝓓 j ⟩[ u₅ ]
        ∐ (𝓓 j) {𝓐} {λ a → ⦅ ε∞ i (α a) ⦆ j} δ₂ ⊑⟨ 𝓓 j ⟩[ u₆ ]
        ⦅ σ ⦆ j ∎⟨ 𝓓 j ⟩
         where
          πε : ⟨ 𝓓 i ⟩ → ⟨ 𝓓 j ⟩
          πε = π lⱼ ∘ ε lᵢ
          πε-is-continuous : is-continuous (𝓓 i) (𝓓 j) πε
          πε-is-continuous = ∘-is-continuous (𝓓 i) (𝓓 k) (𝓓 j) (ε lᵢ) (π lⱼ)
                              (ε-is-continuous lᵢ) (π-is-continuous lⱼ)
          πε' : DCPO[ 𝓓 i , 𝓓 j ]
          πε' = πε , πε-is-continuous
          δ₁ : is-Directed (𝓓 j) (πε ∘ α)
          δ₁ = image-is-directed' (𝓓 i) (𝓓 j) πε' δ
          p : πε ∘ α ＝ (λ a → ⦅ ε∞ i (α a) ⦆ j)
          p = dfunext fe h
           where
            h : πε ∘ α ∼ (λ a → ⦅ ε∞ i (α a) ⦆ j)
            h a = πε (α a)              ＝⟨ refl ⟩
                  π lⱼ (ε lᵢ (α a))     ＝⟨ refl ⟩
                  κ (α a) (k , lᵢ , lⱼ) ＝⟨ (ρ-in-terms-of-κ lᵢ lⱼ (α a)) ⁻¹ ⟩
                  ρ i j (α a)           ＝⟨ refl ⟩
                  ⦅ ε∞ i (α a) ⦆ j      ∎
          δ₂ : is-Directed (𝓓 j) (λ a → ⦅ ε∞ i (α a) ⦆ j)
          δ₂ = transport (is-Directed (𝓓 j)) p δ₁
          u₁ = reflexivity (𝓓 j) (⦅ ε∞ i (∐ (𝓓 i) δ) ⦆ j)
          u₂ = ＝-to-⊑ (𝓓 j) (ρ-in-terms-of-κ lᵢ lⱼ (∐ (𝓓 i) δ))
          u₃ = reflexivity (𝓓 j) (κ (∐ (𝓓 i) δ) (k , lᵢ , lⱼ))
          u₄ = continuous-∐-⊑ (𝓓 i) (𝓓 j) πε' δ
          u₅ = ＝-to-⊑ (𝓓 j) (∐-family-＝ (𝓓 j) p δ₁)
          u₆ = ∐-is-lowerbound-of-upperbounds (𝓓 j) δ₂ (⦅ σ ⦆ j) (λ a → ub a j)

 ε∞' : (i : I) → DCPO[ 𝓓 i , 𝓓∞ ]
 ε∞' i = ε∞ i , ε∞-is-continuous i

\end{code}

This concludes the construction of the bilimit. We proceed by showing that it is
indeed the limit of the diagram.

\begin{code}

 module DcpoCone
         (𝓔 : DCPO {𝓤'} {𝓣'})
         (f : (i : I) → ⟨ 𝓔 ⟩ → ⟨ 𝓓 i ⟩)
         (f-cont : (i : I) → is-continuous 𝓔 (𝓓 i) (f i))
         (comm : (i j : I) (l : i ⊑ j) → π l ∘ f j ∼ f i)
        where

  limit-mediating-arrow : ⟨ 𝓔 ⟩ → ⟨ 𝓓∞ ⟩
  limit-mediating-arrow y = σ , φ
   where
    σ : (i : I) → ⟨ 𝓓 i ⟩
    σ i = f i y
    φ : (i j : I) (l : i ⊑ j) → π l (f j y) ＝ f i y
    φ i j l = comm i j l y

  limit-mediating-arrow-commutes : (i : I) → π∞ i ∘ limit-mediating-arrow ∼ f i
  limit-mediating-arrow-commutes i y = refl

  limit-mediating-arrow-is-unique : (g : ⟨ 𝓔 ⟩ → ⟨ 𝓓∞ ⟩)
                                  → ((i : I) → π∞ i ∘ g ∼ f i)
                                  → g ∼ limit-mediating-arrow
  limit-mediating-arrow-is-unique g g-comm y =
   to-𝓓∞-＝ (λ i → g-comm i y)

  limit-mediating-arrow-is-monotone : is-monotone 𝓔 𝓓∞ limit-mediating-arrow
  limit-mediating-arrow-is-monotone x y l i = f i x ⊑⟨ 𝓓 i ⟩[ m x y l ]
                                              f i y ∎⟨ 𝓓 i ⟩
   where
    m : is-monotone 𝓔 (𝓓 i) (f i)
    m = monotone-if-continuous 𝓔 (𝓓 i) (f i , f-cont i)

  limit-mediating-arrow-is-continuous : is-continuous 𝓔 𝓓∞ limit-mediating-arrow
  limit-mediating-arrow-is-continuous = continuity-criterion' 𝓔 𝓓∞ m mon γ
   where
    m : ⟨ 𝓔 ⟩ → ⟨ 𝓓∞ ⟩
    m = limit-mediating-arrow
    mon : is-monotone 𝓔 𝓓∞ m
    mon = limit-mediating-arrow-is-monotone
    γ : (A : 𝓥 ̇ )(α : A → ⟨ 𝓔 ⟩) (δ : is-Directed 𝓔 α)
      → is-lowerbound-of-upperbounds (underlying-order 𝓓∞) (m (∐ 𝓔 δ)) (m ∘ α)
    γ A α δ σ ub i = ⦅ m (∐ 𝓔 δ) ⦆ i ⊑⟨ 𝓓 i ⟩[ u₁ ]
                     f i (∐ 𝓔 δ)     ⊑⟨ 𝓓 i ⟩[ u₂ ]
                     ∐ (𝓓 i) δ'      ⊑⟨ 𝓓 i ⟩[ u₃ ]
                     ⦅ σ ⦆ i          ∎⟨ 𝓓 i ⟩
     where
      δ' : is-Directed (𝓓 i) (f i ∘ α)
      δ' = image-is-directed' 𝓔 (𝓓 i) (f i , f-cont i) δ
      u₁ = reflexivity (𝓓 i) (⦅ m (∐ 𝓔 δ) ⦆ i)
      u₂ = continuous-∐-⊑ 𝓔 (𝓓 i) (f i , f-cont i) δ
      u₃ = ∐-is-lowerbound-of-upperbounds (𝓓 i) δ' (⦅ σ ⦆ i) (λ a → ub a i)

\end{code}

Next, we wish to show that 𝓓∞ is also the colimit of the diagram. The following
are preliminaries for doing so.

\begin{code}

 ε∞-family : ⟨ 𝓓∞ ⟩ → I → ⟨ 𝓓∞ ⟩
 ε∞-family σ i = ε∞ i (⦅ σ ⦆ i)

 ε∞-family-is-monotone : (σ : ⟨ 𝓓∞ ⟩) (i j : I) → i ⊑ j
                       → ε∞-family σ i ⊑⟨ 𝓓∞ ⟩ ε∞-family σ j
 ε∞-family-is-monotone σ i j l k =
  ∥∥-rec (prop-valuedness (𝓓 k) (⦅ ε∞-family σ i ⦆ k) (⦅ ε∞-family σ j ⦆ k))
   γ (I-semidirected j k)
    where
     γ : (Σ m ꞉ I , j ⊑ m × k ⊑ m)
       → ⦅ ε∞-family σ i ⦆ k ⊑⟨ 𝓓 k ⟩ ⦅ ε∞-family σ j ⦆ k
     γ (m , lⱼ , lₖ) =
      ⦅ ε∞-family σ i ⦆ k                 ⊑⟨ 𝓓 k ⟩[ u₁ ]
      ρ i k (⦅ σ ⦆ i)                     ⊑⟨ 𝓓 k ⟩[ u₂ ]
      κ (⦅ σ ⦆ i) (m , ⊑-trans l lⱼ , lₖ) ⊑⟨ 𝓓 k ⟩[ u₃ ]
      π lₖ (ε (⊑-trans l lⱼ) (⦅ σ ⦆ i))   ⊑⟨ 𝓓 k ⟩[ u₄ ]
      π lₖ (ε lⱼ (ε l (⦅ σ ⦆ i)))         ⊑⟨ 𝓓 k ⟩[ u₅ ]
      π lₖ (ε lⱼ (ε l (π l (⦅ σ ⦆ j))))   ⊑⟨ 𝓓 k ⟩[ u₆ ]
      π lₖ (ε lⱼ (⦅ σ ⦆ j))               ⊑⟨ 𝓓 k ⟩[ u₇ ]
      κ (⦅ σ ⦆ j) (m , lⱼ , lₖ)           ⊑⟨ 𝓓 k ⟩[ u₈ ]
      ρ j k (⦅ σ ⦆ j)                     ⊑⟨ 𝓓 k ⟩[ u₉ ]
      ⦅ ε∞-family σ j ⦆ k                 ∎⟨ 𝓓 k ⟩
       where
        u₁ = reflexivity (𝓓 k) (⦅ ε∞-family σ i ⦆ k)
        u₂ = ＝-to-⊑ (𝓓 k) (ρ-in-terms-of-κ (⊑-trans l lⱼ) lₖ (⦅ σ ⦆ i))
        u₃ = reflexivity (𝓓 k) (κ (⦅ σ ⦆ i) (m , ⊑-trans l lⱼ , lₖ))
        u₄ = ＝-to-⊒ (𝓓 k) (ap (π lₖ) (ε-comp l lⱼ (⦅ σ ⦆ i)))
        u₅ = ＝-to-⊒ (𝓓 k) (ap (π lₖ ∘ ε lⱼ ∘ ε l) (π-equality σ l))
        u₆ = mon (ε l (π l (⦅ σ ⦆ j))) (⦅ σ ⦆ j) (επ-deflation l (⦅ σ ⦆ j))
         where
          mon : is-monotone (𝓓 j) (𝓓 k) (π lₖ ∘ ε lⱼ)
          mon = monotone-if-continuous (𝓓 j) (𝓓 k)
                 (π lₖ ∘ ε lⱼ ,
                  ∘-is-continuous (𝓓 j) (𝓓 m) (𝓓 k)
                  (ε lⱼ) (π lₖ) (ε-is-continuous lⱼ) (π-is-continuous lₖ))
        u₇ = reflexivity (𝓓 k) (κ (⦅ σ ⦆ j) (m , lⱼ , lₖ))
        u₈ = ＝-to-⊒ (𝓓 k) (ρ-in-terms-of-κ lⱼ lₖ (⦅ σ ⦆ j))
        u₉ = reflexivity (𝓓 k) (⦅ ε∞-family σ j ⦆ k)

 ε∞-family-is-directed : (σ : ⟨ 𝓓∞ ⟩) → is-Directed 𝓓∞ (ε∞-family σ)
 ε∞-family-is-directed σ = I-inhabited , δ
  where
   δ : is-semidirected (underlying-order 𝓓∞) (ε∞-family σ)
   δ i j = ∥∥-functor γ (I-semidirected i j)
    where
     γ : (Σ k ꞉ I , i ⊑ k × j ⊑ k)
       → (Σ k ꞉ I , ε∞-family σ i ⊑⟨ 𝓓∞ ⟩ ε∞-family σ k
                  × ε∞-family σ j ⊑⟨ 𝓓∞ ⟩ ε∞-family σ k)
     γ (k , lᵢ , lⱼ) =
      k , ε∞-family-is-monotone σ i k lᵢ ,
          ε∞-family-is-monotone σ j k lⱼ

 ∐-of-ε∞s : (σ : ⟨ 𝓓∞ ⟩) → σ ＝ ∐ 𝓓∞ {I} {ε∞-family σ} (ε∞-family-is-directed σ)
 ∐-of-ε∞s σ = antisymmetry 𝓓∞ σ (∐ 𝓓∞ δ) a b
  where
   α : I → ⟨ 𝓓∞ ⟩
   α = ε∞-family σ
   δ : is-Directed 𝓓∞ α
   δ = ε∞-family-is-directed σ
   a : σ ⊑⟨ 𝓓∞ ⟩ ∐ 𝓓∞ {I} {α} δ
   a i = ⦅ σ ⦆ i                           ⊑⟨ 𝓓 i ⟩[ u₁ ]
         ε ⊑-refl (⦅ σ ⦆ i)                ⊑⟨ 𝓓 i ⟩[ u₂ ]
         π ⊑-refl (ε ⊑-refl (⦅ σ ⦆ i))     ⊑⟨ 𝓓 i ⟩[ u₃ ]
         κ (⦅ σ ⦆ i) (i , ⊑-refl , ⊑-refl) ⊑⟨ 𝓓 i ⟩[ u₄ ]
         ρ i i (⦅ σ ⦆ i)                   ⊑⟨ 𝓓 i ⟩[ u₅ ]
         ⦅ ε∞ i (⦅ σ ⦆ i) ⦆ i              ⊑⟨ 𝓓 i ⟩[ u₆ ]
         family-at-ith-component α i i     ⊑⟨ 𝓓 i ⟩[ u₇ ]
         ∐ (𝓓 i) δ'                        ⊑⟨ 𝓓 i ⟩[ u₈ ]
         ⦅ (∐ 𝓓∞ {I} {α} δ) ⦆ i            ∎⟨ 𝓓 i ⟩
    where
     δ' : is-Directed (𝓓 i) (family-at-ith-component α i)
     δ' = family-at-ith-component-is-directed α δ i
     u₁ = ＝-to-⊒ (𝓓 i) (ε-id i (⦅ σ ⦆ i))
     u₂ = ＝-to-⊒ (𝓓 i) (π-id i (ε ⊑-refl (⦅ σ ⦆ i)))
     u₃ = reflexivity (𝓓 i) (π ⊑-refl (ε ⊑-refl (⦅ σ ⦆ i)))
     u₄ = ＝-to-⊒ (𝓓 i) (ρ-in-terms-of-κ ⊑-refl ⊑-refl (⦅ σ ⦆ i))
     u₅ = reflexivity (𝓓 i) (ρ i i (⦅ σ ⦆ i))
     u₆ = reflexivity (𝓓 i) (⦅ ε∞ i (⦅ σ ⦆ i) ⦆ i )
     u₇ = ∐-is-upperbound (𝓓 i) δ' i
     u₈ = reflexivity (𝓓 i) (⦅ ∐ 𝓓∞ {I} {α} δ ⦆ i)
   b : ∐ 𝓓∞ {I} {α} δ ⊑⟨ 𝓓∞ ⟩ σ
   b = ∐-is-lowerbound-of-upperbounds 𝓓∞ {I} {α} δ σ γ
    where
     γ : (i : I) → α i ⊑⟨ 𝓓∞ ⟩ σ
     γ i j = ∥∥-rec (prop-valuedness (𝓓 j) (⦅ α i ⦆ j) (⦅ σ ⦆ j))
              g (I-semidirected i j)
      where
       g : (Σ k ꞉ I , i ⊑ k × j ⊑ k) → ⦅ α i ⦆ j ⊑⟨ 𝓓 j ⟩ ⦅ σ ⦆ j
       g (k , lᵢ , lⱼ) = ⦅ α i ⦆ j                    ⊑⟨ 𝓓 j ⟩[ u₁ ]
                         ⦅ ε∞ i (⦅ σ ⦆ i) ⦆ j         ⊑⟨ 𝓓 j ⟩[ u₂ ]
                         ρ i j (⦅ σ ⦆ i)              ⊑⟨ 𝓓 j ⟩[ u₃ ]
                         κ (⦅ σ ⦆ i) (k , lᵢ , lⱼ)    ⊑⟨ 𝓓 j ⟩[ u₄ ]
                         π lⱼ (ε lᵢ (⦅ σ ⦆ i))        ⊑⟨ 𝓓 j ⟩[ u₅ ]
                         π lⱼ (ε lᵢ (π lᵢ (⦅ σ ⦆ k))) ⊑⟨ 𝓓 j ⟩[ u₆ ]
                         π lⱼ (⦅ σ ⦆ k)               ⊑⟨ 𝓓 j ⟩[ u₇ ]
                         ⦅ σ ⦆ j                      ∎⟨ 𝓓 j ⟩
        where
         u₁ = reflexivity (𝓓 j) (⦅ α i ⦆ j)
         u₂ = reflexivity (𝓓 j) (⦅ ε∞ i (⦅ σ ⦆ i) ⦆ j)
         u₃ = ＝-to-⊑ (𝓓 j) (ρ-in-terms-of-κ lᵢ lⱼ (⦅ σ ⦆ i))
         u₄ = reflexivity (𝓓 j) (κ (⦅ σ ⦆ i) (k , lᵢ , lⱼ))
         u₅ = ＝-to-⊒ (𝓓 j) (ap (π lⱼ ∘ ε lᵢ) (π-equality σ lᵢ))
         u₆ = mon (ε lᵢ (π lᵢ (⦅ σ ⦆ k))) (⦅ σ ⦆ k) (επ-deflation lᵢ (⦅ σ ⦆ k))
          where
           mon : is-monotone (𝓓 k) (𝓓 j) (π lⱼ)
           mon = monotone-if-continuous (𝓓 k) (𝓓 j)
                  (π lⱼ , π-is-continuous lⱼ)
         u₇ = ＝-to-⊑ (𝓓 j) (π-equality σ lⱼ)

\end{code}

We now show that 𝓓∞ is the colimit of the diagram.

\begin{code}

 module DcpoCocone
         (𝓔 : DCPO {𝓤'} {𝓣'})
         (g : (i : I) → ⟨ 𝓓 i ⟩ → ⟨ 𝓔 ⟩)
         (g-cont : (i : I) → is-continuous (𝓓 i) 𝓔 (g i))
         (comm : (i j : I) (l : i ⊑ j) → g j ∘ ε l ∼ g i)
        where

  colimit-family : ⟨ 𝓓∞ ⟩ → I → ⟨ 𝓔 ⟩
  colimit-family σ i = g i (⦅ σ ⦆ i)

  colimit-family-is-monotone : (σ : ⟨ 𝓓∞ ⟩) (i j : I) (l : i ⊑ j)
                             → colimit-family σ i ⊑⟨ 𝓔 ⟩ colimit-family σ j
  colimit-family-is-monotone σ i j l =
   g i (⦅ σ ⦆ i)             ⊑⟨ 𝓔 ⟩[ u ]
   g i (π l (⦅ σ ⦆ j))       ⊑⟨ 𝓔 ⟩[ v ]
   g j (ε l (π l (⦅ σ ⦆ j))) ⊑⟨ 𝓔 ⟩[ w ]
   g j (⦅ σ ⦆ j)             ∎⟨ 𝓔 ⟩
    where
     u = ＝-to-⊒ 𝓔 (ap (g i) (π-equality σ l))
     v = ＝-to-⊒ 𝓔 (comm i j l (π l (⦅ σ ⦆ j)))
     w = gm (ε l (π l (⦅ σ ⦆ j))) (⦅ σ ⦆ j) (επ-deflation l (⦅ σ ⦆ j))
      where
       gm : is-monotone (𝓓 j) 𝓔 (g j)
       gm = monotone-if-continuous (𝓓 j) 𝓔 (g j , g-cont j)

  colimit-family-is-directed : (σ : ⟨ 𝓓∞ ⟩) → is-Directed 𝓔 (colimit-family σ)
  colimit-family-is-directed σ = I-inhabited , γ
   where
    γ : is-semidirected (underlying-order 𝓔) (colimit-family σ)
    γ i j = ∥∥-functor ψ (I-semidirected i j)
     where
      ψ : (Σ k ꞉ I , i ⊑ k × j ⊑ k)
        → (Σ k ꞉ I , colimit-family σ i ⊑⟨ 𝓔 ⟩ colimit-family σ k
                   × colimit-family σ j ⊑⟨ 𝓔 ⟩ colimit-family σ k)
      ψ (k , lᵢ , lⱼ) =
       k , colimit-family-is-monotone σ i k lᵢ ,
           colimit-family-is-monotone σ j k lⱼ

  colimit-mediating-arrow : ⟨ 𝓓∞ ⟩ → ⟨ 𝓔 ⟩
  colimit-mediating-arrow σ = ∐ 𝓔 {I} {φ} δ
   where
    φ : I → ⟨ 𝓔 ⟩
    φ = colimit-family σ
    δ : is-Directed 𝓔 φ
    δ = colimit-family-is-directed σ

  colimit-mediating-arrow-commutes : (i : I)
                                   → colimit-mediating-arrow ∘ ε∞ i ∼ g i
  colimit-mediating-arrow-commutes i x =
   antisymmetry 𝓔 (colimit-mediating-arrow ((ε∞ i) x)) (g i x) a b
    where
     δ : is-Directed 𝓔 (colimit-family (ε∞ i x))
     δ = colimit-family-is-directed (ε∞ i x)
     a : colimit-mediating-arrow (ε∞ i x) ⊑⟨ 𝓔 ⟩ g i x
     a = ∐-is-lowerbound-of-upperbounds 𝓔 δ (g i x) γ
      where
       γ : (j : I) → colimit-family (ε∞ i x) j ⊑⟨ 𝓔 ⟩ g i x
       γ j = ∥∥-rec (prop-valuedness 𝓔 (colimit-family (ε∞ i x) j) (g i x))
              ϕ (I-semidirected i j)
        where
         ϕ : (Σ k ꞉ I , i ⊑ k × j ⊑ k)
           → colimit-family (ε∞ i x) j ⊑⟨ 𝓔 ⟩ g i x
         ϕ (k , lᵢ , lⱼ) =
          colimit-family (ε∞ i x) j  ⊑⟨ 𝓔 ⟩[ u₁ ]
          g j (ρ i j x)              ⊑⟨ 𝓔 ⟩[ u₂ ]
          g j (κ x (k , lᵢ , lⱼ))    ⊑⟨ 𝓔 ⟩[ u₃ ]
          g j (π lⱼ (ε lᵢ x))        ⊑⟨ 𝓔 ⟩[ u₄ ]
          g k (ε lⱼ (π lⱼ (ε lᵢ x))) ⊑⟨ 𝓔 ⟩[ u₅ ]
          g k (ε lᵢ x)               ⊑⟨ 𝓔 ⟩[ u₆ ]
          g i x                      ∎⟨ 𝓔 ⟩
           where
            u₁ = reflexivity 𝓔 (colimit-family (ε∞ i x) j)
            u₂ = ＝-to-⊑ 𝓔 (ap (g j) (ρ-in-terms-of-κ lᵢ lⱼ x))
            u₃ = reflexivity 𝓔 (g j (κ x (k , lᵢ , lⱼ)))
            u₄ = ＝-to-⊒ 𝓔 (comm j k lⱼ (π lⱼ (ε lᵢ x)))
            u₅ = m (ε lⱼ (π lⱼ (ε lᵢ x))) (ε lᵢ x) (επ-deflation lⱼ (ε lᵢ x))
             where
              m : is-monotone (𝓓 k) 𝓔 (g k)
              m = monotone-if-continuous (𝓓 k) 𝓔 (g k , g-cont k)
            u₆ = ＝-to-⊑ 𝓔 (comm i k lᵢ x)
     b : g i x ⊑⟨ 𝓔 ⟩ colimit-mediating-arrow (ε∞ i x)
     b = g i x                            ⊑⟨ 𝓔 ⟩[ v₁ ]
         g i (ε ⊑-refl x)                 ⊑⟨ 𝓔 ⟩[ v₂ ]
         g i (π ⊑-refl (ε ⊑-refl x))      ⊑⟨ 𝓔 ⟩[ v₃ ]
         g i (κ x (i , ⊑-refl , ⊑-refl))  ⊑⟨ 𝓔 ⟩[ v₄ ]
         g i (ρ i i x)                    ⊑⟨ 𝓔 ⟩[ v₅ ]
         g i (⦅ ε∞ i x ⦆ i)               ⊑⟨ 𝓔 ⟩[ v₆ ]
         ∐ 𝓔 δ                            ⊑⟨ 𝓔 ⟩[ v₇ ]
         colimit-mediating-arrow (ε∞ i x) ∎⟨ 𝓔 ⟩
      where
       v₁ = ＝-to-⊒ 𝓔 (ap (g i) (ε-id i x))
       v₂ = ＝-to-⊒ 𝓔 (ap (g i) (π-id i (ε ⊑-refl x)))
       v₃ = reflexivity 𝓔 (g i (π ⊑-refl (ε ⊑-refl x)))
       v₄ = ＝-to-⊒ 𝓔 (ap (g i) (ρ-in-terms-of-κ ⊑-refl ⊑-refl x))
       v₅ = reflexivity 𝓔 (g i (ρ i i x))
       v₆ = ∐-is-upperbound 𝓔 δ i
       v₇ = reflexivity 𝓔 (∐ 𝓔 δ)

  colimit-mediating-arrow-is-unique : (h : ⟨ 𝓓∞ ⟩ → ⟨ 𝓔 ⟩)
                                    → is-continuous 𝓓∞ 𝓔 h
                                    → ((i : I) → h ∘ ε∞ i ∼ g i)
                                    → h ∼ colimit-mediating-arrow
  colimit-mediating-arrow-is-unique h h-cont h-comm σ =
   h σ                                   ＝⟨ ap h (∐-of-ε∞s σ) ⟩
   h (∐ 𝓓∞ {I} {λ i → ε∞ i (⦅ σ ⦆ i)} δ) ＝⟨ e₁ ⟩
   ∐ 𝓔 {I} {λ i → h (ε∞ i (⦅ σ ⦆ i))} δ₁ ＝⟨ e₂ ⟩
   ∐ 𝓔 {I} {λ i → g i (⦅ σ ⦆ i)} δ₂      ＝⟨ e₃ ⟩
   ∐ 𝓔 {I} {λ i → g i (⦅ σ ⦆ i)} δ₃      ＝⟨ refl ⟩
   colimit-mediating-arrow σ             ∎
    where
     p : (λ i → (h ∘ ε∞ i) (⦅ σ ⦆ i)) ＝ (λ i → g i (⦅ σ ⦆ i))
     p = dfunext fe (λ i → h-comm i (⦅ σ ⦆ i))
     δ : is-Directed 𝓓∞ {I} (ε∞-family σ)
     δ = ε∞-family-is-directed σ
     δ₁ : is-Directed 𝓔 (h ∘ ε∞-family σ)
     δ₁ = image-is-directed' 𝓓∞ 𝓔 (h , h-cont) {I} {ε∞-family σ} δ
     δ₂ : is-Directed 𝓔 (λ i → g i (⦅ σ ⦆ i))
     δ₂ = transport (is-Directed 𝓔 {I}) p δ₁
     δ₃ : is-Directed 𝓔 (colimit-family σ)
     δ₃ = colimit-family-is-directed σ
     e₁ = continuous-∐-＝ 𝓓∞ 𝓔 (h , h-cont) {I} {ε∞-family σ} δ
     e₂ = ∐-family-＝ 𝓔 {I} p δ₁
     e₃ = ∐-independent-of-directedness-witness 𝓔 δ₂ δ₃

  colimit-mediating-arrow-is-monotone : is-monotone 𝓓∞ 𝓔
                                         colimit-mediating-arrow
  colimit-mediating-arrow-is-monotone σ τ l = γ
   where
    δ₁ : is-Directed 𝓔 (colimit-family σ)
    δ₁ = colimit-family-is-directed σ
    δ₂ : is-Directed 𝓔 (colimit-family τ)
    δ₂ = colimit-family-is-directed τ
    γ : ∐ 𝓔 δ₁ ⊑⟨ 𝓔 ⟩ ∐ 𝓔 δ₂
    γ = ∐-is-monotone 𝓔 δ₁ δ₂ ψ
     where
      ψ : (i : I) → colimit-family σ i ⊑⟨ 𝓔 ⟩ colimit-family τ i
      ψ i = g i (⦅ σ ⦆ i) ⊑⟨ 𝓔 ⟩[ m (⦅ σ ⦆ i) (⦅ τ ⦆ i) (l i) ]
            g i (⦅ τ ⦆ i) ∎⟨ 𝓔 ⟩
       where
        m : is-monotone (𝓓 i) 𝓔 (g i)
        m = monotone-if-continuous (𝓓 i) 𝓔 (g i , g-cont i)

  colimit-mediating-arrow-is-continuous : is-continuous 𝓓∞ 𝓔
                                           colimit-mediating-arrow
  colimit-mediating-arrow-is-continuous = continuity-criterion' 𝓓∞ 𝓔 m mon γ
   where
    m : ⟨ 𝓓∞ ⟩ → ⟨ 𝓔 ⟩
    m = colimit-mediating-arrow
    mon : is-monotone 𝓓∞ 𝓔 colimit-mediating-arrow
    mon = colimit-mediating-arrow-is-monotone
    γ : (A : 𝓥 ̇ )(α : A → ⟨ 𝓓∞ ⟩) (δ : is-Directed 𝓓∞ α)
      → is-lowerbound-of-upperbounds (underlying-order 𝓔) (m (∐ 𝓓∞ {A} {α} δ)) (m ∘ α)
    γ A α δ y ub =
     ∐-is-lowerbound-of-upperbounds 𝓔
      (colimit-family-is-directed (∐ 𝓓∞ {A} {α} δ)) y ψ
      where
       ψ : (i : I) → g i (⦅ ∐ 𝓓∞ {A} {α} δ ⦆ i) ⊑⟨ 𝓔 ⟩ y
       ψ i = g i (⦅ ∐ 𝓓∞ {A} {α} δ ⦆ i)         ⊑⟨ 𝓔 ⟩[ u₁ ]
             ∐ 𝓔 {A} {λ a → g i (⦅ α a ⦆ i)} δ₂ ⊑⟨ 𝓔 ⟩[ u₂ ]
             y                                  ∎⟨ 𝓔 ⟩
        where
         δ₁ : is-Directed (𝓓 i) (family-at-ith-component α i)
         δ₁ = family-at-ith-component-is-directed α δ i
         δ₂ : is-Directed 𝓔 (λ a → g i (⦅ α a ⦆ i))
         δ₂ = image-is-directed' (𝓓 i) 𝓔 (g i , g-cont i) δ₁
         u₁ = continuous-∐-⊑ (𝓓 i) 𝓔 (g i , g-cont i) δ₁
         u₂ = ∐-is-lowerbound-of-upperbounds 𝓔 δ₂ y ϕ
          where
           ϕ : (a : A) → g i (⦅ α a ⦆ i) ⊑⟨ 𝓔 ⟩ y
           ϕ a = g i (⦅ α a ⦆ i)                         ⊑⟨ 𝓔 ⟩[ v    ]
                 ∐ 𝓔 (colimit-family-is-directed (α a)) ⊑⟨ 𝓔 ⟩[ ub a ]
                 y                                      ∎⟨ 𝓔 ⟩
            where
             v = ∐-is-upperbound 𝓔 (colimit-family-is-directed (α a)) i

\end{code}

Finally, we consider a curried version of ε∞-family, which will prove useful
(see Dinfinity.lagda) in the construction of Scott's D∞ for which D∞ is
isomorphic to its own self-exponential.

\begin{code}

 ε∞π∞-family : I → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩
 ε∞π∞-family i = DCPO-∘ 𝓓∞ (𝓓 i) 𝓓∞ (π∞' i) (ε∞' i)

 ε∞π∞-family-is-monotone : {i j : I} → i ⊑ j
                         → ε∞π∞-family i ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε∞π∞-family j
 ε∞π∞-family-is-monotone {i} {j} l σ = ε∞-family-is-monotone σ i j l

 ε∞π∞-family-is-directed : is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) ε∞π∞-family
 ε∞π∞-family-is-directed = I-inhabited , δ
  where
   δ : is-semidirected (underlying-order (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)) ε∞π∞-family
   δ i j = ∥∥-functor γ (I-semidirected i j)
    where
     γ : (Σ k ꞉ I , i ⊑ k × j ⊑ k)
       → (Σ k ꞉ I , ε∞π∞-family i ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε∞π∞-family k
                  × ε∞π∞-family j ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε∞π∞-family k)
     γ (k , lᵢ , lⱼ) =
      k , ε∞π∞-family-is-monotone lᵢ ,
          ε∞π∞-family-is-monotone lⱼ

 ∐-of-ε∞π∞s-is-id : ∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) {I} {ε∞π∞-family} ε∞π∞-family-is-directed
                  ＝ id , id-is-continuous 𝓓∞
 ∐-of-ε∞π∞s-is-id = to-continuous-function-＝ 𝓓∞ 𝓓∞ γ
  where
   δ : is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) ε∞π∞-family
   δ = ε∞π∞-family-is-directed
   γ : [ 𝓓∞ , 𝓓∞ ]⟨ ∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) {I} {ε∞π∞-family} δ ⟩ ∼ id
   γ σ = ∐ 𝓓∞ {I} {λ i → ε∞ i (⦅ σ ⦆ i)} δ₁ ＝⟨ e₁ ⟩
         ∐ 𝓓∞ {I} {λ i → ε∞ i (⦅ σ ⦆ i)} δ₂ ＝⟨ e₂ ⟩
         σ                                  ∎
    where
     δ₁ : is-Directed 𝓓∞ (λ i → ε∞ i (⦅ σ ⦆ i))
     δ₁ = pointwise-family-is-directed 𝓓∞ 𝓓∞ ε∞π∞-family δ σ
     δ₂ : is-Directed 𝓓∞ (λ i → ε∞ i (⦅ σ ⦆ i))
     δ₂ = ε∞-family-is-directed σ
     e₁ = ∐-independent-of-directedness-witness 𝓓∞ δ₁ δ₂
     e₂ = (∐-of-ε∞s σ) ⁻¹

\end{code}

Added 9 February 2022.

If every dcpo in the diagram is locally small, then so is its bilimit.

\begin{code}

 𝓓∞-is-locally-small : ((i : I) → is-locally-small (𝓓 i))
                     → is-locally-small 𝓓∞
 𝓓∞-is-locally-small ls = record { _⊑ₛ_ = _⊑ₛ⟨∞⟩_ ; ⊑ₛ-≃-⊑ = γ }
  where
   small-order : (i : I) → ⟨ 𝓓 i ⟩ → ⟨ 𝓓 i ⟩ → 𝓥 ̇
   small-order i = _⊑ₛ_ where open is-locally-small (ls i)
   syntax small-order i x y = x ⊑ₛ⟨ i ⟩ y
   ⊑ₛ-≃-⊑-at : (i : I) {x y : ⟨ 𝓓 i ⟩} → x ⊑ₛ⟨ i ⟩ y ≃ x ⊑⟨ 𝓓 i ⟩ y
   ⊑ₛ-≃-⊑-at i = ⊑ₛ-≃-⊑ where open is-locally-small (ls i)
   _⊑ₛ⟨∞⟩_ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩ → 𝓥 ̇
   σ ⊑ₛ⟨∞⟩ τ = (i : I) → ⦅ σ ⦆ i ⊑ₛ⟨ i ⟩ ⦅ τ ⦆ i
   γ : {σ τ : ⟨ 𝓓∞ ⟩} → (σ ⊑ₛ⟨∞⟩ τ) ≃ (σ ⊑⟨ 𝓓∞ ⟩ τ)
   γ {σ} {τ} = Π-cong fe fe (λ i → ⊑ₛ-≃-⊑-at i)

\end{code}

Next we are going to show that taking the bilimit is closed under structural
continuity/algebraicity and having a small (compact) basis.

To ease the development we first develop some generalities. Given I-indexed
families αᵢ from Jᵢ into 𝓓ᵢ, we construct a family α∞ from Σ J to 𝓓∞ and present
criteria for calculating its supremum and for it being directed.

\begin{code}

 module 𝓓∞-family
         (J : (i : I) → 𝓥 ̇ )
         (α : (i : I) → J i → ⟨ 𝓓 i ⟩)
        where

  J∞ : 𝓥 ̇
  J∞ = Σ i ꞉ I , J i

  J∞-is-inhabited : ((i : I) → ∥ J i ∥) → ∥ J∞ ∥
  J∞-is-inhabited J-inh =
   ∥∥-rec ∥∥-is-prop (λ i → ∥∥-functor (λ j → (i , j)) (J-inh i)) I-inhabited

  α∞ : J∞ → ⟨ 𝓓∞ ⟩
  α∞ (i , j) = ε∞ i (α i j)

  α∞-is-sup-lemma : (σ : ⟨ 𝓓∞ ⟩) (δ : ((i : I) → is-Directed (𝓓 i) (α i)))
                  → ((i : I) → ∐ (𝓓 i) (δ i) ＝ ⦅ σ ⦆ i)
                  → is-sup _≼_ σ α∞
  α∞-is-sup-lemma σ δ e =
   transport (λ - → is-sup _≼_ - α∞) (σ-is-sup ⁻¹) (ub , lb-of-ubs)
    where
     δ' : (i : I) → is-Directed 𝓓∞ (ε∞ i ∘ α i)
     δ' i = image-is-directed' (𝓓 i) 𝓓∞ (ε∞' i) (δ i)
     e₁ : ε∞-family σ ＝ (λ i → ε∞ i (∐ (𝓓 i) (δ i)))
     e₁ = dfunext fe (λ i → ap (ε∞ i) (e i) ⁻¹)
     e₂ : (λ i → ε∞ i (∐ (𝓓 i) (δ i))) ＝ (λ i → ∐ 𝓓∞ (δ' i))
     e₂ = dfunext fe (λ i → continuous-∐-＝ (𝓓 i) 𝓓∞ (ε∞' i) (δ i))

     δ₁ : is-Directed 𝓓∞ (λ (i : I) → ε∞ i (∐ (𝓓 i) (δ i)))
     δ₁ = transport (is-Directed 𝓓∞) e₁ (ε∞-family-is-directed σ)
     δ₂ : is-Directed 𝓓∞ (λ i → ∐ 𝓓∞ (δ' i))
     δ₂ = transport (is-Directed 𝓓∞) e₂ δ₁

     σ-is-sup = σ                              ＝⟨ ∐-of-ε∞s σ ⟩
                ∐ 𝓓∞ (ε∞-family-is-directed σ) ＝⟨ ⦅1⦆ ⟩
                ∐ 𝓓∞ δ₁                        ＝⟨ ⦅2⦆ ⟩
                ∐ 𝓓∞ δ₂                        ∎
      where
       ⦅1⦆ = ∐-family-＝ 𝓓∞ e₁ (ε∞-family-is-directed σ)
       ⦅2⦆ = ∐-family-＝ 𝓓∞ e₂ δ₁

     ub : (k : J∞) → α∞ k ≼ ∐ 𝓓∞ δ₂
     ub (i , j) = transitivity 𝓓∞ (α∞ (i , j)) (∐ 𝓓∞ (δ' i)) (∐ 𝓓∞ δ₂) ⦅1⦆ ⦅2⦆
      where
       ⦅1⦆ : α∞ (i , j) ⊑⟨ 𝓓∞ ⟩ ∐ 𝓓∞ (δ' i)
       ⦅1⦆ = ∐-is-upperbound 𝓓∞ (δ' i) j
       ⦅2⦆ : ∐ 𝓓∞ (δ' i) ⊑⟨ 𝓓∞ ⟩ ∐ 𝓓∞ δ₂
       ⦅2⦆ = ∐-is-upperbound 𝓓∞ δ₂ i

     lb-of-ubs : is-lowerbound-of-upperbounds _≼_ (∐ 𝓓∞ δ₂) α∞
     lb-of-ubs τ τ-is-ub = ∐-is-lowerbound-of-upperbounds 𝓓∞ δ₂ τ
                            (λ i → ∐-is-lowerbound-of-upperbounds 𝓓∞ (δ' i) τ
                                    (λ j → τ-is-ub (i , j)))

  α∞-is-directed-sup-lemma : (σ : ⟨ 𝓓∞ ⟩)
                             (δ : ((i : I) → is-Directed (𝓓 i) (α i)))
                           → ((i : I) → ∐ (𝓓 i) (δ i) ＝ ⦅ σ ⦆ i)
                           → (δ∞ : is-Directed 𝓓∞ α∞) → ∐ 𝓓∞ δ∞ ＝ σ
  α∞-is-directed-sup-lemma σ δ e δ∞ =
   antisymmetry 𝓓∞ (∐ 𝓓∞ δ∞) σ
                (∐-is-lowerbound-of-upperbounds 𝓓∞ δ∞ σ
                  (sup-is-upperbound _≼_ σ-is-sup))
                (sup-is-lowerbound-of-upperbounds _≼_ σ-is-sup (∐ 𝓓∞ δ∞)
                  (∐-is-upperbound 𝓓∞ δ∞))
    where
     σ-is-sup : is-sup _≼_ σ α∞
     σ-is-sup = α∞-is-sup-lemma σ δ e

  α∞-is-directed-lemma : (σ : ⟨ 𝓓∞ ⟩) (δ : ((i : I) → is-Directed (𝓓 i) (α i)))
                       → ((i : I) → ∐ (𝓓 i) (δ i) ＝ ⦅ σ ⦆ i)
                       → ((i : I) (j : J i) → α i j ≪⟨ 𝓓 i ⟩ ⦅ σ ⦆ i)
                       → is-Directed 𝓓∞ α∞
  α∞-is-directed-lemma σ δ sup αs-wb = Ind-∐-is-directed ε∞-after-α dir
   where
    open import DomainTheory.BasesAndContinuity.IndCompletion pt fe 𝓥
    open Ind-completion 𝓓∞
    δ' : (i : I) → is-Directed 𝓓∞ (ε∞ i ∘ α i)
    δ' i = image-is-directed' (𝓓 i) 𝓓∞ (ε∞' i) (δ i)
    ε∞-after-α : I → Ind
    ε∞-after-α i = J i , ε∞ i ∘ α i , δ' i
    dir : is-directed _≲_ ε∞-after-α
    dir = I-inhabited , semidir
     where
      semidir : is-semidirected _≲_ ε∞-after-α
      semidir i₁ i₂ =
       ∥∥-functor (λ (i , l₁ , l₂) → i , cofinality-lemma l₁
                                       , cofinality-lemma l₂)
                  (I-semidirected i₁ i₂)
       where
        cofinality-lemma : {i i' : I} → i ⊑ i' → ε∞-after-α i ≲ ε∞-after-α i'
        cofinality-lemma {i} {i'} l j =
         ∥∥-functor lem (wb (J i') (α i') (δ i') (＝-to-⊒ (𝓓 i') (sup i')))
          where
           lem : (Σ j' ꞉ J i' , ε l (α i j) ⊑⟨ 𝓓 i' ⟩ α i' j')
               → (Σ j' ꞉ J i' , ε∞ i (α i j) ⊑⟨ 𝓓∞ ⟩ ε∞ i' (α i' j'))
           lem (j' , u) = j' , transitivity 𝓓∞ (ε∞ i (α i j))
                                               (ε∞ i' (ε l (α i j)))
                                               (ε∞ i' (α i' j'))
                                               ⦅1⦆ ⦅2⦆
            where
             ⦅1⦆ : ε∞ i (α i j) ⊑⟨ 𝓓∞ ⟩ ε∞ i' (ε l (α i j))
             ⦅1⦆ = ＝-to-⊑ 𝓓∞ ((ε∞-commutes-with-εs i i' l (α i j)) ⁻¹)
             ⦅2⦆ : ε∞ i' (ε l (α i j)) ⊑⟨ 𝓓∞ ⟩ ε∞ i' (α i' j')
             ⦅2⦆ = monotone-if-continuous (𝓓 i') 𝓓∞ (ε∞' i')
                    (ε l (α i j)) (α i' j') u
           wb : ε l (α i j) ≪⟨ 𝓓 i' ⟩ ⦅ σ ⦆ i'
           wb = ≪-⊑-to-≪ (𝓓 i') wb' ineq
            where
             wb' : ε l (α i j) ≪⟨ 𝓓 i' ⟩ ε l (⦅ σ ⦆ i)
             wb' = embeddings-preserve-≪ (𝓓 i) (𝓓 i')
                                         (ε l) (ε-is-continuous l)
                                         (π l) (π-is-continuous l)
                                         (ε-section-of-π l) (επ-deflation l)
                                         (α i j) (⦅ σ ⦆ i) (αs-wb i j)
             ineq = ε l (π∞ i σ)        ⊑⟨ 𝓓 i' ⟩[ ⦅1⦆ ]
                    ε l (π l (π∞ i' σ)) ⊑⟨ 𝓓 i' ⟩[ ⦅2⦆ ]
                    ⦅ σ ⦆ i'            ∎⟨ 𝓓 i' ⟩
              where
               ⦅1⦆ = ＝-to-⊑ (𝓓 i') (ap (ε l) ((π∞-commutes-with-πs i i' l σ) ⁻¹))
               ⦅2⦆ = επ-deflation l (π∞ i' σ)

\end{code}

The construction that defines the family α∞ into 𝓓∞ preserves the way-below
relation and compactness in a sense made precise below.

\begin{code}

  α∞-is-way-below : (σ : ⟨ 𝓓∞ ⟩)
                  → ((i : I) (j : J i) → α i j ≪⟨ 𝓓 i ⟩ ⦅ σ ⦆ i)
                  → (j : J∞) → α∞ j ≪⟨ 𝓓∞ ⟩ σ
  α∞-is-way-below σ wb (i , j) = ≪-⊑-to-≪ 𝓓∞ lem (ε∞π∞-deflation σ)
   where
    lem : ε∞ i (α i j) ≪⟨ 𝓓∞ ⟩ ε∞ i (π∞ i σ)
    lem = embeddings-preserve-≪ (𝓓 i) 𝓓∞
           (ε∞ i) (ε∞-is-continuous i)
           (π∞ i) (π∞-is-continuous i)
           ε∞-section-of-π∞ ε∞π∞-deflation
           (α i j) (π∞ i σ)
           (wb i j)

  α∞-is-compact : ((i : I) (j : J i) → is-compact (𝓓 i) (α i j))
                → (j : J∞) → is-compact 𝓓∞ (α∞ j)
  α∞-is-compact κ (i , j) = embeddings-preserve-compactness (𝓓 i) 𝓓∞
                             (ε∞ i) (ε∞-is-continuous i)
                             (π∞ i) (π∞-is-continuous i)
                             ε∞-section-of-π∞ ε∞π∞-deflation
                             (α i j) (κ i j)

\end{code}

It is now fairly straightforward to prove that if each 𝓓ᵢ is structurally
continuous, then so is its bilimit 𝓓∞.

Note how we don't expect to have a similar result for ordinary continuity,
because this seems to need instances of the axiom of choice in general.

\begin{code}

 𝓓∞-structurally-continuous : ((i : I) → structurally-continuous (𝓓 i))
                            → structurally-continuous 𝓓∞
 𝓓∞-structurally-continuous 𝓒 =
  record
   { index-of-approximating-family     = J∞⁺
   ; approximating-family              = α∞⁺
   ; approximating-family-is-directed  = α∞⁺-is-directed
   ; approximating-family-is-way-below = α∞⁺-is-way-below
   ; approximating-family-∐-＝          = α∞⁺-∐-＝
   }
   where
    open structurally-continuous
    J : (i : I) → ⟨ 𝓓 i ⟩ → 𝓥 ̇
    J i = index-of-approximating-family (𝓒 i)
    α : (i : I) (x : ⟨ 𝓓 i ⟩) → J i x → ⟨ 𝓓 i ⟩
    α i = approximating-family (𝓒 i)
    δ : (i : I) (x : ⟨ 𝓓 i ⟩) → is-Directed (𝓓 i) (α i x)
    δ i = approximating-family-is-directed (𝓒 i)

    J⁺ : (σ : ⟨ 𝓓∞ ⟩) → I → 𝓥 ̇
    J⁺ σ i = J i (⦅ σ ⦆ i)
    α⁺ : (σ : ⟨ 𝓓∞ ⟩) (i : I) → J⁺ σ i → ⟨ 𝓓 i ⟩
    α⁺ σ i = α i (⦅ σ ⦆ i)

    module _
            (σ : ⟨ 𝓓∞ ⟩)
           where

     open 𝓓∞-family (J⁺ σ) (α⁺ σ)

     J∞⁺ :  𝓥 ̇
     J∞⁺ = J∞
     α∞⁺ : J∞⁺ → ⟨ 𝓓∞ ⟩
     α∞⁺ = α∞
     α∞⁺-is-way-below : is-way-upperbound 𝓓∞ σ α∞⁺
     α∞⁺-is-way-below = α∞-is-way-below σ
                         (λ i j → approximating-family-is-way-below (𝓒 i)
                                   (⦅ σ ⦆ i) j)
     α∞⁺-is-directed : is-Directed 𝓓∞ α∞⁺
     α∞⁺-is-directed = α∞-is-directed-lemma σ
                        (λ i → δ i (⦅ σ ⦆ i))
                        (λ i → approximating-family-∐-＝ (𝓒 i) (⦅ σ ⦆ i))
                        (λ i → approximating-family-is-way-below (𝓒 i) (⦅ σ ⦆ i))
     α∞⁺-∐-＝ : ∐ 𝓓∞ α∞⁺-is-directed ＝ σ
     α∞⁺-∐-＝ = α∞-is-directed-sup-lemma σ
                (λ i → δ i (⦅ σ ⦆ i))
                (λ i → approximating-family-∐-＝ (𝓒 i) (⦅ σ ⦆ i))
                α∞⁺-is-directed

\end{code}

Similarly, if each 𝓓ᵢ is structurally algebraic then so is its bilimit 𝓓∞.

\begin{code}

 𝓓∞-structurally-algebraic : ((i : I) → structurally-algebraic (𝓓 i))
                           → structurally-algebraic 𝓓∞
 𝓓∞-structurally-algebraic 𝓐 =
  record
   { index-of-compact-family    = index-of-approximating-family C∞
   ; compact-family             = approximating-family C∞
   ; compact-family-is-directed = approximating-family-is-directed C∞
   ; compact-family-is-compact  = γ
   ; compact-family-∐-＝         = approximating-family-∐-＝ C∞
   }
   where
    open structurally-continuous
    open structurally-algebraic
    𝓒 : (i : I) → structurally-continuous (𝓓 i)
    𝓒 i = structurally-continuous-if-structurally-algebraic (𝓓 i) (𝓐 i)
    C∞ : structurally-continuous 𝓓∞
    C∞ = 𝓓∞-structurally-continuous 𝓒
    J∞ : ⟨ 𝓓∞ ⟩ → 𝓥 ̇
    J∞ = index-of-approximating-family C∞
    α∞ : (σ : ⟨ 𝓓∞ ⟩) → J∞ σ → ⟨ 𝓓∞ ⟩
    α∞ = approximating-family C∞
    γ : (σ : ⟨ 𝓓∞ ⟩) (j : J∞ σ) → is-compact 𝓓∞ (α∞ σ j)
    γ σ (i , j) = embeddings-preserve-compactness (𝓓 i) 𝓓∞
                   (ε∞ i) (ε∞-is-continuous i) (π∞ i) (π∞-is-continuous i)
                   ε∞-section-of-π∞ ε∞π∞-deflation
                   (compact-family (𝓐 i) (⦅ σ ⦆ i) j)
                   (compact-family-is-compact (𝓐 i) (⦅ σ ⦆ i) j)

\end{code}

With a little bit more work, we can show that if each 𝓓ᵢ comes equipped with a
small (compact) basis, then the bilimit 𝓓∞ does too.

\begin{code}

 𝓓∞-has-small-basis : ((i : I) → has-specified-small-basis (𝓓 i))
                    → has-specified-small-basis 𝓓∞
 𝓓∞-has-small-basis 𝓑 = (B∞ , β∞ , β∞-is-small-basis)
  where
   B : I → 𝓥 ̇
   B i = pr₁ (𝓑 i)
   β : (i : I) → B i → ⟨ 𝓓 i ⟩
   β i = pr₁ (pr₂ (𝓑 i))
   β-is-small-basis : (i : I) → is-small-basis (𝓓 i) (β i)
   β-is-small-basis i = pr₂ (pr₂ (𝓑 i))
   B∞ : 𝓥 ̇
   B∞ = Σ i ꞉ I , B i
   β∞ : B∞ → ⟨ 𝓓∞ ⟩
   β∞ (i , b) = ε∞ i (β i b)

   𝓓s-are-locally-small : (i : I) → is-locally-small (𝓓 i)
   𝓓s-are-locally-small i = locally-small-if-small-basis (𝓓 i) (β i)
                             (β-is-small-basis i)

   𝓓s-are-structurally-continuous : (i : I) → structurally-continuous (𝓓 i)
   𝓓s-are-structurally-continuous i =
    structurally-continuous-if-specified-small-basis (𝓓 i)
     (B i , β i , β-is-small-basis i)

   β∞-is-small-basis : is-small-basis 𝓓∞ β∞
   β∞-is-small-basis =
    record
     { ≪ᴮ-is-small    = lemma₁
     ; ↡ᴮ-is-directed = lemma₂
     ; ↡ᴮ-is-sup      = lemma₃
     }
     where
      open is-small-basis

      lemma₁ : (σ : ⟨ 𝓓∞ ⟩) (b : B∞) → is-small (β∞ b ≪⟨ 𝓓∞ ⟩ σ)
      lemma₁ σ (i , b) =
       ≪-is-small-valued-str 𝓓∞
        (𝓓∞-structurally-continuous 𝓓s-are-structurally-continuous)
        (𝓓∞-is-locally-small 𝓓s-are-locally-small)
        (β∞ (i , b)) σ

      module _
              (σ : ⟨ 𝓓∞ ⟩)
             where

       ↡ᴮₛ⁺ : (i : I) → 𝓥 ̇
       ↡ᴮₛ⁺ i = ↡ᴮₛ (β-is-small-basis i) (⦅ σ ⦆ i)
       ↡ιₛ⁺ : (i : I) → ↡ᴮₛ⁺ i → ⟨ 𝓓 i ⟩
       ↡ιₛ⁺ i = ↡-inclusionₛ (β-is-small-basis i) (⦅ σ ⦆ i)
       open 𝓓∞-family ↡ᴮₛ⁺ ↡ιₛ⁺

       ι : J∞ → ↡ᴮ 𝓓∞ β∞ σ
       ι (i , b , u) = ((i , b) , v)
        where
         v : ε∞ i (β i b) ≪⟨ 𝓓∞ ⟩ σ
         v = ≪-⊑-to-≪ 𝓓∞ w (ε∞π∞-deflation σ)
          where
           w : ε∞ i (β i b) ≪⟨ 𝓓∞ ⟩ ε∞ i (⦅ σ ⦆ i)
           w = embeddings-preserve-≪ (𝓓 i) 𝓓∞
                (ε∞ i) (ε∞-is-continuous i) (π∞ i) (π∞-is-continuous i)
                ε∞-section-of-π∞ ε∞π∞-deflation
                (β i b) (⦅ σ ⦆ i) (≪ᴮₛ-to-≪ᴮ (β-is-small-basis i) u)

       sublemma₁ : is-Directed 𝓓∞ (↡-inclusion 𝓓∞ β∞ σ ∘ ι)
       sublemma₁ = α∞-is-directed-lemma σ
                    (λ i → ↡ᴮₛ-is-directed (β-is-small-basis i) (⦅ σ ⦆ i))
                    (λ i → ↡ᴮₛ-∐-＝ (β-is-small-basis i) (⦅ σ ⦆ i))
                    (λ i → ↡ᴮₛ-is-way-below (β-is-small-basis i) (⦅ σ ⦆ i))

       sublemma₂ : σ ＝ ∐ 𝓓∞ sublemma₁
       sublemma₂ = (α∞-is-directed-sup-lemma σ δs es sublemma₁) ⁻¹
        where
         δs : (i : I) → is-Directed (𝓓 i) (↡-inclusionₛ (β-is-small-basis i) (⦅ σ ⦆ i))
         δs i = ↡ᴮₛ-is-directed (β-is-small-basis i) (⦅ σ ⦆ i)
         es : (i : I) → ∐ (𝓓 i) (δs i) ＝ ⦅ σ ⦆ i
         es i = ↡ᴮₛ-∐-＝ (β-is-small-basis i) (⦅ σ ⦆ i)

       lemma₂ : is-Directed 𝓓∞ (↡-inclusion 𝓓∞ β∞ σ)
       lemma₂ = ↡ᴮ-directedness-criterion 𝓓∞ β∞ σ ι
                 sublemma₁ (＝-to-⊑ 𝓓∞ sublemma₂)

       lemma₃ : is-sup (underlying-order 𝓓∞) σ (↡-inclusion 𝓓∞ β∞ σ)
       lemma₃ = ↡ᴮ-sup-criterion 𝓓∞ β∞ σ ι claim
        where
         claim : is-sup (underlying-order 𝓓∞) σ (↡-inclusion 𝓓∞ β∞ σ ∘ ι)
         claim =
          transport (λ - → is-sup (underlying-order 𝓓∞) - (↡-inclusion 𝓓∞ β∞ σ ∘ ι))
                    (sublemma₂ ⁻¹)
                    (∐-is-sup 𝓓∞ sublemma₁)

 𝓓∞-has-small-compact-basis :
    ((i : I) → has-specified-small-compact-basis (𝓓 i))
  → has-specified-small-compact-basis 𝓓∞
 𝓓∞-has-small-compact-basis κ = (B∞ , β∞ , γ)
  where
   B : (i : I) → 𝓥 ̇
   B i = pr₁ (κ i)
   β : (i : I) → B i → ⟨ 𝓓 i ⟩
   β i = pr₁ (pr₂ (κ i))
   β-is-small-compact-basis : (i : I) → is-small-compact-basis (𝓓 i) (β i)
   β-is-small-compact-basis i = pr₂ (pr₂ (κ i))
   β-is-small-basis : (i : I) → is-small-basis (𝓓 i) (β i)
   β-is-small-basis i = compact-basis-is-basis (𝓓 i) (β i)
                         (β-is-small-compact-basis i)

   𝔹 : has-specified-small-basis 𝓓∞
   𝔹 = 𝓓∞-has-small-basis (λ i → (B i , β i , β-is-small-basis i))
   B∞ : 𝓥 ̇
   B∞ = pr₁ 𝔹
   β∞ : B∞ → ⟨ 𝓓∞ ⟩
   β∞ = pr₁ (pr₂ 𝔹)
   β∞-is-small-basis : is-small-basis 𝓓∞ β∞
   β∞-is-small-basis = pr₂ (pr₂ 𝔹)

   γ : is-small-compact-basis 𝓓∞ β∞
   γ = small-and-compact-basis 𝓓∞ β∞ β∞-is-small-basis β∞-is-compact
    where
     open is-small-compact-basis
     β∞-is-compact : (b : B∞) → is-compact 𝓓∞ (β∞ b)
     β∞-is-compact (i , b) = embeddings-preserve-compactness (𝓓 i) 𝓓∞
                              (ε∞ i) (ε∞-is-continuous i)
                              (π∞ i) (π∞-is-continuous i)
                              ε∞-section-of-π∞ ε∞π∞-deflation
                              (β i b)
                              (basis-is-compact (β-is-small-compact-basis i) b)

\end{code}
