Martin Escardo, 21st October 2026.

We show that the compact totally separated interpretation Κ of the
Brouwer ordinal codes, defined in the module
Ordinals.BrouwerCodesDiscreteAndCompactInterpretations, gives Stone
types, in the sense of the module TypeTopology.StoneTypes, assuming
that ¬ WLPO holds.

The hypothesis ¬ WLPO is used for the limit constructor, and it can't
be dropped, as discussed in the module TypeTopology.StoneTypes,
because the code L (λ n → Z) is interpreted as a type equivalent to ℕ∞.
The closure properties of the above module handle the other two
constructors.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module Ordinals.BrouwerCodesGiveStoneTypes
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe

 fe₀ : funext₀
 fe₀ = fe

open import CoNaturals.Type
open import InjectiveTypes.Blackboard fe'
open import Notation.CanonicalMap
open import Taboos.WLPO
open import TypeTopology.CompactTypes
open import TypeTopology.SquashedSum fe'
open import TypeTopology.StoneTypes fe pt
open import UF.DiscreteAndSeparated

\end{code}

We begin by considering the limit step. We work with the construction Σ¹ X
of the module TypeTopology.SquashedSum, which is the sum of the right
Kan extension X / ι of X along the embedding ι of ℕ into ℕ∞. The fiber
of the extension over a point u of ℕ∞ is the product of the types X n
indexed by the witnesses that u is finite with size n, so that the
fiber over a finite point ι k amounts to X k and the fiber over ∞ is a
singleton.

\begin{code}

module _ (X : ℕ → 𝓤 ̇ )
         (κ : (n : ℕ) → is-compact∙ (X n))
         (ζ : (n : ℕ) → is-pre-stone-type (X n))
       where

 private
  Y : ℕ∞ → 𝓤 ̇
  Y = X / ι

 extension-is-stone-type : (u : ℕ∞) → is-stone-type (Y u)
 extension-is-stone-type u =
  prop-indexed-products-are-stone-types
   (ℕ-to-ℕ∞-is-embedding fe₀ u)
   (λ ψ → κ (size ψ))
   (λ ψ → ζ (size ψ))

 private
  component : (v : ℕ∞) (y : Y v) (k : ℕ) → is-decidable (ι k ＝ v) → X k
  component v y k (inl e) = y (k , e)
  component v y k (inr _) = compact∙-types-are-pointed (κ k)

  transfer : (u v : ℕ∞) → Y v → Y u
  transfer u v y ψ = component v y (size ψ) (finite-isolated fe₀ (size ψ) v)

  transfer-at-u : (u : ℕ∞) (y : Y u) → transfer u u y ＝ y
  transfer-at-u u y = dfunext fe I
   where
    I : (ψ : is-finite u) → transfer u u y ψ ＝ y ψ
    I ψ = II (finite-isolated fe₀ (size ψ) u)
     where
      II : (d : is-decidable (ι (size ψ) ＝ u)) → component u y (size ψ) d ＝ y ψ
      II (inl e) = ap (λ - → y (size ψ , -))
                    (ℕ∞-is-set fe₀ e (size-property ψ))
      II (inr ν) = 𝟘-elim (ν (size-property ψ))

 extension-has-extendable-clopens : has-extendable-clopens Y
 extension-has-extendable-clopens u A = B , I
  where
   B : Clopen (Σ¹ X)
   B (v , y) = transfer u v y ϵ A

   I : (y : Y u) → (u , y) ϵ B ＝ y ϵ A
   I y = ap A (transfer-at-u u y)

\end{code}

So the squashed sum of a family of pointed compact pre-Stone types is
a Stone type when ¬ WLPO holds.

\begin{code}

 Σ¹-is-stone-type : ¬ WLPO → is-stone-type (Σ¹ X)
 Σ¹-is-stone-type nwlpo =
  Σ-is-stone-type-if-family-has-extendable-clopens
   (ℕ∞-is-stone-type nwlpo)
   extension-is-stone-type
   extension-has-extendable-clopens

\end{code}

The sum of a family over the two-point type, which is the form that a
binary sum takes in ordinal arithmetic, is a Stone type by the closure
under Σ again, the base being a discrete Stone type.

\begin{code}

Σ-over-two-is-stone-type
 : (A : 𝟙 {𝓤} + 𝟙 {𝓥} → 𝓦 ̇ )
 → is-stone-type (A (inl ⋆))
 → is-stone-type (A (inr ⋆))
 → is-stone-type (Σ A)
Σ-over-two-is-stone-type {𝓤} {𝓥} {𝓦} A ζ₀ ζ₁
 = Σ-is-stone-type-if-family-has-extendable-clopens
    (+-is-stone-type 𝟙-is-stone-type 𝟙-is-stone-type)
    I
    (discrete-bases-extend-clopens d)
 where
  d : is-discrete (𝟙 {𝓤} + 𝟙 {𝓥})
  d = +-is-discrete 𝟙-is-discrete 𝟙-is-discrete

  I : (x : 𝟙 {𝓤} + 𝟙 {𝓥}) → is-stone-type (A x)
  I (inl ⋆) = ζ₀
  I (inr ⋆) = ζ₁

\end{code}

The underlying type of a successor is a sum of a family over the
two-point type, and that of a limit is the squashed sum. So the two
steps above, together with that for the one-point type of the module
TypeTopology.StoneTypes, give by induction on Brouwer codes that the Κ
interpretation produces Stone types.

\begin{code}

open import Ordinals.BrouwerCodes
open import Ordinals.BrouwerCodesDiscreteAndCompactInterpretations fe'
open import Ordinals.ToppedArithmetic fe'
open import Ordinals.ToppedType fe' -- for the Underlying instance
open import Ordinals.Underlying

Κ-is-stone-type : ¬ WLPO → (b : B) → is-stone-type ⟨ Κ b ⟩
Κ-is-stone-type nwlpo Z     = 𝟙-is-stone-type
Κ-is-stone-type nwlpo (S b) =
 Σ-over-two-is-stone-type
  (λ x → ⟨ cases (λ _ → Κ b) (λ _ → 𝟙ᵒ) x ⟩)
  (Κ-is-stone-type nwlpo b)
  𝟙-is-stone-type
Κ-is-stone-type nwlpo (L b) =
 Σ¹-is-stone-type
  (λ n → ⟨ Κ (b n) ⟩)
  (λ n → Κ-compact∙ (b n))
  (λ n → stone-types-are-pre-stone-types (Κ-is-stone-type nwlpo (b n)))
  nwlpo

\end{code}
