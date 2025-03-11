Martin Escardo 23 February 2023

The pre-univalence axiom, first suggested by Evan Cavallo in November
2017 [1] and then again by Peter Lumsdaine in August 2022
verbally to me.

[1] https://groups.google.com/g/homotopytypetheory/c/bKti7krHM-c/m/vxRU3FwADQAJ

The preunivalence axiom is a common generalization of the univalence
axiom and the K axiom.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.PreUnivalence where

open import MLTT.Spartan
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Retracts
open import UF.Sets
open import UF.Subsingletons
open import UF.Univalence

is-preunivalent : ∀ 𝓤 → 𝓤 ⁺ ̇
is-preunivalent 𝓤 = (X Y : 𝓤 ̇ ) → is-embedding (idtoeq X Y)

Preunivalence : 𝓤ω
Preunivalence = (𝓤 : Universe) → is-preunivalent 𝓤

univalence-gives-preunivalence : is-univalent 𝓤
                               → is-preunivalent 𝓤
univalence-gives-preunivalence ua X Y = equivs-are-embeddings
                                         (idtoeq X Y)
                                         (ua X Y)

Univalence-gives-Preunivalence : Univalence → Preunivalence
Univalence-gives-Preunivalence ua 𝓤 = univalence-gives-preunivalence (ua 𝓤)

K-gives-preunivalence : K-axiom 𝓤
                      → K-axiom (𝓤 ⁺)
                      → is-preunivalent 𝓤
K-gives-preunivalence {𝓤} k k' X Y e (p , _) (p' , _) =
 to-subtype-＝ (λ _ → k (X ≃ Y)) (k' (𝓤  ̇ )p p')

K-gives-Preunivalence : K-Axiom → Preunivalence
K-gives-Preunivalence k 𝓤 = K-gives-preunivalence (k 𝓤) (k (𝓤 ⁺))

is-strong-preunivalent : ∀ 𝓤 → 𝓤 ⁺ ̇
is-strong-preunivalent 𝓤 = (X : 𝓤 ̇ ) → is-set (Σ Y ꞉ 𝓤 ̇  , X ≃ Y)

funext-and-preunivalence-give-strong-preunivalence : ∀ {𝓤}
  → funext 𝓤 𝓤 → is-preunivalent 𝓤 → is-strong-preunivalent 𝓤
funext-and-preunivalence-give-strong-preunivalence {𝓤} fe preua X {Y , α} {Y' , α'} =
  retract-of-prop
    (to-Σ-＝ , from-Σ-＝ , tofrom-Σ-＝)
    (equiv-to-prop
      (Σ-cong λ p → (_ , ∙-is-equiv-left (expand-transport p)) ● shift-equiv α (idtoeq _ _ p) α')
      (preua _ _ (≃-sym α ● α')))
  where
  expand-transport : (p : Y ＝ Y') → α ● idtoeq Y Y' p ＝ transport (X ≃_) p α
  expand-transport refl = ≃-refl-right' fe fe fe α

  shift-equiv : {A B C : 𝓤 ̇ }
    (e : A ≃ B) (e' : B ≃ C) (e'' : A ≃ C)
    → (e ● e' ＝ e'') ≃ (e' ＝ ≃-sym e ● e'')
  shift-equiv e e' e'' =
    (e ● e' ＝ e'')                       ≃⟨ _ , ap-is-equiv (≃-sym e ●_) (pr₂ (≃-cong-left'' fe e)) ⟩
    (≃-sym e ● (e ● e') ＝ ≃-sym e ● e'') ≃⟨ ＝-cong-l _ _ (≃-assoc' fe fe fe (≃-sym e) e e') ⟩
    ((≃-sym e ● e) ● e' ＝ ≃-sym e ● e'') ≃⟨ ＝-cong-l _ _ (ap (_● e') (≃-sym-left-inverse' fe e)) ⟩
    (≃-refl _ ● e' ＝ ≃-sym e ● e'')      ≃⟨ ＝-cong-l _ _ (≃-refl-left' fe fe fe e') ⟩
    (e' ＝ ≃-sym e ● e'') ■

\end{code}
