Martin Escardo, 13th June 2025

We repackage the definitions of algebraic injective and flabby
structure in a more convenient way for some purposes.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan

module InjectiveTypes.Repackaging
        {𝓦 : Universe}
        (D : 𝓦 ̇ )
       where

open import UF.Embeddings
open import UF.SubtypeClassifier

aflabby-structure : (𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓦 ̇
aflabby-structure 𝓤
 = Σ ⨆ ꞉ ((P : Ω 𝓤) → (P holds → D) → D)
       , ((P : Ω 𝓤) (f : P holds → D) (p : P holds) → ⨆ P f ＝ f p)

ainjective-structure : (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦 ̇
ainjective-structure 𝓤 𝓥
 = Σ _∣_ ꞉ ({X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → D) → (X ↪ Y) → (Y → D))
         , ({X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → D) (𝕛 : X ↪ Y) → (f ∣ 𝕛) ∘ ⌊ 𝕛 ⌋ ∼ f)

aflabby-structure-gives-ainjective-structure
 : aflabby-structure (𝓤 ⊔ 𝓥) → ainjective-structure 𝓤 𝓥
aflabby-structure-gives-ainjective-structure {𝓤} {𝓥} (⨆ , e)
 = _∣_ , e'
 where
  _∣_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → D) → (X ↪ Y) → (Y → D)
  (f ∣ 𝕛) y = ⨆ ((Fiber 𝕛 y)) (f ∘ pr₁)

  e' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → D) (𝕛 : X ↪ Y) → (f ∣ 𝕛) ∘ ⌊ 𝕛 ⌋ ∼ f
  e' f 𝕛 x = e (Fiber 𝕛 (⌊ 𝕛 ⌋ x)) (f ∘ pr₁) (x , refl)

ainjective-structure-gives-aflabby-structure
 : ainjective-structure 𝓤 𝓥 → aflabby-structure 𝓤
ainjective-structure-gives-aflabby-structure {𝓤} {𝓥} (_∣_ , e) = ⨆ , e'
 where
  ⨆ : (P : Ω 𝓤) → (P holds → D) → D
  ⨆ P f = (f ∣ embedding-to-𝟙) ⋆

  e' : (P : Ω 𝓤) (f : P holds → D) (p : P holds) → ⨆ P f ＝ f p
  e' P f = e f embedding-to-𝟙

\end{code}

We had already given (in InjectiveTypes.BlackBoard) conversions
between ainjective types and a flabby types. We now record that the
ones we gave here agree definitionally with those there, via the
"repackaging" equivalences gives below.

Unfortunately, InjectiveTypes has a global assumption of function
extensionality, which is not used for the definitions of algebraic
injective and flabby structure. Fortunately, we don't need to use the
proofs below (particularly because they are proved with refl), which
are here only for the purpose of emphasizing that we are working with
the same definitions repackaged in a different way.

\begin{code}

open import UF.FunExt
open import UF.Equiv

module _ (fe : FunExt) where

 open import InjectiveTypes.Blackboard fe

 ainjective-type-repackaging : ainjective-structure 𝓤 𝓥 ≃ ainjective-type D 𝓤 𝓥
 ainjective-type-repackaging =
  qinveq
   (λ (_∣_ , e) → λ {X} {Y} j i f → (f ∣ (j , i)) , e f (j , i))
   ((λ ainj →
       (λ {X} {Y} f 𝕛 → pr₁ (ainj ⌊ 𝕛 ⌋ ⌊ 𝕛 ⌋-is-embedding f)) ,
       (λ {X} {Y} f 𝕛 → pr₂ (ainj ⌊ 𝕛 ⌋ ⌊ 𝕛 ⌋-is-embedding f))) ,
    (λ _ → refl) ,
    (λ _ → refl))

 aflabby-repackaging : aflabby-structure 𝓤 ≃ aflabby D 𝓤
 aflabby-repackaging
  = qinveq
     (λ (⨆ , e) P i f → ⨆ (P , i) f , e (P , i) f)
     ((λ aflab →
        (λ P f → pr₁ (aflab (P holds) (holds-is-prop P) f)) ,
        (λ P f → pr₂ (aflab (P holds) (holds-is-prop P) f))) ,
      (λ _ → refl) ,
      (λ _ → refl))

\end{code}

TODO. Write the commutative squares corresponding to the following two
proofs as a comment.

\begin{code}

 ainjective-structure-gives-aflabby-structure-agreement
  : (s : ainjective-structure 𝓤 𝓥)
  → ⌜ aflabby-repackaging ⌝ (ainjective-structure-gives-aflabby-structure s)
  ＝ ainjective-types-are-aflabby D (⌜ ainjective-type-repackaging ⌝ s)
 ainjective-structure-gives-aflabby-structure-agreement s = refl

 \end{code}

 For the second one we need to do a manual eta expasion to deal with
 the way Agda works with implicit arguments, which gives unsolved
 constraints otherwise (this is a well known design issue).

 \begin{code}

 aflabby-structure-gives-ainjective-structure-agreement
  : (s : aflabby-structure 𝓤)
  → (λ {X Y : 𝓤 ̇} (j : X → Y)
     → ⌜ ainjective-type-repackaging ⌝ (aflabby-structure-gives-ainjective-structure s) {X} {Y} j)
  ＝ aflabby-types-are-ainjective D (⌜ aflabby-repackaging ⌝ s)
 aflabby-structure-gives-ainjective-structure-agreement s = refl

 \end{code}
