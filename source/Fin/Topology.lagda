Martin Escardo, November 2019

Other interesting uses of the types Fin n is in the file
https://www.cs.bham.ac.uk/~mhe/TypeTopology/ArithmeticViaEquivalence.html
which proves commutativity of addition and multiplication, and more,
using the corresponding properties for (finite) types.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Fin.Topology where

open import Fin.Bishop
open import Fin.Properties
open import Fin.Type
open import MLTT.Spartan
open import MLTT.SpartanList
open import TypeTopology.CompactTypes
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ClassicalLogic
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

Recall that a type is discrete if it has decidable equality.

\begin{code}

Fin-is-discrete : {n : ℕ} → is-discrete (Fin n)
Fin-is-discrete {0}      = 𝟘-is-discrete
Fin-is-discrete {succ n} = +-is-discrete (Fin-is-discrete {n}) 𝟙-is-discrete

Fin-is-set : {n : ℕ} → is-set (Fin n)
Fin-is-set = discrete-types-are-sets Fin-is-discrete

\end{code}

The type Fin n is compact, or exhaustively searchable.

\begin{code}

Fin-Compact : {n : ℕ} → is-Compact (Fin n) {𝓤}
Fin-Compact {𝓤} {0}      = 𝟘-is-Compact
Fin-Compact {𝓤} {succ n} = +-is-Compact (Fin-Compact {𝓤} {n}) 𝟙-is-Compact


Fin-Π-Compact : (n : ℕ) → is-Π-Compact (Fin n) {𝓤}
Fin-Π-Compact n = Σ-Compact-types-are-Π-Compact (Fin n) Fin-Compact


Fin-Compact∙ : (n : ℕ) → is-Compact∙ (Fin (succ n)) {𝓤}
Fin-Compact∙ n = Compact-pointed-gives-Compact∙ Fin-Compact 𝟎

\end{code}


Added 15th December 2019.

If the type X i is compact for every i : Fin n, then the product type
(i : Fin n) → X i is also compact.

\begin{code}


finite-product-compact : (n : ℕ) (X : Fin n → 𝓤 ̇ )
                       → ((i : Fin n) → is-Compact (X i) {𝓤})
                       → is-Compact (vec n X) {𝓤}
finite-product-compact zero     X c = 𝟙-is-Compact
finite-product-compact (succ n) X c = ×-is-Compact
                                       (c 𝟎)
                                       (finite-product-compact n (X ∘ suc) (c ∘ suc))

finitely-indexed-product-compact : funext 𝓤₀ 𝓤
                                 → (n : ℕ) (X : Fin n → 𝓤 ̇ )
                                 → ((i : Fin n) → is-Compact (X i))
                                 → is-Compact ((i : Fin n) → X i)
finitely-indexed-product-compact fe n X c = Compact-closed-under-≃
                                            (vec-≃ fe n)
                                            (finite-product-compact n X c)

\end{code}

Added 4th September 2026. The same holds for compact pointedness.

\begin{code}

finite-product-compact∙ : (n : ℕ) (X : Fin n → 𝓤 ̇ )
                        → ((i : Fin n) → is-compact∙ (X i))
                        → is-compact∙ (vec n X)
finite-product-compact∙ zero     X c = 𝟙-is-compact∙
finite-product-compact∙ (succ n) X c =
 binary-Tychonoff (c 𝟎) (finite-product-compact∙ n (X ∘ suc) (c ∘ suc))

finitely-indexed-product-compact∙ : funext 𝓤₀ 𝓤
                                  → (n : ℕ) (X : Fin n → 𝓤 ̇ )
                                  → ((i : Fin n) → is-compact∙ (X i))
                                  → is-compact∙ ((i : Fin n) → X i)
finitely-indexed-product-compact∙ fe n X c =
 compact∙-types-are-closed-under-equiv
  (vec-≃ fe n)
  (finite-product-compact∙ n X c)

\end{code}

End of addition.

Finite types are compact, or exhaustively searchable.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open CompactTypesPT pt
 open finiteness pt

 finite-∥Compact∥ : {X : 𝓤 ̇ } → is-finite X → ∥ is-Compact X {𝓥} ∥
 finite-∥Compact∥ {𝓤} {𝓥} {X} (n , α) =
  ∥∥-functor (λ (e : X ≃ Fin n) → Compact-closed-under-≃ (≃-sym e) Fin-Compact) α

 finite-types-are-∃-Compact : Fun-Ext → {X : 𝓤 ̇ } → is-finite X → is-∃-Compact X {𝓥}
 finite-types-are-∃-Compact fe φ = ∥Compact∥-gives-∃-Compact fe (finite-∥Compact∥ φ)

\end{code}

Finite types are discrete and hence sets:

\begin{code}

 finite-types-are-discrete : FunExt → {X : 𝓤 ̇ } → is-finite X → is-discrete X
 finite-types-are-discrete fe {X} (n , s) = ∥∥-rec (being-discrete-is-prop fe) γ s
  where
   γ : X ≃ Fin n → is-discrete X
   γ (f , e) = lc-maps-reflect-discreteness f (equivs-are-lc f e) Fin-is-discrete

 finite-types-are-sets : FunExt → {X : 𝓤 ̇ } → is-finite X → is-set X
 finite-types-are-sets fe φ = discrete-types-are-sets (finite-types-are-discrete fe φ)

 finite-propositions-are-decidable' : Fun-Ext
                                    → {P : 𝓤 ̇ }
                                    → is-prop P
                                    → is-finite P
                                    → is-decidable P
 finite-propositions-are-decidable' fe i j =
  ∃-Compact-propositions-are-decidable i (finite-types-are-∃-Compact fe j)

 finite-propositions-are-decidable : {P : 𝓤 ̇ }
                                   → is-prop P
                                   → is-finite P
                                   → is-decidable P
 finite-propositions-are-decidable {𝓤} {P} i (0 , s) = inr γ
  where
   γ : P → 𝟘
   γ p = ∥∥-rec 𝟘-is-prop (λ (f , _) → f p) s

 finite-propositions-are-decidable {𝓤} {P} i (succ n , s) = inl γ
  where
   γ : P
   γ = ∥∥-rec i (λ 𝕗 → ⌜ 𝕗 ⌝⁻¹ 𝟎) s

 summands-of-finite-sum-always-finite-gives-EM
  : ((𝓤 𝓥 : Universe) (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
          → is-finite (Σ A)
          → (x : X) → is-finite (A x))

  → (𝓦 : Universe) → funext 𝓦 𝓦 → propext 𝓦 → EM 𝓦
 summands-of-finite-sum-always-finite-gives-EM ϕ 𝓦 fe pe P i
  = γ
  where
   X : 𝓦 ⁺ ̇
   X = Ω 𝓦

   A : X → 𝓦 ̇
   A p = p holds

   e : Σ A ≃ (Σ P ꞉ 𝓦 ̇ , is-prop P × P)
   e = Σ-assoc

   s : is-singleton (Σ A)
   s = equiv-to-singleton e (the-true-props-form-a-singleton-type fe pe)

   f : Σ A ≃ Fin 1
   f = singleton-≃ s Fin1-is-singleton

   j : is-finite (Σ A)
   j = 1 , ∣ f ∣

   k : is-finite P
   k = ϕ (𝓦 ⁺) 𝓦 X A j (P , i)

   γ : P + ¬ P
   γ = finite-propositions-are-decidable i k

\end{code}
