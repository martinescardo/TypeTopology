Martin Escardo, July 2026.

Size notions for setoids.

The point of the setoid view is that the identity type plays no role,
with sameness given by the setoid relation. Accordingly, a setoid is
locally small when its relation, rather than its identity type, is
small-valued. The motivating example is the universe with type
equivalence as its relation. Since X ≃ Y already lives in 𝓤, the
universe setoid is locally small with no univalence assumption,
whereas the identity type X ＝ Y is not small without something such
as univalence.

A setoid is small when it is isomorphic to a setoid whose underlying
type and equivalence relation are both small.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EGroups.Size where

open import MLTT.Spartan
open import UF.Equiv
open import UF.Size

open import EGroups.Setoid

\end{code}

A setoid is locally 𝓦-small if each value of its relation is 𝓦-small.

\begin{code}

has-small-valued-relation : (S : Setoid 𝓤 𝓥) (𝓦 : Universe) → 𝓦 ⁺ ⊔ 𝓤 ⊔ 𝓥 ̇
has-small-valued-relation S 𝓦 = (x y : ∣ S ∣) → (x ≈∣ S ∣ y) is 𝓦 small

\end{code}

We regard the universe as a setoid, with type equivalence as its
equivalence relation.

\begin{code}

universe-setoid : (𝓤 : Universe) → Setoid (𝓤 ⁺) 𝓤
universe-setoid 𝓤 = (𝓤 ̇)
                  , _≃_
                  , ≃-refl
                  , (λ X Y → ≃-sym)
                  , (λ X Y Z → _●_)

\end{code}

Its relation is natively locally small. For X and Y in 𝓤 ̇, the type
X ≃ Y already lives in 𝓤, and no univalence is used.

\begin{code}

universe-setoid-is-locally-small
 : (𝓤 : Universe) → has-small-valued-relation (universe-setoid 𝓤) 𝓤
universe-setoid-is-locally-small 𝓤 X Y = native-size (X ≃ Y)

\end{code}

A setoid is 𝓦-small if it is setoid-isomorphic to a setoid whose
underlying type and relation both live in 𝓦, and large if it is not.

\begin{code}

is-small-setoid : (𝓦 : Universe) → Setoid 𝓤 𝓥 → 𝓦 ⁺ ⊔ 𝓤 ⊔ 𝓥 ̇
is-small-setoid 𝓦 S = Σ T ꞉ Setoid 𝓦 𝓦 , (S ≅ˢ T)

is-large-setoid : (𝓦 : Universe) → Setoid 𝓤 𝓥 → 𝓦 ⁺ ⊔ 𝓤 ⊔ 𝓥 ̇
is-large-setoid 𝓦 S = ¬ is-small-setoid 𝓦 S

\end{code}
