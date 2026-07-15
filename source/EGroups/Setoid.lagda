Martin Escardo, July 2026.

Setoids, for the development of groups in pure MLTT (see EGroups.Type
and EGroups.FreeOnType).

A setoid is a type equipped with an equivalence relation, given as
data. We do *not* require the relation to be proposition-valued,
because the relation _∿_ used to construct free groups is not, which
is precisely why Groups.Free truncates it before quotienting, and here
we want to use it as it is.

This module collects the notion of setoid and the generic setoid
infrastructure that is not specific to groups, namely the
relation-relative algebraic predicates, equational reasoning, setoid
maps, setoid isomorphism, and the function setoid.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EGroups.Setoid where

open import MLTT.Spartan

is-equivalence-relation : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-equivalence-relation _≈_ = reflexive  _≈_
                            × symmetric  _≈_
                            × transitive _≈_

Setoid : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
Setoid 𝓤 𝓥 = Σ X ꞉ 𝓤 ̇ , Σ R ꞉ (X → X → 𝓥 ̇ ) , is-equivalence-relation R

\end{code}

We write ∣ S ∣ for the underlying type of a setoid S and x ≈⟦ S ⟧ y
for its equivalence relation.

\begin{code}

∣_∣ : Setoid 𝓤 𝓥 → 𝓤 ̇
∣ S ∣ = pr₁ S

setoid-relation : (S : Setoid 𝓤 𝓥) → ∣ S ∣ → ∣ S ∣ → 𝓥 ̇
setoid-relation S = pr₁ (pr₂ S)

syntax setoid-relation S x y = x ≈⟦ S ⟧ y

setoid-refl : (S : Setoid 𝓤 𝓥) → reflexive (setoid-relation S)
setoid-refl S = pr₁ (pr₂ (pr₂ S))

setoid-sym : (S : Setoid 𝓤 𝓥) → symmetric (setoid-relation S)
setoid-sym S = pr₁ (pr₂ (pr₂ (pr₂ S)))

setoid-trans : (S : Setoid 𝓤 𝓥) → transitive (setoid-relation S)
setoid-trans S = pr₂ (pr₂ (pr₂ (pr₂ S)))

\end{code}

The group laws and the congruence condition, stated up to a given
relation _≈_ rather than up to the identity type ＝. These are the
relation-relative counterparts of associative, left-neutral,
right-neutral from Notation.General. In the HoTT/UF setting the
congruence condition is automatic, via ap, but here it is data.

\begin{code}

is-congruence : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → (X → X → X) → 𝓤 ⊔ 𝓥 ̇
is-congruence _≈_ _·_ = {x x' y y' : _} → x ≈ x' → y ≈ y' → (x · y) ≈ (x' · y')

≈-left-neutral : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → X → (X → X → X) → 𝓤 ⊔ 𝓥 ̇
≈-left-neutral _≈_ e _·_ = ∀ x → (e · x) ≈ x

≈-right-neutral : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → X → (X → X → X) → 𝓤 ⊔ 𝓥 ̇
≈-right-neutral _≈_ e _·_ = ∀ x → (x · e) ≈ x

≈-associative : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → (X → X → X) → 𝓤 ⊔ 𝓥 ̇
≈-associative _≈_ _·_ = ∀ x y z → ((x · y) · z) ≈ (x · (y · z))

\end{code}

Equational reasoning up to an equivalence relation, parameterized by
reflexivity and transitivity.

\begin{code}

module ≈-reasoning
        {X : 𝓤 ̇ }
        (_≈_ : X → X → 𝓥 ̇ )
        (≈r : reflexive  _≈_)
        (≈t : transitive _≈_)
       where

 infixr 0 _≈[_]_
 infix  1 _≈∎

 _≈[_]_ : (x : X) {y z : X} → x ≈ y → y ≈ z → x ≈ z
 x ≈[ p ] q = ≈t x _ _ p q

 _≈∎ : (x : X) → x ≈ x
 x ≈∎ = ≈r x

 ＝-to-≈ : {x y : X} → x ＝ y → x ≈ y
 ＝-to-≈ {x} refl = ≈r x

\end{code}

A setoid map is a function that respects the equivalence relations.

\begin{code}

is-setoid-map : (S : Setoid 𝓤 𝓥) (T : Setoid 𝓤' 𝓥')
              → (∣ S ∣ → ∣ T ∣) → 𝓤 ⊔ 𝓥 ⊔ 𝓥' ̇
is-setoid-map S T f = {x y : ∣ S ∣} → x ≈⟦ S ⟧ y → f x ≈⟦ T ⟧ f y

\end{code}

A setoid isomorphism is a pair of setoid maps that are mutually inverse
up to the equivalence relations.

\begin{code}

record _≅ˢ_ (S : Setoid 𝓤 𝓥) (T : Setoid 𝓤' 𝓥') : 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇ where
 field
  to        : ∣ S ∣ → ∣ T ∣
  from      : ∣ T ∣ → ∣ S ∣
  to-resp   : is-setoid-map S T to
  from-resp : is-setoid-map T S from
  to-from   : (y : ∣ T ∣) → to (from y) ≈⟦ T ⟧ y
  from-to   : (x : ∣ S ∣) → from (to x) ≈⟦ S ⟧ x

\end{code}

The function setoid from a type A into a setoid T, namely functions
A → ∣ T ∣ with the pointwise equivalence relation.

\begin{code}

function-setoid : (A : 𝓤 ̇ ) (T : Setoid 𝓥 𝓦) → Setoid (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓦)
function-setoid A T =
   (A → ∣ T ∣)
 , (λ f g → (a : A) → f a ≈⟦ T ⟧ g a)
 , (λ f a → setoid-refl T (f a))
 , (λ f g p a → setoid-sym T (f a) (g a) (p a))
 , (λ f g h p q a → setoid-trans T (f a) (g a) (h a) (p a) (q a))

\end{code}

The setoid of setoid maps from S to T (the codomain of the free-egroup
adjunction on setoids), with the pointwise equivalence relation.

\begin{code}

setoid-map-setoid : (S : Setoid 𝓤 𝓥) (T : Setoid 𝓤' 𝓥')
                  → Setoid (𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥') (𝓤 ⊔ 𝓥')
setoid-map-setoid S T =
   (Σ f ꞉ (∣ S ∣ → ∣ T ∣) , is-setoid-map S T f)
 , (λ u v → (x : ∣ S ∣) → pr₁ u x ≈⟦ T ⟧ pr₁ v x)
 , (λ u x → setoid-refl T (pr₁ u x))
 , (λ u v p x → setoid-sym T (pr₁ u x) (pr₁ v x) (p x))
 , (λ u v w p q x → setoid-trans T (pr₁ u x) (pr₁ v x) (pr₁ w x) (p x) (q x))

\end{code}
