Martin Escardo, 29 June 2018

The type Ordinals of ordinals in a universe 𝓤.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Ordinals.Notions
open import Ordinals.Underlying
open import UF.ClassicalLogic
open import UF.FunExt
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Ordinals.Type where

\end{code}

An ordinal is a type equipped with ordinal structure. Such a type is
automatically a set.

\begin{code}

OrdinalStructure : 𝓤 ̇ → 𝓤 ⁺ ̇
OrdinalStructure {𝓤} X = Σ _<_ ꞉ (X → X → 𝓤 ̇ ) , (is-well-order _<_)

Ordinal : ∀ 𝓤 → 𝓤 ⁺ ̇
Ordinal 𝓤 = Σ X ꞉ 𝓤 ̇ , OrdinalStructure X

Ord = Ordinal 𝓤₀

\end{code}

NB. Perhaps we will eventually need to have two parameters 𝓤 (the
universe where the underlying type X lives) and 𝓥 (the universe where
_<_ takes values in) for Ordinal.

Ordinals are ranged over by α,β,γ.

The underlying type of an ordinal (which happens to be necessarily a
set):

\begin{code}

instance
 underlying-type-of-ordinal : Underlying (Ordinal 𝓤)
 ⟨_⟩ {{underlying-type-of-ordinal}} (X , _) = X
 underlying-order {{underlying-type-of-ordinal}} (X , _<_ , o) = _<_

structure : (α : Ordinal 𝓤) → OrdinalStructure ⟨ α ⟩
structure (X , s) = s

is-trichotomous : Ordinal 𝓤 → 𝓤 ̇
is-trichotomous α = is-trichotomous-order (underlying-order α)

is-well-ordered : (α : Ordinal 𝓤) → is-well-order (underlying-order α)
is-well-ordered (X , _<_ , o) = o

Prop-valuedness : (α : Ordinal 𝓤) → is-prop-valued (underlying-order α)
Prop-valuedness α = prop-valuedness (underlying-order α) (is-well-ordered α)

Reflexivity : (α : Ordinal 𝓤) {x : ⟨ α ⟩} → x ≼⟨ α ⟩ x
Reflexivity α = ≼-refl (underlying-order α)

Transitivity : (α : Ordinal 𝓤) → is-transitive (underlying-order α)
Transitivity α = transitivity (underlying-order α) (is-well-ordered α)

Well-foundedness : (α : Ordinal 𝓤) (x : ⟨ α ⟩) → is-accessible (underlying-order α) x
Well-foundedness α = well-foundedness (underlying-order α) (is-well-ordered α)

Irreflexivity : (α : Ordinal 𝓤) → is-irreflexive (underlying-order α)
Irreflexivity α x = irreflexive (underlying-order α) x (Well-foundedness α x)

Transfinite-induction : (α : Ordinal 𝓤)
                      → (P : ⟨ α ⟩ → 𝓦 ̇ )
                      → ((x : ⟨ α ⟩)
                      → ((y : ⟨ α ⟩) → y ≺⟨ α ⟩ x → P y) → P x)
                      → (x : ⟨ α ⟩) → P x
Transfinite-induction α = transfinite-induction
                           (underlying-order α)
                           (Well-foundedness α)

Transfinite-recursion : (α : Ordinal 𝓤) {Y : 𝓥 ̇ }
                      → ((x : ⟨ α ⟩)
                      → ((y : ⟨ α ⟩) → y ≺⟨ α ⟩ x → Y) → Y)
                      → ⟨ α ⟩ → Y
Transfinite-recursion α = transfinite-recursion
                           (underlying-order α)
                           (Well-foundedness α)
\end{code}

Added 31 October 2022 by Tom de Jong.
We record the (computational) behaviour of transfinite induction for use in
other constructions.

\begin{code}

Transfinite-induction-behaviour : FunExt
                                → (α : Ordinal 𝓤)
                                → (P : ⟨ α ⟩ → 𝓦 ̇ )
                                → (f : (x : ⟨ α ⟩) → ((y : ⟨ α ⟩) → y ≺⟨ α ⟩ x → P y) → P x)
                                → (x : ⟨ α ⟩)
                                → Transfinite-induction α P f x
                                  ＝ f x (λ y l → Transfinite-induction α P f y)
Transfinite-induction-behaviour fe α = transfinite-induction-behaviour
                                        (underlying-order α) fe
                                        (Well-foundedness α)
\end{code}

End of addition.

\begin{code}

Transfinite-recursion-behaviour : FunExt
                                → (α : Ordinal 𝓤)
                                → {Y : 𝓥 ̇ }
                                → (f : (x : ⟨ α ⟩) → ((y : ⟨ α ⟩) → y ≺⟨ α ⟩ x → Y) → Y)
                                → (x : ⟨ α ⟩)
                                → Transfinite-recursion α f x
                                  ＝ f x (λ y l → Transfinite-recursion α f y)
Transfinite-recursion-behaviour fe α =
 transfinite-recursion-behaviour (underlying-order α) fe (Well-foundedness α)

Extensionality : (α : Ordinal 𝓤) → is-extensional (underlying-order α)
Extensionality α = extensionality (underlying-order α) (is-well-ordered α)

Antisymmetry : (α : Ordinal 𝓤) (x y : ⟨ α ⟩) → x ≼⟨ α ⟩ y → y ≼⟨ α ⟩ x → x ＝ y
Antisymmetry = Extensionality

underlying-type-is-set : FunExt
                       → (α : Ordinal 𝓤)
                       → is-set ⟨ α ⟩
underlying-type-is-set fe α =
 extensionally-ordered-types-are-sets
  (underlying-order α)
  fe
  (Prop-valuedness α)
  (Extensionality α)

is-least : (α : Ordinal 𝓤) → ⟨ α ⟩ → 𝓤 ̇
is-least α x = (y : ⟨ α ⟩) → x ≼⟨ α ⟩ y

being-least-is-prop : Fun-Ext → (α : Ordinal 𝓤) (x : ⟨ α ⟩) → is-prop (is-least α x)
being-least-is-prop fe α x = Π₃-is-prop fe (λ y u _ → Prop-valuedness α u y)

at-most-one-least : (α : Ordinal 𝓤) (x y : ⟨ α ⟩)
                  → is-least α x
                  → is-least α y
                  → x ＝ y
at-most-one-least α x y l l' = Antisymmetry α x y (l y) (l' x)

has-least : Ordinal 𝓤 → 𝓤 ̇
has-least α = Σ ⊥ ꞉ ⟨ α ⟩ , is-least α ⊥

having-least-is-prop : Fun-Ext → (α : Ordinal 𝓤) → is-prop (has-least α)
having-least-is-prop fe α (⊥ , l) (⊥' , l') =
  to-subtype-＝
    (being-least-is-prop fe α)
    (at-most-one-least α ⊥ ⊥' l l')

is-minimal : (α : Ordinal 𝓤) → ⟨ α ⟩ → 𝓤 ̇
is-minimal α x = (y : ⟨ α ⟩) → ¬ (y ≺⟨ α ⟩ x)

minimal-is-least : (α : Ordinal 𝓤) → (x : ⟨ α ⟩) → is-minimal α x → is-least α x
minimal-is-least α x minimal y u l = 𝟘-elim (minimal u l)

least-is-minimal : (α : Ordinal 𝓤) → (x : ⟨ α ⟩) → is-least α x → is-minimal α x
least-is-minimal α x least y l = Irreflexivity α y (least y y l)

is-largest : (α : Ordinal 𝓤) → ⟨ α ⟩ → 𝓤 ̇
is-largest α x = (y : ⟨ α ⟩) → y ≼⟨ α ⟩ x

being-largest-is-prop : Fun-Ext → (α : Ordinal 𝓤) (x : ⟨ α ⟩) → is-prop (is-largest α x)
being-largest-is-prop fe α x = Π₃-is-prop fe (λ y u _ → Prop-valuedness α u x)

at-most-one-largest : (α : Ordinal 𝓤) (x y : ⟨ α ⟩)
                    → is-largest α x
                    → is-largest α y
                    → x ＝ y
at-most-one-largest α x y l l' = Antisymmetry α x y (l' x) (l y)

has-largest : Ordinal 𝓤 → 𝓤 ̇
has-largest α = Σ ⊤ ꞉ ⟨ α ⟩ , is-largest α ⊤

having-largest-is-prop : Fun-Ext → (α : Ordinal 𝓤) → is-prop (has-largest α)
having-largest-is-prop fe α (⊥ , l) (⊥' , l') =
  to-subtype-＝
    (being-largest-is-prop fe α)
    (at-most-one-largest α ⊥ ⊥' l l')

\end{code}

TODO. We should add further properties of the order from the module
Notions. For the moment, we add this:

\begin{code}

irrefl : (α : Ordinal 𝓤) (x : ⟨ α ⟩) → ¬(x ≺⟨ α ⟩ x)
irrefl α x = irreflexive (underlying-order α) x (Well-foundedness α x)

≼-gives-≾ : (α : Ordinal 𝓤) (x y : ⟨ α ⟩) → x ≼⟨ α ⟩ y → x ≾⟨ α ⟩ y
≼-gives-≾ {𝓤} α x y = ≼-coarser-than-≾ (underlying-order α)
                       y (Well-foundedness α y) x

≺-≼-gives-≺ : (α : Ordinal 𝓤) → (x y z : ⟨ α ⟩) → x ≺⟨ α ⟩ y → y ≼⟨ α ⟩ z  → x ≺⟨ α ⟩ z
≺-≼-gives-≺ α x y z p q = q x p

\end{code}

Added here on 12 December 2024 by Tom de Jong, but developed earlier in
collaboration with Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu.

Given an ordinal α and a type family P, subtype of elements satisfying P
inherits an order from α.  This order also inherits wellfoundedness and
transitivity from the order on α, but not necessarily extensionality
constructively (see Ordinals.ShulmanTaboo).

\begin{code}

module _
        (α : Ordinal 𝓤)
        (P : ⟨ α ⟩ → 𝓥 ̇  )
       where

 subtype-order : (Σ x ꞉ ⟨ α ⟩ , P x) → (Σ x ꞉ ⟨ α ⟩ , P x) → 𝓤 ̇
 subtype-order (x , _) (y , _) = x ≺⟨ α ⟩ y

 subtype-order-is-prop-valued : is-prop-valued subtype-order
 subtype-order-is-prop-valued (x , _) (y , _) = Prop-valuedness α x y

 subtype-order-is-well-founded : is-well-founded subtype-order
 subtype-order-is-well-founded (a , p) =
  subtype-order-accessible (a , p) (Well-foundedness α a)
   where
    subtype-order-accessible
     : ((x , p) : Σ x ꞉ ⟨ α ⟩ , P x)
     → is-accessible (underlying-order α) x → is-accessible subtype-order (x , p)
    subtype-order-accessible (x , p) (acc step) =
     acc (λ (x' , p') l → subtype-order-accessible (x' , p') (step x' l))

 subtype-order-is-transitive : is-transitive subtype-order
 subtype-order-is-transitive (x , _) (y , _) (z , _) = Transitivity α x y z

 EM-implies-subtype-order-is-extensional
  : EM 𝓤 → ((x : ⟨ α ⟩) → is-prop (P x)) → is-extensional subtype-order
 EM-implies-subtype-order-is-extensional em P-is-Prop (z , l) (y , l') h h' =
  to-subtype-＝ P-is-Prop (I (II z y))
    where
     I : in-trichotomy (underlying-order α) z y → z ＝ y
     I (inl u) = 𝟘-elim (irrefl α z (h' (z , l) u))
     I (inr (inl e)) = e
     I (inr (inr u)) = 𝟘-elim (irrefl α y (h (y , l') u))

     II : is-trichotomous-order (underlying-order α)
     II = trichotomy₃ (underlying-order α) em (is-well-ordered α)

\end{code}
