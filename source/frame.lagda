Martin Escardo, May 2020

We now consider frames. A frame is a poset with all joins
and finite meets such that binary meets distribute over countable
joins.

TODO. Currently the order is derived from the binary meet. However,
for size reasons, it would be good to add the other as a separate
relation coinciding with the binary meet order.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (*)
open import UF-FunExt
open import UF-Subsingletons

module frame (fe : Fun-Ext) where

open import UF-Base
open import UF-SIP
open import UF-SIP-Examples
open import UF-Equiv hiding (_≅_)
open import UF-Univalence
open import UF-Subsingletons-FunExt
open import UF-UA-FunExt


module _ (𝓤 𝓥 : Universe) where

 frame-structure : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
 frame-structure X = X × (X → X → X) × ({N : 𝓥 ̇ } → ((N → X) → X))

 frame-axioms : (X : 𝓤 ̇ ) → frame-structure X → 𝓤 ⊔ (𝓥 ⁺) ̇
 frame-axioms X (⊤ , _∧_ , ⋁) = I × II × III × IV × V × VI × VII
  where
   I   = is-set X
   II  = (x : X) → x ∧ x ≡ x
   III = (x y : X) → x ∧ y ≡ y ∧ x
   IV  = (x y z : X) → x ∧ (y ∧ z) ≡ (x ∧ y) ∧ z
   V   = (x : X) → x ∧ ⊤ ≡ x
   VI  = (x : X) {N : 𝓥 ̇ } (y : N → X) → x ∧ (⋁ y) ≡ ⋁ (n ↦ (x ∧ y n))
   _≤_ : X → X → 𝓤 ̇
   x ≤ y = x ∧ y ≡ x
   VII = {N : 𝓥 ̇ } (x : N → X)
       → ((n : N) → x n ≤ ⋁ x)
       × ((u : X) → ((n : N) → x n ≤ u) → ⋁ x ≤ u)
 \end{code}

 Axioms I-IV say that (X , ⊤ , ∧) is a bounded semilattice, axiom VII
 says that ⋁ gives least upper bounds w.r.t. the induced partial order,
 and axiom VI says that binary meets distribute over countable joins.

 \begin{code}

 frame-axioms-is-prop : (X : 𝓤 ̇ ) (s : frame-structure X)
                      → is-prop (frame-axioms X s)
 frame-axioms-is-prop X (⊤ , _∧_ , ⋁) = prop-criterion δ
  where
   δ : frame-axioms X (⊤ , _∧_ , ⋁) → is-prop (frame-axioms X (⊤ , _∧_ , ⋁))
   δ (i , ii-vii) =
     ×₇-is-prop
       (being-set-is-prop fe)
       (Π-is-prop fe (λ x →       i {x ∧ x} {x}))
       (Π₂-is-prop fe (λ x y →    i {x ∧ y} {y ∧ x}))
       (Π₃-is-prop fe (λ x y z →  i {x ∧ (y ∧ z)} {(x ∧ y) ∧ z}))
       (Π-is-prop fe (λ x →       i {x ∧ ⊤} {x}))
       (Π-is-prop fe (λ x →
        Π-is-prop' fe (λ N →
        Π-is-prop fe (λ y →       i {x ∧ ⋁ y} {⋁ (λ n → x ∧ y n)}))))
       (Π-is-prop' fe (λ n
         →  Π-is-prop  fe (λ 𝕪 →
         ×-is-prop
          (Π-is-prop fe (λ n →    i {𝕪 n ∧ ⋁ 𝕪} {𝕪 n}))
          (Π₂-is-prop fe (λ u _ → i {⋁ 𝕪 ∧ u} {⋁ 𝕪})))))

 Frame : (𝓤 ⊔ 𝓥)⁺ ̇
 Frame = Σ A ꞉ 𝓤 ̇ , Σ s ꞉ frame-structure A , frame-axioms A s

 _≅[Frame]_ : Frame → Frame → 𝓤 ⊔ (𝓥 ⁺) ̇
 (A , (⊤ , _∧_ , ⋁) , _) ≅[Frame] (A' , (⊤' , _∧'_ , ⋁') , _) =

                         Σ f ꞉ (A → A')
                             , is-equiv f
                             × (f ⊤ ≡ ⊤')
                             × ((λ a b → f (a ∧ b)) ≡ (λ a b → f a ∧' f b))
                             × ((λ {N} (𝕒 : N → A) → f (⋁ 𝕒)) ≡ (λ {N} 𝕒 → ⋁' (n ↦ f (𝕒 n))))

 characterization-of-Frame-≡ : is-univalent 𝓤
                             → (A B : Frame)
                             → (A ≡ B) ≃ (A ≅[Frame] B)
 characterization-of-Frame-≡ ua =
   sip.characterization-of-≡ ua
    (sip-with-axioms.add-axioms
       frame-axioms
       frame-axioms-is-prop
      (sip-join.join
        pointed-type.sns-data
      (sip-join.join
        ∞-magma.sns-data
        ∞-hugemagma.sns-data)))

\end{code}
