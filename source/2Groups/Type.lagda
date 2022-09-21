--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

July 2022
--------------------------------------------------------------------------------

Basic facts about 2-groups, or categorical groups, or gr-categories, in another parlance.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Subsingletons
open import UF.FunExt
open import UF.Subsingletons-FunExt
open import UF.Equiv hiding (_≅_ ; ≅-refl ; _●_)
open import UF.Groupoids

module 2Groups.Type where

\end{code}

Underlying type of the structure

\begin{code}

open import Groups.Type using (⟨_⟩)

\end{code}

The mathematical structure of a 2-Group, or categorical group. The
main structure is of course an operation X → X → X as usual, but since
in categorical algebra the underlying carrier is a category, the
structure also affects morphisms. The most important property of the
structure on morphisms is functoriality, which in categorical algebra
is a reflection of the fact that the operation is overall a functor.

In our case, there should be a companion structure defined on identity
types.  More precisely, given a specific tensor structure on X, we
postulate there exists a lift to the identity types, and we require
that the companion structure satisfy an interchange law with respect
to the underlying structure.

\begin{code}

⊗-structure : 𝓤 ̇ → 𝓤 ̇
⊗-structure X = X → X → X

⊗-structure-Id : (X : 𝓤 ̇) → ⊗-structure X → 𝓤 ̇
⊗-structure-Id X _●_ = ∀ {x x' y y'} → x ＝ x' → y ＝ y'
                      → x ● y ＝ x' ● y'

⊗-structure-Id-interchange : (X : 𝓤 ̇) → (_●_ : ⊗-structure X) → ⊗-structure-Id X _●_ → 𝓤 ̇
⊗-structure-Id-interchange X _●_ _✶_ = {x x' x'' y y' y'' : X}
                                      → (p : x ＝ x') (p' : x' ＝ x'')
                                      → (q : y ＝ y') (q' : y' ＝ y'')
                                      → ((p ✶ q) ∙ (p' ✶ q')) ＝ ((p ∙ p') ✶ (q ∙ q'))

\end{code}

It turns out a lifted structure can be obtained from a given
⊗-structure using ap. In fact, this can be done in several ways.

\begin{code}

⊗-structure-ap-left : {X : 𝓤 ̇ } → (_●_ : ⊗-structure X)
                    → {x y : X} → (p : x ＝ y) → (z : X)
                    → x ● z ＝ y ● z
⊗-structure-ap-left _●_ p z = ap (λ v → v ● z) p

⊗-structure-ap-right : {X : 𝓤 ̇} → (_●_ : ⊗-structure X)
                     → (z : X) → {x y : X} → (p : x ＝ y)
                     →  z ● x ＝ z ● y
⊗-structure-ap-right _●_ z p = ap (λ v → z ● v) p

⊗-structure-to-Id : (X : 𝓤 ̇) → (_●_ : ⊗-structure X)
                   → ⊗-structure-Id X _●_
⊗-structure-to-Id X _●_ {_} {x'} {y} p q =
                    (⊗-structure-ap-left _●_ p y) ∙ (⊗-structure-ap-right _●_ x' q) 

⊗-structure-to-Id' : (X : 𝓤 ̇) → (_●_ : ⊗-structure X)
                    → ⊗-structure-Id X _●_
⊗-structure-to-Id' X _●_ {x} {x'} {y} {y'} p q =
                   (⊗-structure-ap-right _●_ x q) ∙ (⊗-structure-ap-left _●_ p y')

⊗-structure-to-Id₂ : (X : 𝓤 ̇) → (_●_ : ⊗-structure X)
                    → ⊗-structure-Id X _●_
⊗-structure-to-Id₂ X _●_ = ap₂ _●_


\end{code}

The lifts are compatible. We do this by first expressing the
compatibility via a type, and then, second, showing that this type is
inhabited.

\begin{code}

⊗-structure-has-compatible-lifts : (X : 𝓤 ̇) → ⊗-structure X → 𝓤 ̇
⊗-structure-has-compatible-lifts X _●_ = {x x' y y' : X}
                                        → (p : x ＝ x')
                                        → (q : y ＝ y')
                                        → ⊗-structure-to-Id X _●_ {_} {x'} {y} p q 
                                            ＝ ⊗-structure-to-Id' X _●_ {x} {x'} {y} {y'} p q

⊗-structure-lifts-compatible : (X : 𝓤 ̇) → (_●_ : ⊗-structure X)
                              → ⊗-structure-has-compatible-lifts X _●_
⊗-structure-lifts-compatible X _●_ {x} {.x} {y} {y'} refl q = 
                             ⊗-structure-to-Id X _●_ refl q        ＝⟨ refl ⟩
                             refl ∙ (⊗-structure-ap-right _●_ x q) ＝⟨ refl-left-neutral ⟩
                             ⊗-structure-ap-right _●_ x q          ＝⟨ refl ⁻¹ ⟩
                             (⊗-structure-ap-right _●_ x q) ∙ refl ＝⟨ refl ⟩
                             ⊗-structure-to-Id' X _●_ refl q ∎

⊗-structure-has-compatible-lifts₂ : (X : 𝓤 ̇) → ⊗-structure X → 𝓤 ̇
⊗-structure-has-compatible-lifts₂ X _●_ = {x x' y y' : X}
                                        → (p : x ＝ x')
                                        → (q : y ＝ y')
                                        → ⊗-structure-to-Id₂ X _●_ p q ＝
                                            ⊗-structure-to-Id X _●_ p q

⊗-structure-lifts-compatible₂ : (X : 𝓤 ̇) → (_●_ : ⊗-structure X)
                               → ⊗-structure-has-compatible-lifts₂ X _●_
⊗-structure-lifts-compatible₂ X _●_ refl refl = refl

\end{code}

The interchange law holds for the lifts we have introduced. We prove it for one of them.

\begin{code}

⊗-structure-to-Id-has-interchange : (X : 𝓤 ̇) → (_●_ : ⊗-structure X)
                                   → ⊗-structure-Id-interchange X _●_ (⊗-structure-to-Id X _●_)
⊗-structure-to-Id-has-interchange X _●_ {x} {x'} {.x'} {y} {.y} {y''} p refl refl q' =
     ⊗-structure-to-Id X _●_ p refl ∙ ⊗-structure-to-Id X _●_ refl q'         ＝⟨ refl ⟩
     ⊗-structure-to-Id X _●_ p refl ∙ (refl ∙ ⊗-structure-ap-right _●_ x' q') ＝⟨ refl ⟩
     (⊗-structure-ap-left _●_ p y)  ∙ (refl ∙ ⊗-structure-ap-right _●_ x' q') ＝⟨ i ⟩
     (⊗-structure-ap-left _●_ p y)  ∙ (⊗-structure-ap-right _●_ x' q')        ＝⟨ refl ⟩
     ⊗-structure-to-Id X _●_ p  q'                                             ＝⟨ refl ⟩
     ⊗-structure-to-Id X _●_ (p ∙ refl) q'                                     ＝⟨ ii ⟩
     ⊗-structure-to-Id X _●_ (p ∙ refl) (refl ∙ q') ∎
       where
         i = ap (λ v → (⊗-structure-ap-left _●_ p y) ∙ v) (refl-left-neutral {p = ⊗-structure-ap-right _●_ x' q'})
         ii = ap (⊗-structure-to-Id X _●_ (p ∙ refl)) (refl-left-neutral {p = q'}) ⁻¹ 
         
\end{code}



record 2-group-structure (X : 𝓤 ̇) : 𝓤 ̇ where
  field
    _●_ : X → X → X
    is-grpd : is-groupoid X
    α : associative _●_

  private
    p : (x y z t : X) → ((x ● y) ● z) ● t ＝  x ● (y ● (z ● t))
    p x y z t = ((x ● y) ● z) ● t ＝⟨ ap (λ v → v ● t) (α _ _ _) ⟩
                (x ● (y ● z)) ● t ＝⟨ α _ _ _ ⟩
                x ● ((y ● z) ● t) ＝⟨ ap (λ v → x ● v) (α _ _ _) ⟩
                x ● (y ● (z ● t)) ∎
    q : (x y z t : X) → ((x ● y) ● z) ● t ＝ x ● (y ● (z ● t))
    q x y z t = ((x ● y) ● z) ● t ＝⟨ α _ _ _ ⟩
                (x ● y) ● (z ● t) ＝⟨ α _ _ _ ⟩
                x ● (y ● (z ● t)) ∎

  field
    π : {x y z t : X} → p x y z t ＝ q x y z t
    e : X
    l : left-neutral e _●_
    r : right-neutral e _●_
    lr : l e ＝ r e

    inv-l : (x : X) → is-equiv (λ v → x ● v)
    inv-r : (x : X) → is-equiv (λ v → v ● x)

2-Group : (𝓤 : Universe) → 𝓤 ⁺ ̇
2-Group 𝓤 = Σ X ꞉ 𝓤 ̇ , 2-group-structure X

