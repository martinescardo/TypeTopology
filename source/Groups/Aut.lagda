--------------------------------------------------------------------------------
Ettore Aldrovandi aldrovandi@math.fsu.edu
Keri D'Angelo kd349@cornell.edu

June 2022
--------------------------------------------------------------------------------

If X is a set, Aut X, defined in UF-Equiv, is a group.

We assume functional extensionality at level 𝓤.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

open import SpartanMLTT
open import UF-Base hiding (_≈_)
open import UF-Subsingletons
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-FunExt
open import UF-UA-FunExt
open import UF-Subsingletons-FunExt
open import UF-Retracts

open import Groups renaming (_≅_ to _≣_)
open import Groups.Groups-Supplement

module Groups.Aut where

module _ (fe : funext 𝓤 𝓤) (X : 𝓤 ̇) (i : is-set X) where

  is-set-Aut : is-set (Aut X)
  is-set-Aut = Σ-is-set
                  (Π-is-set fe (λ _ → i))
                  λ f → props-are-sets (being-equiv-is-prop'' fe f)


  group-structure-Aut : Aut X → Aut X → Aut X
  group-structure-Aut f g = f ● g

  private
    _·_ = group-structure-Aut

\end{code}

In the following proof of the group axioms, the associativity proof
reproduces that of ≃-assoc in UF-Equiv-FunExt, instead of calling
≃-assoc directly, because the latter uses FunExt and we use funext 𝓤 𝓤
here.  Similarly for the proof of the inverse, which reproduces those
of ≃-sym-is-linv and ≃-sym-is-rinv.

In both cases the key is to use being-equiv-is-prop'' in place of
being-equiv-is-prop.

\begin{code}
  group-axioms-Aut : group-axioms (Aut X) _·_
  group-axioms-Aut = is-set-Aut , assoc-Aut , e , ln-e , rn-e , φ
    where
      assoc-Aut : associative _·_
      assoc-Aut (f , i) (g , j) (h , k) = to-Σ-≡ (p , (q ⁻¹))
        where
          p : (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
          p = refl

          d e : is-equiv (h ∘ g ∘ f)
          d = ∘-is-equiv i (∘-is-equiv j k)
          e = ∘-is-equiv (∘-is-equiv i j) k

          q : transport is-equiv p d ≡ e
          q = being-equiv-is-prop'' fe (h ∘ g ∘ f) _ _

      e : Aut X
      e = id , id-is-equiv X

      ln-e : left-neutral e _·_
      ln-e = λ f → ≃-refl-left' fe fe fe f

      rn-e : right-neutral e _·_
      rn-e = λ f → ≃-refl-right' fe fe fe f

      φ : (f : Aut X) →
          (Σ f' ꞉ Aut X , (f' · f ≡ e) × (f · f' ≡ e))
      pr₁ (φ f) = ≃-sym f
      pr₁ (pr₂ (φ (∣f∣ , is))) = to-Σ-≡ (p , being-equiv-is-prop'' fe _ _ _)
        where
          p : ∣f∣ ∘ inverse ∣f∣ is ≡ id
          p = dfunext fe (inverses-are-sections ∣f∣ is)
      pr₂ (pr₂ (φ (∣f∣ , is))) = to-Σ-≡ (p , being-equiv-is-prop'' fe _ _ _)
        where
          p : inverse ∣f∣ is ∘ ∣f∣ ≡ id
          p = dfunext fe (inverses-are-retractions ∣f∣ is)

  Group-structure-Aut : Group-structure (Aut X)
  Group-structure-Aut = _·_ , group-axioms-Aut
\end{code}

If φ is an equivalence between X and Y, then it induces a morphism
from Aut X to Aut Y. This morphism is a homomorphism for the group
structures defined above.

\begin{code}

module _ (fe : funext 𝓤 𝓤) (fe' : funext 𝓥 𝓥)
         (X : 𝓤 ̇) (i : is-set X)
         (Y : 𝓥 ̇) (j : is-set Y)
         (φ : X ≃ Y)  where

  a : Aut X → Aut Y
  a f = (≃-sym φ ● f ) ● φ

\end{code}
