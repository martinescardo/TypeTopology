--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

July 1, 2021
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K #-}


open import Groups.Type renaming (_≅_ to _≣_)
open import MLTT.Id
open import MLTT.Spartan
open import MLTT.Unit
open import MLTT.Unit-Properties
open import UF.Base
open import UF.Equiv
open import UF.Retracts
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-Properties

\end{code}

We define the trivial group (in the universe $𝓤$) giving the trivial
group structure to the one-point type in the universe.

\begin{code}

module Groups.Triv where

triv : Group 𝓤
triv = 𝟙 , (group-structure-t ,
            is-set-t ,
            (associative-t ,
              (unit-t , (left-neutral-t , right-neutral-t , inv-t))))
  where
    group-structure-t : group-structure 𝟙
    group-structure-t = λ x y → ⋆

    is-set-t : is-set 𝟙
    is-set-t = props-are-sets (𝟙-is-prop)

    associative-t : associative (group-structure-t)
    associative-t = λ x y z → refl

    unit-t : 𝟙
    unit-t = ⋆

    left-neutral-t : left-neutral unit-t group-structure-t
    left-neutral-t = λ { * → refl}

    right-neutral-t : right-neutral unit-t group-structure-t
    right-neutral-t = λ { * → refl}

    inv-t = λ x → ⋆ , (refl , refl)

\end{code}

The trivial group is initial and terminal in the obvious sense.

\begin{code}

-- trivial group is initial

triv-initial : ∀ {𝓤 𝓥} → (G : Group 𝓤) → ⟨ triv {𝓥} ⟩ → ⟨ G ⟩
triv-initial G = λ _ → e⟨ G ⟩

triv-initial-is-hom : ∀ {𝓤 𝓥} → (G : Group 𝓤) → (is-hom (triv {𝓥}) G (triv-initial G))
triv-initial-is-hom G = e⟨ G ⟩ ＝⟨ (unit-left G e⟨ G ⟩) ⁻¹ ⟩
                        e⟨ G ⟩ ·⟨ G ⟩  e⟨ G ⟩ ∎

-- trivial group is terminal

triv-terminal : (G : Group 𝓤) → (⟨ G ⟩ → ⟨ triv {𝓥} ⟩)
triv-terminal G = unique-to-𝟙

triv-terminal-is-hom : (G : Group 𝓤) → (is-hom G (triv {𝓥}) (triv-terminal G))
triv-terminal-is-hom G = refl

\end{code}

If the underlying type of $G$ is contractible then $G$ is isomorphic
to the trivial group. Note that it is not necessary to assume the
center of contraction is the identity.

\begin{code}

group-is-singl-is-triv : (G : Group 𝓤) → is-singleton ⟨ G ⟩ → G ≣ (triv {𝓤})
pr₁ (group-is-singl-is-triv G is) = triv-terminal G
pr₁ (pr₁ (pr₂ (group-is-singl-is-triv G is))) = triv-initial G , λ { * → refl}
pr₂ (pr₁ (pr₂ (group-is-singl-is-triv G is))) = (triv-initial G) , λ x → p ∙ (pr₂ is x)
  where
    c : ⟨ G ⟩
    c = pr₁ is
    p : e⟨ G ⟩ ＝ c
    p = (pr₂ is e⟨ G ⟩) ⁻¹
pr₂ (pr₂ (group-is-singl-is-triv G is)) {x} {y} = triv-terminal-is-hom G {x} {y}

group-is-singl-is-triv' : (G : Group 𝓤) → is-singleton ⟨ G ⟩ → (triv {𝓤}) ≣ G
pr₁ (group-is-singl-is-triv' G is) = triv-initial G
pr₁ (pr₁ (pr₂ (group-is-singl-is-triv' G is))) = (triv-terminal G) , λ x → p ∙ (pr₂ is x)
  where
    c : ⟨ G ⟩
    c = pr₁ is
    p : e⟨ G ⟩ ＝ c
    p = (pr₂ is e⟨ G ⟩) ⁻¹
pr₂ (pr₁ (pr₂ (group-is-singl-is-triv' G is))) = (triv-terminal G) , (λ { * → refl})
pr₂ (pr₂ (group-is-singl-is-triv' G is)) {x} {y} = triv-initial-is-hom G {x} {y}

\end{code}
