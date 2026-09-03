--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

March 15, 2022
--------------------------------------------------------------------------------

Following P. Aluffi, "Algebra: Chapter 0," we consider
equivalence relations that are left- and right-invariant.

If $X$ is a group, the quotient by such an equivalence
relation is again a group.

In particular this is true for the equivalence relation arising from
the standard condition that the image of a group homomorphism be
normal in the target. The quotient is then the cokernel of the
homomorphism (see Groups.Cokernel)

TODO: adapt to use (small) quotients defined in Quotient.Type

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Quotient.Type
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets

module Groups.Quotient
        (pt  : propositional-truncations-exist)
        (fe  : Fun-Ext)
        (sq : set-quotients-exist)
       where

open general-set-quotients-exist sq
open import UF.ImageAndSurjection pt

open import Groups.Type renaming (_≅_ to _≣_)

\end{code}

A relation ≈ on the underlying space ⟨ X ⟩ is left-invariant if

  ∀ g → a ≈ b → ga ≈ gb

Similarly, it is right-invariant if

  ∀ g → a ≈ b → ag ≈ bg

\begin{code}

module _ {𝓤 𝓥 : Universe} (X : Group 𝓤) ((_≈_ , ≈p , ≈r , ≈s , ≈t) : EqRel {𝓤} {𝓥} ⟨ X ⟩ ) where

  open PropositionalTruncation pt

  ≈left-invariant : _
  ≈left-invariant = (a b g : ⟨ X ⟩) → a ≈ b → (g · a) ≈ (g · b)
    where
      _·_ = multiplication X

  ≈left-invariant₁ : _
  ≈left-invariant₁ = {a b g : ⟨ X ⟩} → a ≈ b → (g · a) ≈ (g · b)
    where
      _·_ = multiplication X

  ≈right-invariant : _
  ≈right-invariant = (a b g : ⟨ X ⟩) → a ≈ b → (a · g) ≈ (b · g)
    where
      _·_ = multiplication X

  ≈right-invariant₁ : _
  ≈right-invariant₁ = {a b g : ⟨ X ⟩} → a ≈ b → (a · g) ≈ (b · g)
    where
      _·_ = multiplication X

\end{code}

Relations that are both left- and right-invariant permit the
definition of quotient group under the given equivalence relation. The
left and right invariance conditions together imply that the relation
is compatible with the product and with taking the inverse.

\begin{code}
  module GroupQuotient (≈li : ≈left-invariant)
                       (≈ri : ≈right-invariant) where
    private
      ≋ : EqRel ⟨ X ⟩
      ≋ = (_≈_ , ≈p , ≈r , ≈s , ≈t)

    binop-cong : {x₁ x₂ x₁' x₂' : ⟨ X ⟩}
               → x₁ ≈ x₁' → x₂ ≈ x₂'
               → (x₁ ·⟨ X ⟩ x₂) ≈ (x₁' ·⟨ X ⟩ x₂')
    binop-cong {x₁} {x₂} {x₁'} {x₂'} u₁ u₂ = ≈t (x₁ · x₂) (x₁ · x₂') (x₁' · x₂') p₁ p₂
      where
        _·_ = multiplication X
        p₁ : (x₁ · x₂) ≈ (x₁ · x₂')
        p₁ = ≈li _ _ x₁ u₂
        p₂ : (x₁ · x₂') ≈ (x₁' · x₂')
        p₂ = ≈ri _ _ x₂' u₁

\end{code}

\texttt{id-implies-related} below says that two equal terms must be
related. It should be part of \texttt{Notation.General}, or closer to
general facts about equivalence relations.

\begin{code}

    inv-cong : {x y : ⟨ X ⟩} → x ≈ y → inv X x ≈ inv X y
    inv-cong {x} {y} p = ≈t x' (x' ·⟨ X ⟩ (y ·⟨ X ⟩  y')) y'
                                  I' (≈t (x' ·⟨ X ⟩ (y ·⟨ X ⟩  y')) ((x' ·⟨ X ⟩ y) ·⟨ X ⟩  y') y' III II')
     where
        id-implies-related : ∀ {x y} → x ＝ y → x ≈ y
        id-implies-related {x} {.x} refl = ≈r x

        x' y' e : ⟨ X ⟩
        x'      = inv X x
        y'      = inv X y
        e       = unit X

        I : e ≈ (y ·⟨ X ⟩  y')
        I = id-implies-related ((inv-right X y) ⁻¹)

        I' : x' ≈ (x' ·⟨ X ⟩ (y ·⟨ X ⟩  y'))
        I' = ≈t x' (x' ·⟨ X ⟩ e) ((x' ·⟨ X ⟩ (y ·⟨ X ⟩  y'))) (id-implies-related ((unit-right X x') ⁻¹)) (≈li _ _ _ I)

        II : (x' ·⟨ X ⟩ y) ≈ e
        II = ≈t (x' ·⟨ X ⟩ y) (x' ·⟨ X ⟩ x) e (≈li _ _ _ (≈s _ _ p)) (id-implies-related (inv-left X x))

        II' : ((x' ·⟨ X ⟩ y) ·⟨ X ⟩ y') ≈ y'
        II' = ≈t ((x' ·⟨ X ⟩ y) ·⟨ X ⟩ y') (e ·⟨ X ⟩ y') y' (≈ri _ _ _ II) (id-implies-related (unit-left X y'))

        III : (x' ·⟨ X ⟩ (y ·⟨ X ⟩  y')) ≈ ((x' ·⟨ X ⟩ y) ·⟨ X ⟩  y')
        III = id-implies-related ((assoc X _ _ _) ⁻¹)

    quotient-gr : Group _
    quotient-gr = X≈ , _·_ , is-set-X≈ , assoc≈ , e≈ , ln≈ , rn≈ , λ x → inv≈ x , (inv-left≈ x , inv-right≈ x)
      where
        X≈ : _
        X≈ = ⟨ X ⟩ / ≋

        π≈ : _
        π≈ = η/ ≋

        π≈-is-surjection : is-surjection π≈
        π≈-is-surjection = η/-is-surjection ≋ pt

        _·_ : group-structure X≈
        _·_ = extension₂/ ≋ (multiplication X) binop-cong

        ·-natural : (x y : ⟨ X ⟩) → π≈ x · π≈ y ＝ π≈ (x ·⟨ X ⟩ y)
        ·-natural = λ x y → naturality₂/ ≋ (multiplication X) binop-cong x y

        is-set-X≈ : is-set X≈
        is-set-X≈ = /-is-set ≋

        assoc≈ : associative _·_
        assoc≈ = /-induction₃ fe ≋ (λ x' y' z' → is-set-X≈) γ
         where
          γ : (s t z : ⟨ X ⟩) → ((π≈ s · π≈ t) · π≈ z) ＝ (π≈ s · (π≈ t · π≈ z))
          γ s t z = ((π≈ s · π≈ t) · π≈ z)   ＝⟨ ap (λ v → v · π≈ z) (·-natural s t) ⟩
                    π≈ (s ·⟨ X ⟩ t) · π≈ z    ＝⟨ ·-natural (s ·⟨ X ⟩ t) z ⟩
                    π≈ ((s ·⟨ X ⟩ t) ·⟨ X ⟩ z) ＝⟨ ap π≈ (assoc X s t z) ⟩
                    π≈ (s ·⟨ X ⟩ (t ·⟨ X ⟩ z)) ＝⟨ ·-natural s (t ·⟨ X ⟩ z) ⁻¹ ⟩
                    π≈ s · π≈ (t ·⟨ X ⟩ z)    ＝⟨ ap (λ v → π≈ s · v) (·-natural t  z ⁻¹) ⟩
                    (π≈ s · (π≈ t · π≈ z)) ∎

        e≈ : X≈
        e≈ = π≈ (unit X)

        ln≈ : left-neutral e≈ _·_
        ln≈ = /-induction ≋ (λ _ → /-is-set ≋) γ
          where
            γ : (x : ⟨ X ⟩) → π≈ (unit X) · π≈ x ＝ π≈ x
            γ x = π≈ (unit X) · π≈ x     ＝⟨ ·-natural (unit X) x ⟩
                  π≈ ((unit X) ·⟨ X ⟩ x)  ＝⟨ ap π≈ (unit-left X x) ⟩
                  π≈ x ∎

        rn≈ : right-neutral e≈ _·_
        rn≈ = /-induction ≋ (λ _ → /-is-set ≋) γ
          where
            γ : (x : ⟨ X ⟩) → π≈ x · π≈ (unit X) ＝ π≈ x
            γ x = π≈ x · π≈ (unit X)     ＝⟨ ·-natural x (unit X) ⟩
                  π≈ (x ·⟨ X ⟩ (unit X))  ＝⟨ ap π≈ (unit-right X x) ⟩
                  π≈ x ∎

        inv≈ : X≈ → X≈
        inv≈ = extension₁/ ≋ (inv X) inv-cong

        inv-left≈ : (x : X≈) → (inv≈ x · x) ＝ e≈
        inv-left≈ = /-induction ≋ (λ _ → /-is-set ≋) γ
          where
            γ : (x : ⟨ X ⟩) → (inv≈ (π≈ x) · π≈ x) ＝ e≈
            γ x = inv≈ (π≈ x) · π≈ x   ＝⟨ ap (λ v → v · π≈ x) (naturality/ ≋ (inv X) inv-cong x) ⟩
                  π≈ (inv X x) · π≈ x  ＝⟨ ·-natural (inv X x) x ⟩
                  π≈ (inv X x ·⟨ X ⟩ x) ＝⟨ ap π≈ (inv-left X x) ⟩
                  e≈ ∎

        inv-right≈ : (x : X≈) → (x · inv≈ x) ＝ e≈
        inv-right≈ = /-induction ≋ (λ _ → /-is-set ≋) γ
          where
            γ : (x : ⟨ X ⟩) → (π≈ x · inv≈ (π≈ x)) ＝ e≈
            γ x = π≈ x · inv≈ (π≈ x)   ＝⟨ ap (λ v → π≈ x · v) (naturality/ ≋ (inv X) inv-cong x) ⟩
                  π≈ x · π≈ (inv X x)  ＝⟨ ·-natural x (inv X x) ⟩
                  π≈ (x ·⟨ X ⟩ inv X x) ＝⟨ ap π≈ (inv-right X x) ⟩
                  e≈ ∎
\end{code}

The quotient map π≈ is a homomorphism.

FIXME: This fact has been already proven within the definition of the
quotient, so we just repeat that. We should rewrite this in a more
economical/elegant way, without repeating the proof.

\begin{code}

    quotient-map-is-hom : is-hom X quotient-gr (η/ ≋)
    quotient-map-is-hom {x} {y} = (naturality₂/ ≋ (multiplication X) binop-cong x y ) ⁻¹

\end{code}

On possible formulation of the universal property of quotients is that
if

φ : X → G

is a homomorphism such that φ (x) ＝ φ (y) whenever x ≈ y, then there
is a unique factorization with a homomorphism

φ≈ : X≈ → G

So we prove the map in the universality triangle is a homomorphism.

\begin{code}

    module _ {𝓦 : Universe}
             (G : Group 𝓦)
             (φ : ⟨ X ⟩ → ⟨ G ⟩)
             (i : is-hom X G φ)
             (p : identifies-related-points ≋ φ)
             where

      φ≈ : ⟨ quotient-gr ⟩ → ⟨ G ⟩
      φ≈ = mediating-map/ ≋ (groups-are-sets G) φ p

      mediating-map-is-hom : is-hom quotient-gr G φ≈
      mediating-map-is-hom {x} {y} = δ x y
        where
          X≈ : _
          X≈ = ⟨ quotient-gr ⟩

          π≈ : _
          π≈ = η/ ≋

          β : (s : ⟨ X ⟩) → φ≈ (π≈ s) ＝ φ (s)
          β s = universality-triangle/ ≋ _ φ _ s

          γ : (s t : ⟨ X ⟩) → φ≈ ((π≈ s) ·⟨ quotient-gr ⟩ (π≈ t)) ＝ (φ≈ (π≈ s) ·⟨ G ⟩ φ≈ (π≈ t))
          γ s t = φ≈ ((π≈ s) ·⟨ quotient-gr ⟩ (π≈ t))   ＝⟨ ap φ≈ (quotient-map-is-hom) ⁻¹ ⟩
                  φ≈ (π≈ (s ·⟨ X ⟩ t))                  ＝⟨ β _ ⟩
                  φ (s ·⟨ X ⟩ t)                        ＝⟨ i ⟩
                  φ (s) ·⟨ G ⟩ φ (t)                    ＝⟨ ap (λ v → v ·⟨ G ⟩ φ (t)) (β s) ⁻¹ ⟩
                  φ≈ (π≈ s) ·⟨ G ⟩ φ (t)                ＝⟨ ap (λ v → φ≈ (π≈ s) ·⟨ G ⟩ v) (β t) ⁻¹ ⟩
                  φ≈ (π≈ s) ·⟨ G ⟩ φ≈ (π≈ t) ∎

          δ : (x y : X≈) → φ≈ (x ·⟨ quotient-gr ⟩ y) ＝ (φ≈ x) ·⟨ G ⟩ (φ≈ y)
          δ = /-induction₂ fe ≋ (λ x' y' → groups-are-sets G) γ

\end{code}
