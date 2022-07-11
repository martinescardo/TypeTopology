--------------------------------------------------------------------------------
Ettore Aldrovandi aldrovandi@math.fsu.edu
Keri D'Angelo kd349@cornell.edu

July 2022
--------------------------------------------------------------------------------

TORSORS.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

open import SpartanMLTT
open import UF-Base hiding (_≈_)
open import UF-Subsingletons
open import UF-Powerset
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-Embeddings
open import UF-Univalence
open import UF-Equiv-FunExt
open import UF-FunExt
open import UF-UA-FunExt
open import UF-Subsingletons-FunExt
open import UF-Retracts
open import UF-Classifiers

open import Groups renaming (_≅_ to _≣_)
open import Groups.Groups-Supplement
open import Groups.GroupActions

module Groups.Torsors where

\end{code}


A G-torsor is a G-Set with nonempty underlying carrier and such that for
any x : X the right-multiplication map λ g → g · x is an equivalence.

This can be equivalently formulated by saying that the "shear" map
(g , x) → (g · x , x) is an equivalence.

Those two formulations are equivalent (both being props).

\begin{code}

is-torsor : (G : Group 𝓤) (𝕏 : G Sets) → 𝓤  ̇
is-torsor G (X , a) = is-nonempty X ×
                     ((x : X) → is-equiv (right-mult G {X , a} x))

is-torsor-is-prop : funext 𝓤 𝓤 → funext 𝓤 𝓤₀ →
                    (G : Group 𝓤) (𝕏 : G Sets) →
                    is-prop (is-torsor G 𝕏)
is-torsor-is-prop fe fe₀ G 𝕏 = ×-is-prop (negations-are-props fe₀)
          (Π-is-prop fe (λ x → being-equiv-is-prop'' fe (right-mult G {𝕏} x)))


is-torsor₁ : (G : Group 𝓤) (𝕏 : G Sets) → 𝓤 ̇
is-torsor₁ G 𝕏 = is-nonempty ⟨ 𝕏 ⟩ × is-equiv (mult G {𝕏})

is-torsor₁-is-prop : funext 𝓤 𝓤 → funext 𝓤 𝓤₀ →
                     (G : Group 𝓤) (𝕏 : G Sets) →
                     is-prop (is-torsor₁ G 𝕏)
is-torsor₁-is-prop fe fe₀ G 𝕏 = ×-is-prop (negations-are-props fe₀)
                   (being-equiv-is-prop'' fe (mult G {𝕏}))

torsor→torsor₁ : {G : Group 𝓤} (𝕏 : G Sets) →
                 is-torsor G 𝕏 → is-torsor₁ G 𝕏
torsor→torsor₁ {𝓤} {G} (X , a) (n , e) = n , ee
  where
    ee : is-equiv (mult G {X , a})
    ee = (u , ε) , v , η
      where
        u : X × X → ⟨ G ⟩ × X
        u ( y , x) = (pr₁ (pr₁ (e x)) y) , x

        ε : (mult G {X , a}) ∘ u ∼ id
        ε (y , x) = to-×-≡ (pr₂ (pr₁ (e x)) y) refl

        v : X × X → ⟨ G ⟩ × X
        v (y , x) = pr₁ (pr₂ (e x)) y , x

        η : v ∘ (mult G {X , a}) ∼ id
        η (g , x) = to-×-≡ (pr₂ (pr₂ (e x)) g) refl

torsor₁→torsor : {G : Group 𝓤} (𝕏 : G Sets) →
                 is-torsor₁ G 𝕏 → is-torsor G 𝕏
torsor₁→torsor {𝓤} {G} (X , a) (n , e) = n , ee
  where
    ee : (x : X) → is-equiv (right-mult G {X , a} x)
    ee x = (u , ε) , v , η
      where
        m : ⟨ G ⟩ × X → X × X
        m = mult G {X , a}
        r : ⟨ G ⟩ → X
        r = right-mult G {X , a} x

        ri li : X × X → ⟨ G ⟩ × X
        ri = pr₁ (pr₁ e)
        li = pr₁ (pr₂ e)

        e-ri : m ∘ ri ∼ id
        e-ri = pr₂ (pr₁ e)

        li-e : li ∘ m ∼ id
        li-e = pr₂ (pr₂ e)

        γ : (g : ⟨ G ⟩) → m (g , x) ≡ r g , x
        γ g = refl

        u : X → ⟨ G ⟩
        u y = pr₁ (ri (y , x))

        ε : r ∘ u ∼ id
        ε y = ap pr₁ q ⁻¹
          where
            p : pr₂ ( ri (y , x) ) ≡ x
            p = ap pr₂ (e-ri (y , x))

            q : y , x ≡ r (u y) , x
            q = y , x                      ≡⟨ e-ri (y , x) ⁻¹ ⟩
                m (ri (y , x))             ≡⟨ ap m refl ⟩
                m (u y , pr₂ (ri (y , x))) ≡⟨ ap (λ v → m (u y , v)) p ⟩
                m (u y , x)                ≡⟨ γ (u y) ⟩
                r (u y) , x ∎

        v : X → ⟨ G ⟩
        v y = pr₁ (li (y , x))

        η : v ∘ r ∼ id
        η g = ap pr₁ q ⁻¹
          where
            p : pr₂ (li (r g , x)) ≡ x
            p = ap pr₂ (li-e (g , x))

            q : g , x ≡ v (r g) , x
            q = g , x                        ≡⟨ li-e (g , x) ⁻¹ ⟩
                li (m (g , x))               ≡⟨ ap li (γ g) ⟩
                li (r g , x)                 ≡⟨ refl ⟩
                v (r g) , pr₂ (li (r g , x)) ≡⟨ ap (λ z → v (r g) , z) p ⟩
                v (r g) , x ∎
\end{code}


The type of G-Torsors.

\begin{code}

TORS Tors Torsor : (G : Group 𝓤) → (𝓤 ⁺) ̇
TORS G = Σ 𝕏 ꞉ Action G , is-torsor G 𝕏
Tors = TORS
Torsor = TORS

TORS' Tors' Torsor' : (G : Group 𝓤) → (𝓤 ⁺) ̇
TORS' {𝓤} G = Σ X ꞉ 𝓤 ̇ , Σ a ꞉ Action-structure G X , is-torsor G (X , a)
Tors' = TORS'
Torsor' = TORS'

torsor-equivalent-defs : {G : Group 𝓤} → TORS G ≃ TORS' G
torsor-equivalent-defs = Σ-assoc

underlying-action : {G : Group 𝓤} → (X : Tors G) →
                    Action G
underlying-action X = pr₁ X

torsor-carrier : {G : Group 𝓤} (X : Tors G) → 𝓤 ̇
torsor-carrier X = ⟨ pr₁ X  ⟩

torsor-prop : {G : Group 𝓤} (X : Tors G) → is-torsor G (pr₁ X)
torsor-prop X = pr₂ X

torsor-nonempty : {G : Group 𝓤} (X : Tors G) → is-nonempty (pr₁ (pr₁ X))
torsor-nonempty {𝓤} {G} X = pr₁ (torsor-prop {𝓤} {G} X)

torsor-splitting : {G : Group 𝓤} (X : Tors G) → 
                   ((x : ⟨ pr₁ X ⟩) → is-equiv (right-mult G {pr₁ X} x))
torsor-splitting {𝓤} {G} X = pr₂ (torsor-prop {𝓤} {G} X)

torsor-splitting₁ : {G : Group 𝓤} (X : Tors G) →
                    is-equiv (mult G {pr₁ X})
torsor-splitting₁ {G = G} X = pr₂ (torsor→torsor₁ {G = G} (pr₁ X) (pr₂ X))

torsor-to-equiv : {G : Group 𝓤} (X : Tors G) →
                  (x : torsor-carrier {G = G} X) → ⟨ G ⟩ ≃ (torsor-carrier {G = G} X)
torsor-to-equiv {G = G} X x = (right-mult G {pr₁ X} x) , torsor-splitting {G = G} X x

\end{code}

The equivalence G × X → X × X is the counterpart to the classical fact
that the "shear" map G × X → X × X given by (g , x) ↦ (g · x , x) is
an isomorphism. In classical geometry this implies that the inverse
also has x as its second component. In other words, pr₂ = x.

Not so here, as highligheted by the convoluted proof above where an
explicit proof that pr₂ ( inverse (mult) (y , x)) ≡ x was needed.  We
codify this fact, as it will be useful elsewhere.

\begin{code}

torsor-rinv-mult torsor-linv-mult : (G : Group 𝓤) (X : Tors G) →
                                    (⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩)
torsor-rinv-mult G X (y , x) = pr₁ (ri (y , x)) , x
  where
    m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
    m = mult G {pr₁ X}

    e : is-equiv m
    e = torsor-splitting₁ {G = G} X

    ri : ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩
    ri = pr₁ (pr₁ e)

torsor-linv-mult G X (y , x) = (pr₁ (li (y , x))) , x
  where
    m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
    m = mult G {pr₁ X}

    e : is-equiv m
    e = torsor-splitting₁ {G = G} X

    li : ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩
    li = pr₁ (pr₂ e)

torsor-rinv-mult-is-right-inverse : (G : Group 𝓤) (X : Tors G) → 
                                    (mult G {pr₁ X}) ∘ (torsor-rinv-mult G X) ∼ id
torsor-rinv-mult-is-right-inverse G X (y , x) =  q ⁻¹
  where
    m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
    m = mult G {pr₁ X}
    r : ⟨ G ⟩ → ⟨ pr₁ X ⟩
    r = right-mult G {pr₁ X} x

    e : is-equiv m
    e = torsor-splitting₁ {G = G} X

    ri : ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩
    ri = pr₁ (pr₁ e)

    e-ri : m ∘ ri ∼ id
    e-ri = pr₂ (pr₁ e)

    u : ⟨ pr₁ X ⟩ → ⟨ G ⟩
    u y = pr₁ (ri (y , x))

    p : pr₂ ( ri (y , x) ) ≡ x
    p = ap pr₂ (e-ri (y , x))

    q : y , x ≡ r (u y) , x
    q = y , x                      ≡⟨ e-ri (y , x) ⁻¹ ⟩
        m (ri (y , x))             ≡⟨ ap m refl ⟩
        m (u y , pr₂ (ri (y , x))) ≡⟨ ap (λ v → m (u y , v)) p ⟩
        m (u y , x)                ≡⟨ refl ⟩
        r (u y) , x ∎


torsor-linv-mult-is-left-inverse : (G : Group 𝓤) (X : Tors G) → 
                                   (torsor-linv-mult G X) ∘ (mult G {pr₁ X}) ∼ id
torsor-linv-mult-is-left-inverse G X (g , x) = q ⁻¹
  where
    m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
    m = mult G {pr₁ X}
    r : ⟨ G ⟩ → ⟨ pr₁ X ⟩
    r = right-mult G {pr₁ X} x

    e : is-equiv m
    e = torsor-splitting₁ {G = G} X

    li : ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩
    li = pr₁ (pr₂ e)

    li-e : li ∘ m ∼ id
    li-e = pr₂ (pr₂ e)

    v : ⟨ pr₁ X ⟩ → ⟨ G ⟩
    v y = pr₁ (li (y , x))

    p : pr₂ (li (r g , x)) ≡ x
    p = ap pr₂ (li-e (g , x))

    q : g , x ≡ v (r g) , x
    q = g , x                        ≡⟨ li-e (g , x) ⁻¹ ⟩
        li (m (g , x))               ≡⟨ ap li (refl) ⟩
        li (r g , x)                 ≡⟨ refl ⟩
        v (r g) , pr₂ (li (r g , x)) ≡⟨ ap (λ z → v (r g) , z) p ⟩
        v (r g) , x ∎

\end{code}

For two points x y of a G-torsor there is a unique g ∈ G bringing x to
y. This is the "quotient map" of the G-torsor. Note that in the proof
below we need both "inverses" of the shear map (see above).

\begin{code}

torsor-is-quotient : (G : Group 𝓤) (X : Tors G) (y x : ⟨ pr₁ X ⟩) → 
                      ∃! g ꞉ ⟨ G ⟩ , action-op G (pr₁ X) g x ≡ y
torsor-is-quotient G X y x = (g , ap pr₁ u) ,
               λ { (h , p) → to-Σ-≡ (ap pr₁ (ii h p) , carrier-is-set G (pr₁ X) _ _)}
    where
      gx : ⟨ G ⟩ × ⟨ pr₁ X ⟩
      gx = torsor-rinv-mult G X (y , x)

      g : ⟨ G ⟩
      g = pr₁ gx

      u : mult G {pr₁ X} gx ≡ y , x
      u = torsor-rinv-mult-is-right-inverse G X (y , x)

      m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
      m = mult G {pr₁ X}

      i : (h : ⟨ G ⟩) (p : action-op G (pr₁ X) h x ≡ y) → 
          m (g , x) ≡ m (h , x)
      i h p = m (g , x)                   ≡⟨ to-×-≡ (ap pr₁ u) refl ⟩
              y , x                       ≡⟨ to-×-≡ (p ⁻¹) refl ⟩
              action-op G (pr₁ X) h x , x ≡⟨ refl ⟩
              m (h , x) ∎

      ii : (h : ⟨ G ⟩) (p : action-op G (pr₁ X) h x ≡ y) →
           g , x ≡ h , x
      ii h p = g , x                            ≡⟨ q ⁻¹ ⟩
               torsor-linv-mult G X (m (g , x)) ≡⟨ ap (torsor-linv-mult G X) (i h p) ⟩
               torsor-linv-mult G X (m (h , x)) ≡⟨ r ⟩
               h , x ∎
                 where
                   q = torsor-linv-mult-is-left-inverse G X (g , x)
                   r = torsor-linv-mult-is-left-inverse G X (h , x)

torsor-quotient-map : {G : Group 𝓤} {X : Tors G} →
                      (y x : ⟨ pr₁ X ⟩) → ⟨ G ⟩
torsor-quotient-map {G = G} {X} y x = pr₁ (pr₁ (torsor-is-quotient G X y x ))

-- type as \ldiv
syntax torsor-quotient-map y x = y ∕ x
\end{code}
 

