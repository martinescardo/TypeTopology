--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

June 2022
--------------------------------------------------------------------------------

Group actions on sets and Torsors, following the UniMath blueprint. We
add a couple of things:

1. actions give homomorphisms into groups of automorphisms and
   vice-versa.
2. pullbacks of actions.
3. G Sets

Torsors are in their own file Torsos.lagda


\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Groups.Type renaming (_≅_ to _≣_)
open import MLTT.Spartan
open import UF.Base hiding (_≈_)
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.UA-FunExt
open import UF.Univalence

module Groups.GroupActions where

module _ (G : Group 𝓤) where

  action-structure : 𝓤 ̇ → 𝓤 ̇
  action-structure X = ⟨ G ⟩ → X → X

  action-axioms : (X : 𝓤 ̇ ) → action-structure X → 𝓤 ̇
  action-axioms X _·_ = is-set X ×
                        ((g h : ⟨ G ⟩)(x : X) → (g ·⟨ G ⟩ h) · x ＝ g · (h · x)) ×
                        ((x : X) → (unit G) · x ＝ x)

  Action-structure : 𝓤 ̇ → 𝓤 ̇
  Action-structure X = Σ _·_ ꞉ action-structure X , (action-axioms X _·_)

  Action : 𝓤 ⁺ ̇
  Action = Σ X ꞉ 𝓤 ̇ , Action-structure X


  action-carrier : Action → 𝓤 ̇
  action-carrier (X , _ ) = X

  action-op : (𝕏 : Action) → action-structure ⟨ 𝕏 ⟩
  action-op (X , op , _) = op

  carrier-is-set : (𝕏 : Action) → is-set (action-carrier 𝕏)
  carrier-is-set (X , op , i , _) = i

  action-assoc : (𝕏 : Action) (g h : ⟨ G ⟩) (x : ⟨ 𝕏 ⟩)
               →  (action-op 𝕏) (g ·⟨ G ⟩ h) x ＝ (action-op 𝕏) g ((action-op 𝕏) h x)
  action-assoc (X , op , i , a , u) = a

  action-unit : (𝕏 : Action) (x : ⟨ 𝕏 ⟩)
              →  (action-op 𝕏) (unit G) x ＝ x
  action-unit (X , op , i , a , u) = u

  action-tofun : (𝕏 : Action) (g : ⟨ G ⟩) → ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩
  action-tofun 𝕏 g = λ x → action-op 𝕏 g x

  action-to-fun = action-tofun

  action-tofun-is-equiv : (𝕏 : Action) (g : ⟨ G ⟩) → is-equiv (action-tofun 𝕏 g)
  action-tofun-is-equiv 𝕏 g =
            (f⁻¹ , λ x → (f (f⁻¹ x)                   ＝⟨ (action-assoc 𝕏 _ _ _) ⁻¹ ⟩
                          (g ·⟨ G ⟩ (inv G g)) ◂⟨ 𝕏 ⟩ x ＝⟨ ap (λ v → v ◂⟨ 𝕏 ⟩ x) (inv-right G g) ⟩
                          (unit G) ◂⟨ 𝕏 ⟩ x            ＝⟨ action-unit 𝕏 x  ⟩
                           x ∎)) ,
            (f⁻¹ , λ x → (f⁻¹ (f x)                   ＝⟨ (action-assoc 𝕏 _ _ _) ⁻¹ ⟩
                          ((inv G g) ·⟨ G ⟩ g) ◂⟨ 𝕏 ⟩ x ＝⟨ ap (λ v → v ◂⟨ 𝕏 ⟩ x) (inv-left G g) ⟩
                          (unit G) ◂⟨ 𝕏 ⟩ x            ＝⟨ action-unit 𝕏 x ⟩
                           x  ∎))
    where
      _◂⟨_⟩_ : ⟨ G ⟩ → (𝕏 : Action) → ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩
      g ◂⟨ 𝕏 ⟩ x = action-op 𝕏 g x

      f : ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩
      f = action-tofun 𝕏 g

      f⁻¹ : ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩
      f⁻¹ = action-tofun 𝕏 (inv G g)

  action-to-fun-is-equiv = action-tofun-is-equiv

  action-to-Aut : (𝕏 : Action) (g : ⟨ G ⟩) → Aut ⟨ 𝕏 ⟩
  action-to-Aut 𝕏 g = (action-to-fun 𝕏 g) , action-to-fun-is-equiv 𝕏 g

  -- same names as in UniMath
  left-mult = action-to-fun
  right-mult : (𝕏 : Action) (x : ⟨ 𝕏 ⟩) → ⟨ G ⟩ → ⟨ 𝕏 ⟩
  right-mult 𝕏 x = λ g → action-op 𝕏 g x
  ----------------------------------

  -- the total action map is often used, especially for torsors
  ------------------------------------------------------------
  mult : (𝕏 : Action)
       →  ⟨ G ⟩ × ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩ × ⟨ 𝕏 ⟩
  mult 𝕏 (g , x) = action-op 𝕏 g x , x

\end{code}

In this submodule we prove that an action as defined above induces a
homomorphism from the group G to the automorphism group of the carrier
set. It requires funext 𝓤 𝓤 because Aut (X) (as a group)
does. Conversely, a homomorphism to Aut (X) gives an action.

\begin{code}
  module to-automorphism (fe : funext 𝓤 𝓤)
                         (𝕏 : Action)
                           where

    open import Groups.Aut
    open import Groups.Opposite

    is-hom-action-to-fun : is-hom G ((𝔸ut fe ⟨ 𝕏 ⟩ (carrier-is-set 𝕏)) ᵒᵖ) (action-to-Aut 𝕏)
    is-hom-action-to-fun {g} {h} =
                         to-Σ-＝ ((dfunext fe (λ x → action-assoc 𝕏 g h x)) ,
                                  being-equiv-is-prop'' fe (λ x → g · (h · x)) _ _)
                         where
                                   _·_ : ⟨ G ⟩ → ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩
                                   _·_ = action-op 𝕏


  module from-automorphism (fe : funext 𝓤 𝓤)
                           (X : 𝓤 ̇ )(i : is-set X)
                           (σ : ⟨ G ⟩ → Aut X)
                             where
    open import Groups.Aut
    open import Groups.Opposite

    hom-to-Aut-gives-action : is-hom G ((𝔸ut fe X i) ᵒᵖ ) σ → Action
    hom-to-Aut-gives-action is = X , ((λ g → pr₁ (σ g)) ,
                            (i , (λ g h → happly (ap pr₁ (is {g} {h}))) ,
                             λ x → ( pr₁ (σ (unit G)) x  ＝⟨ happly (ap pr₁ t) x ⟩
                                     pr₁ (unit 𝔸utX) x    ＝⟨ happly' id id refl x ⟩
                                     x ∎ ) ) )
      where
        𝔸utX : Group 𝓤
        𝔸utX = 𝔸ut fe X i
        t : σ (unit G) ＝ unit 𝔸utX
        t = homs-preserve-unit G ((𝔸ut fe X i) ᵒᵖ ) σ is


\end{code}

Resuming the general theory, the group action axioms form a proposition
and the Action-structure is a set.

\begin{code}
  action-axioms-is-prop : funext 𝓤 𝓤
                        → (X : 𝓤 ̇ )
                        → (_·_ : action-structure X)
                        → is-prop (action-axioms X _·_)
  action-axioms-is-prop fe X _·_ s = γ s
    where
      i : is-set X
      i = pr₁ s

      γ : is-prop (action-axioms X _·_)
      γ = ×-is-prop (being-set-is-prop fe)
                    (×-is-prop (Π-is-prop fe
                                  (λ g → Π-is-prop fe
                                     (λ h → Π-is-prop fe
                                        (λ x → i))))
                        (Π-is-prop fe (λ x → i)))


  Action-structure-is-set : funext 𝓤 𝓤
                          → (X : 𝓤 ̇ )
                          → is-set (Action-structure X)
  Action-structure-is-set fe X {s} = γ {s}
    where
      i : is-set X
      i = pr₁ (pr₂ s)

      γ : is-set (Action-structure X)
      γ = Σ-is-set (Π-is-set fe
                      (λ g → Π-is-set fe
                               (λ x → i)))
            λ op → props-are-sets (action-axioms-is-prop fe X op)

\end{code}


Equivariant maps.

\begin{code}

  is-equivariant : (𝕏 𝕐 : Action) (f : ⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩) → 𝓤 ̇
  is-equivariant 𝕏 𝕐 f = ∀ g x → f (g · x) ＝ g * (f x)
    where
      _·_ = action-op 𝕏
      _*_ = action-op 𝕐


  is-equivariant-is-prop : funext 𝓤 𝓤
                         → (𝕏 𝕐 : Action) → (f : ⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩)
                         → is-prop (is-equivariant 𝕏 𝕐 f)
  is-equivariant-is-prop fe 𝕏 𝕐 f s = γ s
    where
      i : is-set (action-carrier 𝕐)
      i = carrier-is-set 𝕐

      γ : is-prop (is-equivariant 𝕏 𝕐 f)
      γ = Π-is-prop fe
                    (λ g → Π-is-prop fe
                                     (λ x → i))

  is-equivariant-comp : (𝕏 𝕐 ℤ : Action)
                      → (p : ⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩) (i : is-equivariant 𝕏 𝕐 p)
                      → (q : ⟨ 𝕐 ⟩ → ⟨ ℤ ⟩) (j : is-equivariant 𝕐 ℤ q)
                      → (is-equivariant 𝕏 ℤ (q ∘ p))
  is-equivariant-comp 𝕏 𝕐 ℤ p i q j g x = q (p (g · x)) ＝⟨ ap q (i g x) ⟩
                                          q (g * (p x)) ＝⟨ j g (p x) ⟩
                                          g ✵ (q (p x)) ∎
    where
      _·_ = action-op 𝕏
      _*_ = action-op 𝕐
      _✵_ = action-op ℤ

\end{code}

The following "fundamental" fact from UniMath is that an
identification p : ⟨ 𝕏 ⟩ ＝ ⟨ 𝕐 ⟩ between the carriers of two actions
essentially gives rise to an equivariant map. More precisely,
equivariance of the identity is the same as the identification of the
structures.

\begin{code}

  ＝-is-equivariant : funext 𝓤 𝓤
                    → (𝕏 𝕐 : Action)
                    → (p : ⟨ 𝕏 ⟩ ＝ ⟨ 𝕐 ⟩)
                    → (transport Action-structure p (pr₂ 𝕏)  ＝ pr₂ 𝕐 ) ≃
                     is-equivariant 𝕏 𝕐 (idtofun ⟨ 𝕏 ⟩ ⟨ 𝕐 ⟩ p)
  pr₁ (＝-is-equivariant fe (X , as) (.X , .as) refl) refl = λ g x → refl
  pr₂ (＝-is-equivariant fe (X , as) (.X , as') refl) =
    logical-equivs-of-props-are-equivs
      is (is-equivariant-is-prop fe ((X , as)) (X , as') id)
        (pr₁ (＝-is-equivariant fe (X , as) (X , as') refl))
        λ i → to-Σ-＝ ((γ i) , (action-axioms-is-prop fe X _·'_ _ _))
      where
        _·_ _·'_ : action-structure X
        _·_  = pr₁ as
        _·'_ = pr₁ as'

        is : is-prop (as ＝ as')
        is = Action-structure-is-set fe X {as} {as'}

        γ : is-equivariant (X , as) (X , as') id → _·_ ＝ _·'_
        γ = λ i → dfunext fe
                  (λ g → dfunext fe λ x → i g x)
\end{code}

The above function is called is_equivariant_identity in UniMath.

\begin{code}

  Action-Map : (𝕏 𝕐 : Action) → 𝓤 ̇
  Action-Map 𝕏 𝕐 = Σ f ꞉ (⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩) , is-equivariant 𝕏 𝕐 f

  underlying-function : (𝕏 𝕐 : Action) (u : Action-Map 𝕏 𝕐) → ⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩
  underlying-function _ _ u = pr₁ u

  equivariance : {𝕏 𝕐 : Action} (u : Action-Map 𝕏 𝕐) →
                 is-equivariant 𝕏 𝕐 (underlying-function 𝕏 𝕐 u)
  equivariance u = pr₂ u


  Action-Map-is-set : funext 𝓤 𝓤
                    → (𝕏 𝕐 : Action)
                    → is-set (Action-Map 𝕏 𝕐)
  Action-Map-is-set fe 𝕏 𝕐 {s} = γ {s}
    where
      γ : is-set (Action-Map 𝕏 𝕐)
      γ = Σ-is-set (Π-is-set fe
                     (λ u → carrier-is-set 𝕐))
                   λ f → props-are-sets (is-equivariant-is-prop fe 𝕏 𝕐 f)

  compose-Action-Map : {𝕏 𝕐 ℤ : Action}
                     → (Action-Map 𝕏 𝕐) → (Action-Map 𝕐 ℤ)
                     → (Action-Map 𝕏 ℤ)
  compose-Action-Map {𝕏} {𝕐} {ℤ} (p , i) (q , j) =
                     (q ∘ p) , (is-equivariant-comp 𝕏 𝕐 ℤ p i q j)

  Action-Iso : (𝕏 𝕐 : Action) → 𝓤 ̇
  Action-Iso 𝕏 𝕐 = Σ f ꞉ ⟨ 𝕏 ⟩ ≃ ⟨ 𝕐 ⟩ , is-equivariant 𝕏 𝕐 (eqtofun f)

  Action-Iso-is-set : funext 𝓤 𝓤
                    → (𝕏 𝕐 : Action)
                    → is-set (Action-Iso 𝕏 𝕐)
  Action-Iso-is-set fe 𝕏 𝕐 {s} = γ {s}
    where
      γ : is-set (Action-Iso 𝕏 𝕐)
      γ = Σ-is-set (Σ-is-set (Π-is-set fe (λ _ → carrier-is-set 𝕐))
                             λ f → props-are-sets (being-equiv-is-prop'' fe f))
                   λ u → props-are-sets (is-equivariant-is-prop fe 𝕏 𝕐 (pr₁ u))

  underlying-iso : (𝕏 𝕐 : Action) → Action-Iso 𝕏 𝕐 → ⟨ 𝕏 ⟩ ≃ ⟨ 𝕐 ⟩
  underlying-iso 𝕏 𝕐 u = pr₁ u

  underlying-iso-is-embedding : funext 𝓤 𝓤
                              → (𝕏 𝕐 : Action)
                              → is-embedding (underlying-iso 𝕏 𝕐)
  underlying-iso-is-embedding fe 𝕏 𝕐 =
    pr₁-is-embedding (λ f → is-equivariant-is-prop fe 𝕏 𝕐 (pr₁ f))

  underlying-iso-injectivity : funext 𝓤 𝓤
                             → (𝕏 𝕐 : Action)
                             → (u v : Action-Iso 𝕏 𝕐)
                             → (u ＝ v) ≃ (underlying-iso 𝕏 𝕐 u ＝ underlying-iso 𝕏 𝕐 v)
  underlying-iso-injectivity fe 𝕏 𝕐 u v =
    ≃-sym (embedding-criterion-converse
             (underlying-iso 𝕏 𝕐)
             (underlying-iso-is-embedding fe 𝕏 𝕐) u v)


  underlying-Action-Map : (𝕏 𝕐 : Action) → Action-Iso 𝕏 𝕐
                        → Action-Map 𝕏 𝕐
  underlying-Action-Map _ _ ((f , _) , is) = f , is

  id-Action-Iso : (𝕏 : Action) → Action-Iso 𝕏 𝕏
  id-Action-Iso 𝕏 = (id , (id-is-equiv ⟨ 𝕏 ⟩)) , (λ g x → refl)

  ＝-to-Action-Iso : {𝕏 𝕐 : Action}
                   → 𝕏 ＝ 𝕐 → Action-Iso 𝕏 𝕐
  ＝-to-Action-Iso {𝕏} {𝕐} p = transport (Action-Iso 𝕏) p (id-Action-Iso 𝕏)

  ＝-to-Action-Iso₁ : {𝕏 𝕐 : Action}
                    → 𝕏 ＝ 𝕐 → Action-Iso 𝕏 𝕐
  ＝-to-Action-Iso₁ {𝕏} {.𝕏} refl = id-Action-Iso 𝕏

  ＝-to-Action-Iso-compare : {𝕏 𝕐 : Action} → (u : 𝕏 ＝ 𝕐)
                           → ＝-to-Action-Iso {𝕏} {𝕐} u ＝ ＝-to-Action-Iso₁ {𝕏} {𝕐} u
  ＝-to-Action-Iso-compare {𝕏} {.𝕏} refl = refl


  compose-Action-Iso : {𝕏 𝕐 ℤ : Action}
                     → Action-Iso 𝕏 𝕐 → Action-Iso 𝕐 ℤ
                     → Action-Iso 𝕏 ℤ
  compose-Action-Iso {𝕏} {𝕐} {ℤ} (f , i) (g , j) =
                     (f ● g) , (is-equivariant-comp 𝕏 𝕐 ℤ (pr₁ f) i (pr₁ g) j)

  compose-Action-Iso-id : funext 𝓤 𝓤
                        → {𝕏 𝕐 : Action} → (u : Action-Iso 𝕏 𝕐)
                        → compose-Action-Iso {𝕏} {𝕐} {𝕐} u (id-Action-Iso 𝕐) ＝ u
  compose-Action-Iso-id fe {𝕏} {𝕐} u = to-subtype-＝
                           (λ f → is-equivariant-is-prop fe 𝕏 𝕐 (eqtofun f))
                           (≃-refl-right' fe fe fe (pr₁ u))

  compose-id-Action-Iso : funext 𝓤 𝓤
                        → {𝕏 𝕐 : Action} → (u : Action-Iso 𝕏 𝕐)
                        → compose-Action-Iso {𝕏} {𝕏} {𝕐} (id-Action-Iso 𝕏) u ＝ u
  compose-id-Action-Iso fe {𝕏} {𝕐} u = to-subtype-＝
                           (λ f → is-equivariant-is-prop fe 𝕏 𝕐 (eqtofun f))
                           (≃-refl-left' fe fe fe (pr₁ u))
\end{code}

Univalence for group actions. The abstract clause below is to speed up
type-checking.

\begin{code}

  module _ (ua : is-univalent 𝓤) where

    private
      fe : funext 𝓤 𝓤
      fe = univalence-gives-funext ua

    Id-equiv-Action-Iso_prelim : (𝕏 𝕐 : Action)
                               → (𝕏 ＝ 𝕐) ≃ (Action-Iso 𝕏 𝕐)
    Id-equiv-Action-Iso_prelim 𝕏 𝕐 = ≃-comp (Φ , ll) (Ψ , ii)
      where
        T : (𝕏 𝕐 : Action) → (𝓤 ⁺) ̇
        T 𝕏 𝕐 = Σ u ꞉ ⟨ 𝕏 ⟩ ＝ ⟨ 𝕐 ⟩ , transport Action-structure u (pr₂ 𝕏) ＝ pr₂ 𝕐

        Φ : (𝕏 ＝ 𝕐) → T 𝕏 𝕐
        Φ = from-Σ-＝

        Φ' : T 𝕏 𝕐 → (𝕏 ＝ 𝕐)
        Φ' = to-Σ-＝

        Ψ : T 𝕏 𝕐 → Action-Iso 𝕏 𝕐
        Ψ (p , is) = (idtoeq ⟨ 𝕏 ⟩ ⟨ 𝕐 ⟩ p) , pr₁ (＝-is-equivariant fe 𝕏 𝕐 p) is

        abstract
          Ψ' : Action-Iso 𝕏 𝕐 → T 𝕏 𝕐
          Ψ' (e , is) = p , pr₁ (≃-sym (＝-is-equivariant fe 𝕏 𝕐 p)) i
            where
              p : ⟨ 𝕏 ⟩ ＝ ⟨ 𝕐 ⟩
              p = eqtoid ua ⟨ 𝕏 ⟩ ⟨ 𝕐 ⟩ e
              i : is-equivariant 𝕏 𝕐 (idtofun ⟨ 𝕏 ⟩ ⟨ 𝕐 ⟩ p)
              i = transport (is-equivariant 𝕏 𝕐) (t ⁻¹) is
                where
                  t : idtofun ⟨ 𝕏 ⟩ ⟨ 𝕐 ⟩ p ＝ eqtofun e
                  t = idtofun-eqtoid ua e

          Ψ'Ψ-id : (σ : T 𝕏 𝕐) → Ψ' (Ψ σ) ＝ σ
          Ψ'Ψ-id (p , is) = to-Σ-＝ (eqtoid-idtoeq ua ⟨ 𝕏 ⟩ ⟨ 𝕐 ⟩ p ,
                                   Action-structure-is-set fe _ _ _)

          ΨΨ'-id : (u : Action-Iso 𝕏 𝕐) → Ψ (Ψ' u) ＝ u
          ΨΨ'-id (e , is) = to-Σ-＝ ((idtoeq-eqtoid ua ⟨ 𝕏 ⟩ ⟨ 𝕐 ⟩ e) ,
                                   (is-equivariant-is-prop fe 𝕏 𝕐 _ _ _))
        ii : is-equiv Ψ
        ii = qinvs-are-equivs Ψ inv-Ψ
          where
            inv-Ψ : invertible Ψ
            inv-Ψ = Ψ' , (Ψ'Ψ-id , ΨΨ'-id)

        ll : is-equiv Φ
        ll = qinvs-are-equivs Φ inv-Φ
          where
            inv-Φ : invertible Φ
            inv-Φ = Φ' , (tofrom-Σ-＝ , fromto-Σ-＝)


    ＝-to-Action-Iso-is-equiv : {𝕏 𝕐 : Action}
                              → is-equiv (＝-to-Action-Iso {𝕏} {𝕐})
    ＝-to-Action-Iso-is-equiv {𝕏} {𝕐} = equiv-closed-under-∼'
                             (pr₂ (Id-equiv-Action-Iso_prelim 𝕏 𝕐)) h
      where
        f = pr₁ (Id-equiv-Action-Iso 𝕏 prelim 𝕐)
        g = ＝-to-Action-Iso
        h : f ∼ g
        h refl = refl


    Id-equiv-Action-Iso : (𝕏 𝕐 : Action)
                        → (𝕏 ＝ 𝕐) ≃ (Action-Iso 𝕏 𝕐)
    Id-equiv-Action-Iso 𝕏 𝕐 = ＝-to-Action-Iso , ＝-to-Action-Iso-is-equiv

\end{code}

A shorthand for the action structure. Convenient in function signature types.

\begin{code}

action-op-syntax : (G : Group 𝓤) (𝕏 : Action G) → action-structure G ⟨ 𝕏 ⟩
action-op-syntax G 𝕏 = action-op G 𝕏
syntax action-op-syntax G 𝕏 g x = g ◂⟨ G ∣ 𝕏 ⟩ x

\end{code}

When explicitly expressed in terms of a group G, the type Action is
just that of G-Sets, so we also use this notation.

\begin{code}

_Sets : Group 𝓤 → 𝓤 ⁺ ̇
G Sets = Action G

\end{code}

For a group homomorphism φ : H → G the action pulls back, because it
is a functor from the one-object category G[1] to sets.

\begin{code}

action-pullback : {H G : Group 𝓤}
                → (f : ⟨ H ⟩ → ⟨ G ⟩) → is-hom H G f
                → G Sets → H Sets
action-pullback {H = H} {G} f i ρ = (action-carrier G ρ) ,
                (λ h x → (f h) · x) ,
                  (carrier-is-set G ρ) ,
                    ((λ h h₁ → λ x → (f (h ·⟨ H ⟩ h₁) · x       ＝⟨ ap (_· x) i ⟩
                                      ((f h) ·⟨ G ⟩ (f h₁)) · x ＝⟨ action-assoc G ρ _ _ _ ⟩
                                      (f h · (f h₁ · x)) ∎  )) ,
                     λ x → (f (unit H) · x ＝⟨ ap (_· x) p ⟩
                            unit G · x     ＝⟨ action-unit G ρ x ⟩
                            x  ∎))
  where
    _·_ = action-op G ρ
    p  = homs-preserve-unit H G f i
\end{code}

TODO: The left adjoint, that is, the map H Sets → G Sets along the
homomorphism H → G. It uses the quotient module.
