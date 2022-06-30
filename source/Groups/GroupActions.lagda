--------------------------------------------------------------------------------
Ettore Aldrovandi aldrovandi@math.fsu.edu
Keri D'Angelo kd349@cornell.edu

June 2022
--------------------------------------------------------------------------------

Group actions on sets.

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

module Groups.GroupActions where

module _ (G : Group 𝓤) where

  action-structure : 𝓤 ̇ → 𝓤 ̇
  action-structure X = ⟨ G ⟩ → X → X

  action-axioms : (X : 𝓤 ̇) → action-structure X → 𝓤 ̇
  action-axioms X _·_ = is-set X ×
                        ((g h : ⟨ G ⟩)(x : X) → (g ·⟨ G ⟩ h) · x ≡ g · (h · x)) ×
                        ((x : X) → (unit G) · x ≡ x)

  Action-structure : 𝓤 ̇ → 𝓤 ̇
  Action-structure X = Σ _·_ ꞉ action-structure X , (action-axioms X _·_)

  Action : 𝓤 ⁺ ̇
  Action = Σ X ꞉ 𝓤 ̇ , Action-structure X


  action-carrier : Action → 𝓤 ̇
  action-carrier (X , _ ) = X

  action-op : (𝕏 : Action) → action-structure ⟨ 𝕏 ⟩
  action-op (X , op , _) = op

  syntax action-op 𝕏 g x = g ◂⟨ 𝕏 ⟩ x

  carrier-is-set : (𝕏 : Action) → is-set (action-carrier 𝕏)
  carrier-is-set (X , op , i , _) = i

  action-assoc : (𝕏 : Action) (g h : ⟨ G ⟩) (x : ⟨ 𝕏 ⟩) →
                 (action-op 𝕏) (g ·⟨ G ⟩ h) x ≡ (action-op 𝕏) g ((action-op 𝕏) h x)
  action-assoc (X , op , i , a , u) = a

  action-unit : (𝕏 : Action) (x : ⟨ 𝕏 ⟩) →
                (action-op 𝕏) (unit G) x ≡ x
  action-unit (X , op , i , a , u) = u

  action-tofun : {𝕏 : Action} (g : ⟨ G ⟩) → ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩
  action-tofun {𝕏} g = λ x → action-op 𝕏 g x

  action-to-fun = action-tofun

  action-tofun-is-equiv : {𝕏 : Action} (g : ⟨ G ⟩) →
                          is-equiv (action-tofun {𝕏} g)
  action-tofun-is-equiv {𝕏} g =
            (f⁻¹ , λ x → (f (f⁻¹ x)                   ≡⟨ (action-assoc 𝕏 _ _ _) ⁻¹ ⟩
                          (g ·⟨ G ⟩ (inv G g)) ◂⟨ 𝕏 ⟩ x ≡⟨ ap (λ v → v ◂⟨ 𝕏 ⟩ x) (inv-right G g) ⟩
                          (unit G) ◂⟨ 𝕏 ⟩ x            ≡⟨ action-unit 𝕏 x  ⟩
                           x ∎)) ,
            (f⁻¹ , λ x → (f⁻¹ (f x)                   ≡⟨ (action-assoc 𝕏 _ _ _) ⁻¹ ⟩
                          ((inv G g) ·⟨ G ⟩ g) ◂⟨ 𝕏 ⟩ x ≡⟨ ap (λ v → v ◂⟨ 𝕏 ⟩ x) (inv-left G g) ⟩
                          (unit G) ◂⟨ 𝕏 ⟩ x            ≡⟨ action-unit 𝕏 x ⟩
                           x  ∎))
    where
      f : ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩
      f = action-tofun {𝕏} g

      f⁻¹ : ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩
      f⁻¹ = action-tofun {𝕏} (inv G g)

  action-to-fun-is-equiv = action-tofun-is-equiv

  action-to-Aut : {𝕏 : Action} (g : ⟨ G ⟩) → Aut ⟨ 𝕏 ⟩
  action-to-Aut {𝕏} g = (action-to-fun {𝕏} g) , action-to-fun-is-equiv {𝕏} g

\end{code}

In this submodule we prove that an action as defined above induces a
homomorphism from the group ot the automorphism group of the carrier
set.

\begin{code}
  module automorphism (fe : funext 𝓤 𝓤) (𝕏 : Action) where

    open import Groups.Aut

    private
      X : 𝓤 ̇
      X = ⟨ 𝕏 ⟩
      i : is-set X
      i = carrier-is-set 𝕏
      _·_ : ⟨ G ⟩ → X → X
      _·_ = action-op 𝕏

      j : is-set (Aut X)
      j = is-set-Aut fe X i

      gr-s-X : _
      gr-s-X = Group-structure-Aut fe X i

    is-hom-action-to-fun : is-hom G (Aut X , gr-s-X) (action-to-Aut {𝕏})
    is-hom-action-to-fun {g} {h} =
                         to-Σ-≡ ((dfunext fe (action-assoc 𝕏 g h)) ,
                           (being-equiv-is-prop'' fe (λ x → g · (h · x)) _ _))
    
\end{code}

Resume the general theory. The group action axioms form a proposition
and the Action-structure is a set.

\begin{code}
  action-axioms-is-prop : funext 𝓤 𝓤 →
                          (X : 𝓤 ̇) →
                          (_·_ : action-structure X) →
                          is-prop (action-axioms X _·_)
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


  Action-structure-is-set : funext 𝓤 𝓤 →
                            (X : 𝓤 ̇) →
                            is-set (Action-structure X)
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

TODO: Prove a SIP as in UniMath: two actions for which the identity is
equivariant (hence same carrier) are the same.

\begin{code}

  is-equivariant : {𝕏 𝕐 : Action} (f : ⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩) → 𝓤 ̇
  is-equivariant {𝕏} {𝕐} f = ∀ g x → f (g · x) ≡ g * (f x)
    where
      _·_ = action-op 𝕏
      _*_ = action-op 𝕐


  is-equivariant-is-prop : funext 𝓤 𝓤 →
                           {𝕏 𝕐 : Action} → (f : ⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩) →
                           is-prop (is-equivariant {𝕏} {𝕐} f)
  is-equivariant-is-prop fe {𝕏} {𝕐} f s = γ s
    where
      i : is-set (action-carrier 𝕐)
      i = carrier-is-set 𝕐
      
      γ : is-prop (is-equivariant {𝕏} {𝕐} f)
      γ = Π-is-prop fe
                    (λ g → Π-is-prop fe
                                     (λ x → i))

  is-equivariant-comp : {𝕏 𝕐 ℤ : Action} →
                        (p : ⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩) (i : is-equivariant {𝕏} {𝕐} p) →
                        (q : ⟨ 𝕐 ⟩ → ⟨ ℤ ⟩) (j : is-equivariant {𝕐} {ℤ} q) → 
                        (is-equivariant {𝕏} {ℤ} (q ∘ p))
  is-equivariant-comp {𝕏} {𝕐} {ℤ} p i q j g x = q (p (g · x)) ≡⟨ ap q (i g x) ⟩
                                                q (g * (p x)) ≡⟨ j g (p x) ⟩
                                                g ✵ (q (p x)) ∎
    where
      _·_ = action-op 𝕏
      _*_ = action-op 𝕐
      _✵_ = action-op ℤ


  Action-Map : (𝕏 𝕐 : Action) → 𝓤  ̇
  Action-Map 𝕏 𝕐 = Σ f ꞉ (⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩) , is-equivariant {𝕏} {𝕐} f

  underlying-function : {𝕏 𝕐 : Action} (u : Action-Map 𝕏 𝕐) → ⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩
  underlying-function u = pr₁ u

  equivariance : {𝕏 𝕐 : Action} (u : Action-Map 𝕏 𝕐) → 
                 is-equivariant {𝕏} {𝕐} (underlying-function {𝕏} {𝕐} u)
  equivariance u = pr₂ u


  Action-Map-is-set : funext 𝓤 𝓤 →
                      (𝕏 𝕐 : Action) →
                      is-set (Action-Map 𝕏 𝕐)
  Action-Map-is-set fe 𝕏 𝕐 {s} = γ {s}
    where
      γ : is-set (Action-Map 𝕏 𝕐)
      γ = Σ-is-set (Π-is-set fe
                     (λ u → carrier-is-set 𝕐))
                   λ f → props-are-sets (is-equivariant-is-prop fe {𝕏} {𝕐} f)

  compose-Action-Map : {𝕏 𝕐 ℤ : Action} →
                       (Action-Map 𝕏 𝕐) → (Action-Map 𝕐 ℤ) →
                       (Action-Map 𝕏 ℤ)
  compose-Action-Map {𝕏} {𝕐} {ℤ} (p , i) (q , j) =
                     (q ∘ p) , (is-equivariant-comp {𝕏} {𝕐} {ℤ} p i q j)

  Action-Iso : (𝕏 𝕐 : Action) → 𝓤 ̇
  Action-Iso 𝕏 𝕐 = Σ f ꞉ ⟨ 𝕏 ⟩ ≃ ⟨ 𝕐 ⟩ , is-equivariant {𝕏} {𝕐} (eqtofun f)

  Action-Iso-is-set : funext 𝓤 𝓤 →
                      (𝕏 𝕐 : Action) →
                      is-set (Action-Iso 𝕏 𝕐)
  Action-Iso-is-set fe 𝕏 𝕐 {s} = γ {s}
    where
      γ : is-set (Action-Iso 𝕏 𝕐)
      γ = Σ-is-set (Σ-is-set (Π-is-set fe (λ _ → carrier-is-set 𝕐))
                             λ f → props-are-sets (being-equiv-is-prop'' fe f))
                   λ u → props-are-sets (is-equivariant-is-prop fe {𝕏} {𝕐} (pr₁ u))

  underlying-iso : {𝕏 𝕐 : Action} → Action-Iso 𝕏 𝕐 → ⟨ 𝕏 ⟩ ≃ ⟨ 𝕐 ⟩
  underlying-iso u = pr₁ u
                   
  underlying-iso-is-embedding : funext 𝓤 𝓤 →
                                {𝕏 𝕐 : Action} →
                                is-embedding (underlying-iso {𝕏} {𝕐} )
  underlying-iso-is-embedding fe {𝕏} {𝕐} =
    pr₁-is-embedding (λ f → is-equivariant-is-prop fe {𝕏} {𝕐} (pr₁ f))
                           
  underlying-iso-injectivity : funext 𝓤 𝓤 → 
                               {𝕏 𝕐 : Action} →
                               (u v : Action-Iso 𝕏 𝕐) →
                               (u ≡ v) ≃ (underlying-iso {𝕏} {𝕐} u ≡ underlying-iso {𝕏} {𝕐} v)
  underlying-iso-injectivity fe {𝕏} {𝕐} u v =
    ≃-sym (embedding-criterion-converse
             (underlying-iso {𝕏} {𝕐})
             (underlying-iso-is-embedding fe {𝕏} {𝕐}) u v) 

  
  underlying-Action-Map : {𝕏 𝕐 : Action} → Action-Iso 𝕏 𝕐 →
                          Action-Map 𝕏 𝕐
  underlying-Action-Map ((f , _) , is) = f , is

  id-Action-Iso : (𝕏 : Action) → Action-Iso 𝕏 𝕏
  id-Action-Iso 𝕏 = (id , (id-is-equiv ⟨ 𝕏 ⟩)) , (λ g x → refl)

  ≡-to-Action-Iso : {𝕏 𝕐 : Action} →
                    𝕏 ≡ 𝕐 → Action-Iso 𝕏 𝕐
  ≡-to-Action-Iso {𝕏} {.𝕏} refl = id-Action-Iso 𝕏

  compose-Action-Iso : {𝕏 𝕐 ℤ : Action} →
                       Action-Iso 𝕏 𝕐 → Action-Iso 𝕐 ℤ →
                       Action-Iso 𝕏 ℤ
  compose-Action-Iso {𝕏} {𝕐} {ℤ} (f , i) (g , j) =
                     (f ● g) , (is-equivariant-comp {𝕏} {𝕐} {ℤ} (pr₁ f) i (pr₁ g) j)

  compose-Action-Iso-id : funext 𝓤 𝓤 → 
                          {𝕏 𝕐 : Action} → (u : Action-Iso 𝕏 𝕐) →
                          compose-Action-Iso {𝕏} {𝕐} {𝕐} u (id-Action-Iso 𝕐) ≡ u
  compose-Action-Iso-id fe {𝕏} {𝕐} u = to-subtype-≡
                           (λ f → is-equivariant-is-prop fe {𝕏} {𝕐} (eqtofun f))
                           (≃-refl-right' fe fe fe (pr₁ u))

  compose-id-Action-Iso : funext 𝓤 𝓤 →
                          {𝕏 𝕐 : Action} → (u : Action-Iso 𝕏 𝕐) →
                          compose-Action-Iso {𝕏} {𝕏} {𝕐} (id-Action-Iso 𝕏) u ≡ u
  compose-id-Action-Iso fe {𝕏} {𝕐} u = to-subtype-≡
                           (λ f → is-equivariant-is-prop fe {𝕏} {𝕐} (eqtofun f))
                           (≃-refl-left' fe fe fe (pr₁ u))

\end{code}

When explicitly expressed in terms of a group G, the type Action is
just that of G-Sets, so we also use this notation.

\begin{code}

_Sets : ∀ {𝓤} → Group 𝓤 → 𝓤 ⁺ ̇
G Sets = Action G

\end{code}
