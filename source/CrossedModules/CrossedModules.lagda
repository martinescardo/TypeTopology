--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

Jul 17, 2021

Revision July 1, 2022
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding ( ₀ ; ₁)
open import UF.PropTrunc
open import UF.ImageAndSurjection
open import UF.FunExt
open import UF.Subsingletons

open import Groups.Type
open import Groups.Homomorphisms
open import Groups.Kernel
open import Groups.Image
open import Groups.Cokernel

open import Quotient.Type

module CrossedModules.CrossedModules
        (sq : set-quotients-exist)
       where

\end{code}

Group Action:

   A group G acts on a group H by automorphisms.

   If there is a homomorphism δ : H → G, this action is compatible
   with the one induced by the inner conjugation on G and H.


\begin{code}

_◂_ : (G : Group 𝓤) (H : Group 𝓥) → 𝓤 ⊔ 𝓥 ̇
G ◂ H = Σ ρ ꞉ (⟨ G ⟩ → ⟨ H ⟩ → ⟨ H ⟩)
      , (∀ {x y : ⟨ G ⟩} {h : ⟨ H ⟩} → (ρ x (ρ y h) ＝ ρ (x ·⟨ G ⟩ y) h)
      × ∀ {x} → (ρ (unit G) x ＝ x)
      × ∀ {g : ⟨ G ⟩} {h h' : ⟨ H ⟩} → ρ g (h ·⟨ H ⟩ h') ＝ (ρ g h) ·⟨ H ⟩ (ρ g h'))

Equivariant : (G : Group 𝓤) (H : Group 𝓥) → G ◂ H → (δ : ⟨ H ⟩ → ⟨ G ⟩) → (is-hom H G δ) → 𝓤 ⊔ 𝓥 ̇
Equivariant G H (ρ , _) δ _ = ∀ {g h} → (δ (ρ g h) ·⟨ G ⟩ g ＝ (g ·⟨ G ⟩ (δ h)))

Peiffer-identity : (G : Group 𝓤) (H : Group 𝓥) → G ◂ H → (δ : ⟨ H ⟩ → ⟨ G ⟩) → (is-hom H G δ) → 𝓥 ̇
Peiffer-identity _ H (ρ , _) δ _ = ∀ {h₁ h₂} → (((ρ (δ h₁) h₂) ·⟨ H ⟩ h₁) ＝ h₁ ·⟨ H ⟩ h₂)

Equivariant' : (G : Group 𝓤) (H : Group 𝓥) → G ◂ H → (δ : ⟨ H ⟩ → ⟨ G ⟩) → (is-hom H G δ) → 𝓤 ⊔ 𝓥 ̇
Equivariant' G H (ρ , _) δ _ = (g : ⟨ G ⟩) (h : ⟨ H ⟩)  → (δ (ρ g h) ＝ (g ·⟨ G ⟩ (δ h)) ·⟨ G ⟩ (inv G g))

action-carrier : {G : Group 𝓤}{H : Group 𝓥} → G ◂ H → ⟨ G ⟩ → ⟨ H ⟩ → ⟨ H ⟩
action-carrier ρ g h = (pr₁ ρ) g h
syntax action-carrier ρ g h = g ◂⟨ ρ ⟩ h

\end{code}

We collect the axioms of a crossed module in a record to have named
component for the various parts. In particular, _₀ and _₁ allow to
write the group components of G : CrossedModule {𝓤} {𝓥} as G ₀ and G ₁

\begin{code}

record CrossedModule : (𝓤 ⊔ 𝓥) ⁺ ̇ where
  field
    _₁ : Group 𝓤
    _₀ : Group 𝓥
    ∂ : ⟨ _₁ ⟩ → ⟨ _₀ ⟩
    is-∂ : is-hom _₁ _₀ ∂
    ρ : _₀ ◂ _₁
    equivariant : Equivariant' _₀ _₁ ρ ∂ is-∂
    peiffer : Peiffer-identity _₀ _₁ ρ ∂ is-∂




module _ {G : CrossedModule {𝓤} {𝓥}}
         {H : CrossedModule {𝓦} {𝓣}} where

\end{code}

We also use a record for the notion of morphism between two crossed
modules.  Note that we need to help Agda figure out some of the
fields, hence the explicit naming, despite the fact we 'open'
CrossedModule.

\begin{code}
  open CrossedModule
  record CrossedModuleHom : (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ⁺ ̇ where
    field
      _₀ : ⟨ G ₀ ⟩ → ⟨ H ₀ ⟩
      is_₀ : is-hom (CrossedModule._₀ G) (CrossedModule._₀ H) _₀
      _₁ : ⟨ G ₁ ⟩ → ⟨ H ₁ ⟩
      is_₁ : is-hom (CrossedModule._₁ G) (CrossedModule._₁ H) _₁
      comm-diag : ∀ {g} → _₀ (∂ G g) ＝ ∂ H (_₁ g)
      action-equivariant : ∀ {g h} → (_₁ ((pr₁ (ρ G)) g h) ＝ (pr₁ (ρ H)) (_₀ g) (_₁ h))

-- It is convenient (?) to have a different definition for the
-- morphisms

  is-CrossMod-hom : (f₀ : ⟨ G ₀ ⟩ → ⟨ H ₀ ⟩) → is-hom ( G ₀) (H ₀) f₀ → (f₁ : ⟨ G ₁ ⟩ → ⟨ H ₁ ⟩) → is-hom (G ₁) (H ₁) f₁ → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ̇
  is-CrossMod-hom f₀ _ f₁ _ = ( ∀ {g} → f₀ (∂ G g) ＝ ∂ H (f₁ g) )
                            × ( ∀ {g h} → f₁ ((pr₁ (ρ G)) g h) ＝ (pr₁ (ρ H)) (f₀ g) (f₁ h) )




\end{code}

Since crossed modules form a 2-category, there is a notion of
homotopy (left-homotopy, with the conventions below) between two
morphisms.

This is a map (not necessarily a homomorphism)
θ : ⟨ G ₀ ⟩ → ⟨ H ₁ ⟩ satisfying the condition

    θ x x' = θ x · ((f₀ x) ◂ (θ x'))

\begin{code}

  is-left-homotopy : (f : CrossedModuleHom) → (⟨ G ₀ ⟩ → ⟨ H ₁ ⟩) → _
  is-left-homotopy f θ = ∀ {x x'} → θ (x ·⟨ G ₀ ⟩ x') ＝ (θ x) ·⟨ H ₁ ⟩ (pr₁ (ρ H) (f₀ x)  (θ x'))
    where
      open CrossedModuleHom
      f₀ = f ₀

  -- Alternative definition
  is-left-homotopy' : (f₀ : ⟨ G ₀ ⟩ → ⟨ H ₀ ⟩) → (i₀ : is-hom (G ₀) (H ₀) f₀) →
                      (f₁ : ⟨ G ₁ ⟩ → ⟨ H ₁ ⟩) → (i₁ : is-hom (G ₁) (H ₁) f₁) →
                      is-CrossMod-hom f₀ i₀ f₁ i₁ →
                      (⟨ G ₀ ⟩ → ⟨ H ₁ ⟩) → _
  is-left-homotopy' f₀ _ f₁ _ _ θ = ∀ {x x'} → θ (x ·⟨ G ₀ ⟩ x') ＝ (θ x) ·⟨ H ₁ ⟩ (pr₁ (ρ H) (f₀ x)  (θ x'))

\end{code}

There is an alternative characterization of left homotopy, where we
give two crossed module homomorphisms and the map θ : ⟨ G ₀ ⟩ → ⟨ H ₁ ⟩ appears
as the formal analogue of a chain homotopy.

\begin{code}

  is-chain-homotopy : (f g : CrossedModuleHom) → (⟨ G ₀ ⟩ → ⟨ H ₁ ⟩) → _
  is-chain-homotopy f g θ = (∀ {x} → g₀ x ＝ ((∂ H) (θ x)) ·⟨ H ₀ ⟩ (f₀ x))
                          × (∀ {a x} → g₁ a ·⟨ H ₁ ⟩ θ x ＝ θ (∂ G a ·⟨ G ₀ ⟩ x) ·⟨ H ₁ ⟩ f₁ a)
                          × (∀ {x x'} → θ (x ·⟨ G ₀ ⟩ x') ＝ (θ x) ·⟨ H ₁ ⟩ (pr₁ (ρ H) (f₀ x)  (θ x')))
                          where
                            open CrossedModuleHom
                            f₀ = f ₀
                            f₁ = f ₁
                            g₀ = g ₀
                            g₁ = g ₁

  is-chain-homotopy' : (f₀ : ⟨ G ₀ ⟩ → ⟨ H ₀ ⟩) → (i₀ : is-hom (G ₀) (H ₀) f₀) →
                       (f₁ : ⟨ G ₁ ⟩ → ⟨ H ₁ ⟩) → (i₁ : is-hom (G ₁) (H ₁) f₁) →
                       is-CrossMod-hom f₀ i₀ f₁ i₁ →
                       (g₀ : ⟨ G ₀ ⟩ → ⟨ H ₀ ⟩) → (j₀ : is-hom (G ₀) (H ₀) g₀) →
                       (g₁ : ⟨ G ₁ ⟩ → ⟨ H ₁ ⟩) → (j₁ : is-hom (G ₁) (H ₁) g₁) →
                       is-CrossMod-hom g₀ j₀ g₁ j₁ →
                       (⟨ G ₀ ⟩ → ⟨ H ₁ ⟩) → _
  is-chain-homotopy' f₀ _ f₁ _ _ g₀ _ g₁ _ _ θ
                     = (∀ {x} → g₀ x ＝ ((∂ H) (θ x)) ·⟨ H ₀ ⟩ (f₀ x))
                     × (∀ {a x} → g₁ a ·⟨ H ₁ ⟩ θ x ＝ θ (∂ G a ·⟨ G ₀ ⟩ x) ·⟨ H ₁ ⟩ f₁ a)
                     × (∀ {x x'} → θ (x ·⟨ G ₀ ⟩ x') ＝ (θ x) ·⟨ H ₁ ⟩ (pr₁ (ρ H) (f₀ x)  (θ x')))



module homotopygroups {G : CrossedModule {𝓤} {𝓥}} (pt : propositional-truncations-exist) (fe : Fun-Ext) (pe : Prop-Ext)
  where
  open CrossedModule
  open Groups.Homomorphisms (G ₁) (G ₀) (∂ G) (is-∂ G)
  open PropositionalTruncation pt
  open Groups.Cokernel.cokernel pt fe pe


  γ : (G : Group 𝓥) → (x y g : ⟨ G ⟩) → (x ＝ y) → (((g ·⟨ G ⟩ x) ·⟨ G ⟩ (inv G g)) ＝ ((g ·⟨ G ⟩ y) ·⟨ G ⟩ (inv G g)))
  γ G x y g p = ap (λ v → ((g ·⟨ G ⟩ v) ·⟨ G ⟩ (inv G g))) p


  ∂-has-norm-im : Groups.Homomorphisms.has-normal-image (G ₁) (G ₀) (∂ G) (is-∂ G) pt
  ∂-has-norm-im g (g' , p) = do
    x , p' ← p
    ∣ (pr₁ (ρ G)) g x , ((equivariant G g x) ∙ (γ (G ₀) (∂ G x) g' g p')) ∣


  π₁ : Group (𝓤 ⊔ 𝓥)
  π₁ = kernel (G ₁) (G ₀) (∂ G) (is-∂ G)


  π₀ : Group _
  π₀ = cokernel-gr sq ((G ₁)) (G ₀) (∂ G) (is-∂ G) ∂-has-norm-im

\end{code}
