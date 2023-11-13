Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

July 17, 2021
--------------------------------------------------------------------------------

Opposite of a Group. Given a group G, its opposite G ᵒᵖ has the same
underlying type, but the "opposite" group structure:

g ·⟨ G ᵒᵖ ⟩ h = h ·⟨ G ⟩ g

\begin{code}

{-# OPTIONS --safe --without-K #-}


open import MLTT.Spartan
open import Groups.Type renaming (_≅_ to _≣_)


module Groups.Opposite where

_ᵒᵖ : Group 𝓤 → Group 𝓤
G ᵒᵖ = ⟨ G ⟩ , (
               (λ g h → h ·⟨ G ⟩ g) ,
                 (groups-are-sets G) ,
                   ((λ x y z → (assoc G z y x) ⁻¹) ,
                     (unit G) ,
                       ((λ x → unit-right G x) , ((λ x → unit-left G x) ,
                         (λ x → (inv G x) , (inv-right G x) , (inv-left G x))))))

infixr 30 _ᵒᵖ

\end{code}

Forming the opposite gives a functor

\begin{code}

op-functoriality : (G H : Group 𝓤)
                 → (f : ⟨ G ⟩ → ⟨ H ⟩) (i : is-hom G H f)
                 → is-hom (G ᵒᵖ) (H ᵒᵖ) f
op-functoriality G H f i {x} {y} = i {y} {x}

\end{code}

Forming the opposite is idempotent.

\begin{code}

opposite-idempotent : (G : Group 𝓤) → G ≣ (G ᵒᵖ) ᵒᵖ
opposite-idempotent G = id , ((pr₂ (≃-refl ⟨ G ⟩)) , refl)
  where
    open import UF.Equiv

\end{code}

The underlying identity map ⟨ G ⟩ → ⟨ G ᵒᵖ ⟩ is NOT a homomorphism,
unless G is abelian.  In fact this is equivalent to G being abelian.

\begin{code}

underlying-id-is-hom : (G : Group 𝓤) (ab : is-abelian G)
                     → is-hom G (G ᵒᵖ) id
underlying-id-is-hom G ab {x} {y} = ab x y

op-hom-gives-abelian : (G : Group 𝓤)
                     → (i : is-hom G (G ᵒᵖ) id)
                     → is-abelian G
op-hom-gives-abelian G i = λ x y → i {x} {y}

\end{code}
