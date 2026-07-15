Martin Escardo, July 2026.

Every group is an egroup.

An ordinary group (Groups.Type) is a set with a group operation whose
laws hold up to the identity type _＝_. It is in particular an egroup:
take the underlying setoid to be the carrier with its identity type as
the equivalence relation (which is an equivalence relation, given by
refl, _⁻¹ and _∙_), and the operation is a congruence for _＝_ via ap₂.

Note that we do not use that the carrier is a set: the identity type
is an equivalence relation in the sense of EGroups.Setoid, whether or
not it is proposition-valued, and egroups do not require the
equivalence relation to be proposition-valued.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EGroups.FromGroup where

open import MLTT.Spartan
open import UF.Base using (ap₂)
open import Groups.Type
             using (Group ; multiplication ; unit ;
                    unit-left ; unit-right ; assoc ;
                    inv ; inv-left ; inv-right)
             renaming (⟨_⟩ to ⟪_⟫)

open import EGroups.Setoid
open import EGroups.Type

Group-to-EGroup : Group 𝓤 → EGroup 𝓤 𝓤
Group-to-EGroup G =
   (⟪ G ⟫ , _＝_ , ((λ x → refl) , (λ x y p → p ⁻¹) , (λ x y z p q → p ∙ q)))
 , multiplication G
 , ( (λ p q → ap₂ (multiplication G) p q)
   , assoc G
   , ( unit G
     , unit-left G
     , unit-right G
     , (λ x → inv G x , inv-left G x , inv-right G x) ) )

\end{code}
