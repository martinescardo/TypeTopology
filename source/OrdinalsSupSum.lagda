Martin Escardo, 2-4 May 2022

Roughly, we show that, for any family β of ordinals indexed by ordinals,

    EM → sup β ⊴ ∑ β → WEM

where EM is the principle of excluded middle and WEM is the weak
principle of excluded middle (excluded middle for negated
propositions).

The problem is that the sum doesn't always exist constructively. So we
need a more precise formulation of the above, which we give below.

We assume univalence in this module, which is needed for the
development of the large ordinal of small ordinals, and, in
particular, the ordering _⊴_ between ordinals and its properties.

Other local assumptions belonging to HoTT/UF are discussed below.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-Univalence

module OrdinalsSupSum
        (ua : Univalence)
       where

open import SpartanMLTT
open import OrdinalsType
open import OrdinalOfOrdinals ua
open import OrdinalOfOrdinalsSuprema ua

open import UF-FunExt
open import UF-UA-FunExt
open import UF-ExcludedMiddle
open import UF-Size
open import UF-PropTrunc
open import UF-Subsingletons

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

open import OrdinalArithmetic fe

\end{code}

Our construction of suprema of families of ordinals needs the
assumption of set quotients, or, equivalently, propositional
truncations and set replacement. But because the existence of
propositional truncations follows from excluded middle, which we
assume for our next theorem, we only need to assume set replacement to
formulate the next theorem, in addition to excluded middle.

Also, sums of ordinal-indexed families of ordinals don't always exist
(see the module OrdinalsShulmanTaboo). They do exist, for example, for
ordinals with a largest element (which, constructively, are not
necessarily limit ordinals), or for all ordinals if we assume the
principle of excluded middle.

\begin{code}

module _ {𝓤 : Universe}
         (em : Excluded-Middle)
         (sr : Set-Replacement (fe-and-em-give-propositional-truncations fe em))
       where

 open sums-assuming-EM (em {𝓤})
 open suprema (fe-and-em-give-propositional-truncations fe em) sr

 sup-bounded-by-sum : (α : Ordinal 𝓤) (β : ⟨ α ⟩ → Ordinal 𝓤)
                    → sup β ⊴ ∑ α β
 sup-bounded-by-sum α β = sup-is-lower-bound-of-upper-bounds β (∑ α β) bound
  where
   bound : (x : ⟨ α ⟩) → β x ⊴ ∑ α β
   bound x = ≼-gives-⊴ (β x) (∑ α β) m
    where
     f : ⟨ β x ⟩ → ⟨ ∑ α β ⟩
     f y = x , y

     fop : is-order-preserving (β x) (∑ α β) f
     fop y z l = inr (refl , l)

     m : β x ≼ ∑ α β
     m = order-preserving-gives-≼ em (β x) (∑ α β) (f , fop)

\end{code}

We also formulate the following immediate consequence for use in
another module, where Ordinalᵀ 𝓤 is the type of topped ordinals in the
universe 𝓤, that is, the ordinals that have a largest element.

\begin{code}

 open import OrdinalsToppedType fe
 open import OrdinalToppedArithmetic fe renaming (∑ to ∑ᵀ)

 sup-bounded-by-sumᵀ : (τ : Ordinalᵀ 𝓤) (υ : ⟪ τ ⟫ → Ordinalᵀ 𝓤)
                     → sup (λ x → [ υ x ]) ⊴ [ ∑ᵀ τ υ ]
 sup-bounded-by-sumᵀ τ υ = sup-bounded-by-sum [ τ ] (λ x → [ υ x ])

\end{code}

This is the end of the anonymous module that assumes the principle of
excluded middle.

We now prove a weak converse of this consequence, namely that weak
excluded middle follows from the assumption that sups are bounded by
sums of topped-ordinals indexed by topped-ordinals. In order to
formulate this, we need to speak of suprema, which are available if we
assume propositional truncations and set replacement (or, equivalently
set quotients).

\begin{code}

module _ {𝓤 : Universe}
         (pt : propositional-truncations-exist)
         (sr : Set-Replacement pt)
       where

 open import OrdinalsToppedType fe
 open import OrdinalToppedArithmetic fe
 open suprema pt sr

 sup-bounded-by-sum-gives-WEM : ({𝓤 : Universe} (τ : Ordinalᵀ 𝓤) (υ : ⟪ τ ⟫ → Ordinalᵀ 𝓤)
                                    → sup (λ x → [ υ x ]) ⊴ [ ∑ τ υ ])

                              → {𝓤 : Universe} → WEM 𝓤
 sup-bounded-by-sum-gives-WEM ϕ {𝓤} = γ
  where
   open import OrdinalOfTruthValues fe 𝓤 (pe 𝓤)
   open Omega (pe 𝓤)
   open import OrdinalArithmetic-Properties ua

   τ = 𝟚ᵒ

   υ : ⟪ 𝟚ᵒ ⟫ →  Ordinalᵀ (𝓤 ⁺)
   υ = cases (λ ⋆ → 𝟙ᵒ) (λ ⋆ → Ωᵒ)

   l : sup (λ x → [ υ x ]) ⊴ [ ∑ τ υ ]
   l = ϕ τ υ

   m : Ωₒ ⊴ sup (λ x → [ υ x ])
   m = sup-is-upper-bound (λ x → [ υ x ]) (inr ⋆)

   o : Ωₒ ⊴ [ ∑ τ υ ]
   o = ⊴-trans Ωₒ (sup (λ x → [ υ x ])) [ ∑ τ υ ] m l

   p : [ ∑ τ υ ] ≡ (𝟙ₒ +ₒ Ωₒ)
   p = alternative-plus 𝟙ᵒ Ωᵒ

   q : Ωₒ ⊴ (𝟙ₒ +ₒ Ωₒ)
   q = transport (Ωₒ ⊴_) p o

   γ : WEM 𝓤
   γ = ⊴-add-taboo q

\end{code}
