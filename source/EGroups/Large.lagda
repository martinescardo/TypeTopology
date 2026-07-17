Martin Escardo, July 2026.

This is the egroup counterpart of Groups.Large. For a large, locally
small type A of generators, the free egroup on A is large: no egroup
with a small carrier is isomorphic to it. This is developed in an
Spartan MLTT.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EGroups.Large where

open import MLTT.Spartan
open import UF.Equiv hiding (_≅_)
open import UF.EquivalenceExamples
open import UF.Size
open import UF.SmallnessProperties

open import Groups.Free using (module free-group-construction ;
                               module free-group-construction-reduction)
open import EGroups.Type
open import EGroups.FreeOnType

\end{code}

We use the generator machinery of free-group-construction-reduction,
whose local-smallness data _＝₀_, refl₀ and from-＝₀ come from the
local smalless of A.

\begin{code}

module _ {𝓤 : Universe}
         (A : 𝓤 ⁺ ̇ )
       where

 open free-group-construction A

 module _ (ls : is-locally-small A) where

  private
   _＝₀_ : A → A → 𝓤 ̇
   a ＝₀ b = resized (a ＝ b) (ls a b)

   refl₀ : (a : A) → a ＝₀ a
   refl₀ a = ⌜ resizing-condition (ls a a) ⌝⁻¹ refl

   from-＝₀ : (a b : A) → a ＝₀ b → a ＝ b
   from-＝₀ a b = ⌜ resizing-condition (ls a b) ⌝

  open free-group-construction-reduction A _＝₀_ refl₀ from-＝₀

  small-copy-gives-small-type-of-generators
   : (𝓖 : EGroup 𝓤 𝓤)
   → 𝓖 ≅ free-egroup A
   → A is 𝓤 small
  small-copy-gives-small-type-of-generators 𝓖 (f , _ , g , _ , fg , _)
   = A-is-small
   where
    κ : A → ⟨ 𝓖 ⟩
    κ a = g (η a)

    module _ (y : ⟨ 𝓖 ⟩) where

     e : (a : A) → κ a ＝ y → η a ∿ f y
     e a p = transport
              (λ - → η a ∿ -)
              (ap f p)
              (srt-symmetric _▷_ (f (g (η a))) (η a) (fg (η a)))

     Φ : fiber κ y → generator (f y)
     Φ (a , p) = ∿→generator (e a p)

     ug : generator (f y) → A
     ug = underlying-generator

     H : ug ∘ Φ ∼ pr₁
     H (a , p) = underlying-generator-∿→generator (e a p)

     Φ-is-small-map : (γ : generator (f y)) → fiber Φ γ is 𝓤 small
     Φ-is-small-map γ = ≃-size-contravariance
                         (≃-sym (pr₁-fiber-equiv (γ , refl)))
                         (maps-between-small-types-are-small-maps
                           pr₁ total-is-small fiber-ug-is-small (γ , refl))
      where
       a₀ : A
       a₀ = ug γ

       fiber-ug-is-small : fiber ug a₀ is 𝓤 small
       fiber-ug-is-small = Σ-is-small
                            (generator-is-small (f y))
                            (λ γ' → ls (ug γ') a₀)

       total-is-small : (Σ (w , _) ꞉ fiber ug a₀ , fiber Φ w) is 𝓤 small
       total-is-small = ≃-size-contravariance e₁ (native-size (κ a₀ ＝ y))
        where
         e₁ : (Σ (w , _) ꞉ fiber ug a₀ , fiber Φ w) ≃ (κ a₀ ＝ y)
         e₁ = (Σ (w , _) ꞉ fiber ug a₀ , fiber Φ w) ≃⟨ I ⟩
              fiber (ug ∘ Φ) a₀                     ≃⟨ II ⟩
              fiber pr₁ a₀                          ≃⟨ III ⟩
              (κ a₀ ＝ y)                           ■
          where
           I   = ≃-sym (fiber-of-composite Φ ug a₀)
           II  = ∼-fiber-≃ H a₀
           III = pr₁-fiber-equiv a₀

     κ-fiber-is-small : fiber κ y is 𝓤 small
     κ-fiber-is-small = size-contravariance Φ Φ-is-small-map
                         (generator-is-small (f y))

    κ-is-small-map : κ is 𝓤 small-map
    κ-is-small-map = κ-fiber-is-small

    A-is-small : A is 𝓤 small
    A-is-small = size-contravariance κ κ-is-small-map (native-size ⟨ 𝓖 ⟩)

  no-small-copy : is-large A
                → (𝓖 : EGroup 𝓤 𝓤) → ¬ (𝓖 ≅ free-egroup A)
  no-small-copy A-is-large 𝓖 iso =
   A-is-large (small-copy-gives-small-type-of-generators 𝓖 iso)

  large-egroup-with-no-small-copy
   : is-large A
   → Σ 𝓕 ꞉ EGroup (𝓤 ⁺) (𝓤 ⁺) , ((𝓖 : EGroup 𝓤 𝓤) → ¬ (𝓖 ≅ 𝓕))
  large-egroup-with-no-small-copy A-is-large
   = free-egroup A , no-small-copy A-is-large

\end{code}

We are not done yet. The objective is to show that there are more
egroups in the next universe in a Spartan MLTT. Large types can be
constructed in a Spartan MLTT, as shown in Various.LawvereFPT in the
module generalized-Coquand, where the universe 𝓤 ̇ is shown to be
large. What is missing in a Spartan MLTT is local smallness: the
universe is locally small under univalence, but I don't see how to
make it locally small in a Spartan MLTT, or how to find any other
large, locally small type in a Spartan MLTT.

The best we can currently do in a Spartan MLTT without HoTT/UF
assumptions is the following conditional statement: if there is a
large, locally small type, then there is an egroup in the next universe
with no small copy.

\begin{code}

there-is-a-large-egroup-if-there-is-a-large-type
 : {𝓤 : Universe}
 → (Σ A ꞉ 𝓤 ⁺ ̇ , is-locally-small A × is-large A)
 → Σ 𝓕 ꞉ EGroup (𝓤 ⁺) (𝓤 ⁺) , ((𝓖 : EGroup 𝓤 𝓤) → ¬ (𝓖 ≅ 𝓕))
there-is-a-large-egroup-if-there-is-a-large-type (A , ls , A-is-large)
 = large-egroup-with-no-small-copy A ls A-is-large

\end{code}
