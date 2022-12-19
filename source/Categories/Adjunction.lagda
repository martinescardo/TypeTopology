Jon Sterling, started 18th Dec 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF.FunExt

module Categories.Adjunction (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Equiv-FunExt

open import Categories.Category fe
open import Categories.Functor fe
open import Categories.NaturalTransformation fe

module adjunction-of-precategories (𝓒 : precategory 𝓤 𝓥) (𝓓 : precategory 𝓤' 𝓥') where
 open functor-of-precategories

 private
  [𝓒,𝓒] = natural-transformation.functor-category.precat 𝓒 𝓒
  [𝓓,𝓓] = natural-transformation.functor-category.precat 𝓓 𝓓
  [𝓒,𝓓] = natural-transformation.functor-category.precat 𝓒 𝓓
  [𝓓,𝓒] = natural-transformation.functor-category.precat 𝓓 𝓒

  module [𝓒,𝓒] = precategory [𝓒,𝓒]
  module [𝓓,𝓓] = precategory [𝓓,𝓓]
  module [𝓒,𝓓] = precategory [𝓒,𝓓]
  module [𝓓,𝓒] = precategory [𝓓,𝓒]

  1[𝓒] = identity-functor.fun 𝓒
  1[𝓓] = identity-functor.fun 𝓓

 module _ (F : functor 𝓒 𝓓) (G : functor 𝓓 𝓒) where
  private
   module F = functor 𝓒 𝓓 F
   module G = functor 𝓓 𝓒 G
   F-G = composite-functor.fun 𝓒 𝓓 𝓒 F G
   G-F = composite-functor.fun 𝓓 𝓒 𝓓 G F
   [F-G]-F = composite-functor.fun 𝓒 𝓒 𝓓 F-G F
   [G-F]-G = composite-functor.fun 𝓓 𝓓 𝓒 G-F G
   module F-G = functor 𝓒 𝓒 F-G
   module G-F = functor 𝓓 𝓓 G-F

  adjunction-structure : 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
  adjunction-structure = [𝓒,𝓒].hom 1[𝓒] F-G × [𝓓,𝓓].hom G-F 1[𝓓]

  module adjunction-structure (str : adjunction-structure) where
   unit : [𝓒,𝓒].hom 1[𝓒] F-G
   unit = pr₁ str

   counit : [𝓓,𝓓].hom G-F 1[𝓓]
   counit = pr₂ str

  module _ (str : adjunction-structure) where
   open adjunction-structure str

   private
    F·η = right-whiskering.whisk 𝓒 𝓒 𝓓 1[𝓒] F-G F unit
    ϵ·F = left-whiskering.whisk 𝓒 𝓓 𝓓 F G-F 1[𝓓] counit
    η·G = left-whiskering.whisk 𝓓 𝓒 𝓒 G 1[𝓒] F-G unit
    G·ϵ = right-whiskering.whisk 𝓓 𝓓 𝓒 G-F 1[𝓓] G counit

   adjunction-axioms : 𝓥 ⊔ 𝓥' ⊔ 𝓤 ⊔ 𝓤' ̇
   adjunction-axioms =
    ([𝓒,𝓓].seq {F} {[F-G]-F} {F} F·η ϵ·F ＝ [𝓒,𝓓].idn F)
    × ([𝓓,𝓒].seq {G} {[G-F]-G} {G} η·G G·ϵ ＝ [𝓓,𝓒].idn G)

   adjunction-axioms-is-prop : is-prop adjunction-axioms
   adjunction-axioms-is-prop =
    ×-is-prop
     ([𝓒,𝓓].hom-is-set F F)
     ([𝓓,𝓒].hom-is-set G G)

  adjunction : 𝓥 ⊔ 𝓥' ⊔ 𝓤 ⊔ 𝓤' ̇
  adjunction = Σ str ꞉ adjunction-structure , adjunction-axioms str

\end{code}
