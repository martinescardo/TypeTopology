Jon Sterling, started 18th Dec 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt

-- TODO: these funext assumptions are getting out of hand;
-- perhaps we should reconsider how these are done?
module Categories.Adjunction
 (fe1 : funext 𝓥 𝓥)
 (fe3 : funext 𝓥' 𝓥')
 (fe4 : funext 𝓤 (𝓤 ⊔ 𝓥 ⊔ 𝓥'))
 (fe5 : funext 𝓥 𝓥')
 (fe6 : funext 𝓤' (𝓥 ⊔ 𝓤' ⊔ 𝓥'))
 (fe7 : funext 𝓥' 𝓥)
 where

open import UF.Base
open import UF.Equiv
open import UF.Lower-FunExt
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Equiv-FunExt

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation


private
 fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)
 fe0 = lower-funext 𝓤 𝓥' fe4

 fe2 : funext 𝓤' (𝓤' ⊔ 𝓥')
 fe2 = lower-funext 𝓤' 𝓥 fe6


module adjunction-of-precategories (𝓒 : precategory 𝓤 𝓥) (𝓓 : precategory 𝓤' 𝓥') where
 open functor-of-precategories

 private
  [𝓒,𝓒] = natural-transformation.functor-category.precat 𝓒 𝓒 fe0 fe1
  [𝓓,𝓓] = natural-transformation.functor-category.precat 𝓓 𝓓 fe2 fe3
  [𝓒,𝓓] = natural-transformation.functor-category.precat 𝓒 𝓓 fe4 fe5
  [𝓓,𝓒] = natural-transformation.functor-category.precat 𝓓 𝓒 fe6 fe7

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
  adjunction-structure = [𝓒,𝓒].hom 1[𝓒] F-G ×  [𝓓,𝓓].hom G-F 1[𝓓]

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
