Jon Sterling, started 18th Dec 2022

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module deprecated.Categories.Adjunction (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Subsingletons

open import deprecated.Categories.Category fe
open import deprecated.Categories.Functor fe
open import deprecated.Categories.NaturalTransformation fe

module adjunction-of-precategories (𝓒 : precategory 𝓤 𝓥) (𝓓 : precategory 𝓤' 𝓥') where
 open functor-of-precategories
 open natural-transformation

 private
  [𝓒,𝓒] = functor-category.precat 𝓒 𝓒
  [𝓓,𝓓] = functor-category.precat 𝓓 𝓓
  [𝓒,𝓓] = functor-category.precat 𝓒 𝓓
  [𝓓,𝓒] = functor-category.precat 𝓓 𝓒

  module [𝓒,𝓒] = precategory [𝓒,𝓒]
  module [𝓓,𝓓] = precategory [𝓓,𝓓]
  module [𝓒,𝓓] = precategory [𝓒,𝓓]
  module [𝓓,𝓒] = precategory [𝓓,𝓒]

  1[𝓒] = identity-functor.fun 𝓒
  1[𝓓] = identity-functor.fun 𝓓


 module _ (F : functor 𝓒 𝓓) (G : functor 𝓓 𝓒) where
  private
   module F = functor F
   module G = functor G
   F-G = composite-functor.fun F G
   G-F = composite-functor.fun G F
   [F-G]-F = composite-functor.fun F-G F
   [G-F]-G = composite-functor.fun G-F G
   F-[G-F] = composite-functor.fun F G-F
   G-[F-G] = composite-functor.fun G F-G
   module F-G = functor F-G
   module G-F = functor G-F

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
    η-F : [𝓒,𝓓].hom F [F-G]-F
    η-F = [𝓒,𝓓].seq (left-unitor-inverse F) (right-whiskering.whisk unit F)

    F-ϵ : [𝓒,𝓓].hom [F-G]-F F
    F-ϵ =
     [𝓒,𝓓].seq
      (associator-inverse F G F)
      ([𝓒,𝓓].seq
       (left-whiskering.whisk F counit)
       (left-unitor F))

    G-η : [𝓓,𝓒].hom G G-[F-G]
    G-η = [𝓓,𝓒].seq (left-unitor-inverse G) (left-whiskering.whisk G unit)

    ϵ-G : [𝓓,𝓒].hom G-[F-G] G
    ϵ-G =
     [𝓓,𝓒].seq
      (associator G F G)
      ([𝓓,𝓒].seq
       (right-whiskering.whisk counit G)
       (left-unitor G))

   adjunction-axioms : 𝓥 ⊔ 𝓥' ⊔ 𝓤 ⊔ 𝓤' ̇
   adjunction-axioms =
    ([𝓒,𝓓].seq η-F F-ϵ ＝ [𝓒,𝓓].idn F)
    × ([𝓓,𝓒].seq G-η ϵ-G ＝ [𝓓,𝓒].idn G)

   adjunction-axioms-is-prop : is-prop adjunction-axioms
   adjunction-axioms-is-prop =
    ×-is-prop
     ([𝓒,𝓓].hom-is-set F F)
     ([𝓓,𝓒].hom-is-set G G)

  record adjunction : 𝓥 ⊔ 𝓥' ⊔ 𝓤 ⊔ 𝓤' ̇ where
   constructor make
   field
    str : adjunction-structure
    ax : adjunction-axioms str

   open adjunction-structure str public

\end{code}
