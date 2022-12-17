Jon Sterling, started 16th Dec 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Categories.NaturalTransformation where

open import MLTT.Spartan
open import UF.FunExt
open import UF.Base
open import UF.Equiv
open import UF.Lower-FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Equiv-FunExt

open import Categories.Category
open import Categories.Functor

module _ {𝓒 : precategory 𝓤 𝓥} {𝓓 : precategory 𝓤' 𝓥'} where
 module 𝓒 = precategory 𝓒
 module 𝓓 = precategory 𝓓
 open functor-of-precategories 𝓒 𝓓

 module _ (F G : functor) where
  module F = functor F
  module G = functor G

  transformation : 𝓤 ⊔ 𝓥' ̇
  transformation = (A : 𝓒.ob) → 𝓓.hom (F.ob A) (G.ob A)

  module _ (α : transformation) where
   is-natural : 𝓤 ⊔ 𝓥 ⊔ 𝓥' ̇
   is-natural =
    (A B : 𝓒.ob) (f : 𝓒.hom A B)
    → 𝓓.seq (F.hom f) (α B) ＝ 𝓓.seq (α A) (G.hom f)

   module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥 ⊔ 𝓥')) (fe1 : funext 𝓥 𝓥')  where
    private
     fe2 : funext 𝓤 (𝓥 ⊔ 𝓥')
     fe2 = lower-funext 𝓤 𝓤 fe0

    being-natural-is-prop : is-prop is-natural
    being-natural-is-prop =
     Π-is-prop fe0 λ _ →
     Π-is-prop fe2 λ _ →
     Π-is-prop fe1 λ _ →
     𝓓.hom-is-set _ _

  natural-transformation : 𝓤 ⊔ 𝓥 ⊔ 𝓥' ̇
  natural-transformation = Σ α ꞉ transformation , is-natural α

\end{code}
