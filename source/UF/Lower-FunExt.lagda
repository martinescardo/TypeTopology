Martin Escardo, 13th January 2021.

Interface to code from my MGS 2019 lecture notes.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Lower-FunExt where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.FunExt

open import MGS.TypeTopology-Interface

import MGS.Equivalences
import MGS.FunExt-from-Univalence
import MGS.Universe-Lifting

abstract

  lower-DN-funext : ∀ 𝓦 𝓣 → DN-funext (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣) → DN-funext 𝓤 𝓥
  lower-DN-funext {𝓤} {𝓥} 𝓦 𝓣 fe = MGS.Universe-Lifting.lower-dfunext 𝓦 𝓣 𝓤 𝓥 fe

  DN-funext-gives-funext : {𝓤 𝓥 : Universe} → DN-funext 𝓤 𝓥 → funext 𝓤 𝓥
  DN-funext-gives-funext dnfe {X} {A} f g = γ
   where
    h : f ＝ g → f ∼ g
    h = MGS.FunExt-from-Univalence.happly f g

    a : is-equiv h
    a = MGS-equivs-are-equivs h (MGS.FunExt-from-Univalence.dfunext-gives-hfunext dnfe f g)

    b : is-equiv (happly' f g)
    b = equiv-closed-under-∼ h (happly' f g) a (happly'-is-MGS-happly f g)

    c :  MGS.Equivalences.is-equiv (happly' f g)
    c = equivs-are-MGS-equivs (happly' f g) b

    γ : is-equiv (happly' f g)
    γ = MGS-equivs-are-equivs (happly' f g) c

  lower-funext : ∀ 𝓦 𝓣 → funext (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣) → funext 𝓤 𝓥
  lower-funext {𝓤} {𝓥} 𝓦 𝓣 fe = DN-funext-gives-funext
                                   (lower-DN-funext 𝓦 𝓣 (dfunext fe))

  lower-fun-ext : ∀ {𝓦} 𝓣 → funext (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣) → funext 𝓤 𝓥
  lower-fun-ext {𝓤} {𝓥} {𝓦} 𝓣 fe = DN-funext-gives-funext
                                      (lower-DN-funext 𝓦 𝓣 (dfunext fe))

\end{code}
