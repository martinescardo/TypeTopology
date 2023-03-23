Jonathan Sterling, 22nd March 2023.

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Coslice.Hom where

open import MLTT.Spartan
open import UF.Base
open import UF.Retracts
open import UF.Equiv
open import UF.Embeddings
open import UF.FunExt
open import UF.IdentitySystems
open import UF.PairFun as PairFun
open import UF.Subsingletons
open import UF.EquivalenceExamples
open import Coslice.Type

module _ {A : 𝓤 ̇ } where
 hom-str-type : coslice A → coslice A → 𝓤 ̇
 hom-str-type X Y = target X → target Y

 hom-coh-type : (X Y : coslice A) → hom-str-type X Y → 𝓤 ̇
 hom-coh-type X Y f = alg Y ∼ f ∘ alg X

 hom : coslice A → coslice A → 𝓤 ̇
 hom X Y = Σ f ꞉ hom-str-type X Y , hom-coh-type X Y f

 hom-fun : {X Y : coslice A} → hom X Y → hom-str-type X Y
 hom-fun (f , α[f]) = f

 hom-alg : {X Y : coslice A} (f : hom X Y) → hom-coh-type X Y (hom-fun f)
 hom-alg (f , α[f]) = α[f]

 module _ {X Y : coslice A} (f g : hom X Y) where
  htpy-str-type : 𝓤 ̇
  htpy-str-type = hom-fun f ∼ hom-fun g

  htpy-coh-type : htpy-str-type → 𝓤 ̇
  htpy-coh-type ϕ = Π a ꞉ A , hom-alg g a ＝ hom-alg f a ∙ ϕ (alg X a)

  hom-≈ : 𝓤 ̇
  hom-≈ = Σ htpy-coh-type

 module _ (fe : FunExt) (X Y : coslice A) (f : hom X Y) where
  open id-sys
  open has-id-sys
  open dep-id-sys
  private [f] = homotopy-id-sys (fe 𝓤 𝓤) (hom-fun f)
  private module [f] = id-sys [f]

  private
   Aux =
    Σ ϕ ꞉ hom-coh-type X Y (hom-fun f) ,
    htpy-coh-type f (hom-fun f , ϕ) (λ _ → refl)

   Aux-singleton-type : singleton-type' (dfunext (fe 𝓤 𝓤) (hom-alg f)) ≃ Aux
   Aux-singleton-type =
    pair-fun-equiv (happly , fe 𝓤 𝓤 _ _) λ h →
    (ap happly ,
     embedding-gives-embedding' _ (equivs-are-embeddings _ (fe 𝓤 𝓤 _ _)) _ _)
    ● (_∙ happly-funext (fe 𝓤 𝓤) _ _ (hom-alg f)) ,
        ∙-is-equiv-right (happly-funext (fe 𝓤 𝓤) _ _ (hom-alg f))
    ● happly-≃ (fe 𝓤 𝓤)

   abstract
    Aux-retract-singleton : Aux ◁ singleton-type' (dfunext (fe 𝓤 𝓤) (hom-alg f))
    Aux-retract-singleton = ≃-gives-◁ (≃-sym Aux-singleton-type)

    Aux-is-prop : is-prop Aux
    Aux-is-prop =
     retract-of-prop
      Aux-retract-singleton
      (singletons-are-props
       (singleton-types'-are-singletons _))

  hom-coh-id-sys : dep-id-sys (hom-str-type X Y) (hom-coh-type X Y) [f] (hom-alg f)
  fam hom-coh-id-sys g ϕ α[g] = htpy-coh-type f (g , α[g]) ϕ
  ctr (sys hom-coh-id-sys) a = refl
  ind (sys hom-coh-id-sys) P p α[f] H =
   transport (uncurry P) (Aux-is-prop _ _) p
  ind-β (sys hom-coh-id-sys) P p =
   ap (λ - → transport (uncurry P) - p) lem
   where
    lem : Aux-is-prop (hom-alg f , λ _ → refl) (hom-alg f , λ _ → refl) ＝ refl
    lem = props-are-sets Aux-is-prop _ _

  hom-id-sys : id-sys (hom X Y) f
  hom-id-sys = pair-id-sys [f] hom-coh-id-sys

 module _ (fe : FunExt) (X Y : coslice A) (f g : hom X Y) where
  private
   [f] = hom-id-sys fe X Y f
   module [f] = id-sys [f]

  from-hom-≈ : hom-≈ f g → f ＝ g
  from-hom-≈ = id-sys-to-path-characterization.to-＝ [f] g

  to-hom-≈-is-equiv : is-equiv from-hom-≈
  to-hom-≈-is-equiv = id-sys-to-path-characterization.to-＝-is-equiv [f] g
\end{code}
