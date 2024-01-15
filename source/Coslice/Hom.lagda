Jonathan Sterling, 22nd March 2023.

\begin{code}
{-# OPTIONS --safe --without-K #-}

module Coslice.Hom where

open import Coslice.Type
open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.IdentitySystems
open import UF.PairFun as PairFun
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-Properties

module _ {A : 𝓦 ̇ } where
 Hom-Str-Type : A ↓ 𝓤 → A ↓ 𝓥 → 𝓤 ⊔ 𝓥 ̇
 Hom-Str-Type X Y = target X → target Y

 Hom-Coh-Type : (X : A ↓ 𝓤) (Y : A ↓ 𝓥) → Hom-Str-Type X Y → 𝓦 ⊔ 𝓥 ̇
 Hom-Coh-Type X Y f = alg Y ∼ f ∘ alg X

 Hom : A ↓ 𝓤 → A ↓ 𝓥 → 𝓦 ⊔ 𝓤 ⊔ 𝓥 ̇
 Hom X Y = Σ f ꞉ Hom-Str-Type X Y , Hom-Coh-Type X Y f

 module _ {X : A ↓ 𝓤} {Y : A ↓ 𝓥} where
  hom-fun : Hom X Y → Hom-Str-Type X Y
  hom-fun (f , α[f]) = f

  hom-alg : (f : Hom X Y) → Hom-Coh-Type X Y (hom-fun f)
  hom-alg (f , α[f]) = α[f]

  module _ (f g : Hom X Y) where
   Homotopy-Str-Type : 𝓤 ⊔ 𝓥 ̇
   Homotopy-Str-Type = hom-fun f ∼ hom-fun g

   Homotopy-Coh-Type : Homotopy-Str-Type → 𝓦 ⊔ 𝓥 ̇
   Homotopy-Coh-Type ϕ = Π a ꞉ A , hom-alg g a ＝ hom-alg f a ∙ ϕ (alg X a)

   Hom-≈ : 𝓦 ⊔ 𝓤 ⊔ 𝓥 ̇
   Hom-≈ = Σ Homotopy-Coh-Type

 module _ (fe : FunExt) (X : A ↓ 𝓤) (Y : A ↓ 𝓥) (f : Hom X Y) where
  open Id-Sys
  open Has-Id-Sys
  open Dep-Id-Sys
  private [f] = homotopy-id-sys (fe _ _) (hom-fun f)
  private module [f] = Id-Sys [f]

  private
   Aux =
    Σ ϕ ꞉ Hom-Coh-Type X Y (hom-fun f) ,
    Homotopy-Coh-Type f (hom-fun f , ϕ) (λ _ → refl)

   Aux-singleton-type : singleton-type' (dfunext (fe _ _) (hom-alg f)) ≃ Aux
   Aux-singleton-type =
    pair-fun-equiv (happly , fe _ _ _ _) λ h →
    (ap happly ,
     embedding-gives-embedding' _ (equivs-are-embeddings _ (fe _ _ _ _)) _ _)
    ● (_∙ happly-funext (fe _ _) _ _ (hom-alg f)) ,
        ∙-is-equiv-right (happly-funext (fe _ _) _ _ (hom-alg f))
    ● happly-≃ (fe _ _)

   abstract
    Aux-retract-singleton : Aux ◁ singleton-type' (dfunext (fe _ _) (hom-alg f))
    Aux-retract-singleton = ≃-gives-◁ (≃-sym Aux-singleton-type)

    Aux-is-prop : is-prop Aux
    Aux-is-prop =
     retract-of-prop
      Aux-retract-singleton
      (singletons-are-props
       (singleton-types'-are-singletons _))

  hom-coh-id-sys
   : Dep-Id-Sys (𝓤 ⊔ 𝓥) (𝓦 ⊔ 𝓥)
      (Hom-Str-Type X Y)
      (Hom-Coh-Type X Y)
      [f]
      (hom-alg f)
  fam hom-coh-id-sys g ϕ α[g] = Homotopy-Coh-Type f (g , α[g]) ϕ
  ctr (sys hom-coh-id-sys) a = refl
  ind (sys hom-coh-id-sys) P p α[f] H =
   transport (uncurry P) (Aux-is-prop _ _) p
  ind-β (sys hom-coh-id-sys) P p =
   ap (λ - → transport (uncurry P) - p) lem
   where
    lem : Aux-is-prop (hom-alg f , λ _ → refl) (hom-alg f , λ _ → refl) ＝ refl
    lem = props-are-sets Aux-is-prop _ _

  hom-id-sys : Id-Sys (𝓤 ⊔ 𝓥 ⊔ 𝓦) (Hom X Y) f
  hom-id-sys = pair-id-sys [f] hom-coh-id-sys

 module _ (fe : FunExt) (X Y : Coslice A) (f g : Hom X Y) where
  private
   [f] = hom-id-sys fe X Y f
   module [f] = Id-Sys [f]

  from-hom-≈ : Hom-≈ f g → f ＝ g
  from-hom-≈ = [f].to-＝ g

  to-hom-≈-is-equiv : is-equiv from-hom-≈
  to-hom-≈-is-equiv = [f].to-＝-is-equiv g
\end{code}
