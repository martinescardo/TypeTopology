Jonathan Sterling, started 22 March, 2023.

Based on Egbert Rijke's "Introduction to Homotopy Type Theory".

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.IdentitySystems where

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.FunExt
open import UF.Retracts
open import UF.Subsingletons
open import UF.PairFun as PairFun

record Has-Id-Sys {𝓦} (A : 𝓤 ̇ ) (a : A) (fam : A → 𝓦 ̇) : 𝓤ω where
 field
  ctr : fam a
  ind : {𝓥 : Universe} (P : (x : A) (q : fam x) → 𝓥 ̇) (p : P a ctr) (x : A) (q : fam x) → P x q
  ind-β : {𝓥 : Universe} (P : (x : A) (q : fam x) → 𝓥 ̇) (p : P a ctr) → ind P p a ctr ＝ p

 to-＝ : (x : A) → fam x → a ＝ x
 to-＝ = ind _ refl

 from-＝ : (x : A) → a ＝ x → fam x
 from-＝ x refl = ctr

 to-＝-is-equiv : (x : A) → is-equiv (to-＝ x)
 pr₁ (pr₁ (to-＝-is-equiv x)) = from-＝ x
 pr₂ (pr₁ (to-＝-is-equiv x)) refl = ind-β _ _
 pr₁ (pr₂ (to-＝-is-equiv x)) = from-＝ x
 pr₂ (pr₂ (to-＝-is-equiv x)) q = aux x q
  where
   aux : (x : A) (q : fam x) → from-＝ x (to-＝ x q) ＝ q
   aux = ind _ (ap (from-＝ a) (ind-β _ _))

record Id-Sys 𝓦 (A : 𝓤 ̇ ) (a : A) : 𝓤ω where
 field
  fam : A → 𝓦  ̇
  sys : Has-Id-Sys A a fam
 open Has-Id-Sys sys public


Unbiased-Id-Sys : Universe → 𝓤 ̇ → 𝓤ω
Unbiased-Id-Sys 𝓦 A = (a : A) → Id-Sys 𝓦 A a


module from-path-characterization
  {A : 𝓤 ̇ }
  (Q : A → A → 𝓤 ̇ )
  (H : {x y : A} → (x ＝ y) ≃ Q x y)
  (a : A)
 where
  open Id-Sys
  open Has-Id-Sys

  private
   Q-refl : {x : A} → Q x x
   Q-refl = eqtofun H refl

   aux
    : (P : (x : A) (q : Q a x) → 𝓥 ̇ )
    → (p : P a Q-refl)
    → (x : A)
    → (q : a ＝ x)
    → P x (eqtofun H q)
   aux P p x refl = p

  id-sys : Id-Sys 𝓤 A a
  fam id-sys = Q a
  ctr (sys id-sys) = Q-refl
  ind (sys id-sys) P p x q =
   transport (P x)
    (inverses-are-sections _ (eqtofun- H) q)
    (aux P p x (back-eqtofun H q))
  ind-β (sys id-sys) P p =
   ap gen
    (Aux-is-prop
     (back-eqtofun H Q-refl ,
      inverses-are-sections _ (eqtofun- H)  Q-refl)
     (refl , refl))
   where
    Aux = Σ ϕ ꞉ a ＝ a , eqtofun H ϕ ＝ Q-refl

    Aux-singl : singleton-type' refl ≃ Aux
    Aux-singl =
     pair-fun-equiv (≃-refl (a ＝ a)) λ ϕ →
     ap (eqtofun H) ,
     embedding-gives-embedding' _
      (equivs-are-embeddings _ (eqtofun- H))
      ϕ
      refl

    Aux-is-prop : is-prop Aux
    Aux-is-prop =
     retract-of-prop
      (≃-gives-◁ (≃-sym Aux-singl))
      (singleton-types'-are-props refl)

    gen : Aux → P a Q-refl
    gen (ϕ , ψ ) = transport (P a) ψ (aux P p a ϕ)


module _ 𝓦 𝓦' (A : 𝓤 ̇ ) (B : A → 𝓥 ̇ ) where
 record Dep-Id-Sys {a : A} ([a] : Id-Sys 𝓦 A a) (b : B a) : 𝓤ω where
  private
   module [a] = Id-Sys [a]
  field
   fam : (x : A) (q : [a].fam x) (y : B x) → 𝓦' ̇
   sys : Has-Id-Sys (B a) b (fam a [a].ctr)

  open Has-Id-Sys sys public


module _
  {A : 𝓤 ̇ } {B : A → 𝓥 ̇ }
  {a : A} {b : B a}
  ([a] : Id-Sys 𝓦 A a)
  ([b] : Dep-Id-Sys 𝓦 𝓦' A B [a] b)
 where
  module [a] = Id-Sys [a]
  module [b] = Dep-Id-Sys [b]

  open Id-Sys
  open Has-Id-Sys

  pair-id-sys : Id-Sys (𝓦 ⊔ 𝓦') (Σ B) (a , b)
  fam pair-id-sys (x , y) = Σ ϕ ꞉ [a].fam x , [b].fam x ϕ y
  pr₁ (ctr (sys pair-id-sys)) = [a].ctr
  pr₂ (ctr (sys pair-id-sys)) = [b].ctr
  ind (sys pair-id-sys) P p =
   λ (x , y) (ϕ , ψ) → aux x ϕ y ψ
   where
    aux : (x : A) (ϕ : [a].fam x) (y : B x) (ψ : [b].fam x ϕ y) → P (x , y) (ϕ , ψ)
    aux = [a].ind _ ([b].ind _ p)
  ind-β (sys pair-id-sys) P p =
   happly (happly ([a].ind-β _ _) b) [b].ctr ∙ [b].ind-β _ _

module _ (A : 𝓤 ̇ ) where
 open Id-Sys
 open Has-Id-Sys

 ＝-id-sys : Unbiased-Id-Sys 𝓤 A
 fam (＝-id-sys a) = a ＝_
 ctr (sys (＝-id-sys a)) = refl
 ind (sys (＝-id-sys a)) P p x refl = p
 ind-β (sys (＝-id-sys a)) _ _ = refl

module _ (fe : funext 𝓤 𝓥) {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) where
 homotopy-id-sys : Id-Sys (𝓤 ⊔ 𝓥) (A → B) f
 homotopy-id-sys = from-path-characterization.id-sys _∼_ (happly-≃ fe) f

\end{code}
