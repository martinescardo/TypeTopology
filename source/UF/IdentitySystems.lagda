Jonathan Sterling, started 22 March, 2023.

Based on Egbert Rijke's "Introduction to Homotopy Type Theory".

\begin{code}

module UF.IdentitySystems where

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.FunExt
open import UF.Retracts
open import UF.Subsingletons
open import UF.PairFun as PairFun

record has-id-sys (A : 𝓤 ̇ ) (a : A) (fam : A → 𝓤 ̇) : 𝓤 ⁺ ̇ where
 field
  ctr : fam a
  ind : (P : (x : A) (q : fam x) → 𝓤 ̇) (p : P a ctr) (x : A) (q : fam x) → P x q
  ind-β : (P : (x : A) (q : fam x) → 𝓤 ̇) (p : P a ctr) → ind P p a ctr ＝ p

record id-sys (A : 𝓤 ̇ ) (a : A) : 𝓤 ⁺ ̇ where
 field
  fam : A → 𝓤 ̇
  sys : has-id-sys A a fam
 open has-id-sys sys public


module id-sys-to-path-characterization {A : 𝓤 ̇ } {a : A} ([a] : id-sys A a) where
 private
  module [a] = id-sys [a]

 to-＝ : (x : A) → [a].fam x → a ＝ x
 to-＝ = [a].ind _ refl

 from-＝ : (x : A) → a ＝ x → [a].fam x
 from-＝ x refl = [a].ctr

 to-＝-is-equiv : (x : A) → is-equiv (to-＝ x)
 pr₁ (pr₁ (to-＝-is-equiv x)) = from-＝ x
 pr₂ (pr₁ (to-＝-is-equiv x)) refl = [a].ind-β _ _
 pr₁ (pr₂ (to-＝-is-equiv x)) = from-＝ x
 pr₂ (pr₂ (to-＝-is-equiv x)) q = aux x q
  where
   aux : (x : A) (q : [a].fam x) → from-＝ x (to-＝ x q) ＝ q
   aux = [a].ind _ (ap (from-＝ a) ([a].ind-β _ _))



module path-characterization-to-id-sys {A : 𝓤 ̇ } (Q : A → A → 𝓤 ̇ ) (eqv : (x y : A) → (x ＝ y) ≃ Q x y) (a : A) where
 open id-sys
 open has-id-sys

 private
  aux : (P : (x : A) (q : Q a x) → 𝓤 ̇ ) (p : P a (⌜ eqv _ _ ⌝ refl)) (x : A) → (q : a ＝ x) → P x (⌜ eqv _ _ ⌝ q)
  aux P p x refl = p

 based-sys : id-sys A a
 fam based-sys = Q a
 ctr (sys based-sys) = ⌜ eqv _ _ ⌝ refl
 ind (sys based-sys) P p x q =
  transport (P x)
   (inverses-are-sections _ ⌜ eqv _ _ ⌝-is-equiv q)
   (aux P p x (⌜ eqv _ _ ⌝⁻¹ q))
 ind-β (sys based-sys) P p =
  ap gen
   (Aux-is-prop
    (⌜ eqv _ _ ⌝⁻¹ (⌜ eqv _ _ ⌝ refl) ,
     inverses-are-sections _ ⌜ eqv _ _ ⌝-is-equiv  (⌜ eqv _ _ ⌝ refl))
    (refl , refl))
  where
   Aux = Σ ϕ ꞉ a ＝ a , ⌜ eqv _ _ ⌝ ϕ ＝ ⌜ eqv _ _ ⌝ refl

   Aux-singl : singleton-type' refl ≃ Aux
   Aux-singl =
    pair-fun-equiv (≃-refl (a ＝ a)) λ ϕ →
    ap ⌜ eqv _ _ ⌝ ,
    embedding-gives-embedding' _
     (equivs-are-embeddings _ ⌜ eqv _ _ ⌝-is-equiv)
     ϕ
     refl

   Aux-is-prop : is-prop Aux
   Aux-is-prop = retract-of-prop (≃-gives-◁ (≃-sym Aux-singl)) (singleton-types'-are-props refl)

   gen : Aux → P a (⌜ eqv _ _ ⌝ refl)
   gen (ϕ , ψ ) = transport (P a) ψ (aux P p a ϕ)



record dep-id-sys (A : 𝓤 ̇ ) (B : A → 𝓤 ̇ ) {a : A} ([a] : id-sys A a) (b : B a) : 𝓤 ⁺ ̇ where
 private
  module [a] = id-sys [a]
 field
  fam : (x : A) (q : [a].fam x) (y : B x) → 𝓤 ̇
  sys : has-id-sys (B a) b (fam a [a].ctr)
 open has-id-sys sys public

module _ {A : 𝓤 ̇ } {B : A → 𝓤 ̇ } {a : A} {b : B a} ([a] : id-sys A a) ([b] : dep-id-sys A B [a] b) where
 module [a] = id-sys [a]
 module [b] = dep-id-sys [b]

 open id-sys
 open has-id-sys

 pair-id-sys : id-sys (Σ B) (a , b)
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

module _ (A : 𝓤 ̇ ) (a : A) where
 open id-sys
 open has-id-sys

 ＝-id-sys : id-sys A a
 fam ＝-id-sys = a ＝_
 ctr (sys ＝-id-sys) = refl
 ind (sys ＝-id-sys) P p x refl = p
 ind-β (sys ＝-id-sys) _ _ = refl

module _ (fe : funext 𝓤 𝓤) {A B : 𝓤 ̇ } (f : A → B) where
 homotopy-id-sys : id-sys (A → B) f
 homotopy-id-sys =
  path-characterization-to-id-sys.based-sys
   _∼_
   (λ _ _ → happly , fe _ _)
   f

\end{code}
