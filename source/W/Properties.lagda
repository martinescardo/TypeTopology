Martin Escardo. 19th December 2020, June 2023.

General properties of W-types.

Notice that we don't assume any axioms from univalent foundations
other than function extensionality, but that we formulate and prove
properties in univalent style.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module W.Properties (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) where

open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Retracts
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import W.Type

private
 𝕎 = W X A

\end{code}

We first show that the identity type of 𝕎 is equivalent to _＝ʷ_
defined as follows.

\begin{code}

_＝ʷ_ : 𝕎 → 𝕎 → 𝓤 ⊔ 𝓥 ̇
ssup x f ＝ʷ ssup x' f' = Σ p ꞉ x ＝ x' , ((a : A x) → f a ＝ʷ f' (transport A p a))

＝ʷ-refl : (w : 𝕎) → w ＝ʷ w
＝ʷ-refl (ssup x f) = refl , (λ a → ＝ʷ-refl (f a))

singleton-typeʷ : 𝕎 → 𝓤 ⊔ 𝓥 ̇
singleton-typeʷ w = Σ t ꞉ 𝕎 , w ＝ʷ t

W-center : (w : 𝕎) → singleton-typeʷ w
W-center w = w , ＝ʷ-refl w

W-centrality : Fun-Ext → (w : 𝕎) (σ : singleton-typeʷ w) → W-center w ＝ σ
W-centrality fe w@(ssup x f) σ@(ssup x g , refl , u) = IV
 where
  have-u : (a : A x) → f a ＝ʷ g a
  have-u = u

  IH : (a : A x) → W-center (f a) ＝ (g a , u a)
  IH a = W-centrality fe (f a) (g a , u a)

  I : (λ a → W-center (f a)) ＝ (λ a → g a , u a)
  I = dfunext fe IH

  π : (Σ h ꞉ (A x → 𝕎) , ((a : A x) → f a ＝ʷ h a))
    → singleton-typeʷ (ssup x f)
  π (h , v) = ssup x h , refl , v

  II : (f , λ a → ＝ʷ-refl (f a)) ＝[ domain π ] (g , u)
  II = ap ΠΣ-distr I

  III : (ssup x f , refl , (λ a → ＝ʷ-refl (f a))) ＝ (ssup x g , refl , u)
  III = ap π II

  IV = W-center w                               ＝⟨refl⟩
       ssup x f , refl , (λ a → ＝ʷ-refl (f a)) ＝⟨ III ⟩
       ssup x g , refl , u                      ＝⟨refl⟩
       σ                                        ∎

singleton-typesʷ-are-singletons : Fun-Ext
                                → (w : 𝕎) → is-singleton (singleton-typeʷ w)
singleton-typesʷ-are-singletons fe w = W-center w , W-centrality fe w

\end{code}

From this it follows that the canonical map from the native notion of
𝕎-identity to the alternative notion of 𝕎-identity defined above is an
equivalence:

\begin{code}

idtoidʷ : (w t : 𝕎) → w ＝ t → w ＝ʷ t
idtoidʷ w w refl = ＝ʷ-refl w

idtoidʷ-is-equiv : Fun-Ext → (w t : 𝕎) → is-equiv (idtoidʷ w t)
idtoidʷ-is-equiv fe w = I
 where
  f : singleton-type w → singleton-typeʷ w
  f = NatΣ (idtoidʷ w)

  f-is-equiv : is-equiv f
  f-is-equiv = maps-of-singletons-are-equivs f
                (singleton-types-are-singletons w)
                (singleton-typesʷ-are-singletons fe w)

  I : (t : 𝕎) → is-equiv (idtoidʷ w t)
  I = NatΣ-equiv-gives-fiberwise-equiv (idtoidʷ w) f-is-equiv

idtoidʷ-≃ : Fun-Ext → (w t : 𝕎) → (w ＝ t) ≃ (w ＝ʷ t)
idtoidʷ-≃ fe w t = idtoidʷ w t , idtoidʷ-is-equiv fe w t

\end{code}

We now describe ways to "construct" and "destruct" native 𝕎
identifications, which are mutually inverse and hence induce an
equivalence.

\begin{code}

to-W-＝ : {x  : X} {φ  : A x  → 𝕎}
          {x' : X} {φ' : A x' → 𝕎}
        → (Σ p ꞉ x ＝ x' , (φ ＝ φ' ∘ transport A p))
        → ssup x φ ＝[ 𝕎 ] ssup x' φ'
to-W-＝ {x} {φ} {x} {φ'} (refl , f) = ap (ssup x) f

from-W-＝ : {x  : X} {φ  : A x  → 𝕎}
              {x' : X} {φ' : A x' → 𝕎}
            → ssup x φ ＝[ 𝕎 ] ssup x' φ'
            → (Σ p ꞉ x ＝ x' , (φ ＝ φ' ∘ transport A p))
from-W-＝ refl = refl , refl

to-from-W-＝ : {x  : X} {φ  : A x  → 𝕎}
               {x' : X} {φ' : A x' → 𝕎}
            → (q : ssup x φ ＝[ 𝕎 ] ssup x' φ')
            → to-W-＝ (from-W-＝ q) ＝ q
to-from-W-＝ refl = refl

from-to-W-＝ : {x  : X} {φ  : A x  → 𝕎}
               {x' : X} {φ' : A x' → 𝕎}
            → (σ : Σ p ꞉ x ＝ x' , (φ ＝ φ' ∘ transport A p))
            → from-W-＝ (to-W-＝ {x} {φ} {x'} {φ'} σ) ＝  σ
from-to-W-＝ (refl , refl) = refl

W-＝ : {x  : X} {φ  : A x  → 𝕎}
       {x' : X} {φ' : A x' → 𝕎}
     → (ssup x φ ＝[ 𝕎 ] ssup x' φ')
     ≃ (Σ p ꞉ x ＝ x' , (φ ＝ φ' ∘ transport A p))
W-＝ {x} {φ} {x'} {φ'} = qinveq
                          from-W-＝
                          (to-W-＝ ,
                           to-from-W-＝ ,
                           from-to-W-＝ {x} {φ} {x'} {φ'})
\end{code}

From this we conclude that if X is a proposition or a set, then 𝕎 is a
proposition or a set respectively:

\begin{code}

W-is-prop : funext 𝓥 (𝓤 ⊔ 𝓥)
          → is-prop X
          → is-prop 𝕎
W-is-prop fe X-is-prop (ssup x φ) (ssup x' φ') = γ
 where
  p : x ＝ x'
  p = X-is-prop x x'

  IH : (a : A x) → φ a ＝ φ' (transport A p a)
  IH a = W-is-prop fe X-is-prop (φ a) (φ' (transport A p a))

  γ : ssup x φ ＝ ssup x' φ'
  γ = to-W-＝ (p , dfunext fe IH)

W-is-set : funext 𝓥 (𝓤 ⊔ 𝓥)
         → is-set X
         → is-set 𝕎
W-is-set fe X-is-set {ssup x φ} {ssup x' φ'} = γ
 where
  S = Σ p ꞉ x ＝ x' , (φ ∼ φ' ∘ transport A p)

  IH : (p : x ＝ x') (a : A x) → is-prop (φ a ＝ φ' (transport A p a))
  IH p a = W-is-set fe X-is-set {φ a} {φ' (transport A p a)}

  α : is-prop S
  α = Σ-is-prop X-is-set (λ p → Π-is-prop fe (IH p))

  β : retract (ssup x φ ＝ ssup x' φ') of S
  β = (λ (p , h) → to-W-＝ (p , dfunext fe h)) ,
      (λ p → pr₁ (from-W-＝ p) , happly (pr₂ (from-W-＝ p))) ,
      h
    where
     h : (λ (p : ssup x (λ v → φ v) ＝ ssup x' (λ v → φ' v))
         → to-W-＝ (pr₁ (from-W-＝ p) , dfunext fe (happly (pr₂ (from-W-＝ p)))))
       ∼ id
     h refl =  ap (ssup x) (dfunext fe (happly refl)) ＝⟨ I ⟩
               ap (ssup x) refl                       ＝⟨refl⟩
               refl                                   ∎
                where
                 I = ap (ap (ssup x)) (funext-happly fe φ φ refl)

  γ : is-prop (ssup x φ ＝ ssup x' φ')
  γ = retract-of-prop β α

\end{code}

Notice that, in both cases, we didn't need to assume anything about
the family A to deduce the truncation level of the type 𝕎 = W X A.
Only the truncation level of X matters.

When the two roots are literally the same, and X is a set, the
identification of the forests is a homotopy, the loop that from-W-＝
produces being refl and its transport therefore the identity.

\begin{code}

forest-＝ : is-set X
         → {x : X} {φ φ' : A x → 𝕎}
         → ssup x φ ＝ ssup x φ'
         → φ ∼ φ'
forest-＝ X-is-set {x} {φ} {φ'} p = happly III
 where
  I : x ＝ x
  I = pr₁ (from-W-＝ p)

  II : φ ＝ φ' ∘ transport A I
  II = pr₂ (from-W-＝ p)

  III : φ ＝ φ'
  III = transport (λ - → φ ＝ φ' ∘ transport A -) (X-is-set I refl) II

\end{code}
