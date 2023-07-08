Martin Escardo. 19th December 2020, June 2023.

General properties of W-types.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

module Iterative.W-Properties where

open import MLTT.Spartan
open import MLTT.W
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

\begin{code}

module _ (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) where

 private
  𝕎 = W X A

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

   IV = W-center w                               ＝⟨ refl ⟩
        ssup x f , refl , (λ a → ＝ʷ-refl (f a)) ＝⟨ III ⟩
        ssup x g , refl , u                      ＝⟨ refl ⟩
        σ                                        ∎

 singleton-typesʷ-are-singletons : Fun-Ext → (w : 𝕎) → is-singleton (singleton-typeʷ w)
 singleton-typesʷ-are-singletons fe w = W-center w , W-centrality fe w

 idtoeqʷ : (w t : 𝕎) → w ＝ t → w ＝ʷ t
 idtoeqʷ w w refl = ＝ʷ-refl w

 idtoeqʷ-is-equiv : Fun-Ext → (w t : 𝕎) → is-equiv (idtoeqʷ w t)
 idtoeqʷ-is-equiv fe w = I
  where
   f : singleton-type w → singleton-typeʷ w
   f = NatΣ (idtoeqʷ w)

   f-is-equiv : is-equiv f
   f-is-equiv = maps-of-singletons-are-equivs f
                 (singleton-types-are-singletons w)
                 (singleton-typesʷ-are-singletons fe w)

   I : (t : 𝕎) → is-equiv (idtoeqʷ w t)
   I = NatΣ-equiv-gives-fiberwise-equiv (idtoeqʷ w) f-is-equiv

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
             → from-W-＝ (to-W-＝ σ) ＝ σ
 from-to-W-＝ (refl , refl) = refl

 W-＝ : {x  : X} {φ  : A x  → 𝕎}
        {x' : X} {φ' : A x' → 𝕎}
      → (ssup x φ ＝[ 𝕎 ] ssup x' φ')
      ≃ (Σ p ꞉ x ＝ x' , (φ ＝ φ' ∘ transport A p))
 W-＝ = qinveq (from-W-＝) (to-W-＝ , to-from-W-＝ , from-to-W-＝)

 W-is-prop : funext 𝓥 (𝓤 ⊔ 𝓥) → is-prop X → is-prop 𝕎
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
                ap (ssup x) refl                       ＝⟨ refl ⟩
                refl                                   ∎
                 where
                  I = ap (ap (ssup x)) (funext-happly fe φ φ refl)

   γ : is-prop (ssup x φ ＝ ssup x' φ')
   γ = retract-of-prop β α

\end{code}
