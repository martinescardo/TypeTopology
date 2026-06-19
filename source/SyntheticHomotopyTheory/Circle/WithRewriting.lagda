Tom de Jong, 19 June 2026.

We postulate the existence of the circle S¹ with definitional computation rules
using Agda's rewriting mechanism and derive its (dependent) universal property.

\begin{code}

{-# OPTIONS --rewriting --without-K #-}

module SyntheticHomotopyTheory.Circle.WithRewriting where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.FunExt

{-# BUILTIN REWRITE _＝_ #-}

postulate
 S¹ : 𝓤₀ ̇
 pt : S¹
 loop : pt ＝ pt

 S¹-recursion : (A : 𝓤 ̇ ) (a : A) → a ＝ a → S¹ → A
 S¹-induction : (A : S¹ → 𝓤 ̇ ) (a : A pt) (l : transport A loop a ＝ a)
              → (s : S¹) → A s

 S¹-recursion-comp-pt : (A : 𝓤 ̇ ) (a : A) (l : a ＝ a)
                      → S¹-recursion A a l pt ＝ a

 {-# REWRITE S¹-recursion-comp-pt #-}

\end{code}

In the following computation rule, we would like to write
   ap f loop ＝ l
but by definition the left-hand side reduces to a transport,
and Agda only allows rewriting when the left-hans side does not reduce,
so we replace [ap f loop] by its unfolding to a transport.

\begin{code}

 S¹-recursion-comp-loop
  : (A : 𝓤 ̇ ) (a : A) (l : a ＝ a)
  → let f = S¹-recursion A a l in
    transport (λ - → f pt ＝ f -) loop refl ＝ l

 {-# REWRITE S¹-recursion-comp-loop #-}

 S¹-induction-comp-pt : (A : S¹ → 𝓤 ̇ ) (a : A pt) (l : transport A loop a ＝ a)
                      → S¹-induction A a l pt ＝ a

 {-# REWRITE S¹-induction-comp-pt #-}

 S¹-induction-comp-loop
  : (A : S¹ → 𝓤 ̇ ) (a : A pt) (l : transport A loop a ＝ a)
  → apd' A (S¹-induction A a l) loop ＝ l

 {-# REWRITE S¹-induction-comp-loop #-}

\end{code}

The above rewrite rules amount to the following definitional equalities.

\begin{code}

private
 S¹-recursion-comp : (A : 𝓤 ̇ )
                     (a : A)
                     (l : a ＝ a)
                   → let f = S¹-recursion A a l in
                     (f pt , ap f loop) ＝
                     ((a , l) ∶ (Σ a' ꞉ A , a' ＝ a'))
 S¹-recursion-comp A a l = refl

 S¹-induction-comp : (A : S¹ → 𝓤 ̇ )
                     (a : A pt)
                     (l : transport A loop a ＝ a)
                   → let f = S¹-induction A a l in
                     (f pt , apd f loop) ＝
                     ((a , l) ∶ (Σ a' ꞉ A pt , transport A loop a' ＝ a'))
 S¹-induction-comp A a l = refl

\end{code}

Assuming function extensionality, we can derive the (dependent) universal
property.

\begin{code}

S¹-universal-property : funext 𝓤₀ 𝓤 → (A : 𝓤 ̇ )
                      → is-equiv ((λ f → f pt , ap f loop)
                                   ∶ ((S¹ → A) → Σ a ꞉ A , a ＝ a))
S¹-universal-property fe A =
 qinvs-are-equivs _ ((λ (a , l) → S¹-recursion A a l) , II , I)
  where
   I : (w : Σ a ꞉ A , a ＝ a) → w ＝ w
   I w = refl

   II : (λ f → S¹-recursion A (f pt) (ap f loop)) ∼ id
   II f = dfunext fe III
    where
     g : S¹ → A
     g = S¹-recursion A (f pt) (ap f loop)

     III : (s : S¹) → S¹-recursion A (f pt) (ap f loop) s ＝ f s
     III = S¹-induction _ refl IV
      where
       IV : transport (λ - → g - ＝ f -) loop refl ＝ refl
       IV = transport (λ - → g - ＝ f -) loop refl ＝⟨ IV₁ ⟩
            ap g loop ⁻¹ ∙ refl ∙ ap f loop        ＝⟨refl⟩
            ap g loop ⁻¹ ∙ ap f loop               ＝⟨refl⟩
            ap f loop ⁻¹ ∙ ap f loop               ＝⟨ IV₂ ⟩
            refl                                   ∎
        where
         IV₁ = transport-after-ap' loop g f refl
         IV₂ = left-inverse (ap f loop)

S¹-universal-property-≃
 : funext 𝓤₀ 𝓤 → (A : 𝓤 ̇ )
 → (S¹ → A) ≃ (Σ a ꞉ A , a ＝ a)
S¹-universal-property-≃ fe A =
 (λ f → f pt , ap f loop) , S¹-universal-property fe A

S¹-dependent-universal-property
 : funext 𝓤₀ 𝓤 → (A : S¹ → 𝓤 ̇ )
 → is-equiv ((λ f → f pt , apd f loop)
              ∶ ((Π s ꞉ S¹ , A s) → Σ a ꞉ A pt , transport A loop a ＝ a))
S¹-dependent-universal-property fe A =
 qinvs-are-equivs (λ f → f pt , apd f loop)
                  ((λ (a , l) → S¹-induction A a l) ,
                   I ,
                   (λ _ → refl))
  where
   I : (λ f → S¹-induction A (f pt) (apd f loop)) ∼ id
   I f = dfunext fe II
    where
     II : (s : S¹) → S¹-induction A (f pt) (apd f loop) s ＝ f s
     II = S¹-induction _ refl III
      where
       g : (s : S¹) → A s
       g = S¹-induction A (f pt) (apd f loop)
       III =
        transport (λ - → g - ＝ f -) loop refl                  ＝⟨ III₁ ⟩
        apd g loop ⁻¹ ∙ ap (transport A loop) refl ∙ apd f loop ＝⟨refl⟩
        apd f loop ⁻¹ ∙ ap (transport A loop) refl ∙ apd f loop ＝⟨ III₂ ⟩
        apd f loop ⁻¹ ∙ refl ∙ apd f loop                       ＝⟨refl⟩
        apd f loop ⁻¹ ∙ apd f loop                              ＝⟨ III₃ ⟩
        refl                                                    ∎
         where
          III₁ = transport-after-ap'-dependent g f loop refl
          III₂ = ap (λ - → apd f loop ⁻¹ ∙ - ∙ apd f loop)
                    (ap-refl (transport A loop))
          III₃ = left-inverse (apd f loop)

S¹-dependent-universal-property-≃
 : funext 𝓤₀ 𝓤 → (A : S¹ → 𝓤 ̇ )
 → (Π s ꞉ S¹ , A s) ≃ (Σ a ꞉ A pt , transport A loop a ＝ a)
S¹-dependent-universal-property-≃ fe A =
 (λ f → f pt , apd f loop) , S¹-dependent-universal-property fe A

\end{code}