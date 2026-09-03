Cory Knapp, 6th June 2018.

This is an alternative version of naive-funext-gives-funext from
UF.FunExt-Properties.lagda (by Martin Escardo, 19th May 2018);

here we split the proof that naive function extensionality into two parts:

1. If post-composition with an equivalence is again an equivalence, then
   function extensionality holds;

2. If naive-function extensionality holds, then the antecedent of the
   above holds.

Point 2. is already proved in UF.Equiv-FunExt.lagda

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.FunExt-from-Naive-FunExt where

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.Yoneda
open import UF.Subsingletons
open import UF.Retracts

equiv-post-comp-closure : ∀ 𝓤 𝓦 𝓥 → (𝓤 ⊔ 𝓥 ⊔ 𝓦) ⁺ ̇
equiv-post-comp-closure 𝓤 𝓥 𝓦 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } (f : X → Y)
                                → is-equiv f → is-equiv (λ (h : A → X) → f ∘ h)

equiv-post-gives-funext' : equiv-post-comp-closure (𝓤 ⊔ 𝓥) 𝓤 𝓤 → funext 𝓤 𝓥
equiv-post-gives-funext' {𝓤} {𝓥} eqc = funext-via-singletons γ
  where
  γ : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) → ((x : X) → is-singleton (A x)) → is-singleton (Π A)
  γ X A φ = retract-of-singleton (r , s , rs) iss
   where
   f : Σ A → X
   f = pr₁
   eqf : is-equiv f
   eqf = pr₁-is-equiv X A φ
   g : (X → Σ A) → (X → X)
   g h = f ∘ h
   eqg : is-equiv g
   eqg = eqc f eqf
   iss : ∃! h ꞉ (X → Σ A), f ∘ h ＝ id
   iss = equivs-are-vv-equivs g eqg id
   r : (Σ h ꞉ (X → Σ A), f ∘ h ＝ id) → Π A
   r (h , p) x = transport A (happly p x) (pr₂ (h x))
   s : Π A → (Σ h ꞉ (X → Σ A), f ∘ h ＝ id)
   s φ = (λ x → x , φ x) , refl
   rs : ∀ φ → r (s φ) ＝ φ
   rs φ = refl

naive-funext-gives-funext' : naive-funext 𝓤 (𝓤 ⊔ 𝓥) → naive-funext 𝓤 𝓤 → funext 𝓤 𝓥
naive-funext-gives-funext' nfe nfe' = equiv-post-gives-funext' (equiv-post nfe nfe')

naive-funext-gives-funext : naive-funext 𝓤 𝓤 → funext 𝓤 𝓤
naive-funext-gives-funext fe = naive-funext-gives-funext' fe fe

\end{code}
