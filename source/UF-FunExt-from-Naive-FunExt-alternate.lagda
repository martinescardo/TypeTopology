Cory Knapp, 6th June 2018.

This is an alternative version of UF-FunExt-from-Naive-FunExt.lagda
(by Martin Escardo, 19th May 2018);

here we split the proof that naive function extensionality into two parts:

1. If post-composition with an equivalence is again an equivalence, then
   function extensionality holds;

2. If naive-function extensionality holds, then the antecedent of the
   above holds.

Point 2. is already proved in UF-Equiv-Funext.lagda

\begin{code}

module UF-FunExt-from-Naive-FunExt-alternate where

open import SpartanMLTT
open import UF-Base
open import UF-FunExt
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Yoneda
open import UF-Subsingletons
open import UF-Retracts

equiv-post-comp-closure : ∀ U V W → (U ⊔ V ⊔ W) ′ ̇
equiv-post-comp-closure U V W = {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → Y)
                              → is-equiv f → is-equiv (λ (h : A → X) → f ∘ h)

equiv-post-gives-funext' : equiv-post-comp-closure (U ⊔ V) U U → funext U V
equiv-post-gives-funext' {U} {V} eqc = funext-via-singletons γ
  where
  γ : (X : U ̇) (A : X → V ̇) → ((x : X) → is-singleton (A x)) → is-singleton (Π A)
  γ X A φ = retract-of-singleton (r , s , rs) iss
   where
   f : Σ A → X
   f = pr₁
   eqf : is-equiv f
   eqf = pr₁-equivalence X A φ
   g : (X → Σ A) → (X → X)
   g h = f ∘ h
   eqg : is-equiv g
   eqg = eqc f eqf
   iss : is-singleton (Σ \(h : X → Σ A) →  f ∘ h ≡ id)
   iss = is-equiv-is-vv-equiv g eqg id
   r : (Σ \(h : X → Σ A) → f ∘ h ≡ id) → Π A
   r (h , p) x = transport A (happly p x) (pr₂ (h x))
   s : Π A → (Σ \(h : X → Σ A) →  f ∘ h ≡ id)
   s φ = (λ x → x , φ x) , refl
   rs : ∀ φ → r (s φ) ≡ φ
   rs φ = refl

naive-funext-gives-funext' : naive-funext U (U ⊔ V) → naive-funext U U → funext U V
naive-funext-gives-funext' nfe nfe' = equiv-post-gives-funext' (equiv-post nfe nfe')

naive-funext-gives-funext : naive-funext U U → funext U U
naive-funext-gives-funext fe = naive-funext-gives-funext' fe fe

\end{code}
