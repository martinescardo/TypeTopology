Tom de Jong, 18-24 December 2020

Formalizing a paper proof sketch from 12 November 2020.
Refactored 24 January 2022.

We construct the free join-semilattice on a set X as the Kuratowski finite
subsets of X.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT

open import ArithmeticViaEquivalence
open import Fin
open import Fin-Properties
open import JoinSemiLattices

open import UF-Base
open import UF-Equiv
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-ImageAndSurjection
open import UF-Powerset
open import UF-PropTrunc
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module FreeJoinSemiLattice
        (pt : propositional-truncations-exist)
       where

open import UF-Powerset-Fin pt hiding (κ)

open binary-union-of-subsets pt

open Kuratowski-finiteness pt

open ImageAndSurjection pt
open PropositionalTruncation pt hiding (_∨_)

\end{code}

The proof that the Kuratowski finite subsets of X denoted by 𝓚 X and ordered by
subset inclusion is a join-semilattice (with joins given by unions) is given in
UF-Powerset-Fin.lagda.

So we proceed directly to showing that 𝓚 X is the *free* join-semilattice on a
set X. Concretely, if L is a join-semilattice and f : X → L is any function,
then there is a *unique* mediating map f♭ : 𝓚 X → L such that:

(i)  f♭ is a join-semilattice homomorphism, i.e.
     - f♭ preserves the least element;
     - f♭ preserves binary joins.
(ii) the diagram
           f
     X ---------> L
      \          ^
       \        /
      η \      / ∃! f♭
         \    /
          v  /
          𝓚 X
     commutes.

The map η : X → 𝓚 X is given by mapping x to the singleton subset ❴ x ❵.

The idea in defining f♭ is to map a Kuratowski finite subset A to the finite
join ∨ⁿ (f ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e) in L, where e is some eumeration
(i.e. surjection) e : Fin n ↠ 𝕋 ⟨ A ⟩.

However, since Kuratowski finite subsets come with an *unspecified* such
enumeration, we must show that the choice of enumeration is irrelevant, i.e. any
two enumerations give rise to the same finite join. We then use a theorem by
Kraus et al. [1] (see wconstant-map-to-set-factors-through-truncation-of-domain)
to construct the desired mapping.

[1] Theorem 5.4 in
    "Notions of Anonymous Existence in Martin-Löf Type Theory"
    by Nicolai Kraus, Martín Escardó, Thierry Coquand and Thorsten Altenkirch.
    In Logical Methods in Computer Science, volume 13, issue 1.
    2017.

\begin{code}

module _
        (𝓛 : JoinSemiLattice 𝓥 𝓣)
       where

 open JoinSemiLattice 𝓛

 module _
         {X : 𝓤 ̇ }
         (X-is-set : is-set X)
         (f : X → L)
        where

  open singleton-subsets X-is-set
  open singleton-Kuratowski-finite-subsets X-is-set

  η : X → 𝓚 X
  η x = ❴ x ❵[𝓚]

\end{code}

We start by defining the mapping for a specified enumeration and we show that
the choice of enumeration is irrelevant, i.e. fₛ A is weakly constant.

\begin{code}
  fₛ : (A : 𝓟 X)
     → (Σ n ꞉ ℕ , Σ e ꞉ (Fin n → 𝕋 A) , is-surjection e)
     → L
  fₛ A (_ , e , _) = ∨ⁿ (f ∘ 𝕋-to-carrier A ∘ e)

  fₛ-is-wconstant : (A : 𝓟 X) → wconstant (fₛ A)
  fₛ-is-wconstant A (n , e , σ) (n' , e' , σ') = ⊑-is-antisymmetric _ _ u v
   where
    f' : 𝕋 A → L
    f' = f ∘ 𝕋-to-carrier A
    u : ∨ⁿ (f' ∘ e) ⊑ ∨ⁿ (f' ∘ e')
    u = ∨ⁿ-is-lowerbound-of-upperbounds (f' ∘ e) (∨ⁿ (f' ∘ e')) ψ
     where
      ψ : (k : Fin n) → (f' ∘ e) k ⊑ ∨ⁿ (f' ∘ e')
      ψ k = ∥∥-rec (⊑-is-prop-valued _ _) ϕ (σ' (e k))
       where
        ϕ : (Σ k' ꞉ Fin n' , e' k' ≡ e k) → (f' ∘ e) k ⊑ ∨ⁿ (f' ∘ e')
        ϕ (k' , p) = (f' ∘ e) k   ⊑⟨ ≡-to-⊑ (ap f' p ⁻¹)           ⟩
                     (f' ∘ e') k' ⊑⟨ ∨ⁿ-is-upperbound (f' ∘ e') k' ⟩
                     ∨ⁿ (f' ∘ e') ⊑∎
    v : ∨ⁿ (f' ∘ e') ⊑ ∨ⁿ (f' ∘ e)
    v = ∨ⁿ-is-lowerbound-of-upperbounds (f' ∘ e') (∨ⁿ (f' ∘ e)) ψ
     where
      ψ : (k' : Fin n') → (f' ∘ e') k' ⊑ ∨ⁿ (f' ∘ e)
      ψ k' = ∥∥-rec (⊑-is-prop-valued _ _) ϕ (σ (e' k'))
       where
        ϕ : (Σ k ꞉ Fin n , e k ≡ e' k') → (f' ∘ e') k' ⊑ ∨ⁿ (f' ∘ e)
        ϕ (k , p) = (f' ∘ e') k' ⊑⟨ ≡-to-⊑ (ap f' p ⁻¹)         ⟩
                    (f' ∘ e) k   ⊑⟨ ∨ⁿ-is-upperbound (f' ∘ e) k ⟩
                    ∨ⁿ (f' ∘ e)  ⊑∎

\end{code}

We now use the theorem by Kraus et al. to construct the map f♭ from fₛ.

\begin{code}

  f♭ : 𝓚 X → L
  f♭ (A , κ) =
   pr₁ (wconstant-map-to-set-factors-through-truncation-of-domain L-is-set
    (fₛ A) (fₛ-is-wconstant A)) κ

  f♭-in-terms-of-fₛ : (A : 𝓟 X) {n : ℕ} {e : (Fin n → 𝕋 A)} (σ : is-surjection e)
                      (κ : is-Kuratowski-finite-subset A)
                    → f♭ (A , κ) ≡ fₛ A (n , e , σ)
  f♭-in-terms-of-fₛ A {n} {e} σ κ = f♭ (A , κ)             ≡⟨ I  ⟩
                                    f♭ (A , ∣ n , e , σ ∣) ≡⟨ II ⟩
                                    fₛ A (n , e , σ)       ∎
   where
    I  = ap (λ - → f♭ (A , -)) (∥∥-is-prop κ ∣ n , e , σ ∣)
    II = (pr₂ (wconstant-map-to-set-factors-through-truncation-of-domain
                L-is-set
                (fₛ A) (fₛ-is-wconstant A))
          (n , e , σ)) ⁻¹

\end{code}

Recall that we must show that
(i)  f♭ is a join-semilattice homomorphism, i.e.
     - f♭ preserves the least element;
     - f♭ preserves binary joins.
(ii) the diagram
           f
     X ---------> L
      \          ^
       \        /
      η \      / ∃! f♭
         \    /
          v  /
          𝓚 X
     commutes.

We show (ii) and then (i) now.

\begin{code}

  f♭-after-η-is-f : f♭ ∘ η ∼ f
  f♭-after-η-is-f x = f♭ (η x)             ≡⟨ I  ⟩
                      fₛ ❴ x ❵ (1 , e , σ) ≡⟨ II ⟩
                      f x                  ∎
   where
    e : Fin 1 → 𝕋 ❴ x ❵
    e 𝟎 = x , refl
    σ : is-surjection e
    σ (x , refl) = ∣ 𝟎 , refl ∣
    I = f♭-in-terms-of-fₛ ❴ x ❵ σ ⟨ η x ⟩₂
    II = ⊑-is-antisymmetric _ _
          (∨-is-lowerbound-of-upperbounds _ _ _
           (⊥-is-least (f x)) (⊑-is-reflexive (f x)))
          (∨-is-upperbound₂ _ _)

  f♭-preserves-⊥ : f♭ ∅[𝓚] ≡ ⊥
  f♭-preserves-⊥ = ⊑-is-antisymmetric _ _ u v
   where
    u : f♭ ∅[𝓚] ⊑ ⊥
    u = f♭ ∅[𝓚]                     ⊑⟨ u₁ ⟩
        ∨ⁿ (f ∘ 𝕋-to-carrier ∅ ∘ e) ⊑⟨ u₂ ⟩
        ⊥                           ⊑∎
     where
      e : Fin 0 → 𝕋 {𝓤} {X} ∅
      e = 𝟘-elim
      σ : is-surjection e
      σ (x , x-in-emptyset) = 𝟘-elim x-in-emptyset
      u₁ = ≡-to-⊑ (f♭-in-terms-of-fₛ ∅ σ ∅-is-Kuratowski-finite-subset)
      u₂ = ⊑-is-reflexive ⊥
    v : ⊥ ⊑ f♭ ∅[𝓚]
    v = ⊥-is-least (f♭ ∅[𝓚])

  f♭-is-monotone : (A B : 𝓚 X)
                → ((x : X) → x ∈ ⟨ A ⟩ → x ∈ ⟨ B ⟩)
                → f♭ A ⊑ f♭ B
  f♭-is-monotone 𝔸@(A , κ₁) 𝔹@(B , κ₂) s =
   ∥∥-rec₂ (⊑-is-prop-valued (f♭ 𝔸) (f♭ 𝔹)) γ κ₁ κ₂
    where
     γ : (Σ n ꞉ ℕ , Fin n ↠ 𝕋 A)
       → (Σ m ꞉ ℕ , Fin m ↠ 𝕋 B)
       → f♭ (A , κ₁) ⊑ f♭ (B , κ₂)
     γ (n , e , e-surj) (n' , e' , e'-surj) =
      f♭ 𝔸                         ⊑⟨ u₁ ⟩
      ∨ⁿ (f ∘ 𝕋-to-carrier A ∘ e)  ⊑⟨ u₂ ⟩
      ∨ⁿ (f ∘ 𝕋-to-carrier B ∘ e') ⊑⟨ u₃ ⟩
      f♭ 𝔹                         ⊑∎
       where
        u₁ = ≡-to-⊑ (f♭-in-terms-of-fₛ A e-surj κ₁)
        u₃ = ≡-to-⊑ ((f♭-in-terms-of-fₛ B e'-surj κ₂) ⁻¹)
        u₂ = ∨ⁿ-is-lowerbound-of-upperbounds (f ∘ 𝕋-to-carrier A ∘ e)
                                             (∨ⁿ (f ∘ 𝕋-to-carrier B ∘ e')) γ₁
         where
          γ₁ : (k : Fin n) → (f ∘ 𝕋-to-carrier A ∘ e) k
                           ⊑ ∨ⁿ (f ∘ 𝕋-to-carrier B ∘ e')
          γ₁ k = ∥∥-rec (⊑-is-prop-valued _ _) γ₂ t
           where
            x : X
            x = 𝕋-to-carrier A (e k)
            a : x ∈ A
            a = 𝕋-to-membership A (e k)
            b : x ∈ B
            b = s x a
            t : ∃ k' ꞉ Fin n' , e' k' ≡ (x , b)
            t = e'-surj (x , b)
            γ₂ : (Σ k' ꞉ Fin n' , e' k' ≡ (x , b))
               → (f ∘ pr₁ ∘ e) k ⊑ ∨ⁿ (f ∘ pr₁ ∘ e')
            γ₂ (k' , p) = (f ∘ 𝕋-to-carrier A) (e k)   ⊑⟨ v₁ ⟩
                          (f ∘ 𝕋-to-carrier B) (e' k') ⊑⟨ v₂ ⟩
                          ∨ⁿ (f ∘ 𝕋-to-carrier B ∘ e') ⊑∎
             where
              v₁ = ≡-to-⊑ (ap f q)
               where
                q : 𝕋-to-carrier A (e k) ≡ 𝕋-to-carrier B (e' k')
                q = ap pr₁ (p ⁻¹)
              v₂ = ∨ⁿ-is-upperbound (f ∘ 𝕋-to-carrier B ∘ e') k'

  f♭-preserves-∨ : (A B : 𝓚 X) → f♭ (A ∪[𝓚] B) ≡ f♭ A ∨ f♭ B
  f♭-preserves-∨ A B = ⊑-is-antisymmetric _ _ u v
   where
    v : (f♭ A ∨ f♭ B) ⊑ f♭ (A ∪[𝓚] B)
    v = ∨-is-lowerbound-of-upperbounds _ _ _
        (f♭-is-monotone A (A ∪[𝓚] B) (∪[𝓚]-is-upperbound₁ A B))
        (f♭-is-monotone B (A ∪[𝓚] B) (∪[𝓚]-is-upperbound₂ A B))
    u : f♭ (A ∪[𝓚] B) ⊑ (f♭ A ∨ f♭ B)
    u = ∥∥-rec (⊑-is-prop-valued (f♭ (A ∪[𝓚] B)) (f♭ A ∨ f♭ B)) γ₁ (⟨ A ⟩₂)
     where
      γ₁ : (Σ n ꞉ ℕ , Σ e ꞉ (Fin n → 𝕋 ⟨ A ⟩) , is-surjection e)
         → f♭ (A ∪[𝓚] B) ⊑ (f♭ A ∨ f♭ B)
      γ₁ (n , e , σ) = ∥∥-rec (⊑-is-prop-valued _ _) γ₂ (⟨ B ⟩₂)
       where
        γ₂ : (Σ n' ꞉ ℕ , Σ e' ꞉ (Fin n' → 𝕋 ⟨ B ⟩) , is-surjection e')
           → f♭ (A ∪[𝓚] B) ⊑ (f♭ A ∨ f♭ B)
        γ₂ (n' , e' , σ') = f♭ (A ∪[𝓚] B)    ⊑⟨ l₁ ⟩
                            ∨ⁿ (f' ∘ [e,e']) ⊑⟨ l₂ ⟩
                            f♭ A ∨ f♭ B      ⊑∎
         where
          f' : 𝕋 (⟨ A ⟩ ∪ ⟨ B ⟩) → L
          f' = f ∘ 𝕋-to-carrier (⟨ A ⟩ ∪ ⟨ B ⟩)
          [e,e'] : Fin (n +' n') → 𝕋 (⟨ A ⟩ ∪ ⟨ B ⟩)
          [e,e'] = (∪-enum ⟨ A ⟩ ⟨ B ⟩ e e')
          τ : is-surjection [e,e']
          τ = ∪-enum-is-surjection ⟨ A ⟩ ⟨ B ⟩ e e' σ σ'
          l₁ = ≡-to-⊑ p
           where
            p : f♭ (A ∪[𝓚] B) ≡ fₛ (⟨ A ⟩ ∪ ⟨ B ⟩) (n +' n' , [e,e'] , τ)
            p = f♭-in-terms-of-fₛ (⟨ A ⟩ ∪ ⟨ B ⟩) τ ⟨ A ∪[𝓚] B ⟩₂
          l₂ = ∨ⁿ-is-lowerbound-of-upperbounds (f' ∘ [e,e']) (f♭ A ∨ f♭ B) ϕ
           where
            ϕ : (k : Fin (n +' n'))
              → (f' ∘ [e,e']) k ⊑ (f♭ A ∨ f♭ B)
            ϕ k = (f' ∘ [e,e']) k                   ⊑⟨ ⊑-is-reflexive _ ⟩
                  (f' ∘ ∪-enum' ⟨ A ⟩ ⟨ B ⟩ e e') c ⊑⟨ ψ c ⟩
                  (f♭ A ∨ f♭ B)                     ⊑∎
             where
              c : Fin n + Fin n'
              c = ⌜ Fin+homo n n' ⌝ k
              ψ : (c : Fin n + Fin n')
                → (f' ∘ ∪-enum' ⟨ A ⟩ ⟨ B ⟩ e e') c ⊑ (f♭ A ∨ f♭ B)
              ψ (inl k) = (f' ∘ ∪-enum' ⟨ A ⟩ ⟨ B ⟩ e e') (inl k) ⊑⟨ u₁ ⟩
                          (f ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e) k          ⊑⟨ u₂ ⟩
                          ∨ⁿ (f ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e)         ⊑⟨ u₃ ⟩
                          fₛ ⟨ A ⟩ (n , e , σ)                    ⊑⟨ u₄ ⟩
                          f♭ A                                    ⊑⟨ u₅ ⟩
                          f♭ A ∨ f♭ B                             ⊑∎
               where
                u₁ = ⊑-is-reflexive ((f ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e) k)
                u₂ = ∨ⁿ-is-upperbound (f ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e) k
                u₃ = ⊑-is-reflexive (∨ⁿ (f ∘ 𝕋-to-carrier ⟨ A ⟩ ∘ e))
                u₄ = ≡-to-⊑ ((f♭-in-terms-of-fₛ ⟨ A ⟩ σ ⟨ A ⟩₂) ⁻¹)
                u₅ = ∨-is-upperbound₁ (f♭ A) (f♭ B)
              ψ (inr k) = (f' ∘ ∪-enum' ⟨ A ⟩ ⟨ B ⟩ e e') (inr k) ⊑⟨ u₁' ⟩
                          (f ∘ 𝕋-to-carrier ⟨ B ⟩ ∘ e') k         ⊑⟨ u₂' ⟩
                          ∨ⁿ (f ∘ 𝕋-to-carrier ⟨ B ⟩ ∘ e')        ⊑⟨ u₃' ⟩
                          fₛ ⟨ B ⟩ (n' , e' , σ')                 ⊑⟨ u₄' ⟩
                          f♭ B                                    ⊑⟨ u₅' ⟩
                          f♭ A ∨ f♭ B                             ⊑∎
               where
                u₁' = ⊑-is-reflexive ((f ∘ 𝕋-to-carrier ⟨ B ⟩ ∘ e') k)
                u₂' = ∨ⁿ-is-upperbound (f ∘ 𝕋-to-carrier ⟨ B ⟩ ∘ e') k
                u₃' = ⊑-is-reflexive (∨ⁿ (f ∘ 𝕋-to-carrier ⟨ B ⟩ ∘ e'))
                u₄' = ≡-to-⊑ ((f♭-in-terms-of-fₛ ⟨ B ⟩ σ' ⟨ B ⟩₂) ⁻¹)
                u₅' = ∨-is-upperbound₂ (f♭ A) (f♭ B)

\end{code}

Finally we prove that f♭ is the unique map with the above properties (i) & (ii).
We do so by using the induction principle for Kuratowski finite subsets, which
is proved in UF-Powerset-Fin.lagda.

\begin{code}

  module _
          (pe : propext 𝓤)
          (fe : funext 𝓤 (𝓤 ⁺))
         where

   f♭-is-unique : (h : 𝓚 X → L)
                → h ∅[𝓚] ≡ ⊥
                → ((A B : 𝓚 X) → h (A ∪[𝓚] B) ≡ h A ∨ h B)
                → (h ∘ η ∼ f)
                → h ∼ f♭
   f♭-is-unique h p₁ p₂ p₃ = Kuratowski-finite-subset-induction pe fe
                             X X-is-set
                             (λ A → h A ≡ f♭ A)
                             (λ _ → L-is-set)
                             q₁ q₂ q₃
    where
     q₁ : h ∅[𝓚] ≡ f♭ ∅[𝓚]
     q₁ = h ∅[𝓚]  ≡⟨ p₁                ⟩
          ⊥       ≡⟨ f♭-preserves-⊥ ⁻¹ ⟩
          f♭ ∅[𝓚] ∎
     q₂ : (x : X) → h (η x) ≡ f♭ (η x)
     q₂ x = h (η x)  ≡⟨ p₃ x                   ⟩
            f x      ≡⟨ (f♭-after-η-is-f x) ⁻¹ ⟩
            f♭ (η x) ∎
     q₃ : (A B : 𝓚 X)
        → h A ≡ f♭ A
        → h B ≡ f♭ B
        → h (A ∪[𝓚] B) ≡ f♭ (A ∪[𝓚] B)
     q₃ A B r₁ r₂ = h (A ∪[𝓚] B)  ≡⟨ p₂ A B                  ⟩
                    h A ∨ h B     ≡⟨ ap₂ _∨_ r₁ r₂           ⟩
                    f♭ A ∨ f♭ B   ≡⟨ (f♭-preserves-∨ A B) ⁻¹ ⟩
                    f♭ (A ∪[𝓚] B) ∎

\end{code}

Assuming some more function extensionality axioms, we can prove "homotopy
uniqueness", i.e. the tuple consisting of f♭ together with the proofs of (i) and
(ii) is unique. This follows easily from the above, because (i) and (ii) are
subsingletons (as L is a set).

\begin{code}

  module _
          (pe : propext 𝓤)
          (fe : funext (𝓤 ⁺) (𝓤 ⁺ ⊔ 𝓥))
         where

   homotopy-uniqueness-of-f♭ :
    ∃! h ꞉ (𝓚 X → L) , (h ∅[𝓚] ≡ ⊥)
                     × ((A B : 𝓚 X) → h (A ∪[𝓚] B) ≡ h A ∨ h B)
                     × h ∘ η ∼ f
   homotopy-uniqueness-of-f♭ =
    (f♭ , f♭-preserves-⊥ , f♭-preserves-∨ , f♭-after-η-is-f) , γ
     where
      γ : (t : (Σ h ꞉ (𝓚 X → L) , (h ∅[𝓚] ≡ ⊥)
                                × ((A B : 𝓚 X) → h (A ∪[𝓚] B) ≡ h A ∨ h B)
                                × h ∘ η ∼ f))
        → (f♭ , f♭-preserves-⊥ , f♭-preserves-∨ , f♭-after-η-is-f) ≡ t
      γ (h , p₁ , p₂ , p₃) = to-subtype-≡ ψ
                             (dfunext (lower-funext (𝓤 ⁺) (𝓤 ⁺) fe)
                               (λ A → (f♭-is-unique
                                         pe
                                         (lower-funext (𝓤 ⁺) 𝓥 fe)
                                         h p₁ p₂ p₃ A) ⁻¹))
       where
        ψ : (k : 𝓚 X → L)
          → is-prop ((k ∅[𝓚] ≡ ⊥)
                    × ((A B : 𝓚 X) → k (A ∪[𝓚] B) ≡ (k A ∨ k B))
                    × k ∘ η ∼ f)
        ψ k = ×-is-prop L-is-set (×-is-prop
                                   (Π-is-prop fe
                                     (λ _ → Π-is-prop (lower-funext (𝓤 ⁺) (𝓤 ⁺) fe)
                                     (λ _ → L-is-set)))
                                   (Π-is-prop (lower-funext (𝓤 ⁺) (𝓤 ⁺) fe)
                                     (λ _ → L-is-set)))

\end{code}

Added 17th March 2021 by Martin Escardo. Alternative definition of 𝓚:

\begin{code}

open import UF-Embeddings

𝓚' : 𝓤 ̇ → 𝓤 ⁺ ̇
𝓚' {𝓤} X = Σ A ꞉ 𝓤 ̇ , (A ↪ X) × is-Kuratowski-finite A

\end{code}

TODO. Show that 𝓚' X is equivalent to 𝓚 X (using UF-Classifiers).

Tom de Jong, 27 August 2021. We implement this TODO.

\begin{code}

open import UF-Univalence

module _
        (ua : Univalence)
       where

 open import UF-Classifiers hiding (𝕋)
 open import UF-EquivalenceExamples

 𝓚-is-equivalent-to-𝓚' : (X : 𝓤 ̇ ) →  𝓚 X ≃ 𝓚' X
 𝓚-is-equivalent-to-𝓚' {𝓤} X = γ
  where
   φ : Subtypes X ≃ 𝓟 X
   φ = Ω-is-subtype-classifier ua X
   κ : 𝓤 ̇ → 𝓤 ̇
   κ = is-Kuratowski-finite
   γ = 𝓚 X                                                ≃⟨ ≃-refl _ ⟩
       (Σ A ꞉ 𝓟 X , κ (𝕋 A))                              ≃⟨ I        ⟩
       (Σ S ꞉ Subtypes X , κ (𝕋 (⌜ φ ⌝ S)))               ≃⟨ Σ-assoc  ⟩
       (Σ A ꞉ 𝓤 ̇ , Σ e ꞉ (A ↪ X) , κ (𝕋 (⌜ φ ⌝ (A , e)))) ≃⟨ II       ⟩
       (Σ A ꞉ 𝓤 ̇ , Σ e ꞉ (A ↪ X) , κ A)                   ≃⟨ ≃-refl _ ⟩
       (Σ A ꞉ 𝓤 ̇ , (A ↪ X) × κ A)                         ≃⟨ ≃-refl _ ⟩
       𝓚' X                                               ■
    where
     I  = ≃-sym (Σ-change-of-variable (λ A → is-Kuratowski-finite-subset A)
                   ⌜ φ ⌝ (⌜⌝-is-equiv φ))
     II = Σ-cong (λ A → Σ-cong (λ e → ψ A e))
      where
       ψ : (A : 𝓤 ̇ ) (e : A ↪ X)
         → κ (𝕋 (⌜ φ ⌝ (A , e))) ≃ κ A
       ψ A e = idtoeq (κ A') (κ A)
                (ap κ (eqtoid (ua 𝓤) A' A lemma))
        where
         A' : 𝓤 ̇
         A' = 𝕋 (⌜ φ ⌝ (A , e))
         lemma = A'                                   ≃⟨ ≃-refl _ ⟩
                 (Σ x ꞉ X , Σ a ꞉ A , etofun e a ≡ x) ≃⟨ τ        ⟩
                 A                                    ■
          where
           τ = total-fiber-is-domain (etofun e)

\end{code}
