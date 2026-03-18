Tom de Jong, 18 March 2026.
Following a discussion with Jakub Opršal.

If a type has a commutative and idempotent binary operation, then its loop space
(at any given point) is commutative.

In gist.ThereAreNoHigherSemilattices2, I formalized that such an operation on a
type induces an idempotent commutative operation ＊Ω on its loop spaces that
moreover is a homomorphism (called interchange in that file):
  (p ∙ q) ＊Ω (r ∙ s) ＝ (p ＊Ω r) ∙ (q ＊Ω s).

Jakub Opršal noted that this is sufficient to prove that ∙ is commutative.
He attributes the argument to Walter Taylor ([Corollary 5.3, 1] for a more
general statement). Jakub also has a later rephrasing of the (simpler) argument
as [Lemma 2.12, 2].

Another (different?) proof is given by David Wärn as part of a MathOverflow
answer: https://mathoverflow.net/a/496927
But I did not distill this from his formalization when I wrote
gist.ThereAreNoHigherSemilattices2 (where David's formalization is referenced).

[1] Walter Taylor. Varieties obeying homotopy laws. Can. J. Math., XXIX(3):
    498–527, 1977. https://doi.org/10.4153/CJM-1977-054-9.
[2] Sebastian Meyer and Jakub Opršal. A topological proof of the Hell–Nešetřil dichotomy.
    https://arxiv.org/abs/2409.12627v2

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.CommutativeLoopSpaces where

open import Agda.Primitive renaming (Set to Type)
open import gist.ThereAreNoHigherSemilattices2

refl-right-neutral : {A : Type} {a b : A} (p : a ＝ b) → p ∙ refl ＝ p
refl-right-neutral refl = refl

refl-left-neutral : {A : Type} {a b : A} (p : a ＝ b) → refl ∙ p ＝ p
refl-left-neutral refl = refl

module idempotent-commutative-operation
        (A           : Type)
        (a₀          : A)
        (_⋆_         : A → A → A)
        (idempotent  : (a : A) → a ⋆ a ＝ a)
        (commutative : (a b : A) → a ⋆ b ＝ b ⋆ a)
       where

 open idempotent A _⋆_ idempotent
 open pointed a₀
 open pointed-type A a₀

 ∙-is-commutative : (p q : ΩA) → p ∙ q ＝ q ∙ p
 ∙-is-commutative = V
  where
   I : (p : ΩA) → p ＝ (p ＊Ω refl) ∙ (refl ＊Ω p)
   I p =
    sym ((p ＊Ω refl) ∙ (refl ＊Ω p) ＝⟨ ＊Ω-interchange-∙ p refl refl p ⟩
         (p ∙ refl) ＊Ω (refl ∙ p)   ＝⟨ I' ⟩
         p ＊Ω p                     ＝⟨ ＊Ω-idempotent p ⟩
         p                           ∎)
     where
      I' = ap₂ _＊Ω_ (refl-right-neutral p) (refl-left-neutral p)

   II : (p q : ΩA) → (p ＊Ω refl) ∙ (refl ＊Ω q) ＝ (refl ＊Ω q) ∙ (p ＊Ω refl)
   II p q =
    (p ＊Ω refl) ∙ (refl ＊Ω q) ＝⟨ II₁ ⟩
    (refl ＊Ω p) ∙ (q ＊Ω refl) ＝⟨ II₂ ⟩
    (refl ∙ q) ＊Ω (p ∙ refl)   ＝⟨ II₃ ⟩
    q ＊Ω p                     ＝⟨ II₄ ⟩
    p ＊Ω q                     ＝⟨ II₅ ⟩
    (refl ∙ p) ＊Ω (q ∙ refl)   ＝⟨ II₆ ⟩
    (refl ＊Ω q) ∙ (p ＊Ω refl) ∎
     where
      II₁ = ap₂ _∙_ (＊Ω-commutative commutative p refl)
                    (＊Ω-commutative commutative refl q)
      II₂ = ＊Ω-interchange-∙ refl p q refl
      II₃ = ap₂ _＊Ω_ (refl-left-neutral q) (refl-right-neutral p)
      II₄ = ＊Ω-commutative commutative q p
      II₅ = ap₂ _＊Ω_ (sym (refl-left-neutral p)) (sym (refl-right-neutral q))
      II₆ = sym (＊Ω-interchange-∙ refl q p refl)

   III : (p : ΩA) → p ＝ (p ∙ p) ＊Ω refl
   III p = p                           ＝⟨ I p ⟩
           (p ＊Ω refl) ∙ (refl ＊Ω p) ＝⟨ III' ⟩
           (p ＊Ω refl) ∙ (p ＊Ω refl) ＝⟨ ＊Ω-interchange-∙ p refl p refl ⟩
           (p ∙ p) ＊Ω refl            ∎
    where
     III' = ap ((p ＊Ω refl) ∙_) (＊Ω-commutative commutative refl p)

   IV : (q : ΩA) → q ＝ refl ＊Ω (q ∙ q)
   IV q = q                           ＝⟨ I q ⟩
          (q ＊Ω refl) ∙ (refl ＊Ω q) ＝⟨ IV' ⟩
          (refl ＊Ω q) ∙ (refl ＊Ω q) ＝⟨ ＊Ω-interchange-∙ refl q refl q ⟩
          refl ＊Ω (q ∙ q)            ∎
    where
     IV' = ap (_∙ (refl ＊Ω q)) (＊Ω-commutative commutative q refl)

   V : (p q : ΩA) → p ∙ q ＝ q ∙ p
   V p q =
    p ∙ q                         ＝⟨ ap₂ _∙_ (III p) (IV q) ⟩
    (p' ＊Ω refl) ∙ (refl ＊Ω q') ＝⟨ II p' q' ⟩
    (refl ＊Ω q') ∙ (p' ＊Ω refl) ＝⟨ ap₂ _∙_ (sym (IV q)) (sym (III p)) ⟩
    q ∙ p                         ∎
     where
      p' = p ∙ p
      q' = q ∙ q

\end{code}