Martin Escardo, 24-25 June 2026.

This file answers a question posed in Various.LawvereFPT, specifically
in the module generalized-Coquand, regarding whether a certain
diagonalization construction could be replaced by a second application
of Lawvere's fixed point theorem.

The answer is that no, not directly. However, we can generalize
Lawvere's FPT as follows. In the above file, we defined

  lfix : {A : 𝓤 ̇ } {X : 𝓥 ̇ }
       → (A → (A → X))
       → ((A → X) → A)
       → (X → X) → X
  lfix r s f = r (s (λ a → f (r a a))) (s (λ a → f (r a a)))

and then proved various fixed point properties for it, including

  lfix-is-fixed-point : {A : 𝓤 ̇ } {X : 𝓥 ̇ }
                        (r : A → (A → X))
                      → (s : (A → X) → A)
                      → s is-section·-of r
                      → (f : X → X) → lfix r s f ＝ f (lfix r s f)

and

  LFPT : {A : 𝓤 ̇ } {X : 𝓥 ̇ } (φ : A → (A → X))
       → is-surjection φ
       → (f : X → X) → ∃ x ꞉ X , x ＝ f x

Here we generalize both, by replacing the identity type former _＝_ by
any binary relation _≈_ whatsoever, and by replacing the notions of
section and of surjection accordingly.

We apply the former to get a simplified version of the module
generalized-Coquand, whose conclusions include

  Lemma₄ : ¬ (Σ U ꞉ 𝓤 ̇ , retract 𝓤 ̇ of U)

  corollary : ∀ 𝓤 → ¬ (retract 𝓤 ⁺ ̇ of (𝓤 ̇ ))

  Theorem : ¬ (Σ U ꞉ 𝓤 ̇ , 𝓤 ̇ ≃ U)

  Corollary : ¬ (𝓤 ⁺ ̇ ≃ 𝓤 ̇ )

At the moment we don't have any application of the second
generalization.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Various.LawvereFPT-Generalized where

open import MLTT.Spartan
open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.Retracts
open import Various.LawvereFPT
open import W.Type

\end{code}

We now develop the first generalization, where the assumptions are
given in two nested anonymous submodules.

\begin{code}

module _
        {𝓤 𝓥 𝓦 : Universe}
        (A : 𝓤 ̇ )
        (X : 𝓥 ̇ )
        (_≈_ : X → X → 𝓦 ̇ )
       where

  private
   𝓕 : 𝓤 ⊔ 𝓥 ̇
   𝓕 = (A → X) → (A → X)

   _≈̇_ : 𝓕 → 𝓕 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
   ϕ ≈̇ ψ = (g : A → X) (a : A) → ϕ g a ≈ ψ g a

  module _ (r  : A → (A → X))
           (s  : (A → X) → A)
           (rs : (r ∘ s) ≈̇ id)
         where

\end{code}

Notice that the proof of the following is the same as the original
proof of the particular case lfix-is-fixed-point, with _＝_ replaced
by _≈_.

\begin{code}

   lfix-is-relational-fixed-point : (f : X → X)
                                  → lfix r s f ≈ f (lfix r s f)
   lfix-is-relational-fixed-point f = e
    where
     g : A → X
     g a = f (r a a)

     e : lfix r s f ≈ f (lfix r s f)
     e = rs g (s g)

   relational-LFPT : (f : X → X) → Σ x ꞉ X , x ≈ f x
   relational-LFPT f = lfix r s f , lfix-is-relational-fixed-point f

\end{code}

For the module generalized-Coquand, we use the following particular
case, where B ≈ C is taken to be "C is a retract of B".

\begin{code}

LFPT-retract : {A : 𝓤 ̇ }
               (r : A → (A → 𝓥 ̇ ))
               (s : (A → 𝓥 ̇ ) → A)
             → ((g : A → 𝓥 ̇ ) (a : A) → retract (g a) of (r (s g) a))
             → (f : 𝓥 ̇ → 𝓥 ̇ ) → Σ B ꞉ 𝓥 ̇ , retract (f B) of B
LFPT-retract {𝓤} {𝓥} {A} = relational-LFPT A (𝓥 ̇ )
                             (λ (B C : 𝓥 ̇ ) → retract C of B)

\end{code}

We now develop the second generalization.

\begin{code}

open import UF.PropTrunc

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 module _
         {𝓤 𝓥 𝓦 : Universe}
         (A : 𝓤 ̇ )
         (X : 𝓥 ̇ )
         (_≈_ : X → X → 𝓦 ̇ )
        where

  private
   _≈̇_ : (A → X) → (A → X) → 𝓤 ⊔ 𝓦 ̇
   ϕ ≈̇ ψ = (a : A) → ϕ a ≈ ψ a

  module _ (φ : A → (A → X))
           (s : (g : A → X) → ∃ a ꞉ A , φ a ≈̇ g)
         where

   relational-surjection-LFPT : (f : X → X) → ∃ x ꞉ X , x ≈ f x
   relational-surjection-LFPT f = ∥∥-functor γ (s g)
    where
     g : A → X
     g a = f (φ a a)

     γ : (Σ a ꞉ A , φ a ≈̇ g) → Σ x ꞉ X , x ≈ f x
     γ (a , q) = φ a a , q a

\end{code}

Again, the proof is literally the same as the original one with the
identity type _＝_ in place of the arbitrary relation _≈_.

As discussed above, we don't yet have any application of the second
generalization. We conclude with an application of the first, which
was its motivation in the first place.

We show that certain assumptions are together impossible, by using two
applications of the fixed point theorem, where the first one is the
generalization and the second one is the original (to show that no
type is logically equivalent to its own negation).

\begin{code}

module generalized-Coquand-streamlined where

 Lemma₀ : (U  : 𝓤 ̇ )
          (R  : U → 𝓤 ̇ )
          (S  : 𝓤 ̇ → U)
          (ρ  : (X : 𝓤 ̇ ) → R (S X) → X)
          (σ  : (X : 𝓤 ̇ ) → X → R (S X))
          (ρσ : (X : 𝓤 ̇ ) (x : X) → ρ X (σ X x) ＝ x)
        → 𝟘
 Lemma₀ {𝓤} U R S ρ σ ρσ = III
  where
   A : 𝓤 ̇
   A = W U R

\end{code}

Thus, an element of the type A is of the form

  ssup u φ

with u : U and φ : R u → A.

\begin{code}

   r : A → (A → 𝓤 ̇ )
   r (ssup u φ) = fiber φ

\end{code}

Notice that, by definition, fiber φ a = Σ x ꞉ R u , φ x ＝ a.

For g : A → 𝓤, we have that Σ a ꞉ A , g a (abbreviated Σ g) lives
in 𝓤, and hence we can apply S to get a point of the type U. We have
that ρ (Σ g) : R (S (Σ g)) → Σ g, and so post-composition with the
first projection gives a function R (S (Σ g)) → A

\begin{code}

   s : (A → 𝓤 ̇ ) → A
   s g = ssup (S (Σ g)) (pr₁ ∘ ρ (Σ g))

   rs : (g : A → 𝓤 ̇ ) (a : A) → retract (g a) of (r (s g) a)
   rs g a = 𝓻 , 𝓼 , 𝓻𝓼
    where
     𝓻 : r (s g) a → g a
     𝓻 (u , e) = transport g e (pr₂ (ρ (Σ g) u))

     𝓼 : g a → r (s g) a
     𝓼 y = σ (Σ g) (a , y) , ap pr₁ (ρσ (Σ g) (a , y))

     𝓻𝓼 : (y : g a) → 𝓻 (𝓼 y) ＝ y
     𝓻𝓼 y =
      𝓻 (𝓼 y)                                                         ＝⟨refl⟩
      transport g (ap pr₁ (ρσ (Σ g) ay)) (pr₂ (ρ (Σ g) (σ (Σ g) ay))) ＝⟨ i ⟩
      transport (g ∘ pr₁) (ρσ (Σ g) ay) (pr₂ (ρ (Σ g) (σ (Σ g) ay)))  ＝⟨ ii ⟩
      pr₂ ay                                                          ＝⟨refl⟩
      y                                                               ∎
       where
        ay : Σ g
        ay = (a , y)

        i  = (transport-ap g pr₁ (ρσ (Σ g) ay))⁻¹
        ii = apd pr₂ (ρσ (Σ g) ay)

   I : Σ B ꞉ 𝓤 ̇ , retract (¬ B) of B
   I = LFPT-retract r s rs ¬_

   II : ¬ (Σ B ꞉ 𝓤 ̇ , retract (¬ B) of B)
   II (B , (f , g , _)) = not-equivalent-to-own-negation'' (f , g)

   III : 𝟘
   III = II I

 Lemma₁ : (U : 𝓤 ̇ ) (R : U → 𝓤 ̇ ) (S : 𝓤 ̇ → U)
        → ¬ ((X : 𝓤 ̇ ) → retract X of (R (S X)))
 Lemma₁ U R S ρ = Lemma₀ U R S
                   (λ X → retraction (ρ X))
                   (λ X → section (ρ X))
                   (λ X → retract-condition (ρ X))

 Lemma₂ : (U : 𝓤 ̇ ) (R : U → 𝓤 ̇ ) (S : 𝓤 ̇ → U)
        → ¬ ((X : 𝓤 ̇ ) → R (S X) ≃ X)
 Lemma₂ U R S e = Lemma₁ U R S (λ X → ≃-gives-▷ (e X))

 Lemma₃ : (U : 𝓤 ̇ ) (R : U → 𝓤 ̇ ) (S : 𝓤 ̇ → U)
        → ¬ ((X : 𝓤 ̇ ) → R (S X) ＝ X)
 Lemma₃ U R S p = Lemma₂ U R S (λ X → idtoeq (R (S X)) X (p X))

 Lemma₄ : ¬ (Σ U ꞉ 𝓤 ̇ , retract 𝓤 ̇ of U)
 Lemma₄ (U , R , S , TS) = Lemma₃ U R S TS

 corollary : ∀ 𝓤 → ¬ (retract 𝓤 ⁺ ̇ of (𝓤 ̇ ))
 corollary 𝓤 ρ = Lemma₄ ((𝓤 ̇ ) , ρ)

 Theorem : ¬ (Σ U ꞉ 𝓤 ̇ , 𝓤 ̇ ≃ U)
 Theorem (U , e) = Lemma₄ (U , ≃-gives-◁ e)

 Corollary : ¬ (𝓤 ⁺ ̇ ≃ 𝓤 ̇ )
 Corollary {𝓤} e = Theorem ((𝓤 ̇ ) , e)

\end{code}
