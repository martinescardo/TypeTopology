Jakub Opršal, 24 March 2026.
Updated on 8 June 2026 by Tom de Jong to use minimal library imports.

My goal here is to sketch key ideas of the proof that a type with a bunch of
ternary operations satisfying certain equations, known in universal algebra as
Willard equations [1, see §2], is necessarily a set.

In universal algebra, these equations are studied because they imply that the
congruence lattices (of any algebra in the variety) need to be *congruence
meet-semidistributive*. This is nevertheless irrelevant for our purposes. The
key point is that the equations are not satisfied in any variety of modules,
i.e., they do not have non-trivial models in the category of groups. Here is an example:

  sᵢ (x, y, x) = tᵢ (x, y, x)  for i = 1, 2, 3
  s₁ (x, x, y) = x
  t₁ (x, y, y) = s₁ (x, y, y)
  s₂ (x, x, y) = t₁ (x, x, y)
  s₃ (x, y, y) = s₂ (x, y, y)
  t₃ (x, x, y) = s₃ (x, x, y)
  t₂ (x, y, y) = t₃ (x, y, y)
  t₂ (x, x, y) = y

These are satisfied by semi-lattice terms s₁ = xy, t₁ = xyz, s₂ = xz, t₂ = z,
s₃ = xyz, and t₃ = yz. My claim is quite general, although in the file, I only
show even simpler case than the above.

THEOREM.
  Any type with ternary operations satisfying Willard equations is a set.

In essence, the argument shows that we can lift any *height 1 equation*, i.e.,
an equation that does not involve composition of operations, between idempotent
operations to the loop space. To do that, we need to assume that loops commute,
but this can be proved in case we satisfy Willards equations using an argument
of Taylor [2], which I also explored in the file [3]. For simplicity, in this
file, I assume that the loops commute, and leave the proof for later.

[1] Ross Willard. A Finite Basis Theorem For Residually Finite, Congruence
    Meet-semidistributive Varieties. J. of Symb. Logic 65(1):187-200, 2000.
    https://doi.org/10.2307/2586531.
[2] Walter Taylor. Varieties obeying homotopy laws. Can. J. Math., XXIX(3):
    498–527, 1977. https://doi.org/10.4153/CJM-1977-054-9.
[3] Jakub Opršal, AlgebraicStructuresForcingSethood.WeakNearUnanimity, March
    2026.

We start with some library for ternary idempotent functions.

\begin{code}

{-# OPTIONS --safe --without-K #-}
module AlgebraicStructuresForcingSethood.SimpleCaseOfWillard where

open import MLTT.Universes
open import MLTT.Id
open import MLTT.Sigma
open import UF.Base using
  ( ap₃
  ; ap₃-∙
  ; refl-left-neutral
  ; ＝-congr
  ; ＝-congr-refl
  ; ＝-congr-∙
  ; ＝-congr-sq
  ; cancel-left
  )

private
 sym = _⁻¹

module abelian-type (A : 𝓤 ̇  )
                    (loops-commute : {a : A} (p q : a ＝ a) → p ∙ q ＝ q ∙ p)
                    where

 conjugation-triv : {a : A} (g : a ＝ a) (p : a ＝ a)
                  → ＝-congr g g p ＝ p
 conjugation-triv g p = cancel-left (＝-congr-sq p g g ∙ loops-commute p g)

 one-＝-congr : {a b c : A} (p : a ＝ a) (q : b ＝ b)
                (h₀ : a ＝ b) (h₁ : a ＝ c) (h₂ : b ＝ c)
              → ＝-congr h₀ h₀ p ＝ q
              → ＝-congr h₁ h₁ p ＝ ＝-congr h₂ h₂ q
 one-＝-congr p q refl h₁ refl eq = conjugation-triv h₁ p ∙ eq

\end{code}

The core idea of the proof is that each ternary operation f gives us a
commuting triangle of paths:

                   *
                  / \
  Ωf refl p refl /   \ Ωf refl refl p
                /  f  \
               * ----- *
              Ωf p refl p

\begin{code}

module ternary-idempotent (A    : 𝓤 ̇ )
                          (f    : A → A → A → A)
                          (idem : (x : A) → f x x x ＝ x)
                          where

 Ωf : {a : A} → a ＝ a → a ＝ a → a ＝ a → a ＝ a
 Ωf p q r = ＝-congr (idem _) (idem _) (ap₃ f p q r)

 triangle : {a : A} (p : a ＝ a)
          → Ωf p refl refl ∙ Ωf refl refl p ＝ Ωf p refl p
 triangle {a} p =
  Ωf p refl refl ∙ Ωf refl refl p                                    ＝⟨ I ⟩
  ＝-congr (idem a) (idem a) (ap₃ f p refl refl ∙ ap₃ f refl refl p) ＝⟨ II ⟩
  ＝-congr (idem a) (idem a) (ap₃ f (p ∙ refl) refl (refl ∙ p))      ＝⟨ III ⟩
  Ωf p refl p                                                        ∎
   where
    I = sym (＝-congr-∙ (idem a) (idem a) (idem a)
                        (ap₃ f p refl refl)
                        (ap₃ f refl refl p))
    II = ap (λ x → ＝-congr (idem a) (idem a) x)
            (sym (ap₃-∙ f p refl refl refl refl p))
    III = ap (λ x →  ＝-congr (idem a) (idem a) (ap₃ f p refl x))
             refl-left-neutral

\end{code}

Next, we build a framework for lifting equations to the action on loops. To be
able to do this, we will need that loops commute.

\begin{code}

module equation-lift (A : 𝓤 ̇ )
                     (s t    : A → A → A → A)
                     (idem-s : (x : A) → s x x x ＝ x)
                     (idem-t : (x : A) → t x x x ＝ x)
                     (loops-commute : {a : A} (p q : a ＝ a) → p ∙ q ＝ q ∙ p)
                     where

 open abelian-type A loops-commute
 open ternary-idempotent A s idem-s renaming (Ωf to Ωs)
 open ternary-idempotent A t idem-t renaming (Ωf to Ωt)

 Ωeq₁ : ((x y : A) → s x y y ＝ t x y y)
      → {a : A} (p q : a ＝ a)
      → Ωs p q q ＝ Ωt p q q
 Ωeq₁ eq {a} p q = one-＝-congr _ _ (eq a a) (idem-s a) (idem-t a) (eq^ p q)
  where
   eq^ : {a a' b b' : A} (p : a ＝ a') (q : b ＝ b')
        → ＝-congr (eq a b) (eq a' b') (ap₃ s p q q) ＝ ap₃ t p q q
   eq^ refl refl = ＝-congr-refl (eq _ _)

 Ωeq₂ : ((x y : A) → s x y x ＝ t x y x)
      → {a : A} (p q : a ＝ a)
      → Ωs p q p ＝ Ωt p q p
 Ωeq₂ eq {a} p q = one-＝-congr _ _ (eq a a) (idem-s a) (idem-t a) (eq^ p q)
  where
   eq^ : {a a' b b' : A} (p : a ＝ a') (q : b ＝ b')
        → ＝-congr (eq a b) (eq a' b') (ap₃ s p q p) ＝ ap₃ t p q p
   eq^ refl refl = ＝-congr-refl (eq _ _)

 Ωeq₃ : ((x y : A) → s x x y ＝ t x x y)
      → {a : A} (p q : a ＝ a)
      → Ωs p p q ＝ Ωt p p q
 Ωeq₃ eq {a} p q = one-＝-congr _ _ (eq a a) (idem-s a) (idem-t a) (eq^ p q)
  where
   eq^ : {a a' b b' : A} (p : a ＝ a') (q : b ＝ b')
        → ＝-congr (eq a b) (eq a' b') (ap₃ s p p q) ＝ ap₃ t p p q
   eq^ refl refl = ＝-congr-refl (eq _ _)

\end{code}

Now, we can properly work with Willard's equations. I write down the simplest
non-trivial case with two ternary operations s and t. The point I want to make
here is that the same technique would also apply to any more complicated
Willard's equations.

\begin{code}

module simple-willard (A : 𝓤 ̇ )
                      (s t : A → A → A → A)
                      (start : (x y : A) → s x x y ＝ x)
                      (st₀   : (x y : A) → s x y y ＝ t x y y)
                      (st₁   : (x y : A) → s x y x ＝ t x y x)
                      (end   : (x y : A) → t x x y ＝ y)
                      (loops-commute : {a : A} (p q : a ＝ a) → p ∙ q ＝ q ∙ p)
                      where

 open ternary-idempotent A s (λ x → start x x)
  renaming (Ωf to Ωs; triangle to triangle-s)
 open ternary-idempotent A t (λ x → end x x)
  renaming (Ωf to Ωt; triangle to triangle-t)
 open equation-lift A s t (λ x → start x x) (λ x → end x x) loops-commute
  using (Ωeq₁ ; Ωeq₂)

 Ωst₀ : {a : A} → (p q : a ＝ a) → Ωs p q q ＝ Ωt p q q
 Ωst₀ = Ωeq₁ st₀

 Ωst₁ : {a : A} → (p q : a ＝ a) → Ωs p q p ＝ Ωt p q p
 Ωst₁ = Ωeq₂ st₁

\end{code}

Willard's equations, and the above lifting lemma allow us to glue the triangles
together to get a shape with boundary p ∙ refl. For example, the simplest case
considered in this file consists of two operations s and t, and hence two
triangles glued as follows:

            p
        * ----- *
       / \  t  /
 refl /   \   / p₂
     /  s  \ /
    * ----- *
        p₂

In other words, we can prove that:

  p₂ ∙ refl ＝ Ωs p refl p = Ωt p refl p ＝ p₂ ∙ p

where p₂ ＝ Ωs p refl refl = Ωt p refl refl. We may then cancel p₂ and derive
the required refl = p.

\begin{code}

 is-set : {a : A} → (p : a ＝ a) → refl ＝ p
 is-set {a} p =
  refl                  ＝⟨ sym (start^ refl p) ⟩
  Ωs refl refl p        ＝⟨ cancel-left glue ⟩
  Ωt refl refl p        ＝⟨ end^ refl p ⟩
  p ∎
   where
    start^ : {a a' b b' : A} (p : a ＝ a') (q : b ＝ b')
           → ＝-congr (start a b) (start a' b') (ap₃ s p p q) ＝ p
    start^ refl refl = ＝-congr-refl (start _ _)

    end^ : {a a' b b' : A} (p : a ＝ a') (q : b ＝ b')
         → ＝-congr (end a b) (end a' b') (ap₃ t p p q) ＝ q
    end^ refl refl = ＝-congr-refl (end _ _)

    glue : Ωs p refl refl ∙ Ωs refl refl p ＝ Ωs p refl refl ∙ Ωt refl refl p
    glue =
      Ωs p refl refl ∙ Ωs refl refl p ＝⟨ triangle-s p ⟩
      Ωs p refl p                     ＝⟨ Ωst₁ p refl ⟩
      Ωt p refl p                     ＝⟨ sym (triangle-t p) ⟩
      Ωt p refl refl ∙ Ωt refl refl p ＝⟨ ap (λ x → x ∙ Ωt refl refl p)
                                             (sym (Ωst₀ p refl)) ⟩
      Ωs p refl refl ∙ Ωt refl refl p ∎

\end{code}

APPENDIX. Taylor term from Willard's term.

The rest of this code shows how to derive existence of a Taylor operation from
the above Willard operations. This is to justify the assumption that loops
commute, which could theoretically be proved by the same method as in [3]. Note
this is a variation on a trick from Taylor's paper [2].

The core idea is to create one term `taylor` (in this case of arity 3 * 3 = 9),
such that

 taylor x x x y y y z z z = s x y z
 taylor x y z x y z x y z = t x y z

and then show that this term satisfies enough identities to be considered a
Taylor term, and hence imply that loops commute.

\begin{code}

 private
  idemₛ : (x : A) → s x x x ＝ x
  idemₛ x = start x x

  idemₜ : (x : A) → t x x x ＝ x
  idemₜ x = end x x

  taylor : A → A → A → A → A → A → A → A → A → A
  taylor x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ = s (t x₀ x₁ x₂) (t x₃ x₄ x₅) (t x₆ x₇ x₈)

  eq₀ : (x y : A) → taylor x x y x x y x x y ＝ taylor y y y y y y y y y
  eq₀ x y =
   taylor x x y x x y x x y ＝⟨ idemₛ (t x x y) ⟩
   t x x y                  ＝⟨ end x y ⟩
   y                        ＝⟨ sym (idemₜ y) ⟩
   t y y y                  ＝⟨ sym (idemₛ (t y y y)) ⟩
   taylor y y y y y y y y y ∎

  eq₁ = eq₀

  eq₂ : (x y : A) → taylor x x x y y y y y y ＝ taylor x y y x y y x y y
  eq₂ x y =
   taylor x x x y y y y y y ＝⟨ ap₃ s (idemₜ x) (idemₜ y) (idemₜ y) ⟩
   s x y y                  ＝⟨ st₀ x y ⟩
   t x y y                  ＝⟨ sym (idemₛ (t x y y)) ⟩
   taylor x y y x y y x y y ∎

  eq₃ = eq₀
  eq₄ = eq₀

  eq₅ : (x y : A) → taylor x x x y y y x x x ＝ taylor x y x x y x x y x
  eq₅ x y =
   taylor x x x y y y x x x ＝⟨ ap₃ s (idemₜ x) (idemₜ y) (idemₜ x) ⟩
   s x y x                  ＝⟨ st₁ x y ⟩
   t x y x                  ＝⟨ sym (idemₛ (t x y x)) ⟩
   taylor x y x x y x x y x ∎

  eq₆ = eq₀
  eq₇ = eq₀

  eq₈ : (x y : A) → taylor x x x x x x x x x ＝ taylor x x x x x x y y y
  eq₈ x y =
   taylor x x x x x x x x x ＝⟨ idemₛ (t x x x) ⟩
   t x x x                  ＝⟨ idemₜ x ⟩
   x                        ＝⟨ sym (start x y) ⟩
   s x x y                  ＝⟨ sym (ap₃ s (idemₜ x) (idemₜ x) (idemₜ y)) ⟩
   taylor x x x x x x y y y ∎

\end{code}
