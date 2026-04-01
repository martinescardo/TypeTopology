Jakub Opršal, 24 Mar 2026.

THEOREM.
  Any type with ternary operations satisfying Willard equations is a set.

We start with some library for ternary idempotent functions. We will work with
triangles obtained by applying the ternary operation on the three triangles
involving p and refl.

\begin{code}

{-# OPTIONS --safe --without-K #-}
module gist.WillardsEquations where

open import MLTT.Spartan

sym : {A : Type} {a b : A} → (a ＝ b) → (b ＝ a)
sym = _⁻¹

refl∙ : {A : Type} {a b : A} (q : a ＝ b) → refl ∙ q ＝ q
refl∙ refl = refl

∙-cancel : {A : Type} {a b c : A} (q : a ＝ b) {p p' : b ＝ c} → q ∙ p ＝ q ∙ p' → p ＝ p'
∙-cancel refl {p = p} {p' = p'} h = sym (refl∙ p) ∙ h ∙ (refl∙ p')

ap₂ : {A B C : Type} (f : A → B → C) {a₁ a₂ : A} {b₁ b₂ : B}
    → a₁ ＝ a₂
    → b₁ ＝ b₂
    → f a₁ b₁ ＝ f a₂ b₂
ap₂ f refl refl = refl

ap₃ : {A B C D : Type} (f : A → B → C → D) {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C}
    → a₁ ＝ a₂
    → b₁ ＝ b₂
    → c₁ ＝ c₂
    → f a₁ b₁ c₁ ＝ f a₂ b₂ c₂
ap₃ f refl refl refl = refl

ap₃-homo : {A B C D : Type}
           (f : A → B → C → D)
           {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B} {c₁ c₂ c₃ : C}
           (pa : a₁ ＝ a₂) (qa : a₂ ＝ a₃)
           (pb : b₁ ＝ b₂) (qb : b₂ ＝ b₃)
           (pc : c₁ ＝ c₂) (qc : c₂ ＝ c₃)
         → ((ap₃ f) pa pb pc) ∙ ((ap₃ f) qa qb qc)
           ＝ (ap₃ f) (pa ∙ qa) (pb ∙ qb) (pc ∙ qc)
ap₃-homo f {a₁ = a} {b₁ = b} {c₁ = c} refl refl refl refl refl refl = refl

eq-cong : {A : Type} {a a' b b' : A}
        → (a ＝ a') → (b ＝ b') → (a ＝ b) → (a' ＝ b')
eq-cong refl refl p = p

eq-cong-∙ : {A : Type} {a a' b b' c c' : A}
            {q : a ＝ a'} {q' : b ＝ b'} {q'' : c ＝ c'}
            (p : a ＝ b) (r : b ＝ c)
          → eq-cong q q'' (p ∙ r) ＝ eq-cong q q' p ∙ eq-cong q' q'' r
eq-cong-∙ {q = refl} {q' = refl} {q'' = refl} p r = refl

eq-cong-refl : {A : Type} {a a' : A} (q : a ＝ a')
             → eq-cong q q refl ＝ refl
eq-cong-refl refl = refl

eq-cong-sq : {A : Type} {a a' b b' : A} (h₁ : a ＝ a') (h₂ : b ＝ b') (p : a ＝ b)
          → h₁ ∙ eq-cong h₁ h₂ p ＝ p ∙ h₂
eq-cong-sq refl refl p = (refl∙ p)

\end{code}

The goal is to prove that the type is a set. Again, we do this by applying
our ternary operations on the same triangles as in the case of majority. Let us define this triangle from a single ternary idempotent operation.

\begin{code}

module ternary-idempotent (A : Type)
                          (f : A → A → A → A)
                          (idem : (x : A) → f x x x ＝ x)
                          where

 Ωf : {a : A} → a ＝ a → a ＝ a → a ＝ a → a ＝ a
 Ωf p q r = eq-cong (idem _) (idem _) (ap₃ f p q r)

 triangle : {a : A} (p : a ＝ a)
          → Ωf p refl refl ∙ Ωf refl refl p ＝ Ωf p refl p
 triangle {a} p =
  Ωf p refl refl ∙ Ωf refl refl p                                    ＝⟨ I ⟩
  eq-cong (idem a) (idem a) (ap₃ f p refl refl ∙ ap₃ f refl refl p)  ＝⟨ II ⟩
  eq-cong (idem a) (idem a) (ap₃ f (p ∙ refl) refl (refl ∙ p))       ＝⟨ III ⟩
  Ωf p refl p ∎
   where
    I = sym (eq-cong-∙ {q = idem a} {q' = idem a} {q'' = idem a}
                       (ap₃ f p refl refl)
                       (ap₃ f refl refl p))
    II = ap (λ x → eq-cong (idem a) (idem a) x)
            (ap₃-homo f p refl refl refl refl p)
    III = ap (λ x →  eq-cong (idem a) (idem a) (ap₃ f p refl x)) (refl∙ p)

\end{code}

Next, we build a framework for lifting equations to the action on loops. To be
able to do this, we will need that loops commute.

\begin{code}

module equation^ (A : Type)
                 (s t    : A → A → A → A)
                 (idem-s : (x : A) → s x x x ＝ x)
                 (idem-t : (x : A) → t x x x ＝ x)
                 (loops-commute : {a : A} (p q : a ＝ a) → p ∙ q ＝ q ∙ p)
                 where

 open ternary-idempotent A s idem-s renaming (Ωf to Ωs)
 open ternary-idempotent A t idem-t renaming (Ωf to Ωt)

 conjugation-triv : {a : A} (g : a ＝ a) (p : a ＝ a)
                  → eq-cong g g p ＝ p
 conjugation-triv g p = ∙-cancel g (eq-cong-sq g g p ∙ loops-commute p g)

 one-eq-cong : {a b c : A} (p : a ＝ a) (q : b ＝ b)
               (h₀ : a ＝ b) (h₁ : a ＝ c) (h₂ : b ＝ c)
             → eq-cong h₀ h₀ p ＝ q
             → eq-cong h₁ h₁ p ＝ eq-cong h₂ h₂ q
 one-eq-cong p q refl h₁ refl eq = conjugation-triv h₁ p ∙ eq

 Ωeq₁ : ((x y : A) → s x y y ＝ t x y y)
      → {a : A} (p q : a ＝ a)
      → Ωs p q q ＝ Ωt p q q
 Ωeq₁ eq {a} p q = one-eq-cong _ _ (eq a a) (idem-s a) (idem-t a) (eq^ p q)
  where
   eq^ : {a a' b b' : A} (p : a ＝ a') (q : b ＝ b')
        → eq-cong (eq a b) (eq a' b') (ap₃ s p q q) ＝ ap₃ t p q q
   eq^ refl refl = eq-cong-refl (eq _ _)

 Ωeq₂ : ((x y : A) → s x y x ＝ t x y x)
      → {a : A} (p q : a ＝ a)
      → Ωs p q p ＝ Ωt p q p
 Ωeq₂ eq {a} p q = one-eq-cong _ _ (eq a a) (idem-s a) (idem-t a) (eq^ p q)
  where
   eq^ : {a a' b b' : A} (p : a ＝ a') (q : b ＝ b')
        → eq-cong (eq a b) (eq a' b') (ap₃ s p q p) ＝ ap₃ t p q p
   eq^ refl refl = eq-cong-refl (eq _ _)

 Ωeq₃ : ((x y : A) → s x x y ＝ t x x y)
      → {a : A} (p q : a ＝ a)
      → Ωs p p q ＝ Ωt p p q
 Ωeq₃ eq {a} p q = one-eq-cong _ _ (eq a a) (idem-s a) (idem-t a) (eq^ p q)
  where
   eq^ : {a a' b b' : A} (p : a ＝ a') (q : b ＝ b')
        → eq-cong (eq a b) (eq a' b') (ap₃ s p p q) ＝ ap₃ t p p q
   eq^ refl refl = eq-cong-refl (eq _ _)

\end{code}

Now, we can properly work with Willard's equations. I write down the simplest
non-trivial case with two ternary operations s and t.

I am assuming here that the paths of the type commute. I believe I can prove it
by a similar technique as in the file gist.TaylorsLemma, but it involves a 9-ary
operation, and it might be easier to write the fully general case.

\begin{code}

module simple-willard (A     : Type)
                      (s t   : A → A → A → A)
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
 open equation^ A s t (λ x → start x x) (λ x → end x x) loops-commute
                using (Ωeq₁ ; Ωeq₂)

 Ωst₀ : {a : A} → (p q : a ＝ a) → Ωs p q q ＝ Ωt p q q
 Ωst₀ = Ωeq₁ st₀

 Ωst₁ : {a : A} → (p q : a ＝ a) → Ωs p q p ＝ Ωt p q p
 Ωst₁ = Ωeq₂ st₁

\end{code}

Having lifted the linear equations, we can start gluing triangles together, as
follows:
            p
        * ----- *
       / \  t  /
 refl /   \   / p₁
     /  s  \ /
    * ----- *
        p₁

In other words:
  p₂ ∙ p ＝ p₁ ＝ p₂ ∙ refl
where
  p₁ ＝ Ωs p refl p    = Ωt p refl p
  p₂ ＝ Ωs p refl refl = Ωt p refl refl

We essentially obtain a closed shape with boudary p ∙ refl, which will consequently show that p ＝ refl.

\begin{code}

 is-set : {a : A} → (p : a ＝ a) → refl ＝ p
 is-set {a} p =
  refl                  ＝⟨ sym (start^ refl p) ⟩
  Ωs refl refl p        ＝⟨ ∙-cancel (Ωs p refl refl) glue ⟩
  Ωt refl refl p        ＝⟨ end^ refl p ⟩
  p ∎
   where
    start^ : {a a' b b' : A} (p : a ＝ a') (q : b ＝ b')
           → eq-cong (start a b) (start a' b') (ap₃ s p p q) ＝ p
    start^ refl refl = eq-cong-refl (start _ _)

    end^ : {a a' b b' : A} (p : a ＝ a') (q : b ＝ b')
         → eq-cong (end a b) (end a' b') (ap₃ t p p q) ＝ q
    end^ refl refl = eq-cong-refl (end _ _)

    glue : Ωs p refl refl ∙ Ωs refl refl p ＝ Ωs p refl refl ∙ Ωt refl refl p
    glue =
      Ωs p refl refl ∙ Ωs refl refl p ＝⟨ triangle-s p ⟩
      Ωs p refl p                     ＝⟨ Ωst₁ p refl ⟩
      Ωt p refl p                     ＝⟨ sym (triangle-t p) ⟩
      Ωt p refl refl ∙ Ωt refl refl p ＝⟨ ap (λ x → x ∙ Ωt refl refl p)
                                            (sym (Ωst₀ p refl)) ⟩
      Ωs p refl refl ∙ Ωt refl refl p ∎

\end{code}

Leaving the proof that this has a Taylor term at the end. From this, I could
theoretically derive that the loops commute using a similar technique as in
[gist.TaylorsLemma].

\begin{code}
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
