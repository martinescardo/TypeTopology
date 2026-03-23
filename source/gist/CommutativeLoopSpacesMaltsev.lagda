Jakub Opršal, 19 Mar 2026.

Maltsev operation makes loop commute. This is another consequence of Taylor's
lemma.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.CummutativeLoopSpacesMaltsev where

open import Agda.Primitive renaming (Set to Type)
open import gist.ThereAreNoHigherSemilattices2
 using (_＝_; refl; ap; ap₂;
  _∙_; sym; refl∙; ∙refl; _＝⟨_⟩_; _∎;
  eq-congr; eq-congr-∙; eq-congr-refl;
  module pointed-type)

∙-assoc :  {A : Type} {a b c d : A} (p : a ＝ b) (q : b ＝ c) (r : c ＝ d)
        → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
∙-assoc refl refl refl = refl

sym-cancel-l : {A : Type} {a b : A} (p : a ＝ b) → refl ＝ p ∙ sym p
sym-cancel-l refl = refl

sym-cancel-r : {A : Type} {a b : A} (p : a ＝ b) → sym p ∙ p ＝ refl
sym-cancel-r refl = refl

∙-lcancel : {A : Type} {a b c : A} {p : a ＝ b} {q q' : b ＝ c}
          → p ∙ q ＝ p ∙ q'
          → q ＝ q'
∙-lcancel {p = refl} {q} {q'} h = sym (refl∙ q) ∙ h ∙ (refl∙ q')

ap₃ : {A B C D : Type} {a a' : A} {b b' : B} {c c' : C}
      (f : A → B → C → D) (p : a ＝ a') (q : b ＝ b') (r : c ＝ c')
    → (f a b c ＝ f a' b' c')  
ap₃ f refl refl refl = refl

ap₃-homo : {A B C D : Type} (f : A → B → C → D)
           {a a' a'' : A} (p : a ＝ a') (p' : a' ＝ a'')
           {b b' b'' : B} (q : b ＝ b') (q' : b' ＝ b'')
           {c c' c'' : C} (r : c ＝ c') (r' : c' ＝ c'')
         → ap₃ f p q r ∙ ap₃ f p' q' r' ＝ ap₃ f (p ∙ p') (q ∙ q') (r ∙ r')
ap₃-homo f refl refl refl refl refl refl = refl

eq-congr-∙' : {A : Type} {a a' a'' b b' b'' : A}
              (h₁ : a' ＝ a'') (h₂ : b' ＝ b'')
              (h₃ : a ＝ a') (h₄ : b ＝ b')
              (p : a ＝ b)
            → eq-congr h₁ h₂ (eq-congr h₃ h₄ p) ＝ eq-congr (h₃ ∙ h₁) (h₄ ∙ h₂) p
eq-congr-∙' refl refl refl refl p = refl

module maltsev-operation
       (A   : Type)
       (a₀  : A)
       (μ   : A → A → A → A)
       (eq₁ : (x y : A) → μ x x y ＝ y)
       (eq₂ : (x y : A) → μ y x x ＝ y)
       where

 open pointed-type A a₀

 ι ε : μ a₀ a₀ a₀ ＝ a₀
 ι = eq₁ a₀ a₀
 ε = eq₂ a₀ a₀

 Ωμ : {a a' : A} (p q r : a ＝ a') → a ＝ a'
 Ωμ p q r = eq-congr (eq₁ _ _) (eq₁ _ _) (ap₃ μ p q r)

\end{code}

This is again based on Taylor's outline:

1. Elements of form `ap₃ μ p refl refl` and `ap₃ μ refl refl q` commute.
2. (equation) Everything is both of the form `ap₃ μ refl refl p` and of the
   form `ap₃ p refl refl`.
3. Profit.

\begin{code}
 rfl₀ : ΩA
 rfl₀ = refl

 simple-case : (p q : a₀ ＝ a₀)
  → ap₃ μ p rfl₀ rfl₀ ∙ ap₃ μ rfl₀ rfl₀ q ＝ ap₃ μ rfl₀ rfl₀ q ∙ ap₃ μ p rfl₀ rfl₀
 simple-case p q =
  ap₃ μ p refl refl ∙ ap₃ μ refl refl q                    ＝⟨ I ⟩
  ap₃ μ (p ∙ refl) (refl ∙ refl) (refl ∙ q)                ＝⟨ II ⟩ 
  ap₃ μ p refl q                                           ＝⟨ III ⟩
  ap₃ μ (refl ∙ p) (refl ∙ refl) (q ∙ refl)                ＝⟨ IV ⟩
  ap₃ μ refl refl q ∙ ap₃ μ p refl refl                    ∎
   where
    I = ap₃-homo μ p refl refl refl refl q
    II = ap₃ (ap₃ μ) (∙refl p) refl (refl∙ q)
    III = sym (ap₃ (ap₃ μ) (refl∙ p) refl (∙refl q))
    IV = sym (ap₃-homo μ refl p refl refl q refl)

 simple-case-Ω : (p q : ΩA)
  → Ωμ p rfl₀ rfl₀ ∙ Ωμ rfl₀ rfl₀ q ＝ Ωμ rfl₀ rfl₀ q ∙ Ωμ p rfl₀ rfl₀
 simple-case-Ω p q =
  Ωμ p refl refl ∙ Ωμ refl refl q                          ＝⟨ sym I ⟩
  eq-congr ι ι (ap₃ μ p refl refl ∙ ap₃ μ refl refl q)     ＝⟨ II ⟩
  eq-congr ι ι (ap₃ μ refl refl q ∙ ap₃ μ p refl refl)     ＝⟨ III ⟩
  Ωμ refl refl q ∙ Ωμ p refl refl                          ∎
   where
    I = eq-congr-∙ (ap₃ μ p refl refl) (ap₃ μ refl refl q)
    II = ap (eq-congr ι ι) (simple-case p q)
    III = eq-congr-∙ (ap₃ μ refl refl q) (ap₃ μ p refl refl)

 -- This concludes step 1

 expand₁ : (p : ΩA) → p ＝ Ωμ refl refl p
 expand₁ p = sym (eq₁^ refl p)
  where
   eq₁^ : {a a' b b' : A} (p' : a ＝ a') (q' : b ＝ b')
        → eq-congr (eq₁ a b) (eq₁ a' b') (ap₃ μ p' p' q') ＝ q'
   eq₁^ {a = a} {b = b} refl refl = eq-congr-refl (eq₁ a b)

 magic : ΩA → ΩA
 magic q = eq-congr (sym ι ∙ ε) (sym ι ∙ ε) q

 expand₂ : (q : ΩA) → q ＝ Ωμ (magic q) refl refl
 expand₂ q =
  q                                                                    ＝⟨ I ⟩
  eq-congr ((sym ι ∙ ε) ∙ (sym ε ∙ ι)) ((sym ι ∙ ε) ∙ (sym ε ∙ ι)) q   ＝⟨ II ⟩
  eq-congr (sym ε ∙ ι) (sym ε ∙ ι) q'                                  ＝⟨ III ⟩
  eq-congr (sym ε ∙ ι) (sym ε ∙ ι) (eq-congr ε ε (ap₃ μ q' refl refl)) ＝⟨ IV ⟩
  eq-congr (ε ∙ (sym ε ∙ ι)) (ε ∙ (sym ε ∙ ι)) (ap₃ μ q' refl refl)    ＝⟨ V ⟩
  Ωμ q' refl refl                                                      ∎
  where
   q' = magic q

   eq₂^ : {a a' b b' : A} (p' : a ＝ a') (p'' : b ＝ b')
        → eq-congr (eq₂ a b) (eq₂ a' b') (ap₃ μ p'' p' p') ＝ p''
   eq₂^ {a = a} {b = b} refl refl = eq-congr-refl (eq₂ a b)

   group-eq₀ : ε ∙ sym ε ∙ ι ＝ ι
   group-eq₀ =
    ε ∙ (sym ε ∙ ι) ＝⟨ sym (∙-assoc ε (sym ε) ι) ⟩ 
    (ε ∙ sym ε) ∙ ι ＝⟨ ap (λ x → x ∙ ι) (sym (sym-cancel-l ε)) ⟩ 
    refl ∙ ι        ＝⟨ refl∙ ι ⟩ 
    ι               ∎

   group-eq₁ : (sym ι ∙ ε) ∙ sym ε ∙ ι ＝ refl
   group-eq₁ =
    (sym ι ∙ ε) ∙ (sym ε ∙ ι) ＝⟨ ∙-assoc (sym ι) ε (sym ε ∙ ι) ⟩ 
    sym ι ∙ (ε ∙ (sym ε ∙ ι)) ＝⟨ ap (λ x → sym ι ∙ x) group-eq₀ ⟩
    sym ι ∙ ι                 ＝⟨ sym-cancel-r ι ⟩ 
    refl ∎

   I = sym(ap₂ (λ x y → eq-congr x y q) group-eq₁ group-eq₁)
   II = sym (eq-congr-∙' (sym ε ∙ ι) (sym ε ∙ ι) (sym ι ∙ ε) (sym ι ∙ ε) q)
   III = ap (eq-congr (sym ε ∙ ι) (sym ε ∙ ι)) (sym (eq₂^ refl q'))
   IV = eq-congr-∙' (sym ε ∙ ι) (sym ε ∙ ι) ε ε (ap₃ μ q' refl refl)
   V = ap₂ (λ x y → eq-congr x y (ap₃ μ q' refl refl)) group-eq₀ group-eq₀

 -- This concludes step 2

 ∙-is-commutative : (p q : ΩA) → p ∙ q ＝ q ∙ p
 ∙-is-commutative p q =
  p ∙ q                                        ＝⟨ I ⟩
  Ωμ (magic p) refl refl ∙ Ωμ refl refl q      ＝⟨ II ⟩
  Ωμ refl refl q ∙ Ωμ (magic p) refl refl      ＝⟨ III ⟩
  q ∙ p ∎
   where
    I = ap₂ _∙_ (expand₂ p) (expand₁ q)
    II = simple-case-Ω (magic p) q
    III = sym (ap₂ _∙_ (expand₁ q) (expand₂ p))
   
\end{code}
   
