Jakub Opršal, 17 Mar 2026.

This is my take on semilattices using a statement that generalises David's
theorem and my majority result. I will use a specific example of Willard terms
and Taylor's lemma as a black box (for now), i.e., I will assume that the paths
on the type commute.

\begin{code}

module gist.ThereAreNoHigherSemilattices3 where

open import Agda.Primitive renaming (Set to Type)
open import gist.ThereAreNoHigherSemilattices2
open import gist.CommutativeLoopSpaces

∙-lcancel : {A : Type} {a b c : A} {p : a ＝ b} {q q' : b ＝ c}
          → p ∙ q ＝ p ∙ q'
          → q ＝ q'
∙-lcancel {p = refl} {q} {q'} h = sym (refl∙ q) ∙ h ∙ (refl∙ q')

sym-cancel-l : {A : Type} {a b : A} (p : a ＝ b) → refl ＝ p ∙ sym p
sym-cancel-l refl = refl

∙-assoc :  {A : Type} {a b c d : A} (p : a ＝ b) (q : b ＝ c) (r : c ＝ d)
        → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
∙-assoc refl refl refl = refl

ap₃ : {A B C D : Type} {a a' : A} {b b' : B} {c c' : C}
      (f : A → B → C → D) (p : a ＝ a') (q : b ＝ b') (r : c ＝ c')
    → (f a b c ＝ f a' b' c')  
ap₃ f refl refl refl = refl

\end{code}

This sets up our type theory. Now to actual work.

\begin{code}

module taylor-type
       (A             : Type)
       (a₀            : A)
       (loops-commute : (p : a₀ ＝ a₀) → (q : a₀ ＝ a₀) → p ∙ q ＝ q ∙ p)
       where

 conjugate : {a b : A} → a ＝ b → a ＝ a → b ＝ b
 conjugate refl p = p

 eq-cong : {a b c d : A} → a ＝ b → c ＝ d → a ＝ c → b ＝ d
 eq-cong refl refl p = p

 eq-cong-refl : {a b : A} → (p : a ＝ b) → eq-cong p p refl ＝ refl
 eq-cong-refl refl = refl

 conj-is-eq-cong :  {a b : A} → {q : a ＝ b} → {p : a ＝ a}
                 → conjugate q p ＝ eq-cong q q p
 conj-is-eq-cong {q = refl} = refl

 conj-refl : {a b : A} → {q : a ＝ b} → conjugate q refl ＝ refl
 conj-refl {q = refl} = refl

 conj-homo : {a b c : A}  (q : b ＝ c) (q'  : a ＝ b) (p : a ＝ a)
           → conjugate q (conjugate q' p) ＝ conjugate (q' ∙ q) p
 conj-homo refl refl p = refl

 conj-sq : {a b : A} (q : a ＝ b) (p : a ＝ a)
         → q ∙ (conjugate q p) ＝ p ∙ q
 conj-sq refl p = (refl∙ (conjugate refl p)) ∙ (sym (∙refl p))

 ΩA : Type
 ΩA = a₀ ＝ a₀

 conj-loop : (q p : ΩA) → conjugate q p ＝ p
 conj-loop q p = ∙-lcancel ((conj-sq q p) ∙ (loops-commute p q))

\end{code}

First, let me develop a thery of ternary operations and height 1 equations
between them. The first goal is to define operations on the loop space ΩA, and
show that they satisfy all height 1 equations of the original ones.

\begin{code}

 _^_ : (f : A → A → A → A)
     → (φ : f a₀ a₀ a₀ ＝ a₀)
     → ΩA → ΩA → ΩA → ΩA
 (f ^ φ) x₀ x₁ x₂ = conjugate φ (ap₃ f x₀ x₁ x₂)

 module lift₃ (f g : A → A → A → A)
              (φ   : f a₀ a₀ a₀ ＝ a₀)
              (γ   : g a₀ a₀ a₀ ＝ a₀)
              (eq  : (x y : A) → f x x y ＝ g x x y)
              where

  eq^ : (p q : ΩA) → (f ^ φ) p p q ＝ (g ^ γ) p p q
  eq^ p q = (f ^ φ) p p q                                 ＝⟨ I ⟩
            conjugate φ (conjugate ε (ap₃ g p p q))       ＝⟨ II ⟩
            conjugate (ε ∙ φ) (ap₃ g p p q)               ＝⟨ III ⟩
            conjugate (γ ∙ sym γ ∙ ε ∙ φ) (ap₃ g p p q)   ＝⟨ IV ⟩
            conjugate (sym γ ∙ ε ∙ φ) ((g ^ γ) p p q)     ＝⟨ V ⟩
            (g ^ γ) p p q                                 ∎
   where
    ε : g a₀ a₀ a₀ ＝ f a₀ a₀ a₀
    ε = sym (eq a₀ a₀)

    I : conjugate φ (ap₃ f p p q) ＝ conjugate φ (conjugate ε (ap₃ g p p q))
    I = ap (conjugate φ) I'
     where
      I' : (ap₃ f) p p q ＝ conjugate ε ((ap₃ g) p p q)
      I' = eq-lift p q ∙ sym (conj-is-eq-cong {q = ε} {p = (ap₃ g) p p q})
       where
       eq-lift : {a b c d : A} (p₀ : a ＝ b) (p₁ : c ＝ d)
         → (ap₃ f) p₀ p₀ p₁
         ＝ eq-cong (sym (eq a c)) (sym (eq b d)) ((ap₃ g) p₀ p₀ p₁)
       eq-lift {a = a} {c = c} refl refl = sym (eq-cong-refl (sym (eq a c)))

    II : conjugate φ (conjugate ε (ap₃ g p p q))
       ＝ conjugate (ε ∙ φ) (ap₃ g p p q)
    II = conj-homo φ ε (ap₃ g p p q)

    III : conjugate (ε ∙ φ) (ap₃ g p p q)
        ＝ conjugate (γ ∙ sym γ ∙ ε ∙ φ) (ap₃ g p p q)
    III = ap₂ conjugate (path-simplify (ε ∙ φ) γ) refl
     where
      path-simplify : {a b c : A} (q₀ : b ＝ c) (p₀ : b ＝ a)
        → q₀ ＝ p₀ ∙ sym p₀ ∙ q₀
      path-simplify q₀ p₀ =
        q₀                 ＝⟨ sym (refl∙ q₀) ⟩
        refl ∙ q₀          ＝⟨ ap₂ _∙_ (sym-cancel-l p₀) refl ⟩
        (p₀ ∙ sym p₀) ∙ q₀ ＝⟨ ∙-assoc p₀ (sym p₀) q₀ ⟩
        p₀ ∙ (sym p₀ ∙ q₀) ∎

    IV : conjugate (γ ∙ sym γ ∙ ε ∙ φ) (ap₃ g p p q)
       ＝ conjugate (sym γ ∙ ε ∙ φ) (conjugate γ (ap₃ g p p q))
    IV = sym (conj-homo (sym γ ∙ ε ∙ φ) γ (ap₃ g p p q))

    V : conjugate (sym γ ∙ ε ∙ φ) ((g ^ γ) p p q) ＝ (g ^ γ) p p q
    V = conj-loop (sym γ ∙ ε ∙ φ) ((g ^ γ) p p q)

\end{code}

The other equations are lifted analoguously.

\begin{code}
 ap-minor : {a a' b b' c c' : A}
          → (h : A → A → A → A)
          → (p : a ＝ a') 
          → (q : b ＝ b') 
          → (r : c ＝ c') 
          → (ap₃ h p q r) ＝ (ap₃ (λ x y z → h y z x) r p q)
 ap-minor h refl refl refl = refl

 module lift₂ (f g : A → A → A → A)
              (φ   : f a₀ a₀ a₀ ＝ a₀)
              (γ   : g a₀ a₀ a₀ ＝ a₀)
              (eq  : (x y : A) → f x y x ＝ g x y x)
              where
  f' g' : A → A → A → A
  f' x y z = f y z x
  g' x y z = g y z x

  open lift₃ f' g' φ γ eq renaming (eq^ to eq^₃)

  eq^ : (p q : ΩA) → (f ^ φ) p q p ＝ (g ^ γ) p q p
  eq^ p q =
    (f ^ φ) p q p  ＝⟨ ap (conjugate φ) (ap-minor f p q p) ⟩
    (f' ^ φ) p p q ＝⟨ eq^₃ p q ⟩
    (g' ^ γ) p p q ＝⟨ sym (ap (conjugate γ) (ap-minor g p q p)) ⟩
    (g ^ γ) p q p  ∎

 module lift₁ (f g : A → A → A → A)
              (φ   : f a₀ a₀ a₀ ＝ a₀)
              (γ   : g a₀ a₀ a₀ ＝ a₀)
              (eq  : (x y : A) → f y x x ＝ g y x x)
              where
  f'' g'' : A → A → A → A
  f'' x y z = f y z x
  g'' x y z = g y z x

  open lift₂ f'' g'' φ γ eq renaming (eq^ to eq^₂)

  eq^ : (p q : ΩA) → (f ^ φ) q p p ＝ (g ^ γ) q p p
  eq^ p q =
    (f ^ φ)   q p p ＝⟨ ap (conjugate φ) (ap-minor f q p p) ⟩
    (f'' ^ φ) p q p ＝⟨ eq^₂ p q ⟩
    (g'' ^ γ) p q p ＝⟨ sym (ap (conjugate γ) (ap-minor g q p p)) ⟩
    (g ^ γ)   q p p  ∎
\end{code}

\begin{code}

 module majority (m   : A → A → A → A)
                 (eq₁ : (a b : A) → m b a a ＝ a)
                 (eq₂ : (a b : A) → m a b a ＝ a)
                 (eq₃ : (a b : A) → m a a b ＝ a)
         where

  μ : m a₀ a₀ a₀ ＝ a₀
  μ = eq₁ a₀ a₀

  m^ : ΩA → ΩA → ΩA → ΩA
  m^ = m ^ μ

  p₁ p₂ : A → A → A → A
  p₁ x _ _ = x
  p₂ _ x _ = x

  open lift₁ m p₂ μ refl eq₁ renaming (eq^ to eq^₁)
  open lift₂ m p₁ μ refl eq₂ renaming (eq^ to eq^₂)
  open lift₃ m p₁ μ refl eq₃ renaming (eq^ to eq^₃)

  is-set : (p : ΩA) → p ＝ refl
  is-set p =
    p                                   ＝⟨ sym I ⟩
    m^ refl p p                         ＝⟨ II ⟩
    m^ refl (p ∙ refl) (refl ∙ p)       ＝⟨ III ⟩
    m^ refl p refl ∙ m^ refl refl p     ＝⟨ IV ⟩
    refl          ∎
   where
    I : m^ refl p p ＝ p
    I = m^ refl p p            ＝⟨ eq^₁ p refl ⟩
        ap₃ p₂ refl p p        ＝⟨ p₂-duh p ⟩ 
        p ∎
     where 
      p₂-duh : {a a' b b' c c' : A}
              {q₁ : a ＝ a'} (q₂ : b ＝ b') {q₃ : c ＝ c'}
            → ap₃ p₂ q₁ q₂ q₃ ＝ q₂
      p₂-duh {q₁ = refl} refl {q₃ = refl} = refl

    II : m^ refl p p ＝ m^ refl (p ∙ refl) (refl ∙ p)
    II = ap₃ m^ refl (sym (∙refl p)) (sym (refl∙ p))

    III : m^ refl (p ∙ refl) (refl ∙ p) ＝ m^ refl p refl ∙ m^ refl refl p
    III = {!   !} -- m^-homomorphism

    IV : m^ refl p refl ∙ m^ refl refl p ＝ refl ∙ refl
    IV = ap₂ _∙_ {!   !} {!   !}
     
\end{code}