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

ap₃-homo : {A B C D : Type} (f : A → B → C → D)
           {a a' a'' : A} (p : a ＝ a') (p' : a' ＝ a'')
           {b b' b'' : B} (q : b ＝ b') (q' : b' ＝ b'')
           {c c' c'' : C} (r : c ＝ c') (r' : c' ＝ c'')
         → ap₃ f p q r ∙ ap₃ f p' q' r' ＝ ap₃ f (p ∙ p') (q ∙ q') (r ∙ r')
ap₃-homo f refl refl refl refl refl refl = refl

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

 conj-is-eq-cong :  {a b : A} → (q : a ＝ b) → (p : a ＝ a)
                 → conjugate q p ＝ eq-congr q q p
 conj-is-eq-cong refl p = refl

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

 ^homo : (f : A → A → A → A)
       → (φ : f a₀ a₀ a₀ ＝ a₀)
       → (p p' q q' r r' : ΩA)
       → (f ^ φ) p q r ∙ (f ^ φ) p' q' r' ＝ (f ^ φ) (p ∙ p') (q ∙ q') (r ∙ r')
 ^homo f φ p p' q q' r r' =
  (f ^ φ) p q r ∙ (f ^ φ) p' q' r'                                ＝⟨ refl ⟩
  conjugate φ (ap₃ f p q r) ∙ conjugate φ (ap₃ f p' q' r')        ＝⟨ I ⟩
  conjugate φ (ap₃ f p q r ∙ ap₃ f p' q' r')                      ＝⟨ II ⟩
  conjugate φ (ap₃ f (p ∙ p') (q ∙ q') (r ∙ r'))                  ＝⟨ refl ⟩
  (f ^ φ) (p ∙ p') (q ∙ q') (r ∙ r') ∎
   where
    I' : (p₀ p₁ : f a₀ a₀ a₀ ＝ f a₀ a₀ a₀)
      → conjugate φ p₀ ∙ conjugate φ p₁ ＝ conjugate φ (p₀ ∙ p₁)
    I' p₀ p₁ =
     conjugate φ p₀ ∙ conjugate φ p₁      ＝⟨ I ⟩
     eq-congr φ φ p₀ ∙ eq-congr φ φ p₁    ＝⟨ sym (eq-congr-∙ p₀ p₁) ⟩
     eq-congr φ φ (p₀ ∙ p₁)               ＝⟨ sym (conj-is-eq-cong φ (p₀ ∙ p₁)) ⟩
     conjugate φ (p₀ ∙ p₁) ∎
      where
       I = ap₂ _∙_ (conj-is-eq-cong φ p₀) (conj-is-eq-cong φ p₁)

    I = I' (ap₃ f p q r) (ap₃ f p' q' r') 

    II' : ap₃ f p q r ∙ ap₃ f p' q' r' ＝ ap₃ f (p ∙ p') (q ∙ q') (r ∙ r')
    II' = ap₃-homo f p p' q q' r r'

    II : conjugate φ (ap₃ f p q r ∙ ap₃ f p' q' r') ＝
      conjugate φ (ap₃ f (p ∙ p') (q ∙ q') (r ∙ r'))
    II =  ap (λ h → conjugate φ h) II'
     

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
      I' = eq-lift p q ∙ sym (conj-is-eq-cong ε (ap₃ g p p q))
       where
       eq-lift : {a b c d : A} (p₀ : a ＝ b) (p₁ : c ＝ d)
         → (ap₃ f) p₀ p₀ p₁
         ＝ eq-congr (sym (eq a c)) (sym (eq b d)) ((ap₃ g) p₀ p₀ p₁)
       eq-lift {a = a} {c = c} refl refl = sym (eq-congr-refl (sym (eq a c)))

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

  ap₃-p₁ : {a a' b b' c c' : A}
           (q₁ : a ＝ a') (q₂ : b ＝ b') (q₃ : c ＝ c')
         → ap₃ p₁ q₁ q₂ q₃ ＝ q₁
  ap₃-p₁ refl refl refl = refl

  ap₃-p₂ : {a a' b b' c c' : A}
           (q₁ : a ＝ a') (q₂ : b ＝ b') (q₃ : c ＝ c')
         → ap₃ p₂ q₁ q₂ q₃ ＝ q₂
  ap₃-p₂ refl refl refl = refl

  open lift₁ m p₂ μ refl eq₁ renaming (eq^ to eq^₁)
  open lift₂ m p₁ μ refl eq₂ renaming (eq^ to eq^₂)
  open lift₃ m p₁ μ refl eq₃ renaming (eq^ to eq^₃)

  is-set : (p : ΩA) → p ＝ refl
  is-set p =
    p                                   ＝⟨ sym (ap₃-p₂ refl p p) ⟩
    ap₃ p₂ refl p p                     ＝⟨ sym (eq^₁ p refl) ⟩ 
    m^ refl p p                         ＝⟨ II ⟩
    m^ refl (p ∙ refl) (refl ∙ p)       ＝⟨ III ⟩
    m^ refl p refl ∙ m^ refl refl p     ＝⟨ IV ⟩
    refl                                ∎
   where
    II  = ap₃ m^ refl (sym (∙refl p)) (sym (refl∙ p))
    III = sym (^homo m μ refl refl p refl refl p)
    IV  = ap₂ _∙_ IV' IV''
     where
      IV' = m^ refl p refl          ＝⟨ eq^₂ refl p ⟩
            (p₁ ^ refl) refl p refl ＝⟨ refl ⟩
            ap₃ p₁ refl p refl      ＝⟨ ap₃-p₁ refl p refl ⟩ 
            refl

      IV'' = m^ refl refl p          ＝⟨ eq^₃ refl p ⟩
             (p₁ ^ refl) refl refl p ＝⟨ refl ⟩
             ap₃ p₁ refl refl p      ＝⟨ ap₃-p₁ refl refl p ⟩ 
             refl
     
\end{code}