Jakub Opršal, 15 Mar 2026.

I want to explore another of Taylor's result in this file. Namely the following
lemma.

LEMMA (Taylor, 1977).
  Let X be a topological space with an n-ary operation t satysfying a
  non-trivial idempotent Maltsev condition, then π₁(X, x₀) is Abelian for all
  x₀ ∈ X.

\begin{code}

{-# OPTIONS --safe --without-K #-}
module gist.TaylorsLemma where

open import MLTT.Spartan

sym : {A : Type} {a b : A} → (a ＝ b) → (b ＝ a)
sym = _⁻¹

sym-lcancel : {A : Type} {a b : A} (p : a ＝ b)
            → sym p ∙ p ＝ refl
sym-lcancel refl = refl

sym-rcancel : {A : Type} {a b : A} (p : a ＝ b)
            → p ∙ sym p ＝ refl
sym-rcancel refl = refl

∙-assoc : {A : Type} {a b c d : A} (p : a ＝ b) (q : b ＝ c) (r : c ＝ d)
        → p ∙ (q ∙ r) ＝ (p ∙ q) ∙ r
∙-assoc p refl refl = refl

refl∙ : {A : Type} {a b : A} (q : a ＝ b) → refl ∙ q ＝ q
refl∙ refl = refl

refl' : {A : Type} → (a : A) → a ＝ a
refl' a = refl

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

ap₃-sym : {A B C D : Type}
          (f : A → B → C → D)
          {a a' : A} {b b' : B} {c c' : C}
          (p : a ＝ a')
          (q : b ＝ b')
          (r : c ＝ c')
        → sym (ap₃ f p q r) ＝ ap₃ f (sym p) (sym q) (sym r)
ap₃-sym f refl refl refl = refl
       

_%_ : {A : Type} {a b : A}
    → (q : a ＝ b) → (p : a ＝ a) → b ＝ b
q % p = (sym q) ∙ p ∙ q

refl-% : {A : Type} {a : A} (p : a ＝ a) → refl % p ＝ p
refl-% p =
  sym refl ∙ p ∙ refl ＝⟨ refl ⟩
  sym refl ∙ p        ＝⟨ ap (λ x → x ∙ p) refl ⟩
  refl ∙ p            ＝⟨ refl∙ p ⟩
  p ∎

%-refl : {A : Type} {a : A} (p : a ＝ a) → p % refl ＝ refl
%-refl p =
  sym p ∙ refl ∙ p ＝⟨ refl ⟩
  sym p ∙ p        ＝⟨ sym-lcancel p ⟩
  refl ∎

\end{code}

The binary case is solved in Tom de Jong's [CommutativeLoopSpaces]. But I will
include the sketch here since this technique will be necessary for the ternary
case. Prove that ap₂ f is onto using the rectangle

  f a a ==idem== a ==idem== f a a
    |            |            |
    q      =>    q'         f q' q'
    |            |            |
  f a a ==idem== a ==idem== f a a

where q' is chosen so that the left square commutes, and the fact that top and
bottom simplifies to refl.

\begin{code}

module ternary-idempotent
       {A    : Type}
       (f    : A → A → A → A)
       (idem : (x : A) → f x x x ＝ x)
       where 

 idem^ : {a b : A}
       → (p : a ＝ b)
       → ap₃ f p p p ∙ idem b ＝ idem a ∙ p
 idem^ {a} refl = refl∙ (idem a) 

 ap₃-onto : {a : A}
         → (p : f a a a ＝ f a a a)
         → Σ λ p' → ap₃ f p' p' p' ＝ p
 ap₃-onto {a} p = p' , hp
   where
    p' : a ＝ a
    p' = (idem a) % p

    hp : ap₃ f p' p' p' ＝ p
    hp = ap₃ f p' p' p' ∙ refl          ＝⟨ I ⟩
         ap₃ f p' p' p' ∙ (ι ∙ ι')      ＝⟨ II ⟩
         (ap₃ f p' p' p' ∙ ι) ∙ ι'      ＝⟨ III ⟩
         (ι ∙ p')             ∙ ι'      ＝⟨ refl ⟩
         ι ∙ ((ι' ∙ p) ∙ ι) ∙ ι'        ＝⟨ IV ⟩
         (ι ∙ (ι' ∙ p)) ∙ ι ∙ ι'        ＝⟨ V ⟩
         (ι ∙ (ι' ∙ p)) ∙ (ι ∙ ι')      ＝⟨ VI ⟩
         ι ∙ (ι' ∙ p)                   ＝⟨ VII ⟩
         (ι ∙ ι') ∙ p                   ＝⟨ VIII ⟩
         refl ∙ p                       ＝⟨ refl∙ p ⟩
         p ∎
     where
      ι = idem a
      ι' = sym ι
      I = ap (λ q → ap₃ f p' p' p' ∙ q) (sym (sym-rcancel ι))
      II = ∙-assoc (ap₃ f p' p' p') ι ι'
      III = ap (λ q → q ∙ ι') (idem^ p')
      IV = ap (λ q → q ∙ ι') (∙-assoc ι (ι' ∙ p) ι)
      V = sym (∙-assoc (ι ∙ (ι' ∙ p)) ι ι')
      VI = ap (λ q → (ι ∙ (ι' ∙ p)) ∙ q) (sym-rcancel ι)
      VII = ∙-assoc ι ι' p
      VIII = ap (λ q → q ∙ p) (sym-rcancel ι)
   
\end{code}

Now, we get to the fun part! I will show Taylor's lemma for ternary idempotent
weak near-unanimity, which is an operation w : A → A → A → A, s.t.,

  w x x y = w x y x = w y x x.

\begin{code}

module ternary-wnu (A    : Type)
                   (w    : A → A → A → A)
                   (idem : (a : A) → w a a a ＝ a)
                   (wnu₁ : (a b : A) → w a a b ＝ w b a a)
                   (wnu₂ : (a b : A) → w a a b ＝ w a b a)
                   where

 w^ : {a : A} → a ＝ a → a ＝ a → a ＝ a → w a a a ＝ w a a a
 w^ = ap₃ w

 base-1 : {a : A}
        → (p₀ p₁ p₂ : a ＝ a)
        → w^ p₀ refl refl ∙ w^ refl p₁ p₂ ＝ w^ refl p₁ p₂ ∙ w^ p₀ refl refl
 base-1 p₀ p₁ p₂ =
  w^ p₀ refl refl ∙ w^ refl p₁ p₂         ＝⟨ I ⟩
  w^ (p₀ ∙ refl) (refl ∙ p₁) (refl ∙ p₂)  ＝⟨ ap₃ w^ refl (refl∙ p₁) (refl∙ p₂) ⟩
  w^ p₀ p₁ p₂                             ＝⟨ sym (ap₃ w^ (refl∙ p₀) refl refl) ⟩
  w^ (refl ∙ p₀) (p₁ ∙ refl) (p₂ ∙ refl)  ＝⟨ IV ⟩
  w^ refl p₁ p₂ ∙ w^ p₀ refl refl ∎
   where
    I = ap₃-homo w p₀ refl refl p₁ refl p₂
    IV = sym (ap₃-homo w refl p₀ p₁ refl p₂ refl)
 
 open ternary-idempotent w idem 

 wnu₁^ : {a a' b b' : A}
       → (p : a ＝ a') (q : b ＝ b')
       → ap₃ w p p q ∙ wnu₁ a' b' ＝ wnu₁ a b ∙ ap₃ w q p p
 wnu₁^ {a = a} {b = b} refl refl = refl∙ (wnu₁ a b)
 
 everything-is-^1 : {a : A} (q : a ＝ a)
                  → Σ λ q' → Σ λ q'' → w^ q q q ＝ w^ refl q' q''
 everything-is-^1 {a} q = q' , q'' , eq
  where
   e = pr₁ (ap₃-onto (wnu₁ a a))
   he : w^ e e e ＝ wnu₁ a a
   he = pr₂ (ap₃-onto (wnu₁ a a))

   eq' : w^ q q refl ＝ w^ refl (e ∙ q ∙ sym e) (e ∙ q ∙ sym e)
   eq' = w^ q q refl                                ＝⟨ I ⟩
        w^ q q refl ∙ (ε ∙ ε')                     ＝⟨ II ⟩
        (w^ q q refl ∙ ε) ∙ ε'                     ＝⟨ III ⟩
        (ε ∙ w^ refl q q) ∙ ε'                     ＝⟨ IV ⟩
        w^ e e e ∙ w^ refl q q ∙ sym (w^ e e e)    ＝⟨ V ⟩
        w^ e e e ∙ w^ refl q q ∙ w^ e' e' e'       ＝⟨ VI ⟩
        w^ e (e ∙ q) (e ∙ q)   ∙ w^ e' e' e'       ＝⟨ VII ⟩
        w^ (e ∙ e') (e ∙ q ∙ e') (e ∙ q ∙ e')      ＝⟨ VIII ⟩
        w^ refl  (e ∙ q ∙ e') (e ∙ q ∙ e')      ∎
    where
     ε = wnu₁ a a
     ε' = sym ε
     e' = sym e

     I = ap (λ p → w^ q q refl ∙ p) (sym (sym-rcancel ε))
     II = ∙-assoc (w^ q q refl) ε ε'
     III = ap (λ p → p ∙ ε') (wnu₁^ q refl)
     IV = ap (λ p → p ∙ w^ refl q q ∙ sym p) (sym he)
     V = ap (λ p → w^ e e e ∙ w^ refl q q ∙ p) (ap₃-sym w e e e)
     VI = ap (λ p → p ∙ w^ e' e' e') (ap₃-homo w e refl e q e q)
     VII = ap₃-homo w e e' (e ∙ q) e' (e ∙ q) e'
     VIII = ap (λ p → w^ p (e ∙ q ∙ e') (e ∙ q ∙ e')) (sym-rcancel e)

   q' = e ∙ q ∙ sym e
   q'' = e ∙ q ∙ sym e ∙ q
   eq : w^ q q q ＝ w^ refl q' q''
   eq = w^ q q q                             ＝⟨ I ⟩
        w^ (q ∙ refl) (q ∙ refl) (refl ∙ q)  ＝⟨ II ⟩
        w^ q q refl ∙ w^ refl refl q         ＝⟨ III ⟩
        w^ refl q' q' ∙ w^ refl refl q       ＝⟨ IV ⟩
        w^ refl (q' ∙ refl) (q' ∙ q)         ＝⟨ refl ⟩
        w^ refl q' q''    ∎
    where
     I = sym (ap₃ w^ refl refl (refl∙ q))
     II = sym (ap₃-homo w q refl q refl refl q)
     III = ap (λ p → p ∙ w^ refl refl q) eq'
     IV = ap₃-homo w refl refl q' refl q' q
 
 commutes₁ : {a : A}
           → (p q : a ＝ a)
           → (w^ p refl refl ∙ w^ q q q ＝ w^ q q q ∙ w^ p refl refl)
 commutes₁ p q = 
  w^ p refl refl ∙ w^ q q q                        ＝⟨ I ⟩ 
  w^ p refl refl ∙ w^ refl q' q''                  ＝⟨ base-1 p q' q'' ⟩ 
  w^ refl q' q'' ∙ w^ p refl refl                  ＝⟨ II ⟩
  w^ q q q       ∙ w^ p refl refl                  ∎
   where
    q'  = pr₁ (everything-is-^1 q)
    q'' = pr₁ (pr₂ (everything-is-^1 q))
    he : w^ q q q ＝ w^ refl q' q''
    he  = pr₂ (pr₂ (everything-is-^1 q))

    I = ap (λ x → w^ p refl refl ∙ x) he
    II = sym (ap (λ x → x ∙ w^ p refl refl) he)
 
 pre-lemma : {a : A}
           → (p q : a ＝ a)
           → w^ p p p ∙ w^ q q q ＝ w^ q q q ∙ w^ p p p
 pre-lemma p q = {!   !}

 taylors-lemma : {a : A} → (p q : a ＝ a) → p ∙ q ＝ q ∙ p
 taylors-lemma p q = {!   !}

\end{code}




BEWARE SOME OLD CODE BELOW!





