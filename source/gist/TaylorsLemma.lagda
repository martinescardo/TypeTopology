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

lap-∙ : {A : Type} {a b c : A} {p p' : a ＝ b} (q : b ＝ c)
      → (p ＝ p') → (p ∙ q ＝ p' ∙ q)
lap-∙ refl h = h

rap-∙ : {A : Type} {a b c : A} {p p' : b ＝ c} (q : a ＝ b)
      → (p ＝ p') → (q ∙ p ＝ q ∙ p')
rap-∙ q refl = refl

map-∙ : {A : Type} {a b c d : A}
      → (p : a ＝ b)
      → {q q' : b ＝ c}
      → (q ＝ q')
      → (r : c ＝ d)
      → (p ∙ q ∙ r ＝ p ∙ q' ∙ r)
map-∙ p refl refl = refl

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


ap₃-homo' : {A B C D : Type}
             (f : A → B → C → D)
             {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B} {c₁ c₂ c₃ : C}
             (pa : a₁ ＝ a₂) (qa : a₂ ＝ a₃) {ra : a₁ ＝ a₃}
             (pb : b₁ ＝ b₂) (qb : b₂ ＝ b₃) {rb : b₁ ＝ b₃}
             (pc : c₁ ＝ c₂) (qc : c₂ ＝ c₃) {rc : c₁ ＝ c₃}
             (a^ : ra ＝ pa ∙ qa) (b^ : rb ＝ pb ∙ qb) (c^ : rc ＝ pc ∙ qc)
           → (ap₃ f) ra rb rc ＝ (ap₃ f) pa pb pc ∙ (ap₃ f) qa qb qc
ap₃-homo' f pa qa pb qb pc qc a^ b^ c^ =
  ap₃ f _ _ _                         ＝⟨ ap₃ (ap₃ f) a^ b^ c^ ⟩
  ap₃ f (pa ∙ qa) (pb ∙ qb) (pc ∙ qc) ＝⟨ sym (ap₃-homo f pa qa pb qb pc qc) ⟩
  ap₃ f pa pb pc ∙ ap₃ f qa qb qc ∎

ap₃-sym : {A B C D : Type}
          (f : A → B → C → D)
          {a a' : A} {b b' : B} {c c' : C}
          (p : a ＝ a')
          (q : b ＝ b')
          (r : c ＝ c')
        → sym (ap₃ f p q r) ＝ ap₃ f (sym p) (sym q) (sym r)
ap₃-sym f refl refl refl = refl
       
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

eq-cong-ap : {A B C D : Type}
             (f : A → B → C → D)
             {a a' a'' a''' : A} {b b' b'' b''' : B} {c c' c'' c''' : C}
             (qa : a' ＝ a) (qa' : a'' ＝ a''') (pa : a' ＝ a'')
             (qb : b' ＝ b) (qb' : b'' ＝ b''') (pb : b' ＝ b'')
             (qc : c' ＝ c) (qc' : c'' ＝ c''') (pc : c' ＝ c'')
           → eq-cong (ap₃ f qa qb qc) (ap₃ f qa' qb' qc') (ap₃ f pa pb pc)
             ＝ ap₃ f (eq-cong qa qa' pa) (eq-cong qb qb' pb) (eq-cong qc qc' pc)
eq-cong-ap f refl refl pa refl refl pb refl refl pc = refl

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
    p' = sym (idem a) ∙ p ∙ idem a

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
  w^ p₀ refl refl ∙ w^ refl p₁ p₂    ＝⟨ sym I ⟩
  w^ p₀ p₁ p₂                        ＝⟨ II ⟩
  w^ refl p₁ p₂ ∙ w^ p₀ refl refl ∎
   where
    I = ap₃-homo' w p₀ refl refl p₁ refl p₂ refl (sym (refl∙ p₁)) (sym (refl∙ p₂))
    II = ap₃-homo' w refl p₀ p₁ refl p₂ refl (sym (refl∙ p₀)) refl refl

 base-2 : {a : A}
        → (p₀ p₁ p₂ : a ＝ a)
        → w^ refl p₁ refl ∙ w^ p₀ refl p₂ ＝ w^ p₀ refl p₂ ∙ w^ refl p₁ refl
 base-2 p₀ p₁ p₂ = 
  w^ refl p₁ refl ∙ w^ p₀ refl p₂    ＝⟨ sym I ⟩
  w^ p₀ p₁ p₂                        ＝⟨ II ⟩
  w^ p₀ refl p₂ ∙ w^ refl p₁ refl ∎
   where
    I = ap₃-homo' w refl p₀ p₁ refl refl p₂ (sym (refl∙ p₀)) refl (sym (refl∙ p₂))
    II = ap₃-homo' w p₀ refl refl p₁ p₂ refl refl (sym (refl∙ p₁)) refl

 base-3 : {a : A}
        → (p₀ p₁ p₂ : a ＝ a)
        → w^ refl refl p₂ ∙ w^ p₀ p₁ refl ＝ w^ p₀ p₁ refl ∙ w^ refl refl p₂
 base-3 p₀ p₁ p₂ = 
  w^ refl refl p₂ ∙ w^ p₀ p₁ refl    ＝⟨ sym I ⟩
  w^ p₀ p₁ p₂                        ＝⟨ II ⟩
  w^ p₀ p₁ refl ∙ w^ refl refl p₂ ∎
   where
    I = ap₃-homo' w refl p₀ refl p₁ p₂ refl (sym (refl∙ p₀)) (sym (refl∙ p₁)) refl
    II = ap₃-homo' w p₀ refl p₁ refl refl p₂ refl refl (sym (refl∙ p₂))
 
 open ternary-idempotent w idem 

 wnu₁^ : {a a' b b' : A}
       → (p : a ＝ a') (q : b ＝ b')
       → ap₃ w p p q ∙ wnu₁ a' b' ＝ wnu₁ a b ∙ ap₃ w q p p
 wnu₁^ {a = a} {b = b} refl refl = refl∙ (wnu₁ a b)
 
 reduce₁ : {a : A} (q : a ＝ a)
                  → Σ λ q' → Σ λ q'' → w^ q q q ＝ w^ refl q' q''
 reduce₁ {a} q = q' , q'' , eq
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
         w^ refl  (e ∙ q ∙ e') (e ∙ q ∙ e')         ∎
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
    q'  = pr₁ (reduce₁ q)
    q'' = pr₁ (pr₂ (reduce₁ q))
    he : w^ q q q ＝ w^ refl q' q''
    he  = pr₂ (pr₂ (reduce₁ q))

    I = ap (λ x → w^ p refl refl ∙ x) he
    II = sym (ap (λ x → x ∙ w^ p refl refl) he)

 wnu₂^ : {a a' b b' : A} (p : a ＝ b) (p' : a' ＝ b')
       →  ap₃ w p p' p ＝ eq-cong (wnu₂ a a') (wnu₂ b b') (ap₃ w p p p')
 wnu₂^ refl refl = sym (eq-cong-refl (wnu₂ _ _))


 reduce₂ : {a : A} (q : a ＝ a)
         → Σ λ q' → Σ λ q'' → ap₃ w q q q ＝ ap₃ w q' refl q''
 reduce₂ {a} q = q , q'' , hq
  where
   e : a ＝ a
   e = pr₁ (ap₃-onto (wnu₂ a a))

   he : wnu₂ a a ＝ ap₃ w e e e
   he = sym (pr₂ (ap₃-onto (wnu₂ a a)))

   q'' = q ∙ (eq-cong e e q)

   part-1 : ap₃ w refl q refl ＝ ap₃ w refl refl (eq-cong e e q)
   part-1 = 
    ap₃ w refl q refl                                           ＝⟨ wnu₂^ refl q ⟩
    eq-cong (wnu₂ a a) (wnu₂ a a) (ap₃ w refl refl q)           ＝⟨ II ⟩
    eq-cong (ap₃ w e e e) (ap₃ w e e e) (ap₃ w refl refl q)     ＝⟨ III ⟩
    ap₃ w (eq-cong e e refl) (eq-cong e e refl) (eq-cong e e q) ＝⟨ IV ⟩
    ap₃ w refl refl (eq-cong e e q) ∎
     where
      II = ap (λ x → eq-cong x x (ap₃ w refl refl q)) he
      III = eq-cong-ap w e e refl e e refl e e q
      IV = ap₂ (λ x y → ap₃ w x x y) (eq-cong-refl e) refl

   hq : ap₃ w q q q ＝ ap₃ w q refl q''
   hq = 
    ap₃ w q q q                                       ＝⟨ I ⟩ 
    ap₃ w q refl q ∙ ap₃ w refl q refl                ＝⟨ II ⟩ 
    ap₃ w q refl q ∙ ap₃ w refl refl (eq-cong e e q)  ＝⟨ III ⟩ 
    ap₃ w q refl q'' ∎
     where
      I = ap₃-homo' w q refl refl q q refl refl (sym (refl∙ q)) refl
      II = ap (λ x → ap₃ w q refl q ∙ x) part-1
      III = sym (ap₃-homo' w q refl refl refl q (eq-cong e e q) refl refl refl)
  
 commutes₂ : {a : A}
           → (p q : a ＝ a)
           → (w^ refl p refl ∙ w^ q q q ＝ w^ q q q ∙ w^ refl p refl)
 commutes₂ {a} p q = 
  w^ refl p refl ∙ w^ q q q                   ＝⟨ I ⟩ 
  w^ refl p refl ∙ w^ q' refl q''             ＝⟨ base-2 q' p q'' ⟩
  w^ q' refl q'' ∙ w^ refl p refl             ＝⟨ II ⟩
  w^ q q q       ∙ w^ refl p refl             ∎
   where
    q'  = pr₁ (reduce₂ q)
    q'' = pr₁ (pr₂ (reduce₂ q))
    hq  = pr₂ (pr₂ (reduce₂ q))

    I = rap-∙ (w^ refl p refl) hq
    II = lap-∙ (w^ refl p refl) (sym hq) 

 reduce₃ : {a : A} (q : a ＝ a)
         → Σ λ q' → Σ λ q'' → ap₃ w q q q ＝ ap₃ w q' q'' refl
 reduce₃ {a} q = (eq-cong e e q) , (q ∙ (eq-cong e e q)) , hq
  where
   e : a ＝ a
   e = pr₁ (ap₃-onto (wnu₂ a a))

   he : wnu₂ a a ＝ ap₃ w e e e
   he = sym (pr₂ (ap₃-onto (wnu₂ a a)))

   part-1 : ap₃ w q refl q ＝ ap₃ w (eq-cong e e q) (eq-cong e e q) refl
   part-1 = 
    ap₃ w q refl q                                           ＝⟨ wnu₂^ q refl ⟩
    eq-cong (wnu₂ a a) (wnu₂ a a) (ap₃ w q q refl)           ＝⟨ II ⟩
    eq-cong (ap₃ w e e e) (ap₃ w e e e) (ap₃ w q q refl)     ＝⟨ III ⟩
    ap₃ w (eq-cong e e q) (eq-cong e e q) (eq-cong e e refl) ＝⟨ IV ⟩
    ap₃ w (eq-cong e e q) (eq-cong e e q) refl ∎
     where
      II = ap (λ x → eq-cong x x (ap₃ w q q refl)) he
      III = eq-cong-ap w e e q e e q e e refl
      IV = ap₂ (λ x y → ap₃ w x x y) refl (eq-cong-refl e)

   hq : ap₃ w q q q ＝ ap₃ w (eq-cong e e q) (q ∙ eq-cong e e q) refl
   hq = 
    ap₃ w q q q                                                     ＝⟨ I ⟩ 
    ap₃ w refl q refl ∙ ap₃ w q refl q                              ＝⟨ II ⟩ 
    ap₃ w refl q refl ∙ ap₃ w (eq-cong e e q) (eq-cong e e q) refl  ＝⟨ III ⟩ 
    ap₃ w (eq-cong e e q) (q ∙ (eq-cong e e q)) refl ∎
     where
      I = ap₃-homo' w refl q q refl refl q (sym (refl∙ q)) refl (sym (refl∙ q))
      II = ap (λ x → ap₃ w refl q refl ∙ x) part-1
      III = sym (ap₃-homo' w refl (eq-cong e e q) q (eq-cong e e q) refl refl
                             (sym (refl∙ (eq-cong e e q))) refl refl)

 commutes₃ : {a : A}
           → (p q : a ＝ a)
           → (w^ refl refl p ∙ w^ q q q ＝ w^ q q q ∙ w^ refl refl p)
 commutes₃ p q =
  w^ refl refl p ∙ w^ q q q        ＝⟨ ap (λ x → w^ refl refl p ∙ x) hq ⟩  
  w^ refl refl p ∙ w^ q' q'' refl  ＝⟨ base-3 q' q'' p ⟩
  w^ q' q'' refl ∙ w^ refl refl p  ＝⟨ ap (λ x → x ∙ w^ refl refl p) (sym hq) ⟩
  w^ q q q       ∙ w^ refl refl p  ∎
   where
    q'  = pr₁ (reduce₃ q)
    q'' = pr₁ (pr₂ (reduce₃ q))
    hq  = pr₂ (pr₂ (reduce₃ q))

 ap₃-homo-w^ : {a : A} {p q r : a ＝ a} {p' q' r' p'' q'' r'' : a ＝ a}
               (p^ : p ＝ p' ∙ p'') (q^ : q ＝ q' ∙ q'') (r^ : r ＝ r' ∙ r'')
             → w^ p q r ＝ w^ p' q' r' ∙ w^ p'' q'' r''
 ap₃-homo-w^ {a} {p} {q} {r} {p'} {q'} {r'} {p''} {q''} {r''} p^ q^ r^ =
  w^ p q r                            ＝⟨ ap₃ w^ p^ q^ r^ ⟩ 
  w^ (p' ∙ p'') (q' ∙ q'') (r' ∙ r'') ＝⟨ sym (ap₃-homo w p' p'' q' q'' r' r'') ⟩
  w^ p' q' r' ∙ w^ p'' q'' r''        ∎

 pre-lemma : {a : A}
           → (p q : a ＝ a)
           → w^ p p p ∙ w^ q q q ＝ w^ q q q ∙ w^ p p p
 pre-lemma {a} p q =
  w^ p p p ∙ w^ q q q                                               ＝⟨ I ⟩
  w^ refl p p ∙ w^ p refl refl ∙ w^ q q q                           ＝⟨ IIa ⟩
  w^ refl p p ∙ (w^ p refl refl ∙ w^ q q q)                         ＝⟨ IIb ⟩
  w^ refl p p ∙ (w^ q q q ∙ w^ p refl refl)                         ＝⟨ IIc ⟩
  w^ refl p p ∙ w^ q q q ∙ w^ p refl refl                           ＝⟨ III ⟩
  w^ refl refl p ∙ w^ refl p refl ∙ w^ q q q ∙ w^ p refl refl       ＝⟨ IVa ⟩
  w^ refl refl p ∙ (w^ refl p refl ∙ w^ q q q) ∙ w^ p refl refl     ＝⟨ IVb ⟩
  w^ refl refl p ∙ (w^ q q q ∙ w^ refl p refl) ∙ w^ p refl refl     ＝⟨ IVc ⟩
  w^ refl refl p ∙ w^ q q q ∙ w^ refl p refl ∙ w^ p refl refl       ＝⟨ Va ⟩
  w^ refl refl p ∙ w^ q q q ∙ (w^ refl p refl ∙ w^ p refl refl)     ＝⟨ Vb ⟩
  w^ refl refl p ∙ w^ q q q ∙ w^ p p refl                           ＝⟨ VI ⟩
  w^ q q q ∙ w^ refl refl p ∙ w^ p p refl                           ＝⟨ VII ⟩
  w^ q q q ∙ (w^ refl refl p ∙ w^ p p refl)                         ＝⟨ sym VIII ⟩
  w^ q q q ∙ w^ p p p ∎
   where
    refl∙p : p ＝ refl ∙ p
    refl∙p = sym (refl∙ p)

    I = lap-∙ (w^ q q q) (ap₃-homo-w^ {p'' = p} refl∙p refl refl)
    IIa = sym (∙-assoc (w^ refl p p) (w^ p refl refl) (w^ q q q))
    IIb = rap-∙ (w^ refl p p) (commutes₁ p q)
    IIc = ∙-assoc (w^ refl p p) (w^ q q q) (w^ p refl refl)
    III = lap-∙ (w^ p refl refl)
                (lap-∙ (w^ q q q) (ap₃-homo-w^ {q'' = p} refl refl∙p refl))
    IVa = sym (lap-∙ (w^ p refl refl)
                     (∙-assoc (w^ refl refl p) (w^ refl p refl) (w^ q q q)))
    IVb = map-∙ (w^ refl refl p) (commutes₂ p q) (w^ p refl refl)
    IVc = lap-∙ (w^ p refl refl)
                (∙-assoc (w^ refl refl p) (w^ q q q) (w^ refl p refl))    
    Va = sym (∙-assoc (w^ refl refl p ∙ w^ q q q)
                      (w^ refl p refl)
                      (w^ p refl refl))
    Vb = sym (rap-∙ (w^ refl refl p ∙ w^ q q q)
                    (ap₃-homo-w^ {p'' = p} refl∙p refl refl))
    VI = lap-∙ (w^ p p refl) (commutes₃ p q)   
    VII = sym (∙-assoc (w^ q q q) (w^ refl refl p) (w^ p p refl))
    VIII = rap-∙ (w^ q q q) (ap₃-homo-w^ {p'' = p} {q'' = p} refl∙p refl∙p refl)

 Ωw-idem : {a b : A} → (p : a ＝ b) → eq-cong (idem a) (idem b) (ap₃ w p p p) ＝ p
 Ωw-idem refl = eq-cong-refl (idem _)

 taylors-lemma : {a : A} → (p q : a ＝ a) → p ∙ q ＝ q ∙ p
 taylors-lemma {a} p q =
  p ∙ q                                           ＝⟨ sym (dissolve p q) ⟩
  eq-cong (idem a) (idem a) (w^ p p p ∙ w^ q q q) ＝⟨ apply-pre-lemma ⟩
  eq-cong (idem a) (idem a) (w^ q q q ∙ w^ p p p) ＝⟨ dissolve q p ⟩
  q ∙ p                                           ∎
   where
    dissolve : (p' q' : a ＝ a)
             → eq-cong (idem a) (idem a) (w^ p' p' p' ∙ w^ q' q' q') ＝ p' ∙ q'
    dissolve p' q' = eq-cong-∙ {q = idem a} {q' = idem a} {q'' = idem a}
                               (w^ p' p' p') (w^ q' q' q')
                   ∙ ap₂ _∙_ (Ωw-idem p') (Ωw-idem q')
  
    apply-pre-lemma = ap (λ x → eq-cong (idem a) (idem a) x) (pre-lemma p q)

\end{code}
