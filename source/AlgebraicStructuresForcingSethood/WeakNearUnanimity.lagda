Jakub Opršal, 15–24 March 2026.
TODO. UPDATE COMMENT

In this file, I want to explore another of Taylor's results from [1]. Namely,
the following lemma.

LEMMA (Taylor, 1977).
  Let X be a topological space with an n-ary operation t satysfying a
  non-trivial idempotent Maltsev condition, then π₁(X, x₀) is abelian for all
  x₀ ∈ X.

This file explores a ternary case of Taylor's operation that is sufficiently
general that simplifications, like those for majority and Maltsev operations,
would not apply here.

The equations are called *ternary weak near-unanimity*. Briefly, they can be
described as similar to majority, except that the three substitutions do not
necesarily return a projection, but just a same value depending on both
x and y, i.e.,

  w (x, x, y) = w (x, y, x) = w (y, x, x)

It should be also noted that [2] contains a simple special case of Taylor's
equation, namely the binary case.

The proof here follows roughly the line that we outlined in [Lemma 2.12, 3],
although I need to prove that certain 'subgrupoids' are normal, which is not
necessary in the case of topological algebras with strictly idempotent
operations. Curiosly, this fact was noted in Taylor's original paper [p. 515, 1].

[1] Walter Taylor. Varieties obeying homotopy laws. Can. J. Math., XXIX(3):
    498–527, 1977. https://doi.org/10.4153/CJM-1977-054-9.
[2] Tom de Jong. AlgebraicStructuresForcingSethood.CommutativeLoopSpaces.lagda,
    18 March 2026.
[3] Sebastian Meyer and Jakub Opršal. A topological proof of the Hell–Nešetřil
    dichotomy. https://arxiv.org/abs/2409.12627v2

WARNING!  I have used this exercise to learn some intricacies of Agda, so the
 code below is quite rough. I am leaving it as is, with proofs of symmetric
 cases being quite distict, for the record of my progress with Agda.

\begin{code}

{-# OPTIONS --safe --without-K #-}
module AlgebraicStructuresForcingSethood.WeakNearUnanimity where

open import MLTT.Universes
open import MLTT.Id
open import MLTT.Sigma
open import UF.Base using
  ( ap₂
  ; ap₃
  ; ap₃-∙
  ; ap₃-∙'
  ; ap₃-⁻¹
  ; refl-left-neutral
  ; ∙assoc
  ; ＝-congr
  ; ＝-congr-refl
  ; ＝-congr-∙
  ; ＝-congr-cancel
  ; ＝-congr-ap₃
  ; right-inverse
  )

private
 sym = _⁻¹

\end{code}

We will need to use that `ap f` is onto in the sense that every path

  q : f a a ＝ f a a

is of the form ap f q' q' q' for a suitably chosen q' : a ＝ a. This is done
similarly as what Tom de Jong did in the binary case [2]; I will use a
rectangle like this:

  f a a ==idem== a ==idem== f a a
    |            |            |
    q      =>    q'         f q' q'
    |            |            |
  f a a ==idem== a ==idem== f a a

where q' is chosen so that the left square commutes. The required equality
`q = ap f q' q'` follows from the fact that top and bottom simplify to refl.

\begin{code}

module ternary-idempotent
       {A    : 𝓤 ̇ }
       (f    : A → A → A → A)
       (idem : (x : A) → f x x x ＝ x)
       where

 idem^ : {a b : A}
       → (p : a ＝ b)
       → ＝-congr (idem a) (idem b) (ap₃ f p p p) ＝ p
 idem^ refl = ＝-congr-refl (idem _)

 ap₃-onto : {a : A}
          → (p : f a a a ＝ f a a a)
          → Σ p' ꞉ a ＝ a , ap₃ f p' p' p' ＝ p
 ap₃-onto {a} p = p' , hp
  where
   p' = ＝-congr (idem a) (idem a) p
   hp = ＝-congr-cancel (idem a) (idem a) (idem^ p')

\end{code}

Now, we get to the fun part! The key idea is that for any binary operation f,
elements of the form `ap f p refl` and `ap f refl q` commute. We apply this to
three different binary operations defined from `w`. Furthermore, we use
Taylor's identies to smuggle the last part through by equating it to an element
that commutes.

\begin{code}

module ternary-wnu (A    : 𝓤 ̇ )
                   (w    : A → A → A → A)
                   (idem : (a : A) → w a a a ＝ a)
                   (wnu₁ : (a b : A) → w a a b ＝ w b a a)
                   (wnu₂ : (a b : A) → w a a b ＝ w a b a)
                   where

 w' : {a : A} → a ＝ a → a ＝ a → a ＝ a → w a a a ＝ w a a a
 w' = ap₃ w

 base-1 : {a : A}
        → (p₀ p₁ p₂ : a ＝ a)
        → w' p₀ refl refl ∙ w' refl p₁ p₂ ＝ w' refl p₁ p₂ ∙ w' p₀ refl refl
 base-1 p₀ p₁ p₂ =
  w' p₀ refl refl ∙ w' refl p₁ p₂    ＝⟨ sym I ⟩
  w' p₀ p₁ p₂                        ＝⟨ II ⟩
  w' refl p₁ p₂ ∙ w' p₀ refl refl    ∎
   where
    I = ap₃-∙' w p₀ refl refl p₁ refl p₂ refl
               (sym refl-left-neutral) (sym refl-left-neutral)
    II = ap₃-∙' w refl p₀ p₁ refl p₂ refl (sym refl-left-neutral) refl refl

 base-2 : {a : A}
        → (p₀ p₁ p₂ : a ＝ a)
        → w' refl p₁ refl ∙ w' p₀ refl p₂ ＝ w' p₀ refl p₂ ∙ w' refl p₁ refl
 base-2 p₀ p₁ p₂ =
  w' refl p₁ refl ∙ w' p₀ refl p₂    ＝⟨ sym I ⟩
  w' p₀ p₁ p₂                        ＝⟨ II ⟩
  w' p₀ refl p₂ ∙ w' refl p₁ refl    ∎
   where
    I = ap₃-∙' w refl p₀ p₁ refl refl p₂
               (sym refl-left-neutral) refl (sym refl-left-neutral)
    II = ap₃-∙' w p₀ refl refl p₁ p₂ refl refl (sym refl-left-neutral) refl

 base-3 : {a : A}
        → (p₀ p₁ p₂ : a ＝ a)
        → w' refl refl p₂ ∙ w' p₀ p₁ refl ＝ w' p₀ p₁ refl ∙ w' refl refl p₂
 base-3 p₀ p₁ p₂ =
  w' refl refl p₂ ∙ w' p₀ p₁ refl    ＝⟨ sym I ⟩
  w' p₀ p₁ p₂                        ＝⟨ II ⟩
  w' p₀ p₁ refl ∙ w' refl refl p₂    ∎
   where
    I = ap₃-∙' w refl p₀ refl p₁ p₂ refl (sym refl-left-neutral)
               (sym refl-left-neutral) refl
    II = ap₃-∙' w p₀ refl p₁ refl refl p₂ refl refl (sym refl-left-neutral)

 open ternary-idempotent w idem

 wnu₁^ : {a a' b b' : A}
       → (p : a ＝ a') (q : b ＝ b')
       → ap₃ w p p q ∙ wnu₁ a' b' ＝ wnu₁ a b ∙ ap₃ w q p p
 wnu₁^ {a = a} {b = b} refl refl = refl-left-neutral

 wnu₂^ : {a a' b b' : A} (p : a ＝ b) (p' : a' ＝ b')
       →  ap₃ w p p' p ＝ ＝-congr (wnu₂ a a') (wnu₂ b b') (ap₃ w p p p')
 wnu₂^ refl refl = sym (＝-congr-refl (wnu₂ _ _))

 reduce₁ : {a : A} (q : a ＝ a)
         → Σ q' ꞉ a ＝ a , Σ q'' ꞉ a ＝ a , w' q q q ＝ w' refl q' q''
 reduce₁ {a} q = q' , q'' , eq
  where
   e = pr₁ (ap₃-onto (wnu₁ a a))
   he : w' e e e ＝ wnu₁ a a
   he = pr₂ (ap₃-onto (wnu₁ a a))

   eq' : w' q q refl ＝ w' refl (e ∙ q ∙ sym e) (e ∙ q ∙ sym e)
   eq' = w' q q refl                                ＝⟨ I ⟩
         w' q q refl ∙ (ε ∙ ε')                     ＝⟨ II ⟩
         (w' q q refl ∙ ε) ∙ ε'                     ＝⟨ III ⟩
         (ε ∙ w' refl q q) ∙ ε'                     ＝⟨ IV ⟩
         w' e e e ∙ w' refl q q ∙ sym (w' e e e)    ＝⟨ V ⟩
         w' e e e ∙ w' refl q q ∙ w' e' e' e'       ＝⟨ VI ⟩
         w' e (e ∙ q) (e ∙ q)   ∙ w' e' e' e'       ＝⟨ VII ⟩
         w' (e ∙ e') (e ∙ q ∙ e') (e ∙ q ∙ e')      ＝⟨ VIII ⟩
         w' refl  (e ∙ q ∙ e') (e ∙ q ∙ e')         ∎
    where
     ε = wnu₁ a a
     ε' = sym ε
     e' = sym e

     I = ap (λ p → w' q q refl ∙ p) (right-inverse ε)
     II = sym (∙assoc (w' q q refl) ε ε')
     III = ap (λ p → p ∙ ε') (wnu₁^ q refl)
     IV = ap (λ p → p ∙ w' refl q q ∙ sym p) (sym he)
     V = ap (λ p → w' e e e ∙ w' refl q q ∙ p) (sym (ap₃-⁻¹ w e e e))
     VI = ap (λ p → p ∙ w' e' e' e') (sym (ap₃-∙ w e refl e q e q))
     VII = sym (ap₃-∙ w e e' (e ∙ q) e' (e ∙ q) e')
     VIII = ap (λ p → w' p (e ∙ q ∙ e') (e ∙ q ∙ e')) (sym (right-inverse e))

   q' = e ∙ q ∙ sym e
   q'' = e ∙ q ∙ sym e ∙ q
   eq : w' q q q ＝ w' refl q' q''
   eq = w' q q q                             ＝⟨ I ⟩
        w' (q ∙ refl) (q ∙ refl) (refl ∙ q)  ＝⟨ II ⟩
        w' q q refl ∙ w' refl refl q         ＝⟨ III ⟩
        w' refl q' q' ∙ w' refl refl q       ＝⟨ IV ⟩
        w' refl (q' ∙ refl) (q' ∙ q)         ＝⟨ refl ⟩
        w' refl q' q''                       ∎
    where
     I = sym (ap₃ w' refl refl refl-left-neutral)
     II = ap₃-∙ w q refl q refl refl q
     III = ap (λ p → p ∙ w' refl refl q) eq'
     IV = sym (ap₃-∙ w refl refl q' refl q' q)

 commutes₁ : {a : A}
           → (p q : a ＝ a)
           → w' p refl refl ∙ w' q q q ＝ w' q q q ∙ w' p refl refl
 commutes₁ p q =
  w' p refl refl ∙ w' q q q                        ＝⟨ I ⟩
  w' p refl refl ∙ w' refl q' q''                  ＝⟨ base-1 p q' q'' ⟩
  w' refl q' q'' ∙ w' p refl refl                  ＝⟨ II ⟩
  w' q q q       ∙ w' p refl refl                  ∎
   where
    q'  = pr₁ (reduce₁ q)
    q'' = pr₁ (pr₂ (reduce₁ q))
    he : w' q q q ＝ w' refl q' q''
    he  = pr₂ (pr₂ (reduce₁ q))

    I = ap (λ - → w' p refl refl ∙ -) he
    II = sym (ap (λ - → - ∙ w' p refl refl) he)

 reduce₂ : {a : A} (q : a ＝ a)
         → Σ q' ꞉ a ＝ a , Σ q'' ꞉ a ＝ a , w' q q q ＝ w'  q' refl q''
 reduce₂ {a} q = q , q'' , hq
  where
   e : a ＝ a
   e = pr₁ (ap₃-onto (wnu₂ a a))

   he : wnu₂ a a ＝ ap₃ w e e e
   he = sym (pr₂ (ap₃-onto (wnu₂ a a)))

   q'' = q ∙ (＝-congr e e q)

   use-wnu₂ : ap₃ w refl q refl ＝ ap₃ w refl refl (＝-congr e e q)
   use-wnu₂ =
    ap₃ w refl q refl                                              ＝⟨ I ⟩
    ＝-congr (wnu₂ a a) (wnu₂ a a) (ap₃ w refl refl q)             ＝⟨ II ⟩
    ＝-congr (ap₃ w e e e) (ap₃ w e e e) (ap₃ w refl refl q)       ＝⟨ III ⟩
    ap₃ w (＝-congr e e refl) (＝-congr e e refl) (＝-congr e e q) ＝⟨ IV ⟩
    ap₃ w refl refl (＝-congr e e q)                               ∎
     where
      I = wnu₂^ refl q
      II = ap (λ - → ＝-congr - - (ap₃ w refl refl q)) he
      III = ＝-congr-ap₃ w e e refl e e refl e e q
      IV = ap₂ (λ - y → ap₃ w - - y) (＝-congr-refl e) refl

   hq : ap₃ w q q q ＝ ap₃ w q refl q''
   hq =
    ap₃ w q q q                                       ＝⟨ I ⟩
    ap₃ w q refl q ∙ ap₃ w refl q refl                ＝⟨ II ⟩
    ap₃ w q refl q ∙ ap₃ w refl refl (＝-congr e e q) ＝⟨ III ⟩
    ap₃ w q refl q''                                  ∎
     where
      I = ap₃-∙' w q refl refl q q refl refl (sym refl-left-neutral) refl
      II = ap (λ - → ap₃ w q refl q ∙ -) use-wnu₂
      III = sym (ap₃-∙' w q refl refl refl q (＝-congr e e q) refl refl refl)

 commutes₂ : {a : A}
           → (p q : a ＝ a)
           → w' refl p refl ∙ w' q q q ＝ w' q q q ∙ w' refl p refl
 commutes₂ p q =
  w' refl p refl ∙ w' q q q                   ＝⟨ I ⟩
  w' refl p refl ∙ w' q' refl q''             ＝⟨ base-2 q' p q'' ⟩
  w' q' refl q'' ∙ w' refl p refl             ＝⟨ II ⟩
  w' q q q       ∙ w' refl p refl             ∎
   where
    q'  = pr₁ (reduce₂ q)
    q'' = pr₁ (pr₂ (reduce₂ q))
    hq  = pr₂ (pr₂ (reduce₂ q))

    I = ap (w' refl p refl ∙_) hq
    II = ap (_∙ w' refl p refl) (sym hq)

 reduce₃ : {a : A} (q : a ＝ a)
         → Σ q' ꞉ a ＝ a , Σ q'' ꞉ a ＝ a , w' q q q ＝ w'  q' q'' refl
 reduce₃ {a} q = (＝-congr e e q) , (q ∙ (＝-congr e e q)) , hq
  where
   e : a ＝ a
   e = pr₁ (ap₃-onto (wnu₂ a a))

   he : wnu₂ a a ＝ ap₃ w e e e
   he = sym (pr₂ (ap₃-onto (wnu₂ a a)))

   use-wnu₂' : ap₃ w q refl q ＝ ap₃ w (＝-congr e e q) (＝-congr e e q) refl
   use-wnu₂' =
    ap₃ w q refl q                                             ＝⟨ wnu₂^ q refl ⟩
    ＝-congr (wnu₂ a a) (wnu₂ a a) (ap₃ w q q refl)             ＝⟨ II ⟩
    ＝-congr (ap₃ w e e e) (ap₃ w e e e) (ap₃ w q q refl)       ＝⟨ III ⟩
    ap₃ w (＝-congr e e q) (＝-congr e e q) (＝-congr e e refl) ＝⟨ IV ⟩
    ap₃ w (＝-congr e e q) (＝-congr e e q) refl                ∎
     where
      II = ap (λ - → ＝-congr - - (ap₃ w q q refl)) he
      III = ＝-congr-ap₃ w e e q e e q e e refl
      IV = ap₂ (λ x y → ap₃ w x x y) refl (＝-congr-refl e)

   hq : ap₃ w q q q ＝ ap₃ w (＝-congr e e q) (q ∙ ＝-congr e e q) refl
   hq =
    ap₃ w q q q                                                      ＝⟨ I ⟩
    ap₃ w refl q refl ∙ ap₃ w q refl q                               ＝⟨ II ⟩
    ap₃ w refl q refl ∙ ap₃ w (＝-congr e e q) (＝-congr e e q) refl ＝⟨ III ⟩
    ap₃ w (＝-congr e e q) (q ∙ (＝-congr e e q)) refl               ∎
     where
      I = ap₃-∙' w refl q q refl refl q (sym refl-left-neutral)
                 refl (sym refl-left-neutral)
      II = ap (λ - → ap₃ w refl q refl ∙ -) use-wnu₂'
      III = sym (ap₃-∙' w refl (＝-congr e e q) q (＝-congr e e q) refl refl
                        (sym refl-left-neutral) refl refl)

 commutes₃ : {a : A}
           → (p q : a ＝ a)
           → w' refl refl p ∙ w' q q q ＝ w' q q q ∙ w' refl refl p
 commutes₃ p q =
  w' refl refl p ∙ w' q q q        ＝⟨ ap (λ - → w' refl refl p ∙ -) hq ⟩
  w' refl refl p ∙ w' q' q'' refl  ＝⟨ base-3 q' q'' p ⟩
  w' q' q'' refl ∙ w' refl refl p  ＝⟨ ap (λ - → - ∙ w' refl refl p) (sym hq) ⟩
  w' q q q       ∙ w' refl refl p  ∎
   where
    q'  = pr₁ (reduce₃ q)
    q'' = pr₁ (pr₂ (reduce₃ q))
    hq  = pr₂ (pr₂ (reduce₃ q))

 ap₃-homo-w' : {a : A} {p q r : a ＝ a} {p' q' r' p'' q'' r'' : a ＝ a}
               (p^ : p ＝ p' ∙ p'') (q^ : q ＝ q' ∙ q'') (r^ : r ＝ r' ∙ r'')
             → w' p q r ＝ w' p' q' r' ∙ w' p'' q'' r''
 ap₃-homo-w' {a} {p} {q} {r} {p'} {q'} {r'} {p''} {q''} {r''} p^ q^ r^ =
  w' p q r                            ＝⟨ ap₃ w' p^ q^ r^ ⟩
  w' (p' ∙ p'') (q' ∙ q'') (r' ∙ r'') ＝⟨ ap₃-∙ w p' p'' q' q'' r' r'' ⟩
  w' p' q' r' ∙ w' p'' q'' r''        ∎

 image-of-w'-commutes : {a : A}
           → (p q : a ＝ a)
           → w' p p p ∙ w' q q q ＝ w' q q q ∙ w' p p p
 image-of-w'-commutes {a} p q =
  w' p p p ∙ w' q q q                                               ＝⟨ I ⟩
  w' refl p p ∙ w' p refl refl ∙ w' q q q                           ＝⟨ IIa ⟩
  w' refl p p ∙ (w' p refl refl ∙ w' q q q)                         ＝⟨ IIb ⟩
  w' refl p p ∙ (w' q q q ∙ w' p refl refl)                         ＝⟨ IIc ⟩
  w' refl p p ∙ w' q q q ∙ w' p refl refl                           ＝⟨ III ⟩
  w' refl refl p ∙ w' refl p refl ∙ w' q q q ∙ w' p refl refl       ＝⟨ IVa ⟩
  w' refl refl p ∙ (w' refl p refl ∙ w' q q q) ∙ w' p refl refl     ＝⟨ IVb ⟩
  w' refl refl p ∙ (w' q q q ∙ w' refl p refl) ∙ w' p refl refl     ＝⟨ IVc ⟩
  w' refl refl p ∙ w' q q q ∙ w' refl p refl ∙ w' p refl refl       ＝⟨ Va ⟩
  w' refl refl p ∙ w' q q q ∙ (w' refl p refl ∙ w' p refl refl)     ＝⟨ Vb ⟩
  w' refl refl p ∙ w' q q q ∙ w' p p refl                           ＝⟨ VI ⟩
  w' q q q ∙ w' refl refl p ∙ w' p p refl                           ＝⟨ VII ⟩
  w' q q q ∙ (w' refl refl p ∙ w' p p refl)                         ＝⟨ sym VIII ⟩
  w' q q q ∙ w' p p p                                               ∎
   where
    refl∙p : p ＝ refl ∙ p
    refl∙p = sym refl-left-neutral

    I = ap (_∙ w' q q q) (ap₃-homo-w' {p'' = p} refl∙p refl refl)
    IIa = ∙assoc (w' refl p p) (w' p refl refl) (w' q q q)
    IIb = ap (w' refl p p ∙_) (commutes₁ p q)
    IIc = sym (∙assoc (w' refl p p) (w' q q q) (w' p refl refl))
    III = ap (_∙ w' p refl refl)
             (ap (_∙ w' q q q) (ap₃-homo-w' {q'' = p} refl refl∙p refl))
    IVa = ap (_∙ w' p refl refl)
             (∙assoc (w' refl refl p) (w' refl p refl) (w' q q q))
    IVb = ap (λ - → w' refl refl p ∙ - ∙ w' p refl refl) (commutes₂ p q)
    IVc = ap (_∙ w' p refl refl)
             (sym (∙assoc (w' refl refl p) (w' q q q) (w' refl p refl)))
    Va = ∙assoc (w' refl refl p ∙ w' q q q)
                (w' refl p refl)
                (w' p refl refl)
    Vb = ap (w' refl refl p ∙ w' q q q ∙_)
            (sym (ap₃-homo-w' {p'' = p} refl∙p refl refl))
    VI = ap (_∙ w' p p refl) (commutes₃ p q)
    VII = ∙assoc (w' q q q) (w' refl refl p) (w' p p refl)
    VIII = ap (w' q q q ∙_)
              (ap₃-homo-w' {p'' = p} {q'' = p} refl∙p refl∙p refl)

 Ωw-idem : {a b : A} → (p : a ＝ b) → ＝-congr (idem a) (idem b) (ap₃ w p p p) ＝ p
 Ωw-idem refl = ＝-congr-refl (idem _)

 taylors-lemma : {a : A} → (p q : a ＝ a) → p ∙ q ＝ q ∙ p
 taylors-lemma {a} p q =
  p ∙ q                                            ＝⟨ sym (dissolve p q) ⟩
  ＝-congr (idem a) (idem a) (w' p p p ∙ w' q q q) ＝⟨ see-above ⟩
  ＝-congr (idem a) (idem a) (w' q q q ∙ w' p p p) ＝⟨ dissolve q p ⟩
  q ∙ p                                            ∎
   where
    dissolve : (p' q' : a ＝ a)
             → ＝-congr (idem a) (idem a) (w' p' p' p' ∙ w' q' q' q') ＝ p' ∙ q'
    dissolve p' q' =
       ＝-congr-∙ (idem a) (idem a) (idem a) (ap₃ w p' p' p') (ap₃ w q' q' q')
     ∙ ap₂ _∙_ (Ωw-idem p') (Ωw-idem q')

    see-above = ap (＝-congr (idem a) (idem a)) (image-of-w'-commutes p q)

\end{code}
