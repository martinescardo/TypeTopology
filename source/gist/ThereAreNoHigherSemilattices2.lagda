Tom de Jong, 25—27 February 2026.

This is the result of my own attempt to understand David Wärn's Agda
formalization [1] which proves that any type equipped with a binary operation
that is associative, commutative and idempotent must be a set, cf. Martin
Escardo's version [2].

[1] David Wärn. https://dwarn.se/agda/Idem.html, 17 February 2026.
    (See also https://mathstodon.xyz/deck/@dwarn/116091515645003634.)

[2] Martin Escardo. gist.ThereAreNoHigherSemilattices.lagda, 23 February 2026.

Like [1] and [2], this file is completely self-contained with the basics taken
from [2].

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.ThereAreNoHigherSemilattices2 where

open import Agda.Primitive renaming (Set to Type)

infix 15 _＝_

data _＝_ {A : Type} (a : A) : A → Type where
 refl : a ＝ a

infixr 20 _∙_

_∙_ : {A : Type} {a b c : A} → a ＝ b → b ＝ c → a ＝ c
refl ∙ refl = refl

\end{code}

For readability, we introduce the standard combinators for equational reasoning.

\begin{code}

_＝⟨_⟩_ : {X : Type} (x : X) {y z : X} → x ＝ y → y ＝ z → x ＝ z
_ ＝⟨ p ⟩ q = p ∙ q

_∎ : {X : Type} (x : X) → x ＝ x
_∎ _ = refl

infix  1 _∎
infixr 0 _＝⟨_⟩_

sym : {A : Type} {a b : A} → a ＝ b → b ＝ a
sym refl = refl

ap : {A B : Type} {a b : A} (f : A → B) → a ＝ b → f a ＝ f b
ap f refl = refl

ap₂ : {A B C : Type} (f : A → B → C) {a₁ a₂ : A} {b₁ b₂ : B}
    → a₁ ＝ a₂
    → b₁ ＝ b₂
    → f a₁ b₁ ＝ f a₂ b₂
ap₂ f refl refl = refl

∙refl : {A : Type} {a b : A} (p : a ＝ b) → p ∙ refl ＝ p
∙refl refl = refl

refl∙ : {A : Type} {a b : A} (p : a ＝ b) → refl ∙ p ＝ p
refl∙ refl = refl

∙-cancel : {A : Type} {a b c : A} (p : a ＝ b) (q₁ q₂ : b ＝ c)
         → p ∙ q₁ ＝ p ∙ q₂ → q₁ ＝ q₂
∙-cancel refl refl q₂ h = refl      ＝⟨ h ⟩
                          refl ∙ q₂ ＝⟨ refl∙ q₂ ⟩
                          q₂        ∎

eq-congr : {A : Type} {a b x y : A} → a ＝ x → b ＝ y → a ＝ b → x ＝ y
eq-congr refl refl p = p

eq-congr-refl : {A : Type} {a x : A} (h : a ＝ x) → eq-congr h h refl ＝ refl
eq-congr-refl refl = refl

eq-congr-nat : {A : Type} {a b x y : A}
               (ha : a ＝ a) (hb : b ＝ b) (hax : a ＝ x) (hby : b ＝ y)
               (p : a ＝ b)
             → eq-congr hax hby (eq-congr ha hb p)
             ＝ eq-congr
                 (eq-congr hax hax ha)
                 (eq-congr hby hby hb)
                 (eq-congr hax hby p)
eq-congr-nat ha hb refl refl p = refl

\end{code}

A variation of the above that was not needed in [2]:

\begin{code}

eq-congr-nat' : {A : Type} {a b x y : A}
                (hab : a ＝ b) (hax : a ＝ x) (hby : b ＝ y)
                (p : a ＝ a)
              → eq-congr hby hby (eq-congr hab hab p)
                ＝ eq-congr
                    (eq-congr hax hby hab)
                    (eq-congr hax hby hab)
                    (eq-congr hax hax p)
eq-congr-nat' refl refl refl p = refl

eq-congr-∙ : {A : Type} {a b c x y z : A}
             {h₁ : a ＝ x} {h₂ : b ＝ y} {h₃ : c ＝ z}
             (p : a ＝ b) (q : b ＝ c)
           → eq-congr h₁ h₃ (p ∙ q) ＝ eq-congr h₁ h₂ p ∙ eq-congr h₂ h₃ q
eq-congr-∙ {h₁ = refl} {h₂ = refl} {h₃ = refl} p q = refl

congr-∙ : {A : Type} {a b u v x y : A}
          (l₁ : a ＝ u) (l₂ : u ＝ x) (r₁ : b ＝ v) (r₂ : v ＝ y) (p : a ＝ b)
        → eq-congr (l₁ ∙ l₂) (r₁ ∙ r₂) p ＝ eq-congr l₂ r₂ (eq-congr l₁ r₁ p)
congr-∙ refl refl refl refl p = refl

\end{code}

In what follows we will often take the first two arguments of eq-congr to be the
same which amounts to conjugating a loop as we show here for good measure.

\begin{code}

conjugate-loop : {A : Type} {a b : A} → a ＝ b → a ＝ a → b ＝ b
conjugate-loop p = eq-congr p p

conjugate-loop' : {A : Type} {a b : A} → a ＝ b → a ＝ a → b ＝ b
conjugate-loop' p q = sym p ∙ q ∙ p

conjugate-loops-agree : {A : Type} {a b x y : A} (p : a ＝ x) (q : a ＝ a)
                      → conjugate-loop p q ＝ conjugate-loop' p q
conjugate-loops-agree refl q =
 q               ＝⟨ sym (refl∙ q) ⟩
 refl ∙ q        ＝⟨ ap (refl ∙_) (sym (∙refl q)) ⟩
 refl ∙ q ∙ refl ∎

\end{code}

This completes our basic library.

We extract two criteria from [1] for the loop space to be trivial. The second
lemma is invoked at the very end.

\begin{code}

module pointed-type
        (A  : Type)
        (a₀ : A)
       where

 ΩA : Type
 ΩA = a₀ ＝ a₀

 trivial-Ω-endomap-criterion : (f : ΩA → ΩA)
                             → ((p : ΩA) → f (f p) ＝ f p)
                             → ((p : ΩA) → f p ∙ f p ＝ p)
                             → (p : ΩA) → p ＝ refl
 trivial-Ω-endomap-criterion f f-idem f-self-concat p = sym III
  where
   I = f p ∙ f p         ＝⟨ ap₂ _∙_ (sym (f-idem p)) (sym (f-idem p)) ⟩
       f (f p) ∙ f (f p) ＝⟨ f-self-concat (f p) ⟩
       f p               ＝⟨ sym (∙refl (f p)) ⟩
       f p ∙ refl        ∎

   II : f p ＝ refl
   II = ∙-cancel (f p) (f p) refl I

   III = refl        ＝⟨ refl ⟩
         refl ∙ refl ＝⟨ ap₂ _∙_ (sym II) (sym II) ⟩
         f p ∙ f p   ＝⟨ f-self-concat p ⟩
         p           ∎

\end{code}

The loop space is trivial if it can be equipped with a binary operation ⋆ such that
- it has an interchange law: (p ⋆ q) ∙ (r ⋆ s) ＝ (p ∙ r) ⋆ (q ∙ s);
- it is idempotent, commutative and associative.

\begin{code}

 trivial-Ω-multiplication-criterion
  : (_⋆_ : ΩA → ΩA → ΩA)
  → ((p q r s : ΩA) → (p ⋆ q) ∙ (r ⋆ s) ＝ (p ∙ r) ⋆ (q ∙ s))
  → ((p : ΩA) → p ⋆ p ＝ p)
  → ((p q : ΩA) → p ⋆ q ＝ q ⋆ p)
  → ((p q r : ΩA) → p ⋆ (q ⋆ r) ＝ (p ⋆ q) ⋆ r)
  → (p : ΩA) → p ＝ refl
 trivial-Ω-multiplication-criterion
  _⋆_ ⋆-interchange-∙ ⋆-idem ⋆-comm ⋆-assoc =
  trivial-Ω-endomap-criterion f f-idempotent f-self-concat-is-id
   where
    f : ΩA → ΩA
    f p = p ⋆ refl

    f-idempotent : (p : ΩA) → f (f p) ＝ f p
    f-idempotent p =
     f (f p)           ＝⟨ refl ⟩
     (f p) ⋆ refl      ＝⟨ refl ⟩
     (p ⋆ refl) ⋆ refl ＝⟨ sym (⋆-assoc p refl refl) ⟩
     p ⋆ (refl ⋆ refl) ＝⟨ ap (p ⋆_) (⋆-idem refl) ⟩
     p ⋆ refl          ＝⟨ refl ⟩
     f p               ∎

    f-self-concat-is-id : (p : ΩA) → f p ∙ f p ＝ p
    f-self-concat-is-id p =
     f p ∙ f p               ＝⟨ refl ⟩
     (p ⋆ refl) ∙ (p ⋆ refl) ＝⟨ I ⟩
     (p ⋆ refl) ∙ (refl ⋆ p) ＝⟨ ⋆-interchange-∙ p refl refl p ⟩
     (p ∙ refl) ⋆ (refl ∙ p) ＝⟨ ap₂ _⋆_ (∙refl p) (refl∙ p) ⟩
     p ⋆ p                   ＝⟨ ⋆-idem p ⟩
     p                       ∎
      where
       I = ap ((p ⋆ refl) ∙_) (⋆-comm p refl)

\end{code}

Now suppose we have a type A with a binary operation _*_. The operation induces
an action on paths that we denote by _＊_. Note that this ＊ is not quite a
binary operation in the sense that it is not of type X → X → X for some X.

\begin{code}

module _
        (A   : Type)
        (_*_ : A → A → A)
       where

 _＊_ : {a a' b b' : A} → a ＝ a' → b ＝ b' → a * b ＝ a' * b'
 p ＊ q = ap₂ _*_ p q

 ＊-interchange-∙ : {a a' b b' x y : A}
                    (p : a ＝ a') (q : b ＝ b') (r : a' ＝ x) (s : b' ＝ y)
                  → (p ＊ q) ∙ (r ＊ s) ＝ (p ∙ r) ＊ (q ∙ s)
 ＊-interchange-∙ refl refl refl refl = refl

\end{code}

We will need the following lemmas about applying ＊ when one of its arguments is
of the form "eq-congr u v (p ＊ q)". Of course, the point is to state these
lemmas in sufficient generality so that they follow trivially from path
induction.

\begin{code}

 ＊-eq-congr-left : {a a' b b' c c' : A}
                    (u : a * b ＝ c) (v : a' * b' ＝ c')
                    (p : a ＝ a') (q : b ＝ b') (r : c ＝ c')
                  → (eq-congr u v (p ＊ q)) ＊ r
                    ＝ eq-congr (u ＊ refl) (v ＊ refl) ((p ＊ q) ＊ r)
 ＊-eq-congr-left refl refl refl refl r = refl

 ＊-eq-congr-right : {a a' b b' c c' : A}
                    (u : a * b ＝ c) (v : a' * b' ＝ c')
                    (p : c ＝ c') (q : a ＝ a') (r : b ＝ b')
                  → p ＊ (eq-congr u v (q ＊ r))
                    ＝ eq-congr (refl ＊ u) (refl ＊ v) (p ＊ (q ＊ r))
 ＊-eq-congr-right refl refl p refl refl = refl

\end{code}

If * is commutative/associative, then so is ＊ up to eq-congr which is necessary
to make things type check as ＊ is a dependent function.

\begin{code}

 commutativity-of-* : Type
 commutativity-of-* = (a b : A) → a * b ＝ b * a

 associativity-of-* : Type
 associativity-of-* = (a b c : A) → (a * b) * c ＝ a * (b * c)

 ＊-comm : (*-comm : commutativity-of-*)
           {a a' b b' : A}
           (p : a ＝ a') (q : b ＝ b')
         → p ＊ q ＝ eq-congr (*-comm b a) (*-comm b' a') (q ＊ p)
 ＊-comm *-comm refl refl = sym (eq-congr-refl (*-comm _ _))

\end{code}

One may expect associativity to go from (p ＊ q) ＊ r to p ＊ (q ＊ r) in line
with associativity-of-*, but we go with the following to avoid having to invert
paths.

\begin{code}

 ＊-assoc
  : (*-assoc : associativity-of-*)
    {a a' b b' c c' : A}
    (p : a ＝ a') (q : b ＝ b') (r : c ＝ c')
  → p ＊ (q ＊ r) ＝ eq-congr (*-assoc a b c) (*-assoc a' b' c') ((p ＊ q) ＊ r)
 ＊-assoc *-assoc refl refl refl = sym (eq-congr-refl (*-assoc _ _ _))

\end{code}

If * is idempotent, then we can define an operation ＊' on paths from a to b.
This operation is again idempotent, and it is crucial here that we have not
restricted to loops yet, so that this has a (trivial) proof by path induction.

\begin{code}

 idempotentency-of-* : Type
 idempotentency-of-* = (a : A) → a * a ＝ a

 module idempotent
         (*-idem : idempotentency-of-*)
        where

  _＊'_ : {a b : A} → a ＝ b → a ＝ b → a ＝ b
  _＊'_ {a} {b} p q = eq-congr (*-idem a) (*-idem b) (p ＊ q)

  ＊'-idempotent : {a b : A} (p : a ＝ b) → p ＊' p ＝ p
  ＊'-idempotent refl = eq-congr-refl (*-idem _)

\end{code}

We now assume that A has a point a₀ and we restrict ＊' to loops on a₀, denoting
this operation by ＊Ω.

\begin{code}

  module pointed
          (a₀ : A)
         where

   open pointed-type A a₀

   private
    ι : a₀ * a₀ ＝ a₀
    ι = *-idem a₀

   _＊Ω_ : ΩA → ΩA → ΩA
   _＊Ω_ = _＊'_

   NB : (p q : ΩA) → p ＊Ω q ＝ conjugate-loop ι (p ＊ q)
   NB p q = refl

   ＊Ω-idempotent : (p : ΩA) → p ＊Ω p ＝ p
   ＊Ω-idempotent = ＊'-idempotent

   ＊Ω-refl : refl ＊Ω refl ＝ refl
   ＊Ω-refl = eq-congr-refl ι

   ＊Ω-interchange-∙ : (p q r s : ΩA)
                    → (p ＊Ω q) ∙ (r ＊Ω s) ＝ (p ∙ r) ＊Ω (q ∙ s)
   ＊Ω-interchange-∙ p q r s =
    (p ＊Ω q) ∙ (r ＊Ω s)                                 ＝⟨ refl ⟩
    conjugate-loop ι (p ＊ q) ∙ conjugate-loop ι (r ＊ s) ＝⟨ I    ⟩
    conjugate-loop ι ((p ＊ q) ∙ (r ＊ s))                ＝⟨ II   ⟩
    conjugate-loop ι ((p ∙ r) ＊ (q ∙ s))                 ＝⟨ refl ⟩
    (p ∙ r) ＊Ω (q ∙ s)                                   ∎
     where
      I  = sym (eq-congr-∙ (p ＊ q) (r ＊ s))
      II = ap (conjugate-loop ι) (＊-interchange-∙ p q r s)

\end{code}

Assuming that * is commutative, we wish to show that ＊Ω is commutative.
The strategy for this is to
  (1) prove that this holds up to conjugating by some appropriately choosen
      (i.e. reverse engineered) loop γ;
  (2) using idempotency of ＊Ω, prove that conjugating by γ is the identity;
  (3) conclude that ＊Ω is commutative (with no conjugation).

\begin{code}

   module _
           (*-comm : commutativity-of-*)
          where

    γ : a₀ ＝ a₀
    γ = conjugate-loop ι (*-comm a₀ a₀)

    ＊Ω-commutative-up-to-conjugation : (p q : ΩA)
                                      → p ＊Ω q ＝ conjugate-loop γ (q ＊Ω p)
    ＊Ω-commutative-up-to-conjugation p q =
     p ＊Ω q                                      ＝⟨ refl ⟩
     conjugate-loop ι (p ＊ q)                    ＝⟨ I    ⟩
     conjugate-loop ι (eq-congr γ₀ γ₀ (q ＊ p))   ＝⟨ refl ⟩
     eq-congr ι ι (eq-congr γ₀ γ₀ (q ＊ p))       ＝⟨ II   ⟩
     eq-congr (eq-congr ι ι γ₀)
              (eq-congr ι ι γ₀)
              (eq-congr ι ι (q ＊ p))             ＝⟨ refl ⟩
     eq-congr γ γ (eq-congr ι ι (q ＊ p))         ＝⟨ refl ⟩
     conjugate-loop γ (conjugate-loop ι (q ＊ p)) ＝⟨ refl ⟩
     conjugate-loop γ (q ＊Ω p)                   ∎
      where
       γ₀ : a₀ * a₀ ＝ a₀ * a₀
       γ₀ = *-comm a₀ a₀
       I  = ap (conjugate-loop ι) (＊-comm *-comm p q)
       II = eq-congr-nat γ₀ γ₀ ι ι (q ＊ p)

    conjugate-loop-comm-is-id : (p : ΩA) → conjugate-loop γ p ＝ p
    conjugate-loop-comm-is-id p =
     conjugate-loop γ p          ＝⟨ I  ⟩
      conjugate-loop γ (p ＊Ω p) ＝⟨ II ⟩
      p ＊Ω p                    ＝⟨ ＊Ω-idempotent p ⟩
      p                          ∎
       where
        I  = ap (conjugate-loop γ) (sym (＊Ω-idempotent p))
        II = sym (＊Ω-commutative-up-to-conjugation p p)

    ＊Ω-commutative : (p q : ΩA) → p ＊Ω q ＝ q ＊Ω p
    ＊Ω-commutative p q =
      p ＊Ω q                    ＝⟨ ＊Ω-commutative-up-to-conjugation p q ⟩
      conjugate-loop γ (q ＊Ω p) ＝⟨ conjugate-loop-comm-is-id (q ＊Ω p) ⟩
      (q ＊Ω p)                  ∎

\end{code}

Assuming that * is associative, we wish to show that ＊Ω is associative.
The strategy for this is like for commutativity above:
  (1) prove that ＊Ω is associative up to conjugating by some appropriately
      choosen (i.e. reverse engineered) loop α;
  (2) using idempotency of ＊Ω, prove that conjugating by α is the identity;
  (3) conclude that ＊Ω is commutative (with no conjugation).

Compared the proof for commutativity, there are two more steps here, namely to
show that (p ＊Ω q) ＊Ω r can be expressed as ((p ＊ q) ＊ r) up to conjugation,
and similarly for the other bracketing.

\begin{code}

   module _
           (*-assoc : associativity-of-*)
          where

    ι₁ : (a₀ * a₀) * a₀ ＝ a₀
    ι₁ = (ι ＊ refl) ∙ ι

    ι₂ : a₀ * (a₀ * a₀) ＝ a₀
    ι₂ = (refl ＊ ι) ∙ ι

    ＊Ω-is-＊-up-to-conjugation₁
     : (p q r : ΩA)
     → (p ＊Ω q) ＊Ω r ＝ conjugate-loop ι₁ ((p ＊ q) ＊ r)
    ＊Ω-is-＊-up-to-conjugation₁ p q r =
     (p ＊Ω q) ＊Ω r                                               ＝⟨ refl ⟩
     conjugate-loop ι (conjugate-loop ι (p ＊ q) ＊ r)             ＝⟨ I    ⟩
     conjugate-loop ι (conjugate-loop (ι ＊ refl) ((p ＊ q) ＊ r)) ＝⟨ II   ⟩
     conjugate-loop ((ι ＊ refl) ∙ ι) ((p ＊ q) ＊ r)              ＝⟨ refl ⟩
     conjugate-loop ι₁ ((p ＊ q) ＊ r)                             ∎
      where
       I  = ap (conjugate-loop ι) (＊-eq-congr-left ι ι p q r)
       II = sym (congr-∙ (ι ＊ refl) ι (ι ＊ refl) ι ((p ＊ q) ＊ r))

    ＊Ω-is-＊-up-to-conjugation₂
     : (p q r : ΩA)
     → p ＊Ω (q ＊Ω r) ＝ conjugate-loop ι₂ (p ＊ (q ＊ r))
    ＊Ω-is-＊-up-to-conjugation₂ p q r =
     p ＊Ω (q ＊Ω r)                                               ＝⟨ refl ⟩
     conjugate-loop ι (p ＊ conjugate-loop ι (q ＊ r))             ＝⟨ I    ⟩
     conjugate-loop ι (conjugate-loop (refl ＊ ι) (p ＊ (q ＊ r))) ＝⟨ II   ⟩
     conjugate-loop ((refl ＊ ι) ∙ ι) (p ＊ (q ＊ r))              ＝⟨ refl ⟩
     conjugate-loop ι₂ (p ＊ (q ＊ r))                             ∎
      where
       I  = ap (conjugate-loop ι) (＊-eq-congr-right ι ι p q r)
       II = sym (congr-∙ (refl ＊ ι) ι (refl ＊ ι) ι (p ＊ (q ＊ r)))

    α : a₀ ＝ a₀
    α = eq-congr ι₁ ι₂ (*-assoc a₀ a₀ a₀)

\end{code}

The rebracketing convention follows that of ＊-assoc.

\begin{code}

    ＊Ω-associative-up-to-conjugation
     : (p q r : ΩA)
     → p ＊Ω (q ＊Ω r) ＝ conjugate-loop α ((p ＊Ω q) ＊Ω r)
    ＊Ω-associative-up-to-conjugation p q r =
     p ＊Ω (q ＊Ω r)                                       ＝⟨ I    ⟩
     conjugate-loop ι₂ (p ＊ (q ＊ r))                     ＝⟨ II   ⟩
     conjugate-loop ι₂ (conjugate-loop α₀ ((p ＊ q) ＊ r)) ＝⟨ refl ⟩
     eq-congr ι₂ ι₂ (eq-congr α₀ α₀ ((p ＊ q) ＊ r))       ＝⟨ III  ⟩
     eq-congr (eq-congr ι₁ ι₂ α₀)
              (eq-congr ι₁ ι₂ α₀)
              (eq-congr ι₁ ι₁ ((p ＊ q) ＊ r))             ＝⟨ refl ⟩
     eq-congr α α (eq-congr ι₁ ι₁ ((p ＊ q) ＊ r))         ＝⟨ refl ⟩
     conjugate-loop α (conjugate-loop ι₁ ((p ＊ q) ＊ r))  ＝⟨ IV   ⟩
     conjugate-loop α ((p ＊Ω q) ＊Ω r)                    ∎
      where
       α₀ = *-assoc a₀ a₀ a₀
       I = ＊Ω-is-＊-up-to-conjugation₂ p q r
       II = ap (conjugate-loop ι₂) (＊-assoc *-assoc p q r)
       III = eq-congr-nat' α₀ ι₁ ι₂ ((p ＊ q) ＊ r)
       IV = ap (conjugate-loop α) (sym (＊Ω-is-＊-up-to-conjugation₁ p q r))

    conjugate-loop-assoc-is-id : (p : ΩA) → conjugate-loop α p ＝ p
    conjugate-loop-assoc-is-id p =
     conjugate-loop α p                 ＝⟨ I  ⟩
     conjugate-loop α (p ＊Ω p)         ＝⟨ II ⟩
     conjugate-loop α ((p ＊Ω p) ＊Ω p) ＝⟨ III ⟩
     p ＊Ω (p ＊Ω p)                    ＝⟨ IV ⟩
     p ＊Ω p                            ＝⟨ V ⟩
     p                                  ∎
      where
       I   = ap (conjugate-loop α) (sym (＊Ω-idempotent p))
       II  = ap (λ - → conjugate-loop α (- ＊Ω p)) (sym (＊Ω-idempotent p))
       III = sym (＊Ω-associative-up-to-conjugation p p p)
       IV  = ap (p ＊Ω_) (＊Ω-idempotent p)
       V   = ＊Ω-idempotent p

    ＊Ω-associative : (p q r : ΩA) → p ＊Ω (q ＊Ω r) ＝ (p ＊Ω q) ＊Ω r
    ＊Ω-associative p q r =
     p ＊Ω (q ＊Ω r)                    ＝⟨ I  ⟩
     conjugate-loop α ((p ＊Ω q) ＊Ω r) ＝⟨ II ⟩
     ((p ＊Ω q) ＊Ω r)                  ∎
      where
       I  = ＊Ω-associative-up-to-conjugation p q r
       II = conjugate-loop-assoc-is-id ((p ＊Ω q) ＊Ω r)

\end{code}

To recap: given an idempotent, commutative and associative operation * on a
pointed type A, we obtained an idempotent, commutative and associative operation
＊Ω on ΩA. Moreover, ＊Ω satisfies the interchange law, so that we can prove the
result claimed at the top by the trivial-Ω-multiplication-criterion lemma.

\begin{code}

 module _
         (a₀ : A)
         (*-idem  : idempotentency-of-*)
         (*-comm  : commutativity-of-*)
         (*-assoc : associativity-of-*)
        where

  open pointed-type A a₀
  open idempotent *-idem
  open pointed a₀

  ΩA-is-trivial : (p : ΩA) → p ＝ refl
  ΩA-is-trivial = trivial-Ω-multiplication-criterion
                   _＊Ω_
                   ＊Ω-interchange-∙
                   ＊Ω-idempotent
                   (＊Ω-commutative *-comm)
                   (＊Ω-associative *-assoc)

\end{code}