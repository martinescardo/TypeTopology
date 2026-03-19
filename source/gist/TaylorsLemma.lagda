Jakub Opršal, 15 Mar 2026.

I want to explore another of Taylor's result in this file. Namely the following
lemma.

LEMMA (Taylor, 1977).
  Let X be a topological space with an n-ary operation t satysfying a
  non-trivial idempotent Maltsev condition, then π₁(X, x₀) is Abelian for all
  x₀ ∈ X.

I will start with a simple example of a ternary weak near-unanimity:

    w(x, x, y) = w(x, y, x) = w(y, x, x)
    w(x, x, x) = x

As before, we use the same starting point. I will start developping a general
framework of ternary operations in this file.

\begin{code}

{-# OPTIONS --safe --without-K #-}
module gist.TaylorsLemma where

open import MLTT.Spartan

sym : {A : Type} {a b : A} → a ＝ b → b ＝ a
sym refl = refl

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

\end{code}

The binary case is solved in Tom de Jong's [CommutativeLoopSpaces]. But I will
include the sketch here since this technique will be necessary for the $n$-ary
case. Prove that ap₂ f is onto using the rectangle

  f a a ==idem== a ==idem== f a a
    |            |            |
    q      =>    q'         f q' q'
    |            |            |
  f a a ==idem== a ==idem== f a a

Where q' = q^idem. And the fact that top and bottom simplifies to refl.
Then use the usual Taylor's argument for binary operations

 f q refl ∙ f p p ＝ f q refl ∙ f refl p ∙ f p refl
                  ＝ f refl p ∙ f q refl ∙ symf ∙ f refl p ∙ sym symf
                  ＝ f refl p ∙ f q refl ∙ f symf' ∙ f refl p ∙ f (sym symf')
                  ＝ f refl p ∙ f q refl ∙ f refl p^symf'
                  ＝ f refl p ∙ f refl p^symf' ∙ f q refl
                  ＝ f refl p ∙ f refl p^symf' ∙ f q refl
                  ＝ f p p ∙ f q refl

And repeat for f refl q.

\begin{code}

module _ {D    : Type}
         (w    : D → D → D → D)
         (idem : (x : D) → w x x x ＝ x)
         (eq₀  : (x y : D) → w x x y ＝ w y x x) -- do I need eq₀ a a ＝ refl ??
         (eq₁  : (x y : D) → w y x x ＝ w x y x)
         (eq₂  : (x y : D) → w x y x ＝ w x x y)
         {a₀   : D}
         where 

 ΩD ΩDʷ : Type
 ΩD  = a₀ ＝ a₀
 ΩDʷ = w a₀ a₀ a₀ ＝ w a₀ a₀ a₀

 w' : ΩD → ΩD → ΩD → ΩDʷ
 w' = ap₃ w

 pre-commutes₀ : {p₀ p₁ p₂ : ΩD}
           → (w' refl p₁ p₂) ∙ (w' p₀ refl refl)
             ＝ (w' p₀ refl refl) ∙ (w' refl p₁ p₂)
 pre-commutes₀ {p₀} {p₁} {p₂} = left ∙ sym right
  where
   refl∙ : (p : a₀ ＝ a₀) → refl ∙ p ＝ p
   refl∙ p = (sym (∙-agrees-with-∙' refl p))

   left : (w' refl p₁ p₂) ∙ (w' p₀ refl refl) ＝ w' p₀ p₁ p₂
   left = ap₃-homo w refl p₀ p₁ refl p₂ refl
          ∙ ap₃ w' (refl∙ p₀) refl refl
   right : (w' p₀ refl refl) ∙ (w' refl p₁ p₂) ＝ w' p₀ p₁ p₂
   right = ap₃-homo w p₀ refl refl p₁ refl p₂
           ∙ ap₃ w' refl (refl∙ p₁) (refl∙ p₂)
  
 commutes₀ : {p₀ q₀ q₁ q₂ : ΩD}
           → (w' q₀ q₁ q₂) ∙ (w' p₀ refl refl)
             ＝ (w' p₀ refl refl) ∙ (w' q₀ q₁ q₂)
 commutes₀ {p₀} {q₀} {q₁} {q₂} = {!   !}
   -- x : Σ r₁ ∶ ΩD , Σ r₂ ∶ ΩD , w' q₀ q₁ q₂ ＝ w' refl r₁ r₂
   -- x = {!   !}
   
\end{code}


 pre-lemma : (p₀ p₁ p₂ : ΩD)
             (q₀ q₁ q₂ : ΩD)
           → (w' p₀ p₁ p₂) ∙ (w' q₀ q₁ q₂) ＝ (w' q₀ q₁ q₂) ∙ (w' p₀ p₁ p₂)
 pre-lemma p₀ p₁ p₂ q₀ q₁ q₂ = {!   !}

 taylors-lemma : (p : ΩD) → (q : ΩD) → p ∙ q ＝ q ∙ p
 taylors-lemma p q = (ap₂ _∙_ (sym (w'-idem p)) (sym (w'-idem q)))
                   ∙ (sym (eq-congr-∙ (w' p p p) (w' q q q)))
                   ∙ (ap (eq-congr (idem a₀) (idem a₀)) (pre-lemma p p p q q q))
                   ∙ eq-congr-∙ (w' q q q) (w' p p p)
                   ∙ (ap₂ _∙_ (w'-idem q) (w'-idem p))
  where
   w'-idem : {a b : D}
           → (p₀ : a ＝ b)
           → eq-congr (idem a) (idem b) ((ap₃ w) p₀ p₀ p₀) ＝ p₀
   w'-idem {a} refl = eq-congr-refl (idem a)
