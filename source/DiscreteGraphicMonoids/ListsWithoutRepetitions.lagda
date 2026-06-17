Martin Escardo and Paulo Oliva, April 2024

The type of lists without repetitions, and various facts about it.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DiscreteGraphicMonoids.ListsWithoutRepetitions
        (fe : Fun-Ext)
       where

open import MLTT.List
            renaming (_∷_ to _•_ ;          -- typed as \bub
                      _++_ to _◦_ ;         -- typed as \buw
                      ++-assoc to ◦-assoc)
open import MLTT.Spartan
open import Naturals.Order
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Subsingletons

module _
         {X : 𝓤 ̇ }
         {{d' : is-discrete' X}}
       where

 private
  d : is-discrete X
  d = discrete'-gives-discrete

\end{code}

We first define a conditional `cons` operation, and then we use it to
define the function δ that deletes all occurrences of an element from a
list.

The function ccons can be made abstract, and this was useful during
the development of this file to get better goals, but it also
complicates some proofs for users of this module, so we are removing
it.

\begin{code}

 ccons : ({x} y : X) → is-decidable (x ＝ y) → List X → List X
 ccons y (inl e) ys = ys
 ccons y (inr u) ys = y • ys

 δ : X → List X → List X
 δ x []       = []
 δ x (y • ys) = ccons y (d x y) (δ x ys)

\end{code}

The following two facts are the specification of δ, together with the
equation δ x [] = []. We never use the definition of `ccons` other
than in the proof of these two facts.

\begin{code}

 module _ (x y : X) (zs : List X) where

  δ-＝ : x ＝ y → δ x (y • zs) ＝ δ x zs
  δ-＝ e =
   δ x (y • zs)             ＝⟨refl⟩
   ccons y (d x y) (δ x zs) ＝⟨ ap (λ - → ccons y - (δ x zs)) I ⟩
   ccons y (inl e) (δ x zs) ＝⟨refl⟩
   δ x zs                   ∎
    where
     I : d x y ＝ inl e
     I = discrete-inl d x y e

  δ-≠ : x ≠ y → δ x (y • zs) ＝ y • δ x zs
  δ-≠ u =
   δ x (y • zs)             ＝⟨refl⟩
   ccons y (d x y) (δ x zs) ＝⟨ ap (λ - → ccons y - (δ x zs)) I ⟩
   ccons y (inr u) (δ x zs) ＝⟨refl⟩
   y • δ x zs               ∎
    where
     I : d x y ＝ inr u
     I = discrete-inr fe d x y u

\end{code}

A particular case of `δ-＝` occurs more often in practice.

\begin{code}

 δ-same : (x : X) (ys : List X) → δ x (x • ys) ＝ δ x ys
 δ-same x ys = δ-＝ x x ys refl

\end{code}

Everything about δ should be proved only from this specification.

\begin{code}

 δ-swap : (x y : X) (zs : List X)
        → δ x (δ y zs) ＝ δ y (δ x zs)
 δ-swap x y []       = refl
 δ-swap x y (z • zs) = h (d x z) (d y z)
  where
   IH : δ x (δ y zs) ＝ δ y (δ x zs)
   IH = δ-swap x y zs

   h : is-decidable (x ＝ z)
     → is-decidable (y ＝ z)
     → δ x (δ y (z • zs)) ＝ δ y (δ x (z • zs))
   h (inl refl) (inl refl) = refl
   h (inl refl) (inr v) =
    δ x (δ y (x • zs)) ＝⟨ ap (δ x) (δ-≠ y x zs v) ⟩
    δ x (x • δ y zs)   ＝⟨ δ-same x (δ y zs) ⟩
    δ x (δ y zs)       ＝⟨ IH ⟩
    δ y (δ x zs)       ＝⟨ ap (δ y) ((δ-same x zs)⁻¹) ⟩
    δ y (δ x (x • zs)) ∎
   h (inr u) (inl refl) =
    δ x (δ y (y • zs)) ＝⟨ ap (δ x) (δ-same y zs) ⟩
    δ x (δ y zs)       ＝⟨ IH ⟩
    δ y (δ x zs)       ＝⟨ (δ-same y (δ x zs))⁻¹ ⟩
    δ y (y • δ x zs)   ＝⟨ ap (δ y) (δ-≠ x y zs u)⁻¹ ⟩
    δ y (δ x (y • zs)) ∎
   h (inr u) (inr v) =
    δ x (δ y (z • zs)) ＝⟨ ap (δ x) (δ-≠ y z zs v) ⟩
    δ x (z • δ y zs)   ＝⟨ δ-≠ x z (δ y zs) u ⟩
    z • δ x (δ y zs)   ＝⟨ ap (z •_) IH ⟩
    z • δ y (δ x zs)   ＝⟨ (δ-≠ y z (δ x zs) v)⁻¹ ⟩
    δ y (z • δ x zs)   ＝⟨ (ap (δ y) (δ-≠ x z zs u))⁻¹ ⟩
    δ y (δ x (z • zs)) ∎

 δ-idemp : (x : X) (ys : List X)
         → δ x (δ x ys) ＝ δ x ys
 δ-idemp x []       = refl
 δ-idemp x (y • ys) = h (d x y)
  where
   IH : δ x (δ x ys) ＝ δ x ys
   IH = δ-idemp x ys

   h : is-decidable (x ＝ y) → δ x (δ x (y • ys)) ＝ δ x (y • ys)
   h (inl refl) =
    δ x (δ x (x • ys)) ＝⟨ ap (δ x) (δ-same x ys) ⟩
    δ x (δ x ys)       ＝⟨ IH ⟩
    δ x ys             ＝⟨ (δ-same x ys)⁻¹ ⟩
    δ x (x • ys)       ∎
   h (inr u) =
    δ x (δ x (y • ys)) ＝⟨ ap (δ x) (δ-≠ x y ys u) ⟩
    δ x (y • δ x ys)   ＝⟨ δ-≠ x y (δ x ys) u ⟩
    y • δ x (δ x ys)   ＝⟨ ap (y •_) IH ⟩
    y • δ x ys         ＝⟨ (δ-≠ x y ys u)⁻¹ ⟩
    δ x (y • ys)       ∎

\end{code}

The following function ρ deletes repetitions from a list, so that a
list xs has no repetitions if and only if ρ xs ＝ xs (and we will take
this as our definition of no repetitions). The elements are deleted
"from left to right", so that any occurrence kept is the left-most
one.

\begin{code}

 ρ : List X → List X
 ρ []       = []
 ρ (x • xs) = x • δ x (ρ xs)

 ρ-is-non-empty : (xs : List X) → is-non-empty xs → is-non-empty (ρ xs)
 ρ-is-non-empty (x • xs) cons-is-non-empty = cons-is-non-empty

 δ-ρ-cancel : (x : X) (ys : List X)
            → δ x (ρ (x • ys)) ＝ δ x (ρ ys)
 δ-ρ-cancel x ys =
  δ x (ρ (x • ys))     ＝⟨refl⟩
  δ x (x • δ x (ρ ys)) ＝⟨ δ-same x (δ x (ρ ys)) ⟩
  δ x (δ x (ρ ys))     ＝⟨ δ-idemp x (ρ ys) ⟩
  δ x (ρ ys)           ∎

 δ-ρ-swap : (x : X) (ys : List X)
          → δ x (ρ ys) ＝ ρ (δ x ys)
 δ-ρ-swap x []       = refl
 δ-ρ-swap x (y • ys) = h (d x y)
  where
   IH : δ x (ρ ys) ＝ ρ (δ x ys)
   IH = δ-ρ-swap x ys

   h : is-decidable (x ＝ y) → δ x (ρ (y • ys)) ＝ ρ (δ x (y • ys))
   h (inl refl) =
    δ x (ρ (x • ys))     ＝⟨ δ-ρ-cancel x ys ⟩
    δ x (ρ ys)           ＝⟨ IH ⟩
    ρ (δ x ys)           ＝⟨ (ap ρ (δ-same x ys))⁻¹ ⟩
    ρ (δ x (x • ys))     ∎
   h (inr u) =
    δ x (ρ (y • ys))     ＝⟨refl⟩
    δ x (y • δ y (ρ ys)) ＝⟨ δ-≠ x y (δ y (ρ ys)) u ⟩
    y • δ x (δ y (ρ ys)) ＝⟨ ap (y •_) (δ-swap x y (ρ ys)) ⟩
    y • δ y (δ x (ρ ys)) ＝⟨ ap (λ - → y • δ y -) IH ⟩
    y • δ y (ρ (δ x ys)) ＝⟨refl⟩
    ρ (y • δ x ys)       ＝⟨ ap ρ ((δ-≠ x y ys u)⁻¹) ⟩
    ρ (δ x (y • ys))     ∎

\end{code}

It follows that an inner repeated deletion within ρ may be ignored, in
the sense that

 δ z (ρ (δ z xs)) ＝ δ z (ρ xs).

More generally, we have the following.

\begin{code}

 δ-inner : (z : X) (xs ys : List X)
         → δ z (ρ (δ z xs ◦ ys)) ＝ δ z (ρ (xs ◦ ys))
 δ-inner z []       ys = refl
 δ-inner z (x • xs) ys = h (d z x)
  where
   IH : δ z (ρ (δ z xs ◦ ys)) ＝ δ z (ρ (xs ◦ ys))
   IH = δ-inner z xs ys

   IH' : (z : X) (ys : List X) → δ z (ρ (δ z xs ◦ ys)) ＝ δ z (ρ (xs ◦ ys))
   IH' z ys = δ-inner z xs ys

   h : is-decidable (z ＝ x)
     → δ z (ρ (δ z (x • xs) ◦ ys)) ＝ δ z (ρ (x • xs ◦ ys))
   h (inl refl) =
    δ z (ρ (δ z (z • xs) ◦ ys)) ＝⟨ I ⟩
    δ z (ρ (δ z xs ◦ ys))       ＝⟨ IH ⟩
    δ z (ρ (xs ◦ ys))           ＝⟨ II ⟩
    δ z (δ z (ρ (xs ◦ ys)))     ＝⟨ III ⟩
    δ z (z • δ z (ρ (xs ◦ ys))) ＝⟨refl⟩
    δ z (ρ (z • xs ◦ ys))       ∎
     where
      I   = ap (λ - → δ x (ρ (- ◦ ys))) (δ-same x xs)
      II  = (δ-idemp z (ρ (xs ◦ ys)))⁻¹
      III = (δ-same z (δ z (ρ (xs ◦ ys))))⁻¹
   h (inr u) =
    δ z (ρ (δ z (x • xs) ◦ ys))     ＝⟨ I ⟩
    δ z (ρ (x • δ z xs ◦ ys))       ＝⟨refl⟩
    δ z (x • δ x (ρ (δ z xs ◦ ys))) ＝⟨ II ⟩
    x • δ z (δ x (ρ (δ z xs ◦ ys))) ＝⟨ III ⟩
    x • δ x (δ z (ρ (δ z xs ◦ ys))) ＝⟨ IV ⟩
    x • δ x (δ z (ρ (xs ◦ ys)))     ＝⟨ V ⟩
    x • δ z (δ x (ρ (xs ◦ ys)))     ＝⟨ VI ⟩
    δ z (x • δ x (ρ (xs ◦ ys)))     ＝⟨refl⟩
    δ z (ρ (x • xs ◦ ys))           ∎
     where
      I   = ap (λ - → δ z (ρ (- ◦ ys))) (δ-≠ z x xs u)
      II  = δ-≠ z x (δ x (ρ (δ z xs ◦ ys))) u
      III = ap (x •_) (δ-swap z x (ρ (δ z xs ◦ ys)))
      IV  = ap (λ - → x • δ x -) IH
      V   = ap (x •_) (δ-swap x z (ρ (xs ◦ ys)))
      VI  = (δ-≠ z x (δ x (ρ (xs ◦ ys))) u)⁻¹

 ρ-left : (xs ys : List X) → ρ (ρ xs ◦ ys) ＝ ρ (xs ◦ ys)
 ρ-left []       ys = refl
 ρ-left (x • xs) ys =
  ρ (ρ (x • xs) ◦ ys)           ＝⟨refl⟩
  x • δ x (ρ (δ x (ρ xs) ◦ ys)) ＝⟨ I ⟩
  x • δ x (ρ (ρ xs ◦ ys))       ＝⟨ II ⟩
  x • δ x (ρ (xs ◦ ys))         ＝⟨refl⟩
  ρ (x • xs ◦ ys)               ∎
   where
    IH : ρ (ρ xs ◦ ys) ＝ ρ (xs ◦ ys)
    IH = ρ-left xs ys

    I  = ap (x •_) (δ-inner x (ρ xs) ys)
    II = ap (λ - → x • δ x -) IH

 ρ-idemp : (xs : List X) → ρ (ρ xs) ＝ ρ xs
 ρ-idemp xs =
  ρ (ρ xs)      ＝⟨ ap ρ ([]-right-neutral (ρ xs)) ⟩
  ρ (ρ xs ◦ []) ＝⟨ ρ-left xs [] ⟩
  ρ (xs ◦ [])   ＝⟨ ap ρ (([]-right-neutral xs)⁻¹) ⟩
  ρ xs          ∎

 ρ-right : (xs ys : List X) → ρ (xs ◦ ρ ys) ＝ ρ (xs ◦ ys)
 ρ-right [] ys = ρ-idemp ys
 ρ-right (x • xs) ys =
  ρ (x • xs ◦ ρ ys)       ＝⟨refl⟩
  x • δ x (ρ (xs ◦ ρ ys)) ＝⟨ ap (λ - → x • δ x -) IH ⟩
  x • δ x (ρ (xs ◦ ys))   ＝⟨refl⟩
  ρ (x • xs ◦ ys) ∎
  where
   IH : ρ (xs ◦ ρ ys) ＝ ρ (xs ◦ ys)
   IH = ρ-right xs ys

 ρ-both : (xs ys : List X) → ρ (ρ xs ◦ ρ ys) ＝ ρ (xs ◦ ys)
 ρ-both xs ys =
  ρ (ρ xs ◦ ρ ys) ＝⟨ ρ-left xs (ρ ys) ⟩
  ρ (xs ◦ ρ ys)   ＝⟨ ρ-right xs ys ⟩
  ρ (xs ◦ ys)     ∎

 ρ-tail : (x : X) (xs : List X)
        → ρ (x • xs) ＝ x • xs
        → ρ xs ＝ xs
 ρ-tail x xs a =
  ρ xs           ＝⟨ ap ρ ((equal-tails a)⁻¹) ⟩
  ρ (δ x (ρ xs)) ＝⟨ (δ-ρ-swap x (ρ xs))⁻¹ ⟩
  δ x (ρ (ρ xs)) ＝⟨ ap (δ x) (ρ-idemp xs) ⟩
  δ x (ρ xs)     ＝⟨ equal-tails a ⟩
  xs             ∎
   where
    notice : x • δ x (ρ xs) ＝ x • xs
    notice = a

 has-no-reps : (xs : List X) → 𝓤 ̇
 has-no-reps xs = ρ xs ＝ xs

\end{code}

The following two technical lemmas, which are probably not very well
named, and are used to show that the monad of non-empty lists without
repetitions is affine, in another module.

\begin{code}

 δ-deletion-lemma : (y : X) (xs : List X)
                  → ¬ (Σ zs ꞉ List X , (δ y xs ＝ y • zs))
 δ-deletion-lemma y (x • xs) (zs , p) = h (d y x)
  where
   h : ¬ is-decidable (y ＝ x)
   h (inl refl) = δ-deletion-lemma y xs
                   (zs , (δ y xs       ＝⟨ (δ-same y xs)⁻¹ ⟩
                          δ y (y • xs) ＝⟨ p ⟩
                          y • zs       ∎))

   h (inr u) = u (equal-heads (y • zs       ＝⟨ p ⁻¹ ⟩
                               δ y (x • xs) ＝⟨ δ-≠ y x xs u ⟩
                               x • δ y xs   ∎))

 repetition-lemma : (x : X) (xs : List X)
                  → ¬ has-no-reps (x • x • xs)
 repetition-lemma x xs p = δ-deletion-lemma x (x • xs) (xs , III)
  where
   have-p : ρ (x • x • xs) ＝ x • x • xs
   have-p = p

   remark : x • δ x (x • δ x (ρ xs)) ＝ x • x • xs
   remark = p

   I : ρ (x • xs) ＝ x • xs
   I = ρ-tail x (x • xs) p

   II : δ x (ρ (x • xs)) ＝ x • xs
   II = equal-tails p

   III : δ x (x • xs) ＝ x • xs
   III = transport (λ - → δ x - ＝ x • xs) I II

\end{code}

We temporarily exit the above anonymous module to make the argument X
explicit.

\begin{code}

List⁻ : (X : 𝓤 ̇ ) {{_ : is-discrete' X}} → 𝓤 ̇
List⁻ X = Σ xs ꞉ List X , has-no-reps xs

\end{code}

And now we work again in an anonymous module with X implicit.

\begin{code}

module _ {X : 𝓤 ̇ }
         {{d' : is-discrete' X}}
       where

 private
  d : is-discrete X
  d = discrete'-gives-discrete

 η⁻ : X → List⁻ X
 η⁻ x = (x • []) , refl

 underlying-list : List⁻ X → List X
 underlying-list = pr₁

 instance
  canonical-map-List⁻-to-List : Canonical-Map (List⁻ X) (List X)
  ι {{canonical-map-List⁻-to-List}} = underlying-list

 underlying-list-has-no-reps : (𝔁𝓈 : List⁻ X) → has-no-reps (ι 𝔁𝓈)
 underlying-list-has-no-reps = pr₂

\end{code}

The symbol ⊙ can be typed a "\o." or "\odot".

\begin{code}

 _⊙_ : List X → List X → List X
 xs ⊙ ys = ρ (xs ◦ ys)

 ⊙-assoc : (a b c : List X) → a ⊙ (b ⊙ c) ＝ (a ⊙ b) ⊙ c
 ⊙-assoc a b c =
  a ⊙ (b ⊙ c)       ＝⟨refl⟩
  ρ (a ◦ ρ (b ◦ c)) ＝⟨ ρ-right a (b ◦ c) ⟩
  ρ (a ◦ (b ◦ c))   ＝⟨ ap ρ ((◦-assoc a b c)⁻¹) ⟩
  ρ ((a ◦ b) ◦ c)   ＝⟨ (ρ-left (a ◦ b) c)⁻¹ ⟩
  ρ (ρ (a ◦ b) ◦ c) ＝⟨refl⟩
  (a ⊙ b) ⊙ c       ∎

 _·_ : List⁻ X → List⁻ X → List⁻ X
 (xs , a) · (ys , b) =
   xs ⊙ ys ,
   (ρ (xs ⊙ ys)         ＝⟨ ap₂ (λ -₁ -₂ → ρ (-₁ ⊙ -₂)) (a ⁻¹) (b ⁻¹) ⟩
    ρ (ρ xs ⊙ ρ ys)     ＝⟨refl⟩
    ρ (ρ (ρ xs ◦ ρ ys)) ＝⟨ ρ-idemp (ρ xs ◦ ρ ys) ⟩
    ρ (ρ xs ◦ ρ ys)     ＝⟨ ρ-both xs ys ⟩
    ρ (xs ◦ ys)         ＝⟨refl⟩
    (xs ⊙ ys)           ∎)

 []⁻ : List⁻ X
 []⁻ = [] , refl

 List-is-discrete : is-discrete (List X)
 List-is-discrete [] [] = inl refl
 List-is-discrete [] (x • ys) = inr ([]-is-not-cons x ys)
 List-is-discrete (x • xs) [] = inr (≠-sym ([]-is-not-cons x xs))
 List-is-discrete (x • xs) (y • ys) with d x y
 ... | inl refl =
     Cases (List-is-discrete xs ys)
      (λ e → inl (ap (x •_) e))
      (λ ν → inr (λ e → ν (equal-tails e)))
 ... | inr ν = inr (λ e → ν (equal-heads e))

 having-no-reps-is-prop : (xs : List X) → is-prop (has-no-reps xs)
 having-no-reps-is-prop xs = discrete-types-are-sets List-is-discrete

 underlying-list-is-embedding : is-embedding underlying-list
 underlying-list-is-embedding = pr₁-is-embedding having-no-reps-is-prop

 to-List⁻-＝ : {𝔁𝓼 𝔂𝓼 : List⁻ X} → ι 𝔁𝓼 ＝ ι 𝔂𝓼 → 𝔁𝓼 ＝ 𝔂𝓼
 to-List⁻-＝ = to-subtype-＝ having-no-reps-is-prop

 ·-lemma : (x : X) (xs : List X) (a : has-no-reps (x • xs))
         → ((x • xs) , a) ＝[ List⁻ X ] (η⁻ x · (xs , ρ-tail x xs a))
 ·-lemma x xs a =
  to-List⁻-＝(x • xs         ＝⟨ ap (x •_) (equal-tails a)⁻¹ ⟩
              x • δ x (ρ xs) ＝⟨refl⟩
              ι (η⁻ x) ⊙ xs  ∎)
   where
    have-a : ρ (x • xs) ＝ x • xs
    have-a = a

    remark : x • δ x (ρ xs) ＝ x • xs
    remark = a

    b : ρ xs ＝ xs
    b = ρ-tail x xs a

    𝔁𝓼 : List⁻ X
    𝔁𝓼 = xs , b

 List⁻-is-discrete : is-discrete (List⁻ X)
 List⁻-is-discrete (xs , _) (ys , _) with List-is-discrete xs ys
 ... | inl e = inl (to-List⁻-＝ e)
 ... | inr u = inr (λ (e : (xs , _) ＝ (ys , _)) → u (ap ι e))

 instance
  List⁻-is-discrete' : is-discrete' (List⁻ X)
  List⁻-is-discrete' = discrete-gives-discrete' List⁻-is-discrete

 []⁻-left-neutral : (𝔁𝓼 : List⁻ X) → []⁻ · 𝔁𝓼 ＝ 𝔁𝓼
 []⁻-left-neutral 𝔁𝓼 =
  to-List⁻-＝
   (ι ([]⁻ · 𝔁𝓼) ＝⟨refl⟩
    ρ (ι 𝔁𝓼)     ＝⟨ underlying-list-has-no-reps 𝔁𝓼 ⟩
    ι 𝔁𝓼         ∎)

 []⁻-right-neutral : (𝔁𝓼 : List⁻ X) → 𝔁𝓼 · []⁻ ＝ 𝔁𝓼
 []⁻-right-neutral 𝔁𝓼 =
  to-List⁻-＝
   (ι (𝔁𝓼 · []⁻)  ＝⟨refl⟩
    ρ (ι 𝔁𝓼 ◦ []) ＝⟨ ap ρ (([]-right-neutral (ι 𝔁𝓼))⁻¹) ⟩
    ρ (ι 𝔁𝓼)      ＝⟨ underlying-list-has-no-reps 𝔁𝓼 ⟩
    ι 𝔁𝓼          ∎)

 ·-assoc : (𝔁𝓼 𝔂𝓼 𝔃𝓼 : List⁻ X) → 𝔁𝓼 · (𝔂𝓼 · 𝔃𝓼) ＝ (𝔁𝓼 · 𝔂𝓼) · 𝔃𝓼
 ·-assoc (xs , _) (ys , _) (zs , _) =
  to-subtype-＝ having-no-reps-is-prop (⊙-assoc xs ys zs)

 δ-◦ : (z : X) (xs ys : List X)
     → δ z (xs ◦ ys) ＝ δ z xs ◦ δ z ys
 δ-◦ z [] ys = refl
 δ-◦ z (x • xs) ys = h (d z x)
  where
   h : is-decidable (z ＝ x) → δ z (x • xs ◦ ys) ＝ δ z (x • xs) ◦ δ z ys
   h (inl refl) =
    δ z (z • xs ◦ ys)     ＝⟨ δ-same z (xs ◦ ys) ⟩
    δ z (xs ◦ ys)         ＝⟨ δ-◦ z xs ys ⟩
    δ z xs ◦ δ z ys       ＝⟨ ap (_◦ δ z ys) ((δ-same z xs)⁻¹) ⟩
    δ z (z • xs) ◦ δ z ys ∎
   h (inr u) =
    δ z (x • xs ◦ ys)     ＝⟨ δ-≠ z x (xs ◦ ys) u ⟩
    x • δ z (xs ◦ ys)     ＝⟨ ap (x •_) (δ-◦ z xs ys) ⟩
    x • (δ z xs ◦ δ z ys) ＝⟨refl⟩
    x • δ z xs ◦ δ z ys   ＝⟨ ap (_◦ δ z ys) ((δ-≠ z x xs u)⁻¹) ⟩
    δ z (x • xs) ◦ δ z ys ∎

 Δ : List X → List X → List X
 Δ [] xs       = xs
 Δ (y • ys) xs = δ y (Δ ys xs )

 δ-Δ-left : (z : X) (xs ys : List X)
          → δ z (Δ ys xs) ＝ Δ ys (δ z xs)
 δ-Δ-left z xs [] = refl
 δ-Δ-left z xs (x • ys) =
  δ z (Δ (x • ys) xs) ＝⟨refl⟩
  δ z (δ x (Δ ys xs)) ＝⟨ δ-swap z x (Δ ys xs) ⟩
  δ x (δ z (Δ ys xs)) ＝⟨ ap (δ x) (δ-Δ-left z xs ys) ⟩
  δ x (Δ ys (δ z xs)) ＝⟨refl⟩
  Δ (x • ys) (δ z xs) ∎

 []-Δ : (ys : List X) → Δ ys [] ＝ []
 []-Δ []       = refl
 []-Δ (y • ys) = ap (δ y) ([]-Δ ys)

 ρ-◦ : (xs ys : List X)
     → ρ (xs ◦ ys) ＝ ρ xs ◦ Δ xs (ρ ys)
 ρ-◦ [] ys = refl
 ρ-◦ (x • xs) ys =
  ρ (x • xs ◦ ys)                      ＝⟨refl⟩
  x • δ x (ρ (xs ◦ ys))                ＝⟨ ap (λ - → x • δ x -) (ρ-◦ xs ys) ⟩
  x • δ x (ρ xs ◦ Δ xs (ρ ys ))        ＝⟨ ap (x •_ ) (δ-◦ x (ρ xs) (Δ xs (ρ ys))) ⟩
  x • (δ x (ρ xs) ◦ δ x (Δ xs (ρ ys))) ＝⟨refl⟩
  ρ (x • xs) ◦ (Δ (x • xs) (ρ ys))     ∎

 ρ-all : (xs ys : List X) → Δ (xs ◦ ys) (ρ xs) ＝ []
 ρ-all [] ys = []-Δ ys
 ρ-all (x • xs) ys =
  Δ (x • xs ◦ ys) (ρ (x • xs))       ＝⟨refl⟩
  δ x (Δ (xs ◦ ys) (x • δ x (ρ xs))) ＝⟨ I ⟩
  Δ (xs ◦ ys) (δ x (x • δ x (ρ xs))) ＝⟨ II ⟩
  Δ (xs ◦ ys) (δ x (δ x (ρ xs)))     ＝⟨ III ⟩
  Δ (xs ◦ ys) (δ x (ρ xs))           ＝⟨ IV ⟩
  δ x (Δ (xs ◦ ys) (ρ xs))           ＝⟨ V ⟩
  δ x []                             ＝⟨refl⟩
  []                                 ∎
   where
    I   = δ-Δ-left x (x • δ x (ρ xs)) (xs ◦ ys)
    II  = ap (Δ (xs ◦ ys)) (δ-same x (δ x (ρ xs)))
    III = ap (Δ (xs ◦ ys)) (δ-idemp x (ρ xs))
    IV  = (δ-Δ-left x (ρ xs) (xs ◦ ys))⁻¹
    V   = ap (δ x) (ρ-all xs ys)

 δ-length : (z : X) (xs : List X)
          → length (δ z xs) ≤ length xs
 δ-length z []       = zero-least 0
 δ-length z (x • xs) = h (d z x)
  where
   IH : length (δ z xs) ≤ length xs
   IH = δ-length z xs

   h : is-decidable (z ＝ x) → length (δ z (x • xs)) ≤ succ (length xs)
   h (inl refl) = transport⁻¹ (_≤ succ (length xs)) I II
    where
     I : length (δ z (x • xs)) ＝ length (δ z xs)
     I = ap length (δ-same z xs)

     II : length (δ z xs) ≤ succ (length xs)
     II = ≤-trans (length (δ z xs)) (length xs) (succ (length xs))
           IH
           (≤-succ (length xs))
   h (inr u) = transport⁻¹ (_≤ succ (length xs)) I II
    where
     I : length (δ z (x • xs)) ＝ length (x • δ z xs)
     I = ap length (δ-≠ z x xs u)

     II : length (x • δ z xs) ≤ succ (length xs)
     II = succ-monotone (length (δ z xs)) (length xs) IH

module _ {X : 𝓤 ̇ }
         {Y : 𝓥 ̇ }
         {{X-is-discrete' : is-discrete' X}}
         {{Y-is-discrete' : is-discrete' Y}}
         (f : X → Y)
       where

 δ-map : (z : X) (xs : List X)
       → δ (f z) (map f (δ z xs)) ＝ δ (f z) (map f xs)
 δ-map z [] = refl
 δ-map z (x • xs) = h (discrete'-gives-discrete z x)
  where
   h : is-decidable (z ＝ x)
     → δ (f z) (map f (δ z (x • xs))) ＝ δ (f z) (map f (x • xs))
   h (inl refl) =
    δ (f z) (map f (δ z (z • xs))) ＝⟨ I ⟩
    δ (f z) (map f (δ z xs))       ＝⟨ IH ⟩
    δ (f z) (map f xs)             ＝⟨ II ⟩
    δ (f z) (f z • map f xs)       ＝⟨refl⟩
    δ (f z) (map f (z • xs))       ∎
     where
      I  = ap (λ - → δ (f z) (map f -)) (δ-same z xs)
      IH = δ-map z xs
      II = (δ-same (f z) (map f xs))⁻¹
   h (inr u) =
    δ (f z) (map f (δ z (x • xs))) ＝⟨ I ⟩
    δ (f z) (map f (x • δ z xs))   ＝⟨refl⟩
    δ (f z) (f x • map f (δ z xs)) ＝⟨ II ⟩
    δ (f z) (f x • map f xs)       ＝⟨refl⟩
    δ (f z) (map f (x • xs))       ∎
     where
      I = ap (λ - → δ (f z) (map f -)) (δ-≠ z x xs u)
      II = g (discrete'-gives-discrete (f z) (f x))
       where
        g : is-decidable (f z ＝ f x)
          → δ (f z) (f x • map f (δ z xs)) ＝ δ (f z) (f x • map f xs)
        g (inl e) =
         δ (f z) (f x • map f (δ z xs)) ＝⟨ III ⟩
         δ (f z) (map f (δ z xs))       ＝⟨ IV ⟩
         δ (f z) (map f xs)             ＝⟨ V ⟩
         δ (f z) (f x • map f xs)       ∎
          where
           III = δ-＝ (f z) (f x) (map f (δ z xs)) e
           IV  = δ-map z xs
           V   = (δ-＝ (f z) (f x) (map f xs) e)⁻¹
        g (inr u) =
         δ (f z) (f x • map f (δ z xs)) ＝⟨ III ⟩
         f x • δ (f z) (map f (δ z xs)) ＝⟨ IV ⟩
         f x • δ (f z) (map f xs)       ＝⟨ V ⟩
         δ (f z) (f x • map f xs)       ∎
          where
           III = δ-≠ (f z) (f x) (map f (δ z xs)) u
           IV  = ap (f x •_) (δ-map z xs)
           V   = (δ-≠ (f z) (f x) (map f xs) u)⁻¹

 ρ-map-lemma : (xs ys : List X)
             → ρ xs ＝ ρ ys
             → ρ (map f xs) ＝ ρ (map f ys)
 ρ-map-lemma = course-of-values-induction-on-length _ h
  where
   h : (xs : List X)
     → ((ys : List X)
            → length ys < length xs
            → (ys' : List X)
            → ρ ys ＝ ρ ys'
            → ρ (map f ys) ＝ ρ (map f ys'))
     → (ys : List X) → ρ xs ＝ ρ ys → ρ (map f xs) ＝ ρ (map f ys)
   h [] IH [] refl = refl
   h (x • xs) IH (y • ys) e = II
    where
     I = ρ (δ x xs) ＝⟨ (δ-ρ-swap x xs)⁻¹ ⟩
         δ x (ρ xs) ＝⟨ equal-tails e ⟩
         δ y (ρ ys) ＝⟨ ap (λ - → δ - (ρ ys)) (equal-heads (e ⁻¹)) ⟩
         δ x (ρ ys) ＝⟨ δ-ρ-swap x ys ⟩
         ρ (δ x ys) ∎

     II = ρ (map f (x • xs))                 ＝⟨refl⟩
          f x • δ (f x) (ρ (map f xs))       ＝⟨ III ⟩
          f x • ρ (δ (f x) (map f xs))       ＝⟨ IV ⟩
          f x • ρ (δ (f x) (map f (δ x xs))) ＝⟨ V ⟩
          f x • δ (f x) (ρ (map f (δ x xs))) ＝⟨ VI ⟩
          f x • δ (f x) (ρ (map f (δ x ys))) ＝⟨ VII ⟩
          f x • ρ (δ (f x) (map f (δ x ys))) ＝⟨ VIII ⟩
          f x • ρ (δ (f x) (map f ys))       ＝⟨ IX ⟩
          f x • δ (f x) (ρ (map f ys))       ＝⟨ XI ⟩
          f y • δ (f y) (ρ (map f ys))       ＝⟨refl⟩
          ρ (map f (y • ys))                 ∎
       where
        III  = ap (f x •_) (δ-ρ-swap (f x) (map f xs))
        IV   = ap (λ - → f x • ρ -) ((δ-map x xs)⁻¹)
        V    = ap (f x •_) ((δ-ρ-swap (f x) (map f (δ x xs)))⁻¹)
        VI   = ap (λ - → f x • δ (f x) -) (IH (δ x xs) (δ-length x xs) (δ x ys) I)
        VII  = ap (f x •_) (δ-ρ-swap (f x) (map f (δ x ys)))
        VIII = ap (λ - → f x • ρ -) (δ-map x ys)
        IX   = ap (f x •_) ((δ-ρ-swap (f x) (map f ys))⁻¹)
        XI   = ap (λ - → f - • δ (f -) (ρ (map f ys))) (equal-heads e)

 ρ-map : (xs : List X)
       → ρ (map f (ρ xs)) ＝ ρ (map f xs)
 ρ-map xs = ρ-map-lemma (ρ xs) xs (ρ-idemp xs)

\end{code}
