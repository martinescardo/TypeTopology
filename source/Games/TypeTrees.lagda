Martin Escardo, Paulo Oliva, 2-27 July 2021

We represent the moves of a history-dependent sequential game by a
dependent-type tree, collected in a type 𝑻.  This is either an empty
tree [] or else has a type X of initial moves at the root, and,
inductively, a family Xf of subtrees indexed by elements of X, which
is written X ∷ Xf. We refer to the family Xf as a forest. We let Xt
range over such trees.

 * Xt ranges over dependent-type trees.
 * Xf ranges over dependent-type forests.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module Games.TypeTrees
        {𝓤 : Universe}
       where

open import MonadOnTypes.Definition hiding (map)
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

data 𝑻 : 𝓤 ⁺ ̇ where
  []  : 𝑻
  _∷_ : (X : 𝓤 ̇ ) (Xf : X → 𝑻) → 𝑻

\end{code}

The type of full paths in a tree Xt, from the root to a leaf, is
inductively defined as follows:

\begin{code}

Path : 𝑻 → 𝓤 ̇
Path []       = 𝟙
Path (X ∷ Xf) = Σ x ꞉ X , Path (Xf x)

\end{code}

As discussed above, a play in a game is defined to be such a path.

The idea is that we choose a move x, and then, inductively, a path in
the subtree Xf x.

The variable xs ranges over paths, that is, elements of the type
Path Xt for a dependent-type-tree Xt.

\begin{code}

pattern ⟨⟩        = ⋆
pattern _::_ x xs = (x , xs)

path-head : {X : 𝓤 ̇ } {Xf : X → 𝑻} → Path (X ∷ Xf) → X
path-head (x :: xs) = x

path-tail : {X : 𝓤 ̇ } {Xf : X → 𝑻} ((x :: xs) : Path (X ∷ Xf)) → Path (Xf x)
path-tail (x :: xs) = xs

plength : {Xt : 𝑻} → Path Xt → ℕ
plength {[]}     ⟨⟩        = 0
plength {X ∷ Xf} (x :: xs) = succ (plength {Xf x} xs)

subpred : {X : 𝓤 ̇ } {R : 𝓣 ̇ } {Xf : X → 𝑻} → ((Σ x ꞉ X , Path (Xf x)) → R) → (x : X) → Path (Xf x) → R
subpred q x xs = q (x :: xs)

\end{code}

NB. An alternative inductive definition of Path is the following,
where, unfortunately, we get a higher type level, and so we won't use
it:

\begin{code}

data Path₁ : 𝑻 → 𝓤 ⁺ ̇ where
 []  : Path₁ []
 _∷_ : {X : 𝓤 ̇ } {Xf : X → 𝑻} (x : X) (xs : Path₁ (Xf x)) → Path₁ (X ∷ Xf)

\end{code}

Equip the internal nodes of a type tree with structure:

\begin{code}

structure : (𝓤 ̇ → 𝓥 ̇ ) → 𝑻 → 𝓤 ⊔ 𝓥 ̇
structure S []       = 𝟙
structure S (X ∷ Xf) = S X × ((x : X) → structure S (Xf x))

\end{code}

NB. An alternative inductive definition of structure is the following,
where, unfortunately, we get a higher type level, and so we won't use
it:

\begin{code}

data structure₁ (S : 𝓤 ̇ → 𝓥 ̇ ) : 𝑻 → 𝓤 ⁺ ⊔ 𝓥 ̇ where
 []  : structure₁ S []
 _∷_ : {X : 𝓤 ̇ } {Xf : X → 𝑻} → S X → ((x : X) → structure₁ S (Xf x)) → structure₁ S (X ∷ Xf)

structure-up : (S : 𝓤 ̇ → 𝓥 ̇ ) (Xt : 𝑻) → structure S Xt → structure₁ S Xt
structure-up S []      ⟨⟩         = []
structure-up S (X ∷ Xf) (s :: sf) = s ∷ (λ x → structure-up S (Xf x) (sf x))

structure-down : (S : 𝓤 ̇ → 𝓥 ̇ ) (Xt : 𝑻) → structure₁ S Xt → structure S Xt
structure-down S []      []        = ⟨⟩
structure-down S (X ∷ Xf) (s ∷ sf) = s :: (λ x → structure-down S (Xf x) (sf x))

\end{code}

Xt is hereditarily P if all its internal nodes satisfy P:

\begin{code}

_is-hereditarily_ : 𝑻 → (𝓤 ̇ → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
[]       is-hereditarily P = 𝟙
(X ∷ Xf) is-hereditarily P = P X × ((x : X) → Xf x is-hereditarily P)

being-hereditary-is-prop : Fun-Ext
                         → (P : 𝓤 ̇ → 𝓥 ̇ )
                         → ((X : 𝓤 ̇ ) → is-prop (P X))
                         → (Xt : 𝑻) → is-prop (Xt is-hereditarily P)
being-hereditary-is-prop fe P P-is-prop-valued [] = 𝟙-is-prop
being-hereditary-is-prop fe P P-is-prop-valued (X ∷ Xf) =
 ×-is-prop
  (P-is-prop-valued X)
  (Π-is-prop fe λ x → being-hereditary-is-prop fe P P-is-prop-valued (Xf x))

\end{code}

The sequence operator for monads is defined on lists, but here we
consider a version on paths of a tree instead:

\begin{code}

path-sequence : {ℓ : Universe → Universe} (𝓣 : Monad {ℓ})
                {Xt : 𝑻}
              → structure (functor 𝓣) Xt
              → functor 𝓣 (Path Xt)
path-sequence 𝓣 {[]}     ⟨⟩        = η 𝓣 ⟨⟩
path-sequence 𝓣 {X ∷ Xf} (t :: tf) = t ⊗[ 𝓣 ] (λ x → path-sequence 𝓣 {Xf x} (tf x))

\end{code}

The induction principle for 𝑻 is included for the sake of
completeness, but won't be used directly:

\begin{code}

𝑻-induction : (P : 𝑻 → 𝓥 ̇ )
            → P []
            → ((X : 𝓤 ̇ ) (Xf : X → 𝑻) → ((x : X) → P (Xf x)) → P (X ∷ Xf))
            → (Xt : 𝑻) → P Xt
𝑻-induction P b f = h
 where
  h : (Xt : 𝑻) → P Xt
  h []       = b
  h (X ∷ Xf) = f X Xf (λ x → h (Xf x))

𝑻-recursion : (A : 𝓥 ̇ )
            → A
            → ((X : 𝓤 ̇ ) → (X → 𝑻) → (X → A) → A)
            → 𝑻 → A
𝑻-recursion A = 𝑻-induction (λ _ → A)

𝑻-iteration : (A : 𝓥 ̇ )
            → A
            → ((X : 𝓤 ̇ ) → (X → A) → A)
            → 𝑻 → A
𝑻-iteration A a g = 𝑻-induction (λ _ → A) a (λ X Xf → g X)

\end{code}

Here are some examples for the sake of illustration:

\begin{code}

private

 Path' : 𝑻 → 𝓤 ̇
 Path' = 𝑻-iteration (𝓤 ̇ )  𝟙 (λ X F → Σ x ꞉ X , F x)

 Path'-[] : Path' [] ＝ 𝟙
 Path'-[] = refl

 Path'-∷ : (X : 𝓤 ̇ ) (Xf : X → 𝑻)
         → Path' (X ∷ Xf) ＝ (Σ x ꞉ X , Path' (Xf x))
 Path'-∷ X Xf = refl

 structure' : (S : 𝓤 ̇ → 𝓥 ̇ ) → 𝑻 → 𝓤 ⊔ 𝓥 ̇
 structure' {𝓥} S = 𝑻-iteration (𝓤 ⊔ 𝓥 ̇ ) 𝟙 (λ X F → S X × ((x : X) → F x))

 structure'-[] : (S : 𝓤 ̇ → 𝓥 ̇ )
               → structure' S [] ＝ 𝟙
 structure'-[] S = refl

 structure'-∷ : (S : 𝓤 ̇ → 𝓥 ̇ ) (X : 𝓤 ̇ ) (Xf : X → 𝑻)
              → structure' S (X ∷ Xf) ＝ S X × ((x : X) → structure' S (Xf x))
 structure'-∷ S X Xf = refl

\end{code}

Moved here 22 Oct 2025 from code from 8th October 2025 in the file
OptimalPlays, with a simplification on 29th October.

\begin{code}

open import MLTT.List

private
 ν : {X : 𝓤 ̇ }
     {Xf : X → 𝑻}
   → ((x : X) → List (Path (Xf x)))
   → (X → List (Path (X ∷ Xf)))
 ν f x = map (x ::_) (f x)

\end{code}

Notice that the above function ν transforms a dependent function into
a non-dependent one.

\begin{code}

list-of-all-paths : (Xt : 𝑻)
                    (lt : structure listed Xt)
                  → List (Path Xt)
list-of-all-paths [] ⟨⟩ = [ ⟨⟩ ]
list-of-all-paths (X ∷ Xf) ((xs , m) , lf) = List-ext (ν f) xs
 where
  f : (x : X) → List (Path (Xf x))
  f x = list-of-all-paths (Xf x) (lf x)

path-is-member-of-list-of-all-paths : (Xt : 𝑻)
                                      (lt : structure listed Xt)
                                      (xs : Path Xt)
                                    → member xs (list-of-all-paths Xt lt)
path-is-member-of-list-of-all-paths [] ⟨⟩ ⟨⟩ = in-head
path-is-member-of-list-of-all-paths (X ∷ Xf) ((ys , m) , lf) (x :: xs) = III
 where
  f : (x : X) → List (Path (Xf x))
  f x = list-of-all-paths (Xf x) (lf x)

  IH : member xs (f x)
  IH = path-is-member-of-list-of-all-paths (Xf x) (lf x) xs

  I : member  (x :: xs) (ν f x)
  I = member-of-map→ (x ::_) (f x) xs IH

  II : member (ν f x) (map (ν f) ys)
  II = member-of-map→ (ν f) ys x (m x)

  III : member (x :: xs) (List-ext (ν f) ys)
  III = member-of-concat→ (x :: xs) (map (ν f) ys) (ν f x) II I

\end{code}

We are not currently using pmap, but we keep it for the record:

\begin{code}

pmap  : {X : 𝓤 ̇ }
        {Xf : X → 𝑻}
      → ((x : X) → Path (Xf x))
      → List X
      → List (Path (X ∷ Xf))
pmap = dmap

\end{code}
