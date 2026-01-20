Martin Escardo, Paulo Oliva, March - April 2023

This file is mostly for efficiency. See the tests with tic-tac-toe at
the end of this file with the various possibilities offered here.

We incorporate alpha-beta pruning to our previous work on finite
history-dependent games using the selection and continuous monads (in
the module Games.FiniteHistoryDependent). But we do much more than
just that.

We define a minimax game (R , Xt, q , ϕt) to be a two-player game with
alternating quantifiers min and max (or max and min).

Part 0 (module minimax). In order to make the calculation of the
optimal outcome more efficient, we assume that the types of moves in
the game tree Xt are listed. Moreover, we add alpha-beta pruned
selection functions (indicated by the symbol "†").

Part 1. We transform such a minimax game G into a game G' so that we
can read off optimal *plays* of G from optimal *outcomes* of G'. This
requires the construction of a new R' and new quantifiers max' and
min', and a proof that optimal outcomes of G' give optimal plays of G.

Part 2. We then add α-β-pruning to G', to get a game G⋆, by further
modifying min' and max' to get min⋆ and max⋆, but keeping R' the
same. This requires a proof that G' and G⋆ have the same optimal
outcome. Of course, the α-β-pruning is done for the sake of
efficiency. By combining this with Part 1, we obtain an efficient way
to play the original game G optimally, with a proof of
correctness. (But we don't prove efficiency theorems.)

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

open import MLTT.Spartan hiding (J)

\end{code}

Part 0.

We now define standard minimax games.

\begin{code}

module Games.alpha-beta
        {𝓤 𝓥 : Universe}
        (R : 𝓤 ̇ )
        (_<_ : R → R → 𝓥 ̇ )
        (δ : (r s : R) → is-decidable (r < s))
      where

open import Games.FiniteHistoryDependent {𝓤} public
open import Games.TypeTrees {𝓤} public
open import MLTT.Athenian
open import MonadOnTypes.J
open import MonadOnTypes.K
open import UF.FunExt

_≥_ : R → R → 𝓥 ̇
r ≥ s = ¬ (r < s)

module _ (Xt : 𝑻)
         (Xt-is-listed⁺ : structure listed⁺ Xt)
         (q : Path Xt → R)
       where

 module minimax where

\end{code}

After defining min and max, we can define the given game G from the
data given as module parameter.

\begin{code}

  max min : R → R → R

  max r s = Cases (δ r s)
             (λ (_ : r < s) → s)
             (λ (_ : r ≥ s) → r)

  min r s = Cases (δ s r)
             (λ (_ : s < r) → s)
             (λ (_ : s ≥ r) → r)

\end{code}

Part 0.

\begin{code}

  open K-definitions R

  Min Max : {X : 𝓤 ̇ } → listed⁺ X → K X
  Min (x₀ , xs , _) p = foldr (λ x → min (p x)) (p x₀) xs
  Max (x₀ , xs , _) p = foldr (λ x → max (p x)) (p x₀) xs

\end{code}

TODO. Min and Max do indeed compute the minimum and maximum
value of p : X → R (easy).

We now label the give tree Xt with the above Min and Max quantifiers
in an alternating fashion.

\begin{code}

  minmax maxmin : (Xt : 𝑻)
                → structure listed⁺ Xt
                → 𝓚 R Xt
  minmax []       ⟨⟩        = ⟨⟩
  minmax (X ∷ Xf) (ℓ :: ss) = Min ℓ :: (λ x → maxmin (Xf x) (ss x))

  maxmin []       ⟨⟩        = ⟨⟩
  maxmin (X ∷ Xf) (ℓ :: ss) = Max ℓ :: (λ x → minmax (Xf x) (ss x))

  G-quantifiers : 𝓚 R Xt
  G-quantifiers = maxmin Xt Xt-is-listed⁺

\end{code}

And with this we get the desired maxmin game.

\begin{code}

  G : Game R
  G = game Xt q G-quantifiers

\end{code}

Now we define selection functions for this game.

\begin{code}

  argmin argmax : {X : 𝓤 ̇ } → (X → R) → X → X → X

  argmin p x m = Cases (δ (p x) (p m))
                  (λ (_ : p x < p m) → x)
                  (λ (_ : p x ≥ p m) → m)

  argmax p x m = Cases (δ (p m) (p x))
                  (λ (_ : p m < p x) → x)
                  (λ (_ : p m ≥ p x) → m)

  open J-definitions R

  ArgMin ArgMax : {X : 𝓤 ̇ } → listed⁺ X → J X
  ArgMin (x₀ , xs , _) p = foldr (argmin p) x₀ xs
  ArgMax (x₀ , xs , _) p = foldr (argmax p) x₀ xs

\end{code}

TODO. Show that ArgMin and ArgMax are selection functions for the
quantifiers Min and Max (easy).

We now label the give tree Xt with the above ArgMin and ArgMax
quantifiers in an alternating fashion.

\begin{code}

  argminmax argmaxmin : (Xt : 𝑻)
                      → structure listed⁺ Xt
                      → 𝓙 R Xt
  argminmax []       ⟨⟩        = ⟨⟩
  argminmax (X ∷ Xf) (ℓ :: ℓf) = ArgMin ℓ :: (λ x → argmaxmin (Xf x) (ℓf x))

  argmaxmin []       ⟨⟩        = ⟨⟩
  argmaxmin (X ∷ Xf) (ℓ :: ℓf) = ArgMax ℓ :: (λ x → argminmax (Xf x) (ℓf x))

  G-selections : 𝓙 R Xt
  G-selections = argmaxmin Xt Xt-is-listed⁺

  G-strategy : Strategy R Xt
  G-strategy = selection-strategy R G-selections q

  optimal-play : Path Xt
  optimal-play = sequenceᴶ R G-selections q

\end{code}

TODO. Prove the lemma formulated as an assumption of the above module (easy).

\begin{code}

  module _ (lemma : _Attains_ R G-selections G-quantifiers)
           (fe : Fun-Ext)
         where

   theorem : is-optimal R G (selection-strategy R G-selections q)
   theorem = Selection-Strategy-Theorem R fe G G-selections lemma

   corollary : q optimal-play ＝ optimal-outcome R G
   corollary = selection-strategy-corollary R fe G G-selections lemma

\end{code}

We now define monadic selection functions with α-β-pruning, using the
reader monad, to speed-up the computation of the optimal play.

\begin{code}

  module _ (fe : Fun-Ext) (-∞ ∞ : R) where

   open import MonadOnTypes.Reader
   open import MonadOnTypes.Construction

   AB = R × R

   T : 𝓤 ̇ → 𝓤 ̇
   T = functor (Reader AB)

   private
    NB : T R ＝ (AB → R)
    NB = refl

   q† : Path Xt → T R
   q† xs (α , β) = q xs

   ArgMin† ArgMax† : {X : 𝓤 ̇ } → List X → X → R → (X → T R) → T X

   ArgMin† []       x₀ r p (α , β) = x₀
   ArgMin† (x ∷ xs) x₀ r p (α , β) =
    case p x (α , β) of
     λ (s : R)
       → Cases (δ α s)
          (λ (_ : α < s)
                → Cases (δ s r)
                   (λ (_ : s < r) → ArgMin† xs x  s p (α , min β s))
                   (λ (_ : s ≥ r) → ArgMin† xs x₀ r p (α , β)))
          (λ (_ : α ≥ s)
                → x)

   ArgMax† []       x₀ r p (α , β) = x₀
   ArgMax† (x ∷ xs) x₀ r p (α , β) =
    case p x (α , β) of
     λ (s : R)
       → Cases (δ s β)
          (λ (_ : s < β)
                → Cases (δ r s)
                   (λ (_ : r < s) → ArgMax† xs x  s p (max α s , β))
                   (λ (_ : r ≥ s) → ArgMax† xs x₀ r p (α , β)))
          (λ (_ : s ≥ β)
                → x)

   𝓡 : Algebra (Reader AB) R
   𝓡 = record {
         structure-map = λ (t : AB → R) → t (-∞ , ∞) ;
         aunit = λ _ → refl ;
         aassoc = λ _ → refl
       }

   ρ : T R → R
   ρ = structure-map 𝓡

   open import Games.FiniteHistoryDependentMonadic
                fe
                (Reader AB)
                {𝓤}
                {𝓤}
                R
                𝓡

   argminmax† argmaxmin† : (Xt : 𝑻)
                         → structure listed⁺ Xt
                         → 𝓙𝓣 Xt
   argminmax† []       ⟨⟩                    = ⟨⟩
   argminmax† (X ∷ Xf) ((x₀ , xs , _) :: ss) =
    (λ (p : X → T R) → ArgMin† xs x₀ (ρ (p x₀)) p)
    :: (λ x → argmaxmin† (Xf x) (ss x))

   argmaxmin† []       ⟨⟩                    = ⟨⟩
   argmaxmin† (X ∷ Xf) ((x₀ , xs , _) :: ss) =
    (λ (p : X → T R) → ArgMax† xs x₀ (ρ (p x₀)) p)
    :: (λ x → argminmax† (Xf x) (ss x))

   G-selections† : 𝓙𝓣 Xt
   G-selections† = argmaxmin† Xt Xt-is-listed⁺

   optimal-play† : Path Xt
   optimal-play† = sequenceᴶᵀ G-selections† q† (-∞ , ∞)

\end{code}

Part 1.

Now we define G' which computes optimal strategies using quantifiers
with a modification of the outcome type to include paths.

\begin{code}

 module minimax' where

  R' : 𝓤 ̇
  R' = R × Path Xt

  q' : Path Xt → R'
  q' xs = q xs , xs

  max' min' : R' → R' → R'

  max' (r , xs) (s , ys)  = Cases (δ r s)
                             (λ (_ : r < s) → (s , ys))
                             (λ (_ : r ≥ s) → (r , xs))

  min' (r , xs) (s , ys)  = Cases (δ s r)
                             (λ (_ : s < r) → (s , ys))
                             (λ (_ : s ≥ r) → (r , xs))

  open K-definitions R'

  Min' Max' : {X : 𝓤 ̇ } → listed⁺ X → K X
  Min' (x₀ , xs , _) p = foldr (λ x → min' (p x)) (p x₀) xs
  Max' (x₀ , xs , _) p = foldr (λ x → max' (p x)) (p x₀) xs

  minmax' maxmin' : (Xt : 𝑻)
                  → structure listed⁺ Xt
                  → 𝓚 R' Xt
  minmax' []       ⟨⟩        = ⟨⟩
  minmax' (X ∷ Xf) (ℓ :: ℓf) = Min' ℓ :: (λ x → maxmin' (Xf x) (ℓf x))
  maxmin' []       ⟨⟩        = ⟨⟩
  maxmin' (X ∷ Xf) (ℓ :: ℓf) = Max' ℓ :: (λ x → minmax' (Xf x) (ℓf x))

  G' : Game R'
  G' = game Xt q' (maxmin' Xt Xt-is-listed⁺)

 {- TODO.

  module _ where

   open minimax R _<_ δ Xt Xt-is-listed⁺ q

   theorem' : optimal-outcome R' G'
            ＝ (K-sequence R (maxmin Xt Xt-is-listed⁺) q ,
               sequenceᴶ R (argmaxmin Xt Xt-is-listed⁺) q)
   theorem' = {!!}
 -}

\end{code}

Now we define G⋆ which again using quantifiers, rather than selection
functions, to compute optimal strategies, but now using monadic
quantifiers with the reader monad to incorporate alpha-beta pruning.

\begin{code}

 module minimax⋆ (-∞ ∞ : R) where

  max min : R → R → R

  max r s = Cases (δ r s)
             (λ (_ : r < s) → s)
             (λ (_ : r ≥ s) → r)

  min r s = Cases (δ s r)
             (λ (_ : s < r) → s)
             (λ (_ : s ≥ r) → r)

  open import MonadOnTypes.Reader
  open import MonadOnTypes.Construction

  AB = R × R

  R⋆ : 𝓤 ̇
  R⋆ = functor (Reader AB) (R × Path Xt)

  private
   NB : R⋆ ＝ (AB → R × Path Xt)
   NB = refl

  q⋆ : Path Xt → R⋆
  q⋆ xs (α , β) = q xs , xs

  max⋆ min⋆ : R⋆ → R⋆ → R⋆

  max⋆ r s αβ = Cases (δ (pr₁ (r αβ)) (pr₁ (s αβ)))
                 (λ (_ : pr₁ (r αβ) < pr₁ (s αβ)) → s αβ)
                 (λ (_ : pr₁ (r αβ) ≥ pr₁ (s αβ)) → r αβ)

  min⋆ r s αβ = Cases (δ (pr₁ (s αβ)) (pr₁ (r αβ)))
                 (λ (_ : pr₁ (s αβ) < pr₁ (r αβ)) → s αβ)
                 (λ (_ : pr₁ (s αβ) ≥ pr₁ (r αβ)) → r αβ)

  Min⋆ Max⋆ : {X : 𝓤 ̇ } → List X → (R × Path Xt) → (X → R⋆) → R⋆

  Min⋆ []       (t , zs) p (α , β) = (t , zs)
  Min⋆ (x ∷ xs) (t , zs) p (α , β) =
   case p x (α , β) of
    λ ((s , ys) : (R × Path Xt))
      → Cases (δ α s)
         (λ (_ : α < s)
               → Cases (δ s t)
                  (λ (_ : s < t) → Min⋆ xs (s , ys) p (α , min β s))
                  (λ (_ : s ≥ t) → Min⋆ xs (t , zs) p (α , β)))
         (λ (_ : α ≥ s)
               → (s , ys))

  Max⋆ []       (t , zs) p (α , β) = (t , zs)
  Max⋆ (x ∷ xs) (t , zs) p (α , β) =
   case p x (α , β) of
    λ ((s , ys) : (R × Path Xt))
      → Cases (δ s β)
         (λ (_ : s < β)
               → Cases (δ t s)
                  (λ (_ : t < s) → Max⋆ xs (s , ys) p (max α s , β))
                  (λ (_ : t ≥ s) → Max⋆ xs (t , zs) p (α , β)))
         (λ (_ : s ≥ β)
               → (s , ys))

  minmax⋆ maxmin⋆ : (Xt : 𝑻)
                  → structure listed⁺ Xt
                  → 𝓚 R⋆ Xt
  minmax⋆ []       ⟨⟩                    = ⟨⟩
  minmax⋆ (X ∷ Xf) ((x₀ , xs , _) :: ss) = (λ p → Min⋆ xs (p x₀ (-∞ , ∞)) p)
                                        :: (λ x → maxmin⋆ (Xf x) (ss x))
  maxmin⋆ []       ⟨⟩                    = ⟨⟩
  maxmin⋆ (X ∷ Xf) ((x₀ , xs , _) :: ss) = (λ p → Max⋆ xs (p x₀ (-∞ , ∞)) p)
                                        :: (λ x → minmax⋆ (Xf x) (ss x))

  G⋆ : Game R⋆
  G⋆ = game Xt q⋆ (maxmin⋆ Xt Xt-is-listed⁺)

 {- TODO.

  module _ where

   open minimax' R _<_ δ Xt Xt-is-listed⁺ q

   theorem⋆₁ : pr₁ (optimal-outcome R⋆ G⋆ (-∞ , ∞)) ＝ pr₁ (optimal-outcome R' G')
   theorem⋆₁ = {!!}

   theorem⋆₂ : q (pr₂ (optimal-outcome R⋆ G⋆ (-∞ , ∞)))
            ＝ pr₁ (optimal-outcome R⋆ G⋆ (-∞ , ∞))
   theorem⋆₂ = {!!}
 -}
\end{code}
