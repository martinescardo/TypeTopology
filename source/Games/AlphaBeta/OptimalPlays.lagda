Martin Escardo and Paulo Oliva, originally March - April 2023, with the
proofs November 2026.

Part of the formalization, in Games.AlphaBeta.index, of the paper

  Martín Hötzel Escardó and Paulo Oliva.
  Alpha-Beta Pruning via Monadic Continuations.

Computing optimal plays (Section 5 of the paper).

Given a minimax game with outcomes in a type V of values and outcome
function q, we extend the type of outcomes to pairs of a value and a
play, compared by their values, and the outcome function to
q'(xs) = (q(xs) , xs). We show that the optimal outcome of the
extended game is a pair of the optimal outcome of the original game
and an optimal play of the original game, in the sense of the module
Games.OptimalPlays. By Theorem 1, applied to the extended game, the
same is true of the outcome computed by the alpha-beta search.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import OrderedTypes.DecidableStrictWeakOrder

module Games.AlphaBeta.OptimalPlays
        {𝓤 𝓣 : Universe}
        {V : 𝓤 ̇ }
        (O : Decidable-Strict-Weak-Order V 𝓣)
       where

open import Games.AlphaBeta.Player
open import Games.TypeTrees {𝓤}
open import MLTT.List
open import MonadOnTypes.NonEmptyList using (List⁺)
open import UF.Base

import Games.AlphaBeta.ViaProductsOfQuantifiers
import Games.AlphaBeta.Maximizer

open import Games.OptimalPlays {𝓤} {𝓤} V
 using (is-optimal-play ; optimal-play-gives-optimal-outcome)

open Decidable-Strict-Weak-Order O

value : {P : 𝓤 ̇ } → V × P → V
value = pr₁

play : {P : 𝓤 ̇ } → V × P → P
play = pr₂

\end{code}

We first work with an arbitrary type P in place of the type of plays.
The original game, with outcomes in V, is the module Original, and
the extended game, with outcomes in V × P, is the module Extended.

\begin{code}

module _ (P : 𝓤 ̇ ) where

 private
  module Original = Games.AlphaBeta.ViaProductsOfQuantifiers O V id
  module Extended = Games.AlphaBeta.ViaProductsOfQuantifiers O (V × P) value

\end{code}

The first projection commutes with the quantifiers, for either order.

\begin{code}

 private
  module _ (O' : Decidable-Strict-Weak-Order V 𝓣) where

   module Maximizer-on-values = Games.AlphaBeta.Maximizer O' V id
   module Maximizer-on-extended-outcomes =
    Games.AlphaBeta.Maximizer O' (V × P) value

   open Maximizer-on-values using (_⊔ᴿ_ ; maxᴿδ ; maxˡ ; φmax)
   open Maximizer-on-extended-outcomes
    renaming (_⊔ᴿ_ to _⊔ᴿ'_ ; maxᴿδ to maxᴿδ' ; maxˡ to maxˡ' ; φmax to φmax')

   open Decidable-Strict-Weak-Order O' renaming (<-decidable to <'-decidable)

   value-⊔ : (r s : V × P) → value (r ⊔ᴿ' s) ＝ value r ⊔ᴿ value s
   value-⊔ r s = I (<'-decidable (value r) (value s))
    where
     I : (d : is-decidable _)
       → value (maxᴿδ' r s d) ＝ maxᴿδ (value r) (value s) d
     I (inl _) = refl
     I (inr _) = refl

   value-maxˡ : {X : 𝓤 ̇ } (p' : X → V × P) (p : X → V)
              → ((x : X) → value (p' x) ＝ p x)
              → (x : X) (xs : List X)
              → value (maxˡ' (p' x) (map p' xs)) ＝ maxˡ (p x) (map p xs)
   value-maxˡ p' p e x []       = e x
   value-maxˡ p' p e x (y ∷ ys) =
    value (maxˡ' (p' x) (map p' (y ∷ ys)))           ＝⟨ I ⟩
    value (p' x) ⊔ᴿ value (maxˡ' (p' y) (map p' ys)) ＝⟨ II ⟩
    maxˡ (p x) (map p (y ∷ ys))                      ∎
     where
      I  = value-⊔ (p' x) (maxˡ' (p' y) (map p' ys))
      II = ap₂ _⊔ᴿ_ (e x) (value-maxˡ p' p e y ys)

   value-φmax : {X : 𝓤 ̇ } (xs : List⁺ X) (p' : X → V × P) (p : X → V)
              → ((x : X) → value (p' x) ＝ p x)
              → value (φmax' xs p') ＝ φmax xs p
   value-φmax ([]       , ν) p' p e = 𝟘-elim ν
   value-φmax ((x ∷ xs) , _) p' p e = value-maxˡ p' p e x xs

 value-quantifier : {X : 𝓤 ̇ } (n : Node X) (p' : X → V × P) (p : X → V)
                  → ((x : X) → value (p' x) ＝ p x)
                  → value (Extended.quantifier n p') ＝ Original.quantifier n p
 value-quantifier (maximizer , xs) = value-φmax O xs
 value-quantifier (minimizer , xs) = value-φmax (opposite O) xs

 value-outcome : (Yt : 𝑻)
                 (nt : structure Node Yt)
                 (q' : Path Yt → V × P)
               → value (Extended.outcome Yt nt q')
               ＝ Original.outcome Yt nt (value ∘ q')
 value-outcome []       ⟨⟩        q' = refl
 value-outcome (X ∷ Xf) (n :: nf) q' =
  value-quantifier n
   (λ x → Extended.outcome (Xf x) (nf x) (subpred q' x))
   (λ x → Original.outcome (Xf x) (nf x) (value ∘ subpred q' x))
   (λ x → value-outcome (Xf x) (nf x) (subpred q' x))

\end{code}

The optimal outcome of the extended game is the outcome of an optimal
play of the original game.

\begin{code}

 outcome-is-attained-at-optimal-play
  : (Yt : 𝑻)
    (nt : structure Node Yt)
    (q' : Path Yt → V × P)
  → Σ ys ꞉ Path Yt , (Extended.outcome Yt nt q' ＝ q' ys)
                   × is-optimal-play
                      (Original.quantifier-tree nt) (value ∘ q') ys
 outcome-is-attained-at-optimal-play []       ⟨⟩        q' = ⟨⟩ , refl , ⋆
 outcome-is-attained-at-optimal-play (X ∷ Xf) (n :: nf) q' =
  let (x  , e)      = Extended.quantifier-is-attained n p'
      (ys , e' , o) = outcome-is-attained-at-optimal-play
                       (Xf x) (nf x) (subpred q' x)

      I : Path (X ∷ Xf)
      I = x :: ys

      II : Extended.outcome (X ∷ Xf) (n :: nf) q' ＝ q' I
      II = Extended.outcome (X ∷ Xf) (n :: nf) q' ＝⟨ e ⟩
           p' x                                   ＝⟨ e' ⟩
           q' I                                   ∎

      III : is-optimal-play (Original.quantifier-tree (n :: nf)) (value ∘ q') I
      III = IV x e , o
  in I , II , III
  where
   p' : X → V × P
   p' x = Extended.outcome (Xf x) (nf x) (subpred q' x)

   IV : (x : X)
      → Extended.quantifier n p' ＝ p' x
      → Original.outcome (X ∷ Xf) (n :: nf) (value ∘ q')
      ＝ Original.outcome (Xf x) (nf x) (value ∘ subpred q' x)
   IV x e = Original.outcome (X ∷ Xf) (n :: nf) (value ∘ q')      ＝⟨ IV₀ ⟩
            value (Extended.outcome (X ∷ Xf) (n :: nf) q')        ＝⟨ IV₁ ⟩
            value (p' x)                                          ＝⟨ IV₂ ⟩
            Original.outcome (Xf x) (nf x) (value ∘ subpred q' x) ∎
    where
     IV₀ = (value-outcome (X ∷ Xf) (n :: nf) q')⁻¹
     IV₁ = ap value e
     IV₂ = value-outcome (Xf x) (nf x) (subpred q' x)

\end{code}

We now take P to be the type of plays of a given game, and the
outcome function of the extended game to be q'(xs) = (q(xs) , xs).
The first component of the optimal outcome of the extended game is
the optimal outcome of the original game, and its second component is
an optimal play.

\begin{code}

module _ (Xt : 𝑻)
         (nt : structure Node Xt)
         (q  : Path Xt → V)
       where

 private
  module Original = Games.AlphaBeta.ViaProductsOfQuantifiers O V id
  module Extended =
   Games.AlphaBeta.ViaProductsOfQuantifiers O (V × Path Xt) value
  module Maximizer-on-extended-outcomes =
   Games.AlphaBeta.Maximizer O (V × Path Xt) value

 q' : Path Xt → V × Path Xt
 q' xs = q xs , xs

 optimal-outcome-of-extended-game
  : value (Extended.outcome Xt nt q') ＝ Original.outcome Xt nt q
 optimal-outcome-of-extended-game = value-outcome (Path Xt) Xt nt q'

 optimal-play-of-extended-game
  : is-optimal-play
     (Original.quantifier-tree nt) q (play (Extended.outcome Xt nt q'))
 optimal-play-of-extended-game =
  let (_ , e , o) = outcome-is-attained-at-optimal-play (Path Xt) Xt nt q'
  in transport
      (is-optimal-play (Original.quantifier-tree nt) q)
      (ap play (e ⁻¹))
      o

\end{code}

The two together, as in the first claim of Corollary 2 of the paper.

\begin{code}

 extended-game-gives-optimal-play
  : Σ t ꞉ Path Xt , (Extended.outcome Xt nt q' ＝ (Original.outcome Xt nt q , t))
                  × is-optimal-play (Original.quantifier-tree nt) q t
 extended-game-gives-optimal-play =
  let (ys , e , o) = outcome-is-attained-at-optimal-play (Path Xt) Xt nt q'

      I : Path Xt
      I = ys

      II : Extended.outcome Xt nt q' ＝ (Original.outcome Xt nt q , I)
      II = Extended.outcome Xt nt q'      ＝⟨ e ⟩
           q' I                           ＝⟨ ap (_, I) (IV I o) ⟩
           (Original.outcome Xt nt q , I) ∎

      III : is-optimal-play (Original.quantifier-tree nt) q I
      III = o
  in I , II , III
  where
   IV : (ys : Path Xt)
      → is-optimal-play (Original.quantifier-tree nt) q ys
      → q ys ＝ Original.outcome Xt nt q
   IV = optimal-play-gives-optimal-outcome (Original.quantifier-tree nt) q

\end{code}

The second claim of Corollary 2 of the paper. If the optimal outcome of
the original game lies strictly between α and β, then the alpha-beta
search of the extended game with these bounds computes the same outcome
as the exhaustive search of the extended game, and hence, by the above,
the optimal outcome of the original game together with an optimal
play.

\begin{code}

 αβ-search-agrees-with-exhaustive-search
  : (α β : V)
  → α < Original.outcome Xt nt q
  → Original.outcome Xt nt q < β
  → Extended.outcome* Xt nt q' (α , β) ＝ Extended.outcome Xt nt q'
 αβ-search-agrees-with-exhaustive-search α β a b =
  Maximizer-on-extended-outcomes.αβ-approximation-exact
   (Extended.theorem Xt nt q') α β
   (transport (α <_) (e ⁻¹) a)
   (transport (_< β) (e ⁻¹) b)
  where
   e : value (Extended.outcome Xt nt q') ＝ Original.outcome Xt nt q
   e = optimal-outcome-of-extended-game

\end{code}

The same holds for the alpha-beta search of the extended game started
with bounds -∞ and ∞ strictly below and above the values of all
outcomes, by Corollary 1(a).

\begin{code}

 αβ-outcome-and-play : V → V → V × Path Xt
 αβ-outcome-and-play -∞ ∞ = Extended.outcome* Xt nt q' (-∞ , ∞)

 module _ (-∞ ∞ : V)
          (a : (xs : Path Xt) → -∞ < q xs)
          (b : (xs : Path Xt) → q xs < ∞)
        where

  private
   e : αβ-outcome-and-play -∞ ∞ ＝ Extended.outcome Xt nt q'
   e = Extended.corollary Xt nt q' -∞ ∞ a b

  αβ-outcome-is-optimal
   : value (αβ-outcome-and-play -∞ ∞) ＝ Original.outcome Xt nt q
  αβ-outcome-is-optimal =
   value (αβ-outcome-and-play -∞ ∞)  ＝⟨ ap value e ⟩
   value (Extended.outcome Xt nt q') ＝⟨ optimal-outcome-of-extended-game ⟩
   Original.outcome Xt nt q          ∎

  αβ-play-is-optimal
   : is-optimal-play
      (Original.quantifier-tree nt) q (play (αβ-outcome-and-play -∞ ∞))
  αβ-play-is-optimal = transport
                        (is-optimal-play (Original.quantifier-tree nt) q)
                        (ap play (e ⁻¹))
                        optimal-play-of-extended-game

\end{code}
