Martin Escardo and Paulo Oliva, originally March - April 2023, with the
proofs November 2026.

Part of the formalization, in Games.AlphaBeta.index, of the paper

  Martín Hötzel Escardó and Paulo Oliva.
  Alpha-Beta Pruning via Monadic Continuations.

The maximizing quantifier and its alpha-beta version.

This module corresponds to Sections 2.1, 3.1 and 4 of the paper, for
the maximizing player. The minimizing player is obtained in the module
Games.AlphaBeta.Minimizer by reversing the order.

We work with a type R of outcomes and a valuation val : R → V into a
type V with a decidable strict weak order, as in Section 4 of the
paper. In Sections 2 to 4 of the paper, R = V and val is the identity,
and in Section 5, R is the type of pairs of a value and a play, with
val the first projection.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import OrderedTypes.DecidableStrictWeakOrder
open import MLTT.List-Properties
open import MLTT.Plus-Properties

module Games.AlphaBeta.Maximizer
        {𝓤 𝓣 : Universe}
        {V : 𝓤 ̇ }
        (O : Decidable-Strict-Weak-Order V 𝓣)
        (R : 𝓤 ̇ )
        (val : R → V)
       where

open import MLTT.List
open import MonadOnTypes.Definition using (functor)
open import MonadOnTypes.K
open import MonadOnTypes.NonEmptyList using (List⁺ ; underlying-list⁺)
open import MonadOnTypes.Reader
open import UF.Base

open Decidable-Strict-Weak-Order O
open K-definitions {𝓤} {R} using (K)

\end{code}

The maximum of two outcomes, with respect to their values, keeps the
left argument in case of a tie, as the Haskell function pickMax of
Appendix A of the paper does. This matters for the computation of optimal plays.

\begin{code}

maxᴿδ : (r s : R) → is-decidable (val r < val s) → R
maxᴿδ r s (inl _) = s
maxᴿδ r s (inr _) = r

_⊔ᴿ_ : R → R → R
r ⊔ᴿ s = maxᴿδ r s (<-decidable (val r) (val s))

⊔ᴿ-upper-left : (r s : R) → val r ≤ val (r ⊔ᴿ s)
⊔ᴿ-upper-left r s = I (<-decidable (val r) (val s))
 where
  I : (d : is-decidable (val r < val s)) → val r ≤ val (maxᴿδ r s d)
  I (inl l) = <-gives-≤ l
  I (inr _) = ≤-refl (val r)

⊔ᴿ-upper-right : (r s : R) → val s ≤ val (r ⊔ᴿ s)
⊔ᴿ-upper-right r s = I (<-decidable (val r) (val s))
 where
  I : (d : is-decidable (val r < val s)) → val s ≤ val (maxᴿδ r s d)
  I (inl _) = ≤-refl (val s)
  I (inr n) = n

⊔ᴿ-preserves : (Q : R → 𝓦 ̇ ) {r s : R} → Q r → Q s → Q (r ⊔ᴿ s)
⊔ᴿ-preserves Q {r} {s} a b = I (<-decidable (val r) (val s))
 where
  I : (d : is-decidable (val r < val s)) → Q (maxᴿδ r s d)
  I (inl _) = b
  I (inr _) = a

⊔ᴿ-reflects : (Q : R → 𝓦 ̇ ) {r s : R} → Q (r ⊔ᴿ s) → Q r + Q s
⊔ᴿ-reflects Q {r} {s} = I (<-decidable (val r) (val s))
 where
  I : (d : is-decidable (val r < val s)) → Q (maxᴿδ r s d) → Q r + Q s
  I (inl _) = inr
  I (inr _) = inl

⊔ᴿ-＝-right : {r s : R} → val r < val s → r ⊔ᴿ s ＝ s
⊔ᴿ-＝-right {r} {s} l = I (<-decidable (val r) (val s))
 where
  I : (d : is-decidable (val r < val s)) → maxᴿδ r s d ＝ s
  I (inl _) = refl
  I (inr n) = 𝟘-elim (n l)

⊔ᴿ-＝-left : {r s : R} → val s ≤ val r → r ⊔ᴿ s ＝ r
⊔ᴿ-＝-left {r} {s} l = I (<-decidable (val r) (val s))
 where
  I : (d : is-decidable (val r < val s)) → maxᴿδ r s d ＝ r
  I (inl m) = 𝟘-elim (l m)
  I (inr _) = refl

\end{code}

The maximum of a non-empty list.

\begin{code}

maxˡ : R → List R → R
maxˡ r []       = r
maxˡ r (s ∷ ss) = r ⊔ᴿ maxˡ s ss

max⁺ : List⁺ R → R
max⁺ ([]       , ν) = 𝟘-elim ν
max⁺ ((r ∷ rs) , _) = maxˡ r rs

maxˡ-preserves : (Q : R → 𝓦 ̇ ) (r : R) (rs : List R)
               → Q r → All Q rs → Q (maxˡ r rs)
maxˡ-preserves Q r []       a []       = a
maxˡ-preserves Q r (s ∷ ss) a (b ∷ bs) =
 ⊔ᴿ-preserves Q a (maxˡ-preserves Q s ss b bs)

\end{code}

The reader monad T, which records the pair (α , β) of bounds. The
continuation monad K is that of the module MonadOnTypes.K.

\begin{code}

_ : {X : 𝓤 ̇ } → K X ＝ ((X → R) → R)
_ = refl

T : 𝓤 ̇ → 𝓤 ̇
T = functor (Reader (V × V))

_ : {X : 𝓤 ̇ } → T X ＝ (V × V → X)
_ = refl

\end{code}

The quantifier φmax of Section 2.1 of the paper, which computes the
maximum of p over a non-empty list of moves, as the Haskell function
phiMax xs p = maximum (map p xs) does.

\begin{code}

φmax : {X : 𝓤 ̇ } → List⁺ X → K X
φmax (xs , ν) p = max⁺ (map p xs , map-is-non-empty p xs ν)

φmax-preserves : {X : 𝓤 ̇ } (Q : R → 𝓦 ̇ ) (xs : List⁺ X) (p : X → R)
               → ((x : X) → Q (p x))
               → Q (φmax xs p)
φmax-preserves         Q ([]       , ν) p a = 𝟘-elim ν
φmax-preserves {𝓦} {X} Q ((x ∷ xs) , _) p a =
 maxˡ-preserves Q (p x) (map p xs) (a x) (I xs)
 where
  I : (ys : List X) → All Q (map p ys)
  I []       = []
  I (y ∷ ys) = a y ∷ I ys

φmax-is-attained : {X : 𝓤 ̇ } (xs : List⁺ X) (p : X → R)
                 → Σ x ꞉ X , φmax xs p ＝ p x
φmax-is-attained {X} xs p =
 φmax-preserves (λ r → Σ x ꞉ X , r ＝ p x) xs p (λ x → x , refl)

\end{code}

The function ℓ of the definition of the quantifier φ*max in Section 4
of the paper, which evaluates the given monadic predicate p on the
moves in the given order, updating α with the maximum of the values
found so far. The function takeUntil of that definition is take-until
of the module MLTT.List-Properties.

\begin{code}

ℓ : {X : 𝓤 ̇ } → (X → T R) → List X → T (List R)
ℓ p []       (α , β) = []
ℓ p (x ∷ xs) (α , β) = let r = p x (α , β) in r ∷ ℓ p xs (max α (val r) , β)

ℓ-is-non-empty : {X : 𝓤 ̇ } (p : X → T R) (xs : List X) (αβ : V × V)
               → is-non-empty xs
               → is-non-empty (ℓ p xs αβ)
ℓ-is-non-empty p []       αβ ν = 𝟘-elim ν
ℓ-is-non-empty p (x ∷ xs) αβ _ = cons-is-non-empty

\end{code}

The alpha-beta quantifier φ*max of Section 4 of the paper. The list of
outcomes is cut after the first outcome whose value is at least β.

\begin{code}

φ*max : {X : 𝓤 ̇ } → List⁺ X → (X → T R) → T R
φ*max (xs , ν) p (α , β) =
 max⁺ (take-until (λ r → β ≤ val r) (λ r → ≤-decidable β (val r))
                  (ℓ p xs (α , β)) ,
       take-until-is-non-empty
        (λ r → β ≤ val r)
        (λ r → ≤-decidable β (val r))
        (ℓ p xs (α , β))
        (ℓ-is-non-empty p xs (α , β) ν))

\end{code}

Lemma 1 of the paper. For a list xs = [x₀ , … , xₙ₋₁], define α₀ = α
and αᵢ₊₁ = max(αᵢ , val(p(xᵢ)(αᵢ , β))). Then the list ℓ(xs)(α , β) is
the list of the outcomes p(xᵢ)(αᵢ , β). We pair each xᵢ with its αᵢ.

\begin{code}

αs : {X : 𝓤 ̇ } → (X → T R) → V → V → List X → List (X × V)
αs p β α []       = []
αs p β α (x ∷ xs) = (x , α) ∷ αs p β (max α (val (p x (α , β)))) xs

ℓ-characterization : {X : 𝓤 ̇ } (p : X → T R) (xs : List X) (α β : V)
                   → ℓ p xs (α , β)
                   ＝ map (λ (x , a) → p x (a , β)) (αs p β α xs)
ℓ-characterization p []       α β = refl
ℓ-characterization p (x ∷ xs) α β =
 ap (p x (α , β) ∷_) (ℓ-characterization p xs (max α (val (p x (α , β)))) β)

\end{code}

Lemma 2 of the paper. (i) If p(xᵢ)(α , β) ≤ α for every i < n, then
αᵢ = α for every i, and φ*max(xs , p)(α , β) ≤ α. (ii) If
p(xᵢ)(αᵢ , β) ≥ β for some i, then φ*max(xs , p)(α , β) ≥ β.

\begin{code}

max⁺-preserves : (Q : R → 𝓦 ̇ ) (rs : List⁺ R)
               → All Q (underlying-list⁺ rs)
               → Q (max⁺ rs)
max⁺-preserves Q ([]       , ν) _        = 𝟘-elim ν
max⁺-preserves Q ((r ∷ rs) , _) (a ∷ as) = maxˡ-preserves Q r rs a as

module _ {X : 𝓤 ̇ }
         (p : X → T R)
         (α β : V)
       where

 private
  B : X → 𝓣 ̇
  B x = val (p x (α , β)) ≤ α

  e : (x : X) → B x → max α (val (p x (α , β))) ＝ α
  e x = max-＝-left

 all-αs-are-α : (xs : List X) → All B xs → All (λ (_ , a) → a ＝ α) (αs p β α xs)
 all-αs-are-α []       []       = []
 all-αs-are-α (x ∷ xs) (b ∷ bs) =
  refl ∷ transport (λ - → All (λ (_ , a) → a ＝ α) (αs p β - xs))
          ((e x b)⁻¹)
          (all-αs-are-α xs bs)

 private
  ℓ-bounded : (xs : List X) → All B xs → All (λ r → val r ≤ α) (ℓ p xs (α , β))
  ℓ-bounded []       []       = []
  ℓ-bounded (x ∷ xs) (b ∷ bs) =
   b ∷ transport (λ - → All (λ r → val r ≤ α) (ℓ p xs (- , β)))
        ((e x b)⁻¹)
        (ℓ-bounded xs bs)

 φ*max-is-at-most-α : (xs : List⁺ X)
                    → All B (underlying-list⁺ xs)
                    → val (φ*max xs p (α , β)) ≤ α
 φ*max-is-at-most-α (xs , ν) bs =
  max⁺-preserves (λ r → val r ≤ α) _
   (take-until-preserves _ _ (λ r → val r ≤ α) (ℓ p xs (α , β))
     (ℓ-bounded xs bs))

φ*max-is-at-least-β : {X : 𝓤 ̇ }
                      (p : X → T R)
                      (α β : V)
                      (xs : List⁺ X)
                      (x : X)
                      (a : V)
                    → member (x , a) (αs p β α (underlying-list⁺ xs))
                    → β ≤ val (p x (a , β))
                    → β ≤ val (φ*max xs p (α , β))
φ*max-is-at-least-β p α β ([]       , ν) x a m l = 𝟘-elim ν
φ*max-is-at-least-β p α β ((y ∷ ys) , _) x a m l = I ys α m l
 where
  reaches-β-decidable : (r : R) → is-decidable (β ≤ val r)
  reaches-β-decidable r = ≤-decidable β (val r)

  I : (ys : List _) (α : V)
    → member (x , a) (αs p β α (y ∷ ys))
    → β ≤ val (p x (a , β))
    → β ≤ val (φ*max ((y ∷ ys) , cons-is-non-empty) p (α , β))
  I ys α in-head l = II (reaches-β-decidable (p x (α , β)))
   where
    II : (e : is-decidable (β ≤ val (p x (α , β))))
       → β ≤ val (maxˡ (p x (α , β))
                     (Cases e
                       (λ _ → [])
                       (λ _ → take-until _ reaches-β-decidable
                               (ℓ p ys (max α (val (p x (α , β))) , β)))))
    II (inl k) = k
    II (inr k) = 𝟘-elim (k l)
  I []        α (in-tail m)  l = 𝟘-elim (empty-list-has-no-members (x , a) m)
  I (y₁ ∷ ys) α (in-tail m)  l = II (reaches-β-decidable r)
   where
    r  = p y (α , β)
    α' = max α (val r)

    II : (e : is-decidable (β ≤ val r))
       → β ≤ val (maxˡ r (Cases e
                           (λ _ → [])
                           (λ _ → take-until _ reaches-β-decidable
                                   (ℓ p (y₁ ∷ ys) (α' , β)))))
    II (inl k) = k
    II (inr _) =
     ≤-trans
      (φ*max-is-at-least-β p α' β ((y₁ ∷ ys) , cons-is-non-empty) x a m l)
      (⊔ᴿ-upper-right r _)

\end{code}

The relation between an outcome r and a monadic outcome t that
Theorem 1 of the paper asserts between the outcome of a game and the
monadic outcome of the alpha-beta version of the game.

\begin{code}

_is-αβ-approximated-by_ : R → T R → 𝓤 ⊔ 𝓣 ̇
r is-αβ-approximated-by t =
 (α β : V) → (val r ≤ α → val (t (α , β)) ≤ α)
           × (β ≤ val r → β ≤ val (t (α , β)))
           × (α < val r → val r < β → t (α , β) ＝ r)

module _ {r : R} {t : T R} (h : r is-αβ-approximated-by t) (α β : V) where

 αβ-approximation-at-most-α : val r ≤ α → val (t (α , β)) ≤ α
 αβ-approximation-at-most-α = pr₁ (h α β)

 αβ-approximation-at-least-β : β ≤ val r → β ≤ val (t (α , β))
 αβ-approximation-at-least-β = pr₁ (pr₂ (h α β))

 αβ-approximation-exact : α < val r → val r < β → t (α , β) ＝ r
 αβ-approximation-exact = pr₂ (pr₂ (h α β))

\end{code}

The induction step, for the maximizing player, of the proof of
Theorem 1 of the paper: if each outcome p x is approximated by the
monadic outcome p* x, then φmax xs p is approximated by φ*max xs p*.

We prove the three parts separately, for a fixed β, as the three cases
of the proof in the paper, where y ∷ ys is the list of moves. Parts
(i) and (ii) use Lemma 2, and part (iii) is by induction on the list
of moves, with α varying.

\begin{code}

module _ {X : 𝓤 ̇ }
         (p  : X → R)
         (p* : X → T R)
         (h  : (x : X) → (p x) is-αβ-approximated-by (p* x))
       where

 private
  h₁ : (x : X) (α β : V) → val (p x) ≤ α → val (p* x (α , β)) ≤ α
  h₁ x α β = αβ-approximation-at-most-α (h x) α β

  h₂ : (x : X) (α β : V) → β ≤ val (p x) → β ≤ val (p* x (α , β))
  h₂ x α β = αβ-approximation-at-least-β (h x) α β

  h₃ : (x : X) (α β : V) → α < val (p x) → val (p x) < β → p* x (α , β) ＝ p x
  h₃ x α β = αβ-approximation-exact (h x) α β

 module _ (β : V) where

  private
   ex : X → List X → R
   ex y ys = φmax ((y ∷ ys) , cons-is-non-empty) p

   ab : V → X → List X → R
   ab α y ys = φ*max ((y ∷ ys) , cons-is-non-empty) p* (α , β)

   reaches-β-decidable : (r : R) → is-decidable (β ≤ val r)
   reaches-β-decidable r = ≤-decidable β (val r)

\end{code}

Every move y has value at most that of the maximum of the list.

\begin{code}

   ex-is-upper-bound : (y : X) (ys : List X)
                     → All (λ x → val (p x) ≤ val (ex y ys)) (y ∷ ys)
   ex-is-upper-bound y []        = ≤-refl (val (p y)) ∷ []
   ex-is-upper-bound y (y₁ ∷ ys) =
    ⊔ᴿ-upper-left (p y) (ex y₁ ys) ∷
    All-map (λ x k → ≤-trans k (⊔ᴿ-upper-right (p y) (ex y₁ ys)))
            (ex-is-upper-bound y₁ ys)

\end{code}

The maximum of the list is the outcome of one of its moves, which the
search considers with some bound α, as recorded by the list αs.

\begin{code}

   ex-is-attained : (Q : R → 𝓦 ̇ ) (ys : List X) (y : X) (α : V)
                  → Q (ex y ys)
                  → Σ x ꞉ X , Σ a ꞉ V , member (x , a) (αs p* β α (y ∷ ys))
                                      × Q (p x)
   ex-is-attained Q []        y α c = y , α , in-head , c
   ex-is-attained Q (y₁ ∷ ys) y α c =
    Cases (⊔ᴿ-reflects Q c)
     (λ (c₀ : Q (p y)) → y , α , in-head , c₀)
     (λ (c₁ : Q (ex y₁ ys)) →
       let (x , a , m , d) = ex-is-attained Q ys y₁
                              (max α (val (p* y (α , β)))) c₁
       in x , a , in-tail m , d)

\end{code}

Case (i) of the proof of Theorem 1 in the paper. The bound of the
maximum gives the bound of the outcome of each move (I), the induction
hypothesis (i) gives the bound of each monadic outcome (II), and
Lemma 2(i), which is φ*max-is-at-most-α, gives the bound of the
alpha-beta search (III).

\begin{code}

  part₁ : (ys : List X) (y : X) (α : V)
        → val (ex y ys) ≤ α → val (ab α y ys) ≤ α
  part₁ ys y α l = III
   where
    I : All (λ x → val (p x) ≤ α) (y ∷ ys)
    I = All-map (λ x k → ≤-trans k l) (ex-is-upper-bound y ys)

    II : All (λ x → val (p* x (α , β)) ≤ α) (y ∷ ys)
    II = All-map (λ x k → h₁ x α β k) I

    III : val (ab α y ys) ≤ α
    III = φ*max-is-at-most-α p* α β ((y ∷ ys) , cons-is-non-empty) II

\end{code}

Case (ii) of the proof of Theorem 1 in the paper: a move xᵢ with
outcome at least β, the induction hypothesis (ii) at (αᵢ , β), and
Lemma 2(ii).

\begin{code}

  part₂ : (ys : List X) (y : X) (α : V)
        → β ≤ val (ex y ys) → β ≤ val (ab α y ys)
  part₂ ys y α l =
   let (x , a , m , k) = ex-is-attained (λ r → β ≤ val r) ys y α l
   in φ*max-is-at-least-β p* α β ((y ∷ ys) , cons-is-non-empty)
       x a m (h₂ x a β k)

\end{code}

Case (iii) of the proof of Theorem 1 in the paper, with k the index
at which the maximum is attained first. When the maximum is not
attained at the head y of the list, the outcome of y is below the
maximum, and the search goes on to the tail with an updated bound still
below the maximum. When the maximum is attained at the head, the bound
becomes the maximum, and part₁ bounds the rest of the list.

\begin{code}

  part₃ : (ys : List X) (y : X) (α : V)
        → α < val (ex y ys)
        → val (ex y ys) < β
        → ab α y ys ＝ ex y ys
  part₃ [] y α a b = I (reaches-β-decidable r)
   where
    r = p* y (α , β)

    I : (e : is-decidable (β ≤ val r))
      → maxˡ r (Cases e (λ _ → []) (λ _ → [])) ＝ p y
    I e = maxˡ r (Cases e (λ _ → []) (λ _ → []))  ＝⟨ II ⟩
          maxˡ r []                               ＝⟨ III ⟩
          p y                                     ∎
     where
      II  = ap (maxˡ r) (Cases-same e [])
      III = h₃ y α β a b

  part₃ (y₁ ∷ ys) y α = I (<-decidable (val (p y)) (val m₁))
   where
    r  = p* y (α , β)
    α' = max α (val r)
    m₁ = ex y₁ ys

    no-cut : val r < β
           → maxˡ r (Cases (reaches-β-decidable r)
                      (λ _ → [])
                      (λ _ → take-until _ reaches-β-decidable
                              (ℓ p* (y₁ ∷ ys) (α' , β))))
           ＝ r ⊔ᴿ ab α' y₁ ys
    no-cut l = ap (maxˡ r)
                  (Cases-right (reaches-β-decidable r) _ _
                    (λ (k : β ≤ val r) → k l))

    I : (d : is-decidable (val (p y) < val m₁))
      → α < val (maxᴿδ (p y) m₁ d)
      → val (maxᴿδ (p y) m₁ d) < β
      → ab α y (y₁ ∷ ys) ＝ maxᴿδ (p y) m₁ d
    I (inl c) a b = II (<-decidable α (val (p y)))
     where
      II : is-decidable (α < val (p y)) → ab α y (y₁ ∷ ys) ＝ m₁
      II (inl a') = ab α y (y₁ ∷ ys) ＝⟨ no-cut l ⟩
                    r ⊔ᴿ ab α' y₁ ys ＝⟨ ap₂ _⊔ᴿ_ e₁ IH ⟩
                    p y ⊔ᴿ m₁        ＝⟨ ⊔ᴿ-＝-right c ⟩
                    m₁               ∎
       where
        e₁ : r ＝ p y
        e₁ = h₃ y α β a' (<-transitive _ _ _ c b)

        l : val r < β
        l = transport (λ - → val - < β) (e₁ ⁻¹) (<-transitive _ _ _ c b)

        e₂ : α' ＝ val (p y)
        e₂ = α'        ＝⟨ e₂₀ ⟩
             val r     ＝⟨ ap val e₁ ⟩
             val (p y) ∎
         where
          e₂₀ = max-＝-right (transport (λ - → α < val -) (e₁ ⁻¹) a')

        IH : ab α' y₁ ys ＝ m₁
        IH = ab α' y₁ ys          ＝⟨ ap (λ - → ab - y₁ ys) e₂ ⟩
             ab (val (p y)) y₁ ys ＝⟨ part₃ ys y₁ (val (p y)) c b ⟩
             m₁                   ∎

      II (inr a'') = ab α y (y₁ ∷ ys) ＝⟨ no-cut l ⟩
                     r ⊔ᴿ ab α' y₁ ys ＝⟨ ap (r ⊔ᴿ_) IH ⟩
                     r ⊔ᴿ m₁          ＝⟨ ⊔ᴿ-＝-right (≤-<-trans k a) ⟩
                     m₁               ∎
       where
        k : val r ≤ α
        k = h₁ y α β a''

        l : val r < β
        l = ≤-<-trans k (<-transitive _ _ _ a b)

        IH : ab α' y₁ ys ＝ m₁
        IH = ab α' y₁ ys ＝⟨ ap (λ - → ab - y₁ ys) (max-＝-left k) ⟩
             ab α y₁ ys  ＝⟨ part₃ ys y₁ α a b ⟩
             m₁          ∎

    I (inr c) a b = ab α y (y₁ ∷ ys) ＝⟨ no-cut l ⟩
                    r ⊔ᴿ ab α' y₁ ys ＝⟨ ⊔ᴿ-＝-left IH ⟩
                    r                ＝⟨ e₁ ⟩
                    p y              ∎
     where
      e₁ : r ＝ p y
      e₁ = h₃ y α β a b

      l : val r < β
      l = transport (λ - → val - < β) (e₁ ⁻¹) b

      e₂ : α' ＝ val r
      e₂ = max-＝-right (transport (λ - → α < val -) (e₁ ⁻¹) a)

      e₃ : α' ＝ val (p y)
      e₃ = α'        ＝⟨ e₂ ⟩
           val r     ＝⟨ ap val e₁ ⟩
           val (p y) ∎

      c' : val m₁ ≤ α'
      c' = transport (val m₁ ≤_) (e₃ ⁻¹) c

      IH : val (ab α' y₁ ys) ≤ val r
      IH = transport (val (ab α' y₁ ys) ≤_) e₂ (part₁ ys y₁ α' c')

\end{code}

The induction step for the maximizing player.

\begin{code}

 φmax-is-αβ-approximated-by-φ*max
  : (xs : List⁺ X) → (φmax xs p) is-αβ-approximated-by (φ*max xs p*)
 φmax-is-αβ-approximated-by-φ*max ([] , ν) α β = 𝟘-elim ν
 φmax-is-αβ-approximated-by-φ*max ((y ∷ ys) , _) α β =
  part₁ β ys y α , part₂ β ys y α , part₃ β ys y α

\end{code}
