Martin Escardo, November-December 2019

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Fin.Pigeonhole where

open import UF.Subsingletons

open import Factorial.Swap
open import Fin.Bishop
open import Fin.Choice
open import Fin.Embeddings
open import Fin.Order
open import Fin.Topology
open import Fin.Type
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import Naturals.Order
open import Notation.Order
open import NotionsOfDecidability.Complemented
open import NotionsOfDecidability.Decidable
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.LeftCancellable
open import UF.PropTrunc

\end{code}

Recall that X ↣ Y is the type of left cancellable maps from X to Y,
which should not be confused with the type X ↪ Y of embeddings of X
into Y. However, for types that are sets, like Fin n, there is no
difference between the embedding property and left cancellability.

\begin{code}

+𝟙-cancel-lemma : {X Y : 𝓤 ̇ }
                → (𝒇 : X + 𝟙 ↣ Y + 𝟙)
                → ⌈ 𝒇 ⌉ 𝟎 ＝ 𝟎
                → X ↣ Y

+𝟙-cancel-lemma {𝓤} {X} {Y} (f , l) p = g , m
 where
  g : X → Y
  g x = pr₁ (inl-preservation {𝓤} {𝓤} {𝓤} {𝓤} f p l x)

  a : (x : X) → f (suc x) ＝ suc (g x)
  a x = pr₂ (inl-preservation f p l x)

  m : left-cancellable g
  m {x} {x'} p = q
   where
    r = f (suc x)  ＝⟨ a x ⟩
        suc (g x)  ＝⟨ ap suc p ⟩
        suc (g x') ＝⟨ (a x')⁻¹ ⟩
        f (suc x') ∎

    q : x ＝ x'
    q = inl-lc (l r)


+𝟙-cancel : {X Y : 𝓤 ̇ }
          → is-discrete Y
          → X + 𝟙 ↣ Y + 𝟙
          → X ↣ Y

+𝟙-cancel {𝓤} {X} {Y} i (f , e) = a
 where
  h : Y + 𝟙 → Y + 𝟙
  h = swap (f 𝟎) 𝟎 (+-is-discrete i 𝟙-is-discrete (f 𝟎)) new-point-is-isolated

  d : left-cancellable h
  d = equivs-are-lc h (swap-is-equiv (f 𝟎) 𝟎 (+-is-discrete i 𝟙-is-discrete (f 𝟎)) new-point-is-isolated)

  f' : X + 𝟙 → Y + 𝟙
  f' = h ∘ f

  e' : left-cancellable f'
  e' = left-cancellable-closed-under-∘ f h e d

  p : f' 𝟎 ＝ 𝟎
  p = swap-equation₀ (f 𝟎) 𝟎 (+-is-discrete i 𝟙-is-discrete (f 𝟎)) new-point-is-isolated

  a : X ↣ Y
  a = +𝟙-cancel-lemma (f' , e') p

\end{code}

In set theory, natural numbers are defined as certain sets, and their
order relation is inherited from the ordering of sets defined by the
existence of injections, or left-cancellable maps. Here, in type
theory, we have defined m ≤ n by induction on m and n, in the style of
Peano Arithmetic, but we can prove that this relation is characterized
by this injection property:

\begin{code}

↣-gives-≤ : (m n : ℕ) → (Fin m ↣ Fin n) → m ≤ n
↣-gives-≤ 0        n        e       = zero-least n
↣-gives-≤ (succ m) 0        (f , i) = 𝟘-elim (f 𝟎)
↣-gives-≤ (succ m) (succ n) e       = ↣-gives-≤ m n (+𝟙-cancel Fin-is-discrete e)


canonical-Fin-inclusion : (m n : ℕ) → m ≤ n → (Fin m → Fin n)
canonical-Fin-inclusion 0        n        l = unique-from-𝟘
canonical-Fin-inclusion (succ m) 0        l = 𝟘-elim l
canonical-Fin-inclusion (succ m) (succ n) l = +functor IH unique-to-𝟙
 where
  IH : Fin m → Fin n
  IH = canonical-Fin-inclusion m n l


canonical-Fin-inclusion-lc : (m n : ℕ) (l : m ≤ n)
                           → left-cancellable (canonical-Fin-inclusion m n l)

canonical-Fin-inclusion-lc 0        n        l {x}     {y}     p = 𝟘-elim x
canonical-Fin-inclusion-lc (succ m) 0        l {x}     {y}     p = 𝟘-elim l
canonical-Fin-inclusion-lc (succ m) (succ n) l {suc x} {suc y} p = γ
 where
  IH : canonical-Fin-inclusion m n l x ＝ canonical-Fin-inclusion m n l y → x ＝ y
  IH = canonical-Fin-inclusion-lc m n l

  γ : suc x ＝ suc y
  γ = ap suc (IH (inl-lc p))

canonical-Fin-inclusion-lc (succ m) (succ n) l {𝟎} {𝟎} p = refl


≤-gives-↣ : (m n : ℕ) → m ≤ n → (Fin m ↣ Fin n)
≤-gives-↣ m n l = canonical-Fin-inclusion m n l , canonical-Fin-inclusion-lc m n l

\end{code}

An equivalent, shorter construction:

\begin{code}
≤-gives-↣' : (m n : ℕ) → m ≤ n → (Fin m ↣ Fin n)
≤-gives-↣' 0        n        l = unique-from-𝟘 , (λ {x} {x'} p → 𝟘-elim x)
≤-gives-↣' (succ m) 0        l = 𝟘-elim l
≤-gives-↣' (succ m) (succ n) l = g , j
 where
  IH : Fin m ↣ Fin n
  IH = ≤-gives-↣' m n l

  f : Fin m → Fin n
  f = pr₁ IH

  i : left-cancellable f
  i = pr₂ IH

  g : Fin (succ m) → Fin (succ n)
  g = +functor f unique-to-𝟙

  j : left-cancellable g
  j {suc x} {suc x'} p = ap suc (i (inl-lc p))
  j {suc x} {𝟎}      p = 𝟘-elim (+disjoint  p)
  j {𝟎}     {suc y}  p = 𝟘-elim (+disjoint' p)
  j {𝟎}     {𝟎}      p = refl

\end{code}

Added 9th December 2019. A version of the pigeonhole principle, which
uses (one direction of) the above characterization of the relation m ≤ n
as the existence of an injection Fin m → Fin n:

\begin{code}

_has-a-repetition : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
f has-a-repetition = Σ x ꞉ domain f , Σ x' ꞉ domain f , (x ≠ x') × (f x ＝ f x')

pigeonhole-principle : (m n : ℕ) (f : Fin m → Fin n)
                     → m > n → f has-a-repetition
pigeonhole-principle m n f g = γ
 where
  a : ¬ (Σ f ꞉ (Fin m → Fin n), left-cancellable f)
  a = contrapositive (↣-gives-≤ m n) (less-not-bigger-or-equal n m g)

  b : ¬ left-cancellable f
  b l = a (f , l)

  c : ¬ ((i j : Fin m) → f i ＝ f j → i ＝ j)
  c φ = b (λ {i} {j} → φ i j)

  d : ¬¬ (f has-a-repetition)
  d ψ = c δ
   where
    ε : (i j : Fin m) → f i ＝ f j → ¬ (i ≠ j)
    ε i j p ν = ψ (i , j , ν , p)

    δ : (i j : Fin m) → f i ＝ f j → i ＝ j
    δ i j p = ¬¬-elim (Fin-is-discrete i j) (ε i j p)

\end{code}

A classical proof ends at this point. For a constructive proof, we
need more steps.

\begin{code}

  u : (i j : Fin m) → is-decidable ((i ≠ j) × (f i ＝ f j))
  u i j = ×-preserves-decidability
           (¬-preserves-decidability (Fin-is-discrete i j))
           (Fin-is-discrete (f i) (f j))

  v : (i : Fin m) → is-decidable (Σ j ꞉ Fin m , (i ≠ j) × (f i ＝ f j))
  v i = Fin-Compact _ (u i)

  w : is-decidable (f has-a-repetition)
  w = Fin-Compact _ v

  γ : f has-a-repetition
  γ = ¬¬-elim w d

\end{code}

This, of course, doesn't give the most efficient algorithm, but it
does give an algorithm for computing an argument of the function whose
value is repeated.

Example. The pigeonhole principle holds for finite types in the
following form:

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open finiteness pt

 finite-pigeonhole-principle : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                               (φ : is-finite X) (ψ : is-finite Y)
                             → cardinality X φ > cardinality Y ψ
                             → ∥ f has-a-repetition ∥

 finite-pigeonhole-principle {𝓤} {𝓥} {X} {Y} f (m , s) (n , t) b = γ
  where
   h : Fin m ≃ X → Y ≃ Fin n → f has-a-repetition
   h (g , d) (h , e) = r r'
    where
     f' : Fin m → Fin n
     f' = h ∘ f ∘ g

     r' : f' has-a-repetition
     r' = pigeonhole-principle m n f' b

     r : f' has-a-repetition → f has-a-repetition
     r (i , j , u , p) = g i , g j , u' , p'
      where
       u' : g i ≠ g j
       u' = contrapositive (equivs-are-lc g d) u

       p' : f (g i) ＝ f (g j)
       p' = equivs-are-lc h e p

   γ : ∥ f has-a-repetition ∥
   γ = ∥∥-functor₂ h (∥∥-functor ≃-sym s) t

\end{code}

We now assume function extensionality for a while:

\begin{code}

 module _ (fe : FunExt) where

\end{code}

We now consider further variations of the finite pigeonhole principle.

\begin{code}

  repeated-values : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → X → 𝓤 ⊔ 𝓥 ̇
  repeated-values f = λ x → Σ x' ꞉ domain f , (x ≠ x') × (f x ＝ f x')

  repetitions-complemented : {m : ℕ} {Y : 𝓥 ̇ } (f : Fin m → Y)
                         → is-finite Y
                         → is-complemented (repeated-values f)

  repetitions-complemented {𝓥} {m} {Y} f (n , t) i =
   Fin-Compact
    (λ j → (i ≠ j) × (f i ＝ f j))
    (λ j → ×-preserves-decidability
            (¬-preserves-decidability (Fin-is-discrete i j))
            (finite-types-are-discrete pt fe (n , t) (f i) (f j)))

  finite-pigeonhole-principle' : {m : ℕ} {Y : 𝓥 ̇ } (f : Fin m → Y)
                                 (ψ : is-finite Y)
                               → m > cardinality Y ψ
                               → f has-a-repetition

  finite-pigeonhole-principle' {𝓥} {m} {Y} f (n , t) b = γ
   where
    h : Y ≃ Fin n → f has-a-repetition
    h (h , e) = r r'
     where
      f' : Fin m → Fin n
      f' = h ∘ f

      r' : f' has-a-repetition
      r' = pigeonhole-principle m n f' b

      r : f' has-a-repetition → f has-a-repetition
      r (i , j , u , p) = i , j , u , equivs-are-lc h e p

    γ' : ∥ f has-a-repetition ∥
    γ' = ∥∥-functor h t

    A : Fin m → 𝓥 ̇
    A i = Σ j ꞉ Fin m , (i ≠ j) × (f i ＝ f j)

    γ : f has-a-repetition
    γ = Fin-Σ-from-∃ pt fe {m} A (repetitions-complemented f (n , t)) γ'

\end{code}

We can easily derive the construction finite-pigeonhole-principle from
finite-pigeonhole-principle', but at the expense of function
extensionality, which was not needed in our original construction.

Further versions of the pigeonhole principle are the following.

\begin{code}

  finite-pigeonhole-principle'' : {m : ℕ} {Y : 𝓥 ̇ } (f : Fin m → Y)
                                  (φ : is-finite Y)
                                → m > cardinality Y φ
                                → Σ-min λ(i : Fin m) → repeated-values f i

  finite-pigeonhole-principle'' {𝓥} {m} {Y} f φ g =
   Σ-gives-Σ-min
    (repeated-values f)
    (repetitions-complemented f φ)
    (finite-pigeonhole-principle' f φ g)

  ℕ-finite-pigeonhole-principle : {Y : 𝓥 ̇ } (f : ℕ → Y)
                                → is-finite Y
                                → f has-a-repetition

  ℕ-finite-pigeonhole-principle {𝓥} {Y} f (m , t) = r r'
   where
    f' : Fin (succ m) → Y
    f' i = f (⟦_⟧ i)

    r' : f' has-a-repetition
    r' = finite-pigeonhole-principle' f'(m , t) (<-succ m)

    r : f' has-a-repetition → f has-a-repetition
    r (i , j , u , p) = ⟦_⟧ i , ⟦_⟧ j , contrapositive (⟦_⟧-lc (succ m)) u , p

\end{code}

Added 13th December 2019.

A well-known application of the pigeonhole principle is that every
element has a (least) finite order in a finite group. This holds
more generally for any finite type equipped with a left-cancellable
binary operation _·_ and a distinguished element e, with the same
construction.

\begin{code}

  module _ {X : 𝓤 ̇ }
           (φ : is-finite X)
           (_·_ : X → X → X)
           (lc : (x : X) → left-cancellable (x ·_))
           (e : X)
         where

    _↑_ : X → ℕ → X
    x ↑ 0        = e
    x ↑ (succ n) = x · (x ↑ n)

    infixl 3 _↑_

    finite-order : (x : X) → Σ k ꞉ ℕ , x ↑ (succ k) ＝ e
    finite-order x = c a
     where
      a : Σ m ꞉ ℕ , Σ n ꞉ ℕ , (m ≠ n) × (x ↑ m ＝ x ↑ n)
      a = ℕ-finite-pigeonhole-principle (x ↑_) φ

      b : (m : ℕ) (n : ℕ) → m ≠ n → x ↑ m ＝ x ↑ n → Σ k ꞉ ℕ , x ↑ (succ k) ＝ e
      b 0        0        ν p = 𝟘-elim (ν refl)
      b 0        (succ n) ν p = n , (p ⁻¹)
      b (succ m) 0        ν p = m , p
      b (succ m) (succ n) ν p = b m n (λ (q : m ＝ n) → ν (ap succ q)) (lc x p)

      c : type-of a → Σ k ꞉ ℕ , x ↑ (succ k) ＝ e
      c (m , n , ν , p) = b m n ν p

\end{code}

And of course then there is a least such k, by bounded minimization,
because finite types are discrete:

\begin{code}

    least-finite-order : (x : X) → Σμ λ(k : ℕ) → x ↑ (succ k) ＝ e
    least-finite-order x = least-from-given A γ (finite-order x)
     where
      A : ℕ → 𝓤 ̇
      A n = x ↑ (succ n) ＝ e

      γ : (n : ℕ) → is-decidable (x ↑ succ n ＝ e)
      γ n = finite-types-are-discrete pt fe φ (x ↑ succ n) e

\end{code}

Remark: the given construction finite-order already produces the
least order, but it seems slightly more difficult to prove this than
just compute the least order from any order. If we were interested
in the efficiency of our constructions (Agda constructions are
functional programs!), we would have to consider this.
