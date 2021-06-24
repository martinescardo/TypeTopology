Martin Escardo, 2014, 21 March 2018, November-December 2019, March-April 2021

The type Fin n is a discrete set with n elements.

 * The function Fin : ℕ → 𝓤₀ is left-cancellable, or an injection (but
   not an embedding in the sense of univalent mathematics).

 * Exhaustive search over Fin n, or its compactness, finding a minimal
   element with a decidable property.

 * m ≤ n iff there is an injection Fin m → Fin n.

 * Finite types, defined by the unspecified existence of an
   isomorphism with some Fin n.

 * Various forms of the pigeonhole principle, and its application to
   show that every element of a finite group has a finite order.

 * Kuratowski finiteness.

And more.

Other interesting uses of the types Fin n is in the file
https://www.cs.bham.ac.uk/~mhe/TypeTopology/ArithmeticViaEquivalence.html
which proves commutativity of addition and multiplication, and more,
using the corresponding properties for (finite) types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Fin where

open import SpartanMLTT
open import UF-Subsingletons renaming (⊤Ω to ⊤)
open import Plus-Properties

Fin : ℕ → 𝓤₀ ̇
Fin 0        = 𝟘
Fin (succ n) = Fin n + 𝟙

\end{code}

We have zero and successor for finite sets, with the following types:

\begin{code}

fzero : {n : ℕ} → Fin (succ n)
fzero = inr *

fsucc : {n : ℕ} → Fin n → Fin (succ n)
fsucc = inl

suc-lc : {n : ℕ} {j k : Fin n} → fsucc j ≡ fsucc k → j ≡ k
suc-lc = inl-lc

largest : (n : ℕ) → Fin (succ n)
largest zero     = fzero
largest (succ n) = fsucc (largest n)

\end{code}

But it will more convenient to have them as patterns, for the sake of
clarity in definitions by pattern matching:

\begin{code}

pattern 𝟎     = inr *
pattern 𝟏     = inl (inr *)
pattern 𝟐     = inl (inl (inr *))
pattern suc i = inl i

\end{code}

The induction principle for Fin is proved by induction on ℕ:

\begin{code}

Fin-induction : (P : (n : ℕ) → Fin n → 𝓤 ̇ )
              → ((n : ℕ) → P (succ n) 𝟎)
              → ((n : ℕ) (i : Fin n) → P n i → P (succ n) (suc i))
              →  (n : ℕ) (i : Fin n) → P n i

Fin-induction P β σ 0        i       = 𝟘-elim i
Fin-induction P β σ (succ n) 𝟎       = β n
Fin-induction P β σ (succ n) (suc i) = σ n i (Fin-induction P β σ n i)

\end{code}

We will not use this induction principle explicitly. Instead, we will
use the above pattern for similar definitions by induction.

\begin{code}

Fin0-is-empty : is-empty (Fin 0)
Fin0-is-empty i = i

Fin1-is-singleton : is-singleton (Fin 1)
Fin1-is-singleton = 𝟎 , γ
 where
  γ : (i : Fin 1) → 𝟎 ≡ i
  γ 𝟎 = refl

Fin0-is-prop : is-prop (Fin 0)
Fin0-is-prop i = 𝟘-elim i

Fin1-is-prop : is-prop (Fin 1)
Fin1-is-prop 𝟎 𝟎 = refl

open import Unit-Properties

positive-not-𝟎 : {n : ℕ} {x : Fin (succ n)} → suc x ≢ 𝟎
positive-not-𝟎 {n} {x} p = 𝟙-is-not-𝟘 (g p)
 where
  f : Fin (succ (succ n)) → 𝓤₀ ̇
  f 𝟎       = 𝟘
  f (suc x) = 𝟙

  g : suc x ≡ 𝟎 → 𝟙 ≡ 𝟘
  g = ap f

when-Fin-is-prop : (n : ℕ) → is-prop (Fin n) → (n ≡ 0) + (n ≡ 1)
when-Fin-is-prop 0               i = inl refl
when-Fin-is-prop 1               i = inr refl
when-Fin-is-prop (succ (succ n)) i = 𝟘-elim (positive-not-𝟎 (i 𝟏 𝟎))

\end{code}

The left cancellability of Fin uses the construction +𝟙-cancellable
defined in the module PlusOneLC.lagda.

\begin{code}

open import PlusOneLC
open import UF-Equiv

Fin-lc : (m n : ℕ) → Fin m ≃ Fin n → m ≡ n
Fin-lc 0           0       p = refl
Fin-lc (succ m)    0       p = 𝟘-elim (⌜ p ⌝ 𝟎)
Fin-lc 0          (succ n) p = 𝟘-elim (⌜ p ⌝⁻¹ 𝟎)
Fin-lc (succ m)   (succ n) p = ap succ r
 where
  IH : Fin m ≃ Fin n → m ≡ n
  IH = Fin-lc m n

  remark : Fin m + 𝟙 ≃ Fin n + 𝟙
  remark = p

  q : Fin m ≃ Fin n
  q = +𝟙-cancellable p

  r : m ≡ n
  r = IH q

\end{code}

Notice that Fin is an example of a map that is left-cancellable but
not an embedding in the sense of univalent mathematics.

Recall that a type is discrete if it has decidable equality.

\begin{code}

open import DiscreteAndSeparated

Fin-is-discrete : (n : ℕ) → is-discrete (Fin n)
Fin-is-discrete 0        = 𝟘-is-discrete
Fin-is-discrete (succ n) = +discrete (Fin-is-discrete n) 𝟙-is-discrete

open import UF-Miscelanea

Fin-is-set : (n : ℕ) → is-set (Fin n)
Fin-is-set n = discrete-types-are-sets (Fin-is-discrete n)

\end{code}

Added November 2019. The type Fin n is compact, or exhaustively
searchable.

\begin{code}

open import CompactTypes

Fin-Compact : (n : ℕ) → Compact (Fin n) {𝓤}
Fin-Compact 0        = 𝟘-Compact
Fin-Compact (succ n) = +-Compact (Fin-Compact n) 𝟙-Compact


Fin-Π-Compact : (n : ℕ) → Π-Compact (Fin n) {𝓤}
Fin-Π-Compact n = Σ-Compact-gives-Π-Compact (Fin n) (Fin-Compact n)


Fin-Compact∙ : (n : ℕ) → Compact∙ (Fin (succ n)) {𝓤}
Fin-Compact∙ n = Compact-pointed-gives-Compact∙ (Fin-Compact (succ n)) 𝟎

\end{code}

Recall that X ↣ Y is the type of left cancellable maps from X to Y,
which should not be confused with the type X ↪ Y of embeddings of X
into Y. However, for types that are sets, like Fin n, there is no
difference between the embedding property and left cancellability.

\begin{code}

open import Swap
open import UF-LeftCancellable

+𝟙-cancel-lemma : {X Y : 𝓤 ̇ }
                → (𝒇 : X + 𝟙 ↣ Y + 𝟙)
                → ⌈ 𝒇 ⌉ 𝟎 ≡ 𝟎
                → X ↣ Y

+𝟙-cancel-lemma {𝓤} {X} {Y} (f , l) p = g , m
 where
  g : X → Y
  g x = pr₁ (inl-preservation {𝓤} {𝓤} {𝓤} {𝓤} f p l x)

  a : (x : X) → f (suc x) ≡ suc (g x)
  a x = pr₂ (inl-preservation f p l x)

  m : left-cancellable g
  m {x} {x'} p = q
   where
    r = f (suc x)  ≡⟨ a x ⟩
        suc (g x)  ≡⟨ ap suc p ⟩
        suc (g x') ≡⟨ (a x')⁻¹ ⟩
        f (suc x') ∎

    q : x ≡ x'
    q = inl-lc (l r)


+𝟙-cancel : {X Y : 𝓤 ̇ }
          → is-discrete Y
          → X + 𝟙 ↣ Y + 𝟙
          → X ↣ Y

+𝟙-cancel {𝓤} {X} {Y} i (f , e) = a
 where
  h : Y + 𝟙 → Y + 𝟙
  h = swap (f 𝟎) 𝟎 (+discrete i 𝟙-is-discrete (f 𝟎)) new-point-is-isolated

  d : left-cancellable h
  d = equivs-are-lc h (swap-is-equiv (f 𝟎) 𝟎 (+discrete i 𝟙-is-discrete (f 𝟎)) new-point-is-isolated)

  f' : X + 𝟙 → Y + 𝟙
  f' = h ∘ f

  e' : left-cancellable f'
  e' = left-cancellable-closed-under-∘ f h e d

  p : f' 𝟎 ≡ 𝟎
  p = swap-equation₀ (f 𝟎) 𝟎 (+discrete i 𝟙-is-discrete (f 𝟎)) new-point-is-isolated

  a : X ↣ Y
  a = +𝟙-cancel-lemma (f' , e') p

open import NaturalsOrder
open import UF-EquivalenceExamples

\end{code}

In set theory, natural numbers are defined as certain sets, and their
order relation is inherited from the ordering of sets defined by the
existence of injections, or left-cancellable maps. Here, in type
theory, we have defined m ≤ n by induction on m and n, in the style of
Peano Arithmetic, but we can prove that this relation is characterized
by this injection property:

\begin{code}

↣-gives-≤ : (m n : ℕ) → (Fin m ↣ Fin n) → m ≤ n
↣-gives-≤ 0        n        e       = zero-minimal n
↣-gives-≤ (succ m) 0        (f , i) = 𝟘-elim (f 𝟎)
↣-gives-≤ (succ m) (succ n) e       = ↣-gives-≤ m n (+𝟙-cancel (Fin-is-discrete n) e)


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
  IH : canonical-Fin-inclusion m n l x ≡ canonical-Fin-inclusion m n l y → x ≡ y
  IH = canonical-Fin-inclusion-lc m n l

  γ : suc x ≡ suc y
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
f has-a-repetition = Σ x ꞉ domain f , Σ x' ꞉ domain f , (x ≢ x') × (f x ≡ f x')

pigeonhole-principle : (m n : ℕ) (f : Fin m → Fin n)
                     → m > n → f has-a-repetition
pigeonhole-principle m n f g = γ
 where
  a : ¬ (Σ f ꞉ (Fin m → Fin n), left-cancellable f)
  a = contrapositive (↣-gives-≤ m n) (less-not-bigger-or-equal n m g)

  b : ¬ left-cancellable f
  b l = a (f , l)

  c : ¬ ((i j : Fin m) → f i ≡ f j → i ≡ j)
  c φ = b (λ {i} {j} → φ i j)

  d : ¬¬ (f has-a-repetition)
  d ψ = c δ
   where
    ε : (i j : Fin m) → f i ≡ f j → ¬ (i ≢ j)
    ε i j p ν = ψ (i , j , ν , p)

    δ : (i j : Fin m) → f i ≡ f j → i ≡ j
    δ i j p = ¬¬-elim (Fin-is-discrete m i j) (ε i j p)

\end{code}

A classical proof ends at this point. For a constructive proof, we
need more steps.

\begin{code}

  u : (i j : Fin m) → decidable ((i ≢ j) × (f i ≡ f j))
  u i j = ×-preserves-decidability
           (¬-preserves-decidability (Fin-is-discrete m i j))
           (Fin-is-discrete n (f i) (f j))

  v : (i : Fin m) → decidable (Σ j ꞉ Fin m , (i ≢ j) × (f i ≡ f j))
  v i = Fin-Compact m _ (u i)

  w : decidable (f has-a-repetition)
  w = Fin-Compact m _ v

  γ : f has-a-repetition
  γ = ¬¬-elim w d

\end{code}

This, of course, doesn't give the most efficient algorithm, but it
does give an algorithm for computing an argument of the function whose
value is repeated.

Added 2nd December 2019. An isomorphic copy of the type Fin n:

\begin{code}

Fin' : ℕ → 𝓤₀ ̇
Fin' n = Σ k ꞉ ℕ , k < n

𝟎' : {n : ℕ} → Fin' (succ n)
𝟎' {n} = 0 , zero-minimal n

suc' : {n : ℕ} → Fin' n → Fin' (succ n)
suc' (k , l) = succ k , l

Fin-unprime : (n : ℕ) → Fin' n → Fin n
Fin-unprime 0        (k , l)      = 𝟘-elim l
Fin-unprime (succ n) (0 , l)      = 𝟎
Fin-unprime (succ n) (succ k , l) = suc (Fin-unprime n (k , l))

Fin-prime : (n : ℕ) → Fin n → Fin' n
Fin-prime 0        i       = 𝟘-elim i
Fin-prime (succ n) (suc i) = suc' (Fin-prime n i)
Fin-prime (succ n) 𝟎       = 𝟎'

ηFin : (n : ℕ) → Fin-prime n ∘ Fin-unprime n ∼ id
ηFin 0        (k , l)      = 𝟘-elim l
ηFin (succ n) (0 , *)      = refl
ηFin (succ n) (succ k , l) = ap suc' (ηFin n (k , l))


εFin : (n : ℕ) → Fin-unprime n ∘ Fin-prime n ∼ id
εFin 0        i       = 𝟘-elim i
εFin (succ n) (suc i) = ap suc (εFin n i)
εFin (succ n) 𝟎       = refl

Fin-prime-is-equiv : (n : ℕ) → is-equiv (Fin-prime n)
Fin-prime-is-equiv n = qinvs-are-equivs (Fin-prime n)
                        (Fin-unprime n , εFin n , ηFin n)


≃-Fin : (n : ℕ) → Fin n ≃ Fin' n
≃-Fin n = Fin-prime n , Fin-prime-is-equiv n

\end{code}

Added 10th Dec 2019. We define the natural order of Fin n by reduction
to the natural order of ℕ so that the canonical embedding Fin n → ℕ is
order preserving and reflecting, using the above isomorphic
manifestation of the type Fin n.

\begin{code}

open import NaturalNumbers-Properties

Fin↦ℕ : {n : ℕ} → Fin n → ℕ
Fin↦ℕ {n} = pr₁ ∘ Fin-prime n

Fin↦ℕ-property : {n : ℕ} (i : Fin n) → Fin↦ℕ i < n
Fin↦ℕ-property {n} i = pr₂ (Fin-prime n i)

open import UF-Embeddings

Fin↦ℕ-is-embedding : (n : ℕ) → is-embedding (Fin↦ℕ {n})
Fin↦ℕ-is-embedding n = ∘-is-embedding
                        (equivs-are-embeddings (Fin-prime n) (Fin-prime-is-equiv n))
                        (pr₁-is-embedding (λ i → <-is-prop-valued i n))


Fin↦ℕ-lc : (n : ℕ) → left-cancellable (Fin↦ℕ {n})
Fin↦ℕ-lc n = embeddings-are-lc Fin↦ℕ (Fin↦ℕ-is-embedding n)

Fin< : {n : ℕ} → Fin n → Set
Fin< i = Fin (Fin↦ℕ i)

coerce : {n : ℕ} {i : Fin n} → Fin< i → Fin n
coerce {succ n} {suc i} 𝟎       = 𝟎
coerce {succ n} {suc i} (suc j) = suc (coerce j)

coerce-lc : {n : ℕ} {i : Fin n} (j k : Fin< i)
          → coerce {n} {i} j ≡ coerce {n} {i} k → j ≡ k
coerce-lc {succ n} {suc i} 𝟎       𝟎       p = refl
coerce-lc {succ n} {suc i} 𝟎       (suc j) p = 𝟘-elim (+disjoint' p)
coerce-lc {succ n} {suc i} (suc j) 𝟎       p = 𝟘-elim (+disjoint p)
coerce-lc {succ n} {suc i} (suc j) (suc k) p = ap suc (coerce-lc {n} j k (suc-lc p))

_≺_ _≼_ : {n : ℕ} → Fin n → Fin n → 𝓤₀ ̇
i ≺ j = Fin↦ℕ i < Fin↦ℕ j
i ≼ j = Fin↦ℕ i ≤ Fin↦ℕ j


_is-lower-bound-of_ : {n : ℕ} → Fin n → (Fin n → 𝓤 ̇ ) → 𝓤 ̇
i is-lower-bound-of A = ∀ j → A j → i ≼ j


lower-bounds-of : {n : ℕ} → (Fin n → 𝓤 ̇ ) → Fin n → 𝓤 ̇
lower-bounds-of A = λ i → i is-lower-bound-of A


_is-upper-bound-of_ : {n : ℕ} → Fin n → (Fin n → 𝓤 ̇ )  → 𝓤 ̇
i is-upper-bound-of A = ∀ j → A j → j ≼ i


_is-inf-of_ : {n : ℕ} → Fin n → (Fin n → 𝓤 ̇ ) → 𝓤 ̇
i is-inf-of A = i is-lower-bound-of A
              × i is-upper-bound-of (lower-bounds-of A)


inf-is-lb : {n : ℕ} (i : Fin n) (A : Fin n → 𝓤 ̇ )
          → i is-inf-of A → i is-lower-bound-of A

inf-is-lb i A = pr₁


inf-is-ub-of-lbs : {n : ℕ} (i : Fin n) (A : Fin n → 𝓤 ̇ )
                 → i is-inf-of A → i is-upper-bound-of (lower-bounds-of A)

inf-is-ub-of-lbs i A = pr₂


inf-construction : {n : ℕ} (A : Fin (succ n) → 𝓤 ̇ )
                 → detachable A
                 → Σ i ꞉ Fin (succ n) , i is-inf-of A × (Σ A → A i)

inf-construction {𝓤} {zero} A δ = 𝟎 , (l , m) , ε
 where
  l : 𝟎 is-lower-bound-of A
  l 𝟎       _ = ≤-refl 0
  l (suc i) _ = 𝟘-elim i

  m : (j : Fin 1) → j is-lower-bound-of A → j ≼ 𝟎
  m 𝟎       _ = ≤-refl 0
  m (suc i) _ = 𝟘-elim i

  ε : Σ A → A 𝟎
  ε (𝟎 , a)     = a
  ε (suc i , a) = 𝟘-elim i

inf-construction {𝓤} {succ n} A δ = γ (δ 𝟎)
 where
  IH : Σ i ꞉ Fin (succ n) , i is-inf-of (A ∘ suc) × ((Σ j ꞉ Fin (succ n) , A (suc j)) → A (suc i))
  IH = inf-construction {𝓤} {n} (A ∘ suc) (δ ∘ suc)

  i : Fin (succ n)
  i = pr₁ IH

  l : (j : Fin (succ n)) → A (suc j) → i ≼ j
  l = inf-is-lb i (A ∘ suc) (pr₁ (pr₂ IH))

  u : (j : Fin (succ n)) → ((k : Fin (succ n)) → A (suc k) → j ≼ k) → j ≼ i
  u = inf-is-ub-of-lbs i (A ∘ suc) (pr₁ (pr₂ IH))

  γ : decidable (A 𝟎) → Σ i' ꞉ Fin (succ (succ n)) , i' is-inf-of A × (Σ A → A i')
  γ (suc a) = 𝟎 , (φ , ψ) , ε
    where
     φ : (j : Fin (succ (succ n))) → A j → 𝟎 ≼ j
     φ j b = zero-minimal (Fin↦ℕ j)

     ψ : (j : Fin (succ (succ n))) → j is-lower-bound-of A → j ≼ 𝟎
     ψ j l = l 𝟎 a

     ε : Σ A → A 𝟎
     ε _ = a

  γ (inr ν) = suc i , (φ , ψ) , ε
    where
     φ : (j : Fin (succ (succ n))) → A j → suc i ≼ j
     φ 𝟎 a = 𝟘-elim (ν a)
     φ (suc j) a = l j a

     ψ : (j : Fin (succ (succ n))) → j is-lower-bound-of A → j ≼ suc i
     ψ 𝟎 l = zero-minimal (Fin↦ℕ i)
     ψ (suc j) l = u j (l ∘ suc)

     ε : Σ A → A (suc i)
     ε (𝟎 , b)     = 𝟘-elim (ν b)
     ε (suc j , b) = pr₂ (pr₂ IH) (j , b)


inf : {n : ℕ} (A : Fin (succ n) → 𝓤 ̇ ) → detachable A → Fin (succ n)
inf A δ = pr₁ (inf-construction A δ)


inf-property : {n : ℕ} (A : Fin (succ n) → 𝓤 ̇ ) (δ : detachable A)
             → (inf A δ) is-inf-of A

inf-property A δ = pr₁ (pr₂ (inf-construction A δ))


inf-is-attained : {n : ℕ} (A : Fin (succ n) → 𝓤 ̇ ) (δ : detachable A)
                → Σ A → A (inf A δ)

inf-is-attained A δ = pr₂ (pr₂ (inf-construction A δ))


Σₘᵢₙ : {n : ℕ} → (Fin n → 𝓤 ̇ ) → 𝓤 ̇
Σₘᵢₙ {𝓤} {n} A = Σ i ꞉ Fin n , A i × (i is-lower-bound-of A)

Σₘᵢₙ-gives-Σ : {n : ℕ} (A : Fin n → 𝓤 ̇ )
             → Σₘᵢₙ A → Σ A

Σₘᵢₙ-gives-Σ A (i , a , _) = (i , a)


Σ-gives-Σₘᵢₙ : {n : ℕ} (A : Fin n → 𝓤 ̇ )
             → detachable A → Σ A → Σₘᵢₙ A

Σ-gives-Σₘᵢₙ {𝓤} {0}      A δ (i , a) = 𝟘-elim i
Σ-gives-Σₘᵢₙ {𝓤} {succ n} A δ σ       = inf A δ ,
                                        inf-is-attained A δ σ ,
                                        inf-is-lb (inf A δ) A (inf-property A δ)


¬¬Σ-gives-Σₘᵢₙ : {n : ℕ} (A : Fin n → 𝓤 ̇ )
               → detachable A → ¬¬ Σ A → Σₘᵢₙ A

¬¬Σ-gives-Σₘᵢₙ {𝓤} {n} A δ u = Σ-gives-Σₘᵢₙ A δ (¬¬-elim (Fin-Compact n A δ) u)


is-prop-valued : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-prop-valued A = ∀ x → is-prop (A x)

open import UF-FunExt
open import UF-Subsingletons-FunExt
open import UF-Base

Σₘᵢₙ-is-prop : FunExt
             → {n : ℕ} (A : Fin n → 𝓤 ̇ )
             → is-prop-valued A → is-prop (Σₘᵢₙ A)

Σₘᵢₙ-is-prop {𝓤} fe {n} A h (i , a , l) (i' , a' , l') = γ
 where
  p : i ≡ i'
  p = Fin↦ℕ-lc n (≤-anti (Fin↦ℕ i) (Fin↦ℕ i') u v)
   where
    u : i ≼ i'
    u = l i' a'

    v : i' ≼ i
    v = l' i a

  H : ∀ j → is-prop (A j × (j is-lower-bound-of A))
  H j = ×-is-prop
         (h j)
         (Π-is-prop (fe 𝓤₀ 𝓤)
           (λ k → Π-is-prop (fe 𝓤 𝓤₀)
                   (λ b → ≤-is-prop-valued (Fin↦ℕ j) (Fin↦ℕ k))))

  γ : i , a , l ≡ i' , a' , l'
  γ = to-Σ-≡ (p , H _ _ _)

\end{code}

Added 8th December 2019. One defines a type to be finite, in univalent
mathematics, if it is isomorphic to Fin n for some n. But one has to
be careful to express this, if we want finiteness to be property
rather than structure, with a suitably chosen notion of existence.

The following is structure rather than property. It amounts to the
type of finite linear orders on X.

\begin{code}

finite-linear-order : 𝓤 ̇ → 𝓤 ̇
finite-linear-order X = Σ n ꞉ ℕ , X ≃ Fin n

\end{code}

Exercise: If X ≃ Fin n, then the type Finite X has n! elements (solved
elsewhere in TypeTopology).

\begin{code}

open import UF-Univalence
open import UF-Equiv-FunExt
open import UF-UniverseEmbedding
open import UF-UA-FunExt

type-of-linear-orders-is-ℕ : Univalence → (Σ X ꞉ 𝓤 ̇ , finite-linear-order X) ≃ ℕ
type-of-linear-orders-is-ℕ {𝓤} ua =
  (Σ X ꞉ 𝓤 ̇ , Σ n ꞉ ℕ , X ≃ Fin n)          ≃⟨ i ⟩
  (Σ X ꞉ 𝓤 ̇ , Σ n ꞉ ℕ , Fin n ≃ X)          ≃⟨ ii ⟩
  (Σ X ꞉ 𝓤 ̇ , Σ n ꞉ ℕ , Lift 𝓤 (Fin n) ≃ X) ≃⟨ iii ⟩
  (Σ X ꞉ 𝓤 ̇ , Σ n ꞉ ℕ , Lift 𝓤 (Fin n) ≡ X) ≃⟨ iv ⟩
  ℕ                                         ■
 where
  fe : FunExt
  fe = Univalence-gives-FunExt ua

  i   = Σ-cong (λ X → Σ-cong (λ n → ≃-Sym fe))
  ii  = Σ-cong (λ X → Σ-cong (λ n → ≃-Comp fe X (Lift-≃ 𝓤 (Fin n))))
  iii = Σ-cong (λ X → Σ-cong (λ n → ≃-sym (univalence-≃ (ua 𝓤) (Lift 𝓤 (Fin n)) X)))
  iv  = total-fiber-is-domain (Lift 𝓤 ∘ Fin)

\end{code}

Hence one considers the following notion of finiteness, which is
property rather than structure:

\begin{code}

open import UF-PropTrunc

module finiteness (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt public

 _has-cardinality_ : 𝓤 ̇ → ℕ → 𝓤 ̇
 X has-cardinality n = ∥ X ≃ Fin n ∥

 is-finite : 𝓤 ̇ → 𝓤 ̇
 is-finite X = Σ n ꞉ ℕ , X has-cardinality n

 cardinality : (X : 𝓤 ̇ ) → is-finite X → ℕ
 cardinality X = pr₁

 cardinality-≃ : (X : 𝓤 ̇ ) (φ : is-finite X) → X has-cardinality (cardinality X φ)
 cardinality-≃ X = pr₂

 being-finite-is-prop : (X : 𝓤 ̇ ) → is-prop (is-finite X)
 being-finite-is-prop X (m , d) (n , e) = γ
  where
   α : (m n : ℕ) → X ≃ Fin m → X ≃ Fin n → m ≡ n
   α m n d e = Fin-lc m n (≃-sym d ● e)

   β : (m n : ℕ) → ∥ X ≃ Fin m ∥ → ∥ X ≃ Fin n ∥ → m ≡ n
   β m n = ∥∥-rec₂ ℕ-is-set (α m n)

   γ : m , d ≡ n , e
   γ = to-Σ-≡ (β m n d e , ∥∥-is-prop _ _)

\end{code}

Equivalently, one can define finiteness as follows, with the
truncation outside the Σ:

\begin{code}

 is-finite' : 𝓤 ̇ → 𝓤 ̇
 is-finite' X = ∃ n ꞉ ℕ , X ≃ Fin n

 being-finite'-is-prop : (X : 𝓤 ̇ ) → is-prop (is-finite' X)
 being-finite'-is-prop X = ∃-is-prop

 finite'-gives-finite : (X : 𝓤 ̇ ) → is-finite' X → is-finite X
 finite'-gives-finite X = ∥∥-rec (being-finite-is-prop X) γ
  where
   γ : (Σ n ꞉ ℕ , X ≃ Fin n) → Σ n ꞉ ℕ , ∥ X ≃ Fin n ∥
   γ (n , e) = n , ∣ e ∣

 finite-gives-finite' : (X : 𝓤 ̇ ) → is-finite X → is-finite' X
 finite-gives-finite' X (n , s) = ∥∥-rec ∥∥-is-prop (λ e → ∣ n , e ∣) s

\end{code}

Finite types are compact, or exhaustively searchable.

\begin{code}

 open CompactTypesPT pt

 finite-∥Compact∥ : {X : 𝓤 ̇ } → is-finite X → ∥ Compact X {𝓥} ∥
 finite-∥Compact∥ {𝓤} {𝓥} {X} (n , α) =
  ∥∥-functor (λ (e : X ≃ Fin n) → Compact-closed-under-≃ (≃-sym e) (Fin-Compact n)) α

 finite-types-are-∃-Compact : Fun-Ext → {X : 𝓤 ̇ } → is-finite X → ∃-Compact X {𝓥}
 finite-types-are-∃-Compact fe φ = ∥Compact∥-gives-∃-Compact fe (finite-∥Compact∥ φ)

 finite-propositions-are-decidable' : Fun-Ext
                                    → {P : 𝓤 ̇ }
                                    → is-prop P
                                    → is-finite P
                                    → decidable P
 finite-propositions-are-decidable' fe i j =
  ∃-Compact-propositions-are-decidable i (finite-types-are-∃-Compact fe j)

\end{code}

But function extensionality is not needed:

\begin{code}

 finite-propositions-are-decidable : {P : 𝓤 ̇ }
                                   → is-prop P
                                   → is-finite P
                                   → decidable P
 finite-propositions-are-decidable {𝓤} {P} i (0 , s) = inr γ
  where
   γ : P → 𝟘
   γ p = ∥∥-rec 𝟘-is-prop (λ (f , _) → f p) s

 finite-propositions-are-decidable {𝓤} {P} i (succ n , s) = inl γ
  where
   γ : P
   γ = ∥∥-rec i (λ 𝕗 → ⌜ 𝕗 ⌝⁻¹ 𝟎) s

 open import UF-ExcludedMiddle

 summands-of-finite-sum-always-finite-gives-EM :

   ((𝓤 𝓥 : Universe) (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
          → is-finite (Σ A)
          → (x : X) → is-finite (A x))

  → (𝓦 : Universe) → funext 𝓦 𝓦 → propext 𝓦 → EM 𝓦
 summands-of-finite-sum-always-finite-gives-EM ϕ 𝓦 fe pe P i = γ
  where
   X : 𝓦 ⁺ ̇
   X = Ω 𝓦

   A : X → 𝓦 ̇
   A p = p holds

   e : Σ A ≃ (Σ P ꞉ 𝓦 ̇ , is-prop P × P)
   e = Σ-assoc

   s : is-singleton (Σ A)
   s = equiv-to-singleton e (the-true-props-form-a-singleton-type fe pe)

   f : Σ A ≃ Fin 1
   f = singleton-≃ s Fin1-is-singleton

   j : is-finite (Σ A)
   j = 1 , ∣ f ∣

   k : is-finite P
   k = ϕ (𝓦 ⁺) 𝓦 X A j (P , i)

   γ : P + ¬ P
   γ = finite-propositions-are-decidable i k

\end{code}

Finite types are discrete and hence sets:

\begin{code}

 finite-types-are-discrete : FunExt → {X : 𝓤 ̇ } → is-finite X → is-discrete X
 finite-types-are-discrete fe {X} (n , s) = ∥∥-rec (being-discrete-is-prop fe) γ s
  where
   γ : X ≃ Fin n → is-discrete X
   γ (f , e) = lc-maps-reflect-discreteness f (equivs-are-lc f e) (Fin-is-discrete n)

 finite-types-are-sets : FunExt → {X : 𝓤 ̇ } → is-finite X → is-set X
 finite-types-are-sets fe φ = discrete-types-are-sets (finite-types-are-discrete fe φ)

\end{code}

Example. The pigeonhole principle holds for finite types in the
following form:

\begin{code}

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
       u' : g i ≢ g j
       u' = contrapositive (equivs-are-lc g d) u

       p' : f (g i) ≡ f (g j)
       p' = equivs-are-lc h e p

   γ : ∥ f has-a-repetition ∥
   γ = ∥∥-functor₂ h (∥∥-functor ≃-sym s) t

\end{code}

We now consider a situation in which anonymous existence gives
explicit existence:

\begin{code}

 Σₘᵢₙ-from-∃ : FunExt → {n : ℕ} (A : Fin n → 𝓤 ̇ )
             → detachable A → is-prop-valued A → ∃ A → Σₘᵢₙ A

 Σₘᵢₙ-from-∃ fe A δ h = ∥∥-rec (Σₘᵢₙ-is-prop fe A h) (Σ-gives-Σₘᵢₙ A δ)

 Fin-Σ-from-∃' : FunExt → {n : ℕ} (A : Fin n → 𝓤 ̇ )
               → detachable A → is-prop-valued A → ∃ A → Σ A

 Fin-Σ-from-∃' fe A δ h e = Σₘᵢₙ-gives-Σ A (Σₘᵢₙ-from-∃ fe A δ h e)

\end{code}

But the prop-valuedness of A is actually not needed, with more work:

\begin{code}

 Fin-Σ-from-∃ : FunExt
              → {n : ℕ} (A : Fin n → 𝓤 ̇ )
              → detachable A → ∃ A → Σ A

 Fin-Σ-from-∃ {𝓤} fe {n} A δ e = γ
  where
   A' : Fin n → 𝓤 ̇
   A' x = ∥ A x ∥

   δ' : detachable A'
   δ' x = d (δ x)
    where
     d : decidable (A x) → decidable (A' x)
     d (inl a) = inl ∣ a ∣
     d (inr u) = inr (∥∥-rec 𝟘-is-prop u)

   f : Σ A → Σ A'
   f (x , a) = x , ∣ a ∣

   e' : ∃ A'
   e' = ∥∥-functor f e

   σ' : Σ A'
   σ' = Fin-Σ-from-∃' fe A' δ' (λ x → ∥∥-is-prop) e'

   g : Σ A' → Σ A
   g (x , a') = x , ¬¬-elim (δ x) (λ (u : ¬ A x) → ∥∥-rec 𝟘-is-prop u a')

   γ : Σ A
   γ = g σ'

\end{code}

We now assume function extensionality for a while:

\begin{code}

 module _ (fe : FunExt) where

\end{code}

We now consider further variations of the finite pigeonhole principle.

\begin{code}

  repeated-values : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → X → 𝓤 ⊔ 𝓥 ̇
  repeated-values f = λ x → Σ x' ꞉ domain f , (x ≢ x') × (f x ≡ f x')

  repetitions-detachable : {m : ℕ} {Y : 𝓥 ̇ } (f : Fin m → Y)
                         → is-finite Y
                         → detachable (repeated-values f)

  repetitions-detachable {𝓥} {m} {Y} f (n , t) i =
   Fin-Compact m
    (λ j → (i ≢ j) × (f i ≡ f j))
    (λ j → ×-preserves-decidability
            (¬-preserves-decidability (Fin-is-discrete m i j))
            (finite-types-are-discrete fe (n , t) (f i) (f j)))

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
    A i = Σ j ꞉ Fin m , (i ≢ j) × (f i ≡ f j)

    γ : f has-a-repetition
    γ = Fin-Σ-from-∃ fe {m} A (repetitions-detachable f (n , t)) γ'

\end{code}

We can easily derive the construction finite-pigeonhole-principle from
finite-pigeonhole-principle', but at the expense of function
extensionality, which was not needed in our original construction.

Further versions of the pigeonhole principle are the following.

\begin{code}

  finite-pigeonhole-principle'' : {m : ℕ} {Y : 𝓥 ̇ } (f : Fin m → Y)
                                  (φ : is-finite Y)
                                → m > cardinality Y φ
                                → Σₘᵢₙ λ(i : Fin m) → repeated-values f i

  finite-pigeonhole-principle'' {𝓥} {m} {Y} f φ g =
   Σ-gives-Σₘᵢₙ
    (repeated-values f)
    (repetitions-detachable f φ)
    (finite-pigeonhole-principle' f φ g)

  ℕ-finite-pigeonhole-principle : {Y : 𝓥 ̇ } (f : ℕ → Y)
                                → is-finite Y
                                → f has-a-repetition

  ℕ-finite-pigeonhole-principle {𝓥} {Y} f (m , t) = r r'
   where
    f' : Fin (succ m) → Y
    f' i = f (Fin↦ℕ i)

    r' : f' has-a-repetition
    r' = finite-pigeonhole-principle' f'(m , t) (<-succ m)

    r : f' has-a-repetition → f has-a-repetition
    r (i , j , u , p) = Fin↦ℕ i , Fin↦ℕ j , contrapositive (Fin↦ℕ-lc (succ m)) u , p

\end{code}

Added 13th December 2019.

A well-known application of the pigeonhole principle is that every
element has a (minimal) finite order in a finite group. This holds
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

    finite-order : (x : X) → Σ k ꞉ ℕ , x ↑ (succ k) ≡ e
    finite-order x = c a
     where
      a : Σ m ꞉ ℕ , Σ n ꞉ ℕ , (m ≢ n) × (x ↑ m ≡ x ↑ n)
      a = ℕ-finite-pigeonhole-principle (x ↑_) φ

      b : (m : ℕ) (n : ℕ) → m ≢ n → x ↑ m ≡ x ↑ n → Σ k ꞉ ℕ , x ↑ (succ k) ≡ e
      b 0        0        ν p = 𝟘-elim (ν refl)
      b 0        (succ n) ν p = n , (p ⁻¹)
      b (succ m) 0        ν p = m , p
      b (succ m) (succ n) ν p = b m n (λ (q : m ≡ n) → ν (ap succ q)) (lc x p)

      c : type-of a → Σ k ꞉ ℕ , x ↑ (succ k) ≡ e
      c (m , n , ν , p) = b m n ν p

\end{code}

And of course then there is a minimal such k, by bounded minimization,
because finite types are discrete:

\begin{code}

    minimal-finite-order : (x : X) → Σμ λ(k : ℕ) → x ↑ (succ k) ≡ e
    minimal-finite-order x = minimal-from-given A γ (finite-order x)
     where
      A : ℕ → 𝓤 ̇
      A n = x ↑ (succ n) ≡ e

      γ : (n : ℕ) → decidable (x ↑ succ n ≡ e)
      γ n = finite-types-are-discrete fe φ (x ↑ succ n) e

\end{code}

Remark: the given construction finite-order already produces the
minimal order, but it seems slightly more difficult to prove this than
just compute the minimal order from any order. If we were interested
in the efficiency of our constructions (Agda constructions are
functional programs!), we would have to consider this.

Added 15th December 2019.

If the type X i is compact for every i : Fin n, then the product type
(i : Fin n) → X i is also compact.

For that purpose we first consider generalized vector types.

\begin{code}

vec : (n : ℕ) → (Fin n → 𝓤 ̇ ) → 𝓤 ̇
vec 0        X = 𝟙
vec (succ n) X = X 𝟎 × vec n (X ∘ suc)

Vec : 𝓤 ̇ → ℕ → 𝓤 ̇
Vec X n = vec n (λ _ → X)

List : 𝓤 ̇ → 𝓤 ̇
List X = Σ n ꞉ ℕ , Vec X n

length : {X : 𝓤 ̇ } → List X → ℕ
length = pr₁

pattern [] = (0 , *)

_∷_ : {X : 𝓤 ̇ } → X → List X → List X
x ∷ (n , s) = succ n , x , s

[_] : {X : 𝓤 ̇ } → X → List X
[ x ] = x ∷ []

\end{code}

Our list encoding satisfies Martin-Löf's rules for lists:

\begin{code}

List-induction : {X : 𝓤 ̇ } (P : List X → 𝓥 ̇ )
               → P []
               → ((x : X) (xs : List X) → P xs → P (x ∷ xs))
               → (xs : List X) → P xs
List-induction {𝓤} {𝓥} {X} P p f = h
 where
  h : (xs : List X) → P xs
  h []               = p
  h (succ n , x , s) = f x (n , s) (h (n , s))

\end{code}

With the computation rules holding definitionally, as required:

\begin{code}

List-induction-[] : {X : 𝓤 ̇ } (P : List X → 𝓥 ̇ )
               → (p : P [])
               → (f : (x : X) (xs : List X) → P xs → P (x ∷ xs))
               → List-induction P p f [] ≡ p
List-induction-[] {𝓤} {𝓥} {X} P p f = refl

List-induction-∷ : {X : 𝓤 ̇ } (P : List X → 𝓥 ̇ )
               → (p : P [])
               → (f : (x : X) (xs : List X) → P xs → P (x ∷ xs))
               → (x : X)
               → (xs : List X)
               → List-induction P p f (x ∷ xs) ≡ f x xs (List-induction P p f xs)
List-induction-∷ {𝓤} {𝓥} {X} P p f x xs = refl

\end{code}

A version of the desired compactness construction:

\begin{code}

finite-product-compact : (n : ℕ) (X : Fin n → 𝓤 ̇ )
                       → ((i : Fin n) → Compact (X i) {𝓤})
                       → Compact (vec n X) {𝓤}

finite-product-compact zero     X c = 𝟙-Compact
finite-product-compact (succ n) X c = ×-Compact
                                       (c 𝟎)
                                       (finite-product-compact n (X ∘ suc) (c ∘ suc))
\end{code}

Standard operations on (generalized) vectors:

\begin{code}

pattern ⟨⟩       = *
pattern _::_ x xs = (x , xs)

hd : {n : ℕ} {X : Fin (succ n) → 𝓤 ̇ } → vec (succ n) X → X 𝟎
hd (x :: xs) = x

tl : {n : ℕ} {X : Fin (succ n) → 𝓤 ̇ } → vec (succ n) X → vec n (X ∘ suc)
tl (x :: xs) = xs

index : (n : ℕ) {X : Fin n → 𝓤 ̇ } → vec n X → (i : Fin n) → X i
index 0        xs        i       = 𝟘-elim i
index (succ n) (x :: xs) 𝟎       = x
index (succ n) (x :: xs) (suc i) = index n xs i

_!!_ : {n : ℕ} {X : 𝓤 ̇ } → Vec X n → (i : Fin n) → X
_!!_ {𝓤} {n} = index n

\end{code}

An isomorphic copy of vec n X.

\begin{code}

vec' : (n : ℕ) → (Fin n → 𝓤 ̇ ) → 𝓤 ̇
vec' n X = (i : Fin n) → X i


Vec' : 𝓤 ̇ → (n : ℕ) → 𝓤 ̇
Vec' X n = vec' n (λ _ → X)


hd' : {n : ℕ} {X : Fin (succ n) → 𝓤 ̇ } → vec' (succ n) X → X 𝟎
hd' xs = xs 𝟎


tl' : {n : ℕ} {X : Fin (succ n) → 𝓤 ̇ } → vec' (succ n) X → vec' n (X ∘ suc)
tl' xs = λ i → xs (suc i)


⟨⟩' : {X : Fin 0 → 𝓤 ̇ } → vec' 0 X
⟨⟩' = λ i → unique-from-𝟘 i


_::'_ : {n : ℕ} {X : Fin (succ n) → 𝓤 ̇ }
     → X 𝟎 → vec' n (X ∘ suc) → vec' (succ n) X
(x ::' xs) 𝟎       = x
(x ::' xs) (suc i) = xs i


xedni : (n : ℕ) {X : Fin n → 𝓤 ̇ } → ((i : Fin n) → X i) → vec n X
xedni 0        xs' = ⟨⟩
xedni (succ n) xs' = hd' xs' :: xedni n (tl' xs')


vecη : (n : ℕ) {X : Fin n → 𝓤 ̇ } → xedni n {X} ∘ index n {X} ∼ id
vecη zero     ⟨⟩       = refl
vecη (succ n) (x :: xs) = ap (x ::_) (vecη n xs)


module _ {𝓤} (fe : funext 𝓤₀ 𝓤) where

 vecε : (n : ℕ) {X : Fin n → 𝓤 ̇ } → index n {X} ∘ xedni n {X} ∼ id
 vecε 0        xs' = dfunext fe (λ i → 𝟘-elim i)
 vecε (succ n) xs' = dfunext fe h
  where
   h : (i : Fin (succ n)) → index (succ n) (xs' 𝟎 :: xedni n (tl' xs')) i ≡ xs' i
   h 𝟎       = refl
   h (suc i) = happly (vecε n (tl' xs')) i


 vec-≃ : (n : ℕ) {X : Fin n → 𝓤 ̇ } → vec n X ≃ vec' n X
 vec-≃ n {X} = qinveq (index n) (xedni n {X} , vecη n , vecε n)

\end{code}

The desired compactness theorem:

\begin{code}

 finitely-indexed-product-compact : (n : ℕ) (X : Fin n → 𝓤 ̇ )
                                  → ((i : Fin n) → Compact (X i))
                                  → Compact ((i : Fin n) → X i)

 finitely-indexed-product-compact n X c = Compact-closed-under-≃
                                           (vec-≃ n)
                                           (finite-product-compact n X c)
\end{code}

9th Feb 2021. More operations on vectors. The stuff on
vectors should be eventually moved to another module.

\begin{code}

⟨_⟩ : {X : 𝓤 ̇ } → X → Vec X 1
⟨ x ⟩ = x :: ⟨⟩

_∔_ : ℕ → ℕ → ℕ
zero   ∔ n = n
succ m ∔ n = succ (m ∔ n)

append : {X : 𝓤 ̇ } (m n : ℕ) → Vec X m → Vec X n → Vec X (m ∔ n)
append zero     n ⟨⟩      t = t
append (succ m) n (x :: s) t = x :: append m n s t

_++_ : {X : 𝓤 ̇ } {m n : ℕ} → Vec X m → Vec X n → Vec X (m ∔ n)
_++_ = append _ _

plus-1-is-succ : (n : ℕ) → n ∔ 1 ≡ succ n
plus-1-is-succ zero     = refl
plus-1-is-succ (succ n) = ap succ (plus-1-is-succ n)

rev' : {X : 𝓤 ̇ } (n : ℕ) → Vec X n → Vec X n
rev' zero     ⟨⟩      = ⟨⟩
rev' (succ n) (x :: s) = γ
 where
  IH : Vec _ (n ∔ 1)
  IH = rev' n s ++ ⟨ x ⟩

  γ : Vec _ (succ n)
  γ = transport (Vec _) (plus-1-is-succ n) IH

rev : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → Vec X n
rev = rev' _

_+ₐ_ : ℕ → ℕ → ℕ
zero   +ₐ n = n
succ m +ₐ n = m +ₐ succ n

rev-append : {X : 𝓤 ̇ } (m n : ℕ) → Vec X m → Vec X n → Vec X (m +ₐ n)
rev-append zero     n ⟨⟩       t = t
rev-append (succ m) n (x :: s) t = rev-append m (succ n) s (x :: t)

revₐ : {X : 𝓤 ̇ } (m : ℕ) → Vec X m → Vec X (m +ₐ zero)
revₐ n s = rev-append n zero s ⟨⟩

\end{code}

Added 19th March 2021.

\begin{code}

having-three-distinct-points-covariant : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                       → X ↪ Y
                                       → has-three-distinct-points X
                                       → has-three-distinct-points Y
having-three-distinct-points-covariant (f , f-is-emb) ((x , y , z) , u , v , w) = γ
 where
  l : left-cancellable f
  l = embeddings-are-lc f f-is-emb

  γ : has-three-distinct-points (codomain f)
  γ = ((f x , f y , f z) , (λ p → u (l p)) , (λ q → v (l q)) , (λ r → w (l r)))

finite-type-with-three-distict-points : (k : ℕ)
                                      → k ≥ 3
                                      → has-three-distinct-points (Fin k)
finite-type-with-three-distict-points (succ (succ (succ k))) * =
 ((𝟎 , 𝟏 , 𝟐) , +disjoint' , (λ a → +disjoint' (inl-lc a)) , +disjoint)

finite-subsets-of-Ω-have-at-most-2-elements : funext 𝓤 𝓤
                                            → propext 𝓤
                                            → (k : ℕ)
                                            → Fin k ↪ Ω 𝓤
                                            → k ≤ 2
finite-subsets-of-Ω-have-at-most-2-elements {𝓤} fe pe k e = γ
 where
  α : k ≥ 3 → has-three-distinct-points (Ω 𝓤)
  α g = having-three-distinct-points-covariant e (finite-type-with-three-distict-points k g)

  β : ¬ (k ≥ 3)
  β = contrapositive α (no-three-distinct-propositions fe pe)

  γ : k ≤ 2
  γ = not-less-bigger-or-equal k 2 β

\end{code}

TODO. Think about Kuratowski finite subsets of Ω.  That is, types
A ↪ Ω 𝓤 for which there is some surjection Fin k ↠ A.  Because any
such type A doesn't have three distinct points, we are looking at
characterizations of surjections of Fin k into types with no three
distinct points.

Added 8th April 2021.

\begin{code}

module Kuratowski-finiteness (pt : propositional-truncations-exist) where

 open finiteness pt
 open import UF-ImageAndSurjection
 open ImageAndSurjection pt
 open CompactTypesPT pt

 is-Kuratowski-finite : 𝓤 ̇ → 𝓤 ̇
 is-Kuratowski-finite X = ∃ n ꞉ ℕ , Fin n ↠ X

 Kuratowski-data : 𝓤 ̇ → 𝓤 ̇
 Kuratowski-data X = Σ n ꞉ ℕ , Fin n ↠ X

 being-Kuratowski-finite-is-prop : {X : 𝓤 ̇ } → is-prop (is-Kuratowski-finite X)
 being-Kuratowski-finite-is-prop = ∃-is-prop

 Kuratowski-finite-types-are-∃-compact : Fun-Ext
                                       → {X : 𝓤 ̇ }
                                       → is-Kuratowski-finite X
                                       → ∃-Compact X {𝓤}
 Kuratowski-finite-types-are-∃-compact fe {X} i = γ
  where
   α : Kuratowski-data X → Compact X
   α (n , f , s) = surjection-Compact f fe s (Fin-Compact n)

   β : ∥ Compact X ∥
   β = ∥∥-functor α i

   γ : ∃-Compact X
   γ = ∥Compact∥-gives-∃-Compact fe β

 finite-types-are-Kuratowski-finite : {X : 𝓤 ̇ }
                                    → is-finite X
                                    → is-Kuratowski-finite X
 finite-types-are-Kuratowski-finite {𝓤} {X} X-is-finite = γ
  where
   δ : finite-linear-order X → is-Kuratowski-finite X
   δ (n , 𝕗) = ∣ n , (⌜ 𝕗 ⌝⁻¹ , equivs-are-surjections (⌜⌝⁻¹-is-equiv 𝕗)) ∣

   γ : is-Kuratowski-finite X
   γ = ∥∥-rec being-Kuratowski-finite-is-prop δ (finite-gives-finite' X X-is-finite)

\end{code}

Conversely, if a Kuratowski finite is discrete (that is, it has
decidable equality) then it is finite, because we can use the
decidable equality to remove repetitions, as observed by Tom de Jong
(and implemented by Martin Escardo):

\begin{code}

 dkf-lemma : funext 𝓤 𝓤₀
           → {X : 𝓤 ̇ }
           → is-discrete X
           → Kuratowski-data X
           → finite-linear-order X
 dkf-lemma {𝓤} fe {X} δ (n , 𝕗) = γ X δ n 𝕗
  where
   γ : (X : 𝓤 ̇ ) → is-discrete X → (n : ℕ) → (Fin n ↠ X) → finite-linear-order X
   γ X δ 0        (f , s) = 0 , empty-≃-𝟘 (λ x → ∥∥-rec 𝟘-is-prop pr₁ (s x))
   γ X δ (succ n) (f , s) = I Δ
    where
     A : Fin n → 𝓤 ̇
     A j = f (suc j) ≡ f 𝟎

     Δ : decidable (Σ A)
     Δ = Fin-Compact n A (λ j → δ (f (suc j)) (f 𝟎))

     g : Fin n → X
     g i = f (suc i)

     I : decidable (Σ A) → finite-linear-order X
     I (inl (j , p)) = IH
      where
       II : (x : X) → (Σ i ꞉ Fin (succ n) , f i ≡ x) → (Σ i ꞉ Fin n , g i ≡ x)
       II x (𝟎 ,     q) = j , (p ∙ q)
       II x (suc i , q) = i , q

       III : is-surjection g
       III x = ∥∥-functor (II x) (s x)

       IH : finite-linear-order X
       IH = γ X δ n (g , III)

     I (inr ν) = succ n' , IX
      where
       X' = X ∖ f 𝟎

       δ' : is-discrete X'
       δ' = lc-maps-reflect-discreteness pr₁ (pr₁-lc (negations-are-props fe)) δ

       g' : Fin n → X'
       g' i = g i , (λ (p : f (suc i) ≡ f 𝟎) → ν (i , p))

       IV : is-surjection g'
       IV (x , u) = VII
        where
         V : ∃ i ꞉ Fin (succ n) , f i ≡ x
         V = s x

         VI : (Σ i ꞉ Fin (succ n) , f i ≡ x) → (Σ i ꞉ Fin n , g' i ≡ (x , u))
         VI (𝟎     , p) = 𝟘-elim (u (p ⁻¹))
         VI (suc i , p) = i , to-subtype-≡ (λ _ → negations-are-props fe) p

         VII : ∃ i ꞉ Fin n , g' i ≡ (x , u)
         VII = ∥∥-functor VI V

       IH : finite-linear-order X'
       IH = γ X' δ' n (g' , IV)

       n' : ℕ
       n' = pr₁ IH

       VIII : X' ≃ Fin n'
       VIII = pr₂ IH

       IX = X           ≃⟨ remove-and-add-isolated-point fe (f 𝟎) (δ (f 𝟎)) ⟩
           (X' + 𝟙)     ≃⟨ +cong VIII (≃-refl 𝟙) ⟩
           (Fin n' + 𝟙) ■

 Kuratowski-finite-discrete-types-are-finite : funext 𝓤 𝓤₀
                                             → {X : 𝓤 ̇ }
                                             → is-discrete X
                                             → is-Kuratowski-finite X
                                             → is-finite X
 Kuratowski-finite-discrete-types-are-finite {𝓤} fe {X} δ κ =
  finite'-gives-finite X (∥∥-functor (dkf-lemma fe δ) κ)


 surjections-preserve-K-finiteness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                   → is-surjection f
                                   → is-Kuratowski-finite X
                                   → is-Kuratowski-finite Y
 surjections-preserve-K-finiteness {𝓤} {𝓥} {X} {Y} f s i = j
  where
   γ : Kuratowski-data X → Kuratowski-data Y
   γ (n , g , t) = n , f ∘ g , ∘-is-surjection t s

   j : is-Kuratowski-finite Y
   j = ∥∥-functor γ i


 total-K-finite-gives-index-type-K-finite' : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                                           → is-Kuratowski-finite (Σ A)
                                           → is-Kuratowski-finite (Σ x ꞉ X , ∥ A x ∥)
 total-K-finite-gives-index-type-K-finite' X A i = γ
  where
   ζ : (x : X) → A x → ∥ A x ∥
   ζ x a = ∣ a ∣

   ζ-is-surjection : (x : X) → is-surjection (ζ x)
   ζ-is-surjection x = pt-is-surjection

   f : Σ A → Σ x ꞉ X , ∥ A x ∥
   f = NatΣ ζ

   f-is-surjection : is-surjection f
   f-is-surjection = NatΣ-is-surjection A (λ x → ∥ A x ∥) ζ ζ-is-surjection

   γ : is-Kuratowski-finite (Σ x ꞉ X , ∥ A x ∥)
   γ = surjections-preserve-K-finiteness f f-is-surjection i

 total-K-finite-gives-index-type-K-finite : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                                          → is-Kuratowski-finite (Σ A)
                                          → ((x : X) → ∥ A x ∥)
                                          → is-Kuratowski-finite X
 total-K-finite-gives-index-type-K-finite A i s =
  surjections-preserve-K-finiteness pr₁ (pr₁-is-surjection A s) i

\end{code}

The finiteness of all Kuratowski finite types gives the discreteness of
all sets (and hence excluded middle, because the type of truth values
is a set).

\begin{code}

 doubleton : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
 doubleton {𝓤} {X} x₀ x₁ = Σ x ꞉ X , (x ≡ x₀) ∨ (x ≡ x₁)

 doubleton-is-set : {X : 𝓤 ̇ } (x₀ x₁ : X)
                  → is-set X
                  → is-set (doubleton x₀ x₁)
 doubleton-is-set {𝓤} {X} x₀ x₁ i = subsets-of-sets-are-sets
                                      X (λ x → (x ≡ x₀) ∨ (x ≡ x₁)) i ∨-is-prop

 doubleton-map : {X : 𝓤 ̇ } (x₀ x₁ : X) → Fin 2 → doubleton x₀ x₁
 doubleton-map x₀ x₁ 𝟎 = x₀ , ∣ inl refl ∣
 doubleton-map x₀ x₁ 𝟏 = x₁ , ∣ inr refl ∣

 doubleton-map-is-surjection : {X : 𝓤 ̇ } {x₀ x₁ : X}
                             → is-surjection (doubleton-map x₀ x₁)
 doubleton-map-is-surjection {𝓤} {X} {x₀} {x₁} (x , s) = ∥∥-functor γ s
  where
   γ : (x ≡ x₀) + (x ≡ x₁) → Σ n ꞉ Fin 2 , doubleton-map x₀ x₁ n ≡ (x , s)
   γ (inl p) = 𝟎 , to-subtype-≡ (λ _ → ∨-is-prop) (p ⁻¹)
   γ (inr q) = 𝟏 , to-subtype-≡ (λ _ → ∨-is-prop) (q ⁻¹)

 doubletons-are-Kuratowki-finite : {X : 𝓤 ̇ } (x₀ x₁ : X)
                                 → is-Kuratowski-finite (doubleton x₀ x₁)
 doubletons-are-Kuratowki-finite x₀ x₁ = ∣ 2 , doubleton-map x₀ x₁ , doubleton-map-is-surjection ∣


 decidable-equality-gives-doubleton-finite : {X : 𝓤 ̇ } (x₀ x₁ : X)
                                           → is-set X
                                           → decidable (x₀ ≡ x₁)
                                           → is-finite (Σ x ꞉ X , (x ≡ x₀) ∨ (x ≡ x₁))
 decidable-equality-gives-doubleton-finite x₀ x₁ X-is-set δ = γ δ
  where
   γ : decidable (x₀ ≡ x₁) → is-finite (doubleton x₀ x₁)
   γ (inl p) = 1 , ∣ singleton-≃ m l ∣
    where
     l : is-singleton (Fin 1)
     l = 𝟎 , c
      where
       c : is-central (Fin 1) 𝟎
       c 𝟎 = refl

     m : is-singleton (doubleton x₀ x₁)
     m = (doubleton-map x₀ x₁ 𝟎 , c)
      where
       c : is-central (doubleton x₀ x₁) (doubleton-map x₀ x₁ 𝟎)
       c (y , s) = to-subtype-≡ (λ _ → ∨-is-prop) (∥∥-rec X-is-set α s)
        where
         α : (y ≡ x₀) + (y ≡ x₁) → x₀ ≡ y
         α (inl q) = q ⁻¹
         α (inr q) = p ∙ q ⁻¹

   γ (inr ν) = 2 , ∣ ≃-sym (doubleton-map x₀ x₁ , f-is-equiv) ∣
    where
     doubleton-map-lc : left-cancellable (doubleton-map x₀ x₁)
     doubleton-map-lc {𝟎} {𝟎} p = refl
     doubleton-map-lc {𝟎} {𝟏} p = 𝟘-elim (ν (ap pr₁ p))
     doubleton-map-lc {𝟏} {𝟎} p = 𝟘-elim (ν (ap pr₁ (p ⁻¹)))
     doubleton-map-lc {𝟏} {𝟏} p = refl

     doubleton-map-is-embedding : is-embedding (doubleton-map x₀ x₁)
     doubleton-map-is-embedding = lc-maps-into-sets-are-embeddings
                                   (doubleton-map x₀ x₁)
                                   doubleton-map-lc
                                   (doubleton-is-set x₀ x₁ X-is-set)

     f-is-equiv : is-equiv (doubleton-map x₀ x₁)
     f-is-equiv = surjective-embeddings-are-equivs
                   (doubleton-map x₀ x₁)
                   doubleton-map-is-embedding
                   doubleton-map-is-surjection

 doubleton-finite-gives-decidable-equality : funext 𝓤 𝓤₀
                                           → {X : 𝓤 ̇ } (x₀ x₁ : X)
                                           → is-set X
                                           → is-finite (Σ x ꞉ X , (x ≡ x₀) ∨ (x ≡ x₁))
                                           → decidable (x₀ ≡ x₁)
 doubleton-finite-gives-decidable-equality fe x₀ x₁ X-is-set ϕ = δ
  where
   γ : is-finite (doubleton x₀ x₁) → decidable (x₀ ≡ x₁)
   γ (0 , s) = ∥∥-rec (decidability-of-prop-is-prop fe X-is-set) α s
    where
     α : doubleton x₀ x₁ ≃ 𝟘 → decidable (x₀ ≡ x₁)
     α (g , i) = 𝟘-elim (g (x₀ , ∣ inl refl ∣))

   γ (1 , s) = inl (∥∥-rec X-is-set β s)
    where
     α : is-prop (Fin 1)
     α 𝟎 𝟎 = refl

     β : doubleton x₀ x₁ ≃ Fin 1 → x₀ ≡ x₁
     β (g , i) = ap pr₁ (equivs-are-lc g i (α (g (doubleton-map x₀ x₁ 𝟎)) (g (doubleton-map x₀ x₁ 𝟏))))

   γ (succ (succ n) , s) = ∥∥-rec (decidability-of-prop-is-prop fe X-is-set) f s
    where
     f : doubleton x₀ x₁ ≃ Fin (succ (succ n)) → decidable (x₀ ≡ x₁)
     f (g , i) = β
      where
       h : x₀ ≡ x₁ → doubleton-map x₀ x₁ 𝟎 ≡ doubleton-map x₀ x₁ 𝟏
       h = to-subtype-≡ (λ _ → ∨-is-prop)

       α : decidable (g (doubleton-map x₀ x₁ 𝟎) ≡ g (doubleton-map x₀ x₁ 𝟏)) → decidable (x₀ ≡ x₁)
       α (inl p) = inl (ap pr₁ (equivs-are-lc g i p))
       α (inr ν) = inr (contrapositive (λ p → ap g (h p)) ν)

       β : decidable (x₀ ≡ x₁)
       β = α (Fin-is-discrete (succ (succ n)) (g (doubleton-map x₀ x₁ 𝟎)) (g (doubleton-map x₀ x₁ 𝟏)))

   δ : decidable (x₀ ≡ x₁)
   δ = γ ϕ

 all-K-finite-types-finite-gives-all-sets-discrete :

     funext 𝓤 𝓤₀
   → ((A : 𝓤 ̇ ) → is-Kuratowski-finite A → is-finite A)
   → (X : 𝓤 ̇ ) → is-set X → is-discrete X

 all-K-finite-types-finite-gives-all-sets-discrete {𝓤} fe ϕ X X-is-set x₀ x₁ =
  doubleton-finite-gives-decidable-equality
   fe x₀ x₁ X-is-set
   (ϕ (doubleton x₀ x₁)
   (doubletons-are-Kuratowki-finite x₀ x₁))

 open import UF-ExcludedMiddle

 all-K-finite-types-finite-gives-EM :

     ((𝓤 : Universe) (A : 𝓤 ̇ ) → is-Kuratowski-finite A → is-finite A)
   → (𝓤 : Universe) → FunExt → PropExt → EM 𝓤
 all-K-finite-types-finite-gives-EM ϕ 𝓤 fe pe =
  Ω-discrete-gives-EM (fe 𝓤 𝓤) (pe 𝓤)
   (all-K-finite-types-finite-gives-all-sets-discrete
     (fe (𝓤 ⁺) 𝓤₀) (ϕ (𝓤 ⁺)) (Ω 𝓤) (Ω-is-set (fe 𝓤 𝓤) (pe 𝓤)))

\end{code}

Added 13 April 2021.

Can every Kuratowski finite discrete type be equipped with a linear
order?

Recall that a type is called discrete if it has decidable equality.

Steve Vickers asks this question for the internal language of a
1-topos, and provides a counter model for it in Section 2.4 of the
following paper:

  S.J. Vickers. Strongly Algebraic = SFP (Topically). Mathematical
  Structures in Computer Science 11 (2001) pp. 717-742,
  http://dx.doi.org/10.1017/S0960129501003437
  https://www.cs.bham.ac.uk/~sjv/SFP.pdf

We here work in MLTT with propositional truncations, in Agda notation,
and instead prove that, in the presence of univalence, it is false
that every (Kuratowski) finite type with decidable equality can be
equipped with a linear order.

We also include an open problem related to this.

The following no-selection lemma is contributed by Tom de Jong:

\begin{code}

 open import Two-Properties

 no-selection : is-univalent 𝓤₀ → ¬ ((X : 𝓤₀ ̇ ) → ∥ X ≃ 𝟚 ∥ → X)
 no-selection ua ϕ = γ
  where
   f : {X : 𝓤₀ ̇ } → X ≡ 𝟚 → X ≃ 𝟚
   f {X} = idtoeq X 𝟚

   n : 𝟚
   n = ϕ 𝟚 ∣ ≃-refl 𝟚 ∣

   α : {X : 𝓤₀ ̇ } (p : X ≡ 𝟚) → ϕ X ∣ f p ∣ ≡  ⌜ f p ⌝⁻¹ n
   α refl = refl

   p : 𝟚 ≡ 𝟚
   p = eqtoid ua 𝟚 𝟚 complement-≃

   q : ∣ f refl ∣ ≡ ∣ f p ∣
   q = ∥∥-is-prop ∣ f refl ∣ ∣ f p ∣

   r : f p ≡ complement-≃
   r = idtoeq-eqtoid ua 𝟚 𝟚 complement-≃

   s = n                     ≡⟨ refl ⟩
       ⌜ f refl ⌝⁻¹ n        ≡⟨ (α refl)⁻¹ ⟩
       ϕ 𝟚 ∣ f refl ∣        ≡⟨ ap (ϕ 𝟚) q ⟩
       ϕ 𝟚 ∣ f p ∣           ≡⟨ α p ⟩
       ⌜ f p ⌝⁻¹ n           ≡⟨ ap (λ - → ⌜ - ⌝⁻¹ n) r ⟩
       ⌜ complement-≃ ⌝⁻¹ n  ≡⟨ refl ⟩
       complement n          ∎

   γ : 𝟘
   γ = complement-no-fp n s


 𝟚-is-Fin2 : 𝟚 ≃ Fin 2
 𝟚-is-Fin2 = qinveq (𝟚-cases 𝟎 𝟏) (g , η , ε)
  where
   g : Fin 2 → 𝟚
   g 𝟎 = ₀
   g 𝟏 = ₁

   η : g ∘ 𝟚-cases 𝟎 𝟏 ∼ id
   η ₀ = refl
   η ₁ = refl

   ε : 𝟚-cases 𝟎 𝟏 ∘ g ∼ id
   ε 𝟎 = refl
   ε 𝟏 = refl

 open import UF-UA-FunExt

 no-orderability-of-finite-types :

  Univalence → ¬ ((X : 𝓤 ̇ ) → is-finite X → finite-linear-order X)

 no-orderability-of-finite-types {𝓤} ua ψ = γ
  where
   fe : FunExt
   fe = Univalence-gives-FunExt ua

   α : (X : 𝓤₀ ̇ ) → ∥ X ≃ 𝟚 ∥ → X ≃ 𝟚
   α X s = VII
    where
     X' : 𝓤 ̇
     X' = Lift 𝓤 X

     I : X ≃ 𝟚 → X' ≃ Fin 2
     I 𝕗 = X'    ≃⟨ Lift-≃ 𝓤 X ⟩
           X     ≃⟨ 𝕗 ⟩
           𝟚     ≃⟨ 𝟚-is-Fin2 ⟩
           Fin 2 ■

     II : ∥ X' ≃ Fin 2 ∥
     II = ∥∥-functor I s

     III : is-finite X'
     III = 2 , II

     IV : finite-linear-order X'
     IV = ψ X' III

     n : ℕ
     n = pr₁ IV

     𝕘 : X' ≃ Fin n
     𝕘 = pr₂ IV

     V : ∥ X' ≃ Fin n ∥ → ∥ X' ≃ Fin 2 ∥ → n ≡ 2
     V = ∥∥-rec₂ ℕ-is-set (λ 𝕗 𝕘 → Fin-lc n 2 (≃-sym 𝕗 ● 𝕘))

     VI : n ≡ 2
     VI = V ∣ 𝕘 ∣ II

     VII = X     ≃⟨ ≃-Lift 𝓤 X ⟩
           X'    ≃⟨ 𝕘 ⟩
           Fin n ≃⟨ idtoeq (Fin n) (Fin 2) (ap Fin VI) ⟩
           Fin 2 ≃⟨ ≃-sym 𝟚-is-Fin2 ⟩
           𝟚     ■

   ϕ : (X : 𝓤₀ ̇ ) → ∥ X ≃ 𝟚 ∥ → X
   ϕ X s = ⌜ ≃-sym (α X s) ⌝ ₀

   γ : 𝟘
   γ = no-selection (ua 𝓤₀) ϕ

\end{code}

Because univalence is consistent, it follows that, without univalence,
the statement

  (X : 𝓤 ̇ ) → is-finite X → finite-linear-order X

is not provable.

The same holds if we replace is-finite by is-Kuratowski-finite or if
we consider Kuratowski finite discrete types.

\begin{code}

 no-orderability-of-K-finite-types :

  Univalence → ¬ ((X : 𝓤 ̇ ) → is-Kuratowski-finite X → finite-linear-order X)

 no-orderability-of-K-finite-types {𝓤} ua ϕ = no-orderability-of-finite-types ua ψ
  where
   ψ : (X : 𝓤 ̇ ) → is-finite X → finite-linear-order X
   ψ X i = ϕ X (finite-types-are-Kuratowski-finite i)

\end{code}

And this gives an alternative answer to the question by Steve Vickers
mentioned above:

\begin{code}

 no-orderability-of-K-finite-discrete-types :

  Univalence → ¬ ((X : 𝓤 ̇ ) → is-Kuratowski-finite X → is-discrete X → finite-linear-order X)

 no-orderability-of-K-finite-discrete-types {𝓤} ua ϕ = no-orderability-of-finite-types ua ψ
  where
   ψ : (X : 𝓤 ̇ ) → is-finite X → finite-linear-order X
   ψ X i = ϕ X (finite-types-are-Kuratowski-finite i)
               (finite-types-are-discrete (Univalence-gives-FunExt ua) i)
\end{code}

TODO. Without univalence, maybe it is the case that from

  (X : 𝓤 ̇ ) → ∥ X ≃ 𝟚 ∥ → X

we can deduce excluded middle or some other constructive taboo.

(It seems not. More later.)

One more notion of finiteness:

\begin{code}

 is-subfinite : 𝓤 ̇ → 𝓤 ̇
 is-subfinite X = ∃ n ꞉ ℕ , X ↪ Fin n

 subfiniteness-data : 𝓤 ̇ → 𝓤 ̇
 subfiniteness-data X = Σ n ꞉ ℕ , X ↪ Fin n

\end{code}

Steve Vickers remarked (personal communication) that, in view of
a remark given above, if a type is simultaneously Kuratowski finite
and subfinite, then it is finite, because subfinite types, being
subtypes of types with decidable equality, have decidable equality.

\begin{code}

 Kuratowski-subfinite-types-are-finite : funext 𝓤 𝓤₀
                                       → {X : 𝓤 ̇ }
                                       → is-Kuratowski-finite X
                                       → is-subfinite X
                                       → is-finite X
 Kuratowski-subfinite-types-are-finite fe {X} k = γ
  where
  δ : subfiniteness-data X → is-finite X
  δ (n , f , e) = Kuratowski-finite-discrete-types-are-finite fe
                   (embeddings-reflect-discreteness f e (Fin-is-discrete n)) k

  γ : is-subfinite X → is-finite X
  γ = ∥∥-rec (being-finite-is-prop X) δ

\end{code}

Summary of finiteness notions for a type X:

     ∃ n ꞉ ℕ , X ≃ Fin n  (is-finite X)
     Σ n ꞉ ℕ , X ≃ Fin n  (finite-linear-order X)

     ∃ n ꞉ ℕ , Fin n ↠ X  (is-Kuratowski-finite X)
     Σ n ꞉ ℕ , Fin n ↠ X  (Kuratowski-data)

     ∃ n ꞉ ℕ , X ↪ Fin n  (is-subfinite)
     Σ n ꞉ ℕ , X ↪ Fin n  (subfiniteness-data)

Addendum.

\begin{code}

 select-equiv-with-𝟚-lemma₁ : FunExt
                            → {X : 𝓤 ̇ } (x₀ : X)
                            → is-prop (Σ x₁ ꞉ X , is-equiv (𝟚-cases x₀ x₁))
 select-equiv-with-𝟚-lemma₁ fe {X} x₀ (y , i) (z , j) = V
  where
   f g : 𝟚 → X
   f = 𝟚-cases x₀ y
   g = 𝟚-cases x₀ z

   f' g' : X → 𝟚
   f' = inverse f i
   g' = inverse g j

   I : z ≢ x₀
   I p = zero-is-not-one
          (₀        ≡⟨ (inverses-are-retractions g j ₀)⁻¹ ⟩
           g' (g ₀) ≡⟨ refl ⟩
           g' x₀    ≡⟨ ap g' (p ⁻¹) ⟩
           g' z     ≡⟨ refl ⟩
           g' (g ₁) ≡⟨ inverses-are-retractions g j ₁ ⟩
           ₁        ∎)

   II : (n : 𝟚) → f n ≡ z → ₁ ≡ n
   II ₀ p = 𝟘-elim (I (p ⁻¹))
   II ₁ p = refl

   III : f (f' z) ≡ z
   III = inverses-are-sections f i z

   IV : y ≡ z
   IV = equivs-are-lc f' (inverses-are-equivs f i)
         (f' y     ≡⟨ refl ⟩
          f' (f ₁) ≡⟨ inverses-are-retractions f i ₁ ⟩
          ₁        ≡⟨ II (f' z) III ⟩
          f' z     ∎)

   V : (y , i) ≡ (z , j)
   V = to-subtype-≡ (λ x₁ → being-equiv-is-prop fe (𝟚-cases x₀ x₁)) IV

 select-equiv-with-𝟚-lemma₂ : FunExt
                            → {X : 𝓤 ̇ }
                            → X ≃ 𝟚
                            → (x₀ : X) → Σ x₁ ꞉ X , is-equiv (𝟚-cases x₀ x₁)
 select-equiv-with-𝟚-lemma₂ fe {X} (f , i) x₀ = γ (f x₀) x₀ refl
  where
   γ : (n : 𝟚) (x₀ : X) → n ≡ f x₀ → Σ x₁ ꞉ X , is-equiv (𝟚-cases x₀ x₁)
   γ ₀ x₀ p = (x₁ , j)
    where
     x₁ : X
     x₁ = inverse f i ₁

     h : inverse f i ∼ 𝟚-cases x₀ x₁
     h ₀ = inverse f i ₀      ≡⟨ ap (inverse f i) p ⟩
           inverse f i (f x₀) ≡⟨ inverses-are-retractions f i x₀ ⟩
           x₀                 ≡⟨ refl ⟩
           𝟚-cases x₀ x₁ ₀    ∎
     h ₁ = refl

     j : is-equiv (𝟚-cases x₀ x₁)
     j = equiv-closed-under-∼' (inverses-are-equivs f i) h

   γ ₁ x₀ p = (x₁ , j)
    where
     x₁ : X
     x₁ = inverse f i ₀

     h : inverse f i ∘ complement ∼ 𝟚-cases x₀ x₁
     h ₀ = inverse f i (complement ₀) ≡⟨ refl ⟩
           inverse f i ₁              ≡⟨ ap (inverse f i) p ⟩
           inverse f i (f x₀)         ≡⟨ inverses-are-retractions f i x₀ ⟩
           x₀                         ≡⟨ refl  ⟩
           𝟚-cases x₀ x₁ ₀            ∎
     h ₁ = refl

     j : is-equiv (𝟚-cases x₀ x₁)
     j = equiv-closed-under-∼'
         (∘-is-equiv complement-is-equiv (inverses-are-equivs f i)) h

 select-equiv-with-𝟚 : FunExt
                     → {X : 𝓤 ̇ }
                     → ∥ X ≃ 𝟚 ∥
                     → X
                     → X ≃ 𝟚
 select-equiv-with-𝟚 fe {X} s x₀ = γ
  where
   α : ∥ X ≃ 𝟚 ∥ → Σ x₁ ꞉ X , is-equiv (𝟚-cases x₀ x₁)
   α = ∥∥-rec (select-equiv-with-𝟚-lemma₁ fe x₀)
             (λ 𝕙 → select-equiv-with-𝟚-lemma₂ fe 𝕙 x₀)

   β : Σ x₁ ꞉ X , is-equiv (𝟚-cases x₀ x₁)
   β = α s

   γ : X ≃ 𝟚
   γ = ≃-sym (𝟚-cases x₀ (pr₁ β) , pr₂ β)

\end{code}

Hence finding an equivalence from the existence of an equivalence is
logically equivalent to finding a point from the existence of an
equivalence (exercise: moreover, these two things are typally
equivalent):

\begin{code}

 select-equiv-with-𝟚-theorem : FunExt
                             → {X : 𝓤 ̇ }
                             → (∥ X ≃ 𝟚 ∥ → X ≃ 𝟚)
                             ⇔ (∥ X ≃ 𝟚 ∥ → X)
 select-equiv-with-𝟚-theorem fe {X} = α , β
  where
   α : (∥ X ≃ 𝟚 ∥ → X ≃ 𝟚) → ∥ X ≃ 𝟚 ∥ → X
   α f s = ⌜ ≃-sym (f s) ⌝ ₀

   β : (∥ X ≃ 𝟚 ∥ → X) → ∥ X ≃ 𝟚 ∥ → X ≃ 𝟚
   β g s = select-equiv-with-𝟚 fe s (g s)

\end{code}
