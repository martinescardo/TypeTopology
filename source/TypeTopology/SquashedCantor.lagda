Martin Escardo, back-of-the-envelope 2011, done July 2018

The main application of this module is to show that the compact
ordinals we construct in other modules are totally separated. This is
difficult because sums don't preserve total separatedness (as shown in
the module FailureOfTotalSeparatedness).

To prove the total separatedness, we show that our compact ordinals
are retracts of the Cantor type, which is enough as total
separatedness is inherited by retracts. The crucial step, developed at
the end of this module as an application of the main development, is
to show that the squashed sum of a family of Cantor retracts is again
a Cantor retract.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module TypeTopology.SquashedCantor (fe : FunExt) where

open import CoNaturals.GenericConvergentSequence
open import CoNaturals.UniversalProperty fe
open import InjectiveTypes.Blackboard fe
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Addition renaming (_+_ to _∔_)
open import Naturals.Sequence fe renaming (head to head' ; tail to tail' ; _∶∶_ to _∶∶'_)
open import Notation.CanonicalMap
open import TypeTopology.SquashedSum fe
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.Retracts
open import UF.Retracts-FunExt
open import UF.Subsingletons

private
 fe₀ : funext 𝓤₀ 𝓤₀
 fe₀ = fe 𝓤₀ 𝓤₀

\end{code}

A delayed element of X is a "time" u : ℕ∞ together with a partial
element of X, which is defined when u is finite. Hence the type of
delayed elements of X is the squashed sum of the constant
family λ (_ : ℕ) → X.

\begin{code}

D : 𝓤 ̇ → 𝓤 ̇
D X = Σ u ꞉ ℕ∞ , (is-finite u → X)

private
 remark₁ : (X : 𝓤 ̇ ) → D X ＝ Σ¹ λ (_ : ℕ) → X
 remark₁ X = refl

Cantor : 𝓤₀ ̇
Cantor = ℕ → 𝟚

Cantor[_] : ℕ∞ → 𝓤₀ ̇
Cantor[ u ] = is-finite u → Cantor

\end{code}

The idea is that Cantor[ u ] is the set of partial elements of the
Cantor space with domain of definition "is-finite u".

Exercises left to the reader (they are not needed so far):

  (1) Cantor[ under n ] ≃ Cantor,

  (2) Cantor[ ∞ ] ≃ 𝟙.

\begin{code}

private
 remark₂ : D Cantor ＝ (Σ u ꞉ ℕ∞ , Cantor[ u ])
 remark₂ = refl

transport-Cantor : {u v : ℕ∞} (p : u ＝ v) → Cantor[ u ] → Cantor[ v ]
transport-Cantor = transport Cantor[_]

transport-finite : {u v : ℕ∞} (p : u ＝ v) → is-finite u → is-finite v
transport-finite = transport is-finite

transport-finite⁻¹ : {u v : ℕ∞} (p : u ＝ v) → is-finite v → is-finite u
transport-finite⁻¹ = transport⁻¹ is-finite

ap-Cantor : {X : 𝓤 ̇ }
            (f : (u : ℕ∞) → Cantor[ u ] → X)
            {u v : ℕ∞}
            (p : u ＝ v)
            {φ : Cantor[ u ]}
          → f u φ ＝ f v (φ ∘ transport-finite⁻¹ p)
ap-Cantor f refl = refl

\end{code}

Transport of partial elements of the Cantor space is composition with
transportation of finiteness:

\begin{code}

tpc : {u v : ℕ∞} (φ : Cantor[ u ]) (p : u ＝ v)
    → transport-Cantor p φ ＝ φ ∘ transport-finite⁻¹ p
tpc φ refl = refl

back-tpc : {u v : ℕ∞} (φ : Cantor[ u ]) (p : v ＝ u)
         → transport-Cantor p (φ ∘ transport-finite p) ＝ φ
back-tpc φ refl = refl

\end{code}

The above renaming in the Sequence import is for us to be able to
avoid "yellow" with the following definitions, which specialize the
implicit arguments of head', tail' and _∶∶'_. As a side-effect, this
also speeds up type checking. NB. We could have used (and we tried) to
have the necessary types as parameters of the module
sequence. However, this doesn't work, as in another module
(CountableTychonoff), these functions are used with different implicit
parameters in the same term.

\begin{code}

head : Cantor → 𝟚
head = head'

tail : Cantor → Cantor
tail = tail'

_∶∶_ : 𝟚 → Cantor → Cantor
_∶∶_ = _∶∶'_

\end{code}

We now define functions

   Head : Cantor → ℕ∞
   Tail : (α : Cantor) → Cantor[ Head α ]
   Cons : (Σ u ꞉ ℕ∞ , Cantor[ u ]) → Cantor

such that for all u : ℕ∞ and φ : Cantor[ u ],

   (Head (Cons (u , φ) , Tail (Cons(u, φ)) = (u , φ),

thus exhibiting (Σ u ꞉ ℕ∞ , Cantor[ u ]) as a retract of Cantor.

This is a constructive rendering of the classical fact that every
sequence α : Cantor is of one of the forms

   1ⁿ0β or 1ᵒᵒ,

which is equivalent to Bishop's LPO (limited principle of
omniscience). Without LPO, we can say that there is no sequence which
is not of any of these two forms, but this is rather weak.

What we do instead is to extract such a prefix 1ⁿ0 or 1ᵒᵒ, with Head,
regarded as an element of ℕ∞ (a decreasing sequence), and the
*partial* suffix, with Tail, which will be total when the prefix is
finite.

The Tail of α is defined when the Head of α is finite.

We define Head by coinduction on ℕ∞, Tail directly, and Cons by
coinduction on Cantor.

We will have Head = lcni as defined in the module
GenericConvergentSequence, but it is more convenient to work with the
following coinductive definition (see the module CoNaturals).

\begin{code}

Head-step : Cantor → 𝟙 {𝓤₀} + Cantor
Head-step α = 𝟚-equality-cases
               (λ (r : head α ＝ ₀) → inl ⋆)
               (λ (r : head α ＝ ₁) → inr (tail α))

Head : Cantor → ℕ∞
Head = ℕ∞-corec Head-step

Head-step₀ : (α : Cantor) → head α ＝ ₀ → Head-step α ＝ inl ⋆
Head-step₀ α = ap (λ - → 𝟚-equality-cases
                          (λ (r : - ＝ ₀) → inl ⋆)
                          (λ (r : - ＝ ₁) → inr (tail α)))

Head-step₁ : (α : Cantor) → head α ＝ ₁ → Head-step α ＝ inr (tail α)
Head-step₁ α = ap (λ - → 𝟚-equality-cases
                          (λ (r : - ＝ ₀) → inl ⋆)
                          (λ (r : - ＝ ₁) → inr (tail α)))

Head₀ : (α : Cantor) → head α ＝ ₀ → Head α ＝ Zero
Head₀ α r = coalg-morphism-Zero
             Head-step
             Head (ℕ∞-corec-homomorphism Head-step)
             α
             ⋆
             (Head-step₀ α r)

Head₁ : (α : Cantor) → head α ＝ ₁ → Head α ＝ Succ (Head (tail α))
Head₁ α r = coalg-morphism-Succ
             Head-step
             Head
             (ℕ∞-corec-homomorphism Head-step)
             α
             (tail α)
             (Head-step₁ α r)
\end{code}

Tail is defined explicitly:

\begin{code}

Tail : (α : Cantor) → Cantor[ Head α ]
Tail α (n , r) k = α (k ∔ succ n)

Tail₀ : (α : Cantor) (i : is-finite (Head (₀ ∶∶ α)))
      → Tail (₀ ∶∶ α) i ＝ α
Tail₀ α (zero   , r) = refl
Tail₀ α (succ n , r) = 𝟘-elim (Succ-not-Zero (Succ (ι n)     ＝⟨ r ⟩
                                              Head (₀ ∶∶ α)  ＝⟨ Head₀ (₀ ∶∶ α) refl ⟩
                                              Zero           ∎))

Tail₁ : (α : Cantor) (i : is-finite (Head (₁ ∶∶ α)))
      → Tail (₁ ∶∶ α) i ＝ α ∘ (λ k → k ∔ size i)
Tail₁ α (zero   , r) = 𝟘-elim (Zero-not-Succ (Zero          ＝⟨ r ⟩
                                              Head (₁ ∶∶ α) ＝⟨ Head₁ (₁ ∶∶ α) refl ⟩
                                              Succ (Head α) ∎))
Tail₁ α (succ n , r) = refl

ap-Tail' : {α β : Cantor} (p : α ＝ β)
         → Tail α ＝ Tail β ∘ transport (λ - → is-finite (Head -)) p
ap-Tail' refl = refl

\end{code}

In practice we find it more convenient to work with the following
version of the above, derived from it:

\begin{code}

ap-Tail : {α β : Cantor} (i : is-finite (Head α))
        → (p : α ＝ β)
        → Tail α i ＝ Tail β (transport (λ - → is-finite (Head -)) p i)
ap-Tail i p = ap (λ - → - i) (ap-Tail' p)

\end{code}

We now coinductively define a function Κ, used to define an
inverse Cons for ⟨Head,Tail⟩:

\begin{code}

head-step : D Cantor → 𝟚
head-step (u , φ) = 𝟚-equality-cases
                     (λ (z : is-Zero u)     → head (φ (Zero-is-finite' fe₀ u z)))
                     (λ (p : is-positive u) → ₁)

tail-step : D Cantor → D Cantor
tail-step (u , φ) = 𝟚-equality-cases
                     (λ (z : is-Zero u)     → u , tail ∘ φ)
                     (λ (p : is-positive u) → Pred u , φ ∘ is-finite-up' fe₀ u)

Κ : D Cantor → Cantor
Κ = seq-corec head-step tail-step

head-Κ-Zero : (φ : Cantor[ Zero ])
            → head (Κ (Zero , φ)) ＝ head (φ Zero-is-finite)
head-Κ-Zero φ = head (Κ (Zero , φ))     ＝⟨ I ⟩
                head-step (Zero , φ)    ＝⟨ II ⟩
                head (φ Zero-is-finite) ∎
              where
               I  = seq-corec-head head-step tail-step (Zero , φ)
               II = ap (λ - → head (φ -)) (being-finite-is-prop fe₀ Zero _ _)

tail-Κ-Zero : (φ : Cantor[ Zero ])
            → tail (Κ (Zero , φ)) ＝ Κ (Zero , tail ∘ φ)
tail-Κ-Zero φ = seq-corec-tail head-step tail-step (Zero , φ)

Κ₀ : (φ : Cantor[ Zero ])
   → Κ (Zero , φ) ＝ φ Zero-is-finite
Κ₀ φ = dfunext fe₀ (l φ )
 where
  l : (φ : Cantor[ Zero ]) (n : ℕ)
    → Κ (Zero , φ ) n ＝ φ Zero-is-finite n
  l φ zero = head-Κ-Zero φ
  l φ (succ n) = γ
   where
    IH : Κ (Zero , tail ∘ φ) n ＝ φ Zero-is-finite (succ n)
    IH = l (tail ∘ φ) n

    γ = Κ (Zero , φ) (succ n)     ＝⟨ ap (λ - → - n) (tail-Κ-Zero φ) ⟩
        Κ (Zero , tail ∘ φ) n     ＝⟨ IH ⟩
        φ Zero-is-finite (succ n) ∎

head-Κ-Succ : (u : ℕ∞) (φ : Cantor[ Succ u ])
            → head (Κ (Succ u , φ ))＝ ₁
head-Κ-Succ u φ = seq-corec-head head-step tail-step (Succ u , φ)

to-Κ-＝ : ({u v} w : ℕ∞)
         (φ : Cantor[ w ])
         (p : u ＝ v)
         {s : is-finite u → is-finite w}
         {t : is-finite v → is-finite w}
        → Κ (u , φ ∘ s) ＝ Κ (v , φ ∘ t)
to-Κ-＝ {u} w φ refl {s} {t} =
  ap (λ - → Κ (u , -))
     (dfunext fe₀ (λ (i : is-finite u) → ap φ (being-finite-is-prop fe₀ w (s i) (t i))))

tail-Κ-Succ : (u : ℕ∞)
              (φ : Cantor[ Succ u ])
            → tail (Κ (Succ u , φ)) ＝ Κ (u , φ ∘ is-finite-up u)
tail-Κ-Succ u φ =
  tail (Κ (Succ u , φ))                             ＝⟨ I ⟩
  Κ (Pred(Succ u) , φ ∘ is-finite-up' fe₀ (Succ u)) ＝⟨ II ⟩
  Κ (u , φ ∘ is-finite-up u)                        ∎
   where
    I  = seq-corec-tail head-step tail-step (Succ u , φ)
    II = to-Κ-＝ (Succ u) φ Pred-Succ

Κ₁ : (u : ℕ∞) (φ : Cantor[ Succ u ])
   → Κ (Succ u , φ) ＝ ₁ ∶∶ Κ (u , φ ∘ is-finite-up u)
Κ₁ u φ = dfunext fe₀ h
 where
  h : (i : ℕ) → Κ (Succ u , φ) i ＝ (₁ ∶∶ Κ (u , φ ∘ is-finite-up u)) i
  h zero     = head-Κ-Succ u φ
  h (succ i) = ap (λ - → - i) (tail-Κ-Succ u φ)

\end{code}

The function Κ is not invertible, but the following function Cons
defined from it is:

\begin{code}

Cons : D Cantor → Cantor
Cons (u , φ) = Κ (u , λ (i : is-finite u) → ₀ ∶∶ φ i)

to-Cons-＝ : ({u v} w : ℕ∞)
            (φ : Cantor[ w ])
            (p : u ＝ v)
            {s : is-finite u → is-finite w}
            {t : is-finite v → is-finite w}
          → Cons (u , φ ∘ s) ＝ Cons (v , φ ∘ t)
to-Cons-＝ {u} {v} w φ = to-Κ-＝ {u} {v} w (λ i → ₀ ∶∶ φ i)

Cons₀ : (φ : Cantor[ Zero ])
      → Cons (Zero , φ) ＝ ₀ ∶∶ φ Zero-is-finite
Cons₀ φ = Κ₀ (λ i → ₀ ∶∶ φ i)

Cons₁ : (u : ℕ∞)
        (φ : Cantor[ Succ u ])
      → Cons (Succ u , φ) ＝ ₁ ∶∶  Cons (u , φ ∘ is-finite-up u)
Cons₁ u φ = Κ₁ u (λ i → ₀ ∶∶ φ i)

tail-Cons-Succ : (u : ℕ∞) (φ : Cantor[ Succ u ])
               → tail (Cons (Succ u , φ)) ＝ Cons (u , φ ∘ is-finite-up u)
tail-Cons-Succ u φ = tail-Κ-Succ u (λ i → ₀ ∶∶ φ i)

\end{code}

Then applying n+1 times the (lower case) function tail to the sequence
Cons (ι n , φ) we get the sequence φ (ι-is-finite n):

\begin{code}

tail-Cons-ι : (n : ℕ) (φ : Cantor[ ι n ])
            → Cons (ι n , φ) ∘ (λ k → k ∔ succ n) ＝ φ (ℕ-to-ℕ∞-is-finite n)
tail-Cons-ι zero φ     = ap tail (Cons₀ φ)
tail-Cons-ι (succ n) φ = γ
 where
  IH : Cons (ι n , φ ∘ is-finite-up (ι n)) ∘ (λ k → k ∔ succ n)
     ＝ φ (is-finite-up (ι n) (ℕ-to-ℕ∞-is-finite n))
  IH = tail-Cons-ι n (φ ∘ is-finite-up (ι n))

  γ : Cons (ι (succ n) , φ) ∘ (λ k → k ∔ succ (succ n))
    ＝ φ (ℕ-to-ℕ∞-is-finite (succ n))
  γ = Cons (ι (succ n) , φ) ∘ (λ k → k ∔ succ (succ n))        ＝⟨ I ⟩
      Cons (ι n , φ ∘ is-finite-up (ι n)) ∘ (λ k → k ∔ succ n) ＝⟨ IH ⟩
      φ (is-finite-up (ι n) (ℕ-to-ℕ∞-is-finite n))             ＝⟨ II ⟩
      φ (ℕ-to-ℕ∞-is-finite (succ n))                           ∎
   where
    I  = ap (λ - → - ∘ (λ k → k ∔ succ (succ n))) (Cons₁ (ι n) φ)
    II = ap φ (being-finite-is-prop fe₀ (ι (succ n)) _ _)

\end{code}

The following can be proved by coinduction on ℕ∞, but it is more
direct to prove it using density, which means it is enough to check
the cases u = ι n (which we do by induction on ℕ) and u = ∞ (which we
do using the fact that ∞ is the unique fixed point of Succ).

\begin{code}

open import UF.DiscreteAndSeparated

Head-Cons : (u : ℕ∞) (φ : Cantor[ u ]) → Head (Cons (u , φ)) ＝ u
Head-Cons = λ u φ → ap (λ - → - φ) (γ u)
 where
  Head-Cons-finite : (n : ℕ) (φ : Cantor[ ι n ])
                   → Head (Cons (ι n , φ)) ＝ ι n
  Head-Cons-finite zero φ = Head₀ (Cons (Zero , φ)) (ap head (Cons₀ φ))
  Head-Cons-finite (succ n) φ =
    Head (Cons (Succ (ι n) , φ))                      ＝⟨ I ⟩
    Succ (Head (tail (Cons (Succ (ι n) , φ))))        ＝⟨ II ⟩
    Succ (Head (Cons (ι n , φ ∘ is-finite-up (ι n)))) ＝⟨ III ⟩
    ι (succ n)                                        ∎
     where
      r : Cons (Succ (ι n) , φ) ＝ ₁ ∶∶ Cons (ι n , φ ∘ is-finite-up (ι n))
      r = Cons₁ (ι n) φ

      IH : Head (Cons (ι n , φ ∘ is-finite-up (ι n))) ＝ ι n
      IH = Head-Cons-finite n (φ ∘ is-finite-up (ι n))

      I   = Head₁ (Cons (Succ (ι n) , φ)) (ap head r)
      II  = ap (Succ ∘ Head ∘ tail) r
      III = ap Succ IH

  Head-Cons-∞ : (φ : Cantor[ ∞ ]) → Head (Cons (∞ , φ)) ＝ ∞
  Head-Cons-∞ φ = unique-fixed-point-of-Succ fe₀ (Head (Cons (∞ , φ))) p
   where
    r : Cons (Succ ∞ , φ ∘ is-finite-down ∞)
      ＝ ₁ ∶∶ Cons (∞ , φ ∘ is-finite-down ∞ ∘ is-finite-up ∞)
    r = Cons₁ ∞ (φ ∘ is-finite-down ∞)

    p = Head (Cons (∞ , φ))                                            ＝⟨ I ⟩
        Head (Cons (Succ ∞ , φ ∘ is-finite-down ∞))                    ＝⟨ II ⟩
        Succ (Head (tail (Cons (Succ ∞ , φ ∘ is-finite-down ∞))))      ＝⟨ III ⟩
        Succ (Head (Cons (∞ , φ ∘ is-finite-down ∞ ∘ is-finite-up ∞))) ＝⟨ IV ⟩
        Succ (Head (Cons (∞ , φ)))                                     ∎
         where
          I   = ap Head (to-Cons-＝ ∞ φ ((Succ-∞-is-∞ fe₀)⁻¹) {id} {is-finite-down ∞})
          II  = Head₁ (Cons (Succ ∞ , φ ∘ is-finite-down ∞)) (ap head r)
          III = ap (Succ ∘ Head ∘ tail) r
          IV  = ap (Succ ∘ Head) (to-Cons-＝ ∞ φ refl {is-finite-down ∞ ∘ is-finite-up ∞} {id})

  γ : (u : ℕ∞) → (λ φ → Head (Cons (u , φ))) ＝ (λ φ → u)
  γ = ℕ∞-ddensity fe₀
       (λ {u} → Π-is-¬¬-separated fe₀ (λ φ → ℕ∞-is-¬¬-separated fe₀))
       (λ n → dfunext fe₀ (Head-Cons-finite n))
       (dfunext fe₀ Head-Cons-∞)

Head-finite : (u : ℕ∞) (φ : Cantor[ u ]) → is-finite (Head (Cons (u , φ))) → is-finite u
Head-finite u φ = transport-finite (Head-Cons u φ)

\end{code}

Notice that the lemma γ in the following theorem is not defined by
induction, but simply by cases zero and succ n for the finiteness
witness:

\begin{code}

Tail-Cons : (u : ℕ∞) (φ : Cantor[ u ])
          → Tail (Cons (u , φ)) ＝ φ ∘ Head-finite u φ
Tail-Cons u φ = dfunext fe₀ (γ u φ)
 where
   γ : (u : ℕ∞) (φ : Cantor[ u ]) (i : is-finite (Head (Cons (u , φ))))
    → Tail (Cons (u , φ)) i ＝ (φ ∘ Head-finite u φ) i
   γ u φ (zero , r) = δ
    where
     p = u                   ＝⟨ (Head-Cons u φ)⁻¹ ⟩
         Head (Cons (u , φ)) ＝⟨ r ⁻¹ ⟩
         ι zero              ∎

     t : is-finite Zero → is-finite u
     t = transport-finite⁻¹ p

     q : Cons (u , φ) ＝ Cons (Zero , φ ∘ t)
     q = ap-Cantor (λ u φ → Cons (u , φ)) p

     j : is-finite (Head (Cons (Zero , φ ∘ t)))
     j = transport (λ - → is-finite (Head -)) q (zero , r)

     k : is-finite (Head (₀ ∶∶ φ (t Zero-is-finite)))
     k = transport (λ - → is-finite (Head -)) (Cons₀ (φ ∘ t)) j

     δ = Tail (Cons (u , φ)) (zero , r)     ＝⟨ I ⟩
         Tail (Cons (Zero , φ ∘ t)) j       ＝⟨ II ⟩
         Tail (₀ ∶∶ φ (t Zero-is-finite)) k ＝⟨ III ⟩
         φ (t Zero-is-finite)               ＝⟨ IV ⟩
         φ (Head-finite u φ (zero , r))     ∎
      where
       I   = ap-Tail (zero , r) q
       II  = ap-Tail j (Cons₀ (φ ∘ t))
       III = Tail₀ (φ (t Zero-is-finite)) k
       IV  = ap φ (being-finite-is-prop fe₀ u _ _)

   γ u φ (succ n , r) = δ
    where
     p = u                   ＝⟨ (Head-Cons u φ)⁻¹ ⟩
         Head (Cons (u , φ)) ＝⟨ r ⁻¹ ⟩
         ι (succ n)          ∎

     t : is-finite (Succ (ι n)) → is-finite u
     t = transport-finite⁻¹ p

     t' : is-finite (ι n) → is-finite u
     t' = t ∘ is-finite-up (ι n)

     q : Cons (u , φ) ＝ Cons (Succ (ι n) , φ ∘ t)
     q = ap-Cantor (λ u φ → Cons (u , φ)) p

     j : is-finite (Head (Cons (Succ (ι n) , φ ∘ t)))
     j = transport (λ - → is-finite (Head -)) q (succ n , r)

     k : is-finite (Head (₁ ∶∶ Cons (ι n , φ ∘ t')))
     k = transport (λ - → is-finite (Head -)) (Cons₁ (ι n) (φ ∘ t)) j

     l = ι (size k)                                              ＝⟨ I ⟩
         Head (₁ ∶∶ Cons (ι n , φ ∘ t'))                         ＝⟨ II ⟩
         Succ (Head (tail (₁ ∶∶ Cons (ι n , (λ x → φ (t' x)))))) ＝⟨ III ⟩
         Succ (ι n)                                              ＝⟨ refl ⟩
         ι (succ n)                                              ∎
          where
           I   = pr₂ k
           II  = Head₁ (₁ ∶∶ Cons (ι n , φ ∘ t')) refl
           III = ap Succ (Head-Cons (ι n) (φ ∘ t'))

     m : size k ＝ succ n
     m = ℕ-to-ℕ∞-lc l

     δ = Tail (Cons (u , φ)) (succ n , r)         ＝⟨ I ⟩
         Tail (Cons (Succ (ι n) , φ ∘ t)) j       ＝⟨ II ⟩
         Tail (₁ ∶∶ Cons (ι n , φ ∘ t')) k        ＝⟨ III ⟩
         Cons (ι n , φ ∘ t') ∘ (λ l → l ∔ size k) ＝⟨ IV ⟩
         Cons (ι n , φ ∘ t') ∘ (λ l → l ∔ succ n) ＝⟨ V ⟩
         φ (t' (ℕ-to-ℕ∞-is-finite n))             ＝⟨ VI ⟩
         φ (Head-finite u φ (succ n , r))         ∎
      where
       I   = ap-Tail (succ n , r) q
       II  = ap-Tail j (Cons₁ (ι n) (φ ∘ t))
       III = Tail₁ (Cons (ι n , φ ∘ t')) k
       IV  = ap (λ - → Cons (ι n , φ ∘ t') ∘ (λ l → l ∔ -)) m
       V   = tail-Cons-ι n (φ ∘ t')
       VI  = ap φ (being-finite-is-prop fe₀ u _ _)

Tail-Cons' : (u : ℕ∞) (φ : Cantor[ u ])
          → transport-Cantor (Head-Cons u φ) (Tail (Cons (u , φ))) ＝ φ
Tail-Cons' u φ = transport-Cantor (Head-Cons u φ) (Tail (Cons (u , φ))) ＝⟨ I ⟩
                 transport-Cantor (Head-Cons u φ) (φ ∘ Head-finite u φ) ＝⟨ II ⟩
                 φ                                                      ∎
 where
  I  = ap (transport-Cantor (Head-Cons u φ)) (Tail-Cons u φ)
  II = back-tpc φ (Head-Cons u φ)

\end{code}

Hence Cons is left invertible, or has a section:

\begin{code}

Snoc : Cantor → D Cantor
Snoc α = (Head α , Tail α)

Snoc-Cons : (d : D Cantor) → Snoc (Cons d) ＝ d
Snoc-Cons (u , φ) = to-Σ-＝ (Head-Cons u φ , Tail-Cons' u φ)

open import UF.Retracts

D-Cantor-retract-of-Cantor : retract (D Cantor) of Cantor
D-Cantor-retract-of-Cantor = Snoc , Cons , Snoc-Cons

\end{code}

We actually have an equivalence, not just a retraction (as a
consequence of Lambek's Lemma - see unfinished code below), but we
delay a proof of this as it is not needed for our immediate purpose
of showing that our searchable ordinals are totally separated.

\begin{code}

Σ¹-Cantor-retract : (X : ℕ → 𝓤 ̇ )
                  → ((n : ℕ) → retract (X n) of Cantor)
                  → retract (Σ¹ X) of Cantor
Σ¹-Cantor-retract {𝓤} X ρ = retracts-compose D-Cantor-retract-of-Cantor r
 where
  s : (u : ℕ∞) → retract (X / ι) u of ((λ _ → Cantor) / ι) u
  s = retract-extension X (λ _ → Cantor) ι ρ

  r : retract (Σ¹ X) of Σ¹ (λ _ → Cantor)
  r = Σ-retract (X / ι) ((λ _ → Cantor) / ι) s

\end{code}

We also need the following retractions (the first with X = ℕ):

\begin{code}

pair-seq-retract : {X : 𝓤 ̇ }
                 → funext 𝓤₀ 𝓤
                 → retract ((ℕ → X) × (ℕ → X)) of (ℕ → X)
pair-seq-retract {𝓤} {X} fe = retracts-compose (retracts-compose c d) b
 where
  open import Naturals.Binary

  a : retract (ℕ → X) of (𝔹 → X)
  a = retract-covariance fe (unary , binary , unary-binary)

  b : retract ((ℕ → X) × (ℕ → X)) of ((𝔹 → X) × (𝔹 → X))
  b = ×-retract a a

  c : retract (𝔹 → X) of (ℕ → X)
  c = retract-covariance fe (binary , unary , binary-unary)

  d : retract ((𝔹 → X) × (𝔹 → X)) of (𝔹 → X)
  d = (f , g , fg)
   where
    f : (𝔹 → X) → (𝔹 → X) × (𝔹 → X)
    f α = (α ∘ L , α ∘ R)

    g : (𝔹 → X) × (𝔹 → X) → 𝔹 → X
    g (α , β) Z     = α Z -- irrelevant choice
    g (α , β) (L b) = α b
    g (α , β) (R b) = β b

    fg : (γ : (𝔹 → X) × (𝔹 → X)) → f (g γ) ＝ γ
    fg (α , β) = refl

+-Cantor-retract : retract (Cantor + Cantor) of Cantor
+-Cantor-retract = f , g , fg
 where
  f : Cantor → Cantor + Cantor
  f α = 𝟚-equality-cases
         (λ (l : α 0 ＝ ₀) → inl (tail α))
         (λ (r : α 0 ＝ ₁) → inr (tail α))

  g : Cantor + Cantor → Cantor
  g (inl α) = ₀ ∶∶ α
  g (inr β) = ₁ ∶∶ β

  fg : (z : Cantor + Cantor) → f (g z) ＝ z
  fg (inl α) = refl
  fg (inr β) = refl

\end{code}

The last retraction is actually an equivalence, and the second last
can be made into one, using ℕ+ℕ≃ℕ, proved in the module
BinaryNaturals (which is not needed for the moment).

End for the moment. 20 July 2018.

TODO. The corecursion principle for D, which is not needed for the
moment (but has the above as a corollary by Lambek's Lemma):

\begin{code}
{-
D-corec : {X : 𝓤 ̇ } (h : X → ℕ∞) (t : (x : X) → is-finite (h x) → X)
        → Σ f ꞉ (X → Cantor)
        , Σ p ꞉ Head ∘ f ∼ h
        , ((x : X) (i : is-finite (Head (f x)) → Tail (f x) i ＝ f (t x (transport-finite (p x) i))))
D-corec {𝓤} {X} h t = ?
-}

\end{code}

TODO. This follows from D-corec, but may be useful to prove it:

\begin{code}
{-
Cons-Snoc : (α : Cantor) → Cons (Snoc α) ＝ α
Cons-Snoc α = dfunext fe₀ γ
 where
  f : Cantor → Cantor
  f α = Cons (Head α , Tail α)
  fh : (α : Cantor) → head (f α) ＝ head α
  fh α = {!!}
  ft : (α : Cantor) → tail (f α) ＝ f (tail α)
  ft α = {!!}
  fid : f ＝ id
  fid = seq-at-most-one head tail f id (fh , ft) ((λ α → refl) , (λ α → refl))
  γ : (i : ℕ) → Cons (Head α , Tail α) i ＝ α i
  γ zero = 𝟚-equality-cases a b
   where
    a : head α ＝ ₀ → Cons (Head α , Tail α) zero ＝ α zero
    a r = ap head (p ∙ q) ∙ r ⁻¹
     where
      s : Head α ＝ Zero
      s = Head₀ α r
      p : Cons (Head α , Tail α) ＝ Cons (Zero , Tail α ∘ transport-finite⁻¹ s)
      p = to-Cons-＝ {Head α} {Zero} (Head α) (Tail α) s {id} {transport-finite⁻¹ s}
      q : Cons (Zero , Tail α ∘ transport-finite⁻¹ s)
        ＝ ₀ ∶∶  Tail α (transport-finite⁻¹ s Zero-is-finite)
      q = Cons₀ (Tail α ∘ transport-finite⁻¹ s)
    b : head α ＝ ₁ → Cons (Head α , Tail α) zero ＝ α zero
    b r = ap head (p ∙ q) ∙ r ⁻¹
     where
      s : Head α ＝ Succ (Head (tail α))
      s = Head₁ α r
      p : Cons (Head α , Tail α)
       ＝ Cons (Succ (Head (tail α)) , Tail α ∘ transport-finite⁻¹ s)
      p = to-Cons-＝ {Head α} {Succ (Head (tail α))} (Head α) (Tail α) s {id} {transport-finite⁻¹ s}
      q : Cons (Succ (Head (tail α)) , Tail α ∘ transport-finite⁻¹ s)
       ＝ (₁ ∶∶  Cons ((Head (tail α)) , (Tail α ∘ transport-finite⁻¹ s ∘ is-finite-up (Head (tail α)))))
      q = Cons₁ (Head (tail α)) (Tail α ∘ transport-finite⁻¹ s)

  γ (succ i) = g
   where
    IH : Cons (Head α , Tail α) i ＝ α i
    IH = γ i
    g : Cons (Head α , Tail α) (succ i) ＝ α (succ i)
    g = {!!}
-}
\end{code}
