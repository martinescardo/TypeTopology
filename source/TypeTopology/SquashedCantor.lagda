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
open import Naturals.Sequence fe
            renaming (head to head' ; tail to tail' ; _∶∶_ to _∶∶'_)
open import Notation.CanonicalMap
open import TypeTopology.SquashedSum fe
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.Retracts
open import UF.Retracts-FunExt
open import UF.Subsingletons

private
 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

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

  (1) Cantor[ ι n ] ≃ Cantor,

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
            {π : Cantor[ u ]}
          → f u π ＝ f v (π ∘ transport-finite⁻¹ p)
ap-Cantor f refl = refl

\end{code}

Transport of partial elements of the Cantor space is composition with
transportation of finiteness:

\begin{code}

tpc : {u v : ℕ∞}
      (π : Cantor[ u ])
      (p : u ＝ v)
    → transport-Cantor p π ＝ π ∘ transport-finite⁻¹ p
tpc π refl = refl

back-tpc : {u v : ℕ∞}
           (π : Cantor[ u ])
           (p : v ＝ u)
         → transport-Cantor p (π ∘ transport-finite p) ＝ π
back-tpc π refl = refl

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
   Cons : D Cantor → Cantor

such that for all u : ℕ∞ and π : Cantor[ u ],

   (Head (Cons (u , π) , Tail (Cons(u, π)) = (u , π),

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

We will have Head = ℕ→𝟚-to-ℕ∞ as defined in the module
GenericConvergentSequence, but it is more convenient to work with the
following coinductive definition (see the module
CoNaturals.UniversalProperty).

\begin{code}

Head-step : Cantor → 𝟙 {𝓤₀} + Cantor
Head-step α = 𝟚-equality-cases
               (λ (r : head α ＝ ₀) → inl ⋆)
               (λ (r : head α ＝ ₁) → inr (tail α))

Head : Cantor → ℕ∞
Head = ℕ∞-corec Head-step

Head-step₀ : (α : Cantor)
           → head α ＝ ₀
           → Head-step α ＝ inl ⋆
Head-step₀ α = ap (λ - → 𝟚-equality-cases
                          (λ (r : - ＝ ₀) → inl ⋆)
                          (λ (r : - ＝ ₁) → inr (tail α)))

Head-step₁ : (α : Cantor)
           → head α ＝ ₁
           → Head-step α ＝ inr (tail α)
Head-step₁ α = ap (λ - → 𝟚-equality-cases
                          (λ (r : - ＝ ₀) → inl ⋆)
                          (λ (r : - ＝ ₁) → inr (tail α)))

Head₀ : (α : Cantor)
      → head α ＝ ₀
      → Head α ＝ Zero
Head₀ α r = coalg-morphism-Zero
             Head-step
             Head (ℕ∞-corec-homomorphism Head-step)
             α
             ⋆
             (Head-step₀ α r)

Head₁ : (α : Cantor)
      → head α ＝ ₁
      → Head α ＝ Succ (Head (tail α))
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
Tail α φ k = α (k ∔ succ (size φ))

Tail₀ : (α : Cantor)
        (φ : is-finite (Head (₀ ∶∶ α)))
      → Tail (₀ ∶∶ α) φ ＝ α
Tail₀ α (0      , r) = refl
Tail₀ α (succ n , r) = 𝟘-elim
                        (Succ-not-Zero
                          (Succ (ι n)     ＝⟨ r ⟩
                           Head (₀ ∶∶ α)  ＝⟨ Head₀ (₀ ∶∶ α) refl ⟩
                           Zero           ∎))

Tail₁ : (α : Cantor)
        (φ : is-finite (Head (₁ ∶∶ α)))
      → Tail (₁ ∶∶ α) φ ＝ α ∘ (λ k → k ∔ size φ)
Tail₁ α (0      , r) = 𝟘-elim
                        (Zero-not-Succ
                          (Zero          ＝⟨ r ⟩
                           Head (₁ ∶∶ α) ＝⟨ Head₁ (₁ ∶∶ α) refl ⟩
                           Succ (Head α) ∎))
Tail₁ α (succ n , r) = refl

ap-Tail' : {α β : Cantor}
           (p : α ＝ β)
         → Tail α ＝ Tail β ∘ transport (λ - → is-finite (Head -)) p
ap-Tail' refl = refl

\end{code}

In practice we find it more convenient to work with the following
version of the above, derived from it:

\begin{code}

ap-Tail : {α β : Cantor}
          (φ : is-finite (Head α))
        → (p : α ＝ β)
        → Tail α φ ＝ Tail β (transport (λ - → is-finite (Head -)) p φ)
ap-Tail φ p = ap (λ - → - φ) (ap-Tail' p)

\end{code}

We now coinductively define a function Κ, used to define an
inverse Cons for ⟨Head , Tail⟩:

\begin{code}

head-step : D Cantor → 𝟚
head-step (u , π) = 𝟚-equality-cases
                     (λ (z : is-Zero u)     → head (π (Zero-is-finite' fe' u z)))
                     (λ (p : is-positive u) → ₁)

tail-step : D Cantor → D Cantor
tail-step (u , π) = 𝟚-equality-cases
                     (λ (z : is-Zero u)     → u , tail ∘ π)
                     (λ (p : is-positive u) → Pred u , π ∘ is-finite-up' fe' u)

Κ : D Cantor → Cantor
Κ = seq-corec head-step tail-step

head-Κ-Zero : (π : Cantor[ Zero ])
            → head (Κ (Zero , π)) ＝ head (π Zero-is-finite)
head-Κ-Zero π =
 head (Κ (Zero , π))     ＝⟨ I ⟩
 head-step (Zero , π)    ＝⟨ II ⟩
 head (π Zero-is-finite) ∎
  where
   I  = seq-corec-head head-step tail-step (Zero , π)
   II = ap (λ - → head (π -)) (being-finite-is-prop fe' Zero _ _)

tail-Κ-Zero : (π : Cantor[ Zero ])
            → tail (Κ (Zero , π)) ＝ Κ (Zero , tail ∘ π)
tail-Κ-Zero π = seq-corec-tail head-step tail-step (Zero , π)

Κ₀ : (π : Cantor[ Zero ])
   → Κ (Zero , π) ＝ π Zero-is-finite
Κ₀ π = dfunext fe' (l π )
 where
  l : (π : Cantor[ Zero ])
    → Κ (Zero , π ) ∼ π Zero-is-finite
  l π 0        = head-Κ-Zero π
  l π (succ n) = γ
   where
    IH : Κ (Zero , tail ∘ π) n ＝ π Zero-is-finite (succ n)
    IH = l (tail ∘ π) n

    γ = Κ (Zero , π) (succ n)     ＝⟨ ap (λ - → - n) (tail-Κ-Zero π) ⟩
        Κ (Zero , tail ∘ π) n     ＝⟨ IH ⟩
        π Zero-is-finite (succ n) ∎

head-Κ-Succ : (u : ℕ∞)
              (π : Cantor[ Succ u ])
            → head (Κ (Succ u , π )) ＝ ₁
head-Κ-Succ u π = seq-corec-head head-step tail-step (Succ u , π)

to-Κ-＝ : ({u v} w : ℕ∞)
          (π : Cantor[ w ])
          (p : u ＝ v)
          {s : is-finite u → is-finite w}
          {t : is-finite v → is-finite w}
        → Κ (u , π ∘ s) ＝ Κ (v , π ∘ t)
to-Κ-＝ {u} w π refl {s} {t} =
 ap (λ - → Κ (u , -))
    (dfunext fe'
      (λ (φ : is-finite u) → ap π (being-finite-is-prop fe' w (s φ) (t φ))))

tail-Κ-Succ : (u : ℕ∞)
              (π : Cantor[ Succ u ])
            → tail (Κ (Succ u , π)) ＝ Κ (u , π ∘ is-finite-up u)
tail-Κ-Succ u π =
  tail (Κ (Succ u , π))                              ＝⟨ I ⟩
  Κ (Pred (Succ u) , π ∘ is-finite-up' fe' (Succ u)) ＝⟨ II ⟩
  Κ (u , π ∘ is-finite-up u)                         ∎
   where
    I  = seq-corec-tail head-step tail-step (Succ u , π)
    II = to-Κ-＝ (Succ u) π Pred-Succ

Κ₁ : (u : ℕ∞) (π : Cantor[ Succ u ])
   → Κ (Succ u , π) ＝ ₁ ∶∶ Κ (u , π ∘ is-finite-up u)
Κ₁ u π = dfunext fe' h
 where
  h : (i : ℕ) → Κ (Succ u , π) i ＝ (₁ ∶∶ Κ (u , π ∘ is-finite-up u)) i
  h 0        = head-Κ-Succ u π
  h (succ i) = ap (λ - → - i) (tail-Κ-Succ u π)

\end{code}

The function Κ is not invertible, but the following function Cons
defined from it is:

\begin{code}

Cons : D Cantor → Cantor
Cons (u , π) = Κ (u , λ (φ : is-finite u) → ₀ ∶∶ π φ)

to-Cons-＝ : ({u v} w : ℕ∞)
             (π : Cantor[ w ])
             (p : u ＝ v)
             {s : is-finite u → is-finite w}
             {t : is-finite v → is-finite w}
           → Cons (u , π ∘ s) ＝ Cons (v , π ∘ t)
to-Cons-＝ {u} {v} w π = to-Κ-＝ {u} {v} w (λ φ → ₀ ∶∶ π φ)

Cons₀ : (π : Cantor[ Zero ])
      → Cons (Zero , π) ＝ ₀ ∶∶ π Zero-is-finite
Cons₀ π = Κ₀ (λ φ → ₀ ∶∶ π φ)

Cons₁ : (u : ℕ∞)
        (π : Cantor[ Succ u ])
      → Cons (Succ u , π) ＝ ₁ ∶∶  Cons (u , π ∘ is-finite-up u)
Cons₁ u π = Κ₁ u (λ φ → ₀ ∶∶ π φ)

tail-Cons-Succ : (u : ℕ∞) (π : Cantor[ Succ u ])
               → tail (Cons (Succ u , π)) ＝ Cons (u , π ∘ is-finite-up u)
tail-Cons-Succ u π = tail-Κ-Succ u (λ φ → ₀ ∶∶ π φ)

\end{code}

Then applying n+1 times the (lower case) function tail to the sequence
Cons (ι n , π) we get the sequence π (ι-is-finite n):

\begin{code}

tail-Cons-ι : (n : ℕ) (π : Cantor[ ι n ])
            → Cons (ι n , π) ∘ (λ k → k ∔ succ n) ＝ π (ℕ-to-ℕ∞-is-finite n)
tail-Cons-ι 0    π     = ap tail (Cons₀ π)
tail-Cons-ι (succ n) π = γ
 where
  IH : Cons (ι n , π ∘ is-finite-up (ι n)) ∘ (λ k → k ∔ succ n)
     ＝ π (is-finite-up (ι n) (ℕ-to-ℕ∞-is-finite n))
  IH = tail-Cons-ι n (π ∘ is-finite-up (ι n))

  γ : Cons (ι (succ n) , π) ∘ (λ k → k ∔ succ (succ n))
    ＝ π (ℕ-to-ℕ∞-is-finite (succ n))
  γ = Cons (ι (succ n) , π) ∘ (λ k → k ∔ succ (succ n))        ＝⟨ I ⟩
      Cons (ι n , π ∘ is-finite-up (ι n)) ∘ (λ k → k ∔ succ n) ＝⟨ IH ⟩
      π (is-finite-up (ι n) (ℕ-to-ℕ∞-is-finite n))             ＝⟨ II ⟩
      π (ℕ-to-ℕ∞-is-finite (succ n))                           ∎
   where
    I  = ap (λ - → - ∘ (λ k → k ∔ succ (succ n))) (Cons₁ (ι n) π)
    II = ap π (being-finite-is-prop fe' (ι (succ n)) _ _)

\end{code}

The following can be proved by coinduction on ℕ∞, but it is more
direct to prove it using density, which means it is enough to check
the cases u = ι n (which we do by induction on ℕ) and u = ∞ (which we
do using the fact that ∞ is the unique fixed point of Succ).

\begin{code}

open import UF.DiscreteAndSeparated

Head-Cons-finite : (n : ℕ) (π : Cantor[ ι n ])
                 → Head (Cons (ι n , π)) ＝ ι n
Head-Cons-finite 0        φ = Head₀ (Cons (Zero , φ)) (ap head (Cons₀ φ))
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

Head-Cons-∞ : (π : Cantor[ ∞ ]) → Head (Cons (∞ , π)) ＝ ∞
Head-Cons-∞ π = γ
 where
  r : Cons (Succ ∞ , π ∘ is-finite-down ∞)
    ＝ ₁ ∶∶ Cons (∞ , π ∘ is-finite-down ∞ ∘ is-finite-up ∞)
  r = Cons₁ ∞ (π ∘ is-finite-down ∞)

  p = Head (Cons (∞ , π))                                            ＝⟨ I ⟩
      Head (Cons (Succ ∞ , π ∘ is-finite-down ∞))                    ＝⟨ II ⟩
      Succ (Head (tail (Cons (Succ ∞ , π ∘ is-finite-down ∞))))      ＝⟨ III ⟩
      Succ (Head (Cons (∞ , π ∘ is-finite-down ∞ ∘ is-finite-up ∞))) ＝⟨ IV ⟩
      Succ (Head (Cons (∞ , π)))                                     ∎
       where
        I   = ap Head
                 (to-Cons-＝ ∞ π ((Succ-∞-is-∞ fe')⁻¹) {id} {is-finite-down ∞})
        II  = Head₁ (Cons (Succ ∞ , π ∘ is-finite-down ∞)) (ap head r)
        III = ap (Succ ∘ Head ∘ tail) r
        IV  = ap (Succ ∘ Head)
                 (to-Cons-＝ ∞ π refl {is-finite-down ∞ ∘ is-finite-up ∞} {id})

  γ : Head (Cons (∞ , π)) ＝ ∞
  γ = unique-fixed-point-of-Succ fe' (Head (Cons (∞ , π))) p

Head-Cons : (u : ℕ∞)
            (π : Cantor[ u ])
          → Head (Cons (u , π)) ＝ u
Head-Cons = λ u (π : Cantor[ u ]) → ap (λ - → - π) (γ u)
 where
  γ : (u : ℕ∞) → (λ π → Head (Cons (u , π))) ＝ (λ π → u)
  γ = ℕ∞-ddensity fe'
       (λ {u} → Π-is-¬¬-separated fe' (λ φ → ℕ∞-is-¬¬-separated fe'))
       (λ n → dfunext fe' (Head-Cons-finite n))
       (dfunext fe' Head-Cons-∞)

Head-finite : (u : ℕ∞)
              (π : Cantor[ u ])
            → is-finite (Head (Cons (u , π)))
            → is-finite u
Head-finite u π = transport-finite (Head-Cons u π)

\end{code}

Notice that the lemma γ in the following theorem is not defined by
induction, but simply by cases 0 and succ n for the finiteness
witness:

\begin{code}

Tail-Cons : (u : ℕ∞)
            (π : Cantor[ u ])
          → Tail (Cons (u , π)) ＝ π ∘ Head-finite u π
Tail-Cons u π = dfunext fe' (γ u π)
 where
   γ : (u : ℕ∞)
       (π : Cantor[ u ])
       (φ : is-finite (Head (Cons (u , π))))
     → Tail (Cons (u , π)) φ ＝ (π ∘ Head-finite u π) φ
   γ u π (0 , r) = δ
    where
     p = u                   ＝⟨ (Head-Cons u π)⁻¹ ⟩
         Head (Cons (u , π)) ＝⟨ r ⁻¹ ⟩
         ι 0                 ∎

     t : is-finite Zero → is-finite u
     t = transport-finite⁻¹ p

     q : Cons (u , π) ＝ Cons (Zero , π ∘ t)
     q = ap-Cantor (λ u π → Cons (u , π)) p

     φ' : is-finite (Head (Cons (Zero , π ∘ t)))
     φ' = transport (λ - → is-finite (Head -)) q (zero , r)

     k : is-finite (Head (₀ ∶∶ π (t Zero-is-finite)))
     k = transport (λ - → is-finite (Head -)) (Cons₀ (π ∘ t)) φ'

     δ = Tail (Cons (u , π)) (zero , r)     ＝⟨ I ⟩
         Tail (Cons (Zero , π ∘ t)) φ'      ＝⟨ II ⟩
         Tail (₀ ∶∶ π (t Zero-is-finite)) k ＝⟨ III ⟩
         π (t Zero-is-finite)               ＝⟨ IV ⟩
         π (Head-finite u π (0 , r))        ∎
      where
       I   = ap-Tail (0 , r) q
       II  = ap-Tail φ' (Cons₀ (π ∘ t))
       III = Tail₀ (π (t Zero-is-finite)) k
       IV  = ap π (being-finite-is-prop fe' u _ _)

   γ u π (succ n , r) = δ
    where
     p = u                   ＝⟨ (Head-Cons u π)⁻¹ ⟩
         Head (Cons (u , π)) ＝⟨ r ⁻¹ ⟩
         ι (succ n)          ∎

     t : is-finite (Succ (ι n)) → is-finite u
     t = transport-finite⁻¹ p

     t' : is-finite (ι n) → is-finite u
     t' = t ∘ is-finite-up (ι n)

     q : Cons (u , π) ＝ Cons (Succ (ι n) , π ∘ t)
     q = ap-Cantor (λ u π → Cons (u , π)) p

     j : is-finite (Head (Cons (Succ (ι n) , π ∘ t)))
     j = transport (λ - → is-finite (Head -)) q (succ n , r)

     k : is-finite (Head (₁ ∶∶ Cons (ι n , π ∘ t')))
     k = transport (λ - → is-finite (Head -)) (Cons₁ (ι n) (π ∘ t)) j

     l = ι (size k)                                              ＝⟨ I ⟩
         Head (₁ ∶∶ Cons (ι n , π ∘ t'))                         ＝⟨ II ⟩
         Succ (Head (tail (₁ ∶∶ Cons (ι n , (λ x → π (t' x)))))) ＝⟨ III ⟩
         Succ (ι n)                                              ＝⟨ refl ⟩
         ι (succ n)                                              ∎
          where
           I   = size-property k
           II  = Head₁ (₁ ∶∶ Cons (ι n , π ∘ t')) refl
           III = ap Succ (Head-Cons (ι n) (π ∘ t'))

     m : size k ＝ succ n
     m = ℕ-to-ℕ∞-lc l

     δ = Tail (Cons (u , π)) (succ n , r)         ＝⟨ I ⟩
         Tail (Cons (Succ (ι n) , π ∘ t)) j       ＝⟨ II ⟩
         Tail (₁ ∶∶ Cons (ι n , π ∘ t')) k        ＝⟨ III ⟩
         Cons (ι n , π ∘ t') ∘ (λ l → l ∔ size k) ＝⟨ IV ⟩
         Cons (ι n , π ∘ t') ∘ (λ l → l ∔ succ n) ＝⟨ V ⟩
         π (t' (ℕ-to-ℕ∞-is-finite n))             ＝⟨ VI ⟩
         π (Head-finite u π (succ n , r))         ∎
      where
       I   = ap-Tail (succ n , r) q
       II  = ap-Tail j (Cons₁ (ι n) (π ∘ t))
       III = Tail₁ (Cons (ι n , π ∘ t')) k
       IV  = ap (λ - → Cons (ι n , π ∘ t') ∘ (λ l → l ∔ -)) m
       V   = tail-Cons-ι n (π ∘ t')
       VI  = ap π (being-finite-is-prop fe' u _ _)

Tail-Cons' : (u : ℕ∞)
             (π : Cantor[ u ])
           → transport-Cantor (Head-Cons u π) (Tail (Cons (u , π))) ＝ π
Tail-Cons' u π = transport-Cantor (Head-Cons u π) (Tail (Cons (u , π))) ＝⟨ I ⟩
                 transport-Cantor (Head-Cons u π) (π ∘ Head-finite u π) ＝⟨ II ⟩
                 π                                                      ∎
 where
  I  = ap (transport-Cantor (Head-Cons u π)) (Tail-Cons u π)
  II = back-tpc π (Head-Cons u π)

\end{code}

Hence Cons is left invertible, or has a section:

\begin{code}

Snoc : Cantor → D Cantor
Snoc α = (Head α , Tail α)

Snoc-Cons : (d : D Cantor) → Snoc (Cons d) ＝ d
Snoc-Cons (u , π) = to-Σ-＝ (Head-Cons u π , Tail-Cons' u π)

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
Σ¹-Cantor-retract X ρ = γ
 where
  s : (u : ℕ∞) → retract (X / ι) u of ((λ _ → Cantor) / ι) u
  s = retract-extension X (λ _ → Cantor) ι ρ

  r : retract (Σ¹ X) of Σ¹ (λ _ → Cantor)
  r = Σ-retract (X / ι) ((λ _ → Cantor) / ι) s

  γ : retract Σ¹ X of Cantor
  γ = retracts-compose D-Cantor-retract-of-Cantor r

\end{code}

We also need the following retractions (the first with X = ℕ):

\begin{code}

pair-seq-retract : {X : 𝓤 ̇ }
                 → retract ((ℕ → X) × (ℕ → X)) of (ℕ → X)
pair-seq-retract {𝓤} {X} = e
 where
  open import Naturals.Binary

  a : retract (ℕ → X) of (𝔹 → X)
  a = retract-covariance fe' (unary , binary , unary-binary)

  b : retract ((ℕ → X) × (ℕ → X)) of ((𝔹 → X) × (𝔹 → X))
  b = ×-retract a a

  c : retract (𝔹 → X) of (ℕ → X)
  c = retract-covariance fe' (binary , unary , binary-unary)

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

  e : retract (ℕ → X) × (ℕ → X) of (ℕ → X)
  e = retracts-compose (retracts-compose c d) b

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

TODO. Complete the following.

\begin{code}

{-
Cons-Snoc : (α : Cantor) → Cons (Snoc α) ＝ α
Cons-Snoc α = dfunext fe' (λ φ → γ φ α)
 where
  γ : (i : ℕ) (α : Cantor) → Cons (Head α , Tail α) i ＝ α i
  γ 0 α = 𝟚-equality-cases a b
   where
    a : head α ＝ ₀ → Cons (Head α , Tail α) 0 ＝ α 0
    a r = ap head (p ∙ q) ∙ r ⁻¹
     where
      s : Head α ＝ Zero
      s = Head₀ α r
      p : Cons (Head α , Tail α) ＝ Cons (Zero , Tail α ∘ transport-finite⁻¹ s)
      p = to-Cons-＝ {Head α} {Zero} (Head α) (Tail α) s {id} {transport-finite⁻¹ s}
      q : Cons (Zero , Tail α ∘ transport-finite⁻¹ s)
        ＝ ₀ ∶∶  Tail α (transport-finite⁻¹ s Zero-is-finite)
      q = Cons₀ (Tail α ∘ transport-finite⁻¹ s)
    b : head α ＝ ₁ → Cons (Head α , Tail α) 0 ＝ α 0
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

  γ (succ i) α = g
   where
    IH : Cons (Head α , Tail α) i ＝ α i
    IH = γ i (α)
    g : Cons (Head α , Tail α) (succ i) ＝ α (succ i)
    g = Cons (Head α , Tail α) (succ i) ＝⟨ {!!} ⟩
        {!!} ＝⟨ {!!} ⟩
        {!!} ＝⟨ {!!} ⟩
        {!!} ＝⟨ {!!} ⟩
        {!!} ＝⟨ {!!} ⟩
        α (succ i) ∎
-}

\end{code}

Added 20th December 2023.

The delay monad structure.

\begin{code}

ηD : {X : 𝓤 ̇ } → X → D X
ηD x = (Zero , λ _ → x)

δD : {X : 𝓤 ̇ } → D X → D X
δD (u , f) = (Succ u , f ∘ is-finite-down u)

\end{code}

Preservation of total separatedness.

\begin{code}

open import TypeTopology.TotallySeparated

D-is-totally-separated : (X : 𝓤 ̇ )
                       → is-totally-separated X
                       → is-totally-separated (D X)
D-is-totally-separated X τ = Σ¹-is-totally-separated (λ _ → X) (λ _ → τ)

\end{code}

Added 9th January 2024.

\begin{code}

D-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
          → (X → Y)
          → (D X → D Y)
D-functor f (u , π) = (u , f ∘ π)

D-functor-id : {X : 𝓤 ̇ }
             → D-functor (𝑖𝑑 X) ∼ 𝑖𝑑 (D X)
D-functor-id d = refl

D-functor-∘ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
              (f : X → Y) (g : Y → Z)
            → D-functor (g ∘ f) ＝ D-functor g ∘ D-functor f
D-functor-∘ f g = refl

D-functor-id-＝ : {X : 𝓤 ̇ }
               → D-functor (𝑖𝑑 X) ＝ 𝑖𝑑 (D X)
D-functor-id-＝ = refl

D-functor-∘-＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                (f : X → Y) (g : Y → Z)
               → D-functor (g ∘ f) ＝ D-functor g ∘ D-functor f
D-functor-∘-＝ f g = refl

open import UF.Sets
open import UF.Sets-Properties

D-is-set : {X : 𝓤 ̇ }
         → is-set X
         → is-set (D X)
D-is-set {𝓤} {X} X-is-set = Σ-is-set
                             (ℕ∞-is-set fe')
                             (λ u → Π-is-set fe' (λ φ → X-is-set))

to-D-＝ : {X : 𝓤 ̇ }
          (u u' : ℕ∞)
          (π  : is-finite u  → X)
          (π' : is-finite u' → X)
        → (Σ p ꞉ u ＝ u' , π ＝ π' ∘ transport is-finite p)
        → (u , π) ＝[ D X ] (u' , π')
to-D-＝ {𝓤} {X} u u π π (refl , refl) = refl

from-D-＝ : {X : 𝓤 ̇ }
            (u u' : ℕ∞)
            (π  : is-finite u  → X)
            (π' : is-finite u' → X)
          → (u , π) ＝[ D X ] (u' , π')
          → Σ p ꞉ u ＝ u' , (π ＝ π' ∘ transport is-finite p)
from-D-＝ {𝓤} {X} u u π π refl = (refl , refl)

\end{code}

This is something I am thinking about:

\begin{code}
{-
is-D-coalgebra-map : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                     (a : A → D A)
                     (b : B → D B)
                   → (A → B)
                   → 𝓤 ⊔ 𝓥 ̇
is-D-coalgebra-map {𝓤} {𝓥} {A} {B} α β f = β ∘ f ∼ D-functor f ∘ α
 where
  headᵃ : A → ℕ∞
  headᵃ = pr₁ ∘ α

  tailᵃ : (a : A) → is-finite (headᵃ a) → A
  tailᵃ = pr₂ ∘ α

  headᵇ : B → ℕ∞
  headᵇ = pr₁ ∘ β

  tailᵇ : (b : B) → is-finite (headᵇ b) → B
  tailᵇ = pr₂ ∘ β

  module _ {u v : ℕ∞}
         where

   t : u ＝ v → is-finite u → is-finite v
   t = transport is-finite

   s : u ＝ v → is-finite u → is-finite v
   s p (n , e) = n , (e ∙ p)

   ts : (p : u ＝ v) (φ : is-finite u) → t p φ ＝ s p φ
   ts refl (n , refl) = refl

  module _ (a : A)
           (p₁ : headᵃ a ＝ headᵇ (f a))
           (h₂ : (n : ℕ)
                 (q : ι n ＝ headᵃ a)
               → f (tailᵃ a (n , q)) ＝ tailᵇ (f a) (n , (q ∙ p₁)))
         where

   p₂ : f ∘ tailᵃ a ＝ tailᵇ (f a) ∘ transport is-finite p₁
   p₂ = dfunext fe' (λ (n , q) →
         (f ∘ tailᵃ a) (n , q) ＝⟨ h₂ n q ⟩
         tailᵇ (f a) (n , (q ∙ p₁)) ＝⟨ ap (tailᵇ (f a)) ((ts p₁ (n , q))⁻¹) ⟩
         (tailᵇ (f a) ∘ transport is-finite p₁) (n , q) ∎)

   I = D-functor f (α a) ＝⟨ refl ⟩
       (headᵃ a , f ∘ tailᵃ a) ＝⟨ I₀ ⟩
       (headᵇ (f a) , tailᵇ (f a)) ＝⟨ refl ⟩
       β (f a) ∎
        where
         I₀ = to-D-＝ (headᵃ a) (headᵇ (f a)) (f ∘ tailᵃ a) (tailᵇ (f a)) (p₁ , p₂)
-}

\end{code}
