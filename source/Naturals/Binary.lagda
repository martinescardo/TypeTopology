Martin Escardo, 16 Dec 2016. Updated June 2021.

Equivalent copy of the natural numbers with logarithmic-size elements.

We use a modification of binary notation to avoid leading zeros and
hence multiple representations of the same number.

The isomorphic copy is formally constructed from 0 by iterating the
functions left(n)=2n+1 and right(n)=2n+2. This is illustrated by the
following tree:

  ...   ...   ...  ...  ...  ...  ...   ...
   7     8     9    10  11   12    13   14
     \  /       \  /      \ /        \ /
      3           4        5          6
        \        /          \        /
            1                   2
              \                /

                       0

Applications:

 * We show how to define functions h : (n : ℕ) → A n by the recursion scheme

     h 0         = a
     h (left n)  = f n (h n)
     h (right n) = g n (h n)

   from given parameters a , f , g.

 * We construct a pairing function and hence an equivalence ℕ × ℕ ≃ ℕ.

 * Similarly we construct an equivalence ℕ ∔ ℕ ≃ ℕ.

 * We define faster arithmetic (addition and multiplication for the moment).

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Naturals.Binary where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Naturals.Properties
open import UF.Equiv
open import UF.Base
open import UF.EquivalenceExamples
open import UF.DiscreteAndSeparated

\end{code}

The functions left = n ↦ 2n+1 and right = n ↦ 2n+2:

\begin{code}

left right : ℕ → ℕ
left 0        = 1
left (succ n) = succ (succ (left n))
right n       = succ (left n)

NB-left-right : (n : ℕ) → left (succ n) ＝ succ (right n)
NB-left-right n = refl

NB-right-left : (n : ℕ) → right (succ n) ＝ succ (left (succ n))
NB-right-left n = refl

\end{code}

Modified binary rendering of the natural numbers:

\begin{code}

data 𝔹 : 𝓤₀ ̇ where
 Z : 𝔹
 L : 𝔹 → 𝔹
 R : 𝔹 → 𝔹

\end{code}

The successor function n ↦ n+1 on 𝔹:

\begin{code}

Succ : 𝔹 → 𝔹
Succ Z     = L Z
Succ (L m) = R m
Succ (R m) = L (Succ m)

\end{code}

Conversion between the two renderings:

\begin{code}

unary : 𝔹 → ℕ
unary Z     = 0
unary (L m) = left (unary m)
unary (R m) = right (unary m)

binary : ℕ → 𝔹
binary 0        = Z
binary (succ n) = Succ (binary n)

\end{code}

Next we show that the functions binary and unary are mutually
inverse, after we formulate and prove some lemmas for that.

First some commutation properties:

               left
          ℕ ─────────► ℕ
          │            │
   binary │            │ binary       (ldiagram)
          │            │
          ▼            ▼
          𝔹─────────► 𝔹
                L


               right
          ℕ ─────────► ℕ
          │            │
   binary │            │ binary       (rdiagram)
          │            │
          ▼            ▼
          𝔹─────────► 𝔹
                R


               Succ
          𝔹 ─────────► 𝔹
          │            │
    unary │            │ unary       (sdiagram)
          │            │
          ▼            ▼
          ℕ ─────────► ℕ
              succ

\begin{code}

ldiagram : (n : ℕ) → binary (left n) ＝ L (binary n)
ldiagram 0        = refl
ldiagram (succ n) = ap (Succ ∘ Succ) (ldiagram n)

rdiagram : (n : ℕ) → binary (right n) ＝ R (binary n)
rdiagram 0        = refl
rdiagram (succ n) = ap (Succ ∘ Succ) (rdiagram n)

sdiagram : (m : 𝔹) → unary (Succ m) ＝ succ (unary m)
sdiagram Z     = refl
sdiagram (L m) = refl
sdiagram (R m) = ap left (sdiagram m)

\end{code}

The functions unary and binary are mutually inverse, using the above
diagrams:

\begin{code}

unary-binary : (n : ℕ) → unary (binary n) ＝ n
unary-binary 0        = refl
unary-binary (succ n) =
 unary (binary (succ n)) ＝⟨ sdiagram (binary n) ⟩
 succ (unary (binary n)) ＝⟨ ap succ (unary-binary n) ⟩
 succ n                  ∎

binary-unary : (m : 𝔹) → binary (unary m) ＝ m
binary-unary Z     = refl
binary-unary (L m) =
 binary (unary (L m)) ＝⟨ ldiagram (unary m) ⟩
 L (binary (unary m)) ＝⟨ ap L (binary-unary m) ⟩
 L m                  ∎
binary-unary (R m) =
 binary (unary (R m)) ＝⟨ rdiagram (unary m) ⟩
 R (binary (unary m)) ＝⟨ ap R (binary-unary m) ⟩
 R m                  ∎

binary-equiv : 𝔹 ≃ ℕ
binary-equiv = qinveq unary (binary , binary-unary , unary-binary)

\end{code}

Example. We define a function height such that height (2ⁿ-1) = n.

The height of a number is its height in the following infinite tree:

  ...   ...   ...  ...  ...  ...  ...   ...
   7     8     9    10  11   12    13   14
     \  /       \  /      \ /        \ /
      3           4        5          6
        \        /          \        /
            1                   2
              \                /

                       0
\begin{code}

size : 𝔹 → ℕ
size Z     = 0
size (L m) = succ (size m)
size (R m) = succ (size m)

height : ℕ → ℕ
height n = size (binary n)

height-examples : (height 0  ＝ 0)
                × (height 1  ＝ 1)
                × (height 2  ＝ 1)
                × (height 3  ＝ 2)
                × (height 4  ＝ 2)
                × (height 5  ＝ 2)
                × (height 6  ＝ 2)
                × (height 7  ＝ 3)
                × (height 8  ＝ 3)
                × (height 9  ＝ 3)
                × (height 10 ＝ 3)
                × (height 11 ＝ 3)
                × (height 12 ＝ 3)
                × (height 13 ＝ 3)
                × (height 14 ＝ 3)
                × (height 15 ＝ 4)
                × (height 16 ＝ 4)
                × (height 17 ＝ 4)
height-examples = refl , refl , refl , refl , refl , refl , refl , refl , refl ,
                  refl , refl , refl , refl , refl , refl , refl , refl , refl
\end{code}

The above diagrams give the following equations for the functino height.

\begin{code}

height-equation₀ : height 0 ＝ 0
height-equation₀ = refl

height-equationₗ : (n : ℕ) → height (left n) ＝ succ (height n)
height-equationₗ n =
 height (left n)        ＝⟨ refl ⟩
 size (binary (left n)) ＝⟨ ap size (ldiagram n) ⟩
 size (L (binary n))    ＝⟨ refl ⟩
 succ (size (binary n)) ＝⟨ refl ⟩
 succ (height n)        ∎

height-equationᵣ : (n : ℕ) → height (right n) ＝ succ (height n)
height-equationᵣ n =
 height (right n)       ＝⟨ refl ⟩
 size (binary (right n))＝⟨ ap size (rdiagram n) ⟩
 size (R (binary n))    ＝⟨ refl ⟩
 succ (size (binary n)) ＝⟨ refl ⟩
 succ (height n)        ∎


\end{code}

We now show that height (2ⁿ-1) ＝ n.

\begin{code}

height-power2-equation : (n : ℕ) → height (pred (power2 n)) ＝ n
height-power2-equation n = VI
 where
  powerl : ℕ → ℕ
  powerl 0        = 0
  powerl (succ n) = left (powerl n)

  I : (n : ℕ) → left (double n) ＝ succ (double (double n))
  I 0        = refl
  I (succ n) = ap (succ ^ 4) (I n)

  II : (n : ℕ) → left (power2 n) ＝ succ (power2 (succ n))
  II 0        = refl
  II (succ n) = I (power2 n)

  III : (n : ℕ) → succ (powerl n) ＝ power2 n
  III 0        = refl
  III (succ n) = succ-lc p
   where
    p = succ (succ (powerl (succ n))) ＝⟨ refl ⟩
        succ (succ (left (powerl n))) ＝⟨ refl ⟩
        left (succ (powerl n))        ＝⟨ ap left (III n) ⟩
        left (power2 n)               ＝⟨ II n ⟩
        succ (power2 (succ n))        ∎

  IV : (n : ℕ) → powerl n ＝ pred (power2 n)
  IV n = ap pred (III n)

  V : (n : ℕ) → height (powerl n) ＝ n
  V 0        = refl
  V (succ n) =
   height (powerl (succ n)) ＝⟨ refl ⟩
   height (left (powerl n)) ＝⟨ height-equationₗ (powerl n) ⟩
   succ (height (powerl n)) ＝⟨ ap succ (V n) ⟩
   succ n                   ∎

  VI = height (pred (power2 n)) ＝⟨ ap height ((IV n)⁻¹) ⟩
       height (powerl n)        ＝⟨ V n ⟩
       n                        ∎

\end{code}

This concludes the height example.

The unary and binary induction principles:

\begin{code}

ℕ-induction : {A : ℕ → 𝓤 ̇ }
            → A 0
            → (∀ n → A n → A (succ n))
            → ∀ n → A n
ℕ-induction {𝓤} {A} a f = h
 where
  h : ∀ n → A n
  h 0     = a
  h (succ n) = f n (h n)

𝔹-induction : {B : 𝔹 → 𝓤 ̇ }
            → B Z
            → (∀ m → B m → B (L m))
            → (∀ m → B m → B (R m))
            → ∀ m → B m
𝔹-induction {𝓤} {B} b f g = h
 where
  h : ∀ m → B m
  h Z  = b
  h (L m) = f m (h m)
  h (R m) = g m (h m)

\end{code}

But also we have unary induction on 𝔹 and binary induction on ℕ:

\begin{code}

unary-induction-on-𝔹 : {B : 𝔹 → 𝓤 ̇ }
                     → B Z
                     → (∀ n → B n → B (Succ n))
                     → ∀ n → B n
unary-induction-on-𝔹 {𝓤} {B} b f = h
 where
  𝒇 : (n : ℕ) → B (binary n) → B (binary (succ n))
  𝒇 n = f (binary n)

  𝒉 : (n : ℕ) → B (binary n)
  𝒉 0        = b
  𝒉 (succ n) = 𝒇 n (𝒉 n)

  𝕙 : (m : 𝔹) → B (binary (unary m))
  𝕙 m = 𝒉 (unary m)

  t : (m : 𝔹) → B (binary (unary m)) → B m
  t m = transport B (binary-unary m)

  h : (m : 𝔹) → B m
  h m = t m (𝕙 m)

\end{code}

The following is the counter-part of the above, but with a more
informative conclusion. Not only the hypotheses

     a : A 0
     f : (n : ℕ) → A n → A (left n)
     g : (n : ℕ) → A n → A (right n)

give the conclusion

     h : (n : ℕ) → A n

but also the equations

     h 0         = a
     h (left n)  = f n (h n)
     h (right n) = g n (h n)

which can be considered as a sort of definition of h by "dependent
binary recursion" on ℕ from the data a,f,g.

\begin{code}

Binary-induction-equations : {A : ℕ → 𝓤 ̇ }
                             (a : A 0)
                             (f : (n : ℕ) → A n → A (left n))
                             (g : (n : ℕ) → A n → A (right n))
                             (h : (n : ℕ) → A n)
                           → 𝓤 ̇
Binary-induction-equations a f g h = eq0 × eqleft × eqright
 where
  eq0     = h 0 ＝ a
  eqleft  = (n : ℕ) → h (left n)  ＝ f n (h n)
  eqright = (n : ℕ) → h (right n) ＝ g n (h n)

Binary-induction-on-ℕ : (A : ℕ → 𝓤 ̇ )
                        (a : A 0)
                        (f : (n : ℕ) → A n → A (left n))
                        (g : (n : ℕ) → A n → A (right n))
                      → Σ h ꞉ ((n : ℕ) → A n) , Binary-induction-equations a f g h
Binary-induction-on-ℕ A a f g = h , refl , IIIa , IIIb
 where
  𝒇 : (m : 𝔹) → A (unary m) → A (left (unary m))
  𝒇 m = f (unary m)

  𝒈 : (m : 𝔹) → A (unary m) → A (right (unary m))
  𝒈 m = g (unary m)

  𝒉 : (m : 𝔹) → A (unary m)
  𝒉 Z     = a
  𝒉 (L m) = 𝒇 m (𝒉 m)
  𝒉 (R m) = 𝒈 m (𝒉 m)

  𝕙 : (n : ℕ) → A (unary (binary n))
  𝕙 n = 𝒉 (binary n)

  τ = transport

  h : (n : ℕ) → A n
  h n = τ A (unary-binary n) (𝕙 n)

  Ia : (n : ℕ) → unary-binary (left n) ＝ ap unary (ldiagram n) ∙ ap left (unary-binary n)
  Ia n = ℕ-is-set _ _

  IIa : (n : ℕ) → τ (A ∘ unary) (ldiagram n) (𝕙 (left n)) ＝ 𝒇 (binary n) (𝕙 n)
  IIa n =
   τ (A ∘ unary) (ldiagram n) (𝕙 (left n))          ＝⟨ refl ⟩
   τ (A ∘ unary) (ldiagram n) (𝒉 (binary (left n))) ＝⟨ apd 𝒉 (ldiagram n) ⟩
   𝒉 (L (binary n))                                 ＝⟨ refl ⟩
   𝒇 (binary n) (𝒉 (binary n))                      ＝⟨ refl ⟩
   𝒇 (binary n) (𝕙 n)                               ∎

  IIIa : (n : ℕ) → h (left n) ＝ f n (h n)
  IIIa n =
   h (left n)                                                                ＝⟨ refl ⟩
   τ A (unary-binary (left n)) (𝕙 (left n))                                  ＝⟨ by-Ia ⟩
   τ A (ap unary (ldiagram n) ∙ ap left (unary-binary n)) (𝕙 (left n))       ＝⟨ by-transport-∙ ⟩
   τ A (ap left (unary-binary n)) (τ A (ap unary (ldiagram n)) (𝕙 (left n))) ＝⟨ by-transport-ap ⟩
   τ A (ap left (unary-binary n)) (τ (A ∘ unary) (ldiagram n) (𝕙 (left n)))  ＝⟨ by-IIa ⟩
   τ A (ap left (unary-binary n)) (𝒇 (binary n) (𝕙 n))                       ＝⟨ refl ⟩
   τ A (ap left (unary-binary n)) (f (unary (binary n)) (𝕙 n))               ＝⟨ by-transport-ap-again ⟩
   τ (A ∘ left) (unary-binary n) (f (unary (binary n)) (𝕙 n))                ＝⟨ by-naturality ⟩
   f n (τ A (unary-binary n) (𝕙 n))                                          ＝⟨ refl ⟩
   f n (h n)                                                                 ∎
    where
     by-Ia                 = ap (λ - → τ A - (𝕙 (left n))) (Ia n)
     by-transport-∙        = transport-∙ A (ap unary (ldiagram n)) (ap left (unary-binary n))
     by-transport-ap       = ap (τ A (ap left (unary-binary n))) ((transport-ap A unary (ldiagram n))⁻¹)
     by-IIa                = ap (τ A (ap left (unary-binary n))) (IIa n)
     by-transport-ap-again = (transport-ap A left (unary-binary n))⁻¹
     by-naturality         = (Nats-are-natural-∼ A (A ∘ left) f (unary-binary n) (𝕙 n))⁻¹

\end{code}

By symmetry, the proof is concluded. But we have to write the symmetric argument in Agda:

\begin{code}

  Ib : (n : ℕ) → unary-binary (right n) ＝ ap unary (rdiagram n) ∙ ap right (unary-binary n)
  Ib n = ℕ-is-set _ _

  IIb : (n : ℕ) → τ (A ∘ unary) (rdiagram n) (𝕙 (right n)) ＝ 𝒈 (binary n) (𝕙 n)
  IIb n =
   τ (A ∘ unary) (rdiagram n) (𝕙 (right n))          ＝⟨ refl ⟩
   τ (A ∘ unary) (rdiagram n) (𝒉 (binary (right n))) ＝⟨ apd 𝒉 (rdiagram n) ⟩
   𝒉 (R (binary n))                                  ＝⟨ refl ⟩
   𝒈 (binary n) (𝒉 (binary n))                       ＝⟨ refl ⟩
   𝒈 (binary n) (𝕙 n)                                ∎

  IIIb : (n : ℕ) → h (right n) ＝ g n (h n)
  IIIb n =
   h (right n)                                                                 ＝⟨ refl ⟩
   τ A (unary-binary (right n)) (𝕙 (right n))                                  ＝⟨ by-Ib ⟩
   τ A (ap unary (rdiagram n) ∙ ap right (unary-binary n)) (𝕙 (right n))       ＝⟨ by-transport-∙ ⟩
   τ A (ap right (unary-binary n)) (τ A (ap unary (rdiagram n)) (𝕙 (right n))) ＝⟨ by-transport-ap ⟩
   τ A (ap right (unary-binary n)) (τ (A ∘ unary) (rdiagram n) (𝕙 (right n)))  ＝⟨ by-IIb ⟩
   τ A (ap right (unary-binary n)) (𝒈 (binary n) (𝕙 n))                        ＝⟨ refl ⟩
   τ A (ap right (unary-binary n)) (g (unary (binary n)) (𝕙 n))                ＝⟨ by-transport-ap-again ⟩
   τ (A ∘ right) (unary-binary n) (g (unary (binary n)) (𝕙 n))                 ＝⟨ by-naturarity ⟩
   g n (τ A (unary-binary n) (𝕙 n))                                            ＝⟨ refl ⟩
   g n (h n)                                                                   ∎
    where
     by-Ib                 = ap (λ - → τ A - (𝕙 (right n))) (Ib n)
     by-transport-∙        = transport-∙ A (ap unary (rdiagram n)) (ap right (unary-binary n))
     by-transport-ap       = ap (τ A (ap right (unary-binary n))) ((transport-ap A unary (rdiagram n))⁻¹)
     by-IIb                = ap (τ A (ap right (unary-binary n))) (IIb n)
     by-transport-ap-again = (transport-ap A right (unary-binary n))⁻¹
     by-naturarity         = (Nats-are-natural-∼ A (A ∘ right) g (unary-binary n) (𝕙 n))⁻¹

\end{code}

(The above stronger induction principle Binary-induction-on-ℕ,
generalizing binary-induction-on-ℕ below, was added 10-11 June 2021.)

TODO. Replace Σ by ∃! in the statement of Binary-induction-on-ℕ
(easy but laborious - see my MGS'2019 lecture notes).

Of course, we get the weaker induction principle (with lower case b)
by projection:

\begin{code}

binary-induction-on-ℕ : (A : ℕ → 𝓤 ̇ )
                      → A 0
                      → ((n : ℕ) → A n → A (left n))
                      → ((n : ℕ) → A n → A (right n))
                      → (n : ℕ) → A n
binary-induction-on-ℕ A a f g = pr₁ (Binary-induction-on-ℕ A a f g)


Binary-induction-uniqueness : {A : ℕ → 𝓤 ̇ }
                              (a   : A 0)
                              (f   : (n : ℕ) → A n → A (left n))
                              (g   : (n : ℕ) → A n → A (right n))
                              (h k : ((n : ℕ) → A n))
                            → Binary-induction-equations a f g h
                            → Binary-induction-equations a f g k
                            → h ∼ k
Binary-induction-uniqueness a f g h k (p0 , pleft , pright) (q0 , qleft , qright) =

 binary-induction-on-ℕ (λ n → h n ＝ k n)

  (h 0 ＝⟨ p0 ⟩
   a   ＝⟨ q0 ⁻¹ ⟩
   k 0 ∎)

  (λ (n : ℕ) (s : h n ＝ k n) → h (left n)   ＝⟨ pleft n ⟩
                               f n (h n)    ＝⟨ ap (f n) s ⟩
                               f n (k n)    ＝⟨ (qleft n)⁻¹ ⟩
                               k (left n)   ∎)

  (λ (n : ℕ) (s : h n ＝ k n) → h (right n)   ＝⟨ pright n ⟩
                               g n (h n)     ＝⟨ ap (g n) s ⟩
                               g n (k n)     ＝⟨ (qright n)⁻¹ ⟩
                               k (right n)   ∎)

\end{code}

Example revisited. We can define the above height function in the
following alternative way.

\begin{code}

Height : Σ height' ꞉ (ℕ → ℕ)
                   ,           (height' 0         ＝ 0)
                   × ((n : ℕ) → height' (left n)  ＝ succ (height' n))
                   × ((n : ℕ) → height' (right n) ＝ succ (height' n))
Height = Binary-induction-on-ℕ (λ _ → ℕ) 0 (λ _ → succ) (λ _ → succ)

\end{code}

The new function still computes, of course:

\begin{code}

Height-example₁₃ : height 13 ＝ pr₁ Height 13
Height-example₁₃ = refl

\end{code}

Example. Because the following functions satisfy the same defining
equations, they coincide:

\begin{code}

Height-example : (n : ℕ) → height n ＝ pr₁ Height n
Height-example =
 Binary-induction-uniqueness
 0
 (λ _ → succ)
 (λ _ → succ)
 height
 (λ n → pr₁ Height n)
 (height-equation₀ , height-equationₗ , height-equationᵣ)
 (pr₁ (pr₂ Height) , pr₁ (pr₂ (pr₂ Height)) , pr₂ (pr₂ (pr₂ Height)))

\end{code}

We get a pairing function as follows, using a rather minimal amount of
arithmetic (14th July 2018).

We use binary notation to simplify the definition. An alternative
would be to work with the usual unary notation, using binary
induction. However, this would prevent us from using pattern matching,
which gives a more intuitive definition.

\begin{code}

first' : 𝔹 → ℕ
first' Z     = 0
first' (L b) = succ (first' b)
first' (R b) = 0

second' : 𝔹 → 𝔹
second' Z     = Z
second' (L b) = second' b
second' (R b) = Succ b

pair' : ℕ → ℕ → 𝔹
pair' 0        0        = Z
pair' (succ n) 0        = L (pair' n 0)
pair' 0        (succ k) = R (binary k)
pair' (succ n) (succ k) = L (pair' n (succ k))

pair'-claim : (n k : ℕ) → pair' (succ n) k ＝ L (pair' n k)
pair'-claim n 0        = refl
pair'-claim n (succ k) = refl

first'-lemma : (n k : ℕ) → first' (pair' n k) ＝ n
first'-lemma 0        0        = refl
first'-lemma 0        (succ k) = refl
first'-lemma (succ n) 0        = ap succ (first'-lemma n 0)
first'-lemma (succ n) (succ k) = ap succ (first'-lemma n (succ k))

second'-lemma : (n k : ℕ) → second' (pair' n k) ＝ binary k
second'-lemma 0     0           = refl
second'-lemma 0     (succ k)    = refl
second'-lemma (succ n) 0        = second'-lemma n 0
second'-lemma (succ n) (succ k) = second'-lemma n (succ k)

pair'-lemma : (b : 𝔹) → pair' (first' b) (unary (second' b)) ＝ b
pair'-lemma Z     = refl
pair'-lemma (L b) =
 pair' (succ (first' b)) (unary (second' b)) ＝⟨ pair'-claim (first' b) (unary (second' b)) ⟩
 L (pair' (first' b) (unary (second' b)))    ＝⟨ ap L (pair'-lemma b) ⟩
 L b                                         ∎
pair'-lemma (R b) =
 pair' (first' (R b)) (unary (second' (R b))) ＝⟨ refl ⟩
 pair' 0 (unary (Succ b))                     ＝⟨ ap (pair' 0) (sdiagram b) ⟩
 pair' 0 (succ (unary b))                     ＝⟨ refl ⟩
 R (binary (unary b))                         ＝⟨ ap R (binary-unary b) ⟩
 R b                                          ∎

pair : ℕ × ℕ → ℕ
pair (n , k) = unary (pair' n k)

first second : ℕ → ℕ
first  = first' ∘ binary
second = unary ∘ second' ∘ binary

first-pair : (n k : ℕ) → first (pair (n , k)) ＝ n
first-pair n k =
 first (pair (n , k))                ＝⟨ refl ⟩
 first' (binary (unary (pair' n k))) ＝⟨ ap first' (binary-unary (pair' n k)) ⟩
 first' (pair' n k)                  ＝⟨ first'-lemma n k ⟩
 n                                   ∎

second-pair : (n k : ℕ) → second (pair (n , k)) ＝ k
second-pair n k =
 second (pair (n , k))                        ＝⟨ refl ⟩
 unary (second' (binary (unary (pair' n k)))) ＝⟨ ap (unary ∘ second') (binary-unary (pair' n k)) ⟩
 unary (second' (pair' n k))                  ＝⟨ ap unary (second'-lemma n k) ⟩
 unary (binary k)                             ＝⟨ unary-binary k ⟩
 k                                            ∎

riap : ℕ → ℕ × ℕ
riap m = (first m , second m)

pair-riap : (m : ℕ) → pair (riap m) ＝ m
pair-riap m =
 pair (riap m)                                                  ＝⟨ refl ⟩
 unary (pair' (first' (binary m)) (unary (second' (binary m)))) ＝⟨ ap unary (pair'-lemma (binary m)) ⟩
 unary (binary m)                                               ＝⟨ unary-binary m ⟩
 m                                                              ∎

riap-pair : (z : ℕ × ℕ) → riap (pair z) ＝ z
riap-pair (n , k) =
 riap (pair (n , k))                            ＝⟨ refl ⟩
 (first (pair (n , k)) , second (pair (n , k))) ＝⟨ to-×-＝ (first-pair n k) (second-pair n k) ⟩
 n , k                                          ∎

pairing : ℕ × ℕ ≃ ℕ
pairing = qinveq pair  (riap , riap-pair , pair-riap)

\end{code}

We now show that ℕ + ℕ ≃ ℕ (July 2018).

\begin{code}

ℕ-plus-𝟙 : ℕ ∔ 𝟙 ≃ ℕ
ℕ-plus-𝟙 = qinveq f (g , ε , η)
 where
  f : ℕ ∔ 𝟙 {𝓤₀} → ℕ
  f (inl n) = succ n
  f (inr *) = 0

  g : ℕ → ℕ ∔ 𝟙
  g 0        = inr ⋆
  g (succ n) = inl n

  η : (n : ℕ) → f (g n) ＝ n
  η 0        = refl
  η (succ n) = refl

  ε : (z : ℕ ∔ 𝟙) → g (f z) ＝ z
  ε (inl n) = refl
  ε (inr ⋆) = refl

two-𝔹-plus-𝟙 : 𝔹 ∔ 𝔹 ∔ 𝟙 ≃ 𝔹
two-𝔹-plus-𝟙 = qinveq f (g , ε , η)
 where
  f : 𝔹 ∔ 𝔹 ∔ 𝟙 {𝓤₀} → 𝔹
  f (inl b)       = L b
  f (inr (inl b)) = R b
  f (inr (inr ⋆)) = Z

  g : 𝔹 → 𝔹 ∔ 𝔹 ∔ 𝟙
  g Z = inr (inr ⋆)
  g (L b) = inl b
  g (R b) = inr (inl b)

  η : (b : 𝔹) → f (g b) ＝ b
  η Z     = refl
  η (L b) = refl
  η (R b) = refl

  ε : (z : 𝔹 ∔ 𝔹 ∔ 𝟙) → g (f z) ＝ z
  ε (inl b)       = refl
  ε (inr (inl b)) = refl
  ε (inr (inr ⋆)) = refl

two-ℕ-plus-𝟙 : ℕ ∔ ℕ ∔ 𝟙 ≃ ℕ
two-ℕ-plus-𝟙 =
    ℕ ∔ (ℕ ∔ 𝟙)    ≃⟨ +-cong (≃-sym binary-equiv) (Ap+ 𝟙 (≃-sym binary-equiv)) ⟩
    𝔹 ∔ (𝔹 ∔ 𝟙)    ≃⟨ two-𝔹-plus-𝟙 ⟩
    𝔹              ≃⟨ binary-equiv ⟩
    ℕ              ■

two-ℕ : ℕ ∔ ℕ ≃ ℕ
two-ℕ =
   ℕ ∔ ℕ        ≃⟨ Ap+ ℕ (≃-sym ℕ-plus-𝟙) ⟩
   (ℕ ∔ 𝟙) ∔ ℕ  ≃⟨ +comm ⟩
   ℕ ∔ ℕ ∔ 𝟙    ≃⟨ two-ℕ-plus-𝟙 ⟩
   ℕ            ■

\end{code}

The following examples show that these equivalences compute:

\begin{code}

module examples where

 example-riap : riap 17 ＝ (1 , 4)
 example-riap = refl

 example-pair : pair (1 , 4) ＝ 17
 example-pair = refl

\end{code}

The following is from the original version in 2016, but we swapped it
with the above pairing example from 2018.

Some operations performed directly in modified binary, for the sake of
efficiency, with their correctness verified.

The doubling function n ↦ 2n on 𝔹:

\begin{code}

Double : 𝔹 → 𝔹
Double Z     = Z
Double (L m) = R (Double m)
Double (R m) = Succ (Succ (R (Double m)))

Double-lemma : (m : 𝔹) → Succ (Succ (Double m)) ＝ Double (Succ m)
Double-lemma Z     = refl
Double-lemma (L m) = refl
Double-lemma (R m) = ap R (Double-lemma m)

ddiagram : (n : ℕ) → binary (double n) ＝ Double (binary n)
ddiagram 0        = refl
ddiagram (succ n) =
 binary (double (succ n))        ＝⟨ refl ⟩
 Succ (Succ (binary (double n))) ＝⟨ ap (Succ ∘ Succ) (ddiagram n) ⟩
 Succ (Succ (Double (binary n))) ＝⟨ Double-lemma (binary n) ⟩
 Double (Succ (binary n))        ＝⟨ refl ⟩
 Double (binary (succ n))        ∎

\end{code}

Now addition, with a faster version in binary:

\begin{code}

_+_ : ℕ → ℕ → ℕ
x + 0      = x
x + succ y = succ (x + y)

_+♭_ : 𝔹 → 𝔹 → 𝔹
x    +♭  Z    = x
Z    +♭  L y  = L y
L x  +♭  L y  = R (x +♭ y)
R x  +♭  L y  = L (Succ (x +♭ y))
Z    +♭  R y  = R y
L x  +♭  R y  = L (Succ (x +♭ y))
R x  +♭  R y  = R (Succ (x +♭ y))

+♭-lemma : ∀ m n → Succ (m +♭ n) ＝ m +♭ Succ n
+♭-lemma Z      Z    = refl
+♭-lemma (L m)  Z    = refl
+♭-lemma (R m)  Z    = refl
+♭-lemma Z     (L n) = refl
+♭-lemma (L m) (L n) = refl
+♭-lemma (R m) (L n) = refl
+♭-lemma Z     (R n) = refl
+♭-lemma (L m) (R n) = ap R (+♭-lemma m n)
+♭-lemma (R m) (R n) = ap (λ - → L (Succ -)) (+♭-lemma m n)

+diagram : ∀ m n → binary (m + n) ＝ binary m +♭ binary n
+diagram m 0        = refl
+diagram m (succ n) =
 binary (m + succ n)         ＝⟨ refl ⟩
 Succ (binary (m + n))       ＝⟨ ap Succ (+diagram m n) ⟩
 Succ (binary m +♭ binary n) ＝⟨ +♭-lemma (binary m) (binary n) ⟩
 binary m +♭ Succ (binary n) ＝⟨ refl ⟩
 binary m +♭ binary (succ n) ∎

\end{code}

Even faster binary addition (linear time).  We define the following
operations with the following specifications:

\begin{code}

_+₀_ _+₁_ _+₂_ : 𝔹 → 𝔹 → 𝔹
Succ₂          : 𝔹 → 𝔹

+₀-spec    : ∀ x y → x +₀ y ＝ x +♭ y
+₁-spec    : ∀ x y → x +₁ y ＝ Succ (x +♭ y)
+₂-spec    : ∀ x y → x +₂ y ＝ Succ (Succ (x +♭ y))
Succ₂-spec : ∀ x →  Succ₂ x ＝ Succ (Succ x)

\end{code}

Definitions:

\begin{code}

x    +₀  Z    = x
Z    +₀  L y  = L y
L x  +₀  L y  = R (x +₀ y)
R x  +₀  L y  = L (x +₁ y)
Z    +₀  R y  = R y
L x  +₀  R y  = L (x +₁ y)
R x  +₀  R y  = R (x +₁ y)

x    +₁  Z    = Succ x
Z    +₁  L y  = R y
L x  +₁  L y  = L (x +₁ y)
R x  +₁  L y  = R (x +₁ y)
Z    +₁  R y  = L (Succ y)
L x  +₁  R y  = R (x +₁ y)
R x  +₁  R y  = L (x +₂ y)

x    +₂  Z    = Succ₂ x
Z    +₂  L y  = L (Succ y)
L x  +₂  L y  = R (x +₁ y)
R x  +₂  L y  = L (x +₂ y)
Z    +₂  R y  = R (Succ y)
L x  +₂  R y  = L (x +₂ y)
R x  +₂  R y  = R (x +₂ y)

Succ₂ Z     = R Z
Succ₂ (L x) = L (Succ x)
Succ₂ (R x) = R (Succ x)

\end{code}

Correctness proof:

\begin{code}

+₀-spec x     Z     = refl
+₀-spec Z     (L y) = refl
+₀-spec (L x) (L y) = ap R (+₀-spec x y)
+₀-spec (R x) (L y) = ap L (+₁-spec x y)
+₀-spec Z     (R y) = refl
+₀-spec (L x) (R y) = ap L (+₁-spec x y)
+₀-spec (R x) (R y) = ap R (+₁-spec x y)

+₁-spec x     Z     = refl
+₁-spec Z     (L y) = refl
+₁-spec (L x) (L y) = ap L (+₁-spec x y)
+₁-spec (R x) (L y) = ap R (+₁-spec x y)
+₁-spec Z (R y)     = refl
+₁-spec (L x) (R y) = ap R (+₁-spec x y)
+₁-spec (R x) (R y) = ap L (+₂-spec x y)

+₂-spec x     Z     = Succ₂-spec x
+₂-spec Z     (L y) = refl
+₂-spec (L x) (L y) = ap R (+₁-spec x y)
+₂-spec (R x) (L y) = ap L (+₂-spec x y)
+₂-spec Z (R y)     = refl
+₂-spec (L x) (R y) = ap L (+₂-spec x y)
+₂-spec (R x) (R y) = ap R (+₂-spec x y)

Succ₂-spec Z     = refl
Succ₂-spec (L x) = refl
Succ₂-spec (R x) = refl

\end{code}

Now multiplication.

\begin{code}

_*_ : ℕ → ℕ → ℕ
m * 0 = 0
m * succ n = m * n + m -- m (n+1) = mn + m

_*♭_ : 𝔹 → 𝔹 → 𝔹
m *♭ Z = Z
m *♭ L n = Double (m *♭ n) +♭ m
m *♭ R n = Double (m *♭ n +♭ m)

_*₁_ : 𝔹 → 𝔹 → 𝔹
m    *₁ Z = Z
Z    *₁ L n  = Z
L m  *₁ L n  = L (Double (m *₁ n) +₀ m +₀ n) -- (2m+1) (2n+1) = 4mn + 2m + 2n + 1 = 2 (2mn+m+n)+1
R m  *₁ L n  = R (Double (m *₁ n +₀ n) +₀ m) -- (2m+2) (2n+1) = 4mn + 2m + 4n + 2 = 2 (2 (mn+n)+m)+2
Z    *₁ R n  = Z
L m  *₁ R n  = R (Double (m *₁ n +₀ m) +₀ n)
R m  *₁ R n  = Double (Double (m *₁ n +₀ (m +₁ n))) -- (2m+2)(2n+2) = 4mn + 4m + 4n + 4 = 4(mn + m + n + 1)

\end{code}

TODO. A proof for Multiplication.

Here is feeble evidence for the moment, in the form of an experiment:

\begin{code}

test : unary (binary 172 *₁ binary 133) ＝ 172 * 133
test = refl

\end{code}

Faster double, by specializing addition x ↦ x + x:

\begin{code}

double₀ double₁ double₂ : 𝔹 → 𝔹
double₀-spec : ∀ x → double₀ x ＝ x +₀ x
double₁-spec : ∀ x → double₁ x ＝ x +₁ x
double₂-spec : ∀ x → double₂ x ＝ x +₂ x

\end{code}

Can be understood as transducer with three states:

\begin{code}

double₀ Z     = Z
double₀ (L x) = R (double₀ x)
double₀ (R x) = R (double₁ x)

double₁ Z     = L Z
double₁ (L x) = L (double₁ x)
double₁ (R x) = L (double₂ x)

double₂ Z     = R Z
double₂ (L x) = R (double₁ x)
double₂ (R x) = R (double₂ x)

double₀-spec Z     = refl
double₀-spec (L x) = ap R (double₀-spec x)
double₀-spec (R x) = ap R (double₁-spec x)

double₁-spec Z     = refl
double₁-spec (L x) = ap L (double₁-spec x)
double₁-spec (R x) = ap L (double₂-spec x)

double₂-spec Z     = refl
double₂-spec (L x) = ap R (double₁-spec x)
double₂-spec (R x) = ap R (double₂-spec x)

\end{code}

And finally the fixities assumed above:

\begin{code}

infixl 6 _+_
infixl 7 _*_
infixl 6 _+♭_
infixl 7 _*♭_
infixl 6 _+₁_
infixl 6 _+₀_
infixl 7 _*₁_

\end{code}
