Martin Escardo, 21th April 2023

Based on Section 8.1 of the paper https://doi.org/10.2168/LMCS-4(3:3)2008

Let 𝟚 be the two-point set with elements 0 and 1.

Consider a given boolean function f : 𝟚ⁿ → 𝟚.

Definition. A *root* of f is some x in 𝟚ⁿ such that f x = 0.

Definition. A *putative root* of f is any x in 𝟚ⁿ such that if f has
some root, then x is a root.

Example. If f doesn't have any root, then any x in 𝟚ⁿ is putative root.

Example. If x is a root, then x is a putative root.

Theorem. For any n, there is a formula that mentions only the variable
𝕗 and the constant 0 such that for any given function f: 𝟚^n → 𝟚, the
formula gives a putative root of f when the variable is substituted
for f.

Example. For n = 3, we have the putative root x := (x₀,x₁,x₂) where

  y  := f(0,0,f(0,0,0))
  x₀ := f(0,y,f(0,y,0))
  x₁ := f(x₀,0,f(x₀,0,0))
  x₂ := f(x₀,x₁,0)

The purpose of this Agda file is to construct such a formula for any
given n, and prove that it indeed gives a putative root.

Because this file is intended for a general public of mathematicians
and computer scientists, we include some remarks that are expected to
be obvious to Agda practioners.

Agda is a computer language based on Martin-Löf Type Theory, which in
turn is the core of HoTT/UF. In this development we adopt the UF
approach to mathematics.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --no-sized-types --no-guardedness --auto-inline #-}

open import MLTT.Spartan hiding (_^_)
open import UF.FunExt

module Various.RootsOfBooleanFunctions (fe : Fun-Ext) where

open import MLTT.Athenian
open import MLTT.Two-Properties

\end{code}

A version of the type of n-tuples of elements of a type X, where Fin n
is the type of numbers 0, ..., n-1 (and is empty when n is 0):

\begin{code}

_^_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X ^ n = Fin n → X

\end{code}

The unique element of the empty tuple:

\begin{code}

!0 : {X : 𝓤 ̇ } → X ^ 0
!0 ()

\end{code}

Any two elements of this type are equal:

\begin{code}

!0-uniqueness' : {X : 𝓤 ̇ } {x y : X ^ 0} (i : Fin 0) → x i ＝ y i
!0-uniqueness' ()

!0-uniqueness : {X : 𝓤 ̇ } {x y : X ^ 0} → x ＝ y
!0-uniqueness = dfunext fe !0-uniqueness'

\end{code}

For any f : 𝟚 → 𝟚, we can check whether it is constantly 1 by checking
whether f (f 0) is 1, which is easily proved by case analysis on the
value of f 0:

\begin{code}

motivating-fact : (f : 𝟚 → 𝟚) →  f (f ₀) ＝ ₁ → (n : 𝟚) → f n ＝ ₁
motivating-fact f r = γ (f ₀) refl r
 where
  γ : (n₀ : 𝟚) → f ₀ ＝ n₀ → f n₀ ＝ ₁ → (n : 𝟚) → f n ＝ ₁
  γ ₀ s r ₀ = r
  γ ₀ s r ₁ = 𝟘-elim (zero-is-not-one (s ⁻¹ ∙ r))
  γ ₁ s r ₀ = s
  γ ₁ s r ₁ = r

\end{code}

Motivated by this, we define:

\begin{code}

ε𝟚 : (𝟚 → 𝟚) → 𝟚
ε𝟚 f = f ₀

A𝟚 : (𝟚 → 𝟚) → 𝟚
A𝟚 f = f (ε𝟚 f)

\end{code}

The desired property of A𝟚 is the following, which follows from the
motivating fact, in one direction, and directly in the other
direction:

\begin{code}

A𝟚-property→ : (f : 𝟚 → 𝟚) → A𝟚 f ＝ ₁ → (b : 𝟚) → f b ＝ ₁
A𝟚-property→ = motivating-fact

A𝟚-property← : (f : 𝟚 → 𝟚) → ((b : 𝟚) → f b ＝ ₁) → A𝟚 f ＝ ₁
A𝟚-property← f α = α (ε𝟚 f)

\end{code}

From this it follows directly that for any f : 𝟚 → 𝟚 we can find a
boolean b₀ such that if f b₀ ＝ ₁ then f n ＝ ₁ for every boolean b:

\begin{code}

σ𝟚 : (f : 𝟚 → 𝟚) → Σ b₀ ꞉ 𝟚 , (f b₀ ＝ ₁ → (b : 𝟚) → f b ＝ ₁)
σ𝟚 f = ε𝟚 f , A𝟚-property→ f

\end{code}

The functional ε𝟚 computes a putative root:

\begin{code}

ε𝟚-gives-putative-root : {n : ℕ} (f : 𝟚 → 𝟚)
                       → (Σ b ꞉ 𝟚 , f b ＝ ₀)
                       → f (ε𝟚 f) ＝ ₀
ε𝟚-gives-putative-root {n} f (b , r) =
 different-from-₁-equal-₀
  (λ (s : A𝟚 f ＝ ₁) → zero-is-not-one
                       (₀   ＝⟨ r ⁻¹ ⟩
                        f b ＝⟨ A𝟚-property→ f s b ⟩
                        ₁   ∎))

\end{code}

We now pause briefly to define some standard functions on tuples.

The head, or first element of a tuple:

\begin{code}

hd : {X : 𝓤 ̇ } {n : ℕ} → X ^ (succ n) → X
hd xs = xs 𝟎

\end{code}

Removing the head of a tuple, we get its tail:

\begin{code}

tl : {X : 𝓤 ̇ } {n : ℕ} → X ^ (succ n) → X ^ n
tl xs i = xs (suc i)

\end{code}

Prepending a new head to a tuple:

\begin{code}

cons : {X : 𝓤 ̇ } {n : ℕ} → X → X ^ n → X ^ (succ n)
cons x xs 𝟎       = x
cons x xs (suc i) = xs i

\end{code}

The fundamental properties of the above three functions:

\begin{code}

head-cons : {X : 𝓤 ̇ } {n : ℕ} (x : X) (xs : X ^ n)
          → hd (cons x xs) ＝ x
head-cons x xs = refl

tail-cons : {X : 𝓤 ̇ } {n : ℕ} (x : X) (xs : X ^ n)
          → tl (cons x xs) ＝ xs
tail-cons x xs = refl

cons-head-tail : {X : 𝓤 ̇ } {n : ℕ} (xs : X ^ (succ n))
               → cons (hd xs) (tl xs) ＝ xs
cons-head-tail xs = dfunext fe γ
 where
  γ : ∀ i → cons (hd xs) (tl xs) i ＝ xs i
  γ  𝟎      = refl
  γ (suc i) = refl

\end{code}

We are now ready to compute putative roots of boolean functions. We
will later adapt this argument to give a formula for the putative
root.

We define two functions A and ε by simulateous induction on n as
follows:

\begin{code}

A : {n : ℕ} → (𝟚 ^ n → 𝟚) → 𝟚
ε : {n : ℕ} → (𝟚 ^ n → 𝟚) → 𝟚 ^ n

A f = f (ε f)

ε {0}      f = λ (_ : Fin 0) → f !0
ε {succ n} f = cons b₀ (ε (f ∘ cons b₀))
  where
   b₀ : 𝟚
   b₀ = ε𝟚 (λ b → A (f ∘ cons b))

\end{code}

It is of course possible to first define ε, by induction on n, and
then A directly from ε as follows:

\begin{code}

ε' : {n : ℕ} → (𝟚 ^ n → 𝟚) → 𝟚 ^ n
ε' {0}      f = λ (_ : Fin 0) → f !0
ε' {succ n} f = cons b₀ (ε (f ∘ cons b₀))
  where
   b₀ : 𝟚
   b₀ = ε𝟚 (λ b → (f ∘ cons b) (ε' (f ∘ cons b)))

A' : {n : ℕ} → (𝟚 ^ n → 𝟚) → 𝟚
A' f = f (ε' f)

\end{code}

However, we want to highlight the role of A in our definition of ε.

We have that A f ＝ ₁ if and only if f x ＝ ₁ for all x in 𝟚 ^ n:

\begin{code}

A-property← : {n : ℕ} (f : 𝟚 ^ n → 𝟚)
            → ((x : 𝟚 ^ n) → f x ＝ ₁)
            → A f ＝ ₁
A-property← f α = α (ε f)

A-property→ : {n : ℕ}
              (f : 𝟚 ^ n → 𝟚)
            → A f ＝ ₁
            → (x : 𝟚 ^ n) → f x ＝ ₁
A-property→ {0} f r x = f x         ＝⟨ ap f !0-uniqueness ⟩
                        f (ε {0} f) ＝⟨ r ⟩
                        ₁           ∎
A-property→ {succ n} f r x = IV
 where
  IH : (b : 𝟚) → A (f ∘ cons b) ＝ ₁ → (β : 𝟚 ^ n) → f (cons b β) ＝ ₁
  IH b = A-property→ {n} (f ∘ cons b)

  b₀ : 𝟚
  b₀ = ε𝟚 (λ b → A (f ∘ cons b))

  I : A (f ∘ cons b₀) ＝ ₁ → (b : 𝟚) → A (f ∘ cons b) ＝ ₁
  I = A𝟚-property→ (λ b → A (f ∘ cons b))

  observation₀ : A f ＝ ₁
  observation₀ = r

  observation₁ : A f ＝ A (f ∘ cons b₀)
  observation₁ = refl

  II : (b : 𝟚) (β : 𝟚 ^ n) → f (cons b β) ＝ ₁
  II b = IH b (I r b)

  III : f (cons (hd x) (tl x)) ＝ ₁
  III = II (hd x) (tl x)

  IV : f x ＝ ₁
  IV = transport (λ - → f - ＝ ₁) (cons-head-tail x) III

σ : {n : ℕ} (f : 𝟚 ^ n → 𝟚)
  → Σ x₀ ꞉ 𝟚 ^ n , (f x₀ ＝ ₁ → (x : 𝟚 ^ n) → f x ＝ ₁)
σ f = ε f , A-property→ f

\end{code}

From this it follows that ε f computes a putative root of f.
That is, if f has a root, then ε f is a root of f:

\begin{code}

ε-gives-putative-root : {n : ℕ} (f : 𝟚 ^ n → 𝟚)
                      → (Σ x ꞉ 𝟚 ^ n , f x ＝ ₀)
                      → f (ε f) ＝ ₀
ε-gives-putative-root {n} f (x , r) =
 different-from-₁-equal-₀
  (λ (s : A f ＝ ₁) → zero-is-not-one
                       (₀   ＝⟨ r ⁻¹ ⟩
                        f x ＝⟨ A-property→ f s x ⟩
                        ₁   ∎))
\end{code}

The above computes a putative root. But what we want to do in this
file is to give a formula for computing putative roots.

So we now introduce a type of formulas, using only the symbol O and a
"variable" 𝕗, defined by induction as follows for any n fixed in
advance:

\begin{code}

data F (n : ℕ) : 𝓤₀ ̇ where
 O : F n
 𝕗 : F n ^ n → F n

\end{code}

Given any function f : 𝟚 ^ n → 𝟚, any formula ϕ in the type F n can be
evaluated to a boolean by replacing the symbol O by the boolean ₀ and
the variable 𝕗 by the function f, by induction on formulas, where we
use the letter ϕs to range over tuples of formulas:

\begin{code}

eval : {n : ℕ} → (𝟚 ^ n → 𝟚) → F n → 𝟚
eval f O      = ₀
eval f (𝕗 ϕs) = f (λ i → eval f (ϕs i))

\end{code}

Now, for any k, we think of the type F k as that of "formulas for
defining booleans", and we repeat the above definitions of the above
functions ε𝟚, A and ε, replacing booleans by formulas for booleans, in
order to compute them symbolically (indicated by the superscript s).

\begin{code}

ε𝟚ˢ : {k : ℕ} → (F k → F k) → F k
ε𝟚ˢ f = f O

Aˢ : {n k : ℕ} → (F k ^ n → F k) → F k
εˢ : {n k : ℕ} → (F k ^ n → F k) → F k ^ n

Aˢ f = f (εˢ f)

εˢ {0}      f = λ (_ : Fin 0) → f !0
εˢ {succ n} f = cons b₀ (εˢ (f ∘ cons b₀))
 where
  b₀ = ε𝟚ˢ (λ b → Aˢ (f ∘ cons b))

\end{code}

Notice now the definitions look exactly the same as those given above,
even if the types of the functions are diffent.

\begin{code}

putative-root-formula : {n : ℕ} → F n ^ n
putative-root-formula = εˢ 𝕗

\end{code}

The intended properties of these functions are, of course:

\begin{code}

Aˢ-desired-property = {n : ℕ} (f : 𝟚 ^ n → 𝟚)
                    → eval f (Aˢ 𝕗) ＝ A f

εˢ-desired-property = {n : ℕ} (f : 𝟚 ^ n → 𝟚)
                    → (i : Fin n) → eval f (εˢ 𝕗 i) ＝ ε f i
\end{code}

We will prove them here on another occasion. But we emphasize, for
now, that we need to prove something stronger, involving not only n
but also k.

In any case, notice that the desired property of for Aˢ follows
directly rom the desired property for εˢ:

\begin{code}

Aˢ-observation : εˢ-desired-property → Aˢ-desired-property
Aˢ-observation d {0} f      = ap f !0-uniqueness
Aˢ-observation d {succ n} f =
 eval f (Aˢ 𝕗)             ＝⟨ refl ⟩
 f (λ i → eval f (εˢ 𝕗 i)) ＝⟨ ap f (dfunext fe (d f)) ⟩
 f (ε f)                   ＝⟨ refl ⟩
 A f                       ∎

\end{code}

Before we prove the desired property for εˢ, we can give an example.

First notice that Agda can't display functions in a nice, visualizable
way. In order to do that, we consider a type of n-tuples of elements
of a type X, which is in bijection with the type X ^ n, and which can
be nicely displayed. This copy of X ^ n can be inductively defined as
follows:

\begin{code}

data tuple (X : 𝓤 ̇ ) : ℕ → 𝓤 ̇ where
 ⋆   : tuple X 0
 _,_ : {n : ℕ} → X → tuple X n → tuple X (succ n)

\end{code}

With this, we can define an equivalent copy F' of F as follows:

\begin{code}

data F' (n : ℕ) : 𝓤₀ ̇ where
 O : F' n
 𝕗 : tuple (F' n) n → F' n

tuplify : {n : ℕ} {X : 𝓤 ̇ } → X ^ n → tuple X n
tuplify {𝓤} {0}      f = ⋆
tuplify {𝓤} {succ n} f = f 𝟎 , tuplify (f ∘ suc)

translate : {n : ℕ} → F n → F' n
translate O      = O
translate (𝕗 ϕs) = 𝕗 (tuplify (λ i → translate (ϕs i)))

\end{code}

With this, we can visualize our formula for e.g. the putative root
when n = 2 as follows:

\begin{code}

example₂ : tuple (F' 2) 2
example₂ = tuplify (λ i → translate (putative-root-formula i))

example₂-explicitly : example₂ ＝
                      (𝕗 (O , (𝕗 (O , (O , ⋆)) , ⋆)) ,
                       𝕗 (𝕗 (O , (𝕗 (O , (O , ⋆)) , ⋆)) , (O , ⋆)) , ⋆)
example₂-explicitly = refl

\end{code}

This says that for any f : 𝟚 ^ 2 → 𝟚, our putative root is
(x₀ , x₁) where

  x₀ = 𝕗 (O , 𝕗 (O , O))
  x₁ = 𝕗 (𝕗 (O , 𝕗 (O , O)) , O)

TODO. Prove the above desired properties and use them to show that the
formula for putative roots indeed gives putative roots.

Appendix. Things that are not needed for the above discussion, but
that we may need for other purposes in the future.

\begin{code}

δΣ : {n : ℕ} (f : 𝟚 ^ n → 𝟚)
   → is-decidable (Σ x ꞉ 𝟚 ^ n , f x ＝ ₀)
δΣ {n} f = γ (f x) refl
 where
  x : 𝟚 ^ n
  x = ε f

  γ : (k : 𝟚) → f x ＝ k → is-decidable (Σ x ꞉ 𝟚 ^ n , f x ＝ ₀)
  γ ₀ r = inl (x  , r)
  γ ₁ r = inr (λ ((β , s) : Σ x ꞉ 𝟚 ^ n , f x ＝ ₀) → zero-is-not-one
                                                      (₀   ＝⟨ s ⁻¹ ⟩
                                                       f β ＝⟨ A-property→ f r β ⟩
                                                       ₁   ∎))

δΠ : {n : ℕ} (f : 𝟚 ^ n → 𝟚)
   → is-decidable (Π x ꞉ 𝟚 ^ n , f x ＝ ₁)
δΠ {n} f = γ (δΣ f)
 where
  γ : is-decidable (Σ x ꞉ 𝟚 ^ n , f x ＝ ₀) → is-decidable ((x : 𝟚 ^ n) → f x ＝ ₁)
  γ (inl (x , r)) = inr (λ ϕ → zero-is-not-one (r ⁻¹ ∙ ϕ x))
  γ (inr ν)       = inl (λ x → different-from-₀-equal-₁ (λ r → ν (x , r)))

F-rec : {n : ℕ} {X : 𝓤 ̇ } → X → (X ^ n → X) → F n → X
F-rec {𝓤} {n} {X} x₀ p = h
 where
  h : F n → X
  h O     = x₀
  h (𝕗 t) = p (λ i → h (t i))

F-ind : {n : ℕ} {X : F n → 𝓤 ̇ }
      → X O
      → ((ts : F n ^ n) → ((i : Fin n) → X (ts i)) → X (𝕗 ts))
      → (t : F n) → X t
F-ind {𝓤} {n} {X} x₀ p = h
 where
  h : (t : F n) → X t
  h O      = x₀
  h (𝕗 ts) = p ts (λ i → h (ts i))

\end{code}
