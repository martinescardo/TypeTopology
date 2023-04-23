Martin Escardo, 21th April 2023

Based on Section 8.1 of the paper https://doi.org/10.2168/LMCS-4(3:3)2008

Let 𝟚 be the two-point set with elements 0 and 1.

Consider a given boolean function f: 𝟚ⁿ → 𝟚.

Definition. A *root* of f is some x in 𝟚ⁿ such that f x = 0.

Definition. A *putative root* of f is any x in 𝟚ⁿ such that if f has
some root, then x is a root.

Example. If f doesn't have any root, then any x in 𝟚ⁿ is putative root.

Example. If x is a root, then x is a putative root.

Theorem. For any n, there is a formula that mentions only the variable
𝕗 and the constant 0 such that for any given function f: 𝟚ⁿ → 𝟚, the
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
be obvious to Agda practioners, but not necessarily for everybody.
Agda is a computer language based on Martin-Löf Type Theory.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --no-sized-types --no-guardedness --auto-inline #-}

module Various.RootsOfBooleanFunctions where

open import MLTT.Spartan hiding (_^_)
open import MLTT.Athenian
open import MLTT.Two-Properties

\end{code}

For any f : 𝟚 → 𝟚, we can check whether it is constantly 1 by checking
whether f (f 0) is 1, which is easily proved by case analysis on the
value of f 0:

\begin{code}

motivating-fact : (f : 𝟚 → 𝟚) → f (f ₀) ＝ ₁ → (b : 𝟚) → f b ＝ ₁
motivating-fact f = γ (f ₀) refl
 where
  γ : (b₀ : 𝟚) → f ₀ ＝ b₀ → f b₀ ＝ ₁ → (b : 𝟚) → f b ＝ ₁
  γ ₀ s r ₀ = r
  γ ₀ s r ₁ = 𝟘-elim
               (zero-is-not-one
                 (₀   ＝⟨ s ⁻¹ ⟩
                  f ₀ ＝⟨ r ⟩
                  ₁   ∎))
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

The functional ε𝟚 computes the putative root ε f for any f: 𝟚 → 𝟚:

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

We define the type X ^ n of n-tuples of elements of a type X by
induction as follows.

\begin{code}

data _^_ (X : 𝓤 ̇ ) : ℕ → 𝓤 ̇ where
 ⋆   : X ^ 0
 _,_ : {n : ℕ} → X → X ^ n → X ^ (succ n)

prepend : {X : 𝓤 ̇ } {n : ℕ} → X → X ^ n → X ^ (succ n)
prepend x = (xs ↦ (x , xs))

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

ε {0}      f = ⋆
ε {succ n} f = prepend b₀ (ε (f ∘ prepend b₀))
  where
   b₀ : 𝟚
   b₀ = ε𝟚 (b ↦ A (f ∘ prepend b))

\end{code}

It is of course possible to first define ε, by induction on n, and
then A directly from ε as follows:

\begin{code}

private

 ε' : {n : ℕ} → (𝟚 ^ n → 𝟚) → 𝟚 ^ n
 ε' {0}      f = ⋆
 ε' {succ n} f = prepend b₀ (ε (f ∘ prepend b₀))
   where
    b₀ : 𝟚
    b₀ = ε𝟚 (b ↦ (f ∘ prepend b) (ε' (f ∘ prepend b)))

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
A-property→ {0}      f r ⋆ = f ⋆         ＝⟨ refl ⟩
                             f (ε {0} f) ＝⟨ r ⟩
                             ₁           ∎
A-property→ {succ n} f r ( x , xs) = II
 where
  IH : (b : 𝟚) → A (f ∘ prepend b) ＝ ₁ → (xs : 𝟚 ^ n) → f (prepend b xs) ＝ ₁
  IH b = A-property→ {n} (f ∘ prepend b)

  b₀ : 𝟚
  b₀ = ε𝟚 (b ↦ A (f ∘ prepend b))

  I : A (f ∘ prepend b₀) ＝ ₁ → (b : 𝟚) → A (f ∘ prepend b) ＝ ₁
  I = A𝟚-property→ (b ↦ A (f ∘ prepend b))

  II : f (x , xs) ＝ ₁
  II = IH x (I r x) xs

σ : {n : ℕ} (f : 𝟚 ^ n → 𝟚)
  → Σ x₀ ꞉ 𝟚 ^ n , (f x₀ ＝ ₁ → (x : 𝟚 ^ n) → f x ＝ ₁)
σ f = ε f , A-property→ f

\end{code}

From this it follows that ε f computes a putative root of f.
That is, if f has a root, then ε f is a root of f:

\begin{code}

ε-gives-putative-root : {n : ℕ}  (f : 𝟚 ^ n → 𝟚)
                      → (Σ x ꞉ 𝟚 ^ n , f x ＝ ₀)
                      → f (ε f) ＝ ₀
ε-gives-putative-root {n} f (x , p) =
 different-from-₁-equal-₀
  (λ (q : A f ＝ ₁) → zero-is-not-one
                       (₀   ＝⟨ p ⁻¹ ⟩
                        f x ＝⟨ A-property→ f q x ⟩
                        ₁   ∎))
\end{code}

The above computes a putative root. But what we want to do in this
file is to give a formula for computing putative roots using only 0
and f, as discussed above.

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

module _ {n : ℕ} (f : 𝟚 ^ n → 𝟚) where

 eval       : F n → 𝟚
 eval-tuple : {k : ℕ} → F n ^ k → 𝟚 ^ k

 eval O     = ₀
 eval (𝕗 ϕ) = f (eval-tuple ϕ)

 eval-tuple ⋆        = ⋆
 eval-tuple (ϕ , ϕs) = eval ϕ , eval-tuple ϕs

\end{code}

Now, for any n, we think of the type F n as that of "formulas for
defining booleans", and we repeat the above definitions of the above
functions ε𝟚, A and ε, replacing booleans by formulas for booleans, in
order to compute them symbolically (indicated by the superscript s).

\begin{code}

ε𝟚ˢ : {n : ℕ} → (F n → F n) → F n
ε𝟚ˢ f = f O

Aˢ : {k n : ℕ} → (F n ^ k → F n) → F n
εˢ : {k n : ℕ} → (F n ^ k → F n) → F n ^ k

Aˢ f = f (εˢ f)

εˢ {0}      {n} f = ⋆
εˢ {succ k} {n} f = prepend b₀ (εˢ (f ∘ prepend b₀))
 where
  b₀ : F n
  b₀ = ε𝟚ˢ (b ↦ Aˢ (f ∘ prepend b))

\end{code}

Notice how the definitions look exactly the same as those given above,
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
                    → eval-tuple f (εˢ 𝕗) ＝ ε f
\end{code}

Before we prove these desired properties, we can give some
examples.

\begin{code}

putative-root-formula₂-works : (f : 𝟚 ^ 2 → 𝟚)
                             → (Σ x ꞉ 𝟚 ^ 2 , f x ＝ ₀)
                             → f (eval-tuple f putative-root-formula) ＝ ₀
putative-root-formula₂-works = ε-gives-putative-root

putative-root-formula₂-explicitly :

  putative-root-formula {2}
  ＝ (𝕗 (O , 𝕗 (O , O , ⋆) , ⋆) , 𝕗 (𝕗 (O , 𝕗 (O , O , ⋆) , ⋆) , O , ⋆) , ⋆)

putative-root-formula₂-explicitly = refl

putative-root-formula₃-works : (f : 𝟚 ^ 3 → 𝟚)
                             → (Σ x ꞉ 𝟚 ^ 3 , f x ＝ ₀)
                             → f (eval-tuple f putative-root-formula) ＝ ₀
putative-root-formula₃-works = ε-gives-putative-root

putative-root-formula₃-explicitly :
 let
  y  = 𝕗 (O , O , 𝕗 (O , O , O , ⋆) , ⋆)
  x₀ = 𝕗 (O , y , 𝕗 (O , y , O , ⋆) , ⋆)
  x₁ = 𝕗 (x₀ , O , 𝕗 (x₀ , O , O , ⋆) , ⋆)
  x₂ = 𝕗 (x₀ , x₁ , O , ⋆)
 in
  putative-root-formula {3} ＝ (x₀ , x₁ , x₂ , ⋆)
putative-root-formula₃-explicitly = refl

\end{code}

TODO. Prove the above desired properties and use them to show that the
formula for putative roots indeed gives putative roots.

In any case, notice that the desired property of Aˢ follows
directly from the desired property for εˢ:

\begin{code}

Aˢ-observation : εˢ-desired-property → Aˢ-desired-property
Aˢ-observation d {0} f      = refl
Aˢ-observation d {succ n} f =
 eval f (Aˢ 𝕗)           ＝⟨ refl ⟩
 f (eval-tuple f (εˢ 𝕗)) ＝⟨ ap f (d f) ⟩
 f (ε f)                 ＝⟨ refl ⟩
 A f                     ∎

\end{code}


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
  γ ₀ p = inl (x  , p)
  γ ₁ p = inr (λ ((x , q) : Σ x ꞉ 𝟚 ^ n , f x ＝ ₀)
                 → zero-is-not-one
                    (₀   ＝⟨ q ⁻¹ ⟩
                     f x ＝⟨ A-property→ f p x ⟩
                     ₁   ∎))

δΠ : {n : ℕ} (f : 𝟚 ^ n → 𝟚)
   → is-decidable (Π x ꞉ 𝟚 ^ n , f x ＝ ₁)
δΠ {n} f = γ (δΣ f)
 where
  γ : is-decidable (Σ x ꞉ 𝟚 ^ n , f x ＝ ₀)
    → is-decidable ((x : 𝟚 ^ n) → f x ＝ ₁)
  γ (inl (x , p)) = inr (λ ϕ → zero-is-not-one (p ⁻¹ ∙ ϕ x))
  γ (inr ν)       = inl (λ x → different-from-₀-equal-₁ (λ p → ν (x , p)))

\end{code}
