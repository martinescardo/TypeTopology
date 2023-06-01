Martin Escardo, 21th April 2023
Based on Section 8.1 of the paper https://doi.org/10.2168/LMCS-4(3:3)2008

Updated 25th May 2023 to (i) give an alternative construction of our
formula for a putative root, and (ii) prove its correctness.

We provide a formula for a putative root of any boolean function
f : 𝟚ⁿ → 𝟚, using only f and ₀, and show its correctness.

In more detail:

Let 𝟚 be the two-point set with elements ₀ and ₁, referred to as the
type of booleans.

Consider a given boolean function f : 𝟚ⁿ → 𝟚.

Definition. A *root* of f is some xs in 𝟚ⁿ such that f xs = ₀.

Definition. A *putative root* of f is any xs in 𝟚ⁿ such that if f has
some root, then xs is a root.

Example. If f doesn't have any root, then any xs in 𝟚ⁿ is putative root.

Example. If xs is a root, then xs is a putative root.

Theorem. For any n, there is a formula that mentions only f and ₀ such
that for any given function f : 𝟚ⁿ → 𝟚, the formula gives a putative
root of f.

We will need to be more precise regarding the formal details of the
statement of this theorem, where we will need to distinguish between
(abstract syntax for) formulas for putative roots and actual putative
roots, but, for the moment, the above imprecise formulation of the
theorem should be good enough.

Example. For n = 3, we have the putative root x := (x₀,x₁,x₂) where

  y  := f(0,0,f(0,0,0))
  x₀ := f(0,y,f(0,y,0))
  x₁ := f(x₀,0,f(x₀,0,0))
  x₂ := f(x₀,x₁,0)

The purpose of this Agda file is to construct such a formula for any
given n, and prove that it indeed gives a putative root.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --no-sized-types --no-guardedness --auto-inline #-}

module Various.RootsOfBooleanFunctions where

open import MLTT.Spartan hiding (_^_)
open import MLTT.Two-Properties
open import UF.Base

\end{code}

For any f : 𝟚 → 𝟚, we can check whether it is constantly ₁ by checking
whether f (f ₀) is ₁, which is easily proved by case analysis on the
value of f ₀:

\begin{code}

motivating-fact : (f : 𝟚 → 𝟚) → f (f ₀) ＝ ₁ → (b : 𝟚) → f b ＝ ₁
motivating-fact f = γ (f ₀) refl
 where
  γ : (b₀ : 𝟚) → f ₀ ＝ b₀ → f b₀ ＝ ₁ → (b : 𝟚) → f b ＝ ₁
  γ ₀ p q ₀ = q
  γ ₀ p q ₁ = 𝟘-elim
               (zero-is-not-one
                 (₀   ＝⟨ p ⁻¹ ⟩
                  f ₀ ＝⟨ q ⟩
                  ₁   ∎))
  γ ₁ p q ₀ = p
  γ ₁ p q ₁ = q

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

The functional ε𝟚 computes the putative root ε f for any f : 𝟚 → 𝟚:

\begin{code}

is-root : {X : 𝓤 ̇ } → X → (X → 𝟚) → 𝓤₀ ̇
is-root x₀ f = f x₀ ＝ ₀

has-root : {X : 𝓤 ̇ } → (X → 𝟚) → 𝓤 ̇
has-root {𝓤} {X} f = Σ x ꞉ X , is-root x f

is-putative-root : {X : 𝓤 ̇ } → X → (X → 𝟚) → 𝓤 ̇
is-putative-root x₀ f = has-root f → is-root x₀ f

ε𝟚-gives-putative-root : {n : ℕ} (f : 𝟚 → 𝟚)
                       → is-putative-root (ε𝟚 f) f
ε𝟚-gives-putative-root f (b , r) =
 different-from-₁-equal-₀
  (λ (p : A𝟚 f ＝ ₁) → zero-is-not-one
                       (₀   ＝⟨ r ⁻¹ ⟩
                        f b ＝⟨ A𝟚-property→ f p b ⟩
                        ₁   ∎))
\end{code}

We define the type X ^ n of n-tuples of elements of a type X by
induction as follows.

\begin{code}

data _^_ (X : 𝓤 ̇ ) : ℕ → 𝓤 ̇ where
 ⟨⟩  : X ^ 0
 _,_ : {n : ℕ} → X → X ^ n → X ^ (succ n)

\end{code}

(This is just another notation for the type of so-called vectors.)

We will often use the "prepend" function (x ,_), for any given x,
written "cons x", defined by cons x xs = (x , xs), or, equivalently:

\begin{code}

cons : {X : 𝓤 ̇ } {n : ℕ} → X → X ^ n → X ^ (succ n)
cons x = (x ,_)

\end{code}

We are now ready to compute putative roots of boolean functions. We
will later adapt this argument to give a *formula* for the putative
root.

We define two functions A and ε by simultateous induction on n as
follows:

\begin{code}

A : {n : ℕ} → (𝟚 ^ n → 𝟚) → 𝟚
ε : {n : ℕ} → (𝟚 ^ n → 𝟚) → 𝟚 ^ n

A f = f (ε f)

ε {0}      f = ⟨⟩
ε {succ n} f = cons b₀ (ε (f ∘ cons b₀) )
 where
  b₀ : 𝟚
  b₀ = ε𝟚 (b ↦ A (f ∘ cons b))

\end{code}

It is of course possible to first define ε, by induction on n, and
then A directly from ε as follows. If we also expand the definition of
ε𝟚, we get:

\begin{code}

private

 ε' : {n : ℕ} → (𝟚 ^ n → 𝟚) → 𝟚 ^ n
 ε' {0}      f = ⟨⟩
 ε' {succ n} f = cons b₀ (ε' (f ∘ cons b₀))
  where
   b₀ : 𝟚
   b₀ = (f ∘ cons ₀) (ε' (f ∘ cons ₀))

 A' : {n : ℕ} → (𝟚 ^ n → 𝟚) → 𝟚
 A' f = f (ε' f)

\end{code}

However, we want to highlight the role of A in our definition of ε.

We have that A f ＝ ₁ if and only if f xs ＝ ₁ for all xs in 𝟚 ^ n:

\begin{code}

A-property← : {n : ℕ} (f : 𝟚 ^ n → 𝟚)
            → ((xs : 𝟚 ^ n) → f xs ＝ ₁)
            → A f ＝ ₁
A-property← f α = α (ε f)

A-property→ : {n : ℕ}
              (f : 𝟚 ^ n → 𝟚)
            → A f ＝ ₁
            → (xs : 𝟚 ^ n) → f xs ＝ ₁
A-property→ {0}      f p ⟨⟩ = f ⟨⟩        ＝⟨ refl ⟩
                              f (ε {0} f) ＝⟨ p ⟩
                              ₁           ∎
A-property→ {succ n} f p (x , xs) = II
 where
  IH : (b : 𝟚) → A (f ∘ cons b) ＝ ₁ → (xs : 𝟚 ^ n) → f (cons b xs) ＝ ₁
  IH b = A-property→ {n} (f ∘ cons b)

  b₀ : 𝟚
  b₀ = ε𝟚 (b ↦ A (f ∘ cons b))

  I : A (f ∘ cons b₀) ＝ ₁ → (b : 𝟚) → A (f ∘ cons b) ＝ ₁
  I = A𝟚-property→ (b ↦ A (f ∘ cons b))

  II : f (x , xs) ＝ ₁
  II = IH x (I p x) xs

σ : {n : ℕ} (f : 𝟚 ^ n → 𝟚)
  → Σ x₀ ꞉ 𝟚 ^ n , (f x₀ ＝ ₁ → (x : 𝟚 ^ n) → f x ＝ ₁)
σ f = ε f , A-property→ f

\end{code}

From this it follows that ε f computes a putative root of f.

\begin{code}

ε-gives-putative-root : {n : ℕ}  (f : 𝟚 ^ n → 𝟚)
                      → is-putative-root (ε f) f
ε-gives-putative-root {n} f (x , p) =
 different-from-₁-equal-₀
  (λ (q : A f ＝ ₁) → zero-is-not-one
                       (₀   ＝⟨ p ⁻¹ ⟩
                        f x ＝⟨ A-property→ f q x ⟩
                        ₁   ∎))

\end{code}

Hence we can check whether f has a root by checking whether f (ε f) ＝ ₀.

\begin{code}

root-existence-criterion : {n : ℕ}  (f : 𝟚 ^ n → 𝟚)
                         → has-root f ⇔ is-root (ε f) f
root-existence-criterion {n} f = (I , II)
 where
  I : has-root f → f (ε f) ＝ ₀
  I = ε-gives-putative-root f

  II : f (ε f) ＝ ₀ → has-root f
  II p = ε f , p

\end{code}

The above computes a putative root, but what we want to do in this
file is to give a *formula* for computing putative roots using only ₀
and f, as discussed above. In a way, this is already achieved
above. Here are some examples:

\begin{code}

example₂ : (f : 𝟚 ^ 2 → 𝟚)
         → ε f ＝ (f (₀ , f (₀ , ₀ , ⟨⟩) , ⟨⟩) ,
                   f (f (₀ , f (₀ , ₀ , ⟨⟩) , ⟨⟩) , ₀ , ⟨⟩) ,
                   ⟨⟩)
example₂ f = refl

example₃ : (f : 𝟚 ^ 3 → 𝟚) →
 let
  y  = f (₀ , ₀ , f (₀ , ₀ , ₀ , ⟨⟩) , ⟨⟩)
  x₀ = f (₀ , y , f (₀ , y , ₀ , ⟨⟩) , ⟨⟩)
  x₁ = f (x₀ , ₀ , f (x₀ , ₀ , ₀ , ⟨⟩) , ⟨⟩)
  x₂ = f (x₀ , x₁ , ₀ , ⟨⟩)
 in
  ε f ＝ (x₀ , x₁ , x₂ , ⟨⟩)
example₃ f = refl

\end{code}

But we want to make this explicit. For that purpose, we introduce a
type E of symbolic expressions, or formulas, using only the symbol O
(standing for ₀) and the symbol 𝕗 (standing for any given function
f : 𝟚 ^ n → 𝟚), defined by induction as follows, with n as a fixed
parameter:

\begin{code}

data E (n : ℕ) : 𝓤₀ ̇ where
 O : E n
 𝕗 : E n ^ n → E n

\end{code}

Given a function f : 𝟚 ^ n → 𝟚, any expression e of type E n can be
evaluated to a boolean by replacing the symbol O by the boolean ₀ and
the symbol 𝕗 by the function f, by induction on formulas, where we use
the variable e to range over expressions, and the variable es to range
over tuples of expressions.

\begin{code}

module _ {n : ℕ} (f : 𝟚 ^ n → 𝟚) where

 eval  : E n → 𝟚
 evals : {k : ℕ} → E n ^ k → 𝟚 ^ k

 eval O      = ₀
 eval (𝕗 es) = f (evals es)

 evals ⟨⟩       = ⟨⟩
 evals (e , es) = eval e , evals es

\end{code}

We use the following auxilary constructions to define a formula for a
putative root of any n-ary boolean function:

\begin{code}

𝕔𝕠𝕟𝕤  : {n : ℕ}   → E (succ n) → E n     → E (succ n)
𝕔𝕠𝕟𝕤s : {n k : ℕ} → E (succ n) → E n ^ k → E (succ n) ^ k

𝕔𝕠𝕟𝕤 e₀ O      = O
𝕔𝕠𝕟𝕤 e₀ (𝕗 es) = (𝕗 ∘ cons e₀) (𝕔𝕠𝕟𝕤s e₀ es)

𝕔𝕠𝕟𝕤s e₀ ⟨⟩       = ⟨⟩
𝕔𝕠𝕟𝕤s e₀ (e , es) = 𝕔𝕠𝕟𝕤 e₀ e , 𝕔𝕠𝕟𝕤s e₀ es

\end{code}

Their intended behaviour is as follows:

\begin{code}

𝕔𝕠𝕟𝕤-behaviour : {n : ℕ}
                 (f : 𝟚 ^ succ n → 𝟚)
                 (e₀ : E (succ n))
                 (e  : E n)
               → eval f (𝕔𝕠𝕟𝕤 e₀ e) ＝ eval (f ∘ cons (eval f e₀)) e

𝕔𝕠𝕟𝕤s-behaviour : {n k : ℕ}
                  (f : 𝟚 ^ succ n → 𝟚)
                  (e₀ : E (succ n))
                  (es : E n ^ k)
                → evals f (𝕔𝕠𝕟𝕤s e₀ es) ＝ evals (f ∘ cons (eval f e₀)) es

𝕔𝕠𝕟𝕤-behaviour f e₀ O      = refl
𝕔𝕠𝕟𝕤-behaviour f e₀ (𝕗 es) = ap (f ∘ cons (eval f e₀)) (𝕔𝕠𝕟𝕤s-behaviour f e₀ es)

𝕔𝕠𝕟𝕤s-behaviour f e₀ ⟨⟩       = refl
𝕔𝕠𝕟𝕤s-behaviour f e₀ (e , es) = ap₂ _,_
                                   (𝕔𝕠𝕟𝕤-behaviour  f e₀ e )
                                   (𝕔𝕠𝕟𝕤s-behaviour f e₀ es)
\end{code}

With this, we can give a formula to compute ε:

\begin{code}

ε-formula : (n : ℕ) → E n ^ n
ε-formula 0        = ⟨⟩
ε-formula (succ n) = cons c₀ (𝕔𝕠𝕟𝕤s c₀ (ε-formula n))
 where
  c₀ : E (succ n)
  c₀ = (𝕗 ∘ cons O) (𝕔𝕠𝕟𝕤s O (ε-formula n))

\end{code}

Notice the similarity with the definition of ε, in particular with its
incarnation ε'.

Here is an example that illustrates this concretely:

\begin{code}

example₃-formula :
 let
  y  = 𝕗 (O , O , 𝕗 (O , O , O , ⟨⟩) , ⟨⟩)
  x₀ = 𝕗 (O , y , 𝕗 (O , y , O , ⟨⟩) , ⟨⟩)
  x₁ = 𝕗 (x₀ , O , 𝕗 (x₀ , O , O , ⟨⟩) , ⟨⟩)
  x₂ = 𝕗 (x₀ , x₁ , O , ⟨⟩)
 in
  ε-formula 3 ＝ (x₀ , x₁ , x₂ , ⟨⟩)
example₃-formula = refl

\end{code}

The desired property of the formula is that evaluating it with any
concrete f gives the putative root ε f of f:

\begin{code}

ε-formula-lemma : (n : ℕ) (f : 𝟚 ^ n → 𝟚)
                → evals f (ε-formula n) ＝ ε f
ε-formula-lemma 0        f = refl
ε-formula-lemma (succ n) f = γ
 where
  es : E n ^ n
  es = ε-formula n

  b₀ : 𝟚
  b₀ = (f ∘ cons ₀) (ε (f ∘ cons ₀))

  c₀ : E (succ n)
  c₀ = (𝕗 ∘ cons O) (𝕔𝕠𝕟𝕤s O es)

  IH : (b : 𝟚) → evals (f ∘ cons b) es ＝ ε (f ∘ cons b)
  IH b = ε-formula-lemma n (f ∘ cons b)

  c₀-property : eval f c₀ ＝ b₀
  c₀-property =
   eval f c₀                            ＝⟨ refl ⟩
   (f ∘ cons ₀) (evals f (𝕔𝕠𝕟𝕤s O es))  ＝⟨ I ⟩
   (f ∘ cons ₀) (evals (f ∘ cons ₀) es) ＝⟨ II ⟩
   (f ∘ cons ₀) (ε (f ∘ cons ₀))        ＝⟨ refl ⟩
   b₀                                   ∎
    where
     I  = ap (f ∘ cons ₀) (𝕔𝕠𝕟𝕤s-behaviour f O es)
     II = ap (f ∘ cons ₀) (IH ₀)

  γ : evals f (ε-formula (succ n)) ＝ ε f
  γ = evals f (ε-formula (succ n))               ＝⟨ refl ⟩
      cons (eval f c₀) (evals f (𝕔𝕠𝕟𝕤s c₀ es))   ＝⟨ I ⟩
      cons b₀ (evals f (𝕔𝕠𝕟𝕤s c₀ es))            ＝⟨ II ⟩
      cons b₀ (evals (f ∘ cons (eval f c₀)) es)  ＝⟨ III ⟩
      cons b₀ (evals (f ∘ cons b₀) es)           ＝⟨ IV ⟩
      cons b₀ (ε (f ∘ cons b₀))                  ＝⟨ refl ⟩
      ε f                                        ∎
       where
        I   = ap (λ - → cons - (evals f (𝕔𝕠𝕟𝕤s c₀ es))) c₀-property
        II  = ap (cons b₀) (𝕔𝕠𝕟𝕤s-behaviour f c₀ es)
        III = ap (λ - → cons b₀ (evals (f ∘ cons -) es)) c₀-property
        IV  = ap (cons b₀) (IH b₀)

\end{code}

From this, together with "ε-gives-putative-root" proved above, it
follows immediately that "ε-formula n" gives a formula for a putative
root of any n-ary boolean function:

\begin{code}

ε-formula-theorem : (n : ℕ) (f : 𝟚 ^ n → 𝟚)
                  → is-putative-root (evals f (ε-formula n)) f
ε-formula-theorem n f = γ
 where
  δ : is-putative-root (ε f) f
    → is-putative-root (evals f (ε-formula n)) f
  δ i ρ = f (evals f (ε-formula n)) ＝⟨ ap f (ε-formula-lemma n f) ⟩
          f (ε f)                   ＝⟨ i ρ ⟩
          ₀                         ∎

  γ : is-putative-root (evals f (ε-formula n)) f
  γ = δ (ε-gives-putative-root f)

\end{code}

Which has our desired theorem as a corollary, namely that, for every n,
there is a formula for a putative root of any n-ary boolean function:

\begin{code}

putative-root-formula-theorem :

 (n : ℕ) → Σ es ꞉ E n ^ n , ((f : 𝟚 ^ n → 𝟚) → is-putative-root (evals f es) f)

putative-root-formula-theorem n = ε-formula n ,
                                  ε-formula-theorem n

\end{code}

Our original definition of the formula for the putative root was the following:

\begin{code}

εᵉ : {n k : ℕ} → (E k ^ n → E k) → E k ^ n
εᵉ {0}      {k} f = ⟨⟩
εᵉ {succ n} {k} f = cons c₀ (εᵉ (f ∘ cons c₀))
 where
  c₀ : E k
  c₀ = (f ∘ cons O) (εᵉ (f ∘ cons O))

ε-formula' : (n : ℕ) → E n ^ n
ε-formula' n = εᵉ 𝕗

\end{code}

The advantage of this definition is that it is almost literally the
same as that of ε'.

The disadvantage is that it is difficult to find a suitable induction
hypothesis to prove the correctness of ε-formula'. We did find such a
proof, but it is long and messy, and we decided not to include it here
for that reason.

Challenges. (1) Find an elegant proof that the function ε-formula'
gives a formulate for putative roots. (2) Moreover, show that
ε-formula' = ε-formula.

It may be that it is easier to prove (2) and then deduce (1), rather
than prove (1) directly. We haven't tried that.
