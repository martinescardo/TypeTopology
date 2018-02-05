
    Ordinals in Gödel's system T and in Martin-Löf Type Theory
    ------------------------------------------------------------

    Martin Escardo, 2010, coded in Agda November 2011.

    This is based on work of Coquand, Setzer and Hancock, in particular:

    (i) Coquand, Hancock and Setzer (1997)
    http://www.cse.chalmers.se/~coquand/ordinal.ps

    (ii) Hancock (Russell'08 Proof Theory meets Type Theory, Swansea)
    http://www.cs.swan.ac.uk/~csetzer/russell08/slides/hancock.pdf

    An interesting and powerful idea is their use of "lenses", which
    allows to define rather large ordinals, in particular in the
    presence of dependent types and universes. Another idea is to use
    Church encodings of ordinals.

    Here I do something more modest, without lenses, but still with
    Church encodings. I explicitly define addition, multiplication and
    exponentiation of ordinals, and there may be a small contribution
    here.

    In the Goedel system T fragment of Agda, these arithmetic
    operations cannot be uniformly typed, but they still have neat
    definitions. In particular, because of the non-uniform typing, we
    can only dominate ordinals strictly below ε₀ - this is not a
    limitation of our approach, but rather of system T.

    Using dependent types (products in fact will be enough) and a
    universe, we can get a uniform typing of the arithmetic
    operations, and hence the ordinal ε₀ and much higher indeed. But I
    will content myself with defining ε₀, which is not definable in
    system T, as an illustration of what dependent types and universes
    add in terms of expressivity. But it is easy to get higher using
    what is defined here. If you want to get really high, then you
    should study lenses: http://personal.cis.strath.ac.uk/~ph/

    We proceed in three steps to define addition, multiplication and
    exponentiation, and hence ε₀ and much higher.

    (1): We essentially use Goedel's system T and work with a type 

            O X = X → (X → X) → ((ℕ → X) → X) → X 

         of Church encodings of ordinal trees, where X is a parameter,
         and define the basic arithmetic operations on ordinals with
         the non-uniform types

            add : O X → O X → O X
            mul : O X → O(O X) → O X
            exp : O(O X) → O(O X) → O X

         These types are the best one can do in system T. With this we
         can define ordinals abitrarily close to, and strictly below,
         the ordinal ε₀.

    (2): We use the first universe and dependent products to define

            O' X = Π(n : ℕ) → Oⁿ⁺¹ X 
  
         and hence the arithmetic operations with uniform types

            add', mul', exp' : O' X → O' X → O' X

         from add, mul, exp defined in step (1). With this we can now
         define ε₀, not only in O' X, but also in O X.

         So you can see the type O' X as an auxiliary construction to
         get more in O X.

    (3): We inductively define a (standard) W-type of ordinal trees
    (e.g. studied by Brouwer, by Howard in an extension of system T,
    and mentioned by Martin-Loef in some of his papers), and show how
    to define complex Brouwer ordinal trees *without* using
    (structural) recursion on ordinals trees, using step (2).

    All (primitive) recursions in the development of (1)-(3) are on
    the set ℕ. This is followed by exercises, now using recursion and
    induction on Brouwer ordinal trees.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} 

module OrdinalCodes where

open import SpartanMLTT
open import Naturals

\end{code}

Step (1). Church ordinal trees:

\begin{code}

O : U₀ ̇ → U₀ ̇
O X = X → (X → X) → ((ℕ → X) → X) → X

zer : {X : U₀ ̇} → O X
zer = λ z → λ s → λ l → z

suc : {X : U₀ ̇} → O X → O X
suc a = λ z → λ s → λ l → s(a z s l)

lim : {X : U₀ ̇} → (ℕ → O X) → O X
lim as = λ z → λ s → λ l → l(λ i → as i z s l)

O-rec : {X : U₀ ̇} → X → (X → X) → ((ℕ → X) → X) → (O X → X)
O-rec z s l a = a z s l

\end{code}

Notice that by uncurrying, flipping and currying the type of O-rec is
isomorphic to {X : U₀ ̇} → O X → O X, but the above form is more
convenient for recursive definitions.

In this first step, we have natural definitions but the types are not
uniform:

\begin{code}

add : {X : U₀ ̇} → O X → O X → O X
add a b = λ z → λ s → λ l → a (b z s l) s l 

mul : {X : U₀ ̇} → O X → O(O X) → O X
mul a = O-rec zer (λ r → add r a) lim

exp : {X : U₀ ̇} → O(O X) → O(O X) → O X
exp a = O-rec (suc zer) (λ r → mul r a) lim

\end{code}

Remark: if we had used O-rec to define add, it would instead have
the type {X : U₀ ̇} → O X → O(O X) → O X, and then mul would have
the type {X : U₀ ̇} → O(O X) → O(O X) → O X, with the same
definition, but the same definition of exp then cannot be typed
using iterations of O. In step (2) we will consider all finite
iterations of O to define a type O', and give a uniform type 
{X : U₀ ̇} → O' X → O' X → O' X to add, mul, and exp.

We will not use the following:

\begin{code}

down : {X : U₀ ̇} → O(O X) → O X
down = O-rec zer suc lim

\end{code}

There is a term up : {X : U₀ ̇} → O X → O(O X), but no such term has
the desired behaviour of being a (left or right) inverse of down. 

Before using the first universe, we can dominate any ordinal below ε₀.

The sequence of finite ordinals first:

\begin{code}

finite : {X : U₀ ̇} → ℕ → O X
finite = rec zer suc

\end{code}

Its limit:

\begin{code}

ω : {X : U₀ ̇} → O X
ω = lim finite

\end{code}

Now the iterated powers of ω, which can't be defined uniformly
without universes or W-types or impredicativity etc.

\begin{code}

ω₁ : {X : U₀ ̇} → O X
ω₁ = exp ω ω

ω₂ : {X : U₀ ̇} → O X
ω₂ = exp ω ω₁

ω₃ : {X : U₀ ̇} → O X
ω₃ = exp ω ω₂

\end{code}

And so on. Although the definitions look uniform, they are not. In
fact, the candidate for the recursion step doesn't have type 
O X → O X, but rather:

\begin{code}

step :  {X : U₀ ̇} → O(O X) → O X
step = exp ω

\end{code}

If you try to define

  ω-tower : {X : U₀ ̇} → ℕ → O X
  ω-tower = rec ω (exp ω) 

then Agda rightfully complains that this would need X = O X, which
is impossible.

Moreover, e.g. in the definition of ω₃ the use of ω has its type X
instantiated to O(O(O(O X))), if I counted properly. Thus, although we
always write ω in the definitions of ω₁, ω₂, ω₃, ..., if we are
strictly working in system T we need a different definition of ω in
each case (with the same raw term but with a different type).


Step (2). 

We now use the first universe to reach ε₀ and beyond.  We
build a type O' X of ordinals based on O X. It is the definition of
rec₁, used to construct O', that uses the first universe. So we
move from higher-type primitive recursion (system T) to even higher
primitive recursion using a universe.

\begin{code}

rec₁ : U₀ ̇ → (U₀ ̇ → U₀ ̇) → ℕ → U₀ ̇
rec₁ X F zero = X
rec₁ X F (succ n) = F(rec₁ X F n)

\end{code}

We define O' X = Π (n : ℕ) → Oⁿ⁺¹ X as follows in Agda notation:

\begin{code}

O' : U₀ ̇ → U₀ ̇
O' X = (n : ℕ) → O(rec₁ X O n)

zer' : {X : U₀ ̇} → O' X
zer' = λ n → zer

suc' : {X : U₀ ̇} → O' X → O' X
suc' a = λ n → suc(a n)

lim' : {X : U₀ ̇} → (ℕ → O' X) → O' X
lim' as = λ n → lim(λ i → as i n)

add' : {X : U₀ ̇} → O' X → O' X → O' X
add' a b = λ n → add (a n) (b n) 

mul' : {X : U₀ ̇} → O' X → O' X → O' X
mul' a b = λ n → mul (a n) (b(succ n))

exp' : {X : U₀ ̇} → O' X → O' X → O' X
exp' a b = λ n → exp (a(succ n)) (b(succ n))

ω' : {X : U₀ ̇} → O' X
ω' = λ n → ω

ω-tower' : {X : U₀ ̇} → ℕ → O' X
ω-tower' = rec ω' (exp' ω') 

\end{code}

The ordinal ε₀ can now be defined in O' X (and hence in O X - see
below).

\begin{code}

ε₀' : {X : U₀ ̇} → O' X
ε₀' = lim' ω-tower'

\end{code}

Because we now have addition, multiplication, exponentiation and
limits in a uniform way, we can of course get much higher than ε₀.
For example, ε₁, ε₂, ... can be defined uniformly and hence we can
define εω. Then proceeding in the same way we can get εα for α =
ε₀, and much higher indeed.


Now, using this last step (2), we can project to step (1) and
define ε₀ as an element of O X using the following coersion:

\begin{code}

O'↦O : {X : U₀ ̇} → O' X → O X
O'↦O a = a zero

ε₀ : {X : U₀ ̇} → O X
ε₀ = O'↦O ε₀'

\end{code}

Notice that the following doesn't type check:

  O↦O' : {X : U₀ ̇} → O X → O' X
  O↦O' a = λ n → a

But it does type check for some particular a, such as ω in the
above definition of ω'.


Step (3). Brouwer's ordinal trees. 

I will use the letters u,v to range over B, and us,vs to range over
forests, that is, sequences ℕ → B.

\begin{code}

data B : U₀ ̇ where
 Z : B
 S : B → B
 L : (ℕ → B) → B

\end{code}

Firstly we can go from O X to B when X=B:

\begin{code}

O↦B : O B → B
O↦B u = u Z S L

\end{code}

We can now define a very tall ordinal tree without recursion on B:

\begin{code}

B-ε₀ : B
B-ε₀ = O↦B ε₀

\end{code}

Step (4): But the above is not the end of the story. This step, not
mentioned above, is started but not completed. We leave the
completion as an exercise at the time of writing.

We can define the tree B-ε₀ by recursion on B and we should show,
in Agda, that this produces the same result as the above
recursion-free definition.

\begin{code}
B-rec : {X : U₀ ̇} → X → (X → X) → ((ℕ → X) → X) → B → X
B-rec {X} z s l = h
 where 
  h : B → X
  h Z = z
  h(S u) = s(h u)
  h(L us) = l(λ i → h(us i))
\end{code}

By suitable uncurrying, flipping and currying, the type of B-rec is
isomorphic to {X : U₀ ̇} → B → O X, but the above form is more
convenient for recursive definitions:

\begin{code}

B↦O : {X : U₀ ̇} → B → O X
B↦O u s z l = B-rec s z l u

\end{code}

Ordinal tree arithmetic:

\begin{code}

B-add : B → B → B
B-add u = B-rec u S L

B-mul : B → B → B
B-mul u = B-rec Z (λ r → B-add r u) L

B-exp : B → B → B
B-exp u = B-rec (S Z) (λ r → B-mul r u) L

B-finite : ℕ → B
B-finite = rec Z S

B-ω : B
B-ω = L B-finite

B-ω-tower : ℕ → B
B-ω-tower = rec B-ω (B-exp B-ω) 

B-ε₀-alternative : B
B-ε₀-alternative = L B-ω-tower

\end{code}

We are almost ready to formulate the exercise. We need to define
extensional equality on B.

\begin{code}

data _≣_ : B → B → U₀ ̇ where
 ≣-Z : Z ≣ Z
 ≣-S : (u v : B) → u ≣ v → S u ≣ S v
 ≣-L : (us vs : ℕ → B) → ((i : ℕ) → us i ≣ vs i) → L us ≣ L vs

\end{code}

Exercises: Construct elements of the following Exercise* types:

\begin{code}

Exercise₀ = B-ε₀ ≣ B-ε₀-alternative

\end{code}

Here is a sketch of how this can be approached:

\begin{code}

Exercise₁ = (u v : B) → B-add u v ≣ O↦B(add (B↦O u) (B↦O v))
Exercise₂ = (u v : B) → B-mul u v ≣ O↦B(mul (B↦O u) (B↦O v))
Exercise₃ = (u v : B) → B-exp u v ≣ O↦B(exp (B↦O u) (B↦O v))

\end{code}

We need more coersions:

\begin{code}

B↦O' : {X : U₀ ̇} → B → O' X
B↦O' u = λ n → B↦O u

O'↦B : O' B → B
O'↦B a =  O↦B(O'↦O a)

Exercise₁' = (u v : B) → B-add u v ≣ O'↦B(add' (B↦O' u) (B↦O' v))
Exercise₂' = (u v : B) → B-mul u v ≣ O'↦B(mul' (B↦O' u) (B↦O' v))
Exercise₃' = (u v : B) → B-exp u v ≣ O'↦B(exp' (B↦O' u) (B↦O' v))

\end{code}

And, to solve the above exercises, you will need induction on B
(which amounts to "primitive recursion" on B, rather than simple
recursion or iteration B-rec on B):

\begin{code}

B-induction : {A : B → U₀ ̇} → 
   A Z → 
  ((u : B) → A u → A(S u)) → 
  ((us : ℕ → B) → ((i : ℕ) → A(us i)) → A(L us)) →
-----------------------------------------------------------
  ((u : B) → A u)

B-induction {A} z s l = h
 where 
  h : (u : B) → A u
  h Z = z
  h(S u) = s u (h u)
  h(L us) = l us (λ i → h(us i))

\end{code}
