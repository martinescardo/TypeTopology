Arithmetic via equivalence
--------------------------

Martín Hötzel Escardó

Originally 10 July 2014, modified 10 Oct 2017, 22 March 2018, 25 Nov 2019.

This is a literate proof in univalent mathematics, in Agda
notation. Although the concepts of univalent mathematics are used, the
univalence axiom is not needed.

We have that 3+3+3+3+3 = 5+5+5, or 5×3 = 3×5, and more generally

  m×n = n×m.

This can of course be proved by induction. A more appealing pictorial
proof is

  ooo
  ooo         ooooo
  ooo    =    ooooo
  ooo         ooooo
  ooo

where "o" is a pebble. We just rotate the grid of pebbles, or swap
the coordinates, and doing this doesn't change the number of pebbles.

How can this proof be formally rendered, as faithfully as possible to
the intuition?

We first define an interpretation function Fin : ℕ → 𝓤₀ of numbers as
sets (in the universe 𝓤₀) by

 (1) Fin   0  = 𝟘,          where 𝟘 is the empty set,
 (2) Fin(n+1) = Fin n + 𝟙,  where 𝟙 is the singleton set,

Then Fin is a semiring homomorphism:

 (3) Fin(m + n) ≃ Fin m + Fin n, where "+" in the rhs is disjoint union,
 (4) Fin 1 ≃ 𝟙,
 (5) Fin(m × n) ≃ Fin m × Fin n, where "×" in the rhs is cartesian product,

It is also left-cancellable:

 (6) Fin m ≃ Fin n → m = n.

Two boxes with the same number of pebbles are counted by same number.

But instead of proving (3)-(5) after defining addition and
multiplication, we prove that

 (3') For every m,n:ℕ there is k:ℕ with Fin k ≃ Fin m + Fin n.
 (5') For every m,n:ℕ there is k:ℕ with Fin k ≃ Fin m × Fin n.

We then define addition and multiplication on ℕ from (3') and (5'),
from which (3) and (5) follow tautologically.

This relies on type arithmetic. To prove (3'), we use the trivial
bijections, or *equivalences* in the terminology of univalent
mathematics,

 X ≃ X + 𝟘,
 (X + Y) + 𝟙 ≃ X + (Y + 𝟙),

mimicking the definition of addition on ℕ in Peano arithmetic (but
with the equations written backwards).

To prove (4), we use the equivalence

 𝟘 + 𝟙 ≃ 𝟙

To prove (5'), we use the equivalences

 𝟘 ≃ X × 𝟘,
 X × Y + X ≃ X × (Y + 𝟙),

mimicking the definition of multiplication on ℕ in Peano arithmetic
(again backwards).

To prove the cancellation property (6), we use the cancellation
property

 X + 𝟙 ≃ Y + 𝟙 → X ≃ Y,

mimicking the cancellation property of the successor function on ℕ.
(This is the only combinatorial argument here.)

Now, relying on the equivalence

 X × Y ≃ Y × X,

which corresponds to the rotation of the grid of pebbles, we can prove
m × n = n × m as follows:

 Fin(m × n) ≃ Fin m × Fin n   by (5)
            ≃ Fin n × Fin m   by  X × Y ≃ Y × X,
            ≃ Fin(n × m)      by (5),

and so

 m × n ≃ n × m                by (6).

Similarly we can prove, of course,

 m + n ≃ n + m

using (3) and the equivalence

 X + Y ≃ Y + X.

Among all these constructions, we use induction on ℕ only in

  * the definition (1-2) of the function Fin : ℕ → 𝓤₀,

  * the existence (3')-(5') of addition and multiplication, and

  * the left-cancellability (6) of Fin.

With this, induction is not needed to prove that addition and
multiplication are commutative.

Side-remark, to be explored in a future version. From the equivalence

 (5) Fin(m × n) ≃ Fin m × Fin n

we get two maps

     f : Fin(m × n) → Fin m,
     g : Fin(m × n) → Fin n,

which we didn't define explicitly or combinatorially.

21st March 2018 remark: After doing this, I found this article by Tim
Gowers:

    Why is multiplication commutative?
    https://www.dpmms.cam.ac.uk/~wtg10/commutative.html

which says very much the same as above (implemented below in univalent
foundations in Agda notation).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT hiding (_^_)

module ArithmeticViaEquivalence where

open import UF-Subsingletons
open import UF-Equiv
open import UF-EquivalenceExamples
open import Fin
open import Fin-Properties

\end{code}

The 1st definition by induction is that of the function Fin defined in
the module Fin imported above, namely

  Fin   0  = 𝟘,
  Fin(n+1) = Fin n + 𝟙.

From a natural number n, get a finite set Fin n with n elements. This
can be considered as an interpretation function, which defines the
meaning of numbers as types.

2nd definition by induction. Existence of addition:

\begin{code}

+construction : (m n : ℕ) → Σ k ꞉ ℕ , Fin k ≃ Fin m + Fin n
+construction m zero = m , 𝟘-rneutral
+construction m (succ n) = g
  where
    IH : Σ k ꞉ ℕ , Fin k ≃ Fin m + Fin n
    IH = +construction m n
    k : ℕ
    k = pr₁ IH
    φ : Fin k ≃ Fin m + Fin n
    φ = pr₂ IH

    φ' =  Fin k + 𝟙           ≃⟨ Ap+ 𝟙 φ ⟩
         (Fin m + Fin n) + 𝟙  ≃⟨ +assoc ⟩
         (Fin m + Fin n + 𝟙)  ■

    g : Σ k' ꞉ ℕ , Fin k' ≃ Fin m + Fin (succ n)
    g = succ k , φ'

\end{code}

The construction gives an addition function by projection:

\begin{code}

_+'_ : ℕ → ℕ → ℕ
m +' n = pr₁(+construction m n)

infixl 20 _+'_

\end{code}

The construction also shows that its satisfies the usual
characterizing equations from Peano arithmetic:

\begin{code}

+base : {m : ℕ} → m +' zero ≡ m
+base = refl

+step : {m n : ℕ} → m +' (succ n) ≡ succ(m +' n)
+step = refl

\end{code}

Tautologically, we get that Fin : ℕ → 𝓤₀ is an
addition-homomorphism:

\begin{code}

Fin+homo : (m n : ℕ) → Fin(m +' n) ≃ Fin m + Fin n
Fin+homo m n = pr₂(+construction m n)

\end{code}

The 3rd and last use of induction is for the left-cancellability of
Fin : ℕ → 𝓤₀, which is in the module Fin.

With this, no further induction is needed to prove commutativity of
addition:

\begin{code}

+'-comm : (m n : ℕ) → m +' n ≡ n +' m
+'-comm m n = Fin-lc (m +' n) (n +' m)
 (Fin (m +' n)   ≃⟨ Fin+homo m n ⟩
  Fin m + Fin n  ≃⟨ +comm ⟩
  Fin n + Fin m  ≃⟨ ≃-sym (Fin+homo n m) ⟩
  Fin (n +' m)   ■)

\end{code}

Exercise. Associativity without induction.

We now repeat this story for multiplication:

\begin{code}

×construction : (m n : ℕ) → Σ k ꞉ ℕ , Fin k ≃ Fin m × Fin n
×construction m zero = zero , ×𝟘
×construction m (succ n) = g
  where
    IH : Σ k ꞉ ℕ , Fin k ≃ Fin m × Fin n
    IH = ×construction m n
    k : ℕ
    k = pr₁ IH
    φ : Fin k ≃ Fin m × Fin n
    φ = pr₂ IH

    φ' = Fin (k +' m)          ≃⟨ Fin+homo k m ⟩
         Fin k + Fin m         ≃⟨ Ap+ (Fin m) φ ⟩
         Fin m × Fin n + Fin m ≃⟨ 𝟙distr ⟩
         Fin m × (Fin n + 𝟙)   ■

    g : Σ k' ꞉ ℕ , Fin k' ≃ Fin m × Fin (succ n)
    g = (k +' m) , φ'

_×'_ : ℕ → ℕ → ℕ
m ×' n = pr₁(×construction m n)

infixl 22 _×'_

×base : {m : ℕ} → m ×' zero ≡ zero
×base = refl

×step : {m n : ℕ} → m ×' (succ n) ≡ m ×' n +' m
×step = refl

Fin×homo : (m n : ℕ) → Fin(m ×' n) ≃ Fin m × Fin n
Fin×homo m n = pr₂(×construction m n)

×'-comm : (m n : ℕ) → m ×' n ≡ n ×' m
×'-comm m n = Fin-lc (m ×' n) (n ×' m)
 (Fin (m ×' n)   ≃⟨ Fin×homo m n ⟩
  Fin m × Fin n  ≃⟨ ×comm ⟩
  Fin n × Fin m  ≃⟨ ≃-sym (Fin×homo n m) ⟩
  Fin (n ×' m)   ■)

\end{code}

Exercise. Associativity without induction.

Added 30th August 2018: Exponentiation. Requires one more induction
and function extensionality.

\begin{code}

open import UF-FunExt

module exponentiation-and-factorial (fe : FunExt) where

 fe₀ : funext 𝓤₀ 𝓤₀
 fe₀ = fe 𝓤₀ 𝓤₀

 →construction : (m n : ℕ) → Σ k ꞉ ℕ , Fin k ≃ (Fin m → Fin n)
 →construction zero n = succ zero ,
                        (𝟘 + 𝟙        ≃⟨ 𝟘-lneutral ⟩
                         𝟙            ≃⟨ 𝟘→ fe₀ ⟩
                        (𝟘 → Fin n)   ■)
 →construction (succ m) n = g
  where
   IH : Σ k ꞉ ℕ , Fin k ≃ (Fin m → Fin n)
   IH = →construction m n
   k : ℕ
   k = pr₁ IH
   φ : Fin k ≃ (Fin m → Fin n)
   φ = pr₂ IH

   φ' = Fin (k ×' n)                   ≃⟨ Fin×homo k n ⟩
        Fin k × Fin n                  ≃⟨ ×-cong φ (𝟙→ fe₀) ⟩
       (Fin m → Fin n) × (𝟙 → Fin n)   ≃⟨ ≃-sym (+→ fe₀) ⟩
       (Fin m + 𝟙 → Fin n)             ■

   g : Σ k' ꞉ ℕ , Fin k' ≃ (Fin (succ m) → Fin n)
   g = k ×' n , φ'

 _^_ : ℕ → ℕ → ℕ
 n ^ m = pr₁(→construction m n)

 infixl 23 _^_

 ^base : {n : ℕ} → n ^ zero ≡ succ zero
 ^base = refl

 ^step : {m n : ℕ} → n ^ (succ m) ≡ (n ^ m) ×' n
 ^step = refl

 Fin^homo : (m n : ℕ) → Fin(n ^ m) ≃ (Fin m → Fin n)
 Fin^homo m n = pr₂(→construction m n)

\end{code}

 Then, without the need for induction, we get the exponential laws:

\begin{code}

 ^+homo : (k m n : ℕ) → k ^ (m +' n) ≡ (k ^ m) ×' (k ^ n)
 ^+homo k m n = Fin-lc (k ^ (m +' n)) (k ^ m ×' k ^ n)
  (Fin (k ^ (m +' n))                ≃⟨ Fin^homo (m +' n) k ⟩
  (Fin (m +' n) → Fin k)             ≃⟨ →cong fe₀ fe₀ (Fin+homo m n) (≃-refl (Fin k)) ⟩
  (Fin m + Fin n → Fin k)            ≃⟨ +→ fe₀  ⟩
  (Fin m → Fin k) × (Fin n → Fin k)  ≃⟨ ×-cong (≃-sym (Fin^homo m k)) (≃-sym (Fin^homo n k)) ⟩
   Fin (k ^ m) × Fin (k ^ n)         ≃⟨ ≃-sym (Fin×homo (k ^ m) (k ^ n)) ⟩
   Fin (k ^ m ×' k ^ n)              ■)

 iterated^ : (k m n : ℕ) → k ^ (m ×' n) ≡ (k ^ n) ^ m
 iterated^ k m n = Fin-lc (k ^ (m ×' n)) (k ^ n ^ m)
    (Fin (k ^ (m ×' n))        ≃⟨ Fin^homo (m ×' n) k ⟩
    (Fin (m ×' n) → Fin k)     ≃⟨ →cong fe₀ fe₀ (Fin×homo m n) (≃-refl (Fin k)) ⟩
    (Fin m × Fin n → Fin k)    ≃⟨ curry-uncurry fe ⟩
    (Fin m → (Fin n → Fin k))  ≃⟨ →cong fe₀ fe₀ (≃-refl (Fin m)) (≃-sym (Fin^homo n k)) ⟩
    (Fin m → Fin (k ^ n))      ≃⟨ ≃-sym (Fin^homo m (k ^ n)) ⟩
     Fin (k ^ n ^ m)           ■)

\end{code}

Added 25t November 2019: Numerical factorial from the type theoretical
factorial, which also uses function extensionality (which is not
actually necessary - see the comments in the module UF-Factorial).

\begin{code}

 open import UF-Factorial fe public

 !construction : (n : ℕ) → Σ k ꞉ ℕ , Fin k ≃ Aut (Fin n)
 !construction zero = 1 ,
                      (Fin 1          ≃⟨ ≃-refl (Fin 1) ⟩
                       𝟘 + 𝟙          ≃⟨ 𝟘-lneutral ⟩
                       𝟙              ≃⟨ factorial-base ⟩
                       Aut (Fin zero) ■)
 !construction (succ n) = g
  where
   IH : Σ k ꞉ ℕ , Fin k ≃ Aut(Fin n)
   IH = !construction n
   k : ℕ
   k = pr₁ IH
   φ : Fin k ≃ Aut(Fin n)
   φ = pr₂ IH

   φ' = Fin (succ n ×' k)         ≃⟨ Fin×homo (succ n) k ⟩
        Fin (succ n) × Fin k      ≃⟨ ×-cong (≃-refl (Fin (succ n))) φ ⟩
        (Fin n + 𝟙) × Aut (Fin n) ≃⟨ discrete-factorial (Fin n) Fin-is-discrete ⟩
        Aut (Fin n + 𝟙)           ■

   g : Σ k' ꞉ ℕ , Fin k' ≃ Aut (Fin (succ n))
   g = succ n ×' k , φ'

\end{code}

Geometric definition of the factorial function:

\begin{code}

 _! : ℕ → ℕ
 n ! = pr₁ (!construction n)

 infix 100 _!

\end{code}

The following are theorems rather than definitions:

\sbegin{code}

 !-base : 0 ! ≡ 1
 !-base = refl

 !-step : (n : ℕ) → (n +' 1)! ≡ (n +' 1) ×' n !
 !-step n = refl

\end{code}

Added 8th December 2019. Some corollaries.

Recall that a type X is finite if there is n : ℕ with X ≃ Fin n.

\begin{code}

open import UF-PropTrunc

module _ (pt : propositional-truncations-exist)
         (fe : FunExt)
         {𝓤 : Universe}
         {X : 𝓤 ̇ }
         where

 open finiteness pt
 open exponentiation-and-factorial fe
 open import UF-Equiv-FunExt

 Aut-finite : is-finite X → is-finite (Aut X)
 Aut-finite (n , α) = n ! , γ
  where
   δ : X ≃ Fin n → Aut X ≃ Fin (n !)
   δ d = Aut X       ≃⟨ ≃-cong fe d d ⟩
         Aut (Fin n) ≃⟨ ≃-sym (pr₂ (!construction n)) ⟩
         Fin (n !)   ■
   γ : ∥ Aut X ≃ Fin (n !) ∥
   γ = ∥∥-functor δ α

 module _ {𝓥 : Universe} {Y : 𝓥 ̇ } where

  +finite : is-finite X → is-finite Y → is-finite (X + Y)
  ×finite : is-finite X → is-finite Y → is-finite (X × Y)
  →finite : is-finite X → is-finite Y → is-finite (X → Y)

  +finite (m , α) (n , β) = m +' n , γ
   where
    δ : X ≃ Fin m → Y ≃ Fin n → X + Y ≃ Fin (m +' n)
    δ d e = X + Y         ≃⟨ +cong d e ⟩
            Fin m + Fin n ≃⟨ ≃-sym (pr₂ (+construction m n)) ⟩
            Fin (m +' n)  ■
    γ : ∥ X + Y ≃ Fin (m +' n) ∥
    γ = ∥∥-functor₂ δ α β

  ×finite (m , α) (n , β) = m ×' n , γ
   where
    δ : X ≃ Fin m → Y ≃ Fin n → X × Y ≃ Fin (m ×' n)
    δ d e = X × Y         ≃⟨ ×-cong d e ⟩
            Fin m × Fin n ≃⟨ ≃-sym (pr₂ (×construction m n)) ⟩
            Fin (m ×' n)  ■
    γ : ∥ X × Y ≃ Fin (m ×' n) ∥
    γ = ∥∥-functor₂ δ α β

  →finite (m , α) (n , β) = n ^ m , γ
   where
    δ : X ≃ Fin m → Y ≃ Fin n → (X → Y) ≃ Fin (n ^ m)
    δ d e = (X → Y)         ≃⟨ →cong (fe 𝓤₀ 𝓤₀) (fe 𝓤 𝓥) d e ⟩
            (Fin m → Fin n) ≃⟨ ≃-sym (pr₂ (→construction m n)) ⟩
            Fin (n ^ m)     ■
    γ : ∥ (X → Y) ≃ Fin (n ^ m) ∥
    γ = ∥∥-functor₂ δ α β

\end{code}

We have accounted for the type constructors +, ×, →, and ≃ (and hence
≡ if we assume univalence). The last two types to account for in our
spartan MLTT are Π and Σ.

\begin{code}

open import UF-PropIndexedPiSigma

Σconstruction : (n : ℕ) (a : Fin n → ℕ)
              → Σ k ꞉ ℕ , Fin k ≃ (Σ i ꞉ Fin n , Fin (a i))
Σconstruction 0 a = 0 , (Fin 0                    ≃⟨ ≃-refl _ ⟩
                         𝟘                        ≃⟨ ≃-sym (prop-indexed-sum-zero id) ⟩
                         (Σ i ꞉ 𝟘 , Fin (a i)) ■)
Σconstruction (succ n) a = g
 where
  IH : Σ k ꞉ ℕ , Fin k ≃ (Σ i ꞉ Fin n , Fin (a (suc i)))
  IH = Σconstruction n (λ i → a (suc i))
  k : ℕ
  k = pr₁ IH
  φ : Fin k ≃ (Σ i ꞉ Fin n , Fin (a (suc i)))
  φ = pr₂ IH
  φ' = Fin (a 𝟎 +' k)                                                      ≃⟨ i ⟩
       Fin (a 𝟎) + Fin k                                                   ≃⟨ ii ⟩
       Fin k + Fin (a 𝟎)                                                   ≃⟨ iii ⟩
       (Σ i ꞉ Fin n , Fin (a (suc i))) + (Σ i ꞉ 𝟙 , Fin (a (inr i))) ≃⟨ iv ⟩
      (Σ i ꞉ Fin n + 𝟙 , Fin (a i))                                     ■
   where
    i   = pr₂ (+construction (a 𝟎) k)
    ii  = +comm
    iii = +cong φ (≃-sym (prop-indexed-sum 𝟙-is-prop ⋆))
    iv  = Σ+distr (Fin n) 𝟙 (λ i → Fin (a i))

  g : Σ k' ꞉ ℕ , Fin k' ≃ (Σ i ꞉ Fin (succ n) , Fin (a i))
  g = a 𝟎 +' k , φ'

\end{code}

The numerical sum:

\begin{code}

∑ : {n : ℕ} → (Fin n → ℕ) → ℕ
∑ {n} a = pr₁ (Σconstruction n a)

\end{code}

Which is characterized by its usual inductive definition:

\begin{code}

∑-base : (a : Fin 0 → ℕ)
       → ∑ a ≡ 0
∑-base a = refl

∑-step : {n : ℕ} (a : Fin (succ n) → ℕ)
       → ∑ a ≡ a 𝟎 +' ∑ (a ∘ suc)
∑-step {n} a = refl

\end{code}

For Π we need function extensionality:

\begin{code}

module _ (fe : funext 𝓤₀ 𝓤₀) where

 Πconstruction : (n : ℕ) (a : Fin n → ℕ)
               → Σ k ꞉ ℕ , Fin k ≃ (Π i ꞉ Fin n , Fin (a i))
 Πconstruction 0 a = 1 , (Fin 1                     ≃⟨ i ⟩
                          𝟘 + 𝟙                     ≃⟨ ii ⟩
                          𝟙                         ≃⟨ iii ⟩
                          (Π i ꞉ 𝟘 , Fin (a i))     ≃⟨ iv ⟩
                          (Π i ꞉ Fin 0 , Fin (a i)) ■)
  where
   i   = ≃-refl _
   ii  = 𝟘-lneutral
   iii = ≃-sym (prop-indexed-product-one fe id)
   iv  = ≃-refl _

 Πconstruction (succ n) a = g
  where
   IH : Σ k ꞉ ℕ , Fin k ≃ (Π i ꞉ Fin n , Fin (a (suc i)))
   IH = Πconstruction n (λ i → a (suc i))
   k : ℕ
   k = pr₁ IH
   φ : Fin k ≃ (Π i ꞉ Fin n , Fin (a (suc i)))
   φ = pr₂ IH
   φ' = Fin (a 𝟎 ×' k)                                                      ≃⟨ i ⟩
        Fin (a 𝟎) × Fin k                                                   ≃⟨ ii ⟩
        Fin k × Fin (a 𝟎)                                                   ≃⟨ iii ⟩
        (Π i ꞉ Fin n , Fin (a (suc i))) × (Π i ꞉ 𝟙 , Fin (a (inr i))) ≃⟨ iv ⟩
        (Π i ꞉ Fin n + 𝟙 , Fin (a i))                                    ■
    where
     i   = pr₂ (×construction (a 𝟎) k)
     ii  = ×comm
     iii = ×-cong φ (≃-sym (prop-indexed-product fe 𝟙-is-prop ⋆))
     iv  = Π×+ fe

   g : Σ k' ꞉ ℕ , Fin k' ≃ (Π i ꞉ Fin (succ n) , Fin (a i))
   g = a 𝟎 ×' k , φ'

 ∏ : {n : ℕ} → (Fin n → ℕ) → ℕ
 ∏ {n} a = pr₁ (Πconstruction n a)

 ∏-base : (a : Fin 0 → ℕ)
        → ∏ a ≡ 1
 ∏-base a = refl

 ∏-step : {n : ℕ} (a : Fin (succ n) → ℕ)
        → ∏ a ≡ a 𝟎 ×' ∏ (a ∘ suc)
 ∏-step {n} a = refl

\end{code}

In order to avoid the use of the commutativity of + and × to get the
natural inductive constructions of ∑ and ∏, it would have been better
to have defined Fin(succ n) = 𝟙 + Fin n. In retrospect, this
definition seems more natural in general.

Todo: Corollary. If X is a type and A is an X-indexed family of types,
and if X is finite and A x is finite for every x : X, then the types Σ A
and Π A are finite.
