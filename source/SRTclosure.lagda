Martin Escardo, 03 February 2021.

Symmetric, reflexive, transitive closure of a relation. Also of a
relation with rank.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module SRTclosure
       (𝓤 : Universe)
       (X : 𝓤 ̇ )
       (A : X → X → 𝓤 ̇ )
       where

open import UF-Subsingletons
open import UF-Base
open import UF-Retracts
open import UF-Equiv
open import UF-UniverseEmbedding
open import UF-UA-FunExt
open import UF-FunExt
open import UF-PropTrunc

B : X → X → 𝓤 ̇
B x y = A x y + A y x

B-symmetric : (x y : X) → B x y → B y x
B-symmetric x y (inl a) = inr a
B-symmetric x y (inr a) = inl a

A-included-in-B : (x y : X) → A x y → B x y
A-included-in-B x y = inl

B-induction : (R : X → X → 𝓥 ̇ )
            → Symmetric R
            → ((x y : X) → A x y → R x y)
            → ((x y : X) → B x y → R x y)
B-induction R s A-included-in-R x y (inl a) = A-included-in-R x y a
B-induction R s A-included-in-R x y (inr a) = s y x (A-included-in-R y x a)

C : ℕ → X → X → 𝓤 ̇
C zero     x y = x ≡ y
C (succ n) x y = Σ z ꞉ X , B x z × C n z y

_∔_ : ℕ → ℕ → ℕ
zero   ∔ n = n
succ m ∔ n = succ (m ∔ n)

C-reflexive : (x : X) → C 0 x x
C-reflexive x = refl

CB-transitive : (n : ℕ) (x y z : X) → C n x y → B y z → C (succ n) x z
CB-transitive zero     x x z refl        b  = z , b , refl
CB-transitive (succ n) x y z (t , b , c) b' = t , b , CB-transitive n t y z c b'

C-symmetric : (m : ℕ) (x y : X) → C m x y → C m y x
C-symmetric zero     x x refl        = refl
C-symmetric (succ m) x y (z , b , c) = γ
  where
   c' : C m y z
   c' = C-symmetric m z y c

   γ : C (succ m) y x
   γ = CB-transitive m y z x c' (B-symmetric x z b)

C-transitive : (m n : ℕ) (x y z : X) → C m x y → C n y z → C (m ∔ n) x z
C-transitive zero     n x x z refl        c' = c'
C-transitive (succ m) n x y z (t , b , c) c' = t , b , C-transitive m n t y z c c'

D : X → X → 𝓤 ̇
D x y = Σ n ꞉ ℕ , C n x y

D-reflexive : Reflexive D
D-reflexive x = 0 , refl

D-symmetric : Symmetric D
D-symmetric x y (m , c) = m , C-symmetric m x y c

D-transitive : Transitive D
D-transitive x y z (m , c) (m' , c') = (m ∔ m') , C-transitive m m' x y z c c'

B-included-in-D : (x y : X) → B x y → D x y
B-included-in-D x y b = 1 , y , b , refl

A-included-in-D : (x y : X) → A x y → D x y
A-included-in-D x y a = B-included-in-D x y (A-included-in-B x y a)

D-induction : (R : X → X → 𝓥 ̇)
            → Reflexive R
            → Symmetric R
            → Transitive R
            → ((x y : X) → A x y → R x y)
            → ((x y : X) → D x y → R x y)
D-induction R r s t A-included-in-R = D-included-in-R
 where
  D-included-in-R : (x y : X) → D x y → R x y
  D-included-in-R x x (zero , refl) = r x
  D-included-in-R x y (succ n , z , b , c) = t x z y (B-induction R s A-included-in-R x z b)
                                                     (D-included-in-R z y (n , c))

module _ (pt : propositional-truncations-exist)
         (A-is-prop-valued : (x y : X) → is-prop (A x y))
       where

 open PropositionalTruncation pt

 E : X → X → 𝓤 ̇
 E x y = ∥ D x y ∥

 E-is-prop-valued : (x y : X) → is-prop (E x y)
 E-is-prop-valued x y = ∥∥-is-prop

 E-reflexive : Reflexive E
 E-reflexive x = ∣ D-reflexive x ∣

 E-symmetric : Symmetric E
 E-symmetric x y = ∥∥-functor (D-symmetric x y)

 E-transitive : Transitive E
 E-transitive x y z = ∥∥-functor₂ (D-transitive x y z)

 A-included-in-E : (x y : X) → A x y → E x y
 A-included-in-E x y a = ∥∥-functor (A-included-in-D x y) ∣ a ∣

 E-induction : (R : X → X → 𝓥 ̇)
             → Reflexive R
             → Symmetric R
             → Transitive R
             → ((x y : X) → is-prop (R x y))
             → ((x y : X) → A x y → R x y)
             → ((x y : X) → E x y → R x y)
 E-induction R r s t R-is-prop-valued A-included-in-R x y =
  ∥∥-rec (R-is-prop-valued x y) (D-induction R r s t A-included-in-R x y)
