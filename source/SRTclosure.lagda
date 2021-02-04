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

open import NaturalsAddition renaming (_+_ to right-addition)

open import UF-Subsingletons
open import UF-PropTrunc

\end{code}

The symmetric closure of A:

\begin{code}

B : X → X → 𝓤 ̇
B x y = A x y + A y x

_⊑_ : (X → X → 𝓤 ̇ ) → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
R ⊑ S = ∀ x y → R x y → S x y

B-symmetric : (x y : X) → B x y → B y x
B-symmetric x y (inl a) = inr a
B-symmetric x y (inr a) = inl a

A-included-in-B : A ⊑ B
A-included-in-B x y = inl

B-induction : (R : X → X → 𝓥 ̇ )
            → Symmetric R
            → A ⊑ R
            → B ⊑ R
B-induction R s A-included-in-R x y (inl a) = A-included-in-R x y a
B-induction R s A-included-in-R x y (inr a) = s y x (A-included-in-R y x a)

\end{code}

To define the relexive-transitive closure of B, we consider an
intermmediate step:

\begin{code}

C : ℕ → X → X → 𝓤 ̇
C zero     x y = x ≡ y
C (succ n) x y = Σ z ꞉ X , B x z × C n z y

_∔_ : ℕ → ℕ → ℕ
m ∔ n = right-addition n m

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

\end{code}

The reflexive-transitive closure of B, and hence the
symmetric-reflexive-transitive closure of A:

\begin{code}

D : X → X → 𝓤 ̇
D x y = Σ n ꞉ ℕ , C n x y

D-reflexive : Reflexive D
D-reflexive x = 0 , refl

D-symmetric : Symmetric D
D-symmetric x y (m , c) = m , C-symmetric m x y c

D-transitive : Transitive D
D-transitive x y z (m , c) (m' , c') = (m ∔ m') , C-transitive m m' x y z c c'

B-included-in-D : B ⊑ D
B-included-in-D x y b = 1 , y , b , refl

A-included-in-D : A ⊑ D
A-included-in-D x y a = B-included-in-D x y (A-included-in-B x y a)

D-induction : (R : X → X → 𝓥 ̇)
            → Reflexive R
            → Symmetric R
            → Transitive R
            → A ⊑ R
            → D ⊑ R
D-induction R r s t A-included-in-R = γ
 where
  γ : (x y : X) → D x y → R x y
  γ x x (zero , refl)        = r x
  γ x y (succ n , z , b , c) = t x z y (B-induction R s A-included-in-R x z b)
                                       (γ z y (n , c))

\end{code}

The proposition-valued, symmetric-reflexive-transitive closure of A:

\begin{code}

module _ (pt : propositional-truncations-exist) where

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

 A-included-in-E : A ⊑ E
 A-included-in-E x y a = ∥∥-functor (A-included-in-D x y) ∣ a ∣

 E-induction : (R : X → X → 𝓥 ̇)
             → Reflexive R
             → Symmetric R
             → Transitive R
             → ((x y : X) → is-prop (R x y))
             → A ⊑ R
             → E ⊑ R
 E-induction R r s t R-is-prop-valued A-included-in-R x y =
  ∥∥-rec (R-is-prop-valued x y) (D-induction R r s t A-included-in-R x y)

\end{code}

TODO. Consider relations with rank (with applications to the
construction of free groups (without higher inductive types.

\begin{code}

open import NaturalsOrder

module _ (ℓ : X → ℕ)
         (δ : (x y : X) → A x y → ℓ x > ℓ y)
       where



\end{code}
