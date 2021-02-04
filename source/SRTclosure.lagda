Martin Escardo, 03 February 2021.

Symmetric, reflexive, transitive closure of a relation.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module SRTclosure where

open import UF-Subsingletons
open import UF-PropTrunc

open import NaturalsAddition renaming (_+_ to right-addition)

_∔_ : ℕ → ℕ → ℕ
m ∔ n = right-addition n m

_⊑_ : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → (X → X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
R ⊑ S = ∀ x y → R x y → S x y

\end{code}

The symmetric closure of a relation A:

\begin{code}

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
         (A : X → X → 𝓥 ̇ )
       where

 s-closure : X → X → 𝓥 ̇
 s-closure x y = A x y + A y x

 s-symmetric : Symmetric s-closure
 s-symmetric x y (inl a) = inr a
 s-symmetric x y (inr a) = inl a

 s-extension : A ⊑ s-closure
 s-extension x y = inl

 s-induction : (R : X → X → 𝓦 ̇ )
             → Symmetric R
             → A ⊑ R
             → s-closure ⊑ R
 s-induction R s A-included-in-R x y (inl a) = A-included-in-R x y a
 s-induction R s A-included-in-R x y (inr a) = s y x (A-included-in-R y x a)

\end{code}

To define the reflexive-transitive closure, we first consider the
iteration of a relation B:

\begin{code}

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
         (B : X → X → 𝓤 ̇ )
       where

 iteration : ℕ → X → X → 𝓤 ̇
 iteration zero     x y = x ≡ y
 iteration (succ n) x y = Σ z ꞉ X , B x z × iteration n z y

 iteration-reflexive : (x : X) → iteration 0 x x
 iteration-reflexive x = refl

 iteration-transitive' : (n : ℕ) (x y z : X) → iteration n x y → B y z → iteration (succ n) x z
 iteration-transitive' zero     x x z refl        b  = z , b , refl
 iteration-transitive' (succ n) x y z (t , b , c) b' = t , b , iteration-transitive' n t y z c b'

 iteration-symmetric : Symmetric B → (m : ℕ) → Symmetric (iteration m)
 iteration-symmetric sym zero     x x refl        = refl
 iteration-symmetric sym (succ m) x y (z , b , c) = γ
   where
    c' : iteration m y z
    c' = iteration-symmetric sym m z y c

    γ : iteration (succ m) y x
    γ = iteration-transitive' m y z x c' (sym x z b)

 iteration-transitive : (m n : ℕ) (x y z : X) → iteration m x y → iteration n y z → iteration (m ∔ n) x z
 iteration-transitive zero     n x x z refl        c' = c'
 iteration-transitive (succ m) n x y z (t , b , c) c' = t , b , iteration-transitive m n t y z c c'

\end{code}

The reflexive-transitive closure of a relation B:

\begin{code}

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
         (B : X → X → 𝓤 ̇ )
       where

 rt-closure : X → X → 𝓤 ̇
 rt-closure x y = Σ n ꞉ ℕ , iteration B n x y

 rt-reflexive : Reflexive rt-closure
 rt-reflexive x = 0 , refl

 rt-symmetric : Symmetric B → Symmetric rt-closure
 rt-symmetric s x y (m , c) = m , iteration-symmetric B s m x y c

 rt-transitive : Transitive rt-closure
 rt-transitive x y z (m , c) (m' , c') = (m ∔ m') , iteration-transitive B m m' x y z c c'

 rt-extension : B ⊑ rt-closure
 rt-extension x y b = 1 , y , b , refl

 rt-induction : (R : X → X → 𝓥 ̇)
              → Reflexive R
              → Transitive R
              → B ⊑ R
              → rt-closure ⊑ R
 rt-induction R r t B-included-in-R = γ
  where
   γ : (x y : X) → rt-closure x y → R x y
   γ x x (zero , refl)        = r x
   γ x y (succ n , z , b , c) = t x z y (B-included-in-R x z b) (γ z y (n , c))

\end{code}

By combining the symmetric closure with the reflective-transitive
closure, we get the symmetric-reflexive-transitive-closure:

\begin{code}

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
         (A : X → X → 𝓤 ̇ )
       where

 srt-closure : X → X → 𝓤 ̇
 srt-closure = rt-closure (s-closure A)

 srt-symmetric : Symmetric srt-closure
 srt-symmetric = rt-symmetric (s-closure A) (s-symmetric A)

 srt-reflexive : Reflexive srt-closure
 srt-reflexive = rt-reflexive (s-closure A)

 srt-transitive : Transitive srt-closure
 srt-transitive = rt-transitive (s-closure A)

 srt-extension : A ⊑ srt-closure
 srt-extension x y a = rt-extension (s-closure A) x y (s-extension A x y a)

 srt-induction : (R : X → X → 𝓥 ̇)
               → Symmetric R
               → Reflexive R
               → Transitive R
               → A ⊑ R
               → srt-closure ⊑ R
 srt-induction R s r t A-included-in-R x y = γ
  where
   δ : s-closure A ⊑ R
   δ = s-induction A R s A-included-in-R

   γ : srt-closure x y → R x y
   γ = rt-induction (s-closure A) R r t δ x y


\end{code}

The proposition-valued, symmetric-reflexive-transitive closure of A:

\begin{code}

module psrt
        (pt : propositional-truncations-exist)
        {𝓤 : Universe}
        {X : 𝓤 ̇ }
        (A : X → X → 𝓤 ̇ )
       where

 open PropositionalTruncation pt

 psrt-closure : X → X → 𝓤 ̇
 psrt-closure x y = ∥ srt-closure A x y ∥

 psrt-is-prop-valued : (x y : X) → is-prop (psrt-closure x y)
 psrt-is-prop-valued x y = ∥∥-is-prop

 psrt-symmetric : Symmetric psrt-closure
 psrt-symmetric x y = ∥∥-functor (srt-symmetric A x y)

 psrt-reflexive : Reflexive psrt-closure
 psrt-reflexive x = ∣ srt-reflexive A x ∣


 psrt-transitive : Transitive psrt-closure
 psrt-transitive x y z = ∥∥-functor₂ (srt-transitive A x y z)

 psrt-extension : A ⊑ psrt-closure
 psrt-extension x y a = ∥∥-functor (srt-extension A x y) ∣ a ∣

 psrt-induction : (R : X → X → 𝓥 ̇)
                → ((x y : X) → is-prop (R x y))
                → Reflexive R
                → Symmetric R
                → Transitive R
                → A ⊑ R
                → psrt-closure ⊑ R
 psrt-induction R p r s t A-included-in-R x y =
  ∥∥-rec (p x y) (srt-induction A R s r t A-included-in-R x y)

\end{code}
