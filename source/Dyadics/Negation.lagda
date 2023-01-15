\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Dyadics.Rationals
open import Integers.Type
open import Integers.Multiplication
open import Integers.Negation renaming (-_ to ℤ-_)
open import Integers.Parity
open import Naturals.Exponents
open import UF.Base hiding (_≈_)
open import UF.Subsingletons

module Dyadics.Negation where

-_ : ℤ[1/2] → ℤ[1/2]
- ((z , n) , _) = normalise-pos (ℤ- z , n)

infix 31 -_

ℤ[1/2]-minus-zero : - 0ℤ[1/2] ＝ 0ℤ[1/2]
ℤ[1/2]-minus-zero = refl

{-

minus-normalise-pos : (z : ℤ) (n : ℕ) → normalise-pos (z , n) ≈ - normalise-pos (ℤ- z , n)
minus-normalise-pos z n = {!!}
 where
  q : ℤ[1/2]
  q = normalise-pos (ℤ- z , n)

  z' : ℤ
  z' = (pr₁ ∘ pr₁) q

  n' : ℕ
  n' = (pr₂ ∘ pr₁) q

  i : normalise-pos (z , n) ＝ normalise-pos (ℤ- z' , n')
  i = ≈-to-＝ _ _ si
   where
    si : normalise-pos (z , n) ≈ normalise-pos (ℤ- z' , n')
    si = {!!} ＝⟨ {!!} ⟩
         {!!} ＝⟨ {!!} ⟩
         {!!} ＝⟨ {!!} ⟩
         {!!} ＝⟨ {!!} ⟩
         {!!} ∎
-}
{-

  normalise-pos (z , n) ≈ 

                        ≈ 
                        ≈ normalise-pos (- z' , n')
                        ≈ - (z' , n') , _
                        ≈ - normalise-pos (ℤ- z , n)
 

  q : ℤ[1/2]
  q = normalise-pos (ℤ- z , n)

-- q = normalise-pos (z' , n')
--        

  z' : ℤ
  z' = (pr₁ ∘ pr₁)  q

  n' : ℕ
  n' = (pr₂ ∘ pr₁) q

{-

   normalise-pos (z       , n)
   normalise-pos (- (- z) , n)

                                   
   normalise-pos (ℤ- z' , n')     ≈   - normalise-pos (ℤ- z , n)
   - (z' , n') , _                    - normalise-pos (z' , n')
   - q
   - normalise-pos (ℤ- z , n)

-}

  i : normalise-pos (ℤ- z , n) ≈ normalise-pos (ℤ- z' , n')
  i = {!!}

  ii : normalise-pos (z' , n') ≈ normalise-pos (ℤ- z , n)
  ii = ≈-sym q (normalise-pos (z' , n')) (≈-normalise-pos q)

  iii : {!!}
  iii = {!!}
-}
{-
ℤ[1/2]-minus-minus' : (z : ℤ[1/2]) → z ≈ - (- z)
ℤ[1/2]-minus-minus' ((z , n) , α) = γ
 where
-- TODO : Clean
  γ : (z , n) , α ≈ (- (- ((z , n) , α)))
  γ = ≈-trans₄ (((z , n) , α))
               (normalise-pos (z , n))
               (- normalise-pos (ℤ- z , n))
               (- (- normalise-pos (ℤ- (ℤ- z) , n)))
               (- (- normalise-pos (z , n)))
               (- (- ((z , n) , α)))
               (≈-normalise-pos ((z , n) , α)) -- first transitive proof
               (minus-normalise-pos z n)
               (≈-ap -_ (normalise-pos (ℤ- z , n)) (- normalise-pos (ℤ- (ℤ- z) , n)) (minus-normalise-pos (ℤ- z) n))
               (＝-to-≈ _ _ (ap (λ a → - (- normalise-pos (a , n))) (minus-minus-is-plus z)))
               (＝-to-≈ (- (- normalise-pos (z , n))) (- (- ((z , n) , α))) -- last transitive proof
                (ap (-_ ∘ -_)
                 (≈-to-＝ ((normalise-pos (z , n))) ((z , n) , α)
                  (≈-sym ((z , n) , α) (normalise-pos (z , n)) (≈-normalise-pos ((z , n) , α))))))

ℤ[1/2]-minus-minus : (z : ℤ[1/2]) → z ＝ - (- z)
ℤ[1/2]-minus-minus z = ≈-to-＝ z (- (- z)) (ℤ[1/2]-minus-minus' z)
-}
\end{code}

-_ : ℤ[1/2] → ℤ[1/2]
- ((z , n) , inl l)        = (ℤ- z , n) , (inl l)
- ((z , n) , inr (l , oz)) = (ℤ- z , n) , (inr (l , ℤodd-neg z oz))

minus : ℤ[1/2] → ℤ[1/2]
minus ((z , n) , _) = normalise-pos (ℤ- z , n)

ℤ[1/2]-minus-minus' : ∀ z → z ＝ minus (minus z)
ℤ[1/2]-minus-minus' ((z , n) , _) = {!!}


infix 31 -_

ℤ[1/2]-minus-zero : - 0ℤ[1/2] ＝ 0ℤ[1/2]
ℤ[1/2]-minus-zero = refl

{-
normalise-negation : (((z , n) , e) : ℤ[1/2]) → - normalise-pos (z , n) ＝ normalise-pos (ℤ- z , n)
normalise-negation ((z , n) , e) = {!!}
-}

ℤ[1/2]-minus-minus : (z : ℤ[1/2]) → z ＝ (- (- z))
ℤ[1/2]-minus-minus ((z , n) , inl l)        = ≈-to-＝ _ _ (ap (_* pos (2^ n)) (minus-minus-is-plus z ⁻¹))
ℤ[1/2]-minus-minus ((z , n) , inr (l , oz)) = ≈-to-＝ _ _ (ap (_* pos (2^ n)) (minus-minus-is-plus z ⁻¹))

\end{code}
