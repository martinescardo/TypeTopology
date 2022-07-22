```agda

{-# OPTIONS --allow-unsolved-metas #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.CanonicalMap
open import Notation.Order
open import DedekindReals.Integers.Integers
open import DedekindReals.Integers.Addition
open import DedekindReals.Integers.Order
open import DedekindReals.Integers.Multiplication
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Multiplication renaming (_*_ to _*ℕ_)
open import DedekindReals.Integers.Negation
open import UF.Base
open import UF.FunExt
open import UF.Powerset hiding (𝕋)
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Quotient

module Todd.BelowLemmas
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (sq : set-quotients-exist)
 where

open import Todd.BelowAndAbove fe using (below-implies-below' ; _below'_ ; below'-implies-below)
open import Todd.DyadicReals pe pt fe
open import Todd.RationalsDyadic fe
open import Todd.TernaryBoehmRealsPrelude fe
open import Todd.TernaryBoehmReals pt fe pe sq hiding (ι ; _≤_≤_)

UU : ℤ → ℤ
UU (pos x)     = (pos x /2') /2'
UU (negsucc x) = - (((pos x + pos 4) /2') /2')

below-upRight-lem₁ : (z : ℤ) → upRight (upRight z) ＝ UU z
below-upRight-lem₁ (pos x) = refl
below-upRight-lem₁ (negsucc x) = refl

below-upRight-lem₃ : (a b : ℤ) → a * pos 2 + b * pos 2 ＝ pos 2 * (a + b)
below-upRight-lem₃ a b = (distributivity-mult-over-ℤ a b (pos 2) ⁻¹ ∙ ℤ*-comm (a + b) (pos 2))

below-upRight-lem₂ : ((x , b) (y , b') : 𝕋) → (n : ℤ) → (x (succℤ n) + y (succℤ n) ＝ pos 2 * (x n + y n))
                                                      ∔ (x (succℤ n) + y (succℤ n) ＝ pos 2 * (x n + y n) + pos 1)
                                                      ∔ (x (succℤ n) + y (succℤ n) ＝ pos 2 * (x n + y n) + pos 2)
                                                      ∔ (x (succℤ n) + y (succℤ n) ＝ pos 2 * (x n + y n) + pos 3)
                                                      ∔ (x (succℤ n) + y (succℤ n) ＝ pos 2 * (x n + y n) + pos 4) 
below-upRight-lem₂ (x , b) (y , b') n with below-implies-below' (x (succℤ n)) (x n) (b n) , below-implies-below' (y (succℤ n)) (y n) (b' n)
... | inl a , inl b
 = inl (ap₂ _+_ a b ∙ distributivity-mult-over-ℤ (x n) (y n) (pos 2) ⁻¹ ∙ ℤ*-comm (x n + y n) (pos 2))
... | inl a , inr (inl b)
 = inr (inl (ap₂ _+_ a b ∙ ℤ-right-succ (x n * pos 2) (y n * pos 2) ∙ ap succℤ (below-upRight-lem₃ (x n) (y n))))
... | inl a , inr (inr b)
 = inr (inr (inl (ap₂ _+_ a b ∙ ℤ-right-succ (x n * pos 2) (succℤ (y n * pos 2)) ∙ ap succℤ (ℤ-right-succ (x n * pos 2) (y n * pos 2)) ∙ ap (_+ pos 2) (below-upRight-lem₃ (x n) (y n)))))
... | inr (inl a) , inl b
 = inr (inl (ap₂ _+_ a b ∙ ℤ-left-succ (x n * pos 2) (y n * pos 2) ∙ ap succℤ (below-upRight-lem₃ (x n) (y n))))
... | inr (inr a) , inl b
 = inr (inr (inl (ap₂ _+_ a b ∙ ℤ-left-succ (succℤ (x n * pos 2)) (y n * pos 2) ∙ ap succℤ (ℤ-left-succ (x n * pos 2) (y n * pos 2)) ∙ ap (_+ pos 2) (below-upRight-lem₃ (x n) (y n)))))
... | inr (inl a) , inr (inl b)
 = inr (inr (inl (ap₂ _+_ a b ∙ ℤ-left-succ (x n * pos 2) (succℤ (y n * pos 2)) ∙ ap succℤ (ℤ-right-succ (x n * pos 2) (y n * pos 2)) ∙ ap (_+ pos 2) (below-upRight-lem₃ (x n) (y n)))))
... | inr (inr a) , inr (inl b)
  = inr (inr (inr (inl (ap₂ _+_ a b ∙ ℤ-right-succ (succℤ (succℤ (x n * pos 2))) (y n * pos 2) ∙ ap succℤ (ℤ-left-succ (succℤ (x n * pos 2)) (y n * pos 2)) ∙ ap (_+ pos 2) (ℤ-left-succ (x n * pos 2) (y n * pos 2)) ∙ ap (_+ pos 3) (below-upRight-lem₃ (x n) (y n))))))
... | inr (inl a) , inr (inr b)
 = inr (inr (inr (inl (ap₂ _+_ a b ∙ ℤ-left-succ (x n * pos 2) (y n * pos 2 + pos 2) ∙ ap succℤ (ℤ-right-succ (x n * pos 2) (y n * pos 2 + pos 1)) ∙ ap (_+ pos 2) (ℤ-right-succ (x n * pos 2) (y n * pos 2)) ∙ ap (_+ pos 3) (below-upRight-lem₃ (x n) (y n))))))
... | inr (inr a) , inr (inr b)
 = inr (inr (inr (inr (ap₂ _+_ a b ∙ ℤ-left-succ (succℤ (x n * pos 2)) (y n * pos 2 + pos 2) ∙ ap succℤ (ℤ-left-succ (x n * pos 2) (y n * pos 2 + pos 2)) ∙ ap (_+ pos 2) (ℤ-right-succ (x n * pos 2) (succℤ (y n * pos 2))) ∙ ap (_+ pos 3) (ℤ-right-succ (x n * pos 2) (y n * pos 2)) ∙ ap (_+ pos 4) (below-upRight-lem₃ (x n) (y n))))))

UU-lemma₁ : (x : ℤ) → UU (pos 8 + x) ＝ pos 2 + UU x
UU-lemma₁ (pos 0) = refl
UU-lemma₁ (pos 1) = refl
UU-lemma₁ (pos 2) = refl
UU-lemma₁ (pos 3) = refl
UU-lemma₁ (pos (succ (succ (succ (succ x))))) = UU (pos 8 + pos (succ (succ (succ (succ x)))))        ＝⟨ ap UU (ℤ+-comm (pos 8) (pos (succ (succ (succ (succ x)))))) ⟩
                                               UU (pos (succ (succ (succ (succ x)))) + pos 8)         ＝⟨ refl ⟩
                                               succℤ (succℤ (UU (pos (succ (succ (succ (succ x))))))) ＝⟨ ℤ+-comm (UU (pos (succ (succ (succ (succ x)))))) (pos 2) ⟩
                                               pos 2 + UU (pos (succ (succ (succ (succ x))))) ∎
UU-lemma₁ (negsucc 0) = refl
UU-lemma₁ (negsucc 1) = refl
UU-lemma₁ (negsucc 2) = refl
UU-lemma₁ (negsucc 3) = refl
UU-lemma₁ (negsucc 4) = refl
UU-lemma₁ (negsucc 5) = refl
UU-lemma₁ (negsucc 6) = refl
UU-lemma₁ (negsucc 7) = refl
UU-lemma₁ (negsucc (succ (succ (succ (succ (succ (succ (succ (succ x)))))))))
 = UU (pos 8 + negsucc (x +ℕ 8))        ＝⟨ refl ⟩
   UU (pos 8 + (negsucc x - pos 8))     ＝⟨ ap (λ z → UU (pos 8 + z)) (ℤ+-comm (negsucc x) (- pos 8)) ⟩
   UU (pos 8 + ((- pos 8) + negsucc x)) ＝⟨ ap UU (ℤ+-assoc (pos 8) (- pos 8) (negsucc x) ⁻¹) ⟩
   UU (pos 0 + negsucc x)               ＝⟨ ap UU (ℤ+-comm (pos 0) (negsucc x)) ⟩
   UU (negsucc x)                       ＝⟨ refl ⟩
   negsucc (x /2 /2)                                 ＝⟨ predsuccℤ (negsucc (x /2 /2)) ⁻¹ ⟩
   predℤ (succℤ (negsucc (x /2 /2)))                 ＝⟨ ap predℤ (predsuccℤ (succℤ (negsucc (x /2 /2))) ⁻¹) ⟩
   predℤ (predℤ (succℤ (succℤ (negsucc (x /2 /2))))) ＝⟨ ap (λ z → predℤ (predℤ z)) (ℤ+-comm (negsucc ((x /2) /2)) (pos 2)) ⟩
   predℤ (predℤ (pos 2 + negsucc ((x /2) /2)))       ＝⟨ refl ⟩
   pos 2 + UU (negsucc (x +ℕ 8))                     ∎

UU-lemma₂ : (x : ℕ) (y : ℤ) → UU y below pos x → UU (pos 8 + y) below pos (succ x)
UU-lemma₂ x y b with below-implies-below' (UU y) (pos x) b
... | inl UUy2x
 = below'-implies-below (UU (pos 8 + y)) (pos (succ x))
    (inl (UU-lemma₁ y
          ∙ ap (pos 2 +_) UUy2x
           ∙ ℤ+-comm (pos 2) (pos x * pos 2)
            ∙ ℤ-left-succ (pos x) (pos (succ x)) ⁻¹))
... | inr (inl UUy2x+1)
 = below'-implies-below (UU (pos 8 + y)) (pos (succ x))
    (inr (inl (UU-lemma₁ y
               ∙ ap (pos 2 +_) UUy2x+1
                ∙ ℤ+-assoc (pos 1) (pos 1) (succℤ (pos x * pos 2))
                 ∙ ℤ+-comm (pos 1) (pos 1 + succℤ (pos x * pos 2))
                  ∙ ap succℤ (ℤ+-comm (pos 1) (succℤ (pos x * pos 2)))
                   ∙ ap succℤ (ℤ-left-succ (pos x) (pos (succ x)) ⁻¹))))
... | inr (inr UUy2x+2)
 = below'-implies-below (UU (pos 8 + y)) (pos (succ x))
   (inr (inr (UU-lemma₁ y
              ∙ ap (pos 2 +_) UUy2x+2
               ∙ ℤ+-comm (pos 2) (succℤ (succℤ (pos x * pos 2)))
                ∙ ap (_+ pos 2) (ℤ-left-succ (pos x) (pos (succ x))) ⁻¹)))

UU-below : (x : ℕ) → UU (pos 8 + pos 2 * pos x) below succℤ (UU (pos x))
UU-below 0 = (0 , refl) , (2 , refl)
UU-below 1 = (0 , refl) , (2 , refl)
UU-below 2 = (1 , refl) , (1 , refl)
UU-below 3 = (1 , refl) , (1 , refl)
UU-below (succ (succ (succ (succ x)))) = UU-lemma₂ (succ (x /2 /2)) (pos 2 + (pos 2 + (pos 2 + (pos 2 + pos 2 * pos x)))) (transport (_below pos (succ ((x /2) /2))) (ap UU I) (UU-below x))
 where
  I : pos 8 + pos 2 * pos x ＝ pos 2 + (pos 2 + (pos 2 + (pos 2 + pos 2 * pos x)))
  I = ℤ+-assoc (pos 6) (pos 2) (pos 2 * pos x) ∙ ℤ+-assoc (pos 4) (pos 2) (pos 2 + pos 2 * pos x) ∙ ℤ+-assoc (pos 2) (pos 2) (pos 2 + (pos 2 + pos 2 * pos x))

UU-growth : ∀ x → succℤ (UU x) ＝ UU (x + pos 4)
UU-growth (pos x) = refl
UU-growth (negsucc 0) = refl
UU-growth (negsucc 1) = refl
UU-growth (negsucc 2) = refl
UU-growth (negsucc 3) = refl
UU-growth (negsucc (succ (succ (succ (succ x))))) = refl

UU-neg-lem : (x : ℤ) → UU (negsucc 7 + x) ＝ negsucc 1 + UU x
UU-neg-lem (pos 0) = refl
UU-neg-lem (pos 1) = refl
UU-neg-lem (pos 2) = refl
UU-neg-lem (pos 3) = refl
UU-neg-lem (pos (succ (succ (succ (succ x))))) = UU (negsucc 7 + pos (succ (succ (succ (succ x))))) ＝⟨ ap (λ z → UU (negsucc 7 + z)) (distributivity-pos-addition x 4) ⟩
                                                UU (negsucc 7 + (pos x + pos 4))                   ＝⟨ ap UU (ℤ+-assoc (negsucc 7) (pos x) (pos 4) ⁻¹)  ⟩
                                                UU (negsucc 7 + pos x + pos 4)                     ＝⟨ UU-growth (negsucc 7 + pos x) ⁻¹ ⟩
                                                succℤ (UU (negsucc 7 + pos x))                     ＝⟨ refl ⟩
                                                UU (negsucc 7 + pos x) + pos 1                     ＝⟨ ap (_+ pos 1) (UU-neg-lem (pos x)) ⟩
                                                negsucc 1 + (UU (pos x)) + pos 1                   ＝⟨ refl ⟩ 
                                                negsucc 1 + UU (pos (succ (succ (succ (succ x))))) ∎
UU-neg-lem (negsucc 0) = refl
UU-neg-lem (negsucc 1) = refl
UU-neg-lem (negsucc 2) = refl
UU-neg-lem (negsucc 3) = refl
UU-neg-lem (negsucc (succ (succ (succ (succ x))))) = UU (negsucc 7 + negsucc (succ (succ (succ (succ x)))))     ＝⟨ refl ⟩
                                                    UU ((- pos 8) + (- pos (succ x)) - pos 4)                  ＝⟨ ap (λ l → UU (l - pos 4)) (negation-dist (pos 8) (pos (succ x))) ⟩
                                                    UU ((- (pos 8 + pos (succ x))) - pos 4)                    ＝⟨ ap (λ z → UU ((- z) - pos 4)) (distributivity-pos-addition 8 (succ x)) ⟩
                                                    UU ((- pos (8 +ℕ (succ x))) - pos 4)                       ＝⟨ refl ⟩
                                                    predℤ (UU (- pos (8 +ℕ (succ x))))                         ＝⟨ ap (λ l → predℤ (UU (- l))) (distributivity-pos-addition 8 (succ x) ⁻¹) ⟩
                                                    predℤ (UU (- (pos 8 + pos (succ x))))                      ＝⟨ ap (λ z → predℤ (UU z)) (negation-dist (pos 8) (pos (succ x)) ⁻¹) ⟩
                                                    predℤ (UU ((- pos 8) - pos (succ x)))                      ＝⟨ refl ⟩
                                                    UU (negsucc 7 + negsucc x) + negsucc 0                     ＝⟨ ap (_+ negsucc 0) (UU-neg-lem (negsucc x)) ⟩
                                                    negsucc 1 + UU (negsucc x) + negsucc 0                     ＝⟨ ℤ+-assoc (negsucc 1) (UU (negsucc x)) (negsucc 0) ⟩
                                                    negsucc 1 + (UU (negsucc x) + negsucc 0)                   ＝⟨ refl ⟩
                                                    negsucc 1 + UU (negsucc (succ (succ (succ (succ x)))))     ∎

below-pred : (x y : ℤ) → y below x → negsucc 1 + y below predℤ x
below-pred x y (l₁ , l₂) = first , second
 where
  first : downLeft (predℤ x) ≤ (negsucc 1 + y)
  first = transport₂ _≤_ I II (ℤ≤-adding' (downLeft x) y (negsucc 1) l₁)
   where
    I : downLeft x - pos 2 ＝ downLeft (predℤ x)
    I = ap predℤ (ℤ-left-pred x x ⁻¹) ∙ ℤ-right-pred (predℤ x) x ⁻¹
    II : y + negsucc 1 ＝ negsucc 1 + y
    II = ℤ+-comm y (negsucc 1)
  second : negsucc 1 + y ≤ downRight (predℤ x)
  second = transport₂ _≤_ I II (ℤ≤-adding' y (downRight x) (negsucc 1) l₂)
   where
    I : y + negsucc 1 ＝ negsucc 1 + y
    I = ℤ+-comm y (negsucc 1)
    II : downRight x + negsucc 1 ＝ downRight (predℤ x)
    II = predℤ (predℤ (succℤ (succℤ (x + x)))) ＝⟨ ap predℤ (predsuccℤ (succℤ (x + x))) ⟩
         predℤ (succℤ (x + x))                 ＝⟨ predsuccℤ (x + x) ⟩
         x + x                                 ＝⟨ succpredℤ (x + x) ⁻¹ ⟩
         succℤ (predℤ (x + x))                 ＝⟨ ap succℤ (succpredℤ (predℤ (x + x)) ⁻¹) ⟩
         succℤ (succℤ (predℤ (predℤ (x + x)))) ＝⟨ ap (λ z → succℤ (succℤ (predℤ z))) (ℤ-right-pred x x ⁻¹) ⟩
         succℤ (succℤ (predℤ (x + predℤ x)))   ＝⟨ ap (λ z → succℤ (succℤ z)) (ℤ-left-pred x (predℤ x) ⁻¹) ⟩
         succℤ (succℤ ((predℤ x + predℤ x)))   ＝⟨ refl ⟩
         downRight (predℤ x)                   ∎

UU-below-neg : (x : ℕ) → UU ((- pos 8) + pos 2 * negsucc x) below predℤ (UU (negsucc x))
UU-below-neg 0 = (1 , refl) , (1 , refl)
UU-below-neg 1 = (1 , refl) , (1 , refl)
UU-below-neg 2 = (0 , refl) , (2 , refl)
UU-below-neg 3 = (0 , refl) , (2 , refl)
UU-below-neg (succ (succ (succ (succ x)))) =
  transport
    (_below negsucc (succ (succ ((x /2) /2))))
     (UU-neg-lem (negsucc 1 + (negsucc 1 + (negsucc 1 + (negsucc 1 + pos 2 * negsucc x)))) ⁻¹)
      (below-pred (negsucc (succ (x /2 /2))) (UU (negsucc 1 + (negsucc 1 + (negsucc 1 + (negsucc 1 + pos 2 * negsucc x))))) I)
  where
   I : UU (negsucc 1 + (negsucc 1 + (negsucc 1 + (negsucc 1 + pos 2 * negsucc x)))) below negsucc (succ ((x /2) /2))
   I = transport
        (_below negsucc (succ ((x /2) /2)))
         (ap UU (ℤ+-assoc (negsucc 5) (negsucc 1) (pos 2 * negsucc x)
                 ∙ ℤ+-assoc (negsucc 3) (negsucc 1) (negsucc 1 + pos 2 * negsucc x)
                  ∙ ℤ+-assoc (negsucc 1) (negsucc 1) (negsucc 1 + (negsucc 1 + pos 2 * negsucc x))))
          (UU-below-neg x)

-- (z : ℤ) (n : ℕ) ∀ a b → (upRight ^ n) (pos {!!} * z            ) below (upRight ^ n) z
-- (z : ℤ) (n : ℕ) ∀ a b → (upRight ^ n) (pos {!!} * z +pos (2^ n)) below (upRight ^ n) z

-- (k c : ℤ) → k ≤ c → Σ i ꞉ ℕ , ((n : ℕ) → (lb ((upRight ^ i) k , n - i) ≤ lb (c , n)) × (rb (c , n) ≤ rb ((upRight ^ i) k , n - i)

--  [                                   ] = 3
--  [                          ]
--  [                ]
--  [   k    ]             [   c  ]

UU-double-0 : (z : ℤ) → UU (pos 2 * z) below UU z
UU-double-0 (pos 0) = (0 , refl) , (2 , refl)
UU-double-0 (pos 1) = (0 , refl) , (2 , refl)
UU-double-0 (pos 2) = (1 , refl) , (1 , refl)
UU-double-0 (pos 3) = (1 , refl) , (1 , refl)
UU-double-0 (pos (succ (succ (succ (succ x))))) = transport (_below succℤ (UU (pos x))) I (UU-below x)
 where
  I : UU (pos 8 + pos 2 * pos x) ＝  UU (pos 2 + (pos 2 + (pos 2 + (pos 2 + pos 2 * pos x))))
  I = ap UU (ℤ+-assoc (pos 6) (pos 2) (pos 2 * pos x) ∙ ℤ+-assoc (pos 4) (pos 2) (pos 2 + pos 2 * pos x) ∙ ℤ+-assoc (pos 2) (pos 2) (pos 2 + (pos 2 + pos 2 * pos x)))
UU-double-0 (negsucc 0) = (1 , refl) , 1 , refl
UU-double-0 (negsucc 1) = (1 , refl) , 1 , refl
UU-double-0 (negsucc 2) = (0 , refl) , 2 , refl
UU-double-0 (negsucc 3) = (0 , refl) , (2 , refl)
UU-double-0 (negsucc (succ (succ (succ (succ x))))) =
 transport (_below predℤ (UU (negsucc x))) I (UU-below-neg x)
  where
   I : UU (negsucc 7 + pos 2 * negsucc x) ＝ UU (negsucc 1 + (negsucc 1 + (negsucc 1 + (negsucc 1 + pos 2 * negsucc x))))
   I = ap UU (ℤ+-assoc (negsucc 5) (negsucc 1) (pos 2 * negsucc x) ∙ ℤ+-assoc (negsucc 3) (negsucc 1) (negsucc 1 + pos 2 * negsucc x) ∙ ℤ+-assoc (negsucc 1) (negsucc 1) (negsucc 1 + (negsucc 1 + pos 2 * negsucc x)))

UU-mod-behaviour-1 : ∀ x → (UU (x + pos 1) ＝ UU x) ∔ (UU (x + pos 1) ＝ succℤ (UU x))
UU-mod-behaviour-1 (pos 0) = inl refl
UU-mod-behaviour-1 (pos 1) = inl refl
UU-mod-behaviour-1 (pos 2) = inl refl
UU-mod-behaviour-1 (pos 3) = inr refl
UU-mod-behaviour-1 (pos (succ (succ (succ (succ x))))) with UU-mod-behaviour-1 (pos x)
... | inl e = inl (ap succℤ e)
... | inr e = inr (ap succℤ e)
UU-mod-behaviour-1 (negsucc 0) = inr refl
UU-mod-behaviour-1 (negsucc 1) = inl refl
UU-mod-behaviour-1 (negsucc 2) = inl refl
UU-mod-behaviour-1 (negsucc 3) = inl refl
UU-mod-behaviour-1 (negsucc 4) = inr refl
UU-mod-behaviour-1 (negsucc 5) = inl refl
UU-mod-behaviour-1 (negsucc 6) = inl refl 
UU-mod-behaviour-1 (negsucc 7) = inl refl
UU-mod-behaviour-1 (negsucc (succ (succ (succ (succ (succ (succ (succ (succ x))))))))) with UU-mod-behaviour-1 (negsucc (succ (succ (succ (succ x)))))
... | inl e = inl (ap predℤ e)
... | inr e = inr (ap predℤ e)

UU-mod-behaviour-2 :  ∀ x → (UU (x + pos 2) ＝ UU x) ∔ (UU (x + pos 2) ＝ succℤ (UU x))
UU-mod-behaviour-2 (pos 0) = inl refl
UU-mod-behaviour-2 (pos 1) = inl refl
UU-mod-behaviour-2 (pos 2) = inr refl
UU-mod-behaviour-2 (pos 3) = inr refl
UU-mod-behaviour-2 (pos (succ (succ (succ (succ x))))) with UU-mod-behaviour-2 (pos x)
... | inl e = inl (ap succℤ e)
... | inr e = inr (ap succℤ e)
UU-mod-behaviour-2 (negsucc 0) = inr refl
UU-mod-behaviour-2 (negsucc 1) = inr refl
UU-mod-behaviour-2 (negsucc 2) = inl refl
UU-mod-behaviour-2 (negsucc 3) = inl refl
UU-mod-behaviour-2 (negsucc 4) = inr refl
UU-mod-behaviour-2 (negsucc 5) = inr refl
UU-mod-behaviour-2 (negsucc 6) = inl refl
UU-mod-behaviour-2 (negsucc 7) = inl refl
UU-mod-behaviour-2 (negsucc (succ (succ (succ (succ (succ (succ (succ (succ x))))))))) with UU-mod-behaviour-2 (negsucc (succ (succ (succ (succ x)))))
... | inl e = inl (ap predℤ e)
... | inr e = inr (ap predℤ e)

UU-mod-behaviour-3 :  ∀ x → (UU (x + pos 3) ＝ UU x) ∔ (UU (x + pos 3) ＝ succℤ (UU x))
UU-mod-behaviour-3 (pos 0) = inl refl
UU-mod-behaviour-3 (pos 1) = inr refl
UU-mod-behaviour-3 (pos 2) = inr refl
UU-mod-behaviour-3 (pos 3) = inr refl
UU-mod-behaviour-3 (pos (succ (succ (succ (succ x))))) with UU-mod-behaviour-3 (pos x)
... | inl e = inl (ap succℤ e)
... | inr e = inr (ap succℤ e)
UU-mod-behaviour-3 (negsucc 0) = inr refl
UU-mod-behaviour-3 (negsucc 1) = inr refl
UU-mod-behaviour-3 (negsucc 2) = inr refl
UU-mod-behaviour-3 (negsucc 3) = inl refl
UU-mod-behaviour-3 (negsucc 4) = inr refl
UU-mod-behaviour-3 (negsucc 5) = inr refl
UU-mod-behaviour-3 (negsucc 6) = inr refl
UU-mod-behaviour-3 (negsucc 7) = inl refl
UU-mod-behaviour-3 (negsucc (succ (succ (succ (succ (succ (succ (succ (succ x))))))))) with UU-mod-behaviour-3 (negsucc (succ (succ (succ (succ x)))))
... | inl e = inl (ap predℤ e)
... | inr e = inr (ap predℤ e)

UU-double-4 : (z : ℤ) → UU (pos 2 * z + pos 4) below UU z
UU-double-4 (pos 0) = (1 , refl) , (1 , refl)
UU-double-4 (pos 1) = (1 , refl) , (1 , refl)
UU-double-4 (pos 2) = (2 , refl) , (0 , refl)
UU-double-4 (pos 3) = (2 , refl) , (0 , refl)
UU-double-4 (pos (succ (succ (succ (succ x))))) with UU-double-4 (pos x)
... | l₁ , l₂ = first , second
 where
  first : succℤ (pos (succ ((x /2) /2)) + pos ((x /2) /2)) ≤ℤ UU (succℤ (succℤ (succℤ (succℤ (pos 2 + (pos 2 + (pos 2 + (pos 2 + pos 2 * pos x))))))))
  first = transport₂ _≤ℤ_ I II (ℤ≤-adding' (pos ((x /2) /2) * pos 2) (UU (succℤ (succℤ (succℤ (succℤ (pos 2 * pos x)))))) (pos 2) l₁)
   where
    I : pos ((x /2) /2) * pos 2 + pos 2 ＝ succℤ (pos (succ ((x /2) /2)) + pos ((x /2) /2))
    I = pos ((x /2) /2) * pos 2 + pos 2                  ＝⟨ refl ⟩
        succℤ (succℤ (pos ((x /2) /2) +pos ((x /2) /2))) ＝⟨ ap succℤ (ℤ-left-succ (pos (x /2 /2)) (pos (x /2 /2)) ⁻¹) ⟩
        succℤ (pos (succ ((x /2) /2)) + pos ((x /2) /2)) ∎
    II : UU (succℤ (succℤ (succℤ (succℤ (pos 2 * pos x))))) + pos 2 ＝ UU (succℤ  (succℤ (succℤ (succℤ (pos 2 + (pos 2 + (pos 2 + (pos 2 + pos 2 * pos x))))))))
    II = UU (succℤ (succℤ (succℤ (succℤ (pos 2 * pos x))))) + pos 2       ＝⟨ refl ⟩
         UU (pos 2 * pos x + pos 4) + pos 2                               ＝⟨ ap (_+ pos 2) (UU-growth (pos 2 * pos x) ⁻¹) ⟩
         succℤ (UU (pos 2 * pos x)) + pos 2                               ＝⟨ ap succℤ (ℤ+-comm (UU (pos 2 * pos x)) (pos 2)) ⟩
         succℤ (pos 2 + UU (pos 2 * pos x))                               ＝⟨ ap succℤ (UU-lemma₁ (pos 2 * pos x) ⁻¹) ⟩
         succℤ (UU (pos 8 + pos 2 * pos x))                               ＝⟨ ap (λ z → succℤ (UU z)) (ℤ+-assoc (pos 6) (pos 2) (pos 2 * pos x)) ⟩
         succℤ (UU (pos 6 + (pos 2 + pos 2 * pos x)))                     ＝⟨ ap (λ z → succℤ (UU z)) (ℤ+-assoc (pos 4) (pos 2) (pos 2 + pos 2 * pos x)) ⟩
         succℤ (UU (pos 4 + (pos 2 + (pos 2 + pos 2 * pos x))))           ＝⟨ ap (λ z → succℤ (UU z)) (ℤ+-assoc (pos 2) (pos 2) (pos 2 + (pos 2 + (pos 2 * pos x)))) ⟩
         succℤ (UU (pos 2 + (pos 2 + (pos 2 + (pos 2 + pos 2 * pos x))))) ＝⟨ UU-growth (pos 2 + (pos 2 + (pos 2 + (pos 2 + pos 2 * pos x)))) ⟩
         UU (succℤ (succℤ (succℤ (succℤ (pos 2 + (pos 2 + (pos 2 + (pos 2 + pos 2 * pos x)))))))) ∎
  second : UU (succℤ (succℤ (succℤ (succℤ (pos 2 + (pos 2 + (pos 2 + (pos 2 + pos 2 * pos x)))))))) ≤ℤ succℤ (succℤ (succℤ (pos (succ ((x /2) /2)) +pos ((x /2) /2))))
  second = transport₂ _≤ℤ_ I II (ℤ≤-adding' (UU (succℤ (succℤ (succℤ (succℤ (pos 2 * pos x)))))) (succℤ (succℤ (pos ((x /2) /2) + pos ((x /2) /2)))) (pos 2) l₂)
   where
    I : UU (succℤ (succℤ (succℤ (succℤ (pos 2 * pos x))))) + pos 2 ＝ UU (succℤ (succℤ (succℤ (succℤ (pos 2 + (pos 2 + (pos 2 + (pos 2 + pos 2 * pos x))))))))
    I = UU (succℤ (succℤ (succℤ (succℤ (pos 2 * pos x))))) + pos 2 ＝⟨ ℤ+-comm (UU (succℤ (succℤ (succℤ (succℤ (pos 2 * pos x)))))) (pos 2) ⟩
        pos 2 + UU (succℤ (succℤ (succℤ (succℤ (pos 2 * pos x))))) ＝⟨ UU-lemma₁ (succℤ (succℤ (succℤ (succℤ (pos 2 * pos x))))) ⁻¹ ⟩
        UU (pos 8 + succℤ (succℤ (succℤ (succℤ (pos 2 * pos x))))) ＝⟨ refl ⟩
        UU (pos 8 + (pos 2 * pos x + pos 4))                       ＝⟨ ap UU (ℤ+-assoc (pos 8) (pos 2 * pos x) (pos 4) ⁻¹) ⟩
        UU (pos 8 + pos 2 * pos x + pos 4)                         ＝⟨ ap (λ z → UU (z + pos 4)) (ℤ+-assoc (pos 6) (pos 2) (pos 2 * pos x)) ⟩
        UU (pos 6 + (pos 2 + pos 2 * pos x) + pos 4)               ＝⟨ ap (λ z → UU (z + pos 4)) (ℤ+-assoc (pos 4) (pos 2) (pos 2 + pos 2 * pos x)) ⟩
        UU (pos 4 + (pos 2 + (pos 2 + pos 2 * pos x)) + pos 4)     ＝⟨ ap (λ z → UU (z + pos 4)) (ℤ+-assoc (pos 2) (pos 2) (pos 2 + (pos 2 + pos 2 * pos x))) ⟩
        UU (pos 2 + (pos 2 + (pos 2 + (pos 2 + pos 2 * pos x))) + pos 4) ∎
    II : succℤ (succℤ (pos ((x /2) /2) * pos 2)) + pos 2 ＝ succℤ (pos ((x /2) /2)) + pos ((x /2) /2) + pos 3
    II = succℤ (succℤ (pos ((x /2) /2) * pos 2)) + pos 2 ＝⟨ refl ⟩
         (pos ((x /2) /2) * pos 2 + pos 2) + pos 2       ＝⟨ ℤ+-assoc (pos ((x /2) /2) * pos 2) (pos 2) (pos 2) ⟩
         pos ((x /2) /2) * pos 2 + pos 2 + pos 2         ＝⟨ ℤ+-assoc (pos ((x /2) /2) * pos 2 + pos 1) (pos 1) (pos 2) ⟩
         (pos ((x /2) /2) * pos 2 + pos 1) + pos 3       ＝⟨ ap (_+ pos 3) (ℤ-left-succ (pos (x /2 /2)) (pos (x /2 /2)) ⁻¹) ⟩
         (pos ((x /2) /2) + pos 1) + pos ((x /2) /2) + pos 3 ∎
UU-double-4 (negsucc 0) = (2 , refl) , (0 , refl)
UU-double-4 (negsucc 1) = (2 , refl) , (0 , refl)
UU-double-4 (negsucc 2) = (1 , refl) , (1 , refl)
UU-double-4 (negsucc 3) = (1 , refl) , (1 , refl)
UU-double-4 (negsucc (succ (succ (succ (succ x))))) with UU-double-4 (negsucc x)
... | l₁ , l₂ = first , second
 where
  first : predℤ (negsucc (succ ((x /2) /2)) + negsucc ((x /2) /2)) ≤ℤ UU (succℤ (succℤ (succℤ (succℤ (negsucc 1 + (negsucc 1 + (negsucc 1 + (negsucc 1 + pos 2 * negsucc x))))))))
  first = transport₂ _≤ℤ_ I II (ℤ≤-adding' (UU (negsucc x) * pos 2) (UU (pos 2 * negsucc x + pos 4)) (negsucc 1) l₁)
   where
    I : UU (negsucc x) * pos 2 - pos 2 ＝ UU (negsucc x - pos 4) * pos 2
    I = UU (negsucc x) * pos 2 - pos 2             ＝⟨ refl ⟩
        UU (negsucc x) * pos 2 + (- pos 1) * pos 2 ＝⟨ distributivity-mult-over-ℤ (UU (negsucc x)) (- pos 1) (pos 2) ⁻¹ ⟩
        (UU (negsucc x) - pos 1) * pos 2           ＝⟨ refl ⟩
        UU (negsucc x - pos 4) * pos 2             ∎
    II : UU (pos 2 * negsucc x + pos 4) + negsucc 1 ＝ UU (negsucc 1 + (negsucc 1 + (negsucc 1 + (negsucc 1 + pos 2 * negsucc x))) + pos 4)
    II = UU (pos 2 * negsucc x + pos 4) + negsucc 1                             ＝⟨ ℤ+-comm (UU (pos 2 * negsucc x + pos 4)) (negsucc 1) ⟩
         negsucc 1 + UU (pos 2 * negsucc x + pos 4)                             ＝⟨ UU-neg-lem (pos 2 * negsucc x + pos 4) ⁻¹ ⟩
         UU (negsucc 7 + (pos 2 * negsucc x + pos 4))                           ＝⟨ ap UU (ℤ+-assoc (negsucc 7) (pos 2 * negsucc x) (pos 4) ⁻¹) ⟩
         UU (negsucc 7 + pos 2 * negsucc x + pos 4)                             ＝⟨ ap (λ z → UU (z + pos 4)) (ℤ+-assoc (negsucc 5) (negsucc 1) (pos 2 * negsucc x)) ⟩
         UU (negsucc 5 + (negsucc 1 + pos 2 * negsucc x) + pos 4)               ＝⟨ ap (λ z → UU (z + pos 4)) (ℤ+-assoc (negsucc 3) (negsucc 1) (negsucc 1 + pos 2 * negsucc x)) ⟩
         UU (negsucc 3 + (negsucc 1 + (negsucc 1 + pos 2 * negsucc x)) + pos 4) ＝⟨ ap (λ z → UU (z + pos 4)) (ℤ+-assoc (negsucc 1) (negsucc 1) (negsucc 1 + (negsucc 1 + pos 2 * negsucc x))) ⟩
         UU (negsucc 1 + (negsucc 1 + (negsucc 1 + (negsucc 1 + pos 2 * negsucc x))) + pos 4) ∎
  second : UU (pos 2 * (negsucc x - pos 4) + pos 4) ≤ℤ UU (negsucc x - pos 4) * pos 2 + pos 2
  second = transport₂ _≤ℤ_ I II (ℤ≤-adding' (UU (pos 2 * negsucc x + pos 4)) (UU (negsucc x) * pos 2 + pos 2) (negsucc 1) l₂)
   where
    I : UU (pos 2 * negsucc x + pos 4) + negsucc 1 ＝ UU (pos 2 * (negsucc x - pos 4) + pos 4)
    I = UU (pos 2 * negsucc x + pos 4) + negsucc 1           ＝⟨ ℤ+-comm (UU (pos 2 * negsucc x + pos 4)) (negsucc 1) ⟩
        negsucc 1 + UU (pos 2 * negsucc x + pos 4)           ＝⟨ UU-neg-lem (pos 2 * negsucc x + pos 4) ⁻¹ ⟩
        UU (negsucc 7 + (pos 2 * negsucc x + pos 4))         ＝⟨ refl ⟩
        UU (pos 2 * negsucc 3 + (pos 2 * negsucc x + pos 4)) ＝⟨ ap UU (ℤ+-assoc (pos 2 * negsucc 3) (pos 2 * negsucc x) (pos 4) ⁻¹) ⟩
        UU (pos 2 * negsucc 3 + pos 2 * negsucc x + pos 4)   ＝⟨ ap (λ z → UU (z + pos 4)) (distributivity-mult-over-ℤ' (negsucc 3) (negsucc x) (pos 2) ⁻¹) ⟩
        UU (pos 2 * (negsucc 3 + negsucc x) + pos 4)         ＝⟨ ap (λ z → UU (pos 2 * z + pos 4)) (ℤ+-comm (negsucc 3) (negsucc x)) ⟩
        UU (pos 2 * (negsucc x - pos 4) + pos 4)             ∎
    II : UU (negsucc x) * pos 2 + pos 2 + negsucc 1 ＝ UU (negsucc x - pos 4) * pos 2 + pos 2
    II = UU (negsucc x) * pos 2 + pos 2 - pos 2             ＝⟨ ℤ+-assoc (UU (negsucc x) * pos 2) (pos 2) (- pos 2) ⟩
         UU (negsucc x) * pos 2 + (pos 2 + (- pos 2))       ＝⟨ ap (UU (negsucc x) * pos 2 +_) (ℤ+-comm (pos 2) (- pos 2)) ⟩
         UU (negsucc x) * pos 2 + ((- pos 2) + pos 2)       ＝⟨ ℤ+-assoc (UU (negsucc x) * pos 2) (- pos 2) (pos 2) ⁻¹ ⟩
         UU (negsucc x) * pos 2 - pos 2 + pos 2             ＝⟨ ap (_+ pos 2) (distributivity-mult-over-ℤ (UU (negsucc x)) (- pos 1) (pos 2) ⁻¹) ⟩
         (UU (negsucc x) - pos 1) * pos 2 + pos 2           ＝⟨ refl ⟩
         UU (negsucc x - pos 4) * pos 2 + pos 2             ∎

UU-double-1 : (z : ℤ) → UU (pos 2 * z + pos 1) below UU z
UU-double-1 z with UU-mod-behaviour-1 (pos 2 * z)
... | inl e = transport (_below (UU z)) (e ⁻¹) (UU-double-0 z)
... | inr e = transport (_below (UU z)) ((e ∙ UU-growth (pos 2 * z)) ⁻¹) (UU-double-4 z)

UU-double-2 : (z : ℤ) → UU (pos 2 * z + pos 2) below UU z
UU-double-2 z with UU-mod-behaviour-2 (pos 2 * z)
... | inl e = transport (_below (UU z)) (e ⁻¹) (UU-double-0 z) 
... | inr e = transport (_below (UU z)) ((e ∙ UU-growth (pos 2 * z)) ⁻¹) (UU-double-4 z)

UU-double-3 : (z : ℤ) → UU (pos 2 * z + pos 3) below UU z
UU-double-3 z with UU-mod-behaviour-3 (pos 2 * z)
... | inl e = transport (_below (UU z)) (e ⁻¹) (UU-double-0 z)
... | inr e = transport (_below (UU z)) ((e ∙ UU-growth (pos 2 * z)) ⁻¹) (UU-double-4 z)

below-upRight : ((x , b) (y , b) : 𝕋) → (n : ℤ) → upRight (upRight (x (succℤ n) + y (succℤ n))) below upRight (upRight (x n + y n))
below-upRight (x , b) (y , b') n with below-upRight-lem₂ (x , b) (y , b') n
... | inl case₁
 = transport₂ _below_ (below-upRight-lem₁ (pos 2 * (x n + y n)) ⁻¹ ∙ ap (λ z → upRight (upRight z)) (case₁ ⁻¹)) (below-upRight-lem₁ (x n + y n) ⁻¹) (UU-double-0 (x n + y n))
... | inr (inl case₂)
 = transport₂ _below_ (below-upRight-lem₁ (pos 2 * (x n + y n) + pos 1) ⁻¹ ∙ ap (λ z → upRight (upRight z)) (case₂ ⁻¹)) (below-upRight-lem₁ (x n + y n) ⁻¹) (UU-double-1 (x n + y n))
... | inr (inr (inl case₃))
 = transport₂ _below_ (below-upRight-lem₁ (pos 2 * (x n + y n) + pos 2) ⁻¹ ∙ ap (λ z → upRight (upRight z)) (case₃ ⁻¹)) (below-upRight-lem₁ (x n + y n) ⁻¹) (UU-double-2 (x n + y n))
... | inr (inr (inr (inl case₄)))
 = transport₂ _below_ (below-upRight-lem₁ (pos 2 * (x n + y n) + pos 3) ⁻¹ ∙ ap (λ z → upRight (upRight z)) (case₄ ⁻¹)) (below-upRight-lem₁ (x n + y n) ⁻¹) (UU-double-3 (x n + y n))
... | inr (inr (inr (inr case₅)))
 = transport₂ _below_ (below-upRight-lem₁ (pos 2 * (x n + y n) + pos 4) ⁻¹ ∙ ap (λ z → upRight (upRight z)) (case₅ ⁻¹)) (below-upRight-lem₁ (x n + y n) ⁻¹) (UU-double-4 (x n + y n))

```
