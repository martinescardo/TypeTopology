\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Integers.Type
open import Integers.Multiplication
open import Integers.Order
open import Integers.Parity
open import Rationals.Fractions hiding (_≈_)
open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import Rationals.Type
open import Naturals.Division
open import Naturals.Exponents
open import Naturals.HCF
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.Order
open import Naturals.Parity
open import Naturals.Properties
open import Notation.Order
open import UF.Base hiding (_≈_)
open import UF.Miscelanea
open import UF.Subsingletons
open import TypeTopology.DiscreteAndSeparated
open import TypeTopology.SigmaDiscreteAndTotallySeparated


module Dyadics.Rationals where

ℤ[1/2]-cond : (z : ℤ) (n : ℕ) → 𝓤₀ ̇
ℤ[1/2]-cond z n = (n ＝ 0) ∔ (n > 0 × ℤodd z)

ℤ[1/2]-cond-is-prop : (z : ℤ) (n : ℕ) → is-prop (ℤ[1/2]-cond z n)
ℤ[1/2]-cond-is-prop z n = +-is-prop ℕ-is-set (×-is-prop (<-is-prop-valued 0 n) (ℤodd-is-prop z)) I
 where
  I : n ＝ 0 → ¬ (0 < n × ℤodd z)
  I n＝0 (0<n , odd-z) = not-less-than-itself 0 (transport (0 <_) n＝0 0<n)

ℤ[1/2]-cond-is-discrete : ((z , n) : ℤ × ℕ) → is-discrete (ℤ[1/2]-cond z n)
ℤ[1/2]-cond-is-discrete (z , n) = +-is-discrete (λ x y → inl (ℕ-is-set x y))
                                   (×-is-discrete (λ x y → inl (<-is-prop-valued 0 n x y))
                                                  (λ x y → inl (ℤodd-is-prop z x y)))
ℤ[1/2] : 𝓤₀ ̇
ℤ[1/2] = Σ (z , n) ꞉ ℤ × ℕ , ℤ[1/2]-cond z n

ℤ[1/2]-is-discrete : is-discrete ℤ[1/2]
ℤ[1/2]-is-discrete = Σ-is-discrete (×-is-discrete ℤ-is-discrete ℕ-is-discrete) ℤ[1/2]-cond-is-discrete

ℤ[1/2]-is-set : is-set ℤ[1/2]
ℤ[1/2]-is-set = discrete-types-are-sets ℤ[1/2]-is-discrete
{-
normalise-pos-lemma'' : (z : ℤ) (n : ℕ) → ℤeven z → (0<n : 0 < n) → Σ k ꞉ ℤ , z ＝ pos 2 * k → ℤ[1/2]
normalise-pos-lemma'' z 0        ez 0<n (k , e) = 𝟘-elim 0<n
normalise-pos-lemma'' z (succ n) ez 0<n (k , e) = {!!}

normalise-pos-lemma' : (z : ℤ) (n : ℕ) → ℤeven z ∔ ℤodd z → (0<n : 0 < n) → ℤ[1/2]
normalise-pos-lemma' z n (inr oz) 0<n = (z , n) , inr (0<n , oz)
normalise-pos-lemma' z n (inl ez) 0<n = normalise-pos-lemma'' z n ez 0<n (ℤeven-is-multiple-of-two z ez)
-}

normalise-pos-lemma : (z : ℤ) (n : ℕ) → ℤ[1/2]
normalise-pos-lemma z 0        = (z , 0) , (inl refl)
normalise-pos-lemma z (succ n) =
 Cases (ℤeven-or-odd z) (λ ez → (λ (k , e) → normalise-pos-lemma k n) (ℤeven-is-multiple-of-two z ez))
                        (λ oz → (z , succ n) , inr (⋆ , oz))

normalise-pos : ℤ × ℕ → ℤ[1/2]
normalise-pos (z , n) = normalise-pos-lemma z n

normalise-neg-lemma : (z : ℤ) (n : ℕ) → ℤ[1/2]
normalise-neg-lemma z 0        = (z * pos 2 , 0) , (inl refl)
normalise-neg-lemma z (succ n) = normalise-neg-lemma (z * pos 2) n

normalise-neg : ℤ × ℕ → ℤ[1/2]
normalise-neg (z , n) = normalise-neg-lemma z n

normalise : ℤ × ℤ → ℤ[1/2]
normalise (z , pos n)     = normalise-pos (z , n)
normalise (z , negsucc n) = normalise-neg (z , n)

0ℤ[1/2] : ℤ[1/2]
0ℤ[1/2] = (pos 0 , 0) , (inl refl)

1ℤ[1/2] : ℤ[1/2]
1ℤ[1/2] = (pos 1 , 0) , (inl refl)

_≈'_ : (x y : ℤ × ℕ) → 𝓤₀ ̇
(x , n) ≈' (y , m) = x * pos (2^ m) ＝ y * pos (2^ n)

_≈_ : (x y : ℤ[1/2]) → 𝓤₀ ̇
(x , _) ≈ (y , _) = x ≈' y

ℤ[1/2]-lt-lemma : (x : ℤ) → (n : ℕ) → ℤodd x → is-in-lowest-terms (x , pred (2^ (succ n)))
ℤ[1/2]-lt-lemma x n ox = (1-divides-all (abs x) , 1-divides-all (succ (pred (2^ (succ n))))) , I
 where
  I : (d : ℕ) → is-common-divisor d (abs x) (succ (pred (2^ (succ n)))) → d ∣ 1
  I d icd-d = III II
   where
    II : is-common-divisor d (abs x) (2^ (succ n))
    II = transport (λ - → is-common-divisor d (abs x) -) (succ-pred' (2^ (succ n)) (exponents-not-zero (succ n))) icd-d
    III : is-common-divisor d (abs x) (2^ (succ n)) → d ∣ 1
    III (d|x , d|2^sn) = odd-power-of-two-coprime d (abs x) (succ n) ox d|x d|2^sn

ℤ[1/2]-to-ℚ : ℤ[1/2] → ℚ
ℤ[1/2]-to-ℚ ((x , n)      , inl n＝0)       = (x , 0) , (denom-zero-lt x)
ℤ[1/2]-to-ℚ ((x , 0)      , inr (0<n , ox)) = 𝟘-elim 0<n
ℤ[1/2]-to-ℚ ((x , succ n) , inr (0<n , ox)) = (x , pred (2^ (succ n))) , (ℤ[1/2]-lt-lemma x n ox)

≈-to-＝-lemma-sub-proof₁ : ((x , m) (y , n) : ℤ × ℕ)
              → (x , m) ≈' (y , n)
              → m ＝ 0
              → n ＝ 0
              → (x , m) ＝ (y , n)
≈-to-＝-lemma-sub-proof₁ (x , m) (y , n) e m＝0 n＝0 = to-×-＝ I (m＝0 ∙ n＝0 ⁻¹)
 where
  I : x ＝ y
  I = x              ＝⟨ refl                                  ⟩
      x * pos (2^ 0) ＝⟨ ap (λ z → x * (pos (2^ z))) (n＝0 ⁻¹) ⟩
      x * pos (2^ n) ＝⟨ e                                     ⟩
      y * pos (2^ m) ＝⟨ ap (λ z → y * (pos (2^ z))) m＝0      ⟩
      y * pos (2^ 0) ＝⟨ refl                                  ⟩
      y              ∎

≈-to-＝-lemma-sub-proof₂ : ((x , m) (y , n) : ℤ × ℕ) → (x , m) ≈' (y , n) → m ＝ 0 → ¬ (n > 0 × ℤodd y)
≈-to-＝-lemma-sub-proof₂ (x , m) (y , 0)      e m＝0 (n>0 , oy) = 𝟘-elim n>0
≈-to-＝-lemma-sub-proof₂ (x , m) (y , succ n) e m＝0 (n>0 , oy) = ℤodd-not-even y oy (transport ℤeven I II)
 where
  I : x * pos (2^ (succ n)) ＝ y
  I = x * pos (2^ (succ n)) ＝⟨ e ⟩
      y * pos (2^ m)        ＝⟨ ap (λ - → y * pos (2^ -)) m＝0 ⟩
      y * pos (2^ 0)        ＝⟨ refl ⟩
      y ∎
  II : ℤeven (x * pos (2^ (succ n)))
  II = ℤtimes-even-is-even' x (pos (2^ (succ n))) (2-exponents-even n)

≈-to-＝-cancellation-lemma : (x y : ℤ) (n : ℕ) → (x , 1) ≈' (y , succ (succ n)) → (x , 0) ≈' (y , succ n)
≈-to-＝-cancellation-lemma x y n e = ℤ-mult-right-cancellable (x * pos (2^ (succ n))) (y * pos (2^ 0)) (pos 2) id I
 where
  I : x * pos (2^ (succ n)) * pos 2 ＝ y * pos (2^ 0) * pos 2
  I = x * pos (2^ (succ n)) * pos 2   ＝⟨ ℤ*-assoc x (pos (2^ (succ n))) (pos 2)                       ⟩
      x * (pos (2^ (succ n)) * pos 2) ＝⟨ ap (x *_) (pos-multiplication-equiv-to-ℕ (2^ (succ n)) 2)    ⟩
      x * pos (2^ (succ n) ℕ* 2)      ＝⟨ ap (λ - → x * pos -) (mult-commutativity (2^ (succ n)) 2)    ⟩
      x * pos (2^ (succ (succ n)))    ＝⟨ e                                                            ⟩
      y * pos (2^ 1)                  ＝⟨ ap (y *_) (pos-multiplication-equiv-to-ℕ 2 1) ⁻¹             ⟩
      y * (pos 2 * pos 1)             ＝⟨ refl                                                         ⟩
      y * pos (2^ 0) * pos 2          ∎

≈-to-＝-lemma-sub-proof₃ : (x : ℤ) (m : ℕ) (y : ℤ) (n : ℕ) → (x , m) ≈' (y , n) → m > 0 × ℤodd x → n > 0 × ℤodd y → (x , m) ＝ (y , n)
≈-to-＝-lemma-sub-proof₃ x  m               y  0               e (m>0 , ox) (n>0 , on) = 𝟘-elim n>0
≈-to-＝-lemma-sub-proof₃ x  0               y  (succ n)        e (m>0 , ox) (n>0 , on) = 𝟘-elim m>0
≈-to-＝-lemma-sub-proof₃ x  1               y  1               e (m>0 , ox) (n>0 , on) = to-×-＝ (ℤ-mult-right-cancellable x y (pos (2^ 1)) id e) refl
≈-to-＝-lemma-sub-proof₃ x  1               y  (succ (succ n)) e (m>0 , ox) (n>0 , on) = 𝟘-elim (≈-to-＝-lemma-sub-proof₂ (x , 0) (y , succ n) (≈-to-＝-cancellation-lemma x y n e) refl (⋆ , on))
≈-to-＝-lemma-sub-proof₃ x  (succ (succ m)) y  1               e (m>0 , ox) (n>0 , on) = 𝟘-elim (≈-to-＝-lemma-sub-proof₂ (y , 0) (x , succ m) (≈-to-＝-cancellation-lemma y x m (e ⁻¹)) refl (⋆ , ox))
≈-to-＝-lemma-sub-proof₃ x  (succ (succ m)) y  (succ (succ n)) e (m>0 , ox) (n>0 , on) = III (from-×-＝' (≈-to-＝-lemma-sub-proof₃ x (succ m) y (succ n) II (⋆ , ox) (⋆ , on)))
 where
  I : x * pos (2^ (succ n)) * pos 2 ＝ y * pos (2^ (succ m)) * pos 2
  I = x * pos (2^ (succ n)) * pos 2   ＝⟨ ℤ*-assoc x (pos (2^ (succ n))) (pos 2)                       ⟩
      x * (pos (2^ (succ n)) * pos 2) ＝⟨ ap (x *_) (pos-multiplication-equiv-to-ℕ (2^ (succ n)) 2)    ⟩
      x * pos (2^ (succ n) ℕ* 2)      ＝⟨ ap (λ - → x * pos -) (mult-commutativity (2^ (succ n)) 2)    ⟩
      x * pos (2^ (succ (succ n)))    ＝⟨ e                                                            ⟩
      y * pos (2^ (succ (succ m)))    ＝⟨ ap (λ - → y * pos -) (mult-commutativity 2 (2^ (succ m)))    ⟩
      y * pos (2^ (succ m) ℕ* 2)      ＝⟨ ap (y *_) (pos-multiplication-equiv-to-ℕ (2^ (succ m)) 2 ⁻¹) ⟩
      y * (pos (2^ (succ m)) * pos 2) ＝⟨ ℤ*-assoc y (pos (2^ (succ m))) (pos 2) ⁻¹ ⟩
      y * pos (2^ (succ m)) * pos 2   ∎

  II : x * pos (2^ (succ n)) ＝ y * pos (2^ (succ m))
  II = ℤ-mult-right-cancellable (x * pos (2^ (succ n))) (y * pos (2^ (succ m))) (pos 2) id I

  III : (x ＝ y) × (succ m ＝ succ n) → x , succ (succ m) ＝ y , succ (succ n)
  III (x＝y , m＝n) = to-×-＝ x＝y (ap succ m＝n)

≈-to-＝-lemma-sub-proof₄ : ((x , m) (y , n) : ℤ × ℕ) → (x , m) ≈' (y , n) → m > 0 × ℤodd x → n > 0 × ℤodd y → (x , m) ＝ (y , n)
≈-to-＝-lemma-sub-proof₄ (x , m) (y , n) e p q = ≈-to-＝-lemma-sub-proof₃ x m y n e p q

≈-to-＝-lemma : ((x , m) (y , n) : ℤ × ℕ)
              → (x , m) ≈' (y , n)
              → ℤ[1/2]-cond x m
              → ℤ[1/2]-cond y n
              → (x , m) ＝ (y , n)
≈-to-＝-lemma x y e (inl p) (inl q) = ≈-to-＝-lemma-sub-proof₁ x y e p q
≈-to-＝-lemma x y e (inl p) (inr q) = 𝟘-elim (≈-to-＝-lemma-sub-proof₂ x y e p q)
≈-to-＝-lemma x y e (inr p) (inl q) = 𝟘-elim (≈-to-＝-lemma-sub-proof₂ y x (e ⁻¹) q p)
≈-to-＝-lemma x y e (inr p) (inr q) = ≈-to-＝-lemma-sub-proof₄ x y e p q

≈-to-＝ : (x y : ℤ[1/2]) → x ≈ y → x ＝ y
≈-to-＝ ((x , n) , p) ((y , m) , q) eq =
 to-subtype-＝ (λ (x , n) → ℤ[1/2]-cond-is-prop x n) (≈-to-＝-lemma (x , n) (y , m) eq p q)

ℤ[1/2]-to-normalise-pos : (((x , n) , e) : ℤ[1/2]) → ((x , n) , e) ＝ normalise-pos (x , n)
ℤ[1/2]-to-normalise-pos ((x , 0)        , inl n＝0)       = to-subtype-＝ (λ (x , n) → ℤ[1/2]-cond-is-prop x n) refl
ℤ[1/2]-to-normalise-pos ((x , (succ n)) , inl n＝0)       = 𝟘-elim (positive-not-zero n n＝0)
ℤ[1/2]-to-normalise-pos ((x , 0)        , inr (0<0 , oz)) = 𝟘-elim (not-less-than-itself 0 0<0)
ℤ[1/2]-to-normalise-pos ((x , succ n)   , inr (0<n , oz)) =
 ap (λ zzz → dep-cases
     (λ ez → normalise-pos-lemma (pr₁ (ℤeven-is-multiple-of-two x ez)) n)
     (λ oz₁ → (x , succ n) , inr (⋆ , oz₁)) zzz)
      (ℤeven-or-odd-is-prop x (inr oz) (ℤeven-or-odd x))

\end{code}
