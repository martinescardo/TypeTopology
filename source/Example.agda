open import SpartanMLTT hiding (_+_)
open import NaturalsAddition

zero-is-left-neutral : (x : ℕ) → 0 + x ≡ x
zero-is-left-neutral zero     = refl
zero-is-left-neutral (succ x) = ap succ IH
 where
  IH : 0 + x ≡ x
  IH = zero-is-left-neutral x

left-succ : (x y : ℕ) → succ x + y ≡ succ (x + y)
left-succ x zero = refl
left-succ x (succ y) = ap succ IH
 where
  IH : succ x + y ≡ succ (x + y)
  IH = left-succ x y

addition-commutative : (x y : ℕ) → x + y ≡ y + x
addition-commutative x y = induction base step x
 where
  base : 0 + y ≡ y 
  base = {!!}
  
  step : (k : ℕ) → k + y ≡ y + k → succ k + y ≡ succ (y + k)
  step k IH = conclusion
   where
    from-IH : succ (k + y) ≡ succ (y + k)
    from-IH = {!!}

    conclusion : succ k + y ≡ y + succ k
    conclusion = {!!}

  
