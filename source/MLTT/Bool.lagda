\begin{code}

{-# OPTIONS --safe --without-K #-} --

module MLTT.Bool where

open import MLTT.Spartan

data Bool : 𝓤₀ ̇ where
 true false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}

true-is-not-false : true ≠ false
true-is-not-false p = transport f p ⋆
 where
  f : Bool → 𝓤₀ ̇
  f true  = 𝟙
  f false = 𝟘

if_then_else_ : {X : 𝓤 ̇ } → Bool → X → X → X
if true  then x else y = x
if false then x else y = y

Bool-induction : (A : Bool → 𝓤 ̇ ) → A true → A false → (b : Bool) → A b
Bool-induction A x y true  = x
Bool-induction A x y false = y

Bool-equality-cases : {A : 𝓤 ̇ } (x : Bool)
                    → (x ＝ true → A) → (x ＝ false → A) → A
Bool-equality-cases true  f g = f refl
Bool-equality-cases false f g = g refl

not : Bool → Bool
not false = true
not true  = false

_||_ _&&_ : Bool → Bool → Bool

true  || y = true
false || y = y

true  && y = y
false && y = false

true-right-||-absorptive : (x : Bool) → x || true ＝ true
true-right-||-absorptive true  = refl
true-right-||-absorptive false = refl

||-left-intro : ({x} y : Bool) → x ＝ true → x || y ＝ true
||-left-intro {true}  y e = refl
||-left-intro {false} y e = 𝟘-elim (true-is-not-false (e ⁻¹))

||-right-intro : ({x} y : Bool) → y ＝ true → x || y ＝ true
||-right-intro {true}  true  e = refl
||-right-intro {true}  false e = refl
||-right-intro {false} true  e = refl
||-right-intro {false} false e = e

||-gives-+ : {x y : Bool} → x || y ＝ true → (x ＝ true) + (y ＝ true)
||-gives-+ {true}  {y}     e = inl refl
||-gives-+ {false} {true}  e = inr refl
||-gives-+ {false} {false} e = inl e

&&-gives-× : {x y : Bool} → x && y ＝ true → (x ＝ true) × (y ＝ true)
&&-gives-× {true}  {true}  e = refl , refl
&&-gives-× {true}  {false} e = refl , e
&&-gives-× {false} {y}     e = 𝟘-elim (true-is-not-false (e ⁻¹))

&&-intro : {x y : Bool} → x ＝ true → y ＝ true → x && y ＝ true
&&-intro {true}  {true}  p q = refl
&&-intro {true}  {false} p q = q
&&-intro {false} {y}     p q = p

infixl 10 _||_
infixl 20 _&&_

record Eq {𝓤} (X : 𝓤 ̇ ) : 𝓤 ̇ where
  field
    _==_    : X → X → Bool
    ==-refl : (x : X) → (x == x) ＝ true

open Eq {{...}} public

ℕ-== : ℕ → ℕ → Bool
ℕ-== 0        0        = true
ℕ-== 0        (succ y) = false
ℕ-== (succ x) 0        = false
ℕ-== (succ x) (succ y) = ℕ-== x y

ℕ-refl : (n : ℕ) → (ℕ-== n n) ＝ true
ℕ-refl 0        = refl
ℕ-refl (succ n) = ℕ-refl n

instance
 eqℕ : Eq ℕ
 _==_    {{eqℕ}} = ℕ-==
 ==-refl {{eqℕ}} = ℕ-refl

\end{code}
