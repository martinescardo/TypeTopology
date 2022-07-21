Martin Escardo and Paulo Oliva 2021

Non-spartan types in MLTT, which are definable from spartan MLTT, but we include here for some work on game theory with Paulo Oliva.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module MLTT.NonSpartanMLTTTypes where

open import MLTT.Spartan

data Maybe {𝓤 : Universe} (A : 𝓤 ̇ ) : 𝓤 ̇ where
 Nothing : Maybe A
 Just    : A → Maybe A

Just-is-not-Nothing : {A : 𝓤 ̇ } {a : A} → Just a ≢ Nothing
Just-is-not-Nothing ()

Nothing-is-isolated : {A : 𝓤 ̇ } (x : Maybe A) → decidable (Nothing ＝ x)
Nothing-is-isolated Nothing  = inl refl
Nothing-is-isolated (Just a) = inr (λ (p : Nothing ＝ Just a) → Just-is-not-Nothing (p ⁻¹))

Nothing-is-isolated' : {A : 𝓤 ̇ } (x : Maybe A) → decidable (x ＝ Nothing)
Nothing-is-isolated' Nothing  = inl refl
Nothing-is-isolated' (Just a) = inr Just-is-not-Nothing

open import UF.Miscelanea
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons

Nothing-is-h-isolated : {A : 𝓤 ̇ } (x : Maybe A) → is-prop (Nothing ＝ x)
Nothing-is-h-isolated x = isolated-is-h-isolated Nothing Nothing-is-isolated

Nothing-is-h-isolated' : {A : 𝓤 ̇ } (x : Maybe A) → is-prop (x ＝ Nothing)
Nothing-is-h-isolated' x = equiv-to-prop ＝-flip (Nothing-is-h-isolated x)

data Bool : 𝓤₀ ̇ where
 true false : Bool

true-is-not-false : true ≢ false
true-is-not-false ()

if_then_else_ : {X : 𝓤 ̇ } → Bool → X → X → X
if true  then x else y = x
if false then x else y = y

Bool-induction : (A : Bool → 𝓤 ̇ ) → A true → A false → (b : Bool) → A b
Bool-induction A x y true  = x
Bool-induction A x y false = y

Bool-equality-cases : {A : 𝓤 ̇ } (x : Bool) → (x ＝ true → A) → (x ＝ false → A) → A
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
||-left-intro {true} y e = refl

||-right-intro : ({x} y : Bool) → y ＝ true → x || y ＝ true
||-right-intro {true}  true e = refl
||-right-intro {false} true e = refl

||-gives-+ : {x y : Bool} → x || y ＝ true → (x ＝ true) + (y ＝ true)
||-gives-+ {true}  {y}    _ = inl refl
||-gives-+ {false} {true} _ = inr refl

&&-gives-× : {x y : Bool} → x && y ＝ true → (x ＝ true) × (y ＝ true)
&&-gives-× {true} {true} _ = refl , refl

&&-intro : {x y : Bool} → x ＝ true → y ＝ true → x && y ＝ true
&&-intro {true} {true} refl refl = refl

infixl 10 _||_
infixl 20 _&&_

record Eq {𝓤} (X : 𝓤 ̇ ) : 𝓤 ̇  where
  field
    _==_    : X → X → Bool
    ==-refl : (x : X) → (x == x) ＝ true

open Eq {{...}} public

data List {𝓤 : Universe} (X : 𝓤 ̇ ) : 𝓤 ̇ where
 []  : List X
 _∷_ : X → List X → List X

infixr 3 _∷_

_++_ : {𝓤 : Universe} {X : 𝓤 ̇ } → List X → List X → List X
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

empty : {𝓤 : Universe} {X : 𝓤 ̇ } → List X → Bool
empty []       = true
empty (x ∷ xs) = false

map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
    → (X → Y)
    → List X → List Y
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

module list-util
          {𝓤 : Universe}
          {X : 𝓤 ̇ }
          {{_ : Eq X}}
        where

  _is-in_ : X → List X → Bool
  x is-in []       = false
  x is-in (y ∷ ys) = (x == y) || (x is-in ys)

  insert : X → List X → List X
  insert x xs = x ∷ xs

  _contained-in_ : List X → List X → Bool
  []       contained-in ys = true
  (x ∷ xs) contained-in ys = (x is-in ys) && (xs contained-in ys)

  contained-lemma₀ : (x z : X) (xs ys : List X)
                   → ys contained-in (x ∷ xs) ＝ true
                   → ys contained-in (x ∷ z ∷ xs) ＝ true
  contained-lemma₀ x z xs []       e = e
  contained-lemma₀ x z xs (y ∷ ys) e = γ
   where
    IH : ys contained-in (x ∷ xs) ＝ true → ys contained-in (x ∷ z ∷ xs) ＝ true
    IH = contained-lemma₀ x z xs ys

    e₁ : (y == x) || (y is-in xs) ＝ true
    e₁ = pr₁ (&&-gives-× e)

    e₂ : ys contained-in (x ∷ xs) ＝ true
    e₂ = pr₂ (&&-gives-× e)

    a : (y == x) || ((y == z) || (y is-in xs)) ＝ true
    a = Cases (||-gives-+ e₁)
         (λ (e : (y == x) ＝ true)   → ||-left-intro ((y == z) || (y is-in xs)) e)
         (λ (e : y is-in xs ＝ true) → ||-right-intro {y == x} ((y == z) || (y is-in xs)) (||-right-intro (y is-in xs) e))

    b : ys contained-in (x ∷ z ∷ xs) ＝ true
    b = IH e₂

    γ : ((y == x) || ((y == z) || (y is-in xs))) && (ys contained-in (x ∷ z ∷ xs)) ＝ true
    γ = &&-intro a b

  contained-lemma₁ : (x : X) (ys : List X)
                   → ys contained-in (x ∷ ys) ＝ true
  contained-lemma₁ x []       = refl
  contained-lemma₁ x (y ∷ ys) = γ
   where
    IH : ys contained-in (x ∷ ys) ＝ true
    IH = contained-lemma₁ x ys

    a : y == x || (y == y || (y is-in ys)) ＝ true
    a = ||-right-intro {y == x} ((y == y) || (y is-in ys)) (||-left-intro (y is-in ys) (==-refl y))

    b : ys contained-in (x ∷ y ∷ ys) ＝ true
    b = contained-lemma₀ x y ys ys IH

    γ : (y == x || (y == y || (y is-in ys))) && (ys contained-in (x ∷ y ∷ ys)) ＝ true
    γ = &&-intro a b

  some-contained : List (List X) → List X → Bool
  some-contained []         ys = false
  some-contained (xs ∷ xss) ys = xs contained-in ys || some-contained xss ys

  remove-first : X → List X → List X
  remove-first x []       = []
  remove-first x (y ∷ ys) = if x == y then ys else (y ∷ remove-first x ys)

  remove-all : X → List X → List X
  remove-all x []       = []
  remove-all x (y ∷ ys) = if x == y then remove-all x ys else (y ∷ remove-all x ys)

  _minus_ : List X → List X → List X
  xs minus []       = xs
  xs minus (y ∷ ys) = (remove-all y xs) minus ys

data Fin : ℕ → 𝓤₀  ̇  where
 𝟎   : {n : ℕ} → Fin (succ n)
 suc : {n : ℕ} → Fin n → Fin (succ n)

pattern 𝟏 = suc 𝟎
pattern 𝟐 = suc 𝟏
pattern 𝟑 = suc 𝟐
pattern 𝟒 = suc 𝟑
pattern 𝟓 = suc 𝟒
pattern 𝟔 = suc 𝟓
pattern 𝟕 = suc 𝟔
pattern 𝟖 = suc 𝟕
pattern 𝟗 = suc 𝟖

list-Fin : (n : ℕ) → List (Fin n)
list-Fin zero     = []
list-Fin (succ n) = 𝟎 ∷ map suc (list-Fin n)

Fin-== : {n : ℕ} → Fin n → Fin n → Bool
Fin-== {succ n} (suc x) (suc y) = Fin-== {n} x y
Fin-== {succ n} (suc x) 𝟎       = false
Fin-== {succ n} 𝟎       (suc y) = false
Fin-== {succ n} 𝟎       𝟎       = true

Fin-refl : {n : ℕ} (x : Fin n) → (Fin-== x x) ＝ true
Fin-refl {succ n} (suc x) = Fin-refl {n} x
Fin-refl {succ n} 𝟎       = refl

module _ {n : ℕ} where
 instance
  eqFin : Eq (Fin n)
  _==_    {{eqFin}} = Fin-== {n}
  ==-refl {{eqFin}} = Fin-refl {n}

\end{code}
