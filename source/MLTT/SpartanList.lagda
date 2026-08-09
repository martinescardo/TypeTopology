Martin Escardo, 15th December 2019, 9th Feb 2021.

Vectors with a different type for each entry (vec), usual vectors
(Vec) and lists (List) in our spartan MLTT.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.SpartanList where

open import MLTT.Spartan
open import Fin.Type

vec : (n : ℕ) → (Fin n → 𝓤 ̇ ) → 𝓤 ̇
vec 0        X = 𝟙
vec (succ n) X = X 𝟎 × vec n (X ∘ suc)

Vec : 𝓤 ̇ → ℕ → 𝓤 ̇
Vec X n = vec n (λ _ → X)

List : 𝓤 ̇ → 𝓤 ̇
List X = Σ n ꞉ ℕ , Vec X n

length : {X : 𝓤 ̇ } → List X → ℕ
length = pr₁

pattern [] = (0 , ⋆)

_∷_ : {X : 𝓤 ̇ } → X → List X → List X
x ∷ (n , s) = succ n , x , s

[_] : {X : 𝓤 ̇ } → X → List X
[ x ] = x ∷ []

\end{code}

Our list encoding satisfies Martin-Löf's rules for lists:

\begin{code}

List-induction : {X : 𝓤 ̇ } (P : List X → 𝓥 ̇ )
               → P []
               → ((x : X) (xs : List X) → P xs → P (x ∷ xs))
               → (xs : List X) → P xs
List-induction {𝓤} {𝓥} {X} P p f xs = h (length xs) (pr₂ xs)
 where
  h : (n : ℕ) → (v : Vec X n) → P (n , v)
  h 0 _              = p
  h (succ n) (x , s) = f x (n , s) (h n s)

\end{code}

With the computation rules holding definitionally, as required:

\begin{code}

List-induction-[] : {X : 𝓤 ̇ } (P : List X → 𝓥 ̇ )
               → (p : P [])
               → (f : (x : X) (xs : List X) → P xs → P (x ∷ xs))
               → List-induction P p f [] ＝ p
List-induction-[] {𝓤} {𝓥} {X} P p f = refl

List-induction-∷ : {X : 𝓤 ̇ } (P : List X → 𝓥 ̇ )
               → (p : P [])
               → (f : (x : X) (xs : List X) → P xs → P (x ∷ xs))
               → (x : X)
               → (xs : List X)
               → List-induction P p f (x ∷ xs) ＝ f x xs (List-induction P p f xs)
List-induction-∷ {𝓤} {𝓥} {X} P p f x xs = refl

pattern ⟨⟩       = ⋆
pattern _::_ x xs = (x , xs)

hd : {n : ℕ} {X : Fin (succ n) → 𝓤 ̇ } → vec (succ n) X → X 𝟎
hd (x :: xs) = x

tl : {n : ℕ} {X : Fin (succ n) → 𝓤 ̇ } → vec (succ n) X → vec n (X ∘ suc)
tl (x :: xs) = xs

index : (n : ℕ) {X : Fin n → 𝓤 ̇ } → vec n X → (i : Fin n) → X i
index 0        xs        i       = 𝟘-elim i
index (succ n) (x :: xs) 𝟎       = x
index (succ n) (x :: xs) (suc i) = index n xs i

_!!_ : {n : ℕ} {X : 𝓤 ̇ } → Vec X n → (i : Fin n) → X
_!!_ {𝓤} {n} = index n

\end{code}

An isomorphic copy of vec n X.

\begin{code}

vec' : (n : ℕ) → (Fin n → 𝓤 ̇ ) → 𝓤 ̇
vec' n X = (i : Fin n) → X i

Vec' : ℕ → 𝓤 ̇ → 𝓤 ̇
Vec' n X = vec' n (λ _ → X)

hd' : {n : ℕ} {X : Fin (succ n) → 𝓤 ̇ } → vec' (succ n) X → X 𝟎
hd' xs = xs 𝟎

tl' : {n : ℕ} {X : Fin (succ n) → 𝓤 ̇ } → vec' (succ n) X → vec' n (X ∘ suc)
tl' xs = λ i → xs (suc i)


⟨⟩' : {X : Fin 0 → 𝓤 ̇ } → vec' 0 X
⟨⟩' = λ i → unique-from-𝟘 i


_::'_ : {n : ℕ} {X : Fin (succ n) → 𝓤 ̇ }
     → X 𝟎 → vec' n (X ∘ suc) → vec' (succ n) X
(x ::' xs) 𝟎       = x
(x ::' xs) (suc i) = xs i


xedni : (n : ℕ) {X : Fin n → 𝓤 ̇ } → ((i : Fin n) → X i) → vec n X
xedni 0        xs' = ⟨⟩
xedni (succ n) xs' = hd' xs' :: xedni n (tl' xs')


vecη : (n : ℕ) {X : Fin n → 𝓤 ̇ } → xedni n {X} ∘ index n {X} ∼ id
vecη zero     ⟨⟩       = refl
vecη (succ n) (x :: xs) = ap (x ::_) (vecη n xs)

open import UF.FunExt
open import UF.Base
open import UF.Equiv

module _ {𝓤} (fe : funext 𝓤₀ 𝓤) where

 vecε : (n : ℕ) {X : Fin n → 𝓤 ̇ } → index n {X} ∘ xedni n {X} ∼ id
 vecε 0        xs' = dfunext fe (λ i → 𝟘-elim i)
 vecε (succ n) xs' = dfunext fe h
  where
   h : (i : Fin (succ n)) → index (succ n) (xs' 𝟎 :: xedni n (tl' xs')) i ＝ xs' i
   h 𝟎       = refl
   h (suc i) = happly (vecε n (tl' xs')) i


 vec-≃ : (n : ℕ) {X : Fin n → 𝓤 ̇ } → vec n X ≃ vec' n X
 vec-≃ n {X} = qinveq (index n) (xedni n {X} , vecη n , vecε n)

\end{code}

9th Feb 2021. More operations on vectors. The stuff on
vectors should be eventually moved to another module.

\begin{code}

⟨_⟩ : {X : 𝓤 ̇ } → X → Vec X 1
⟨ x ⟩ = x :: ⟨⟩

_∔_ : ℕ → ℕ → ℕ
zero   ∔ n = n
succ m ∔ n = succ (m ∔ n)

append : {X : 𝓤 ̇ } (m n : ℕ) → Vec X m → Vec X n → Vec X (m ∔ n)
append zero     n ⟨⟩      t = t
append (succ m) n (x :: s) t = x :: append m n s t

_++_ : {X : 𝓤 ̇ } {m n : ℕ} → Vec X m → Vec X n → Vec X (m ∔ n)
_++_ = append _ _

plus-1-is-succ : (n : ℕ) → n ∔ 1 ＝ succ n
plus-1-is-succ zero     = refl
plus-1-is-succ (succ n) = ap succ (plus-1-is-succ n)

rev' : {X : 𝓤 ̇ } (n : ℕ) → Vec X n → Vec X n
rev' zero     ⟨⟩      = ⟨⟩
rev' (succ n) (x :: s) = γ
 where
  IH : Vec _ (n ∔ 1)
  IH = rev' n s ++ ⟨ x ⟩

  γ : Vec _ (succ n)
  γ = transport (Vec _) (plus-1-is-succ n) IH

rev : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → Vec X n
rev = rev' _

_+ₐ_ : ℕ → ℕ → ℕ
zero   +ₐ n = n
succ m +ₐ n = m +ₐ succ n

rev-append : {X : 𝓤 ̇ } (m n : ℕ) → Vec X m → Vec X n → Vec X (m +ₐ n)
rev-append zero     n ⟨⟩       t = t
rev-append (succ m) n (x :: s) t = rev-append m (succ n) s (x :: t)

revₐ : {X : 𝓤 ̇ } (m : ℕ) → Vec X m → Vec X (m +ₐ zero)
revₐ n s = rev-append n zero s ⟨⟩

\end{code}
