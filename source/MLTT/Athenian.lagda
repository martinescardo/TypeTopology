Martin Escardo and Paulo Oliva 2021

Non-spartan types in MLTT, which are definable from spartan MLTT, but we include here for some work on game theory with Paulo Oliva.

\begin{code}

{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness --auto-inline #-} -- --exact-split

module MLTT.Athenian where

open import MLTT.Spartan
open import Naturals.Properties

data Maybe {𝓤 : Universe} (A : 𝓤 ̇ ) : 𝓤 ̇ where
 Nothing : Maybe A
 Just    : A → Maybe A

{-# BUILTIN MAYBE Maybe #-}

Just-is-not-Nothing : {A : 𝓤 ̇ } {a : A} → Just a ≠ Nothing
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

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}

true-is-not-false : true ≠ false
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

data List {𝓤 : Universe} (X : 𝓤 ̇ ) : 𝓤 ̇ where
 []  : List X
 _∷_ : X → List X → List X

{-# BUILTIN LIST List #-}

infixr 3 _∷_

length : {X : 𝓤 ̇ } → List X → ℕ
length []       = 0
length (x ∷ xs) = succ (length xs)

Vector' : 𝓤 ̇ → ℕ → 𝓤 ̇
Vector' X n = (Σ xs ꞉ List X , length xs ＝ n)

_∷'_ : {X : 𝓤 ̇ } {n : ℕ} → X → Vector' X n → Vector' X (succ n)
x ∷' (xs , p) = (x ∷ xs) , ap succ p

foldr : {X : 𝓤 ̇ } {R : 𝓥 ̇ } → List X → (X → R → R) → R → R
foldr []       f r = r
foldr (x ∷ xs) f r = f x (foldr xs f r)

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

data member {X : 𝓤 ̇ } : X → List X → 𝓤 ̇  where
 in-head : {x : X}   {xs : List X} → member x (x ∷ xs)
 in-tail : {x y : X} {xs : List X} → member x xs → member x (y ∷ xs)

member-map : {X Y : Type} (f : X → Y) (x : X) (xs : List X)
           → member x xs
           → member (f x) (map f xs)
member-map f x' (_ ∷ _)  in-head     = in-head
member-map f x' (_ ∷ xs) (in-tail m) = in-tail (member-map f x' xs m)

listable : Type → Type
listable X = Σ xs ꞉ List X , ((x : X) → member x xs)

listable⁺ : Type → Type
listable⁺ X = X × listable X

type-from-list : {X : Type} → List X → Type
type-from-list {X} xs = Σ x ꞉ X , member x xs

type-from-list-is-listable : {X : Type} (xs : List X)
                           → listable (type-from-list xs)
type-from-list-is-listable {X} [] = [] , g
 where
  g : (σ : type-from-list []) → member σ []
  g (x , ())
type-from-list-is-listable {X} (x ∷ xs) = g
 where
  h : (x : X) → type-from-list (x ∷ xs)
  h x = x , in-head

  t : type-from-list xs → type-from-list (x ∷ xs)
  t (x , m) = x , in-tail m

  α : List (type-from-list xs) → List (type-from-list (x ∷ xs))
  α σs = h x ∷ map t σs

  β : ((σs , μ) : listable (type-from-list xs))
    → (τ : type-from-list (x ∷ xs)) → member τ (α σs)
  β (σs , μ) (y , in-head)   = in-head
  β (σs , μ) (y , in-tail m) = in-tail (member-map t (y , m) σs (μ (y , m)))

  f : listable (type-from-list xs) → listable (type-from-list (x ∷ xs))
  f (σs , μ) = α σs , β (σs , μ)

  g : listable (type-from-list (x ∷ xs))
  g = f (type-from-list-is-listable xs)

module _ {X : 𝓤 ̇ } where

 delete : {n : ℕ}
          {y : X}
          ((xs , _) : Vector' X (succ n))
        → member y xs
        → Vector' X n
 delete {0}      _              in-head     = [] , refl
 delete {0}      _              (in-tail _) = [] , refl
 delete {succ _} ((_ ∷ xs) , p) in-head     = xs , succ-lc p
 delete {succ n} ((x ∷ xs) , p) (in-tail m) = x ∷' delete {n} (xs , succ-lc p) m

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

\end{code}

Remove first occurrence:

\begin{code}

 remove : X → List X → List X
 remove x []       = []
 remove x (y ∷ ys) = if x == y then ys else (y ∷ remove x ys)

 remove-head : (x y : X) (ys : List X)
             → (x == y) ＝ true
             → remove x (y ∷ ys) ＝ ys
 remove-head x y ys q =
  remove x (y ∷ ys)                          ＝⟨ refl ⟩
  (if x == y then ys else (y ∷ remove x ys)) ＝⟨ I ⟩
  (if true then ys else (y ∷ remove x ys))   ＝⟨ refl ⟩
  ys                                         ∎
   where
    I = ap (λ - → if - then ys else (y ∷ remove x ys)) q

 remove-tail : (x y : X) (ys : List X)
             → (x == y) ＝ false
             → remove x (y ∷ ys) ＝ y ∷ remove x ys
 remove-tail x y ys q =
  remove x (y ∷ ys)                        ＝⟨ refl ⟩
  if x == y then ys else (y ∷ remove x ys) ＝⟨ I ⟩
  if false then ys else (y ∷ remove x ys)  ＝⟨ refl ⟩
  y ∷ remove x ys                          ∎
   where
    I  = ap (λ - → if - then ys else (y ∷ remove x ys)) q

 remove-length : (x : X) (ys : List X)
               → member x ys
               → (n : ℕ)
               → length ys ＝ succ n
               → length (remove x ys) ＝ n
 remove-length x ys@(z ∷ zs) m n p = h m n p (x == z) refl
  where
   h : member x ys
     → (n : ℕ)
     → length ys ＝ succ n
     → (b : Bool) → (x == z) ＝ b → length (remove x ys) ＝ n
   h _ n p true q =
    length (remove x (z ∷ zs)) ＝⟨ ap length (remove-head x z zs q) ⟩
    length zs                  ＝⟨ succ-lc p ⟩
    n                          ∎

   h in-head n p false q =
    𝟘-elim (true-is-not-false
             (true    ＝⟨ (==-refl x)⁻¹ ⟩
             (x == x) ＝⟨ q ⟩
             false    ∎))
   h (in-tail in-head)     0        () false q
   h (in-tail (in-tail m)) 0        () false q
   h (in-tail m)           (succ n) p  false q =
    length (remove x (z ∷ zs))  ＝⟨ I ⟩
    length (z ∷ remove x zs)    ＝⟨ refl ⟩
    succ (length (remove x zs)) ＝⟨ II ⟩
    succ n                      ∎
     where
      I  = ap length (remove-tail x z zs q)
      II = ap succ (remove-length x zs m n (succ-lc p))

 delete' : {n : ℕ}
           (x : X)
           ((xs , _) : Vector' X (succ n))
         → member x xs
         → Vector' X n
 delete' {n} x (xs , p) m = remove x xs , remove-length x xs m n p

 remove-all : X → List X → List X
 remove-all x []       = []
 remove-all x (y ∷ ys) = if x == y then remove-all x ys else (y ∷ remove-all x ys)

 _minus_ : List X → List X → List X
 xs minus []       = xs
 xs minus (y ∷ ys) = (remove-all y xs) minus ys

data Fin : ℕ → 𝓤₀ ̇  where
 𝟎   : {n : ℕ} → Fin (succ n)
 suc : {n : ℕ} → Fin n → Fin (succ n)

ℕ-to-Fin : (n : ℕ) → Fin (succ n)
ℕ-to-Fin 0     = 𝟎
ℕ-to-Fin (succ n) = suc (ℕ-to-Fin n)

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
list-Fin 0        = []
list-Fin (succ n) = 𝟎 ∷ map suc (list-Fin n)

list-Fin-correct : (n : ℕ) (i : Fin n) → member i (list-Fin n)
list-Fin-correct (succ n) 𝟎       = in-head
list-Fin-correct (succ n) (suc i) = in-tail g
 where
  IH : member i (list-Fin n)
  IH = list-Fin-correct n i

  g : member (suc i) (map suc (list-Fin n))
  g = member-map suc i (list-Fin n) IH

Fin-listable : (n : ℕ) → listable (Fin n)
Fin-listable n = list-Fin n , list-Fin-correct n

Fin-listable⁺ : (n : ℕ) → listable⁺ (Fin (succ n))
Fin-listable⁺ n = 𝟎 , Fin-listable (succ n)

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

data Vector (A : 𝓤 ̇ ) : ℕ → 𝓤 ̇ where
 []   : Vector A 0
 _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

head : {A : 𝓤 ̇ } {n : ℕ} → Vector A (succ n) → A
head (x ∷ xs) = x

tail : {A : 𝓤 ̇ } {n : ℕ} → Vector A (succ n) → Vector A n
tail (x ∷ xs) = xs

_!!_ : {X : 𝓤 ̇ } {n : ℕ} → Vector X n → Fin n → X
(x ∷ xs) !! 𝟎     = x
(x ∷ xs) !! suc n = xs !! n


module vector-util
        {𝓤 : Universe}
        {X : 𝓤 ̇ }
        {{_ : Eq X}}
       where

  data _is-in_ : X → {n : ℕ} → Vector X n → 𝓤 ̇ where
   in-head : {x : X}   {n : ℕ} {xs : Vector X n} → x is-in (x ∷ xs)
   in-tail : {x y : X} {n : ℕ} {xs : Vector X n} → x is-in xs → x is-in (y ∷ xs)

  insert : X → {n : ℕ} → Vector X n → Vector X (succ n)
  insert x xs = x ∷ xs

  remove : (x : X) {n : ℕ}
           (xs : Vector X (succ n))
         → x is-in xs
         → Vector X n
  remove x {0}      (_ ∷ []) in-head     = []
  remove x {succ n} (_ ∷ xs) in-head     = xs
  remove x {succ n} (y ∷ xs) (in-tail p) = y ∷ remove x {n} xs p

  has-no-repetitions : {n : ℕ} → Vector X n → 𝓤 ̇
  has-no-repetitions []       = 𝟙
  has-no-repetitions (x ∷ xs) = ¬ (x is-in xs) × has-no-repetitions xs

\end{code}
