Martin Escardo, January 2021.

It is possible to work with lists *defined* from the ingredients of
our Spartan MLTT (see the module Fin.lagda). For the moment we are
Athenian in this respect.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

module MLTT.List where

open import MLTT.Spartan
open import MLTT.Bool
open import Naturals.Properties
open import Naturals.Order hiding (minus)
open import Notation.Order

data List {𝓤} (X : 𝓤 ̇ ) : 𝓤 ̇  where
 [] : List X
 _∷_ : X → List X → List X

infixr 3 _∷_

{-# BUILTIN LIST List #-}

length : {X : 𝓤 ̇ } → List X → ℕ
length []       = 0
length (x ∷ xs) = succ (length xs)

course-of-values-induction-on-length
 : {X : 𝓤 ̇}
 → (P : List X → 𝓥 ̇ )
 → ((xs : List X) → ((ys : List X) → length ys < length xs → P ys) → P xs)
 → (xs : List X) → P xs
course-of-values-induction-on-length {𝓤} {𝓥} {X} =
 course-of-values-induction-on-value-of-function length

Vector' : 𝓤 ̇ → ℕ → 𝓤 ̇
Vector' X n = (Σ xs ꞉ List X , length xs ＝ n)

_∷'_ : {X : 𝓤 ̇ } {n : ℕ} → X → Vector' X n → Vector' X (succ n)
x ∷' (xs , p) = (x ∷ xs) , ap succ p

equal-heads : {X : 𝓤 ̇ } {x y : X} {s t : List X}
            → x ∷ s ＝ y ∷ t
            → x ＝ y
equal-heads refl = refl

equal-tails : {X : 𝓤 ̇ } {x y : X} {s t : List X}
            → x ∷ s ＝ y ∷ t
            → s ＝ t
equal-tails refl = refl

equal-head-tail : {X : 𝓤 ̇ } {x : X} {s t : List X}
                → x ∷ s ＝ t
                → Σ y ꞉ X , Σ t' ꞉ List X , (t ＝ y ∷ t')
equal-head-tail {𝓤} {X} {x} {s} {t} refl = x , s , refl

[_] : {X : 𝓤 ̇ } → X → List X
[ x ] = x ∷ []

[]-is-not-cons : {X : 𝓤 ̇ } (x : X) (xs : List X)
               → [] ≠ x ∷ xs
[]-is-not-cons x []        ()
[]-is-not-cons x (x₀ ∷ xs) ()

_++_ : {X : 𝓤 ̇ } → List X → List X → List X
[]      ++ t = t
(x ∷ s) ++ t = x ∷ (s ++ t)

infixr 2 _++_

[]-right-neutral : {X : 𝓤 ̇ } (s : List X) → s ＝ s ++ []
[]-right-neutral []      = refl
[]-right-neutral (x ∷ s) = ap (x ∷_) ([]-right-neutral s)

++-assoc : {X : 𝓤 ̇ } → associative (_++_ {𝓤} {X})
++-assoc []      t u = refl
++-assoc (x ∷ s) t u = ap (x ∷_) (++-assoc s t u)

foldr : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y → Y) → Y → List X → Y
foldr _·_ ε []       = ε
foldr _·_ ε (x ∷ xs) = x · foldr _·_ ε xs

map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → List X → List Y
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

_<$>_ = map

is-non-empty : {X : 𝓤 ̇ } → List X → 𝓤 ̇
is-non-empty []       = 𝟘
is-non-empty (x ∷ xs) = 𝟙

[]-is-empty : {X : 𝓤 ̇ } → ¬ is-non-empty ([] {𝓤} {X})
[]-is-empty = 𝟘-elim

-- cons-is-non-empty : {X : 𝓤 ̇ } {x : X} {xs : List X} → is-non-empty (x ∷ xs)
pattern cons-is-non-empty = ⋆

is-non-empty-++ : {X : 𝓤 ̇ } (xs ys : List X)
                → is-non-empty xs
                → is-non-empty (xs ++ ys)
is-non-empty-++ (x ∷ xs) ys ⋆ = ⋆

empty : {X : 𝓤 ̇ } → List X → Bool
empty []       = true
empty (x ∷ xs) = false

data member {X : 𝓤 ̇ } : X → List X → 𝓤 ̇  where
 in-head : {x : X}   {xs : List X} → member x (x ∷ xs)
 in-tail : {x y : X} {xs : List X} → member x xs → member x (y ∷ xs)

member-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (x : X) (xs : List X)
           → member x xs
           → member (f x) (map f xs)
member-map f x' (_ ∷ _)  in-head     = in-head
member-map f x' (_ ∷ xs) (in-tail m) = in-tail (member-map f x' xs m)

member' : {X : 𝓤 ̇ } → X → List X → 𝓤 ̇
member' y []       = 𝟘
member' y (x ∷ xs) = (x ＝ y) + member' y xs

\end{code}


\begin{code}

member'-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (x : X) (xs : List X)
            → member' x xs
            → member' (f x) (map f xs)
member'-map f x' (x ∷ xs) (inl p) = inl (ap f p)
member'-map f x' (x ∷ xs) (inr m) = inr (member'-map f x' xs m)

listed : 𝓤 ̇  → 𝓤 ̇
listed X = Σ xs ꞉ List X , ((x : X) → member x xs)

listed⁺ : 𝓤 ̇  → 𝓤 ̇
listed⁺ X = X × listed X

type-from-list : {X : 𝓤  ̇} → List X → 𝓤  ̇
type-from-list {X = X} xs = Σ x ꞉ X , member x xs

type-from-list-is-listed : {X : 𝓤 ̇ } (xs : List X)
                         → listed (type-from-list xs)
type-from-list-is-listed {𝓤} {X} [] = [] , g
 where
  g : (σ : type-from-list []) → member σ []
  g (x , ())
type-from-list-is-listed {𝓤} {X} (x ∷ xs) = g
 where
  h : (x : X) → type-from-list (x ∷ xs)
  h x = x , in-head

  t : type-from-list xs → type-from-list (x ∷ xs)
  t (x , m) = x , in-tail m

  α : List (type-from-list xs) → List (type-from-list (x ∷ xs))
  α σs = h x ∷ map t σs

  β : ((σs , μ) : listed (type-from-list xs))
    → (τ : type-from-list (x ∷ xs)) → member τ (α σs)
  β (σs , μ) (y , in-head)   = in-head
  β (σs , μ) (y , in-tail m) = in-tail (member-map t (y , m) σs (μ (y , m)))

  f : listed (type-from-list xs) → listed (type-from-list (x ∷ xs))
  f (σs , μ) = α σs , β (σs , μ)

  g : listed (type-from-list (x ∷ xs))
  g = f (type-from-list-is-listed xs)

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

 remove-first : X → List X → List X
 remove-first x []       = []
 remove-first x (y ∷ ys) = if x == y then ys else (y ∷ remove-first x ys)

 remove-all : X → List X → List X
 remove-all x []       = []
 remove-all x (y ∷ ys) = if x == y then remove-all x ys else (y ∷ remove-all x ys)

 _minus_ : List X → List X → List X
 xs minus []       = xs
 xs minus (y ∷ ys) = (remove-all y xs) minus ys

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

\end{code}

Added by Ayberk Tosun on 2023-10-16.

\begin{code}

right-concatenation-preserves-membership : {X : 𝓤 ̇ } (x : X) (xs ys : List X)
                                         → member x xs → member x (xs ++ ys)
right-concatenation-preserves-membership x xs@(x′ ∷ _)   ys in-head = in-head
right-concatenation-preserves-membership x xs@(x′ ∷ xs′) ys (in-tail p) =
 in-tail (right-concatenation-preserves-membership x xs′ ys p)

left-concatenation-preserves-membership : {X : 𝓤 ̇ } (x : X) (xs ys : List X)
                                      → member x xs → member x (ys ++ xs)
left-concatenation-preserves-membership x xs []       p = p
left-concatenation-preserves-membership x xs (y ∷ ys) p = †
 where
  † : member x (y ∷ (ys ++ xs))
  † = in-tail (left-concatenation-preserves-membership x xs ys p)

++-membership₁ : {X : 𝓤 ̇ } (x : X) (xs ys : List X)
               → member x (xs ++ ys) → member x xs + member x ys
++-membership₁ x []       zs p           = inr p
++-membership₁ x (x ∷ ys) zs in-head     = inl in-head
++-membership₁ x (y ∷ ys) zs (in-tail p) = cases † ‡ (++-membership₁ x ys zs p)
 where
  † : member x ys → member x (y ∷ ys) + member x zs
  † p = inl (in-tail p)

  ‡ : member x zs → member x (y ∷ ys) + member x zs
  ‡ = inr

\end{code}

Added 2nd April 2024 by Martin Escardo and Paulo Oliva. Ingredients
for the list monad.

\begin{code}

map-++ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
         (f : X → Y)
         (xs ys : List X)
       → map f (xs ++ ys) ＝ map f xs ++ map f ys
map-++ f [] ys       = refl
map-++ f (x ∷ xs) ys = ap (f x ∷_) (map-++ f xs ys)

concat : {X : 𝓤 ̇ } → List (List X) → List X
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

concat-singletons : {X : 𝓤 ̇ }
                    (xs : List X) → concat (map [_] xs) ＝ xs
concat-singletons []       = refl
concat-singletons (x ∷ xs) = ap (x ∷_) (concat-singletons xs)

concat-++ : {X : 𝓤 ̇ }
            (xss yss : List (List X))
          → concat (xss ++ yss) ＝ concat xss ++ concat yss
concat-++ [] yss = refl
concat-++ (xs ∷ xss) yss =
 concat (xs ∷ xss ++ yss)         ＝⟨ refl ⟩
 xs ++ concat (xss ++ yss)        ＝⟨ I ⟩
 xs ++ (concat xss ++ concat yss) ＝⟨ II ⟩
 (xs ++ concat xss) ++ concat yss ＝⟨ refl ⟩
 concat (xs ∷ xss) ++ concat yss  ∎
  where
   I  = ap (xs ++_) (concat-++ xss yss)
   II = (++-assoc xs (concat xss) (concat yss))⁻¹

\end{code}

The following are the Kleisli extension operation for the list monad and its associativity law.

\begin{code}

ext : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
    → (X → List Y) → (List X → List Y)
ext f xs = concat (map f xs)

ext-assoc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
            (g : Y → List Z) (f : X → List Y)
            (xs : List X)
          → ext (λ x → ext g (f x)) xs ＝ ext g (ext f xs)
ext-assoc g f []       = refl
ext-assoc g f (x ∷ xs) =
 ext (λ - → ext g (f -)) (x ∷ xs)          ＝⟨ refl ⟩
 ext g (f x) ++ ext (λ - → ext g (f -)) xs ＝⟨ I ⟩
 ext g (f x) ++ ext g (ext f xs)           ＝⟨ II ⟩
 concat (map g (f x) ++ map g (ext f xs))  ＝⟨ III ⟩
 ext g (f x ++ ext f xs)                   ＝⟨ refl ⟩
 ext g (ext f (x ∷ xs))                    ∎
  where
   I   = ap (ext g (f x) ++_) (ext-assoc g f xs)
   II  = (concat-++ (map g (f x)) (map g (ext f xs)))⁻¹
   III = (ap concat (map-++ g (f x) (ext f xs)))⁻¹

\end{code}
