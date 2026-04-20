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
open import UF.Base
open import UF.Subsingletons

data List {𝓤} (X : 𝓤 ̇ ) : 𝓤 ̇ where
 [] : List X
 _∷_ : X → List X → List X

infixr 3 _∷_

{-# BUILTIN LIST List #-}

length : {X : 𝓤 ̇ } → List X → ℕ
length []       = 0
length (x ∷ xs) = succ (length xs)

course-of-values-induction-on-length
 : {X : 𝓤 ̇ }
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

-- cons-is-non-empty : {X : 𝓤 ̇ } {x : X} {xs : List X} → is-non-empty (x ∷ xs)
pattern cons-is-non-empty = ⋆

list-non-emptiness-is-decidable : {X : 𝓤 ̇ }
                                  (xs : List X)
                                → is-decidable (is-non-empty xs)
list-non-emptiness-is-decidable [] = inr 𝟘-elim
list-non-emptiness-is-decidable (x ∷ xs) = inl cons-is-non-empty

map-is-non-empty : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (xs : List X)
                 → is-non-empty xs
                 → is-non-empty (map f xs)
map-is-non-empty f (x ∷ xs) cons-is-non-empty = cons-is-non-empty


[]-is-empty : {X : 𝓤 ̇ } → ¬ is-non-empty ([] {𝓤} {X})
[]-is-empty = 𝟘-elim

is-non-empty-++ : {X : 𝓤 ̇ } (xs ys : List X)
                → is-non-empty xs
                → is-non-empty (xs ++ ys)
is-non-empty-++ (x ∷ xs) ys ⋆ = ⋆

empty : {X : 𝓤 ̇ } → List X → Bool
empty []       = true
empty (x ∷ xs) = false

data member {X : 𝓤 ̇ } : X → List X → 𝓤 ̇ where
 in-head : {x : X}   {xs : List X} → member x (x ∷ xs)
 in-tail : {x y : X} {xs : List X} → member x xs → member x (y ∷ xs)

empty-list-has-no-members : {X : 𝓤 ̇ }
                            (x : X)
                          → ¬ member x []
empty-list-has-no-members x ()

lists-with-members-are-non-empty : {X : 𝓤 ̇ }
                                   {y : X}
                                   {xs : List X}
                                 → member y xs
                                 → is-non-empty xs
lists-with-members-are-non-empty in-head     = cons-is-non-empty
lists-with-members-are-non-empty (in-tail m) = cons-is-non-empty

member-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (x : X) (xs : List X)
           → member x xs
           → member (f x) (map f xs)
member-map f x' (_ ∷ _)  in-head     = in-head
member-map f x' (_ ∷ xs) (in-tail m) = in-tail (member-map f x' xs m)

private
 filter-helper : {X : 𝓤 ̇ }
                 (p : X → 𝓥 ̇ )
                 (x : X)
               → p x + ¬ p x
               → List X
               → List X
 filter-helper p x (inl _) xs = x ∷ xs
 filter-helper p x (inr _) xs = xs

filter : {X : 𝓤 ̇ } (p : X → 𝓥 ̇ ) → ((x : X) → p x + ¬ p x) → List X → List X
filter p δ []       = []
filter p δ (x ∷ xs) = filter-helper p x (δ x) (filter p δ xs)

open import MLTT.Plus-Properties

filter-member→ : {X : 𝓤 ̇ }
                 (p : X → 𝓥 ̇ )
                 (δ : (x : X) → p x + ¬ p x)
                 (y : X)
                 (xs : List X)
               → member y (filter p δ xs)
               → p y
filter-member→ {𝓤} {𝓥} {X} p δ y (x ∷ xs) = h x xs (δ x)
 where
  h : (x : X)
      (xs : List X)
    → (d : p x + ¬ p x)
    → member y (filter-helper p x d (filter p δ xs))
    → p y
  h x xs        (inl l) in-head     = l
  h x xs        (inl _) (in-tail m) = filter-member→ p δ y xs m
  h x (x' ∷ xs) (inr _) m           = h x' xs (δ x') m

filter-member← : {X : 𝓤 ̇ }
                 (p : X → 𝓥 ̇ )
                 (δ : (x : X) → p x + ¬ p x)
                 (y : X)
                 (xs : List X)
               → p y
               → member y xs
               → member y (filter p δ xs)
filter-member← {𝓤} {𝓥} {X} p δ y (x ∷ xs) = h x xs (δ x)
 where
  h : (x : X)
      (xs : List X)
    → (d : p x + ¬ p x)
    → p y
    → member y (x ∷ xs)
    → member y (filter-helper p x d (filter p δ xs))
  h x xs (inl _) py in-head = in-head
  h x (x' ∷ xs) (inl _) py (in-tail m) = in-tail (h x' xs (δ x') py m)
  h x xs (inr r) py in-head = 𝟘-elim (r py)
  h x xs (inr _) py (in-tail m) = filter-member← p δ y xs py m

member' : {X : 𝓤 ̇ } → X → List X → 𝓤 ̇
member' y []       = 𝟘
member' y (x ∷ xs) = (x ＝ y) + member' y xs

member'-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (x : X) (xs : List X)
            → member' x xs
            → member' (f x) (map f xs)
member'-map f x' (x ∷ xs) (inl p) = inl (ap f p)
member'-map f x' (x ∷ xs) (inr m) = inr (member'-map f x' xs m)

listed : 𝓤 ̇ → 𝓤 ̇
listed X = Σ xs ꞉ List X , ((x : X) → member x xs)

the-list : {X : 𝓤 ̇ } → listed X → List X
the-list (xs , m) = xs

member-of-the-list : {X : 𝓤 ̇ } (X-is-listed : listed X)
                   → (x : X) → member x (the-list X-is-listed)
member-of-the-list (xs , m) = m

𝟙-is-listed : listed (𝟙 {𝓤})
𝟙-is-listed = (⋆ ∷ []) , (λ x → in-head)

listed⁺ : 𝓤 ̇ → 𝓤 ̇
listed⁺ X = X × listed X

distinguished-element : {X : 𝓤 ̇ } → listed⁺ X → X
distinguished-element (x , X-listed) = x

listed⁺-types-are-listed : {X : 𝓤 ̇ } → listed⁺ X → listed X
listed⁺-types-are-listed (x , X-is-listed) = X-is-listed

𝟙-is-listed⁺ : listed⁺ (𝟙 {𝓤})
𝟙-is-listed⁺ = ⋆ , 𝟙-is-listed

type-from-list : {X : 𝓤 ̇ } → List X → 𝓤 ̇
type-from-list {𝓤} {X} xs = Σ x ꞉ X , member x xs

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
  remove x (y ∷ ys)                          ＝⟨refl⟩
  (if x == y then ys else (y ∷ remove x ys)) ＝⟨ I ⟩
  (if true then ys else (y ∷ remove x ys))   ＝⟨refl⟩
  ys                                         ∎
   where
    I = ap (λ - → if - then ys else (y ∷ remove x ys)) q

 remove-tail : (x y : X) (ys : List X)
             → (x == y) ＝ false
             → remove x (y ∷ ys) ＝ y ∷ remove x ys
 remove-tail x y ys q =
  remove x (y ∷ ys)                        ＝⟨refl⟩
  if x == y then ys else (y ∷ remove x ys) ＝⟨ I ⟩
  if false then ys else (y ∷ remove x ys)  ＝⟨refl⟩
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
    length (z ∷ remove x zs)    ＝⟨refl⟩
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
                                         → member x xs
                                         → member x (xs ++ ys)
right-concatenation-preserves-membership x xs@(x′ ∷ _)   ys in-head = in-head
right-concatenation-preserves-membership x xs@(x′ ∷ xs′) ys (in-tail p) =
 in-tail (right-concatenation-preserves-membership x xs′ ys p)

left-concatenation-preserves-membership : {X : 𝓤 ̇ } (x : X) (xs ys : List X)
                                      → member x xs
                                      → member x (ys ++ xs)
left-concatenation-preserves-membership x xs []       p = p
left-concatenation-preserves-membership x xs (y ∷ ys) p = †
 where
  † : member x (y ∷ (ys ++ xs))
  † = in-tail (left-concatenation-preserves-membership x xs ys p)

split-++-membership : {X : 𝓤 ̇ } (x : X) (xs ys : List X)
                    → member x (xs ++ ys)
                    → member x xs + member x ys
split-++-membership x []       zs p           = inr p
split-++-membership x (x ∷ ys) zs in-head     = inl in-head
split-++-membership x (y ∷ ys) zs (in-tail p) =
 cases † ‡ (split-++-membership x ys zs p)
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

map-id : {X : 𝓤 ̇ }
         (xs : List X)
       → map id xs ＝ xs
map-id [] = refl
map-id (x ∷ xs) = ap (x ∷_) (map-id xs)

map-∘ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
        (f : X → Y) (g : Y → Z)
      → map (g ∘ f) ∼ map g ∘ map f
map-∘ f g []       = refl
map-∘ f g (x ∷ xs) = ap (g (f x) ∷_) (map-∘ f g xs)

concat : {X : 𝓤 ̇ } → List (List X) → List X
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

concat-singletons' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     (g : X → Y)
                     (xs : List X)
                   → concat (map (λ x → [ g x ]) xs) ＝ map g xs
concat-singletons' g []       = refl
concat-singletons' g (x ∷ xs) = ap (g x ∷_) (concat-singletons' g xs)

concat-singletons : {X : 𝓤 ̇ }
                    (xs : List X) → concat (map [_] xs) ＝ xs
concat-singletons xs = concat-singletons' id xs ∙ map-id xs

concat-++ : {X : 𝓤 ̇ }
            (xss yss : List (List X))
          → concat (xss ++ yss) ＝ concat xss ++ concat yss
concat-++ [] yss = refl
concat-++ (xs ∷ xss) yss =
 concat (xs ∷ xss ++ yss)         ＝⟨refl⟩
 xs ++ concat (xss ++ yss)        ＝⟨ I ⟩
 xs ++ (concat xss ++ concat yss) ＝⟨ II ⟩
 (xs ++ concat xss) ++ concat yss ＝⟨refl⟩
 concat (xs ∷ xss) ++ concat yss  ∎
  where
   I  = ap (xs ++_) (concat-++ xss yss)
   II = (++-assoc xs (concat xss) (concat yss))⁻¹

\end{code}

The following are the Kleisli extension operations for the list monad
and its associativity law.

\begin{code}

List-ext : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
         → (X → List Y) → (List X → List Y)
List-ext f xs = concat (map f xs)

List-ext-unit : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                (f : X → List Y) (x : X)
              → f x ++ [] ＝ f x
List-ext-unit f x = ([]-right-neutral (f x))⁻¹

List-ext-assoc
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
   (g : Y → List Z) (f : X → List Y)
   (xs : List X)
 → List-ext (λ x → List-ext g (f x)) xs ＝ List-ext g (List-ext f xs)
List-ext-assoc g f []       = refl
List-ext-assoc g f (x ∷ xs) =
 List-ext (λ - → List-ext g (f -)) (x ∷ xs)               ＝⟨refl⟩
 List-ext g (f x) ++ List-ext (λ - → List-ext g (f -)) xs ＝⟨ I ⟩
 List-ext g (f x) ++ List-ext g (List-ext f xs)           ＝⟨ II ⟩
 concat (map g (f x) ++ map g (List-ext f xs))            ＝⟨ III ⟩
 List-ext g (f x ++ List-ext f xs)                        ＝⟨refl⟩
 List-ext g (List-ext f (x ∷ xs))                         ∎
  where
   I   = ap (List-ext g (f x) ++_) (List-ext-assoc g f xs)
   II  = (concat-++ (map g (f x)) (map g (List-ext f xs)))⁻¹
   III = (ap concat (map-++ g (f x) (List-ext f xs)))⁻¹

map' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → List X → List Y
map' f = List-ext (λ x → [ f x ])

map-agrees-with-map' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                       (f : X → Y)
                     → map f ∼ map' f
map-agrees-with-map' f [] = refl
map-agrees-with-map' f (x ∷ xs) = ap (f x ∷_) (map-agrees-with-map' f xs)

\end{code}

Added by Martin Escardo and Paulo Oliva 12th March 2025.

\begin{code}

member-of-concat← : {X : 𝓤 ̇ } (x : X) (yss : List (List X))
                  → member x (concat yss)
                  → Σ ys ꞉ List X , member ys yss × member x ys
member-of-concat← {𝓤} {X} x (ys ∷ yss) m = II I
 where
  I : member x ys + member x (concat yss)
  I = split-++-membership x ys (concat yss) m

  II : type-of I → Σ ys' ꞉ List X , member ys' (ys ∷ yss) × member x ys'
  II (inl l) = ys , in-head , l
  II (inr r) = III IH
   where
    IH : Σ ys' ꞉ List X , member ys' yss × member x ys'
    IH = member-of-concat← x yss r

    III : type-of IH → Σ ys' ꞉ List X , member ys' (ys ∷ yss) × member x ys'
    III (ys' , r₁ , r₂) = ys' , in-tail r₁ , r₂

member-of-map← : {X Y : 𝓤 ̇ } (f : X → Y) (y : Y) (xs : List X)
              → member y (map f xs)
              → Σ x ꞉ X , member x xs × (f x ＝ y)
member-of-map← f y (x ∷ xs) in-head = x , in-head , refl
member-of-map← {𝓤} {X} f y (x ∷ xs) (in-tail m) = I IH
 where
  IH : Σ x ꞉ X , member x xs × (f x ＝ y)
  IH = member-of-map← f y xs m

  I : type-of IH → Σ x' ꞉ X , member x' (x ∷ xs) × (f x' ＝ y)
  I (x , m , e) = x , in-tail m , e

\end{code}

Added 10 April 2025 by Fredrik Nordvall Forsberg.

\begin{code}

data All {X : 𝓤 ̇ } (P : X → 𝓥 ̇ ) : List X → 𝓤 ⊔ 𝓥 ̇  where
  [] : All P []
  _∷_ : {x : X} {xs : List X} → P x → All P xs → All P (x ∷ xs)

All-is-prop : {X : 𝓤 ̇ } (P : X → 𝓥 ̇ )
            → is-prop-valued-family P
            → is-prop-valued-family (All P)
All-is-prop P p [] [] [] = refl
All-is-prop P p (x ∷ l) (a ∷ as) (a' ∷ as') =
 ap₂ _∷_ (p x a a') (All-is-prop P p l as as')

\end{code}

Added by Martin Escardo and Paulo Oliva 14th May 2025.

\begin{code}

member-of-concat→ : {X : 𝓤 ̇ } (x : X) (yss : List (List X))
                    (zs : List X)
                  → member zs yss
                  → member x zs
                  → member x (concat yss)
member-of-concat→ x (ys ∷ yss) .ys in-head m₂ =
 right-concatenation-preserves-membership x ys (concat yss) m₂
member-of-concat→ x (ys ∷ yss) zs (in-tail m₁) m₂ =
 left-concatenation-preserves-membership x (concat yss) ys IH
 where
  IH : member x (concat yss)
  IH = member-of-concat→ x yss zs m₁ m₂

member-of-map→ : {X Y : 𝓤 ̇ } (f : X → Y) (xs : List X)
                 (x : X)
               → member x xs
               → member (f x) (map f xs)
member-of-map→ f xs x in-head = in-head
member-of-map→ f (_ ∷ xs) x (in-tail m) = in-tail (member-of-map→ f xs x m)

\end{code}

Added 8-22 October by Martin Escardo and Paulo Oliva.

\begin{code}

conditionally-prepend : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                      → (x : X)
                      → A x + ¬ A x
                      → List (Σ x ꞉ X , A x)
                      → List (Σ x ꞉ X , A x)
conditionally-prepend A x (inl a) ys = (x , a) ∷ ys
conditionally-prepend A x (inr _) ys = ys

filter' : {X : 𝓤 ̇ }
          (A : X → 𝓥 ̇ )
        → ((x : X) → A x + ¬ A x)
        → List X
        → List (Σ x ꞉ X , A x)
filter' A δ []       = []
filter' A δ (x ∷ xs) = conditionally-prepend A x (δ x) (filter' A δ xs)

filter'-member← : {X : 𝓤 ̇ }
                  (A : X → 𝓥 ̇ )
                  (δ : (x : X) → A x + ¬ A x)
                  (A-is-prop-valued : (x : X) → is-prop (A x))
                  (y : X)
                  (xs : List X)
                  (a : A y)
                → member y xs
                → member (y , a) (filter' A δ xs)
filter'-member← {𝓤} {𝓥} {X} A δ A-is-prop-valued y (x ∷ xs) = h x xs (δ x)
 where
  h : (x : X)
      (xs : List X)
    → (d : A x + ¬ A x)
      (a : A y)
    → member y (x ∷ xs)
    → member (y , a) (conditionally-prepend A x d (filter' A δ xs))
  h x xs (inl b) a in-head = II
   where
    I : member (y , a) ((y , a) ∷ filter' A δ xs)
    I = in-head

    II : member (y , a) ((y , b) ∷ filter' A δ xs)
    II = transport
          (λ - → member (y , a) ((y , -) ∷ filter' A δ xs))
          (A-is-prop-valued y a b)
          I
  h x (x' ∷ xs) (inl b) a (in-tail m) = in-tail (h x' xs (δ x') a m)
  h x xs (inr r) a in-head = 𝟘-elim (r a)
  h x xs (inr x₁) a (in-tail m) = filter'-member← A δ A-is-prop-valued y xs a m

detachable-subtype-of-listed-type-is-listed
 : {X : 𝓤 ̇ }
 → (A : X → 𝓥 ̇ )
 → ((x : X) → is-decidable (A x))
 → ((x : X) → is-prop (A x))
 → listed X
 → listed (Σ x ꞉ X , A x)
detachable-subtype-of-listed-type-is-listed {𝓤} {𝓥} {X} A δ A-is-prop-valued (xs , m)
 = filter' A δ xs , γ
 where
  γ : (σ : Σ x ꞉ X , A x) → member σ (filter' A δ xs)
  γ (x , a) = filter'-member← A δ A-is-prop-valued x xs a (m x)

\end{code}

Added by Martin Escardo and Paulo Oliva 29th October 2025.

Dependent version of `map`.

\begin{code}

dmap : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → ((x : X) → Y x) → List X → List (Σ x ꞉ X , Y x)
dmap f []       = []
dmap f (x ∷ xs) = (x , f x) ∷ dmap f xs

\end{code}

We now discuss the non-dependent special case of the above.

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) where

 pr₁-of-dmap : (xs : List X)
             → xs ＝ map pr₁ (dmap f xs)
 pr₁-of-dmap [] = refl
 pr₁-of-dmap (x ∷ xs) = ap (x ∷_) (pr₁-of-dmap xs)

 map-from-dmap : (xs : List X)
               → map f xs ＝ map pr₂ (dmap f xs)
 map-from-dmap [] = refl
 map-from-dmap (x ∷ xs) = ap (f x ∷_) (map-from-dmap xs)

\end{code}

In the non-dependent case, we can define dmap from map.

\begin{code}

 dmap-from-map : (xs : List X)
               → dmap f xs ＝ map (λ x → x , f x) xs
 dmap-from-map [] = refl
 dmap-from-map (x ∷ xs) = ap ((x , f x) ∷_) (dmap-from-map xs)

\end{code}
