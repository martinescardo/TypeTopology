Taken from the Advanced Functional Programming module lecture notes 2023-24

Defines an insertion sort function and proves its correctness

\begin{code}

{-# OPTIONS --safe --without-K #-}


open import MLTT.Spartan renaming (_+_ to _∔_)
open import MLTT.List
open import Notation.Order
open import Ordinals.Notions
open import TGH.isomorphisms
open import TGH.iso-utils


module TGH.AFP2024.InsertionSort (X : Type) (_<_ : X → X → 𝓤₀ ̇ )
 (trichotomy : is-trichotomous-order _<_) where
insert : X → List X → List X
insert y [] = y ∷ []
insert y (x ∷ xs) = γ (trichotomy x y)
 where
  γ : (x < y) ∔ (x ＝ y) ∔ (y < x) → List X
  γ (inl y<x) = x ∷ insert y xs
  γ (inr x≤y) = y ∷ x ∷ xs

insert-all : List X → List X → List X
insert-all [] ys = ys
insert-all (x ∷ xs) ys = insert x (insert-all xs ys)

insertion-sort : List X → List X
insertion-sort xs = insert-all xs []

data Sorted : List X → Set where
 nil-sorted  : Sorted []
 sing-sorted : {x : X} → Sorted (x ∷ [])
 adj-sorted  : {y x : X} {xs : List X}
             → Sorted (x ∷ xs)
             → (x ＝ y) ∔ (y < x)
             → Sorted (y ∷ x ∷ xs)

Pos : {X : Type} → List X → 𝓤₀ ̇ 
Pos [] = 𝟘
Pos (_ ∷ xs) = 𝟙 ∔ Pos xs

Inhab : {X : Type} (l : List X) → Pos l → X
Inhab (x ∷ _) (inl ⋆) = x
Inhab (_ ∷ l) (inr p) = Inhab l p

record _IsPermutationOf_ (xs ys : List X) : Type where
 field
  pos-iso : Pos xs ≅ Pos ys
  inhab-eq : (p : Pos xs) → Inhab xs p ＝ Inhab ys (_≅_.bijection pos-iso p)

record SortingAlgorithm : Type where
 field
  sort : List X → List X
  sort-is-sorted : (xs : List X) → Sorted (sort xs)
  sort-is-permutation : (xs : List X) → (sort xs) IsPermutationOf xs

insert-is-sorted : (x : X) (xs : List X) → Sorted xs → Sorted (insert x xs)
insert-is-sorted y [] nil-sorted = sing-sorted 
insert-is-sorted y (x ∷ []) sing-sorted with trichotomy x y
insert-is-sorted y (x ∷ []) sing-sorted | inl x<y
 = adj-sorted sing-sorted (inr x<y)
insert-is-sorted y (x ∷ []) sing-sorted | inr y≤x
 = adj-sorted sing-sorted y≤x
insert-is-sorted y (z ∷ x ∷ xs) (adj-sorted srtd z≤x) with trichotomy z y
insert-is-sorted y (z ∷ x ∷ xs) (adj-sorted srtd z≤x)
 | inl z<y with trichotomy x y | insert-is-sorted y (x ∷ xs) srtd
insert-is-sorted y (z ∷ x ∷ xs) (adj-sorted srtd z≤x)
 | inl z<y | inl x<y | srtd' = adj-sorted srtd' z≤x
insert-is-sorted y (z ∷ x ∷ xs) (adj-sorted srtd z≤x)
 | inl z<y | inr y≤x | _ = adj-sorted (adj-sorted srtd y≤x) (inr z<y)
insert-is-sorted y (z ∷ x ∷ xs) (adj-sorted srtd z≤x)
 | inr y≤z = adj-sorted (adj-sorted srtd z≤x) y≤z

insert-all-is-sorted : (xs ys : List X) (ys-srtd : Sorted ys)
  → Sorted (insert-all xs ys)
insert-all-is-sorted [] ys ys-srtd = ys-srtd
insert-all-is-sorted (x ∷ xs) ys ys-srtd
 = insert-is-sorted x (insert-all xs ys) (insert-all-is-sorted xs ys ys-srtd)

insertion-sort-is-sorted : (xs : List X) → Sorted (insertion-sort xs)
insertion-sort-is-sorted xs = insert-all-is-sorted xs [] nil-sorted 

insert-pos-iso : (x : X) (xs : List X)
 → Pos (insert x xs) ≅ 𝟙 ∔ Pos xs
insert-pos-iso y [] = id-iso (𝟙 ∔ 𝟘)
insert-pos-iso y (x ∷ xs) with trichotomy x y
insert-pos-iso y (x ∷ xs) | inl x<y
 = ∔-left-swap-iso 𝟙 𝟙 (Pos xs) ∘ᵢ
   (∔-pair-iso (id-iso 𝟙) (insert-pos-iso y xs))
insert-pos-iso y (x ∷ xs) | inr y≤x = id-iso (𝟙 ∔ 𝟙 ∔ Pos xs)

insert-all-pos-iso : (xs ys : List X)
  → Pos (insert-all xs ys) ≅ Pos (xs ++ ys)
insert-all-pos-iso [] ys = id-iso (Pos ys)
insert-all-pos-iso (x ∷ xs) ys =
 Pos (insert x (insert-all xs ys)) ≅⟨ insert-pos-iso x (insert-all xs ys) ⟩
 𝟙 ∔ Pos (insert-all xs ys)
 ≅⟨ ∔-pair-iso (id-iso 𝟙) (insert-all-pos-iso xs ys) ⟩
 (𝟙 ∔ Pos (xs ++ ys)) ∎ᵢ

pos-swap-lemma : (x y : X) (xs : List X)
 → (p : Pos (y ∷ xs))
 → Inhab (x ∷ y ∷ xs) (inr p) ＝
   Inhab (y ∷ x ∷ xs) (_≅_.bijection (∔-left-swap-iso 𝟙 𝟙 (Pos xs)) (inr p))
pos-swap-lemma x y xs (inl ⋆) = refl
pos-swap-lemma x y xs (inr p) = refl

insert-inhab-eq : (x : X) (xs : List X)
 → (p : Pos (insert x xs))
 → Inhab (insert x xs) p ＝ Inhab (x ∷ xs)
   (_≅_.bijection (insert-pos-iso x xs) p)
insert-inhab-eq y [] p = refl
insert-inhab-eq y (x ∷ xs) p with trichotomy x y
insert-inhab-eq y (x ∷ xs) (inl ⋆) | inl x<y = refl
insert-inhab-eq y (x ∷ xs) (inr p) | inl x<y 
 = Inhab (insert y xs) p ＝⟨ insert-inhab-eq y xs p ⟩
 Inhab (y ∷ xs) (_≅_.bijection (insert-pos-iso y xs) p) ＝⟨ refl ⟩
 Inhab (x ∷ y ∷ xs) (inr (_≅_.bijection (insert-pos-iso y xs) p))
 ＝⟨ pos-swap-lemma x y xs (_≅_.bijection (insert-pos-iso y xs) p) ⟩ 
 Inhab (y ∷ x ∷ xs) (_≅_.bijection (∔-left-swap-iso 𝟙 𝟙 (Pos xs))
                       (inr (_≅_.bijection (insert-pos-iso y xs) p))) ∎ 
insert-inhab-eq y (x ∷ xs) p | inr y≤x = refl

inhab-ext-lemma : (x : X) (xs ys : List X) 
 → (α : Pos xs ≅ Pos ys)
 → (e : (p : Pos xs) → Inhab xs p ＝ Inhab ys (_≅_.bijection α p))
 → (p : Pos (x ∷ xs))
 → Inhab (x ∷ xs) p ＝ Inhab (x ∷ ys)
    (_≅_.bijection (∔-pair-iso (id-iso 𝟙) α) p)
inhab-ext-lemma x xs ys α e (inl ⋆) = refl
inhab-ext-lemma x xs ys α e (inr p) = e p

insert-all-inhab-eq : (xs ys : List X) (p : Pos (insert-all xs ys))
 → Inhab (insert-all xs ys) p ＝
   Inhab (xs ++ ys) (_≅_.bijection (insert-all-pos-iso xs ys) p)
insert-all-inhab-eq [] ys p = refl
insert-all-inhab-eq (x ∷ xs) ys p
 = Inhab (insert x (insert-all xs ys)) p
    ＝⟨ insert-inhab-eq x (insert-all xs ys) p ⟩
   Inhab (x ∷ insert-all xs ys) (_≅_.bijection
   (insert-pos-iso x (insert-all xs ys)) p)
    ＝⟨ inhab-ext-lemma x (insert-all xs ys) (xs ++ ys)
    (insert-all-pos-iso xs ys)
    (λ p → insert-all-inhab-eq xs ys p)
    (_≅_.bijection (insert-pos-iso x (insert-all xs ys)) p) ⟩ 
   Inhab (x ∷ xs ++ ys)
   (_≅_.bijection (∔-pair-iso (id-iso 𝟙) (insert-all-pos-iso xs ys))
   (_≅_.bijection (insert-pos-iso x (insert-all xs ys)) p)) ∎

insert-is-perm : (x : X) (xs : List X)
 → (insert x xs) IsPermutationOf (x ∷ xs)
insert-is-perm x xs = record { pos-iso = insert-pos-iso x xs
                      ; inhab-eq = insert-inhab-eq x xs }

insert-all-is-perm : (xs ys : List X)
 → (insert-all xs ys) IsPermutationOf (xs ++ ys)
insert-all-is-perm xs ys = record { pos-iso = insert-all-pos-iso xs ys
                           ; inhab-eq = insert-all-inhab-eq xs ys }

insertion-sort-is-perm : (xs : List X)
 → (insertion-sort xs) IsPermutationOf xs
insertion-sort-is-perm xs = transport (insertion-sort xs IsPermutationOf_)
 (([]-right-neutral xs)⁻¹) (insert-all-is-perm xs [])

insertion-sort-algorithm : SortingAlgorithm
insertion-sort-algorithm =
  record { sort = insertion-sort
         ; sort-is-sorted = insertion-sort-is-sorted
         ; sort-is-permutation = insertion-sort-is-perm
         } 

\end{code}
