Martin Escardo and Paulo Oliva, April 2024

The following are facts that we thought would be needed to ultimately
show that lists without repetitions form a monad, but we ended up not
needing them.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DiscreteGraphicMonoids.ListsWithoutRepetitionsMore
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import MLTT.List
            renaming (_∷_ to _•_ ;          -- typed as \bub
                      _++_ to _◦_ ;         -- typed as \buw
                      ++-assoc to ◦-assoc)
open import MLTT.Plus-Properties
open import UF.Base
open import DiscreteGraphicMonoids.ListsWithoutRepetitions fe
open import UF.DiscreteAndSeparated

module _
         {𝓤 : Universe}
         {X : 𝓤 ̇ }
         {{d' : is-discrete' X}}
       where

 private
  d : is-discrete X
  d = discrete'-gives-discrete d'

 _∉_ _∈_ : X → List X → 𝓤 ̇
 x ∉ xs = ρ (x • xs) ＝ x • ρ xs
 x ∈ xs = ¬ (x ∉ xs)

 ∉-is-decidable : (x : X) (xs : List X) → (x ∉ xs) + (x ∈ xs)
 ∉-is-decidable x xs = List-is-discrete (ρ (x • xs)) (x • ρ xs)

 ∉-step : (z x : X) (xs : List X) → z ≠ x → z ∉ xs → z ∉ (x • xs)
 ∉-step z x xs ν μ =
  ρ (z • x • xs) ＝⟨ refl ⟩
  z • δ z (x • δ x (ρ xs)) ＝⟨ ap (z •_) (δ-≠ z x (δ x (ρ xs)) ν) ⟩
  z • x • δ z (δ x (ρ xs)) ＝⟨ ap (λ - → z • x • -) (δ-swap z x (ρ xs)) ⟩
  z • x • δ x (δ z (ρ xs)) ＝⟨ ap (λ - → z • x • δ x -) μ' ⟩
  z • x • δ x (ρ xs)       ＝⟨ refl ⟩
  z • ρ (x • xs)           ∎
   where
    μ' : δ z (ρ xs) ＝ ρ xs
    μ' = equal-tails μ

 split : (z : X) (xs : List X)
       → (z ∉ xs)
       + (Σ (ys , zs) ꞉ List X × List X , (xs ＝ ys ◦ z • zs) × (z ∉ ys))
 split z [] = inl refl
 split z (x • xs) = h (d z x)
  where
   IH : (z ∉ xs)
      + (Σ (ys , zs) ꞉ List X × List X , (xs ＝ ys ◦ z • zs) × (z ∉ ys))
   IH = split z xs

   h : is-decidable (z ＝ x)
     → (z ∉ (x • xs))
     + (Σ (ys , zs) ꞉ List X × List X , (x • xs ＝ ys ◦ z • zs) × (z ∉ ys))
   h (inl refl) = inr (([] , xs) , (refl , refl))
   h (inr ν) = k (∉-is-decidable z xs)
    where
     k : is-decidable (z ∉ xs)
       → (z ∉ (x • xs))
       + (Σ (ys , zs) ꞉ List X × List X , (x • xs ＝ ys ◦ z • zs) × (z ∉ ys))
     k (inl μ) = inl (∉-step z x xs ν μ)
     k (inr ι) = inr (II I)
      where
       I : Σ (ys , zs) ꞉ List X × List X , (xs ＝ ys ◦ z • zs) × (z ∉ ys)
       I = Left-fails-gives-right-holds IH ι

       II : type-of I
          → Σ (ys' , zs') ꞉ List X × List X , (x • xs ＝ ys' ◦ z • zs') × (z ∉ ys')
       II ((ys , zs) , (e , μ')) =
        ((x • ys) , zs) , ((ap (x •_) e) , ∉-step z x ys ν μ')

 split' : (z : X) (xs : List X)
        → (z ∈ xs)
        → (Σ (ys , zs) ꞉ List X × List X , (xs ＝ ys ◦ z • zs) × (z ∉ ys))
 split' z xs i = Cases (split z xs)
                  (λ (ν : z ∉ xs) → 𝟘-elim (i ν))
                  id

 ·-charac : (xs ys : List X)
          → ρ xs ＝ xs
          → ρ ys ＝ ys
          → ρ (xs ◦ ys) ＝ xs ◦ (Δ xs ys)
 ·-charac xs ys a b =
  ρ (xs ◦ ys)          ＝⟨ ρ-◦ xs ys ⟩
  ρ xs ◦ (Δ xs (ρ ys)) ＝⟨ ap₂ (λ -₁ -₂ → -₁ ◦ (Δ xs -₂)) a b ⟩
  xs ◦ (Δ xs ys)       ∎

 Δ-∘ : (xs ys zs : List X)
     → Δ (xs ◦ ys) zs ＝ Δ ys (Δ xs zs)
 Δ-∘ [] ys zs = refl
 Δ-∘ (x • xs) ys zs =
  Δ (x • xs ◦ ys) zs   ＝⟨ refl ⟩
  δ x (Δ (xs ◦ ys) zs) ＝⟨ ap (δ x) (Δ-∘ xs ys zs) ⟩
  δ x (Δ ys (Δ xs zs)) ＝⟨ δ-Δ-left x (Δ xs zs) ys ⟩
  Δ ys (δ x (Δ xs zs)) ＝⟨ refl ⟩
  Δ ys (Δ (x • xs) zs) ∎

 δ-Δ-right : (z : X) (xs ys : List X)
           → δ z (Δ ys xs) ＝ δ z (Δ (δ z ys) xs)
 δ-Δ-right z xs [] = refl
 δ-Δ-right z xs (y • ys) = h (d z y)
  where
   h : is-decidable (z ＝ y)
     → δ z (Δ (y • ys) xs) ＝ δ z (Δ (δ z (y • ys)) xs)
   h (inl refl) =
     δ z (Δ (z • ys) xs)       ＝⟨ refl ⟩
     δ z (δ z (Δ ys xs))       ＝⟨ δ-idemp z (Δ ys xs) ⟩
     δ z (Δ ys xs)             ＝⟨ δ-Δ-right z xs ys ⟩
     δ z (Δ (δ z ys) xs)       ＝⟨ (ap (λ - → δ z ( Δ - xs)) (δ-same z ys))⁻¹ ⟩
     δ z (Δ (δ z (z • ys)) xs) ∎

   h (inr u) =
    δ z (Δ (y • ys) xs)       ＝⟨ refl ⟩
    δ z (δ y (Δ ys xs))       ＝⟨ δ-swap z y (Δ ys xs) ⟩
    δ y (δ z (Δ ys xs))       ＝⟨ ap (δ y) (δ-Δ-right z xs ys) ⟩
    δ y (δ z (Δ (δ z ys) xs)) ＝⟨ δ-swap y z (Δ (δ z ys) xs) ⟩
    δ z (δ y (Δ (δ z ys) xs)) ＝⟨ refl ⟩
    δ z (Δ (y • δ z ys) xs)   ＝⟨ (ap (λ - → δ z (Δ - xs)) (δ-≠ z y ys u))⁻¹ ⟩
    δ z (Δ (δ z (y • ys)) xs) ∎

 ρ-Δ : (xs ys : List X)
    → ρ (Δ ys xs) ＝ Δ (ρ ys) (ρ xs)
 ρ-Δ xs [] = refl
 ρ-Δ xs (y • ys) =
  ρ (Δ (y • ys) xs)           ＝⟨ refl ⟩
  ρ (δ y (Δ ys xs))           ＝⟨ (δ-ρ-swap y (Δ ys xs))⁻¹ ⟩
  δ y (ρ (Δ ys xs))           ＝⟨ ap (δ y) (ρ-Δ xs ys) ⟩
  δ y (Δ (ρ ys) (ρ xs))       ＝⟨ δ-Δ-right y (ρ xs) (ρ ys) ⟩
  δ y (Δ (δ y (ρ ys)) (ρ xs)) ＝⟨ refl ⟩
  Δ (ρ (y • ys)) (ρ xs)       ∎

 δ-Δ : (z : X) (xs ys : List X)
     → δ z (Δ ys xs) ＝ Δ ys (δ z xs)
 δ-Δ = δ-Δ-left

 δ-Δ-cancel : (z : X) (xs ys : List X)
            → δ z (Δ (δ z ys) xs) ＝ Δ ys (δ z xs)
 δ-Δ-cancel z xs ys = (δ-Δ-right z xs ys)⁻¹ ∙ δ-Δ-left z xs ys

\end{code}
