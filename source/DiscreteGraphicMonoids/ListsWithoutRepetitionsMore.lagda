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
          → ρ (xs ◦ ys) ＝ xs ◦ (ys ∖ xs)
 ·-charac xs ys a b =
  ρ (xs ◦ ys)        ＝⟨ ρ-◦ xs ys ⟩
  ρ xs ◦ (ρ ys ∖ xs) ＝⟨ ap₂ (λ -₁ -₂ → -₁ ◦ (-₂ ∖ xs)) a b ⟩
  xs ◦ (ys ∖ xs)     ∎

 ∖-∘ : (xs ys zs : List X)
     → zs ∖ (xs ◦ ys) ＝ (zs ∖ xs) ∖ ys
 ∖-∘ [] ys zs = refl
 ∖-∘ (x • xs) ys zs =
  zs ∖ (x • xs ◦ ys)   ＝⟨ refl ⟩
  δ x (zs ∖ (xs ◦ ys)) ＝⟨ ap (δ x) (∖-∘ xs ys zs) ⟩
  δ x ((zs ∖ xs) ∖ ys) ＝⟨ δ-∖-left x (zs ∖ xs) ys ⟩
  (δ x (zs ∖ xs) ∖ ys) ＝⟨ refl ⟩
  (zs ∖ (x • xs)) ∖ ys ∎

 δ-∖-right : (z : X) (xs ys : List X)
           → δ z (xs ∖ ys) ＝ δ z (xs ∖ δ z ys)
 δ-∖-right z xs [] = refl
 δ-∖-right z xs (y • ys) = h (d z y)
  where
   h : is-decidable (z ＝ y)
     → δ z (xs ∖ (y • ys)) ＝ δ z (xs ∖ δ z (y • ys))
   h (inl refl) =
     δ z (xs ∖ (z • ys))     ＝⟨ refl ⟩
     δ z (δ z (xs ∖ ys))     ＝⟨ δ-idemp z (xs ∖ ys) ⟩
     δ z (xs ∖ ys)           ＝⟨ δ-∖-right z xs ys ⟩
     δ z (xs ∖ δ z ys)       ＝⟨ (ap (λ - → δ z (xs ∖ -)) (δ-same z ys))⁻¹ ⟩
     δ z (xs ∖ δ z (z • ys)) ∎

   h (inr u) =
    δ z (xs ∖ (y • ys))     ＝⟨ refl ⟩
    δ z (δ y (xs ∖ ys))     ＝⟨ δ-swap z y (xs ∖ ys) ⟩
    δ y (δ z (xs ∖ ys))     ＝⟨ ap (δ y) (δ-∖-right z xs ys) ⟩
    δ y (δ z (xs ∖ δ z ys)) ＝⟨ δ-swap y z (xs ∖ δ z ys) ⟩
    δ z (δ y (xs ∖ δ z ys)) ＝⟨ refl ⟩
    δ z (xs ∖ (y • δ z ys)) ＝⟨ (ap (λ - → δ z (xs ∖ -)) (δ-≠ z y ys u))⁻¹ ⟩
    δ z (xs ∖ δ z (y • ys)) ∎

 ρ-∖ : (xs ys : List X)
    → ρ (xs ∖ ys) ＝ ρ xs ∖ ρ ys
 ρ-∖ xs [] = refl
 ρ-∖ xs (y • ys) =
  ρ (xs ∖ (y • ys))       ＝⟨ refl ⟩
  ρ (δ y (xs ∖ ys))       ＝⟨ (δ-ρ-swap y (xs ∖ ys))⁻¹ ⟩
  δ y (ρ (xs ∖ ys))       ＝⟨ ap (δ y) (ρ-∖ xs ys) ⟩
  δ y (ρ xs ∖ ρ ys)       ＝⟨ δ-∖-right y (ρ xs) (ρ ys) ⟩
  δ y (ρ xs ∖ δ y (ρ ys)) ＝⟨ refl ⟩
  ρ xs ∖ ρ (y • ys)       ∎

 δ-∖ : (z : X) (xs ys : List X)
     → δ z (xs ∖ ys) ＝ δ z xs ∖ ys
 δ-∖  = δ-∖-left

 δ-∖-cancel : (z : X) (xs ys : List X)
            → δ z (xs ∖ δ z ys) ＝ δ z xs ∖ ys
 δ-∖-cancel z xs ys = (δ-∖-right z xs ys)⁻¹ ∙ δ-∖-left z xs ys

\end{code}
