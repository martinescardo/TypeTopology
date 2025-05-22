Taken from the Advanced Functional Programming module lecture notes 2023-24

Formalises isomorphisms in Agda

\begin{code}
{-# OPTIONS --without-K --safe #-}

module TGH.AFP2024.isomorphisms where

open import MLTT.Spartan

module isomorphisms where
 private
  is-bijection : {A B : 𝓤₀ ̇ } → (A → B) → 𝓤₀ ̇ 
  is-bijection f = Σ g ꞉ (codomain f → domain f) , ((g ∘ f ∼ id) × (f ∘ g ∼ id))

  _≅_ : Type → Type → Type
  A ≅ B = Σ f ꞉ (A → B) , is-bijection f

record is-bijection {A B : 𝓤₀ ̇ } (f : A → B) : 𝓤₀ ̇  where
 constructor
  Inverse
 field
  inverse : B → A
  η       : inverse ∘ f ∼ id
  ε       : f ∘ inverse ∼ id

record _≅_ (A B : 𝓤₀ ̇ ) : 𝓤₀ ̇  where
 constructor
  Isomorphism
 field
  bijection   : A → B
  bijectivity : is-bijection bijection

infix 0 _≅_

\end{code}
