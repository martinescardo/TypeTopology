Martin Escardo and Paulo Oliva, April 2024

The type of lists without repetitions over a discrete type form a
discrete graphic monoid. In another module, we prove that it gives the
free discrete graphic monoid.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DiscreteGraphicMonoids.LWRDGM
        (fe : Fun-Ext)
       where

open import DiscreteGraphicMonoids.ListsWithoutRepetitions fe
open import DiscreteGraphicMonoids.Type
open import MLTT.List
            renaming (_∷_ to _•_ ;          -- typed as \bub
                      _++_ to _◦_ ;         -- typed as \buw
                      ++-assoc to ◦-assoc)
open import MLTT.Spartan
open import UF.DiscreteAndSeparated

module _
         {𝓤 : Universe}
         {X : 𝓤 ̇ }
         {{d' : is-discrete' X}}
       where

 private
  d : is-discrete X
  d = discrete'-gives-discrete d'

 graphical⁻-lemma : (xs ys : List X)
                  → ρ ((xs ◦ ys) ◦ xs) ＝ ρ (xs ◦ ys)
 graphical⁻-lemma xs ys =
  ρ ((xs ◦ ys) ◦ xs)               ＝⟨ ρ-◦ (xs ◦ ys) xs ⟩
  ρ (xs ◦ ys) ◦ (ρ xs ∖ (xs ◦ ys)) ＝⟨ ap (ρ (xs ◦ ys) ◦_) (ρ-all xs ys) ⟩
  ρ (xs ◦ ys) ◦ []                 ＝⟨ ([]-right-neutral (ρ (xs ◦ ys)))⁻¹ ⟩
  ρ (xs ◦ ys)                      ∎

 graphical⁻ : graphical _·_
 graphical⁻ (xs , a) (ys , b) =
  to-List⁻-＝
   (ρ (ρ (xs ◦ ys) ◦ xs) ＝⟨ ρ-left (xs ◦ ys) xs ⟩
   ρ ((xs ◦ ys) ◦ xs)    ＝⟨ graphical⁻-lemma xs ys ⟩
   ρ (xs ◦ ys)           ∎)

\end{code}

The symbol ⊙ can be typed a "\o."

\begin{code}

List⁻-DGM : (X : 𝓤 ̇) {{d : is-discrete' X}} → DGM 𝓤
List⁻-DGM X {{d}} =
 List⁻ X  ,
 ([]⁻ , _·_) ,
 List⁻-is-discrete ,
 []⁻-left-neutral ,
 []⁻-right-neutral ,
 ·-assoc ,
 graphical⁻

\end{code}
