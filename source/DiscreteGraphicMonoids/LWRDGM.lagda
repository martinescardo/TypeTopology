Martin Escardo and Paulo Oliva, April 2024

The type of lists without repetitions over a discrete type forms a discrete
graphic monoid. In DiscreteGraphicMonoids.Free, we prove that it gives the free
discrete graphic monoid.

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
  d = discrete'-gives-discrete

 graphical⁻ : graphical (_·_ {𝓤} {X})
 graphical⁻ (xs , a) (ys , b) =
  to-List⁻-＝
   (ρ (ρ (xs ◦ ys) ◦ xs)               ＝⟨ ρ-left (xs ◦ ys) xs ⟩
    ρ ((xs ◦ ys) ◦ xs)                 ＝⟨ ρ-◦ (xs ◦ ys) xs ⟩
    ρ (xs ◦ ys) ◦ (Δ (xs ◦ ys) (ρ xs)) ＝⟨ ap (ρ (xs ◦ ys) ◦_) (ρ-all xs ys) ⟩
    ρ (xs ◦ ys) ◦ []                   ＝⟨ ([]-right-neutral (ρ (xs ◦ ys)))⁻¹ ⟩
    ρ (xs ◦ ys)                        ∎)

\end{code}

The discrete graphic monoid of lists without repetition over a
discrete type.

\begin{code}

List⁻-DGM : (X : 𝓤 ̇ ) {{d : is-discrete' X}} → DGM 𝓤
List⁻-DGM X =
 List⁻ X  ,
 ([]⁻ , _·_) ,
 List⁻-is-discrete ,
 []⁻-left-neutral ,
 []⁻-right-neutral ,
 ·-assoc ,
 graphical⁻

\end{code}
