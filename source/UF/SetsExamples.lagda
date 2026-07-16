Martin Escardo, July 2026.

Examples of sets in the sense of HoTT/UF, other than those given in
many other files.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.SetsExamples where

open import MLTT.Spartan
open import MLTT.List
open import UF.Hedberg
open import UF.Sets
open import UF.Subsingletons

module _ {X : 𝓤 ̇ } where

 private
  _≡_ : List X → List X → 𝓤 ̇
  []       ≡ []       = 𝟙
  []       ≡ (y ∷ ys) = 𝟘
  (x ∷ xs) ≡ []       = 𝟘
  (x ∷ xs) ≡ (y ∷ ys) = (x ＝ y) ×  (xs ≡ ys)

  ≡-refl : (l : List X) → l ≡ l
  ≡-refl []       = ⋆
  ≡-refl (x ∷ xs) = refl , ≡-refl xs

  to-≡ : (xs ys : List X) → xs ＝ ys → xs ≡ ys
  to-≡ xs ys p = transport (xs ≡_) p (≡-refl xs)

  from-≡ : (xs ys : List X) → xs ≡ ys → xs ＝ ys
  from-≡ []       []       ⋆          = refl
  from-≡ []       (y ∷ ys) e          = 𝟘-elim e
  from-≡ (x ∷ xs) []       e          = 𝟘-elim e
  from-≡ (x ∷ xs) (x ∷ ys) (refl , r) = ap (x ∷_) (from-≡ xs ys r)

  ≡-is-prop-valued : is-set X → (xs ys : List X) → is-prop (xs ≡ ys)
  ≡-is-prop-valued s []       []       = 𝟙-is-prop
  ≡-is-prop-valued s []       (y ∷ ys) = 𝟘-is-prop
  ≡-is-prop-valued s (x ∷ xs) []       = 𝟘-is-prop
  ≡-is-prop-valued s (x ∷ xs) (y ∷ ys) = ×-is-prop
                                          (s {x} {y})
                                          (≡-is-prop-valued s xs ys)

 lists-are-sets : is-set X → is-set (List X)
 lists-are-sets s = Id-collapsibles-are-sets c
  where
   c : Id-collapsible (List X)
   c {xs} {ys} = from-≡ xs ys ∘ to-≡ xs ys ,
                 (λ p q → ap (from-≡ xs ys)
                             (≡-is-prop-valued s xs ys
                               (to-≡ xs ys p)
                               (to-≡ xs ys q)))

\end{code}
