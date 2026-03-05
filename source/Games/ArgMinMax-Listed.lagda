Martin Escardo and Paulo Oliva, 3rd March 2026,
moved and refined from the alpha-beta file.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module Games.ArgMinMax-Listed
        {𝓤 𝓥 : Universe}
        (R : 𝓤 ̇ )
        (_<_ : R → R → 𝓥 ̇ )
        (δ : (r s : R) → is-decidable (r < s))
      where

open import MLTT.List
open import NotionsOfDecidability.Complemented

_≥_ _≤_ : R → R → 𝓥 ̇
r ≥ s = ¬ (r < s)
s ≤ r = r ≥ s

private
 min' max' : (r s : R) → is-decidable (r < s) → R

 min' r s (inl lt) = r
 min' r s (inr ge) = s

 max' r s (inl lt) = s
 max' r s (inr ge) = r

min max : R → R → R
min r s = min' r s (δ r s)
max r s = max' r s (δ r s)

open import MonadOnTypes.K
open K-definitions R

Min Max : {X : 𝓤 ̇ } → listed⁺ X → K X
Min (x₀ , xs , _) p = foldr (λ x → min (p x)) (p x₀) xs
Max (x₀ , xs , _) p = foldr (λ x → max (p x)) (p x₀) xs

private
 argmin' argmax' : {X : 𝓤 ̇ } (p : X → R) (x y : X) → is-decidable (p x < p y) → X

 argmin' p x y (inl le) = x
 argmin' p x y (inr ge) = y

 argmax' p x y (inl le) = y
 argmax' p x y (inr ge) = x

 argmin'-spec : {X : 𝓤 ̇ } (p : X → R) (x y : X) (d : is-decidable (p x < p y))
              → p (argmin' p x y d) ＝ min' (p x) (p y) d
 argmin'-spec p x y (inl lt) = refl
 argmin'-spec p x y (inr ge) = refl

 argmax'-spec : {X : 𝓤 ̇ } (p : X → R) (x y : X) (d : is-decidable (p x < p y))
              → p (argmax' p x y d) ＝ max' (p x) (p y) d
 argmax'-spec p x y (inl lt) = refl
 argmax'-spec p x y (inr ge) = refl


argmin argmax : {X : 𝓤 ̇ } → (X → R) → X → X → X

argmin p x y = argmin' p x y (δ (p x) (p y))
argmax p x y = argmax' p x y (δ (p x) (p y))


argmin-spec : {X : 𝓤 ̇ } (p : X → R) (x y : X)
            → p (argmin p x y) ＝ min (p x) (p y)
argmin-spec p x y = argmin'-spec p x y (δ (p x) (p y))

argmax-spec : {X : 𝓤 ̇ } (p : X → R) (x y : X)
            → p (argmax p x y) ＝ max (p x) (p y)
argmax-spec p x y = argmax'-spec p x y (δ (p x) (p y))

open import MonadOnTypes.J
open J-definitions R

ArgMin ArgMax : {X : 𝓤 ̇ } → listed⁺ X → J X
ArgMin (x₀ , xs , _) p = foldr (argmin p) x₀ xs
ArgMax (x₀ , xs , _) p = foldr (argmax p) x₀ xs

open import MonadOnTypes.JK R

ArgMin-spec : {X : 𝓤 ̇ } (ℓ : listed⁺ X) → (ArgMin ℓ) attains (Min ℓ)
ArgMin-spec {X} (x₀ , xs , m) p = I xs
 where
  I : (xs : List X)
    → p (foldr (argmin p) x₀ xs) ＝ foldr (λ x → min (p x)) (p x₀) xs
  I [] = refl
  I (x ∷ xs) = I₀
   where
    IH : p (foldr (argmin p) x₀ xs) ＝ foldr (λ x → min (p x)) (p x₀) xs
    IH = I xs

    I₀ = p (argmin p x (foldr (argmin p) x₀ xs))         ＝⟨ I₁ ⟩
         min (p x) (p (foldr (argmin p) x₀ xs))          ＝⟨ I₂ ⟩
         min (p x) (foldr (λ x₁ → min (p x₁)) (p x₀) xs) ∎
          where
           I₁ = argmin-spec p x (foldr (argmin p) x₀ xs)
           I₂ = ap (min (p x)) IH

ArgMax-spec : {X : 𝓤 ̇ } (ℓ : listed⁺ X) → (ArgMax ℓ) attains (Max ℓ)
ArgMax-spec {X} (x₀ , xs , m) p = I xs
 where
  I : (xs : List X)
    → p (foldr (argmax p) x₀ xs) ＝ foldr (λ x → max (p x)) (p x₀) xs
  I [] = refl
  I (x ∷ xs) = I₀
   where
    IH : p (foldr (argmax p) x₀ xs) ＝ foldr (λ x → max (p x)) (p x₀) xs
    IH = I xs

    I₀ = p (argmax p x (foldr (argmax p) x₀ xs))         ＝⟨ I₁ ⟩
         max (p x) (p (foldr (argmax p) x₀ xs))          ＝⟨ I₂ ⟩
         max (p x) (foldr (λ x₁ → max (p x₁)) (p x₀) xs) ∎
          where
           I₁ = argmax-spec p x (foldr (argmax p) x₀ xs)
           I₂ = ap (max (p x)) IH

\end{code}
