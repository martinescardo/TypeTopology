Martin Escardo, Paulo Oliva, circa March 2024

Non-empty list monad.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module MonadOnTypesMGU.NonEmptyList where

open import MonadOnTypesMGU.Construction

data neList (X : 𝓤 ̇ ) : 𝓤 ̇ where
 [_]  : X → neList X
 _::_ : X → neList X → neList X

infixr 3 _::_
infixr 2 _++_

_++_ : {X : 𝓤 ̇ } → neList X → neList X → neList X
[ x ] ++ ys     = x :: ys
(x :: xs) ++ ys = x :: (xs ++ ys)

assoc-++ : {X : 𝓤 ̇ } (xs ys zs : neList X) → (xs ++ ys) ++ zs ＝ xs ++ (ys ++ zs)
assoc-++ [ x ]     ys zs = refl
assoc-++ (x :: xs) ys zs = ap (x ::_) (assoc-++ xs ys zs)

𝕃⁺ : Monad {λ 𝓤 → 𝓤}
𝕃⁺ = record {
 functor = neList ;
 η       = [_] ;
 ext     = ext' ;
 ext-η   = ext'-η ;
 unit    = λ f x → refl ;
 assoc   = assoc'
 }
 where
  ext' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → neList Y) → neList X → neList Y
  ext' f [ x ]     = f x
  ext' f (x :: xs) = f x ++ ext' f xs

  ext'-++ : {Y : 𝓤 ̇ } {Z : 𝓥 ̇ }
            (g : Y → neList Z)
            (xs ys : neList Y)
          → ext' g xs ++ ext' g ys ＝ ext' g (xs ++ ys)
  ext'-++ g [ x ]     ys = refl
  ext'-++ g (x :: xs) ys =
   ext' g (x :: xs) ++ ext' g ys   ＝⟨refl⟩
   (g x ++ ext' g xs) ++ ext' g ys ＝⟨ assoc-++ (g x) (ext' g xs) (ext' g ys) ⟩
   g x ++ (ext' g xs ++ ext' g ys) ＝⟨ ap (g x ++_) (ext'-++ g xs ys) ⟩
   g x ++ ext' g (xs ++ ys)        ＝⟨refl⟩
   ext' g (x :: xs ++ ys)          ∎

  ext'-η : {X : 𝓤 ̇ } → ext' [_] ∼ 𝑖𝑑 (neList X)
  ext'-η [ x ]     = refl
  ext'-η (x :: xs) = ap (x ::_) (ext'-η xs)

  assoc' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
           (g : Y → neList Z) (f : X → neList Y)
           (xs : neList X)
         → ext' (λ - → ext' g (f -)) xs ＝ ext' g (ext' f xs)
  assoc' g f [ x ]     = refl
  assoc' g f (x :: xs) =
   ext' (λ - → ext' g (f -)) (x :: xs)           ＝⟨refl⟩
   ext' g (f x) ++ ext' (λ - → ext' g (f -)) xs  ＝⟨ ap (ext' g (f x) ++_) (assoc' g f xs) ⟩
   ext' g (f x) ++ ext' g (ext' f xs)            ＝⟨ ext'-++ g (f x) (ext' f xs) ⟩
   ext' g (f x ++ ext' f xs)                     ＝⟨refl⟩
   ext' g (ext' f (x :: xs))                     ∎

module neList-definitions where

 _⊗ᴸ⁺_ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
      → neList X
      → ((x : X) → neList (Y x))
      → neList (Σ x ꞉ X , Y x)
 _⊗ᴸ⁺_ = _⊗_ 𝕃⁺

 ηᴸ⁺ : {X : 𝓤 ̇ } → X → neList X
 ηᴸ⁺ = η 𝕃⁺

 extᴸ⁺ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → neList Y) → neList X → neList Y
 extᴸ⁺ = ext 𝕃⁺

 mapᴸ⁺ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → neList X → neList Y
 mapᴸ⁺ = map 𝕃⁺

\end{code}
