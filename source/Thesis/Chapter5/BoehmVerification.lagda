\begin{code}
{-# OPTIONS --allow-unsolved-metas --exact-split --without-K --auto-inline
            --experimental-lossy-unification #-}

open import Integers.Addition renaming (_+_ to _ℤ+_;  _-_ to _ℤ-_)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Negation renaming (-_ to ℤ-_ )
open import Integers.Order
open import Integers.Type
open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.Order
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Order hiding (≤-refl)
open import UF.Base
open import UF.FunExt
open import UF.Powerset hiding (𝕋)
open import UF.PropTrunc
open import UF.Quotient
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Thesis.AndrewSneap.DyadicRationals renaming (normalise to ι)
open import Thesis.Chapter5.PLDIPrelude

module Thesis.Chapter5.BoehmVerification
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (dy : Dyadics)
  where

_≡_ = Id

open import Thesis.AndrewSneap.DyadicReals pe pt fe dy renaming (located to located')

downLeft downMid downRight : ℤ → ℤ
downLeft  k = (k ℤ+ k)
downMid   k = (k ℤ+ k) +pos 1
downRight k = (k ℤ+ k) +pos 2

upRight upLeft : ℤ → ℤ
upRight k = sign k (num k /2)
upLeft  k = upRight (predℤ k)

_below_ : ℤ → ℤ → 𝓤₀ ̇
a below b = downLeft b ≤ a ≤ downRight b

fully-ternary : (ℤ → ℤ) → 𝓤₀  ̇
fully-ternary x = (δ : ℤ) → x (succℤ δ) below x δ

𝕋 : 𝓤₀ ̇ 
𝕋 = Σ x ꞉ (ℤ → ℤ) , fully-ternary x

open Dyadics dy
  renaming ( _ℤ[1/2]+_ to _+_ ; ℤ[1/2]-_ to -_ ; _ℤ[1/2]-_ to _-_
           ; _ℤ[1/2]*_ to _*_ )
                                    
open import Naturals.Order
  renaming (max to ℕmax) hiding (≤-refl ; ≤-trans ; ≤-split)

ℤ[1/2]² : 𝓤₀ ̇
ℤ[1/2]² = Σ (l , r) ꞉ (ℤ[1/2] × ℤ[1/2]) , l ≤ r

ld rd : ℤ[1/2] × ℤ[1/2] → ℤ[1/2]
ld (l , r) = l
rd (l , r) = r

_covers_ : ℤ[1/2] × ℤ[1/2] → ℤ[1/2] × ℤ[1/2] → 𝓤₀ ̇
a covers b = (ld a ≤ ld b) × (rd b ≤ rd a)

covers-refl : (ab : ℤ[1/2] × ℤ[1/2]) → ab covers ab
covers-refl (a , b) = ≤-refl a , ≤-refl b

covers-trans : (a b c : ℤ[1/2] × ℤ[1/2]) → a covers b → b covers c → a covers c
covers-trans a b c (l≤₁ , r≤₁) (l≤₂ , r≤₂)
 = trans' (ld a) (ld b) (ld c) l≤₁ l≤₂
 , trans' (rd c ) (rd b) (rd a) r≤₂ r≤₁

nested located : (ℤ → ℤ[1/2] × ℤ[1/2]) → 𝓤₀ ̇
nested      ζ = (n : ℤ) → (ζ n) covers (ζ (succℤ n))
located     ζ = (ϵ : ℤ[1/2]) → is-positive ϵ
              → Σ n ꞉ ℤ , (pr₂ (ζ n) - pr₁ (ζ n)) ≤ ϵ

⦅_⦆ : (χ : ℤ → ℤ[1/2]²)
      → nested (pr₁ ∘ χ) → located (pr₁ ∘ χ)
      → ℝ-d
⦅_⦆ = {!!}

ℤ³ : 𝓤₀ ̇
ℤ³ = Σ ((l , r) , p) ꞉ ((ℤ × ℤ) × ℤ) , l ≤ r

η : ℤ³ → ℤ[1/2]²
η (((l , r) , p) , i) = ((ι (l , p)) , ι (r , p)) , {!!}

⦅_⦆' : (χ : ℤ → ℤ³)
      → nested (pr₁ ∘ η ∘ χ) → located (pr₁ ∘ η ∘ χ)
      → ℝ-d
⦅ χ ⦆' = ⦅ η ∘ χ ⦆

ℤ² : 𝓤₀ ̇ 
ℤ² = ℤ × ℤ

to-dcode : ℤ² → ℤ³
to-dcode (k , p) = (((k , k +pos 2) , p) , {!!})

ρ : ℤ² → ℤ[1/2]²
ρ = η ∘ to-dcode

⦅_⦆'' : (χ : ℤ → ℤ²)
        → nested  (pr₁ ∘ ρ ∘ χ) -- DIFFERS FROM PAPER
        → located (pr₁ ∘ ρ ∘ χ) -- DIFFERS FROM PAPER
        → ℝ-d
⦅_⦆'' = ⦅_⦆' ∘ (to-dcode ∘_)

to-interval-seq : 𝕋 → (ℤ → ℤ²)
to-interval-seq χ n = (pr₁ χ n) , n
\end{code}

Prenormalising

\begin{code}
is-prenormalised : (ℤ → ℤ²) → 𝓤₀ ̇
is-prenormalised χ = (n : ℤ) → pr₂ (χ n) ≥ n

prenormalise : (χ : ℤ → ℤ²) → located (pr₁ ∘ ρ ∘ χ)
             → ℤ → ℤ²
prenormalise χ π n = χ (pr₁ (π (ι (pos 1 , {!pos!})) {!!}))

prenormalised-located : (χ : ℤ → ℤ²)
                      → is-prenormalised χ
                      → located (pr₁ ∘ ρ ∘ χ)
prenormalised-located χ p ϵ _ = {!!}

prenormalise-prenormalised
 : (χ : ℤ → ℤ²) (π : located (pr₁ ∘ ρ ∘ χ))
 → is-prenormalised (prenormalise χ π)
prenormalise-prenormalised = {!!}

prenormalise-nested : (χ : ℤ → ℤ²) (π : located (pr₁ ∘ ρ ∘ χ))
                    → nested (pr₁ ∘ ρ ∘ χ)
                    → nested (pr₁ ∘ ρ ∘ prenormalise χ π)
prenormalise-nested = {!!}

prenormalise-same-real
 : (χ : ℤ → ℤ²)
 → (τ : nested (pr₁ ∘ ρ ∘ χ)) (π : located (pr₁ ∘ ρ ∘ χ))
 → Id (⦅ χ ⦆'' τ π)
      (⦅ prenormalise χ π ⦆''
          (prenormalise-nested χ π τ)
          (prenormalised-located (prenormalise χ π)
            (prenormalise-prenormalised χ π)))
prenormalise-same-real = {!!}
\end{code}

Normalising

\begin{code}
is-normalised : (ℤ → ℤ²) → 𝓤₀ ̇ 
is-normalised χ = (n : ℤ) → pr₂ (χ n) ＝ n

normalised-prenormalised : (χ : ℤ → ℤ²)
                         → is-normalised χ
                         → is-prenormalised χ 
normalised-prenormalised χ ρ n = 0 , (ρ n ⁻¹)

normalised-located : (χ : ℤ → ℤ²)
                   → is-normalised χ
                   → located (pr₁ ∘ ρ ∘ χ)
normalised-located χ
 = prenormalised-located χ
 ∘ normalised-prenormalised χ

normalise' : (χ : ℤ → ℤ²) → is-prenormalised χ → (ℤ → ℤ²)
normalise' = {!!} -- in other file

normalise'-normalised : (χ : ℤ → ℤ²) (p : is-prenormalised χ)
                      → is-normalised (normalise' χ p)
normalise'-normalised = {!!} -- in other file

normalise'-nested : (χ : ℤ → ℤ²) (p : is-prenormalised χ)
                  → nested (pr₁ ∘ ρ ∘ χ)
                  → nested (pr₁ ∘ ρ ∘ normalise' χ p)
normalise'-nested = {!!} -- in other file

normalise'-same-real
 : (χ : ℤ → ℤ²)
 → (τ : nested (pr₁ ∘ ρ ∘ χ))
 → (p : is-prenormalised χ)
 → Id (⦅ χ ⦆'' τ (prenormalised-located χ p))
      (⦅ normalise' χ p ⦆''
          (normalise'-nested χ p τ)
          (normalised-located (normalise' χ p)
            (normalise'-normalised χ p)))
normalise'-same-real = {!!}

\end{code}

Prenormalising composed with normalising

\begin{code}

normalise : (χ : ℤ → ℤ²) → located (pr₁ ∘ ρ ∘ χ) → (ℤ → ℤ²)
normalise χ π
 = normalise' (prenormalise χ π)
     (prenormalise-prenormalised χ π)

normalise-normalised : (χ : ℤ → ℤ²) (π : located (pr₁ ∘ ρ ∘ χ))
                     → is-normalised (normalise χ π)
normalise-normalised χ π
 = normalise'-normalised (prenormalise χ π)
     (prenormalise-prenormalised χ π)

normalise-nested : (χ : ℤ → ℤ²) (π : located (pr₁ ∘ ρ ∘ χ))
                 → nested (pr₁ ∘ ρ ∘ χ)
                 → nested (pr₁ ∘ ρ ∘ normalise χ π)
normalise-nested χ π τ
 = normalise'-nested (prenormalise χ π)
     (prenormalise-prenormalised χ π)
     (prenormalise-nested χ π τ)

normalise-same-real
 : (χ : ℤ → ℤ²)
 → (τ : nested  (pr₁ ∘ ρ ∘ χ))
 → (π : located (pr₁ ∘ ρ ∘ χ))
 → Id (⦅ χ ⦆'' τ π)
      (⦅ normalise χ π ⦆''
          (normalise-nested χ π τ)
          (normalised-located (normalise χ π)
            (normalise-normalised χ π)))
normalise-same-real χ τ π
 = {!!}

\end{code}

From normalised sequences to ternary boehm encodings

\begin{code}
ternary-nested : (χ : ℤ → ℤ²)
               → is-normalised χ
               → fully-ternary (pr₁ ∘ χ) ⇔ nested (pr₁ ∘ ρ ∘ χ)
ternary-nested = {!!}

𝕋→nested-normalised : 𝕋 → Σ χ ꞉ (ℤ → ℤ²)
                    , (nested (pr₁ ∘ ρ ∘ χ) -- DIFFERS FROM PAPER
                    × is-normalised χ)
𝕋→nested-normalised χ
 = to-interval-seq χ
 , pr₁ (ternary-nested _ i) (pr₂ χ)
 , i
 where
   i : is-normalised (to-interval-seq χ)
   i n = refl

𝕋→nested-located : 𝕋 → Σ χ ꞉ (ℤ → ℤ²)
                 , (nested (pr₁ ∘ ρ ∘ χ)
                 × located (pr₁ ∘ ρ ∘ χ))
𝕋→nested-located χ
 = χ' , τ , normalised-located χ' π
 where
  γ = 𝕋→nested-normalised χ
  χ' = pr₁ γ 
  τ  = pr₁ (pr₂ γ)
  π  = pr₂ (pr₂ γ)

ternary-normalised→𝕋 : Σ χ ꞉ (ℤ → ℤ²)
                     , (nested (pr₁ ∘ ρ ∘ χ)
                     × is-normalised χ)
                     → 𝕋
ternary-normalised→𝕋 χ = {!!}

⟦_⟧ : 𝕋 → ℝ-d
⟦ χ ⟧ = ⦅ χ' ⦆'' τ π
 where
  γ = 𝕋→nested-located χ
  χ' = pr₁ γ 
  τ  = pr₁ (pr₂ γ)
  π  = pr₂ (pr₂ γ)

-- Exact real arithmetic

join' : ℤ³ → ℤ²
join' = {!!}

join : (ℤ → ℤ³) → (ℤ → ℤ²)
join χ n = join' (χ n)

join'-covers : (a : ℤ³) → (pr₁ ∘ ρ ∘ join') a covers (pr₁ ∘ η) a
join'-covers = {!!}

join'-needed : (a b : ℤ³)
             → (pr₁ ∘ η)         a covers (pr₁ ∘ η)         b
             → (pr₁ ∘ ρ ∘ join') a covers (pr₁ ∘ ρ ∘ join') b
join'-needed = {!!}

join-nested : (χ : ℤ → ℤ³) → nested (pr₁ ∘ η ∘ χ) → nested (pr₁ ∘ ρ ∘ join χ)
join-nested χ τ n = join'-needed (χ n) (χ (succℤ n)) (τ n) 

join-located : (χ : ℤ → ℤ³) → located (pr₁ ∘ η ∘ χ) → located (pr₁ ∘ ρ ∘ join χ)
join-located χ π = {!!}

join-same-real : (χ : ℤ → ℤ³)
               → (τ : nested  (pr₁ ∘ η ∘ χ))
               → (π : located (pr₁ ∘ η ∘ χ))
               → Id (⦅ χ ⦆' τ π)
                    (⦅ (join χ) ⦆'' (join-nested _ τ) (join-located _ π))
join-same-real = {!!}

module _
  {d : ℕ}
  (f : Vec ℝ-d d → ℝ-d)
  (A : Vec ℤ³  d → ℤ³ )
  (A-function : (as : Vec ℤ³ d) (ws : Vec ℝ-d d) -- DIFFERS FROM PAPER
              → pairwise₂
                  (λ (a , b) w → (ℤ[1/2]-to-ℝ-d a) ℝ-d≤ w
                               × w ℝ-d≤ (ℤ[1/2]-to-ℝ-d b))
                  (vec-map (pr₁ ∘ η) as) ws
              → ((ℤ[1/2]-to-ℝ-d ((pr₁ ∘ pr₁ ∘ η) (A as))) ℝ-d≤ f ws)
              × (f ws ℝ-d≤ (ℤ[1/2]-to-ℝ-d ((pr₂ ∘ pr₁ ∘ η) (A as)))))
  (A-nested   : (as bs : Vec ℤ³ d)
              → pairwise₂ _covers_ (vec-map (pr₁ ∘ η) as) (vec-map (pr₁ ∘ η) bs)
              → (pr₁ ∘ η) (A as) covers (pr₁ ∘ η) (A bs))
  (A-located  : (as : Vec ℤ³ d)
              → (ϵ : ℤ[1/2]) → is-positive ϵ → Σ δs ꞉ Vec ℤ[1/2] d
              , ((bs : Vec ℤ³ d)
                → pairwise₂ _covers_ (vec-map (pr₁ ∘ η) as) (vec-map (pr₁ ∘ η) bs)
                → pairwise₂ _≤_ (vec-map ((λ (x , y) → y - x) ∘ pr₁ ∘ η) as) δs
                → let ((Ak , Ac) , _) = η (A as) in (Ac - Ak) ≤ ϵ))
  -- DIFFERS FROM PAPER
  where

 f' : Vec (ℤ → ℤ³) d → (ℤ → ℤ³)
 f' χs n = A (vec-map (λ χ → χ n) χs)

 f'-nested : (χs : Vec (Σ χ ꞉ (ℤ → ℤ³)
                        , nested  (pr₁ ∘ η ∘ χ)
                        × located (pr₁ ∘ η ∘ χ)) d)
           → nested (pr₁ ∘ η ∘ f' (vec-map pr₁ χs))
 f'-nested χs n = A-nested
                    (vec-map (λ χ → χ n) (vec-map pr₁ χs))
                    (vec-map (λ χ → χ (succℤ n)) (vec-map pr₁ χs))
                    (γ χs)
  where
   γ : {m : ℕ} → (χs : Vec (Σ χ ꞉ (ℤ → ℤ³)
                      , nested  (pr₁ ∘ η ∘ χ)
                      × located (pr₁ ∘ η ∘ χ)) m)
     → pairwise₂ _covers_
       (vec-map (pr₁ ∘ η) (vec-map (λ χ → χ n) (vec-map pr₁ χs)))
       (vec-map (pr₁ ∘ η) (vec-map (λ χ → χ (succℤ n)) (vec-map pr₁ χs)))
   γ [] = ⋆
   γ ((x , τ , _) ∷ χs) = τ n , γ χs

 vec-fold : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {n : ℕ}
          → B → (A → B → B) → Vec A n → B
 vec-fold b f [] = b
 vec-fold b f (x ∷ as) = vec-fold (f x b) f as

 f'-located : (χs : Vec (Σ χ ꞉ (ℤ → ℤ³)
                        , nested  (pr₁ ∘ η ∘ χ)
                        × located (pr₁ ∘ η ∘ χ)) d)
            → located (pr₁ ∘ η ∘ f' (vec-map pr₁ χs))
 f'-located χs ϵ i = {!!}

 f'-same-real : (χs : Vec (Σ χ ꞉ (ℤ → ℤ³)
                    , nested  (pr₁ ∘ η ∘ χ)
                    × located (pr₁ ∘ η ∘ χ)) d)
              → Id (f (vec-map (λ (χ , τ , π) → ⦅ χ ⦆' τ π) χs))
                   (⦅ f' (vec-map pr₁ χs) ⦆' (f'-nested χs) (f'-located χs))
 f'-same-real χs = same-cuts-gives-equality _ _
                     (λ p p≤f → pr₁ (A-function {!!} {!!} {!!}))
                     {!!} {!!} {!!}

 f''-aux : Vec (ℤ → ℤ²) d → (ℤ → ℤ³)
 f''-aux χs = f' (vec-map (to-dcode ∘_) χs)

 f''-aux-transport
  : {n : ℕ} → (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                         , nested  (pr₁ ∘ ρ ∘ χ)
                         × located (pr₁ ∘ ρ ∘ χ)) n)
  → Id (vec-map
         (pr₁ {𝓤₀} {𝓤₀} {(x : ℤ) → ℤ³}
              {λ χ → nested (pr₁ ∘ η ∘ χ) × located (pr₁ ∘ η ∘ χ)})
         (vec-map (λ (χ , τ , π) → to-dcode ∘ χ , τ , π) χs))
       (vec-map (to-dcode ∘_) (vec-map pr₁ χs))
 f''-aux-transport [] = refl
 f''-aux-transport ((x , _) ∷ χs) = ap ((to-dcode ∘ x) ∷_)
                                      (f''-aux-transport χs)

 f''-aux-nested : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                        , nested  (pr₁ ∘ ρ ∘ χ)
                        × located (pr₁ ∘ ρ ∘ χ)) d)
                → nested (pr₁ ∘ η ∘ f''-aux (vec-map pr₁ χs))
 f''-aux-nested χs
  = transport nested
      (dfunext (fe _ _ )
      (λ n → ap (λ - → (pr₁ ∘ η ∘ f' -) n)
        (f''-aux-transport χs)))
      (f'-nested (vec-map (λ (χ , τ , π) → to-dcode ∘ χ , τ , π) χs))

 f''-aux-located : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                        , nested  (pr₁ ∘ ρ ∘ χ)
                        × located (pr₁ ∘ ρ ∘ χ)) d)
            → located (pr₁ ∘ η ∘ f''-aux (vec-map pr₁ χs))
 f''-aux-located χs
  = transport located
      (dfunext (fe _ _ )
      (λ n → ap (λ - → (pr₁ ∘ η ∘ f' -) n)
        (f''-aux-transport χs)))
      (f'-located (vec-map (λ (χ , τ , π) → to-dcode ∘ χ , τ , π) χs))

 f''-aux-same-real : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                    , nested  (pr₁ ∘ ρ ∘ χ)
                    × located (pr₁ ∘ ρ ∘ χ)) d)
              → Id (f (vec-map (λ (χ , τ , π) → ⦅ χ ⦆'' τ π) χs))
                   (⦅ f''-aux (vec-map pr₁ χs) ⦆'
                       (f''-aux-nested χs) (f''-aux-located χs))
 f''-aux-same-real χs
  = ap f (vec-map-∼
      (λ (χ , τ , π) → to-dcode ∘ χ , τ , π)
      (λ (χ , τ , π) → ⦅ χ ⦆' τ π) χs)
  ∙ f'-same-real
      (vec-map (λ (χ , τ , π) → to-dcode ∘ χ , τ , π) χs)
  ∙ {!!}

 f'' : Vec (ℤ → ℤ²) d → (ℤ → ℤ²)
 f'' = join ∘ f''-aux

 f''-nested : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                         , nested  (pr₁ ∘ ρ ∘ χ)
                         × located (pr₁ ∘ ρ ∘ χ)) d)
            → nested (pr₁ ∘ ρ ∘ f'' (vec-map pr₁ χs))
 f''-nested χs = join-nested (f''-aux (vec-map pr₁ χs))
                   (f''-aux-nested χs)

 f''-located : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                        , nested  (pr₁ ∘ ρ ∘ χ)
                        × located (pr₁ ∘ ρ ∘ χ)) d)
            → located (pr₁ ∘ ρ ∘ f'' (vec-map pr₁ χs))
 f''-located χs = join-located (f''-aux (vec-map pr₁ χs))
                    (f''-aux-located χs)

 f''-same-real : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
               , nested  (pr₁ ∘ ρ ∘ χ)
               × located (pr₁ ∘ ρ ∘ χ)) d)
               → Id (f (vec-map (λ (χ , τ , π) → ⦅ χ ⦆'' τ π) χs))
                     (⦅ f'' (vec-map pr₁ χs) ⦆''
                       (f''-nested χs) (f''-located χs))
 f''-same-real χs = join-same-real (f''-aux (vec-map pr₁ χs))
                      (join-nested (f''-aux (vec-map pr₁ χs))
                        (f''-aux-nested χs))
                      (join-located (f''-aux (vec-map pr₁ χs))
                        (f''-aux-located χs))

 f*-aux : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
              , nested  (pr₁ ∘ ρ ∘ χ)
              × located (pr₁ ∘ ρ ∘ χ)) d)
        → (ℤ → ℤ²)
 f*-aux χs = normalise (f'' (vec-map pr₁ χs)) (f''-located χs)

 f*-aux-nested : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                         , nested  (pr₁ ∘ ρ ∘ χ)
                         × located (pr₁ ∘ ρ ∘ χ)) d)
               → nested (pr₁ ∘ ρ ∘ f*-aux χs)
 f*-aux-nested χs = normalise-nested (f'' (vec-map pr₁ χs))
                      (f''-located χs)
                      (f''-nested χs)

 f*-aux-normalised : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                         , nested  (pr₁ ∘ ρ ∘ χ)
                         × located (pr₁ ∘ ρ ∘ χ)) d)
                   → is-normalised (f*-aux χs)
 f*-aux-normalised χs = normalise-normalised _ (f''-located χs)

 f*-aux-located : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                      , nested  (pr₁ ∘ ρ ∘ χ)
                      × located (pr₁ ∘ ρ ∘ χ)) d)
                → located (pr₁ ∘ ρ ∘ f*-aux χs)
 f*-aux-located χs = normalised-located (f*-aux χs)
                       (f*-aux-normalised χs)

 f*-aux-same-real : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                      , nested  (pr₁ ∘ ρ ∘ χ)
                      × located (pr₁ ∘ ρ ∘ χ)) d)
                  → f (vec-map (λ (χ , τ , π) → ⦅ χ ⦆'' τ π) χs)
                  ≡ ⦅ f*-aux χs ⦆'' (f*-aux-nested χs) (f*-aux-located χs)
 f*-aux-same-real χs
  = f''-same-real χs
  ∙ normalise-same-real (f'' (vec-map pr₁ χs))
      (f''-nested χs)
      (f''-located χs)

 f* : Vec 𝕋 d → 𝕋
 f* χs = ternary-normalised→𝕋
           ( f*-aux            ζs
           , f*-aux-nested     ζs
           , f*-aux-normalised ζs)
  where
   ζs  = vec-map 𝕋→nested-located χs

 f*-same-real : (χs : Vec 𝕋 d)
              → f (vec-map ⟦_⟧ χs) ≡ ⟦ f* χs ⟧
 f*-same-real χs
  = ap f (vec-map-∼ 𝕋→nested-located (λ (χ , τ , π) → ⦅ χ ⦆'' τ π) χs)
  ∙ f*-aux-same-real (vec-map 𝕋→nested-located χs)
  ∙ {!!}

\end{code}
