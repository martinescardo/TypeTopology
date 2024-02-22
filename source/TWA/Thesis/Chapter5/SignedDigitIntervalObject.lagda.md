[⇐ Index](../html/TWA.Thesis.index.html)

# Verification of signed-digit operations

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import Naturals.Addition renaming (_+_ to _+ℕ_)

open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter5.SignedDigit
open import TWA.Thesis.Chapter5.IntervalObject hiding (⟨_⟩)

module TWA.Thesis.Chapter5.SignedDigitIntervalObject
 {𝓦 : Universe}
 (fe : FunExt)
 (io : Interval-object fe 𝓦)
 where

open import TWA.Thesis.Chapter5.IntervalObjectApproximation fe io
open basic-interval-object-development fe io hiding (−1 ; O ; +1)
```

## Representation map

```
⟨_⟩ : 𝟛 → 𝕀
⟨ −1 ⟩ = u
⟨  O ⟩ = u ⊕ v
⟨ +1 ⟩ = v

⟪_⟫ : 𝟛ᴺ → 𝕀
⟪ α ⟫ = M (map ⟨_⟩ α)

_realises¹_ : (𝟛ᴺ → 𝟛ᴺ) → (𝕀 → 𝕀) → 𝓦  ̇
f realises¹ f' = (α : 𝟛ᴺ) → f' ⟪ α ⟫ ＝ ⟪ f α ⟫

_realises²_ : (𝟛ᴺ → 𝟛ᴺ → 𝟛ᴺ) → (𝕀 → 𝕀 → 𝕀) → 𝓦 ̇
f realises² f' = (α β : 𝟛ᴺ) → ⟪ f α β ⟫ ＝ f' ⟪ α ⟫ ⟪ β ⟫

_pw-realises¹_ : (𝟛 → 𝟛) → (𝕀 → 𝕀) → 𝓦 ̇
f pw-realises¹ f' = (a : 𝟛) → f' ⟨ a ⟩ ＝ ⟨ f a ⟩

_pw-realises²_ : (𝟛 → 𝟛 → 𝟛) → (𝕀 → 𝕀 → 𝕀) → 𝓦 ̇
f pw-realises² f' = (a b : 𝟛) → f' ⟨ a ⟩ ⟨ b ⟩ ＝ ⟨ f a b ⟩

_realises'_ : (𝟛 → 𝟛ᴺ → 𝟛ᴺ) → (𝕀 → 𝕀 → 𝕀) → 𝓦 ̇
f realises' f' = (a : 𝟛) (β : 𝟛ᴺ) → ⟪ f a β ⟫ ＝ f' ⟨ a ⟩ ⟪ β ⟫

id-realiser : id realises¹ id
id-realiser α = refl

∘-realiser : {f g : 𝟛ᴺ → 𝟛ᴺ} {f' g' : 𝕀 → 𝕀}
           → f realises¹ f'
           → g realises¹ g'
           → (f ∘ g) realises¹ (f' ∘ g')
∘-realiser {f} {g} {f'} {g'} f→ g→ α
 = ap f' (g→ α) ∙ f→ (g α)

map-realiser : (f : 𝟛 → 𝟛) (f' : 𝕀 → 𝕀)
             → f pw-realises¹ f'
             → is-⊕-homomorphism fe 𝓘 𝓘 f'
             → (map f) realises¹ f'
map-realiser f f' f→ f⊕ α = ⊕-homs-are-M-homs f' f⊕ (map ⟨_⟩ α)
                          ∙ ap M (dfunext (fe 𝓤₀ 𝓦) (λ i → f→ (α i)))

map-realiser² : (f : 𝟛 → 𝟛ᴺ → 𝟛ᴺ) (f' : 𝕀 → 𝕀 → 𝕀)
              → f realises' f'
              → ((a : 𝟛) → is-⊕-homomorphism fe 𝓘 𝓘 (f' ⟨ a ⟩))
              → (α β : 𝟛ᴺ)
              → M (map ⟪_⟫ (zipWith f α (repeat β)))
              ＝ M (λ n → f' ⟨ α n ⟩ ⟪ β ⟫)
map-realiser² f f' f→ f⊕ α β
 = ap M (dfunext (fe 𝓤₀ 𝓦) (λ i → f→ (α i) β))
```

## Negation

```
flip-realiser : flip pw-realises¹ −_
flip-realiser −1 = −1-inverse
flip-realiser  O =  O-inverse
flip-realiser +1 = +1-inverse

neg-realiser : neg realises¹ −_
neg-realiser
 = map-realiser flip −_ flip-realiser −-is-⊕-homomorphism
```

## Binary midpoint

```
half : 𝟝 → 𝕀
half −2 = u
half −1 = u /2
half  O = u ⊕ v
half +1 = v /2
half +2 = v

⊕-hom-l : {a b c : 𝕀} → a ⊕ (b ⊕ c) ＝ (a ⊕ b) ⊕ (a ⊕ c)
⊕-hom-l {a} {b} {c} = ⊕-is-⊕-homomorphism-r fe 𝓘 a b c

⊕-idem' = λ {a}             → ⊕-idem a
⊕-comm' = λ {a} {b}         → ⊕-comm a b
⊕-tran' = λ {a} {b} {c} {d} → ⊕-tran a b c d 
⊕-canc' = λ {a} {b} {c}     → ⊕-canc a b c 

div2-aux-＝ : (x y : 𝟝) (z : 𝕀) → let (a , b) = div2-aux x y in
             ⟨ a ⟩ ⊕ (half b ⊕ z) ＝ (half x ⊕ (half y ⊕ z))
div2-aux-＝ −2 y z = refl
div2-aux-＝ −1 −2 z = ap (_⊕ ((u ⊕ v) ⊕ z)) ⊕-idem' ⁻¹ ∙ ⊕-tran'
div2-aux-＝ −1 −1 z = ap (_⊕ ((v ⊕ (u ⊕ v)) ⊕ z)) (⊕-idem' ⁻¹ ∙ ⊕-idem' ⁻¹)
                   ∙ ⊕-tran' ∙ ap (_⊕ ((u ⊕ u) ⊕ z)) ⊕-tran'
                   ∙ ⊕-tran' ∙ ap (_⊕ ((u ⊕ (u ⊕ v)) ⊕ z))
                                (⊕-comm' ∙ ap (_⊕ (u ⊕ v)) ⊕-idem')
div2-aux-＝ −1  O z = ap (_⊕ (u ⊕ z)) ⊕-idem' ⁻¹ ∙ ⊕-tran'
                   ∙ ap (_⊕ ((u ⊕ v) ⊕ z)) ⊕-comm'
div2-aux-＝ −1 +1 z = ap (_⊕ ((u ⊕ (u ⊕ v)) ⊕ z))
                       (⊕-comm' ∙ ap (_⊕ u) ⊕-idem' ⁻¹)
                   ∙ ⊕-tran' ∙ ap (_⊕ (u ⊕ z)) ⊕-tran' ∙ ⊕-tran'
                   ∙ ap (_⊕ ((v ⊕ (u ⊕ v)) ⊕ z))
                       (⊕-comm' ∙ ap (u ⊕_) ⊕-comm')
div2-aux-＝ −1 +2 z = ⊕-tran'
div2-aux-＝  O  y z = refl
div2-aux-＝ +1 −2 z = ap (_⊕ ((u ⊕ v) ⊕ z)) ⊕-comm' ∙ ⊕-tran'
div2-aux-＝ +1 −1 z = ap (λ - → ((- ⊕ v) ⊕ ((v ⊕ (u ⊕ v)) ⊕ z))) ⊕-idem' ⁻¹
                          ∙ ⊕-tran' ∙ ap (_⊕ (v ⊕ z)) ⊕-tran'
                          ∙ ⊕-tran' ∙ ap (_⊕ ((u ⊕ (u ⊕ v)) ⊕ z)) ⊕-comm'
div2-aux-＝ +1  O z = ap (_⊕ (v ⊕ z)) ⊕-idem' ⁻¹ ∙ ⊕-tran'
                   ∙ ap (_⊕ ((u ⊕ v) ⊕ z)) ⊕-comm'
div2-aux-＝ +1 +1 z = ap (_⊕ ((u ⊕ (u ⊕ v)) ⊕ z)) (⊕-idem' ⁻¹ ∙ ⊕-idem' ⁻¹)
                   ∙ ⊕-tran' ∙ ap (_⊕ ((v ⊕ v) ⊕ z)) ⊕-tran' ∙ ⊕-tran'
                   ∙ ap (_⊕ ((v ⊕ (u ⊕ v)) ⊕ z))
                        (⊕-comm' ∙ ap (_⊕ (v ⊕ u)) ⊕-idem' ∙ ap (v ⊕_) ⊕-comm')
div2-aux-＝ +1 +2 z = ap (_⊕ ((u ⊕ v) ⊕ z)) ⊕-idem' ⁻¹ ∙ ⊕-tran'
div2-aux-＝ +2 y z = refl

div2-approx' : Π (fg-n-approx' (map ⟨_⟩ ∘ div2) (map half))
div2-approx' n f α
 = (z , w)
 , (ap ((map ⟨_⟩ ∘ div2) α 0 ⊕_) (pr₂ IH)
 ∙ div2-aux-＝ (α 0) (α 1)
     (m (append-one w ((first- n) (tail (map half (b ∷ x)))))))
 where
  b = pr₂ (div2-aux (α 0) (α 1))
  x = tail (tail α)
  IH = f (b ∷ x)
  z w : 𝕀
  z = pr₁ (pr₁ IH)
  w = pr₂ (pr₁ IH)

div2-realiser : (α : 𝟝ᴺ) → ⟪ div2 α ⟫ ＝ M (map half α)
div2-realiser = fg-approx-holds (map ⟨_⟩ ∘ div2) (map half) div2-approx'

half-add-realiser : (α β : 𝟛ᴺ) → M (map half (add2 α β)) ＝ (⟪ α ⟫ ⊕ ⟪ β ⟫)
half-add-realiser α β = ap M (dfunext (fe 𝓤₀ 𝓦) (λ i → γ (α i) (β i)))
                      ∙ M-hom (map ⟨_⟩ α) (map ⟨_⟩ β) ⁻¹
 where
  γ : (a b : 𝟛) → half (a +𝟛 b) ＝ (⟨ a ⟩ ⊕ ⟨ b ⟩)
  γ −1 −1 = ⊕-idem' ⁻¹
  γ −1  O = refl
  γ −1 +1 = refl
  γ  O −1 = ⊕-comm'
  γ  O  O = ⊕-idem' ⁻¹
  γ  O +1 = ⊕-comm'
  γ +1 −1 = ⊕-comm'
  γ +1  O = refl
  γ +1 +1 = ⊕-idem' ⁻¹

mid-realiser : mid realises² _⊕_
mid-realiser α β = div2-realiser (add2 α β)
                 ∙ half-add-realiser α β
```

## Infinitary midpoint

```
quarter : 𝟡 → 𝕀
quarter −4 = u
quarter −3 = u ⊕ (u ⊕ (u ⊕ v))
quarter −2 = u ⊕ (u ⊕ v)
quarter −1 = u ⊕ (v ⊕ (u ⊕ v))
quarter  O = u ⊕ v
quarter +1 = v ⊕ (u ⊕ (u ⊕ v))
quarter +2 = v ⊕ (u ⊕ v)
quarter +3 = v ⊕ (v ⊕ (u ⊕ v))
quarter +4 = v

l : {a b c : 𝕀} → a ＝ b → (a ⊕ c) ＝ (b ⊕ c)
l refl = refl

r : {a b c : 𝕀} → b ＝ c → (a ⊕ b) ＝ (a ⊕ c)
r refl = refl

div4-aux-＝ : (x y : 𝟡) (z : 𝕀)
            → let (a , b) = div4-aux x y in
              ⟨ a ⟩ ⊕ (quarter b ⊕ z)
            ＝ (quarter x ⊕ (quarter y ⊕ z))
div4-aux-＝ −4  y z = refl
div4-aux-＝ −3 −4 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
div4-aux-＝ −3 −3 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (r (l (⊕-idem' ⁻¹
         ∙ ⊕-comm')
      ∙ ⊕-tran')
   ∙ l (⊕-idem' ⁻¹)
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ −3 −2 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ −3 −1 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (l (⊕-idem' ⁻¹)
   ∙ r (l (⊕-idem' ⁻¹)
     ∙ ⊕-tran'
     ∙ l ⊕-comm')
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ −3  O z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (r ⊕-comm'
   ∙ l (⊕-idem' ⁻¹)
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ −3 +1 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (l (⊕-idem' ⁻¹)
   ∙ ⊕-tran'
   ∙ r (l (⊕-idem' ⁻¹)
     ∙ ⊕-tran')
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ −3 +2 z
 = l (⊕-idem' ⁻¹
   ∙ r (⊕-idem' ⁻¹)
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ −3 +3 z
 = l (⊕-idem' ⁻¹
   ∙ r (⊕-idem' ⁻¹
     ∙ r (⊕-idem' ⁻¹))
   ∙ r ⊕-tran'
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-idem'
div4-aux-＝ −3 +4 z
 = ⊕-tran'
div4-aux-＝ −2 −4 z = div2-aux-＝ −1 −2 z
div4-aux-＝ −2 −3 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (l (⊕-idem' ⁻¹)
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ −2 −2 z = div2-aux-＝ −1 −1 z
div4-aux-＝ −2 −1 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (l (⊕-idem' ⁻¹)
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ −2 O z  = div2-aux-＝ −1  O z
div4-aux-＝ −2 +1 z
 = r ⊕-comm' ∙ ⊕-tran'
 ∙ r (l (⊕-idem' ⁻¹)
   ∙ ⊕-tran' ∙ l ⊕-comm')
 ∙ ⊕-tran' ∙ r ⊕-comm'
div4-aux-＝ −2 +2 z = div2-aux-＝ −1 +1 z
div4-aux-＝ −2 +3 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (⊕-tran'
   ∙ l ⊕-idem')
 ∙ ⊕-tran'
div4-aux-＝ −2 +4 z = div2-aux-＝ −1 +2 z
div4-aux-＝ −1 −4 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
div4-aux-＝ −1 −3 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (l (⊕-idem' ⁻¹)
   ∙ ⊕-tran'
   ∙ l ⊕-comm'
   ∙ r (l (⊕-idem' ⁻¹)
     ∙ ⊕-tran')
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ −1 −2 z
 = l (⊕-idem' ⁻¹
   ∙ l ⊕-comm'
   ∙ r (⊕-idem' ⁻¹)
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ −1 −1 z
 = l ⊕-comm'
 ∙ ⊕-tran'
 ∙ l (l (⊕-idem' ⁻¹)
   ∙ ⊕-tran'
   ∙ r (l (⊕-idem' ⁻¹)
     ∙ ⊕-tran'
     ∙ l ⊕-comm')
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ −1 O z
 = l ⊕-comm'
 ∙ ⊕-tran'
 ∙ l (l (⊕-idem' ⁻¹)
    ∙ r ⊕-comm'
   ∙ ⊕-tran'
   ∙ r ⊕-comm')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ −1 +1 z
 = l ⊕-comm'
 ∙ ⊕-tran'
 ∙ l (r (l (⊕-idem' ⁻¹)
      ∙ ⊕-tran')
   ∙ l (⊕-idem' ⁻¹)
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ −1 +2 z
 = r ⊕-comm' ∙ ⊕-tran'
 ∙ r (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ r ⊕-comm'
div4-aux-＝ −1 +3 z
 = l ⊕-comm'
 ∙ ⊕-tran'
 ∙ l (r (l (⊕-idem' ⁻¹
         ∙ ⊕-comm')
      ∙ ⊕-tran'
      ∙ l ⊕-comm'
      ∙ ⊕-tran')
   ∙ l (⊕-idem' ⁻¹)
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ −1 +4 z = ⊕-tran'
div4-aux-＝  O  y z = refl 
div4-aux-＝ +1 −4 z
 = l ⊕-comm'
 ∙ ⊕-tran'
div4-aux-＝ +1 −3 z
 = ⊕-tran'
 ∙ l (l (⊕-idem' ⁻¹)
   ∙ ⊕-tran'
   ∙ l ⊕-comm'
   ∙ r (l (⊕-idem' ⁻¹)
     ∙ ⊕-tran')
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +1 −2 z
 = ⊕-tran'
 ∙ l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +1 −1 z
 = ⊕-tran'
 ∙ l (r (l (⊕-idem' ⁻¹)
      ∙ ⊕-tran'
      ∙ l ⊕-comm')
   ∙ l (⊕-idem' ⁻¹)
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +1 O z
 = ⊕-tran'
 ∙ l (r ⊕-comm'
   ∙ l (⊕-idem' ⁻¹)
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +1 +1 z
 = ⊕-tran'
 ∙ l (l (⊕-idem' ⁻¹)
   ∙ ⊕-tran'
   ∙ r (l (⊕-idem' ⁻¹)
     ∙ ⊕-tran')
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +1 +2 z
 = ⊕-tran'
 ∙ l (⊕-idem' ⁻¹
   ∙ r (⊕-idem' ⁻¹)
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +1 +3 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (l (⊕-idem' ⁻¹)
   ∙ ⊕-tran'
   ∙ l ⊕-comm'
   ∙ r (l (⊕-idem' ⁻¹)
     ∙ ⊕-tran'
     ∙ l ⊕-comm')
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +1 +4 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
div4-aux-＝ +2 −4 z = div2-aux-＝ +1 −2 z
div4-aux-＝ +2 −3 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (l ⊕-comm'
   ∙ ⊕-tran'
   ∙ l ⊕-idem')
 ∙ ⊕-tran'
div4-aux-＝ +2 −2 z = div2-aux-＝ +1 −1 z
div4-aux-＝ +2 −1 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (l ⊕-comm'
   ∙ ⊕-tran'
   ∙ l ⊕-idem')
 ∙ ⊕-tran'
div4-aux-＝ +2 O z = div2-aux-＝ +1 O z
div4-aux-＝ +2 +1 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
 ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +2 +2 z = div2-aux-＝ +1 +1 z
div4-aux-＝ +2 +3 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
 ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +2 +4 z = div2-aux-＝ +1 +2 z
div4-aux-＝ +3 −4 z
 = l ⊕-comm'
 ∙ ⊕-tran'
div4-aux-＝ +3 −3 z
 = l (⊕-idem' ⁻¹
   ∙ l ⊕-comm'
   ∙ r (⊕-idem' ⁻¹
     ∙ l ⊕-comm'
     ∙ r (⊕-idem' ⁻¹)
     ∙ ⊕-tran')
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-idem'
div4-aux-＝ +3 −2 z
 = l (⊕-idem' ⁻¹
   ∙ l ⊕-comm'
   ∙ r (⊕-idem' ⁻¹)
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +3 −1 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (l (⊕-idem' ⁻¹)
   ∙ ⊕-tran'
   ∙ r (l (⊕-idem' ⁻¹)
     ∙ ⊕-tran'
     ∙ l ⊕-comm')
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +3  O z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (l (⊕-idem' ⁻¹)
   ∙ r ⊕-comm'
   ∙ ⊕-tran'
   ∙ r ⊕-comm')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +3 +1 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (r (l (⊕-idem' ⁻¹)
      ∙ ⊕-tran')
   ∙ l (⊕-idem' ⁻¹)
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +3 +2 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +3 +3 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
 ∙ l (r (l (⊕-idem' ⁻¹)
      ∙ ⊕-tran'
      ∙ l ⊕-comm')
   ∙ l (⊕-idem' ⁻¹)
   ∙ ⊕-tran')
 ∙ ⊕-tran'
 ∙ l ⊕-comm'
div4-aux-＝ +3 +4 z
 = l (⊕-idem' ⁻¹)
 ∙ ⊕-tran'
div4-aux-＝ +4  y z = refl

div4-approx' : Π (fg-n-approx' (map ⟨_⟩ ∘ div4) (map quarter))
div4-approx' n f α
 = (z , w)
 , (ap ((map ⟨_⟩ ∘ div4) α 0 ⊕_) (pr₂ IH)
 ∙ div4-aux-＝ (α 0) (α 1)
     (m (append-one w ((first- n) (tail (map quarter (b ∷ x)))))))
 where
  b = pr₂ (div4-aux (α 0) (α 1))
  x = tail (tail α)
  IH = f (b ∷ x)
  z w : 𝕀
  z = pr₁ (pr₁ IH)
  w = pr₂ (pr₁ IH)

quarter-realiser : (α : 𝟡ᴺ) → ⟪ div4 α ⟫ ＝ M (map quarter α)
quarter-realiser = fg-approx-holds (map ⟨_⟩ ∘ div4) (map quarter)
                     div4-approx'

⟪⟪_⟫⟫ : 𝟡ᴺ → 𝕀
⟪⟪ x ⟫⟫ = M (map quarter x)

_realisesᴺ_ : ((ℕ → 𝟛ᴺ) → 𝟛ᴺ) → ((ℕ → 𝕀) → 𝕀) → 𝓦 ̇
f realisesᴺ f' = (δs : ℕ → 𝟛ᴺ) → f' (map ⟪_⟫ δs) ＝ ⟪ f δs ⟫

𝟡s-conv-＝ : (a b c : 𝟛)
           → (⟨ a ⟩ ⊕ (⟨ b ⟩ ⊕ ⟨ c ⟩))
           ＝ quarter ((a +𝟛 a) +𝟝 (b +𝟛 c))
𝟡s-conv-＝ −1 −1 −1 = ap (u ⊕_) ⊕-idem' ∙ ⊕-idem'
𝟡s-conv-＝ −1 −1  O = refl
𝟡s-conv-＝ −1 −1 +1 = refl
𝟡s-conv-＝ −1  O −1 = ap (u ⊕_) ⊕-comm'
𝟡s-conv-＝ −1  O  O = ap (u ⊕_) ⊕-idem'
𝟡s-conv-＝ −1  O +1 = ap (u ⊕_) ⊕-comm'
𝟡s-conv-＝ −1 +1 −1 = ap (u ⊕_) ⊕-comm'
𝟡s-conv-＝ −1 +1  O = refl 
𝟡s-conv-＝ −1 +1 +1 = ap (u ⊕_) ⊕-idem'
𝟡s-conv-＝  O −1 −1 = ⊕-comm' ∙ ap (_⊕ (u ⊕ v)) ⊕-idem'
𝟡s-conv-＝  O −1  O = ⊕-tran' ∙ ap (_⊕ (v ⊕ (u ⊕ v))) ⊕-idem'
𝟡s-conv-＝  O −1 +1 = ⊕-idem'
𝟡s-conv-＝  O  O −1 = ap ((u ⊕ v) ⊕_) ⊕-comm' ∙ ⊕-tran'
                   ∙ ap (_⊕ (v ⊕ (u ⊕ v))) ⊕-idem'
𝟡s-conv-＝  O  O  O = ap ((u ⊕ v) ⊕_) ⊕-idem' ∙ ⊕-idem'
𝟡s-conv-＝  O  O +1 = ⊕-tran' ∙ ap ((u ⊕ (u ⊕ v)) ⊕_) ⊕-idem' ∙ ⊕-comm'
𝟡s-conv-＝  O +1 −1 = ap ((u ⊕ v) ⊕_) ⊕-comm' ∙ ⊕-idem'
𝟡s-conv-＝  O +1  O = ap (_⊕ (v ⊕ (u ⊕ v))) ⊕-comm' ∙ ⊕-tran'
                   ∙ ap (_⊕ (u ⊕ (u ⊕ v))) ⊕-idem'
𝟡s-conv-＝  O +1 +1 = ⊕-comm' ∙ ap (_⊕ (u ⊕ v)) ⊕-idem'
𝟡s-conv-＝ +1 −1 −1 = ap (v ⊕_) ⊕-idem' ∙ ⊕-comm'
𝟡s-conv-＝ +1 −1  O = refl
𝟡s-conv-＝ +1 −1 +1 = refl
𝟡s-conv-＝ +1  O −1 = ap (v ⊕_) ⊕-comm'
𝟡s-conv-＝ +1  O  O = ap (v ⊕_) ⊕-idem'
𝟡s-conv-＝ +1  O +1 = ap (v ⊕_) ⊕-comm'
𝟡s-conv-＝ +1 +1 −1 = ap (v ⊕_) ⊕-comm'
𝟡s-conv-＝ +1 +1  O = refl
𝟡s-conv-＝ +1 +1 +1 = ap (v ⊕_) ⊕-idem' ∙ ⊕-idem'

M-bigMid'-＝ : (x y : 𝟛ᴺ) (z : 𝕀)
            → (⟪ x ⟫ ⊕ (⟪ y ⟫ ⊕ z))
            ＝ (⟨ x 0 ⟩ ⊕ (⟨ x 1 ⟩ ⊕ ⟨ y 0 ⟩))
            ⊕ ((⟪ mid (tail (tail x)) (tail y) ⟫) ⊕ z)
M-bigMid'-＝ x y z
 = ap (_⊕ (⟪ y ⟫ ⊕ z))
     (M-prop₁ (map ⟨_⟩ x)
 ∙ ap (⟨ x 0 ⟩ ⊕_) (M-prop₁ (map ⟨_⟩ (tail x))))
 ∙ ap ((⟨ x 0 ⟩ ⊕ (⟨ x 1 ⟩ ⊕ ⟪ tail (tail x) ⟫)) ⊕_)
     (ap (_⊕ z) (M-prop₁ (map ⟨_⟩ y)))
 ∙ ap (_⊕ ((⟨ y 0 ⟩ ⊕ ⟪ tail y ⟫) ⊕ z)) (⊕-comm')
 ∙ ⊕-tran' ∙ ap (_⊕ (⟨ x 0 ⟩ ⊕ z)) ⊕-tran'
 ∙ ⊕-tran' ∙ ap (_⊕ ((⟪ tail (tail x) ⟫ ⊕ ⟪ tail y ⟫) ⊕ z)) ⊕-comm'
 ∙ ap (λ - → (⟨ x 0 ⟩ ⊕ (⟨ x 1 ⟩ ⊕ ⟨ y 0 ⟩)) ⊕ (- ⊕ z))
     (mid-realiser (tail (tail x)) (tail y) ⁻¹)

bigMid'-approx : Π (fg-n-approx' (map ⟪_⟫) (map quarter ∘ bigMid'))
bigMid'-approx n f αs
 = (z , w)
 , (M-bigMid'-＝ (αs 0) (αs 1)
     (m (append-one z ((first- n) (map ⟪_⟫ zs))))
 ∙ ap (_⊕ ((⟪ mid x y ⟫) ⊕ m (append-one z ((first- n) (map ⟪_⟫ zs)))))
      (𝟡s-conv-＝ a b c')
 ∙ ap (quarter ((a +𝟛 a) +𝟝 (b +𝟛 c')) ⊕_) (pr₂ IH))
 where
   x = tail (tail (αs 0))
   y = tail (αs 1)
   a = αs 0 0
   b = αs 0 1
   c' = αs 1 0
   zs = tail (tail αs)
   IH = f (mid x y ∷ zs)
   z w : 𝕀
   z = pr₁ (pr₁ IH)
   w = pr₂ (pr₁ IH)

M-realiser : bigMid realisesᴺ M
M-realiser δs = fg-approx-holds (map ⟪_⟫) (map quarter ∘ bigMid')
                  bigMid'-approx δs
                  ∙ quarter-realiser (bigMid' δs) ⁻¹
```

## Multiplication

```
digitMul-realiser : digitMul realises' _*_
digitMul-realiser −1 α
 = neg-realiser α ⁻¹ ∙ *-gives-negation-r ⟪ α ⟫ ⁻¹
digitMul-realiser  O α
 = M-idem (u ⊕ v)    ∙ *-gives-zero-r     ⟪ α ⟫ ⁻¹
digitMul-realiser +1 α
 = id-realiser α ⁻¹  ∙ *-gives-id-r       ⟪ α ⟫ ⁻¹

mul-realiser : mul realises² _*_
mul-realiser α β = M-realiser (zipWith digitMul α (λ _ → β)) ⁻¹
                 ∙ map-realiser² digitMul _*_ digitMul-realiser
                     (λ a → *-is-⊕-homomorphism-l ⟨ a ⟩) α β
                 ∙ ⊕-homs-are-M-homs (_* ⟪ β ⟫)
                     (*-is-⊕-homomorphism-r ⟪ β ⟫)
                     (map ⟨_⟩ α) ⁻¹
```

[⇐ Index](../html/TWA.Thesis.index.html)
