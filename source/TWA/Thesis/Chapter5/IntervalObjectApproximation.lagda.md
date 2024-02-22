[⇐ Index](../html/TWA.Thesis.index.html)

# Interval object finite approximations

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import UF.Base
open import MLTT.SpartanList hiding (_∷_;⟨_⟩;[_])

open import TWA.Thesis.Chapter2.Vectors
open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter5.IntervalObject

module TWA.Thesis.Chapter5.IntervalObjectApproximation
 (fe : FunExt)
 (io : Interval-object fe 𝓤)
 where

open basic-interval-object-development fe io hiding (−1 ; O ; +1)

first-_ : {A : 𝓥 ̇ } (n : ℕ) → (ℕ → A) → Vec A n
first- n = Seq-to-Vec n

append-one : {X : 𝓥 ̇ } {n : ℕ} → X → Vec X n → Vec X (succ n)
append-one {𝓥} {X} {0} y ⟨⟩ = y :: ⟨⟩
append-one {𝓥} {X} {succ n} y (x :: xs) = x :: append-one y xs

m : {n : ℕ} → Vec 𝕀 (succ n) → 𝕀
m {0} (x :: ⟨⟩) = x
m {succ n} (x :: xs) = x ⊕ m xs

n-approx : (x y : ℕ → 𝕀) (n : ℕ) → 𝓤  ̇
n-approx x y n = Σ (z , w) ꞉ 𝕀 × 𝕀
               , m (append-one z ((first- n) x))
               ＝ m (append-one w ((first- n) y))

approximation : 𝓤  ̇
approximation = (x y : ℕ → 𝕀) → Π (n-approx x y) → M x ＝ M y

multi-canc : (w z : 𝕀) (y : ℕ → 𝕀) (n : ℕ)
           → m (append-one w ((first- n) y))
           ＝ m (append-one z ((first- n) y))
           → w ＝ z
multi-canc w .w y 0 refl = refl
multi-canc w z y (succ n) e
 = multi-canc w z (y ∘ succ) n
     (⊕-canc _ _ _ (⊕-comm _ _ ∙ e ∙ ⊕-comm _ _))

one-sided-approx : (x : 𝕀) (y : ℕ → 𝕀)
                 → ((n : ℕ)
                    → Σ w ꞉ 𝕀 , x ＝ m (append-one w ((first- n) y)))
                 → x ＝ M y
one-sided-approx x y f = M-prop₂ ws y γ where
  ws : ℕ → 𝕀
  ws 0 = x
  ws (succ i) = pr₁ (f (succ i))
  γ : (i : ℕ) → ws i ＝ (y i ⊕ ws (succ i))
  γ 0 = pr₂ (f 1)
  γ (succ i) = multi-canc
                 (ws (succ i))
                 (y (succ i) ⊕ ws (succ (succ i)))
                 y
                 (succ i) (pr₂ (f (succ i)) ⁻¹
             ∙ (pr₂ (f (succ (succ i)))
             ∙ δ'' y (ws (succ (succ i))) i))
   where
    δ'' : (y : ℕ → 𝕀) (z : 𝕀) (i : ℕ)
        → m (append-one z ((first- (succ (succ i))) y))
        ＝ m (append-one (y (succ i) ⊕ z) ((first- (succ i)) y))
    δ'' y z 0 = refl
    δ'' y z (succ i) = ap (y 0 ⊕_) (δ'' (y ∘ succ) z i)
    
_++'_ : {n : ℕ} {X : 𝓤 ̇ } → Vec X n → (ℕ → X) → (ℕ → X)
_++'_ {n} {X} v α = Vec-to-Seq n α v

m-prop₁ : (n : ℕ) (a b c : ℕ → 𝕀) (e : 𝕀)
        → (m (append-one e ((first- succ n) a))
          ⊕ M ((first- n) b ++' λ i → (c (succ (i +ℕ n)))))
        ＝ M ((append-one (a n ⊕ e) ((first- n) λ i → a i ⊕ b i))
            ++' (λ i → c (succ (i +ℕ n))))
m-prop₁ 0 a b c e = M-prop₁ _ ⁻¹
m-prop₁ (succ n) a b c e
 = ap ((a 0 ⊕ (a 1 ⊕ m (append-one e ((first- n) (a ∘ succ ∘ succ))))) ⊕_)
     (M-prop₁ ((first- succ n) b ++' (λ i → c (succ (i +ℕ succ n)))))
     ∙ ⊕-tran _ _ _ _
     ∙ ap ((a 0 ⊕ b 0) ⊕_) (m-prop₁ n (tail a) (tail b) (tail c) e)
     ∙ M-prop₁ (append-one (a (succ n) ⊕ e)
         ((first- succ n) (λ i → a i ⊕ b i))
         ++' (λ i → c (succ (i +ℕ succ n)))) ⁻¹

M-append-＝ : (x : ℕ → 𝕀) (n : ℕ)
            → M x
            ＝ M (append-one (x n) ((first- n) x)
                   ++' (λ i → x (succ (i +ℕ n))))
M-append-＝ x 0 = M-prop₁ x
                   ∙ M-prop₁
                       (append-one (x 0) ((first- 0) x)
                         ++' (λ i → x (succ (i +ℕ 0)))) ⁻¹
M-append-＝ x (succ n) = M-prop₁ x
                       ∙ ap (x 0 ⊕_) (M-append-＝ (tail x) n)
                       ∙ M-prop₁
                           (append-one (x (succ n)) ((first- succ n) x)
                             ++' (λ i → x (succ (i +ℕ succ n)))) ⁻¹

M-append-++-＝ : (x y : ℕ → 𝕀) (n : ℕ)
     → M (λ i → x i ⊕ y i)
     ＝ (m (append-one (y n) ((first- succ n) x))
         ⊕ M (((first- n) y) ++' (λ i → (x (succ (i +ℕ n)))
                                      ⊕ (y (succ (i +ℕ n))))))
M-append-++-＝ x y n = M-append-＝ (λ i → x i ⊕ y i) n
           ∙ m-prop₁ n x y (λ i → x i ⊕ y i) (y n) ⁻¹

append-++-= : (x y : ℕ → 𝕀) (w : 𝕀) (n : ℕ)
        → ((append-one w ((first- n) x)) ++' y)
        ＝ (((first- n) x) ++' (w ∷ y))
append-++-= x y w 0 = dfunext (fe 𝓤₀ 𝓤) (induction refl λ _ _ → refl)
append-++-= x y w (succ n) = dfunext (fe 𝓤₀ 𝓤) (induction refl
                           (λ k _ → happly (append-++-= (tail x) y w n) k))

tail-_ : {X : 𝓤 ̇ } → ℕ → (ℕ → X) → (ℕ → X)
(tail- 0) α = α
(tail- succ n) α = tail ((tail- n) α)

M→m : (α : ℕ → 𝕀) (n : ℕ)
    → M α ＝ m (append-one (M ((tail- n) α)) ((first- n) α))
M→m α 0 = refl
M→m α (succ n) = M-prop₁ α
               ∙ ap (α 0 ⊕_)
               (transport
                    (λ - → M (tail α)
                         ＝ m (append-one (M -) ((first- n) (tail α))))
                    (γ α n) (M→m (tail α) n))
  where
    γ : (α : ℕ → 𝕀) (n : ℕ) → ((tail- n) (tail α)) ＝ ((tail- succ n) α)
    γ α 0 = refl
    γ α (succ n) = ap tail (γ α n)

tail-first' : {X : 𝓤 ̇ } {m : ℕ}
            → (a : Vec X (succ m)) (β : ℕ → X) (n : ℕ)
            → (tail- succ n) (a ++' β)
            ＝ (tail- n) (tl {𝓤} {m} {λ _ → X} a ++' β)
tail-first' {X} {m} (_ :: xs) β 0 = refl
tail-first' {X} {m} (_ :: xs) β (succ n)
 = ap tail (tail-first' {X} {m} (_ :: xs) β n)

tail-first : {X : 𝓤 ̇ }
           → (α β : ℕ → X) (n : ℕ)
           → (tail- n) (((first- n) α) ++' β) ＝ β
tail-first α β 0 = refl
tail-first α β (succ n)
 = tail-first' ((first- (succ n)) α) β n ∙ tail-first (tail α) β n

first-first : {X : 𝓤 ̇ }
            → (α β : ℕ → X) (n : ℕ)
            → ((first- n) ((first- n) α ++' β)) ＝ (first- n) α
first-first α β 0 = refl
first-first α β (succ n) = ap (α 0 ::_) (first-first (tail α) β n)

approx-holds : approximation
approx-holds x y f = ⊕-canc (M x) (M y) (M (tail z)) γ
 where
  z w : ℕ → 𝕀
  z n = pr₁ (pr₁ (f n))
  w n = pr₂ (pr₁ (f n))
  w'' : (n : ℕ) → (ℕ → 𝕀)
  w'' n = (y n ⊕ w (succ n))
        ∷ (λ i → x (succ (i +ℕ n))
          ⊕ z (succ (succ (i +ℕ n))))
  γ'' : (n : ℕ) → m (append-one (z n) ((first- n) x))
                ＝ m (append-one (w n) ((first- n) y))
  γ'' n = pr₂ (f n)
  γ' : (n : ℕ) → Σ w* ꞉ 𝕀 , M (λ i → x i ⊕ (tail z) i)
     ＝ m (append-one w* ((first- n) (λ i → y i ⊕ (tail z) i)))
  γ' n = M (w'' n)
       , (M-append-++-＝ x (tail z) n
       ∙ ap (_⊕ M ((first- n) (tail z) ++' (λ i → x (succ (i +ℕ n))
                                           ⊕ tail z (succ (i +ℕ n)))))
            (γ'' (succ n))
       ∙ m-prop₁ n y (tail z) (λ i → x i ⊕ (tail z) i) (w (succ n))
       ∙ ap M (append-++-= (λ i → y i ⊕ (tail z) i)
                (λ i → x (succ (i +ℕ n)) ⊕ (tail z) (succ (i +ℕ n)))
            (w'' n 0) n)
       ∙ M→m (((first- n) (λ i → y i ⊕ (tail z) i) ++' (w'' n))) n
       ∙ (ap (λ - → m (append-one (M -)
               ((first- n)
                 ((first- n)
                 (λ i → y i ⊕ (tail z) i) ++' (w'' n)))))
          (tail-first (λ i → y i ⊕ (tail z) i) (w'' n) n)
        ∙ ap (λ - → m (append-one (M (w'' n)) -))
           (first-first (λ i → y i ⊕ (tail z) i) (w'' n) n)))
  γ : (M x ⊕ M (z ∘ succ)) ＝ (M y ⊕ M (z ∘ succ))
  γ = M-hom x (z ∘ succ)
        ∙ one-sided-approx
            (M (λ i → x i ⊕ pr₁ (pr₁ (f (succ i)))))
            (λ i → y i ⊕ z (succ i))
            γ'
        ∙ M-hom y (z ∘ succ) ⁻¹

n-approx' : (ℕ → 𝕀) → (ℕ → 𝕀) → ℕ → 𝓤  ̇
n-approx' x y n = Σ (z , w) ꞉ 𝕀 × 𝕀
                , m (append-one z ((first- (succ n)) x))
                ＝ m (append-one w ((first- (succ n)) y))

n-approx'→n-approx
 : (x y : ℕ → 𝕀) → Π (n-approx' x y) → Π (n-approx x y)
n-approx'→n-approx x y f 0 = (u , u) , refl
n-approx'→n-approx x y f (succ n) = f n

fg-n-approx' : {X : 𝓥 ̇ } → (f g : X → ℕ → 𝕀) → ℕ → 𝓤 ⊔ 𝓥 ̇
fg-n-approx' f g n
 = (∀ x → n-approx' (f x) (g x) n) 
 → (∀ x → n-approx' (f x) (g x) (succ n)) 

fg-approx-holds : {X : 𝓥 ̇ } (f g : X → ℕ → 𝕀)
                → Π (fg-n-approx' f g)
                → ∀ x → M (f x) ＝ M (g x)
fg-approx-holds {_} {X} f g h x
 = approx-holds (f x) (g x) (n-approx'→n-approx (f x) (g x) (γ x))
 where
  γ : (x : X) → Π (n-approx' (f x) (g x))
  γ x 0 = (g x 0 , f x 0) , ⊕-comm _ _
  γ x (succ n) = h n (λ y → γ y n) x

cancellation-holds : cancellative fe _⊕_
cancellation-holds a b c f = M-idem a ⁻¹ ∙ γ ∙ M-idem b
 where
  n-approx-c : (i : ℕ)
             → m (append-one c ((first- i) (λ _ → a)))
             ＝ m (append-one c ((first- i) (λ _ → b)))
  n-approx-c 0 = refl
  n-approx-c 1 = f
  n-approx-c (succ (succ i))
   = (   a    ⊕ (a ⊕ wa)) ＝⟨ ap (_⊕ (a ⊕ wa)) (⊕-idem a ⁻¹) ⟩
     ((a ⊕ a) ⊕ (a ⊕ wa)) ＝⟨ ap ((a ⊕ a) ⊕_) (n-approx-c (succ i)) ⟩
     ((a ⊕ a) ⊕ (b ⊕ wb)) ＝⟨ ⊕-tran a a b wb ⟩
     ((a ⊕ b) ⊕ (a ⊕ wb)) ＝⟨ ap (λ - → (a ⊕ b) ⊕ (a ⊕ -)) (IH₂ ⁻¹) ⟩
     ((a ⊕ b) ⊕ (a ⊕ wa)) ＝⟨ ap ((a ⊕ b) ⊕_) (n-approx-c (succ i)) ⟩
     ((a ⊕ b) ⊕ (b ⊕ wb)) ＝⟨ ap (_⊕ (b ⊕ wb)) (⊕-comm a b) ⟩ 
     ((b ⊕ a) ⊕ (b ⊕ wb)) ＝⟨ ⊕-tran b a b wb ⟩
     ((b ⊕ b) ⊕ (a ⊕ wb)) ＝⟨ ap (λ - → (b ⊕ b) ⊕ (a ⊕ -)) (IH₂ ⁻¹) ⟩
     ((b ⊕ b) ⊕ (a ⊕ wa)) ＝⟨ ap ((b ⊕ b) ⊕_) (n-approx-c (succ i)) ⟩
     ((b ⊕ b) ⊕ (b ⊕ wb)) ＝⟨ ap (_⊕ (b ⊕ wb)) (⊕-idem b) ⟩
     (   b    ⊕ (b ⊕ wb)) ∎
   where
    wa = m (append-one c ((first- i) (λ _ → a)) )
    wb = m (append-one c ((first- i) (λ _ → b)))
    IH₂ : wa ＝ wb
    IH₂ = n-approx-c i
  γ : M (λ _ → a) ＝ M (λ _ → b)
  γ = approx-holds (λ _ → a) (λ _ → b) (λ i → (c , c) :: n-approx-c i)
```

[⇐ Index](../html/TWA.Thesis.index.html)
