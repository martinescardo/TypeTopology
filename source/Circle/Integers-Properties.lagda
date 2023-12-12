Tom de Jong
Reboot: 22 January 2021
Earlier version: 18 September 2020

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Circle.Integers

open import MLTT.Spartan
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-Properties

module Circle.Integers-Properties where

ℤ-is-set : is-set ℤ
ℤ-is-set = +-is-set 𝟙 (ℕ + ℕ) (props-are-sets 𝟙-is-prop)
            (+-is-set ℕ ℕ ℕ-is-set ℕ-is-set)

succ-ℤ : ℤ → ℤ
succ-ℤ 𝟎              = pos 0
succ-ℤ (pos n)        = pos (succ n)
succ-ℤ (neg 0)        = 𝟎
succ-ℤ (neg (succ n)) = neg n

pred-ℤ : ℤ → ℤ
pred-ℤ 𝟎              = neg 0
pred-ℤ (pos 0)        = 𝟎
pred-ℤ (pos (succ n)) = pos n
pred-ℤ (neg n)        = neg (succ n)

succ-ℤ-is-retraction : succ-ℤ ∘ pred-ℤ ∼ id
succ-ℤ-is-retraction 𝟎              = refl
succ-ℤ-is-retraction (pos zero)     = refl
succ-ℤ-is-retraction (pos (succ n)) = refl
succ-ℤ-is-retraction (neg n)        = refl

succ-ℤ-is-section : pred-ℤ ∘ succ-ℤ ∼ id
succ-ℤ-is-section 𝟎              = refl
succ-ℤ-is-section (pos n)        = refl
succ-ℤ-is-section (neg zero)     = refl
succ-ℤ-is-section (neg (succ n)) = refl

succ-ℤ-is-equiv : is-equiv succ-ℤ
succ-ℤ-is-equiv = qinvs-are-equivs succ-ℤ
                   (pred-ℤ , succ-ℤ-is-section , succ-ℤ-is-retraction)

succ-ℤ-≃ : ℤ ≃ ℤ
succ-ℤ-≃ = (succ-ℤ , succ-ℤ-is-equiv)

pred-ℤ-is-equiv : is-equiv pred-ℤ
pred-ℤ-is-equiv = ⌜⌝-is-equiv (≃-sym succ-ℤ-≃)

\end{code}

We will consider iterations of succ-ℤ and pred-ℤ in defining addition on ℤ and
need some lemmas for working with those iterations.

\begin{code}
commute-with-iterated-function : {X : 𝓤 ̇ } (f g : X → X)
                               → f ∘ g ∼ g ∘ f
                               → (n : ℕ) → f ∘ (g ^ n) ∼ (g ^ n) ∘ f
commute-with-iterated-function f g h zero     x = refl
commute-with-iterated-function f g h (succ n) x =
 (f ∘ g ∘ (g ^ n)) x ＝⟨ h ((g ^ n) x) ⟩
 (g ∘ f ∘ (g ^ n)) x ＝⟨ ap g (IH x)   ⟩
 (g ∘ (g ^ n) ∘ f) x ∎
  where
   IH : f ∘ (g ^ n) ∼ (g ^ n) ∘ f
   IH = commute-with-iterated-function f g h n

commute-with-iterated-functions : {X : 𝓤 ̇ } (f g : X → X)
                                → f ∘ g ∼ g ∘ f
                                → (n m : ℕ)
                                → (f ^ n) ∘ (g ^ m) ∼ (g ^ m) ∘ (f ^ n)
commute-with-iterated-functions f g h n m =
 commute-with-iterated-function (f ^ n) g γ m
  where
   γ : (f ^ n) ∘ g ∼ g ∘ (f ^ n)
   γ x = (commute-with-iterated-function g f (λ y → h y ⁻¹) n x) ⁻¹

iterated-function-is-section : {X : 𝓤 ̇ } (s : X → X) (r : X → X)
                             → r ∘ s ∼ id
                             → (n : ℕ) → (r ^ n) ∘ (s ^ n) ∼ id
iterated-function-is-section s r ρ zero     x = refl
iterated-function-is-section s r ρ (succ n) x =
 (r ∘ (r ^ n) ∘ s ∘ (s ^ n)) x ＝⟨ I   ⟩
 (r ∘ (r ^ n) ∘ (s ^ n) ∘ s) x ＝⟨ II  ⟩
 (r ∘ s) x                     ＝⟨ ρ x ⟩
 x                             ∎
  where
   I  = ap (r ^ (succ n)) (commute-with-iterated-function s s (λ x → refl) n x)
   II = ap r (iterated-function-is-section s r ρ n (s x))

iterated-function-is-equiv : {X : 𝓤 ̇ } (f : X → X)
                           → is-equiv f
                           → (n : ℕ) → is-equiv (f ^ n)
iterated-function-is-equiv f ((s , ε) , (r , η)) n =
 (((s ^ n) , (iterated-function-is-section s f ε n)) ,
  ((r ^ n) , (iterated-function-is-section f r η n)))

commute-with-succ-ℤ^n : (f : ℤ → ℤ)
                      → (f ∘ succ-ℤ ∼ succ-ℤ ∘ f)
                      → (n : ℕ) → f ∘ (succ-ℤ ^ n) ∼ (succ-ℤ ^ n) ∘ f
commute-with-succ-ℤ^n f c = commute-with-iterated-function f succ-ℤ c

commute-with-pred-ℤ : (f : ℤ → ℤ)
                    → (f ∘ succ-ℤ ∼ succ-ℤ ∘ f)
                    → f ∘ pred-ℤ ∼ pred-ℤ ∘ f
commute-with-pred-ℤ f c z = equivs-are-lc succ-ℤ succ-ℤ-is-equiv γ
 where
  γ : succ-ℤ (f (pred-ℤ z)) ＝ succ-ℤ (pred-ℤ (f z))
  γ = succ-ℤ (f (pred-ℤ z)) ＝⟨ (c (pred-ℤ z)) ⁻¹               ⟩
      f (succ-ℤ (pred-ℤ z)) ＝⟨ ap f (succ-ℤ-is-retraction z)   ⟩
      f z                   ＝⟨ (succ-ℤ-is-retraction (f z)) ⁻¹ ⟩
      succ-ℤ (pred-ℤ (f z)) ∎

succ-ℤ-commutes-with-pred-ℤ : succ-ℤ ∘ pred-ℤ ∼ pred-ℤ ∘ succ-ℤ
succ-ℤ-commutes-with-pred-ℤ = commute-with-pred-ℤ succ-ℤ (λ x → refl)

pred-ℤ-commutes-with-succ-ℤ : pred-ℤ ∘ succ-ℤ ∼ succ-ℤ ∘ pred-ℤ
pred-ℤ-commutes-with-succ-ℤ x = (succ-ℤ-commutes-with-pred-ℤ x) ⁻¹

commute-with-pred-ℤ^n : (f : ℤ → ℤ)
                      → (f ∘ succ-ℤ ∼ succ-ℤ ∘ f)
                      → (n : ℕ) → f ∘ (pred-ℤ ^ n) ∼ (pred-ℤ ^ n) ∘ f
commute-with-pred-ℤ^n f c =
 commute-with-iterated-function f pred-ℤ (commute-with-pred-ℤ f c)

succ-ℤ^n-is-retraction : (n : ℕ) → (succ-ℤ ^ n) ∘ (pred-ℤ ^ n) ∼ id
succ-ℤ^n-is-retraction =
 iterated-function-is-section pred-ℤ succ-ℤ succ-ℤ-is-retraction

succ-ℤ^n-is-section : (n : ℕ) → (pred-ℤ ^ n) ∘ (succ-ℤ ^ n) ∼ id
succ-ℤ^n-is-section =
 iterated-function-is-section succ-ℤ pred-ℤ succ-ℤ-is-section

pos-is-succ-ℤ-iterated : (n : ℕ) → pos n ＝ (succ-ℤ ^ (succ n)) 𝟎
pos-is-succ-ℤ-iterated zero     = refl
pos-is-succ-ℤ-iterated (succ n) = ap succ-ℤ (pos-is-succ-ℤ-iterated n)

neg-is-pred-ℤ-iterated : (n : ℕ) → neg n ＝ (pred-ℤ ^ (succ n)) 𝟎
neg-is-pred-ℤ-iterated zero     = refl
neg-is-pred-ℤ-iterated (succ n) = ap pred-ℤ (neg-is-pred-ℤ-iterated n)

\end{code}

We are now ready to define addition on ℤ and prove its basic properties, such as
commutativity.

\begin{code}

_+ℤ_ : ℤ → ℤ → ℤ
_+ℤ_ 𝟎       = id
_+ℤ_ (pos n) = (succ-ℤ ^ (succ n))
_+ℤ_ (neg n) = (pred-ℤ ^ (succ n))

+ℤ-is-commutative : (x y : ℤ) → x +ℤ y ＝ y +ℤ x
+ℤ-is-commutative 𝟎 𝟎 = refl
+ℤ-is-commutative 𝟎 (pos m) = pos-is-succ-ℤ-iterated m
+ℤ-is-commutative 𝟎 (neg m) = neg-is-pred-ℤ-iterated m
+ℤ-is-commutative (pos n) 𝟎 = (pos-is-succ-ℤ-iterated n) ⁻¹
+ℤ-is-commutative (neg n) 𝟎 = (neg-is-pred-ℤ-iterated n) ⁻¹
+ℤ-is-commutative (pos n) (pos m) =
 (succ-ℤ ^ succ n) (pos m)               ＝⟨ I    ⟩
 (succ-ℤ ^ succ n) ((succ-ℤ ^ succ m) 𝟎) ＝⟨ II   ⟩
 (succ-ℤ ^ succ m) ((succ-ℤ ^ succ n) 𝟎) ＝⟨ III  ⟩
 (succ-ℤ ^ succ m) (pos n)               ＝⟨ refl ⟩
 pos m +ℤ pos n                          ∎
  where
   I   = ap (succ-ℤ ^ (succ n)) (pos-is-succ-ℤ-iterated m)
   II  = commute-with-iterated-functions succ-ℤ succ-ℤ
          (λ x → refl) (succ n) (succ m) 𝟎
   III = ap (succ-ℤ ^ (succ m)) ((pos-is-succ-ℤ-iterated n) ⁻¹)
+ℤ-is-commutative (pos n) (neg m) =
 (succ-ℤ ^ succ n) (neg m)               ＝⟨ I   ⟩
 (succ-ℤ ^ succ n) ((pred-ℤ ^ succ m) 𝟎) ＝⟨ II  ⟩
 (pred-ℤ ^ succ m) ((succ-ℤ ^ succ n) 𝟎) ＝⟨ III ⟩
 (pred-ℤ ^ succ m) (pos n)               ＝⟨ refl ⟩
 neg m +ℤ pos n                          ∎
  where
   I   = ap (succ-ℤ ^ succ n) (neg-is-pred-ℤ-iterated m)
   II  = commute-with-iterated-functions succ-ℤ pred-ℤ
          succ-ℤ-commutes-with-pred-ℤ (succ n) (succ m) 𝟎
   III = ap (pred-ℤ ^ succ m) ((pos-is-succ-ℤ-iterated n) ⁻¹)
+ℤ-is-commutative (neg n) (pos m) =
 (pred-ℤ ^ succ n) (pos m)               ＝⟨ I    ⟩
 (pred-ℤ ^ succ n) ((succ-ℤ ^ succ m) 𝟎) ＝⟨ II   ⟩
 (succ-ℤ ^ succ m) ((pred-ℤ ^ succ n) 𝟎) ＝⟨ III  ⟩
 (succ-ℤ ^ succ m) (neg n)               ＝⟨ refl ⟩
 pos m +ℤ neg n                          ∎
  where
   I   = ap (pred-ℤ ^ succ n) (pos-is-succ-ℤ-iterated m)
   II  = commute-with-iterated-functions pred-ℤ succ-ℤ
          pred-ℤ-commutes-with-succ-ℤ (succ n) (succ m) 𝟎
   III = ap (succ-ℤ ^ succ m) ((neg-is-pred-ℤ-iterated n) ⁻¹)
+ℤ-is-commutative (neg n) (neg m) =
 (pred-ℤ ^ succ n) (neg m)               ＝⟨ I    ⟩
 (pred-ℤ ^ succ n) ((pred-ℤ ^ succ m) 𝟎) ＝⟨ II   ⟩
 (pred-ℤ ^ succ m) ((pred-ℤ ^ succ n) 𝟎) ＝⟨ III  ⟩
 (pred-ℤ ^ succ m) (neg n)               ＝⟨ refl ⟩
 neg m +ℤ neg n                          ∎
  where
   I   = ap (pred-ℤ ^ succ n) (neg-is-pred-ℤ-iterated m)
   II  = commute-with-iterated-functions pred-ℤ pred-ℤ
          (λ x → refl) (succ n) (succ m) 𝟎
   III = ap (pred-ℤ ^ succ m) ((neg-is-pred-ℤ-iterated n) ⁻¹)

\end{code}

Next is negation of integers.

\begin{code}

─_ : ℤ → ℤ
─ 𝟎       = 𝟎
─ (pos n) = neg n
─ (neg n) = pos n

─-is-linv : (x : ℤ) → x +ℤ (─ x) ＝ 𝟎
─-is-linv 𝟎 = refl
─-is-linv (pos n) =
 (succ-ℤ ^ succ n) (neg n)               ＝⟨ I  ⟩
 (succ-ℤ ^ succ n) ((pred-ℤ ^ succ n) 𝟎) ＝⟨ II ⟩
 𝟎                                       ∎
  where
   I  = ap (succ-ℤ ^ succ n) (neg-is-pred-ℤ-iterated n)
   II = succ-ℤ^n-is-retraction (succ n) 𝟎
─-is-linv (neg n) =
 (pred-ℤ ^ succ n) (pos n)               ＝⟨ I  ⟩
 (pred-ℤ ^ succ n) ((succ-ℤ ^ succ n) 𝟎) ＝⟨ II ⟩
 𝟎                                       ∎
  where
   I  = ap (pred-ℤ ^ succ n) (pos-is-succ-ℤ-iterated n)
   II = succ-ℤ^n-is-section (succ n) 𝟎

─-is-involutive : (x : ℤ) → ─ ─ x ＝ x
─-is-involutive 𝟎       = refl
─-is-involutive (pos n) = refl
─-is-involutive (neg n) = refl

─-is-rinv : (x : ℤ) → (─ x) +ℤ x ＝ 𝟎
─-is-rinv x = (─ x) +ℤ x ＝⟨ +ℤ-is-commutative (─ x) x ⟩
              x +ℤ (─ x) ＝⟨ ─-is-linv x               ⟩
              𝟎          ∎

\end{code}

Finally, we prove some lemmas on adding/shifting by a fixed integer.

\begin{code}

+ℤ-is-equiv-left : (x : ℤ) → is-equiv (λ y → x +ℤ y)
+ℤ-is-equiv-left 𝟎       = id-is-equiv ℤ
+ℤ-is-equiv-left (pos n) = iterated-function-is-equiv succ-ℤ succ-ℤ-is-equiv (succ n)
+ℤ-is-equiv-left (neg n) = iterated-function-is-equiv pred-ℤ pred-ℤ-is-equiv (succ n)

+ℤ-is-equiv-right : (y : ℤ) → is-equiv (λ x → x +ℤ y)
+ℤ-is-equiv-right y = equiv-closed-under-∼ (λ x → y +ℤ x) (λ x → x +ℤ y)
                  (+ℤ-is-equiv-left y) (λ x → +ℤ-is-commutative x y)

shift-if-commute-with-succ-ℤ : (f : ℤ → ℤ)
                             → f ∘ succ-ℤ ∼ succ-ℤ ∘ f
                             → f ∼ (λ x → x +ℤ f 𝟎)
shift-if-commute-with-succ-ℤ f h 𝟎 = refl
shift-if-commute-with-succ-ℤ f h (pos n) =
 f (pos n)                 ＝⟨ ap f (pos-is-succ-ℤ-iterated n) ⟩
 f ((succ-ℤ ^ succ n) 𝟎)   ＝⟨ commute-with-iterated-function
                               f succ-ℤ h (succ n) 𝟎          ⟩
 (succ-ℤ ^ (succ n)) (f 𝟎) ∎
shift-if-commute-with-succ-ℤ f h (neg n) =
 f (neg n)                 ＝⟨ ap f (neg-is-pred-ℤ-iterated n)                ⟩
 f ((pred-ℤ ^ succ n) 𝟎)   ＝⟨ commute-with-iterated-function
                               f pred-ℤ (commute-with-pred-ℤ f h) (succ n) 𝟎 ⟩
 (pred-ℤ ^ (succ n)) (f 𝟎) ∎

left-shift-commutes-with-succ-ℤ : (x : ℤ)
                                → (λ y → x +ℤ y) ∘ succ-ℤ
                                ∼ succ-ℤ ∘ (λ y → x +ℤ y)
left-shift-commutes-with-succ-ℤ 𝟎 y = refl
left-shift-commutes-with-succ-ℤ (pos n) y =
 (commute-with-succ-ℤ^n succ-ℤ (λ _ → refl) (succ n) y) ⁻¹
left-shift-commutes-with-succ-ℤ (neg n) y =
 (commute-with-pred-ℤ^n succ-ℤ (λ _ → refl) (succ n) y) ⁻¹

right-shift-commutes-with-succ-ℤ : (y : ℤ)
                                 → (λ x → x +ℤ y) ∘ succ-ℤ
                                 ∼ succ-ℤ ∘ (λ x → x +ℤ y)
right-shift-commutes-with-succ-ℤ y x =
 (succ-ℤ x) +ℤ y ＝⟨ +ℤ-is-commutative (succ-ℤ x) y      ⟩
 y +ℤ (succ-ℤ x) ＝⟨ left-shift-commutes-with-succ-ℤ y x ⟩
 succ-ℤ (y +ℤ x) ＝⟨ ap succ-ℤ (+ℤ-is-commutative y x)   ⟩
 succ-ℤ (x +ℤ y) ∎

is-equiv-if-commute-with-succ-ℤ : (f : ℤ → ℤ)
                                → f ∘ succ-ℤ ∼ succ-ℤ ∘ f
                                → is-equiv f
is-equiv-if-commute-with-succ-ℤ f h =
 equiv-closed-under-∼ (λ x → x +ℤ f 𝟎) f
  (+ℤ-is-equiv-right (f 𝟎)) (shift-if-commute-with-succ-ℤ f h)

\end{code}
