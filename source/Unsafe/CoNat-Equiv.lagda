Alice Laroche, 4th of December 2024

We show that the type of conaturals defined by coinduction is
equivalent to the type of conaturals defined as generic convergent
sequences when assuming funext and that bisimilarity is equality.

\begin{code}

{-# OPTIONS --guardedness #-}

module Unsafe.CoNat-Equiv where

open import CoNaturals.Type
open import MLTT.Spartan
open import MLTT.Plus-Properties
open import MLTT.Two-Properties
open import UF.Equiv
open import UF.FunExt

\end{code}

This implementation of CoNat comes from the Cubical Agda Library.

\begin{code}

CoNat' : 𝓤₀ ̇
record CoNat : 𝓤₀ ̇

CoNat' = 𝟙 + CoNat
record CoNat where
 constructor conat
 coinductive
 field
  force : 𝟙 + CoNat

open CoNat public

pattern cozero = inl ⋆
pattern cosuc n = inr n

\end{code}

Because we can't reason about coinductive type equality in classical
Agda, we define an binary relation which is equivalent to equality.
The correctness of it is proven in the Cubical Agda Library.

Three types are needed in order to convince the termination checker
some functions terminates.

\begin{code}

record _＝C_ (x y : CoNat) : Set
data _＝C'_ (x y : CoNat') : Set
_＝C''_ : CoNat' → CoNat' → Set

cozero  ＝C'' cozero  = 𝟙
cozero  ＝C'' cosuc y = 𝟘
cosuc x ＝C'' cozero  = 𝟘
cosuc x ＝C'' cosuc y = x ＝C y

data _＝C'_  x y where
    con : x ＝C'' y → x ＝C' y

record _＝C_ x y where
 coinductive
 field
  prove : force x ＝C' force y
open _＝C_

\end{code}

We can at least show that the relation is an equivalence relation.

\begin{code}

＝C-refl : ∀ {x y} → x ＝ y → x ＝C y
＝C'-refl : ∀ {x y} → x ＝ y → x ＝C' y

＝C-refl p .prove = ＝C'-refl (ap force p)
＝C'-refl {cozero} {cozero}   p = con ⋆
＝C'-refl {cosuc _} {cosuc _} p = con (＝C-refl (inr-lc p))

＝C-sym  : ∀ {x y} → x ＝C y → y ＝C x
＝C'-sym : ∀ {x y} → x ＝C' y → y ＝C' x

＝C-sym p .prove = ＝C'-sym (p .prove)
＝C'-sym {cozero}  {cozero}  (con p) = con ⋆
＝C'-sym {cosuc _} {cosuc _} (con p) = con (＝C-sym p)

＝C-trans : ∀ {x y z} → x ＝C y → y ＝C z → x ＝C z
＝C'-trans : ∀ {x y z} → x ＝C' y → y ＝C' z → x ＝C' z

＝C-trans p q .prove = ＝C'-trans (p .prove) (q .prove)
＝C'-trans {cozero} {cozero} {cozero}   (con p) (con q) = con ⋆
＝C'-trans {cosuc _} {cosuc _} {cosuc _} (con p) (con q) = con (＝C-trans p q)

\end{code}

We give a mapping from CoNat' to ℕ → 2 and use it to define a
criterion for the relationship defined above.

\begin{code}

CoNat'-to-ℕ→𝟚 : CoNat' → (ℕ → 𝟚)
CoNat'-to-ℕ→𝟚 cozero  zero = ₀
CoNat'-to-ℕ→𝟚 cozero (succ n) = ₀
CoNat'-to-ℕ→𝟚 (cosuc x)  zero = ₁
CoNat'-to-ℕ→𝟚 (cosuc x) (succ n) = CoNat'-to-ℕ→𝟚 (x .force) n

CoNat-to-ℕ→𝟚 : CoNat → (ℕ → 𝟚)
CoNat-to-ℕ→𝟚 x = CoNat'-to-ℕ→𝟚 (x .force)

CoNat-equality-criterion : (x y : CoNat)
                         → ((n : ℕ) → CoNat-to-ℕ→𝟚 x n ＝ CoNat-to-ℕ→𝟚 y n)
                         → x ＝C y
CoNat-equality-criterion' : (x y : CoNat')
                          → ((n : ℕ) → CoNat'-to-ℕ→𝟚 x n ＝ CoNat'-to-ℕ→𝟚 y n)
                          → x ＝C' y

CoNat-equality-criterion x y f .prove =
 CoNat-equality-criterion' (x .force) (y .force) f

CoNat-equality-criterion' cozero cozero       f =
 con ⋆
CoNat-equality-criterion' cozero (cosuc x)    f =
 con (zero-is-not-one (f 0))
CoNat-equality-criterion' (cosuc x) (cozero)  f =
 con (one-is-not-zero (f 0))
CoNat-equality-criterion' (cosuc x) (cosuc y) f =
 con (CoNat-equality-criterion x y (f ∘ succ))

\end{code}

Finally we write functions ℕ∞ → CoNat and Conat → ℕ∞ and show that
they give an equivalence between ℕ∞ and CoNat, assuming function
extensionality and that our equivalence relation is a bisimilarity
relation.

\begin{code}

f : ℕ∞ → CoNat
f' : 𝟚 → ℕ∞ → CoNat'

f x .force = f' (ℕ∞-to-ℕ→𝟚 x 0) x
f' ₀ x = cozero
f' ₁ x = cosuc (f (Pred x))

is-decreasing-CoNat'-to-ℕ→𝟚 : ∀ x → is-decreasing (CoNat'-to-ℕ→𝟚 x)
is-decreasing-CoNat'-to-ℕ→𝟚 (cozero)   zero    = ⋆
is-decreasing-CoNat'-to-ℕ→𝟚 (cozero)  (succ n) = ⋆
is-decreasing-CoNat'-to-ℕ→𝟚 (cosuc x)  zero    = ₁-top
is-decreasing-CoNat'-to-ℕ→𝟚 (cosuc x) (succ n) = is-decreasing-CoNat'-to-ℕ→𝟚
                                                  (x .force)
                                                  n

is-decreasing-CoNat-to-ℕ→𝟚 : ∀ x → is-decreasing (CoNat-to-ℕ→𝟚 x)
is-decreasing-CoNat-to-ℕ→𝟚 x n = is-decreasing-CoNat'-to-ℕ→𝟚 (x .force) n

g : CoNat → ℕ∞
g x = CoNat-to-ℕ→𝟚 x , is-decreasing-CoNat-to-ℕ→𝟚 x

CoNat≈ℕ∞ : funext₀
         → (bisim : ∀ x y → x ＝C y → x ＝ y)
         → ℕ∞ ≃ CoNat
CoNat≈ℕ∞ fe bisim = f , (g , λ - → bisim _ _ (f∘g∼id -)) , (g , g∘f∼id)
 where
  g∘f∼id : g ∘ f ∼ id
  g∘f∼id x = ℕ∞-to-ℕ→𝟚-lc fe (dfunext fe (I x _ refl))
   where
    I : (x : ℕ∞)
      → (b : 𝟚) → b ＝ ℕ∞-to-ℕ→𝟚 x 0
      → (n : ℕ)
      → ℕ∞-to-ℕ→𝟚 (g (f x)) n ＝ ℕ∞-to-ℕ→𝟚 x n
    I x ₀ eq zero = ap (λ - → ℕ∞-to-ℕ→𝟚 (g (conat (f' - x))) zero) eq ⁻¹ ∙ eq
    I x ₁ eq zero = ap (λ - → ℕ∞-to-ℕ→𝟚 (g (conat (f' - x))) zero) eq ⁻¹ ∙ eq
    I x ₀ eq (succ n) = ap (λ - → ℕ∞-to-ℕ→𝟚 (g (conat (f' - x))) (succ n)) eq ⁻¹
                      ∙ ap (λ - → ℕ∞-to-ℕ→𝟚 - (succ n))
                        ( is-Zero-equal-Zero fe {g (conat cozero)} refl
                        ∙ is-Zero-equal-Zero fe {x} (eq ⁻¹) ⁻¹)
    I x ₁ eq (succ n) = ap (λ - → ℕ∞-to-ℕ→𝟚 (g (conat (f' - x))) (succ n)) eq ⁻¹
                      ∙ I (Pred x) _ refl n

  f∘g∼id : (x : CoNat) → f (g x) ＝C x
  f∘g∼id x = CoNat-equality-criterion _ _ (I (x .force))
   where
    I : (x : CoNat')
      → (n : ℕ) → CoNat-to-ℕ→𝟚 (f (g (conat x))) n ＝ CoNat-to-ℕ→𝟚 (conat x) n
    I (cozero) zero = refl
    I (cosuc α) zero = refl
    I (cozero) (succ n) = refl
    I (cosuc α) (succ n) = I (α .force) n

\end{code}
