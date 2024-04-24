--------------------------------------------------------------------------------
title:          Transporting a distributive lattice along an equivalence
author:         Ayberk Tosun
date-started:   2024-04-22
--------------------------------------------------------------------------------

Given a distributive lattice `L : 𝓤` and an equivalence of the carrier set

    `e : ⟨ L ⟩ ≃ Aᶜ`

to some type `Aᶜ : 𝓥`, we can transport the distributive lattice `L` to
live in universe `𝓥` by copying over the distributive lattice structure from
`L` onto `Aᶜ`.

In this module, we prove this fact, and define some machinery for working with
such copies.

The superscript `(-)ᶜ` is intended to be mnemonic for "copy". We use this
convention to distinguish all distributive lattice operations from their copies
on `Aᶜ`.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import Slice.Family
open import UF.Base
open import UF.FunExt
open import UF.ImageAndSurjection
open import UF.PropTrunc
open import UF.Size
open import UF.SubtypeClassifier
open import UF.UA-FunExt
open import UF.Univalence

module Locales.DistributiveLattice.Resizing
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

open import Locales.Compactness pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.Frame pt fe
open import Locales.SmallBasis pt fe sr
open import UF.Equiv
open import UF.Logic
open import UF.Sets-Properties

open AllCombinators pt fe hiding (_∧_; _∨_)
open Locale
open PropositionalTruncation pt hiding (_∨_)

\end{code}

We work in an anonymous module parameterized by a distributive lattice `L : 𝓤`,
a type `A : 𝓥`, and an equivalence `e : ⟨ L ⟩ ≃ A`.

\begin{code}

module _ (L  : DistributiveLattice 𝓤)
         (A₀ : 𝓥  ̇)
         (e  : ∣ L ∣ᵈ ≃ A₀) where

 open DistributiveLattice L renaming (𝟏 to 𝟏L; 𝟎 to 𝟎L)

 s : ∣ L ∣ᵈ → A₀
 s = ⌜ e ⌝

 r : A₀ → ∣ L ∣ᵈ
 r = inverse ⌜ e ⌝ (⌜⌝-is-equiv e)

 r-cancels-s : r ∘ s ∼ id
 r-cancels-s = inverses-are-retractions s (⌜⌝-is-equiv e)

 s-cancels-r : s ∘ r ∼ id
 s-cancels-r x = pr₂ (pr₁ (pr₂ e)) x

\end{code}

The copy of the meet operation on type `A` is denoted `_∧₀_` and is defined
as:

\begin{code}

 _∧₀_ : A₀ → A₀ → A₀
 _∧₀_ = λ x y → s (r x ∧ r y)

\end{code}

We can now prove that `s` and `r` map the two meet operations onto each other.

\begin{code}

 r-preserves-∧ : (x y : A₀) → r (x ∧₀ y) ＝ r x ∧ r y
 r-preserves-∧ x y = r-cancels-s (r x ∧ r y)

 s-preserves-∧ : (x y : X) → s (x ∧ y) ＝ s x ∧₀ s y
 s-preserves-∧ x y = s (x ∧ y)             ＝⟨ Ⅰ ⟩
                     s (x ∧ r (s y))       ＝⟨ Ⅱ ⟩
                     s (r (s x) ∧ r (s y)) ∎
                      where
                       Ⅰ = ap (λ - → s (x ∧ -)) (r-cancels-s y) ⁻¹
                       Ⅱ = ap (λ - → s (- ∧ r (s y))) (r-cancels-s x ⁻¹)

\end{code}

Now, we do exactly the same thing for the join operation.

\begin{code}

 _∨₀_ : A₀ → A₀ → A₀
 _∨₀_ = λ x y → s (r x ∨ r y)

 r-preserves-∨ : (x y : A₀) → r (x ∨₀ y) ＝ r x ∨ r y
 r-preserves-∨ x y = r-cancels-s (r x ∨ r y)

 s-preserves-∨ : (x y : X) → s (x ∨ y) ＝ s x ∨₀ s y
 s-preserves-∨ x y =
  s (x ∨ y)                ＝⟨ Ⅰ    ⟩
  s (x ∨ r (s y))          ＝⟨ Ⅱ    ⟩
  s (r (s x) ∨ r (s y))    ＝⟨ refl ⟩
  s x ∨₀ s y               ∎
   where
    Ⅰ = ap (λ - → s (x ∨ -)) (r-cancels-s y ⁻¹)
    Ⅱ = ap (λ - → s (- ∨ r (s y))) (r-cancels-s x ⁻¹)

\end{code}

The bottom element of the new lattice is just `s 𝟎`

\begin{code}

 𝟎₀ : A₀
 𝟎₀ = s 𝟎L

\end{code}

The top element is `s 𝟏`.

\begin{code}

 𝟏₀ : A₀
 𝟏₀ = s 𝟏L

\end{code}

We now proceed to prove that `(A₀ , 𝟎₀ , 𝟏₀ , _∧₀_ , _∨₀_)` forms a
distributive lattice. We refer to this as the _𝓥-small copy_ of `L`.

We start with the unit laws.

\begin{code}

 ∧₀-unit : (x : A₀) → x ∧₀ 𝟏₀ ＝ x
 ∧₀-unit x =
  s (r x ∧ r (s 𝟏L)) ＝⟨ Ⅰ ⟩
  s (r x ∧ 𝟏L)       ＝⟨ Ⅱ ⟩
  s (r x)            ＝⟨ Ⅲ ⟩
  x                  ∎
   where
    Ⅰ = ap (λ - → s (r x ∧ -)) (r-cancels-s 𝟏L)
    Ⅱ = ap s (∧-unit (r x))
    Ⅲ = s-cancels-r x


 ∨₀-unit : (x : A₀) → x ∨₀ 𝟎₀ ＝ x
 ∨₀-unit x =
  s (r x ∨ r (s 𝟎L)) ＝⟨ Ⅰ ⟩
  s (r x ∨ 𝟎L)       ＝⟨ Ⅱ ⟩
  s (r x)            ＝⟨ Ⅲ ⟩
  x                  ∎
   where
    Ⅰ = ap (λ - → s (r x ∨ -)) (r-cancels-s 𝟎L)
    Ⅱ = ap s (∨-unit (r x))
    Ⅲ = s-cancels-r x

\end{code}

Associativity laws.

\begin{code}

 ∧₀-is-associative : (x y z : A₀) → x ∧₀ (y ∧₀ z) ＝ (x ∧₀ y) ∧₀ z
 ∧₀-is-associative x y z =
  x ∧₀ (y ∧₀ z)                ＝⟨ refl ⟩
  s (r x ∧ r (s (r y ∧ r z)))  ＝⟨ Ⅰ    ⟩
  s (r x ∧ (r y ∧ r z))        ＝⟨ Ⅱ    ⟩
  s ((r x ∧ r y) ∧ r z)        ＝⟨ Ⅲ    ⟩
  s (r (s (r x ∧ r y)) ∧ r z)  ＝⟨ refl ⟩
  s (r (s (r x ∧ r y)) ∧ r z)  ＝⟨ refl ⟩
  (x ∧₀ y) ∧₀ z                ∎
   where
    Ⅰ = ap (λ - → s (r x ∧ -)) (r-cancels-s (r y ∧ r z))
    Ⅱ = ap s (∧-associative (r x) (r y) (r z))
    Ⅲ = ap (λ - → s (- ∧ r z)) (r-cancels-s (r x ∧ r y) ⁻¹)

 ∨₀-associative : (x y z : A₀) → x ∨₀ (y ∨₀ z) ＝ (x ∨₀ y) ∨₀ z
 ∨₀-associative x y z =
  x ∨₀ (y ∨₀ z)                ＝⟨ refl ⟩
  s (r x ∨ r (s (r y ∨ r z)))  ＝⟨ Ⅰ    ⟩
  s (r x ∨ (r y ∨ r z))        ＝⟨ Ⅱ    ⟩
  s ((r x ∨ r y) ∨ r z)        ＝⟨ Ⅲ    ⟩
  s (r (s (r x ∨ r y)) ∨ r z)  ＝⟨ refl ⟩
  s (r (s (r x ∨ r y)) ∨ r z)  ＝⟨ refl ⟩
  (x ∨₀ y) ∨₀ z                ∎
   where
    Ⅰ = ap (λ - → s (r x ∨ -)) (r-cancels-s (r y ∨ r z))
    Ⅱ = ap s (∨-associative (r x) (r y) (r z))
    Ⅲ = ap (λ - → s (- ∨ r z)) (r-cancels-s (r x ∨ r y) ⁻¹)

\end{code}

Commutativity laws.

\begin{code}

 ∧₀-is-commutative : (x y : A₀) → x ∧₀ y ＝ y ∧₀ x
 ∧₀-is-commutative x y = ap s (∧-commutative (r x) (r y))

 ∨₀-commutative : (x y : A₀) → x ∨₀ y ＝ y ∨₀ x
 ∨₀-commutative x y = ap s (∨-commutative (r x) (r y))

\end{code}

Idempotency laws.

\begin{code}

 ∧₀-idempotent : (x : A₀) → x ∧₀ x ＝ x
 ∧₀-idempotent x =
  s (r x ∧ r x) ＝⟨ Ⅰ ⟩
  s (r x)       ＝⟨ Ⅱ ⟩
  x             ∎
   where
    Ⅰ = ap s (∧-idempotent (r x))
    Ⅱ = s-cancels-r x

 ∨₀-idempotent : (x : A₀) → x ∨₀ x ＝ x
 ∨₀-idempotent x =
   s (r x ∨ r x) ＝⟨ Ⅰ ⟩
   s (r x)       ＝⟨ Ⅱ ⟩
   x             ∎
    where
     Ⅰ = ap s (∨-idempotent (r x))
     Ⅱ = s-cancels-r x

\end{code}

Absorption laws.

\begin{code}

 ∧₀-absorptive : (x y : A₀) → x ∧₀ (x ∨₀ y) ＝ x
 ∧₀-absorptive x y =
  s (r x ∧ r (s (r x ∨ r y)))   ＝⟨ Ⅰ ⟩
  s (r x ∧ (r x ∨ r y))         ＝⟨ Ⅱ ⟩
  s (r x)                       ＝⟨ Ⅲ ⟩
  x                             ∎
   where
    Ⅰ = ap (λ - → s (r x ∧ -)) (r-cancels-s (r x ∨ r y))
    Ⅱ = ap s (∧-absorptive (r x) (r y))
    Ⅲ = s-cancels-r x

 ∨₀-absorptive : (x y : A₀) → x ∨₀ (x ∧₀ y) ＝ x
 ∨₀-absorptive x y =
  x ∨₀ (x ∧₀ y)                 ＝⟨ refl ⟩
  s (r x ∨ r (s (r x ∧ r y)))   ＝⟨ Ⅰ    ⟩
  s (r x ∨ (r x ∧ r y))         ＝⟨ Ⅱ    ⟩
  s (r x)                       ＝⟨ Ⅲ    ⟩
  x                             ∎
   where
    Ⅰ = ap (λ - → s (r x ∨ -)) (r-cancels-s (r x ∧ r y))
    Ⅱ = ap s (∨-absorptive (r x) (r y))
    Ⅲ = s-cancels-r x

\end{code}

Finally, the distributivity law.

\begin{code}

 distributivity₀ᵈ : (x y z : A₀) → x ∧₀ (y ∨₀ z) ＝ (x ∧₀ y) ∨₀ (x ∧₀ z)
 distributivity₀ᵈ x y z =
  x ∧₀ (y ∨₀ z)                             ＝⟨ refl ⟩
  s (r x ∧ r (s (r y ∨ r z)))               ＝⟨ Ⅰ    ⟩
  s (r x ∧ (r y ∨ r z))                     ＝⟨ Ⅱ    ⟩
  s ((r x ∧ r y) ∨ (r x ∧ r z))             ＝⟨ Ⅲ    ⟩
  s ((r x ∧ r y) ∨ r (s (r x ∧ r z)))       ＝⟨ Ⅳ    ⟩
  s (r (s (r x ∧ r y)) ∨ r (s (r x ∧ r z))) ＝⟨ refl ⟩
  s (r (x ∧₀ y) ∨ r (x ∧₀ z))               ＝⟨ refl ⟩
  (x ∧₀ y) ∨₀ (x ∧₀ z)                      ∎
   where
    Ⅰ = ap (λ - → s (r x ∧ -)) (r-cancels-s (r y ∨ r z))
    Ⅱ = ap s (distributivityᵈ (r x) (r y) (r z))
    Ⅲ = ap (λ - → s ((r x ∧ r y) ∨ -)) (r-cancels-s (r x ∧ r z) ⁻¹)
    Ⅳ = ap (λ - → s (- ∨ r (s (r x ∧ r z)))) (r-cancels-s (r x ∧ r y) ⁻¹)

\end{code}

We package everything up into `copyᵈ` below.

\begin{code}

 copyᵈ : DistributiveLattice 𝓥
 copyᵈ = record
          { X               = A₀
          ; 𝟏               = 𝟏₀
          ; 𝟎               = 𝟎₀
          ; _∧_             = _∧₀_
          ; _∨_             = _∨₀_
          ; X-is-set        = equiv-to-set
                               (≃-sym e)
                               carrier-of-[ poset-ofᵈ L ]-is-set
          ; ∧-associative   = ∧₀-is-associative
          ; ∧-commutative   = ∧₀-is-commutative
          ; ∧-unit          = ∧₀-unit
          ; ∧-idempotent    = ∧₀-idempotent
          ; ∧-absorptive    = ∧₀-absorptive
          ; ∨-associative   = ∨₀-associative
          ; ∨-commutative   = ∨₀-commutative
          ; ∨-unit          = ∨₀-unit
          ; ∨-idempotent    = ∨₀-idempotent
          ; ∨-absorptive    = ∨₀-absorptive
          ; distributivityᵈ = distributivity₀ᵈ
          }

\end{code}

\begin{code}

 s-preserves-𝟏 : preserves-𝟏 L copyᵈ s holds
 s-preserves-𝟏 = refl

 s-preserves-𝟎 : preserves-𝟎 L copyᵈ s holds
 s-preserves-𝟎 = refl

\end{code}

We package `s` up with the proof that it is a homomorphism, and call it
`sₕ`.

\begin{code}

 sₕ : L ─d→ copyᵈ
 sₕ = record
       { h                 = s
       ; h-is-homomorphism = α , β , γ , δ
       }
      where
       α : preserves-𝟏 L copyᵈ s holds
       α = refl

       β : preserves-∧ L copyᵈ s holds
       β = s-preserves-∧

       γ : preserves-𝟎 L copyᵈ s holds
       γ = s-preserves-𝟎

       δ : preserves-∨ L copyᵈ s holds
       δ = s-preserves-∨

\end{code}

Now, we we do the same thing for `r`

\begin{code}

 rₕ : copyᵈ ─d→ L
 rₕ =
  record
   { h                 = r
   ; h-is-homomorphism = α , β , γ , δ
   }
    where
     α : preserves-𝟏 copyᵈ L r holds
     α = r-cancels-s 𝟏L

     β : preserves-∧ copyᵈ L r holds
     β = r-preserves-∧

     γ : preserves-𝟎 copyᵈ L r holds
     γ = r-cancels-s 𝟎L

     δ : preserves-∨ copyᵈ L r holds
     δ = r-preserves-∨

\end{code}

\begin{code}

 s-is-homomorphism : is-homomorphismᵈ L copyᵈ s holds
 s-is-homomorphism = Homomorphismᵈᵣ.h-is-homomorphism sₕ

 r-is-homomorphism : is-homomorphismᵈ copyᵈ L r holds
 r-is-homomorphism = Homomorphismᵈᵣ.h-is-homomorphism rₕ

\end{code}

Combining the fact that `s` and `r` are parts of an equivalence with the rather
trivial proof that they are homomorphisms with respect to the 𝓥-small copy of
`L`, we obtain that `L` is isomorphic to its 𝓥-small copy.

\begin{code}

 open DistributiveLatticeIsomorphisms

 copy-isomorphic-to-original : L ≅d≅ copyᵈ
 copy-isomorphic-to-original =
  record
   { 𝓈           = sₕ
   ; 𝓇           = rₕ
   ; r-cancels-s = r-cancels-s
   ; s-cancels-r = s-cancels-r
   }

\end{code}
