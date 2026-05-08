--------------------------------------------------------------------------------
title:          Transporting a distributive lattice along an equivalence
author:         Ayberk Tosun
date-started:   2024-04-22
date-completed: 2024-04-30
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
open import UF.FunExt
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

open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Homomorphism fe pt
open import Locales.DistributiveLattice.Isomorphism fe pt
open import Locales.Frame pt fe
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

module DistributiveLatticeResizing (L  : DistributiveLattice 𝓤)
                                   (Aᶜ : 𝓥 ̇ )
                                   (e  : ∣ L ∣ᵈ ≃ Aᶜ) where

 open DistributiveLattice L renaming (𝟏 to 𝟏L; 𝟎 to 𝟎L)

 s : ∣ L ∣ᵈ → Aᶜ
 s = ⌜ e ⌝

 r : Aᶜ → ∣ L ∣ᵈ
 r = inverse ⌜ e ⌝ (⌜⌝-is-equiv e)

\end{code}

The copy of the meet operation on type `A` is denoted `_∧ᶜ_` and is defined as:

\begin{code}

 _∧ᶜ_ : Aᶜ → Aᶜ → Aᶜ
 _∧ᶜ_ = λ x y → s (r x ∧ r y)

\end{code}

We can now prove that `s` and `r` map the two meet operations onto each other.

\begin{code}

 r-preserves-∧ : (x y : Aᶜ) → r (x ∧ᶜ y) ＝ r x ∧ r y
 r-preserves-∧ x y = inverses-are-retractions' e (r x ∧ r y)

 s-preserves-∧ : (x y : X) → s (x ∧ y) ＝ s x ∧ᶜ s y
 s-preserves-∧ x y = s (x ∧ y)             ＝⟨ Ⅰ ⟩
                     s (x ∧ r (s y))       ＝⟨ Ⅱ ⟩
                     s (r (s x) ∧ r (s y)) ∎
                      where
                       Ⅰ = ap (λ - → s (x ∧ -)) (inverses-are-retractions' e y) ⁻¹
                       Ⅱ = ap (λ - → s (- ∧ r (s y))) (inverses-are-retractions' e x ⁻¹)

\end{code}

Now, we do exactly the same thing for the join operation.

\begin{code}

 _∨ᶜ_ : Aᶜ → Aᶜ → Aᶜ
 _∨ᶜ_ = λ x y → s (r x ∨ r y)

 r-preserves-∨ : (x y : Aᶜ) → r (x ∨ᶜ y) ＝ r x ∨ r y
 r-preserves-∨ x y = inverses-are-retractions' e (r x ∨ r y)

 s-preserves-∨ : (x y : X) → s (x ∨ y) ＝ s x ∨ᶜ s y
 s-preserves-∨ x y =
  s (x ∨ y)                ＝⟨ Ⅰ    ⟩
  s (x ∨ r (s y))          ＝⟨ Ⅱ    ⟩
  s (r (s x) ∨ r (s y))    ＝⟨refl⟩
  s x ∨ᶜ s y               ∎
   where
    Ⅰ = ap (λ - → s (x ∨ -)) (inverses-are-retractions' e y ⁻¹)
    Ⅱ = ap (λ - → s (- ∨ r (s y))) (inverses-are-retractions' e x ⁻¹)

\end{code}

The bottom element of the new lattice is just `s 𝟎`

\begin{code}

 𝟎ᶜ : Aᶜ
 𝟎ᶜ = s 𝟎L

\end{code}

The top element is `s 𝟏`.

\begin{code}

 𝟏ᶜ : Aᶜ
 𝟏ᶜ = s 𝟏L

\end{code}

We now proceed to prove that `(Aᶜ , 𝟎ᶜ , 𝟏ᶜ , _∧ᶜ_ , _∨ᶜ_)` forms a
distributive lattice. We refer to this as the _𝓥-small copy_ of `L`.

We start with the unit laws.

\begin{code}

 ∧ᶜ-unit : (x : Aᶜ) → x ∧ᶜ 𝟏ᶜ ＝ x
 ∧ᶜ-unit x =
  s (r x ∧ r (s 𝟏L)) ＝⟨ Ⅰ ⟩
  s (r x ∧ 𝟏L)       ＝⟨ Ⅱ ⟩
  s (r x)            ＝⟨ Ⅲ ⟩
  x                  ∎
   where
    Ⅰ = ap (λ - → s (r x ∧ -)) (inverses-are-retractions' e 𝟏L)
    Ⅱ = ap s (∧-unit (r x))
    Ⅲ = inverses-are-sections' e x


 ∨ᶜ-unit : (x : Aᶜ) → x ∨ᶜ 𝟎ᶜ ＝ x
 ∨ᶜ-unit x =
  s (r x ∨ r (s 𝟎L)) ＝⟨ Ⅰ ⟩
  s (r x ∨ 𝟎L)       ＝⟨ Ⅱ ⟩
  s (r x)            ＝⟨ Ⅲ ⟩
  x                  ∎
   where
    Ⅰ = ap (λ - → s (r x ∨ -)) (inverses-are-retractions' e 𝟎L)
    Ⅱ = ap s (∨-unit (r x))
    Ⅲ = inverses-are-sections' e x

\end{code}

Associativity laws.

\begin{code}

 ∧ᶜ-is-associative : (x y z : Aᶜ) → x ∧ᶜ (y ∧ᶜ z) ＝ (x ∧ᶜ y) ∧ᶜ z
 ∧ᶜ-is-associative x y z =
  x ∧ᶜ (y ∧ᶜ z)                ＝⟨refl⟩
  s (r x ∧ r (s (r y ∧ r z)))  ＝⟨ Ⅰ    ⟩
  s (r x ∧ (r y ∧ r z))        ＝⟨ Ⅱ    ⟩
  s ((r x ∧ r y) ∧ r z)        ＝⟨ Ⅲ    ⟩
  s (r (s (r x ∧ r y)) ∧ r z)  ＝⟨refl⟩
  s (r (s (r x ∧ r y)) ∧ r z)  ＝⟨refl⟩
  (x ∧ᶜ y) ∧ᶜ z                ∎
   where
    Ⅰ = ap (λ - → s (r x ∧ -)) (inverses-are-retractions' e (r y ∧ r z))
    Ⅱ = ap s (∧-associative (r x) (r y) (r z))
    Ⅲ = ap (λ - → s (- ∧ r z)) (inverses-are-retractions' e (r x ∧ r y) ⁻¹)

 ∨ᶜ-associative : (x y z : Aᶜ) → x ∨ᶜ (y ∨ᶜ z) ＝ (x ∨ᶜ y) ∨ᶜ z
 ∨ᶜ-associative x y z =
  x ∨ᶜ (y ∨ᶜ z)                ＝⟨refl⟩
  s (r x ∨ r (s (r y ∨ r z)))  ＝⟨ Ⅰ    ⟩
  s (r x ∨ (r y ∨ r z))        ＝⟨ Ⅱ    ⟩
  s ((r x ∨ r y) ∨ r z)        ＝⟨ Ⅲ    ⟩
  s (r (s (r x ∨ r y)) ∨ r z)  ＝⟨refl⟩
  s (r (s (r x ∨ r y)) ∨ r z)  ＝⟨refl⟩
  (x ∨ᶜ y) ∨ᶜ z                ∎
   where
    Ⅰ = ap (λ - → s (r x ∨ -)) (inverses-are-retractions' e (r y ∨ r z))
    Ⅱ = ap s (∨-associative (r x) (r y) (r z))
    Ⅲ = ap (λ - → s (- ∨ r z)) (inverses-are-retractions' e (r x ∨ r y) ⁻¹)

\end{code}

Commutativity laws.

\begin{code}

 ∧ᶜ-is-commutative : (x y : Aᶜ) → x ∧ᶜ y ＝ y ∧ᶜ x
 ∧ᶜ-is-commutative x y = ap s (∧-commutative (r x) (r y))

 ∨ᶜ-commutative : (x y : Aᶜ) → x ∨ᶜ y ＝ y ∨ᶜ x
 ∨ᶜ-commutative x y = ap s (∨-commutative (r x) (r y))

\end{code}

Idempotency laws.

\begin{code}

 ∧ᶜ-idempotent : (x : Aᶜ) → x ∧ᶜ x ＝ x
 ∧ᶜ-idempotent x =
  s (r x ∧ r x) ＝⟨ Ⅰ ⟩
  s (r x)       ＝⟨ Ⅱ ⟩
  x             ∎
   where
    Ⅰ = ap s (∧-idempotent (r x))
    Ⅱ = inverses-are-sections' e x

 ∨ᶜ-idempotent : (x : Aᶜ) → x ∨ᶜ x ＝ x
 ∨ᶜ-idempotent x =
   s (r x ∨ r x) ＝⟨ Ⅰ ⟩
   s (r x)       ＝⟨ Ⅱ ⟩
   x             ∎
    where
     Ⅰ = ap s (∨-idempotent (r x))
     Ⅱ = inverses-are-sections' e x

\end{code}

Absorption laws.

\begin{code}

 ∧ᶜ-absorptive : (x y : Aᶜ) → x ∧ᶜ (x ∨ᶜ y) ＝ x
 ∧ᶜ-absorptive x y =
  s (r x ∧ r (s (r x ∨ r y)))   ＝⟨ Ⅰ ⟩
  s (r x ∧ (r x ∨ r y))         ＝⟨ Ⅱ ⟩
  s (r x)                       ＝⟨ Ⅲ ⟩
  x                             ∎
   where
    Ⅰ = ap (λ - → s (r x ∧ -)) (inverses-are-retractions' e (r x ∨ r y))
    Ⅱ = ap s (∧-absorptive (r x) (r y))
    Ⅲ = inverses-are-sections' e x

 ∨ᶜ-absorptive : (x y : Aᶜ) → x ∨ᶜ (x ∧ᶜ y) ＝ x
 ∨ᶜ-absorptive x y =
  x ∨ᶜ (x ∧ᶜ y)                 ＝⟨refl⟩
  s (r x ∨ r (s (r x ∧ r y)))   ＝⟨ Ⅰ    ⟩
  s (r x ∨ (r x ∧ r y))         ＝⟨ Ⅱ    ⟩
  s (r x)                       ＝⟨ Ⅲ    ⟩
  x                             ∎
   where
    Ⅰ = ap (λ - → s (r x ∨ -)) (inverses-are-retractions' e (r x ∧ r y))
    Ⅱ = ap s (∨-absorptive (r x) (r y))
    Ⅲ = inverses-are-sections' e x

\end{code}

Finally, the distributivity law.

\begin{code}

 distributivityᶜ : (x y z : Aᶜ) → x ∧ᶜ (y ∨ᶜ z) ＝ (x ∧ᶜ y) ∨ᶜ (x ∧ᶜ z)
 distributivityᶜ x y z =
  x ∧ᶜ (y ∨ᶜ z)                             ＝⟨refl⟩
  s (r x ∧ r (s (r y ∨ r z)))               ＝⟨ Ⅰ    ⟩
  s (r x ∧ (r y ∨ r z))                     ＝⟨ Ⅱ    ⟩
  s ((r x ∧ r y) ∨ (r x ∧ r z))             ＝⟨ Ⅲ    ⟩
  s ((r x ∧ r y) ∨ r (s (r x ∧ r z)))       ＝⟨ Ⅳ    ⟩
  s (r (s (r x ∧ r y)) ∨ r (s (r x ∧ r z))) ＝⟨refl⟩
  s (r (x ∧ᶜ y) ∨ r (x ∧ᶜ z))               ＝⟨refl⟩
  (x ∧ᶜ y) ∨ᶜ (x ∧ᶜ z)                      ∎
   where
    Ⅰ = ap (λ - → s (r x ∧ -)) (inverses-are-retractions' e (r y ∨ r z))
    Ⅱ = ap s (distributivityᵈ (r x) (r y) (r z))
    Ⅲ = ap (λ - → s ((r x ∧ r y) ∨ -)) (inverses-are-retractions' e (r x ∧ r z) ⁻¹)
    Ⅳ = ap (λ - → s (- ∨ r (s (r x ∧ r z)))) (inverses-are-retractions' e (r x ∧ r y) ⁻¹)

\end{code}

We package everything up into `copyᵈ` below.

\begin{code}

 Lᶜ : DistributiveLattice 𝓥
 Lᶜ = record
       { X               = Aᶜ
       ; 𝟏               = 𝟏ᶜ
       ; 𝟎               = 𝟎ᶜ
       ; _∧_             = _∧ᶜ_
       ; _∨_             = _∨ᶜ_
       ; X-is-set        = equiv-to-set
                            (≃-sym e)
                            carrier-of-[ poset-ofᵈ L ]-is-set
       ; ∧-associative   = ∧ᶜ-is-associative
       ; ∧-commutative   = ∧ᶜ-is-commutative
       ; ∧-unit          = ∧ᶜ-unit
       ; ∧-idempotent    = ∧ᶜ-idempotent
       ; ∧-absorptive    = ∧ᶜ-absorptive
       ; ∨-associative   = ∨ᶜ-associative
       ; ∨-commutative   = ∨ᶜ-commutative
       ; ∨-unit          = ∨ᶜ-unit
       ; ∨-idempotent    = ∨ᶜ-idempotent
       ; ∨-absorptive    = ∨ᶜ-absorptive
       ; distributivityᵈ = distributivityᶜ
      }

 ⦅_⦆ᶜ : DistributiveLattice 𝓥
 ⦅_⦆ᶜ = Lᶜ

 s-preserves-𝟏 : preserves-𝟏 L Lᶜ s holds
 s-preserves-𝟏 = refl

 s-preserves-𝟎 : preserves-𝟎 L Lᶜ s holds
 s-preserves-𝟎 = refl

\end{code}

We package `s` up with the proof that it is a homomorphism, and call it
`sₕ`.

\begin{code}

 sₕ : L ─d→ Lᶜ
 sₕ =
  record
   { h                 = s
   ; h-is-homomorphism = α , β , γ , δ
  }
    where
     α : preserves-𝟏 L Lᶜ s holds
     α = refl

     β : preserves-∧ L Lᶜ s holds
     β = s-preserves-∧

     γ : preserves-𝟎 L Lᶜ s holds
     γ = s-preserves-𝟎

     δ : preserves-∨ L Lᶜ s holds
     δ = s-preserves-∨

\end{code}

Now, we we do the same thing for `r`

\begin{code}

 rₕ : Lᶜ ─d→ L
 rₕ =
  record
   { h                 = r
   ; h-is-homomorphism = α , β , γ , δ
  }
    where
     α : preserves-𝟏 Lᶜ L r holds
     α = inverses-are-retractions' e 𝟏L

     β : preserves-∧ Lᶜ L r holds
     β = r-preserves-∧

     γ : preserves-𝟎 Lᶜ L r holds
     γ = inverses-are-retractions' e 𝟎L

     δ : preserves-∨ Lᶜ L r holds
     δ = r-preserves-∨

 s-is-homomorphism : is-homomorphismᵈ L Lᶜ s holds
 s-is-homomorphism = Homomorphismᵈᵣ.h-is-homomorphism sₕ

 r-is-homomorphism : is-homomorphismᵈ Lᶜ L r holds
 r-is-homomorphism = Homomorphismᵈᵣ.h-is-homomorphism rₕ

\end{code}

Combining the fact that `s` and `r` are parts of an equivalence with the rather
trivial proof that they are homomorphisms with respect to `Lᶜ`, we obtain
the fact that `L` is isomorphic to its 𝓥-small copy.

\begin{code}

 open DistributiveLatticeIsomorphisms

 copy-isomorphic-to-original : L ≅d≅ Lᶜ
 copy-isomorphic-to-original =
  record
   { 𝓈           = sₕ
   ; 𝓇           = rₕ
   ; r-cancels-s = inverses-are-retractions' e
   ; s-cancels-r = inverses-are-sections' e
  }

\end{code}
