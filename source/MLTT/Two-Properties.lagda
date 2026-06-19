Martin Escardo

The two-point type is defined, together with its induction principle,
in the module SpartanMLTT. Here we develop some general machinery.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Two-Properties where

open import MLTT.Spartan
open import MLTT.Unit-Properties
open import Naturals.Properties
open import Notation.CanonicalMap
open import Notation.Order
open import UF.FunExt
open import UF.Retracts
open import UF.Subsingletons

𝟚-Cases : {A : 𝓤 ̇ } → 𝟚 → A → A → A
𝟚-Cases a b c = 𝟚-cases b c a

𝟚-cases-lemma : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) (a₀ a₁ : A) (b : 𝟚)
              → f (𝟚-cases a₀ a₁ b) ＝ 𝟚-cases (f a₀) (f a₁) b
𝟚-cases-lemma f a₀ a₁ ₀ = refl
𝟚-cases-lemma f a₀ a₁ ₁ = refl

𝟚-equality-cases : {A : 𝓤 ̇ } {b : 𝟚} → (b ＝ ₀ → A) → (b ＝ ₁ → A) → A
𝟚-equality-cases {𝓤} {A} {₀} f₀ f₁ = f₀ refl
𝟚-equality-cases {𝓤} {A} {₁} f₀ f₁ = f₁ refl

𝟚-equality-cases₀ : {A : 𝓤 ̇ }
                    {b : 𝟚}
                    {f₀ : b ＝ ₀ → A}
                    {f₁ : b ＝ ₁ → A}
                    (p : b ＝ ₀)
                  → 𝟚-equality-cases {𝓤} {A} {b} f₀ f₁ ＝ f₀ p
𝟚-equality-cases₀ {𝓤} {A} {₀} refl = refl

𝟚-equality-cases₁ : {A : 𝓤 ̇ }
                    {b : 𝟚}
                    {f₀ : b ＝ ₀ → A}
                    {f₁ : b ＝ ₁ → A}
                    (p : b ＝ ₁)
                  → 𝟚-equality-cases {𝓤} {A} {b} f₀ f₁ ＝ f₁ p
𝟚-equality-cases₁ {𝓤} {A} {.₁} refl = refl

𝟚-equality-cases' : {A₀ A₁ : 𝓤 ̇ } {b : 𝟚}
                  → (b ＝ ₀ → A₀) → (b ＝ ₁ → A₁) → A₀ + A₁
𝟚-equality-cases' {𝓤} {A₀} {A₁} {₀} f₀ f₁ = inl (f₀ refl)
𝟚-equality-cases' {𝓤} {A₀} {A₁} {₁} f₀ f₁ = inr (f₁ refl)

𝟚-possibilities : (b : 𝟚) → (b ＝ ₀) + (b ＝ ₁)
𝟚-possibilities ₀ = inl refl
𝟚-possibilities ₁ = inr refl

𝟚-excluded-third : (b : 𝟚) → b ≠ ₀ → b ≠ ₁ → 𝟘 {𝓤₀}
𝟚-excluded-third ₀ u v = u refl
𝟚-excluded-third ₁ u v = v refl

𝟚-things-distinct-from-a-third-are-equal : (x y z : 𝟚) → x ≠ z → y ≠ z → x ＝ y
𝟚-things-distinct-from-a-third-are-equal ₀ ₀ z u v = refl
𝟚-things-distinct-from-a-third-are-equal ₀ ₁ z u v =
 𝟘-elim (𝟚-excluded-third z (≠-sym u) (≠-sym v))
𝟚-things-distinct-from-a-third-are-equal ₁ ₀ z u v =
 𝟘-elim (𝟚-excluded-third z (≠-sym v) (≠-sym u))
𝟚-things-distinct-from-a-third-are-equal ₁ ₁ z u v = refl

one-is-not-zero : ₁ ≠ ₀
one-is-not-zero p = 𝟙-is-not-𝟘 q
 where
  f : 𝟚 → 𝓤₀ ̇
  f ₀ = 𝟘
  f ₁ = 𝟙

  q : 𝟙 ＝ 𝟘
  q = ap f p

zero-is-not-one : ₀ ≠ ₁
zero-is-not-one p = one-is-not-zero (p ⁻¹)

𝟚-ext : {b c : 𝟚} → (b ＝ ₁ → c ＝ ₁) → (c ＝ ₁ → b ＝ ₁) → b ＝ c
𝟚-ext {₀} {₀} f g = refl
𝟚-ext {₀} {₁} f g = 𝟘-elim (zero-is-not-one (g refl))
𝟚-ext {₁} {₀} f g = 𝟘-elim (zero-is-not-one (f refl))
𝟚-ext {₁} {₁} f g = refl

equal-₁-different-from-₀ : {b : 𝟚} → b ＝ ₁ → b ≠ ₀
equal-₁-different-from-₀ r s = zero-is-not-one (s ⁻¹ ∙ r)

different-from-₀-equal-₁ : {b : 𝟚} → b ≠ ₀ → b ＝ ₁
different-from-₀-equal-₁ f = 𝟚-equality-cases (𝟘-elim ∘ f) (λ r → r)

different-from-₁-equal-₀ : {b : 𝟚} → b ≠ ₁ → b ＝ ₀
different-from-₁-equal-₀ f = 𝟚-equality-cases (λ r → r) (𝟘-elim ∘ f)

equal-₀-different-from-₁ : {b : 𝟚} → b ＝ ₀ → b ≠ ₁
equal-₀-different-from-₁ r s = zero-is-not-one (r ⁻¹ ∙ s)

[a＝₁→b＝₁]-gives-[b＝₀→a＝₀] : {a b : 𝟚} → (a ＝ ₁ → b ＝ ₁) → b ＝ ₀ → a ＝ ₀
[a＝₁→b＝₁]-gives-[b＝₀→a＝₀] f =
 different-from-₁-equal-₀ ∘ (contrapositive f) ∘ equal-₀-different-from-₁

[a＝₀→b＝₀]-gives-[b＝₁→a＝₁] : {a b : 𝟚} → (a ＝ ₀ → b ＝ ₀) → b ＝ ₁ → a ＝ ₁
[a＝₀→b＝₀]-gives-[b＝₁→a＝₁] f =
 different-from-₀-equal-₁ ∘ (contrapositive f) ∘ equal-₁-different-from-₀

\end{code}

𝟚-Characteristic function of equality on 𝟚:

\begin{code}

complement : 𝟚 → 𝟚
complement ₀ = ₁
complement ₁ = ₀

complement-no-fp : (n : 𝟚) → n ≠ complement n
complement-no-fp ₀ p = 𝟘-elim (zero-is-not-one p)
complement-no-fp ₁ p = 𝟘-elim (one-is-not-zero p)

complement-involutive : (b : 𝟚) → complement (complement b) ＝ b
complement-involutive ₀ = refl
complement-involutive ₁ = refl

complement-lc : (b c : 𝟚) → complement b ＝ complement c → b ＝ c
complement-lc ₀ ₀ refl = refl
complement-lc ₀ ₁ p    = p ⁻¹
complement-lc ₁ ₀ p    = p ⁻¹
complement-lc ₁ ₁ refl = refl

eq𝟚 : 𝟚 → 𝟚 → 𝟚
eq𝟚 ₀ n = complement n
eq𝟚 ₁ n = n

eq𝟚-equal : (m n : 𝟚) → eq𝟚 m n ＝ ₁ → m ＝ n
eq𝟚-equal ₀ n p = ap complement (p ⁻¹) ∙ complement-involutive n
eq𝟚-equal ₁ n p = p ⁻¹

equal-eq𝟚 : (m n : 𝟚) → m ＝ n → eq𝟚 m n ＝ ₁
equal-eq𝟚 ₀ ₀ refl = refl
equal-eq𝟚 ₁ ₁ refl = refl

\end{code}

Natural order of binary numbers:

\begin{code}

_<₂_ : (a b : 𝟚) → 𝓤₀ ̇
₀ <₂ ₀ = 𝟘
₀ <₂ ₁ = 𝟙
₁ <₂ b = 𝟘

_≤₂_ : (a b : 𝟚) → 𝓤₀ ̇
₀ ≤₂ b = 𝟙
₁ ≤₂ ₀ = 𝟘
₁ ≤₂ ₁ = 𝟙

instance
 strict-order-𝟚-𝟚 : Strict-Order 𝟚 𝟚
 _<_ {{strict-order-𝟚-𝟚}} = _<₂_

 order-𝟚-𝟚 : Order 𝟚 𝟚
 _≤_ {{order-𝟚-𝟚}} = _≤₂_

<₂-is-prop-valued : {b c : 𝟚} → is-prop (b < c)
<₂-is-prop-valued {₀} {₀} = 𝟘-is-prop
<₂-is-prop-valued {₀} {₁} = 𝟙-is-prop
<₂-is-prop-valued {₁} {c} = 𝟘-is-prop

≤₂-is-prop-valued : {b c : 𝟚} → is-prop (b ≤ c)
≤₂-is-prop-valued {₀} {c} = 𝟙-is-prop
≤₂-is-prop-valued {₁} {₀} = 𝟘-is-prop
≤₂-is-prop-valued {₁} {₁} = 𝟙-is-prop

<₂-criterion : {a b : 𝟚} → (a ＝ ₀) → (b ＝ ₁) → a < b
<₂-criterion {₀} {₁} refl refl = ⋆

<₂-criterion-converse : {a b : 𝟚} → a < b → (a ＝ ₀) × (b ＝ ₁)
<₂-criterion-converse {₀} {₁} l = refl , refl

≤₂-criterion : {a b : 𝟚} → (a ＝ ₁ → b ＝ ₁) → a ≤ b
≤₂-criterion {₀} {b} f = ⋆
≤₂-criterion {₁} {₀} f = 𝟘-elim (zero-is-not-one (f refl))
≤₂-criterion {₁} {₁} f = ⋆

≤₂-criterion-converse : {a b : 𝟚} → a ≤ b → a ＝ ₁ → b ＝ ₁
≤₂-criterion-converse {₁} {₁} l refl = refl

₀-smallest : {a b : 𝟚} → a ≤ b → b ＝ ₀ → a ＝ ₀
₀-smallest {₀} {b} l refl = refl

<₂-gives-≤₂ : {a b : 𝟚} → a < b → a ≤ b
<₂-gives-≤₂ {₀} {₀} ()
<₂-gives-≤₂ {₀} {₁} ⋆ = ⋆
<₂-gives-≤₂ {₁} {c} ()

<₂-trans : (a b c : 𝟚) → a < b → b < c → a < c
<₂-trans ₀ ₀ c l m = m
<₂-trans ₀ ₁ c l ()

Lemma[a＝₀→b<c→a<c] : {a b c : 𝟚} → a ＝ ₀ → b < c → a < c
Lemma[a＝₀→b<c→a<c] {₀} {₀} {c} refl l = l

Lemma[a<b→c≠₀→a<c] : {a b c : 𝟚} → a < b → c ≠ ₀ → a < c
Lemma[a<b→c≠₀→a<c] {₀} {₁} {₀} l ν = ν refl
Lemma[a<b→c≠₀→a<c] {₀} {₁} {₁} l ν = ⋆

₁-top : {b : 𝟚} → b ≤ ₁
₁-top {₀} = ⋆
₁-top {₁} = ⋆

₀-bottom : {b : 𝟚} → ₀ ≤ b
₀-bottom {₀} = ⋆
₀-bottom {₁} = ⋆

₁-maximal : {b : 𝟚} → ₁ ≤ b → b ＝ ₁
₁-maximal {₁} l = refl

₁-maximal-converse : {b : 𝟚} → b ＝ ₁ → ₁ ≤ b
₁-maximal-converse {₁} refl = ⋆

₀-minimal : {b : 𝟚} → b ≤ ₀ → b ＝ ₀
₀-minimal {₀} l = refl

₀-minimal-converse : {b : 𝟚} → b ＝ ₀ → b ≤ ₀
₀-minimal-converse {₀} refl = ⋆

_≤₂'_ : (a b : 𝟚) → 𝓤₀ ̇
a ≤₂' b = b ＝ ₀ → a ＝ ₀

≤₂-gives-≤₂' : {a b : 𝟚} → a ≤ b → a ≤₂' b
≤₂-gives-≤₂' {₀} {b} _ p = refl
≤₂-gives-≤₂' {₁} {₀} () p
≤₂-gives-≤₂' {₁} {₁} _ p = p

≤₂'-gives-≤₂ : {a b : 𝟚} → a ≤₂' b → a ≤ b
≤₂'-gives-≤₂ {₀} {b} _ = ⋆
≤₂'-gives-≤₂ {₁} {₀} l = 𝟘-elim (one-is-not-zero (l refl))
≤₂'-gives-≤₂ {₁} {₁} _ = ⋆

≤₂-refl : {b : 𝟚} → b ≤ b
≤₂-refl {₀} = ⋆
≤₂-refl {₁} = ⋆

≤₂-trans : (a b c : 𝟚) → a ≤ b → b ≤ c → a ≤ c
≤₂-trans ₀ b c l m = ⋆
≤₂-trans ₁ ₁ ₁ l m = ⋆

≤₂-anti : {a b : 𝟚} → a ≤ b → b ≤ a → a ＝ b
≤₂-anti {₀} {₀} l m = refl
≤₂-anti {₀} {₁} l ()
≤₂-anti {₁} {₀} () m
≤₂-anti {₁} {₁} l m = refl

min𝟚 : 𝟚 → 𝟚 → 𝟚
min𝟚 ₀ b = ₀
min𝟚 ₁ b = b

min𝟚-comm : (b c : 𝟚) → min𝟚 b c ＝ min𝟚 c b
min𝟚-comm ₀ ₀ = refl
min𝟚-comm ₀ ₁ = refl
min𝟚-comm ₁ ₀ = refl
min𝟚-comm ₁ ₁ = refl

min𝟚-idemp : (b : 𝟚) → min𝟚 b b ＝ b
min𝟚-idemp ₀ = refl
min𝟚-idemp ₁ = refl

min𝟚-property₀ : (b : 𝟚) → min𝟚 b ₀ ＝ ₀
min𝟚-property₀ ₀ = refl
min𝟚-property₀ ₁ = refl

min𝟚-preserves-≤ : {a b a' b' : 𝟚} → a ≤ a' → b ≤ b' → min𝟚 a b ≤ min𝟚 a' b'
min𝟚-preserves-≤ {₀} {b} {a'} {b'} l m = l
min𝟚-preserves-≤ {₁} {b} {₁}  {b'} l m = m

Lemma[minab≤₂a] : {a b : 𝟚} → min𝟚 a b ≤ a
Lemma[minab≤₂a] {₀} {b} = ⋆
Lemma[minab≤₂a] {₁} {₀} = ⋆
Lemma[minab≤₂a] {₁} {₁} = ⋆

Lemma[minab≤₂b] : {a b : 𝟚} → min𝟚 a b ≤ b
Lemma[minab≤₂b] {₀} {b} = ⋆
Lemma[minab≤₂b] {₁} {₀} = ⋆
Lemma[minab≤₂b] {₁} {₁} = ⋆

Lemma[min𝟚ab＝₁→b＝₁] : {a b : 𝟚} → min𝟚 a b ＝ ₁ → b ＝ ₁
Lemma[min𝟚ab＝₁→b＝₁] {₀} {₀} r = r
Lemma[min𝟚ab＝₁→b＝₁] {₀} {₁} r = refl
Lemma[min𝟚ab＝₁→b＝₁] {₁} {₀} r = r
Lemma[min𝟚ab＝₁→b＝₁] {₁} {₁} r = refl

Lemma[min𝟚ab＝₁→a＝₁] : {a b : 𝟚} → min𝟚 a b ＝ ₁ → a ＝ ₁
Lemma[min𝟚ab＝₁→a＝₁] {₀} r = r
Lemma[min𝟚ab＝₁→a＝₁] {₁} r = refl

Lemma[a＝₁→b＝₁→min𝟚ab＝₁] : {a b : 𝟚} → a ＝ ₁ → b ＝ ₁ → min𝟚 a b ＝ ₁
Lemma[a＝₁→b＝₁→min𝟚ab＝₁] {₁} {₁} p q = refl

Lemma[a≤₂b→min𝟚ab＝a] : {a b : 𝟚} → a ≤ b → min𝟚 a b ＝ a
Lemma[a≤₂b→min𝟚ab＝a] {₀} {b} p = refl
Lemma[a≤₂b→min𝟚ab＝a] {₁} {₁} p = refl

Lemma[min𝟚ab＝₀] : {a b : 𝟚} → (a ＝ ₀) + (b ＝ ₀) → min𝟚 a b ＝ ₀
Lemma[min𝟚ab＝₀] {₀} {b} (inl p) = refl
Lemma[min𝟚ab＝₀] {₀} {₀} (inr q) = refl
Lemma[min𝟚ab＝₀] {₁} {₀} (inr q) = refl

lemma[min𝟚ab＝₀] : {a b : 𝟚} → min𝟚 a b ＝ ₀ → (a ＝ ₀) + (b ＝ ₀)
lemma[min𝟚ab＝₀] {₀} {b} p = inl p
lemma[min𝟚ab＝₀] {₁} {b} p = inr p

max𝟚 : 𝟚 → 𝟚 → 𝟚
max𝟚 ₀ b = b
max𝟚 ₁ b = ₁

max𝟚-comm : (b c : 𝟚) → max𝟚 b c ＝ max𝟚 c b
max𝟚-comm ₀ ₀ = refl
max𝟚-comm ₀ ₁ = refl
max𝟚-comm ₁ ₀ = refl
max𝟚-comm ₁ ₁ = refl

max𝟚-idemp : (b : 𝟚) → max𝟚 b b ＝ b
max𝟚-idemp ₀ = refl
max𝟚-idemp ₁ = refl

max𝟚-lemma : {a b : 𝟚} → max𝟚 a b ＝ ₁ → (a ＝ ₁) + (b ＝ ₁)
max𝟚-lemma {₀} r = inr r
max𝟚-lemma {₁} r = inl refl

max𝟚-lemma-converse : {a b : 𝟚} → (a ＝ ₁) + (b ＝ ₁) → max𝟚 a b ＝ ₁
max𝟚-lemma-converse {₀} (inl r) = unique-from-𝟘 (zero-is-not-one r)
max𝟚-lemma-converse {₀} (inr r) = r
max𝟚-lemma-converse {₁} x       = refl

max𝟚-lemma' : {a b : 𝟚} → max𝟚 a b ＝ ₁ → (a ＝ ₀) × (b ＝ ₁)
                                       + (a ＝ ₁) × (b ＝ ₀)
                                       + (a ＝ ₁) × (b ＝ ₁)
max𝟚-lemma' {₀} {₁} r = inl (refl , refl)
max𝟚-lemma' {₁} {₀} r = inr (inl (refl , refl))
max𝟚-lemma' {₁} {₁} r = inr (inr (refl , refl))

max𝟚-lemma'' : {a b : 𝟚} → max𝟚 a b ＝ ₁ → (a ＝ ₁) × (b ＝ ₀)
                                        + (b ＝ ₁)
max𝟚-lemma'' {₁} {₀} r = inl (refl , refl)
max𝟚-lemma'' {₀} {₁} r = inr refl
max𝟚-lemma'' {₁} {₁} r = inr refl

max𝟚-preserves-≤ : {a b a' b' : 𝟚} → a ≤ a' → b ≤ b' → max𝟚 a b ≤ max𝟚 a' b'
max𝟚-preserves-≤ {₀} {b} {₀} {b'} l m = m
max𝟚-preserves-≤ {₀} {₀} {₁} {b'} l m = m
max𝟚-preserves-≤ {₀} {₁} {₁} {b'} l m = l
max𝟚-preserves-≤ {₁} {b} {₁} {b'} l m = l

max𝟚-₀-left : {a b : 𝟚} → max𝟚 a b ＝ ₀ → a ＝ ₀
max𝟚-₀-left {₀} {b} p = refl

max𝟚-₀-right : {a b : 𝟚} → max𝟚 a b ＝ ₀ → b ＝ ₀
max𝟚-₀-right {₀} {b} p = p

\end{code}

Addition modulo 2:

\begin{code}

_⊕_ : 𝟚 → 𝟚 → 𝟚
₀ ⊕ x = x
₁ ⊕ x = complement x

complement-of-eq𝟚-is-⊕ : (m n : 𝟚) → complement (eq𝟚 m n) ＝ m ⊕ n
complement-of-eq𝟚-is-⊕ ₀ n = complement-involutive n
complement-of-eq𝟚-is-⊕ ₁ n = refl

Lemma[b⊕b＝₀] : {b : 𝟚} → b ⊕ b ＝ ₀
Lemma[b⊕b＝₀] {₀} = refl
Lemma[b⊕b＝₀] {₁} = refl

Lemma[b＝c→b⊕c＝₀] : {b c : 𝟚} → b ＝ c → b ⊕ c ＝ ₀
Lemma[b＝c→b⊕c＝₀] {b} {c} r = ap (λ - → b ⊕ -) (r ⁻¹) ∙ (Lemma[b⊕b＝₀] {b})

Lemma[b⊕c＝₀→b＝c] : {b c : 𝟚} → b ⊕ c ＝ ₀ → b ＝ c
Lemma[b⊕c＝₀→b＝c] {₀} {₀} r = refl
Lemma[b⊕c＝₀→b＝c] {₀} {₁} r = r ⁻¹
Lemma[b⊕c＝₀→b＝c] {₁} {₀} r = r
Lemma[b⊕c＝₀→b＝c] {₁} {₁} r = refl

Lemma[b≠c→b⊕c＝₁] : {b c : 𝟚} → b ≠ c → b ⊕ c ＝ ₁
Lemma[b≠c→b⊕c＝₁] = different-from-₀-equal-₁ ∘ (contrapositive Lemma[b⊕c＝₀→b＝c])

Lemma[b⊕c＝₁→b≠c] : {b c : 𝟚} → b ⊕ c ＝ ₁ → b ≠ c
Lemma[b⊕c＝₁→b≠c] = (contrapositive Lemma[b＝c→b⊕c＝₀]) ∘ equal-₁-different-from-₀

complement₀ : {a : 𝟚} → complement a ＝ ₀ → a ＝ ₁
complement₀ {₁} refl = refl

complement₁ : {a : 𝟚} → complement a ＝ ₁ → a ＝ ₀
complement₁ {₀} refl = refl

complement₁-back : {a : 𝟚} → a ＝ ₀ → complement a ＝ ₁
complement₁-back {₀} refl = refl

complement₀-back : {a : 𝟚} → a ＝ ₁ → complement a ＝ ₀
complement₀-back {₁} refl = refl

complement-one-gives-argument-not-one : {a : 𝟚} → complement a ＝ ₁ → a ≠ ₁
complement-one-gives-argument-not-one {₀} _ = zero-is-not-one

argument-not-one-gives-complement-one : {a : 𝟚} → a ≠ ₁ → complement a ＝ ₁
argument-not-one-gives-complement-one {₀} ν = refl
argument-not-one-gives-complement-one {₁} ν = 𝟘-elim (ν refl)

complement-left : {b c : 𝟚} → complement b ≤ c → complement c ≤ b
complement-left {₀} {₁} l = ⋆
complement-left {₁} {₀} l = ⋆
complement-left {₁} {₁} l = ⋆

complement-right : {b c : 𝟚} → b ≤ complement c → c ≤ complement b
complement-right {₀} {₀} l = ⋆
complement-right {₀} {₁} l = ⋆
complement-right {₁} {₀} l = ⋆

complement-both-left : {b c : 𝟚} → complement b ≤ complement c → c ≤ b
complement-both-left {₀} {₀} l = ⋆
complement-both-left {₁} {₀} l = ⋆
complement-both-left {₁} {₁} l = ⋆

complement-both-right : {b c : 𝟚} → b ≤ c → complement c ≤ complement b
complement-both-right {₀} {₀} l = ⋆
complement-both-right {₀} {₁} l = ⋆
complement-both-right {₁} {₁} l = ⋆

⊕-involutive : {a b : 𝟚} → a ⊕ a ⊕ b ＝ b
⊕-involutive {₀} {b} = refl
⊕-involutive {₁} {b} = complement-involutive b

⊕-assoc : {a b c : 𝟚} → (a ⊕ b) ⊕ c ＝ a ⊕ (b ⊕ c)
⊕-assoc {₀} {b} {c} = refl
⊕-assoc {₁} {₀} {c} = refl
⊕-assoc {₁} {₁} {c} = (complement-involutive c)⁻¹

⊕-property₁ : {a b : 𝟚} (g : a ≥ b)
            → a ⊕ b ＝ ₁ → (a ＝ ₁) × (b ＝ ₀)
⊕-property₁ {₀} {₀} g ()
⊕-property₁ {₀} {₁} () p
⊕-property₁ {₁} {₀} g p = refl , refl

⊕-intro₀₀ : {a b : 𝟚} → a ＝ ₀ → b ＝ ₀ → a ⊕ b ＝ ₀
⊕-intro₀₀ {₀} {₀} p q = refl

⊕-intro₀₁ : {a b : 𝟚} → a ＝ ₀ → b ＝ ₁ → a ⊕ b ＝ ₁
⊕-intro₀₁ {₀} {₁} p q = refl

⊕-intro₁₀ : {a b : 𝟚} → a ＝ ₁ → b ＝ ₀ → a ⊕ b ＝ ₁
⊕-intro₁₀ {₁} {₀} p q = refl

⊕-intro₁₁ : {a b : 𝟚} → a ＝ ₁ → b ＝ ₁ → a ⊕ b ＝ ₀
⊕-intro₁₁ {₁} {₁} p q = refl

⊕-₀-right-neutral : {a : 𝟚} → a ⊕ ₀ ＝ a
⊕-₀-right-neutral {₀} = refl
⊕-₀-right-neutral {₁} = refl

⊕-₀-right-neutral' : {a b : 𝟚} → b ＝ ₀ → a ⊕ b ＝ a
⊕-₀-right-neutral' {₀} {₀} p = refl
⊕-₀-right-neutral' {₁} {₀} p = refl

⊕-left-complement : {a b : 𝟚} → b ＝ ₁ → a ⊕ b ＝ complement a
⊕-left-complement {₀} {₁} p = refl
⊕-left-complement {₁} {₁} p = refl

≤₂-add-left : (a b : 𝟚) → b ≤ a → a ⊕ b ≤ a
≤₂-add-left ₀ b = id
≤₂-add-left ₁ b = λ _ → ₁-top

≤₂-remove-left : (a b : 𝟚) → a ⊕ b ≤ a → b ≤ a
≤₂-remove-left ₀ b = id
≤₂-remove-left ₁ b = λ _ → ₁-top

Lemma[b＝₀+b＝₁] : {b : 𝟚} → (b ＝ ₀) + (b ＝ ₁)
Lemma[b＝₀+b＝₁] {₀} = inl refl
Lemma[b＝₀+b＝₁] {₁} = inr refl

Lemma[b≠₀→b＝₁] : {b : 𝟚} → ¬ (b ＝ ₀) → b ＝ ₁
Lemma[b≠₀→b＝₁] {₀} f = 𝟘-elim (f refl)
Lemma[b≠₀→b＝₁] {₁} f = refl

Lemma[b≠₁→b＝₀] : {b : 𝟚} → ¬ (b ＝ ₁) → b ＝ ₀
Lemma[b≠₁→b＝₀] {₀} f = refl
Lemma[b≠₁→b＝₀] {₁} f = 𝟘-elim (f refl)

𝟚-to-ℕ : 𝟚 → ℕ
𝟚-to-ℕ ₀ = 0
𝟚-to-ℕ ₁ = 1

instance
 Canonical-Map-𝟚-ℕ : Canonical-Map 𝟚 ℕ
 ι {{Canonical-Map-𝟚-ℕ}} = 𝟚-to-ℕ

𝟚-to-ℕ-is-lc : left-cancellable 𝟚-to-ℕ
𝟚-to-ℕ-is-lc {₀} {₀} refl = refl
𝟚-to-ℕ-is-lc {₀} {₁} r    = 𝟘-elim (positive-not-zero 0 (r ⁻¹))
𝟚-to-ℕ-is-lc {₁} {₀} r    = 𝟘-elim (positive-not-zero 0 r)
𝟚-to-ℕ-is-lc {₁} {₁} refl = refl

C-B-embedding : (ℕ → 𝟚) → (ℕ → ℕ)
C-B-embedding α = 𝟚-to-ℕ ∘ α

C-B-embedding-is-lc : funext 𝓤₀ 𝓤₀ → left-cancellable C-B-embedding
C-B-embedding-is-lc fe {α} {β} p = dfunext fe h
 where
  h : (n : ℕ) → α n ＝ β n
  h n = 𝟚-to-ℕ-is-lc (ap (λ - → - n) p)

𝟚-retract-of-ℕ : retract 𝟚 of ℕ
𝟚-retract-of-ℕ = r , s , rs
 where
  r : ℕ → 𝟚
  r 0        = ₀
  r (succ n) = ₁

  s : 𝟚 → ℕ
  s ₀ = 0
  s ₁ = 1

  rs : r ∘ s ∼ id
  rs ₀ = refl
  rs ₁ = refl

\end{code}

Fixities and precedences:

\begin{code}

infixr 31 _⊕_

\end{code}
