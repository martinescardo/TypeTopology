Martin Escardo

The two-point type is defined, together with its induction principle,
in the module SpartanMLTT. Here we develop some general machinery.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Two-Properties where

open import SpartanMLTT
open import Unit-Properties

𝟚-Cases : {A : 𝓤 ̇ } → 𝟚 → A → A → A
𝟚-Cases a b c = 𝟚-cases b c a

𝟚-equality-cases : {A : 𝓤 ̇ } {b : 𝟚} → (b ≡ ₀ → A) → (b ≡ ₁ → A) → A
𝟚-equality-cases {𝓤} {A} {₀} f₀ f₁ = f₀ refl
𝟚-equality-cases {𝓤} {A} {₁} f₀ f₁ = f₁ refl

𝟚-equality-cases₀ : {A : 𝓤 ̇ } {b : 𝟚} {f₀ : b ≡ ₀ → A} {f₁ : b ≡ ₁ → A}
                  → (p : b ≡ ₀) → 𝟚-equality-cases {𝓤} {A} {b} f₀ f₁ ≡ f₀ p
𝟚-equality-cases₀ {𝓤} {A} {.₀} refl = refl

𝟚-equality-cases₁ : {A : 𝓤 ̇ } {b : 𝟚} {f₀ : b ≡ ₀ → A} {f₁ : b ≡ ₁ → A}
                  → (p : b ≡ ₁) → 𝟚-equality-cases {𝓤} {A} {b} f₀ f₁ ≡ f₁ p
𝟚-equality-cases₁ {𝓤} {A} {.₁} refl = refl

𝟚-equality-cases' : {A₀ A₁ : 𝓤 ̇ } {b : 𝟚} → (b ≡ ₀ → A₀) → (b ≡ ₁ → A₁) → A₀ + A₁
𝟚-equality-cases' {𝓤} {A₀} {A₁} {₀} f₀ f₁ = inl (f₀ refl)
𝟚-equality-cases' {𝓤} {A₀} {A₁} {₁} f₀ f₁ = inr (f₁ refl)

𝟚-possibilities : (b : 𝟚) → (b ≡ ₀) + (b ≡ ₁)
𝟚-possibilities ₀ = inl refl
𝟚-possibilities ₁ = inr refl


𝟚-excluded-third : (b : 𝟚) → b ≢ ₀ → b ≢ ₁ → 𝟘 {𝓤₀}
𝟚-excluded-third ₀ u v = u refl
𝟚-excluded-third ₁ u v = v refl

𝟚-things-distinct-from-a-third-are-equal : (x y z : 𝟚) → x ≢ z → y ≢ z → x ≡ y
𝟚-things-distinct-from-a-third-are-equal ₀ ₀ z u v = refl
𝟚-things-distinct-from-a-third-are-equal ₀ ₁ z u v = 𝟘-elim (𝟚-excluded-third z (≢-sym u) (≢-sym v))
𝟚-things-distinct-from-a-third-are-equal ₁ ₀ z u v = 𝟘-elim (𝟚-excluded-third z (≢-sym v) (≢-sym u))
𝟚-things-distinct-from-a-third-are-equal ₁ ₁ z u v = refl

one-is-not-zero : ₁ ≢ ₀
one-is-not-zero p = 𝟙-is-not-𝟘 q
 where
  f : 𝟚 → 𝓤₀ ̇
  f ₀ = 𝟘
  f ₁ = 𝟙

  q : 𝟙 ≡ 𝟘
  q = ap f p

zero-is-not-one : ₀ ≢ ₁
zero-is-not-one p = one-is-not-zero (p ⁻¹)

equal-₁-different-from-₀ : {b : 𝟚} → b ≡ ₁ → b ≢ ₀
equal-₁-different-from-₀ r s = zero-is-not-one (s ⁻¹ ∙ r)

different-from-₀-equal-₁ : {b : 𝟚} → b ≢ ₀ → b ≡ ₁
different-from-₀-equal-₁ f = 𝟚-equality-cases (𝟘-elim ∘ f) (λ r → r)

different-from-₁-equal-₀ : {b : 𝟚} → b ≢ ₁ → b ≡ ₀
different-from-₁-equal-₀ f = 𝟚-equality-cases (λ r → r) (𝟘-elim ∘ f)

equal-₀-different-from-₁ : {b : 𝟚} → b ≡ ₀ → b ≢ ₁
equal-₀-different-from-₁ r s = zero-is-not-one (r ⁻¹ ∙ s)

[a≡₁→b≡₁]-gives-[b≡₀→a≡₀] : {a b : 𝟚} → (a ≡ ₁ → b ≡ ₁) → b ≡ ₀ → a ≡ ₀
[a≡₁→b≡₁]-gives-[b≡₀→a≡₀] f = different-from-₁-equal-₀ ∘ (contrapositive f) ∘ equal-₀-different-from-₁

[a≡₀→b≡₀]-gives-[b≡₁→a≡₁] : {a b : 𝟚} → (a ≡ ₀ → b ≡ ₀) → b ≡ ₁ → a ≡ ₁
[a≡₀→b≡₀]-gives-[b≡₁→a≡₁] f = different-from-₀-equal-₁ ∘ (contrapositive f) ∘ equal-₁-different-from-₀

\end{code}

𝟚-Characteristic function of equality on 𝟚:

\begin{code}

complement : 𝟚 → 𝟚
complement ₀ = ₁
complement ₁ = ₀

complement-no-fp : (n : 𝟚) → n ≡ complement n → 𝟘 {𝓤}
complement-no-fp ₀ p = 𝟘-elim (zero-is-not-one p)
complement-no-fp ₁ p = 𝟘-elim (one-is-not-zero p)

complement-involutive : (b : 𝟚) → complement (complement b) ≡ b
complement-involutive ₀ = refl
complement-involutive ₁ = refl

eq𝟚 : 𝟚 → 𝟚 → 𝟚
eq𝟚 ₀ n = complement n
eq𝟚 ₁ n = n

eq𝟚-equal : (m n : 𝟚) → eq𝟚 m n ≡ ₁ → m ≡ n
eq𝟚-equal ₀ n p = ap complement (p ⁻¹) ∙ complement-involutive n
eq𝟚-equal ₁ n p = p ⁻¹

equal-eq𝟚 : (m n : 𝟚) → m ≡ n → eq𝟚 m n ≡ ₁
equal-eq𝟚 ₀ ₀ refl = refl
equal-eq𝟚 ₁ ₁ refl = refl

\end{code}

Natural order of binary numbers:

\begin{code}

_<₂_ : (a b : 𝟚) → 𝓤₀ ̇
a <₂ b = (a ≡ ₀) × (b ≡ ₁)

_≤₂_ : (a b : 𝟚) → 𝓤₀ ̇
a ≤₂ b = a ≡ ₁ → b ≡ ₁

<₂-gives-≤₂ : {a b : 𝟚} → a <₂ b → a ≤₂ b
<₂-gives-≤₂ (refl , refl) _ = refl

₁-top : {b : 𝟚} → b ≤₂ ₁
₁-top r = refl

₀-bottom : {b : 𝟚} → ₀ ≤₂ b
₀-bottom {b} p = 𝟘-elim (zero-is-not-one p)

_≤₂'_ : (a b : 𝟚) → 𝓤₀ ̇
a ≤₂' b = b ≡ ₀ → a ≡ ₀

≤₂-gives-≤₂' : {a b : 𝟚} → a ≤₂ b → a ≤₂' b
≤₂-gives-≤₂' {₀} {b} f p = refl
≤₂-gives-≤₂' {₁} {₀} f p = (f refl)⁻¹
≤₂-gives-≤₂' {₁} {₁} f p = p

≤₂'-gives-≤₂ : {a b : 𝟚} → a ≤₂' b → a ≤₂ b
≤₂'-gives-≤₂ {₀} {₀} f p = p
≤₂'-gives-≤₂ {₀} {₁} f p = refl
≤₂'-gives-≤₂ {₁} {₀} f p = (f refl)⁻¹
≤₂'-gives-≤₂ {₁} {₁} f p = p

≤₂-anti : {a b : 𝟚} → a ≤₂ b → b ≤₂ a → a ≡ b
≤₂-anti {₀} {₀} f g = refl
≤₂-anti {₀} {₁} f g = g refl
≤₂-anti {₁} {₀} f g = ≤₂-gives-≤₂' f refl
≤₂-anti {₁} {₁} f g = refl

₁-maximal : {b : 𝟚} → ₁ ≤₂ b → b ≡ ₁
₁-maximal = ≤₂-anti ₁-top

_≥₂_ : (a b : 𝟚) → 𝓤₀ ̇
a ≥₂ b = b ≤₂ a

min𝟚 : 𝟚 → 𝟚 → 𝟚
min𝟚 ₀ b = ₀
min𝟚 ₁ b = b

Lemma[minab≤₂a] : {a b : 𝟚} → min𝟚 a b ≤₂ a
Lemma[minab≤₂a] {₀} {b} r = 𝟘-elim (equal-₁-different-from-₀ r refl)
Lemma[minab≤₂a] {₁} {b} r = refl

Lemma[minab≤₂b] : {a b : 𝟚} → min𝟚 a b ≤₂ b
Lemma[minab≤₂b] {₀} {b} r = 𝟘-elim (equal-₁-different-from-₀ r refl)
Lemma[minab≤₂b] {₁} {b} r = r

Lemma[min𝟚ab≡₁→b≡₁] : {a b : 𝟚} → min𝟚 a b ≡ ₁ → b ≡ ₁
Lemma[min𝟚ab≡₁→b≡₁] {₀} {₀} r = r
Lemma[min𝟚ab≡₁→b≡₁] {₀} {₁} r = refl
Lemma[min𝟚ab≡₁→b≡₁] {₁} {₀} r = r
Lemma[min𝟚ab≡₁→b≡₁] {₁} {₁} r = refl

Lemma[min𝟚ab≡₁→a≡₁]  : {a b : 𝟚} → min𝟚 a b ≡ ₁ → a ≡ ₁
Lemma[min𝟚ab≡₁→a≡₁] {₀} r = r
Lemma[min𝟚ab≡₁→a≡₁] {₁} r = refl

Lemma[a≡₁→b≡₁→min𝟚ab≡₁] : {a b : 𝟚} → a ≡ ₁ → b ≡ ₁ → min𝟚 a b ≡ ₁
Lemma[a≡₁→b≡₁→min𝟚ab≡₁] {₀} {₀} p q = q
Lemma[a≡₁→b≡₁→min𝟚ab≡₁] {₀} {₁} p q = p
Lemma[a≡₁→b≡₁→min𝟚ab≡₁] {₁} {₀} p q = q
Lemma[a≡₁→b≡₁→min𝟚ab≡₁] {₁} {₁} p q = refl

Lemma[a≤₂b→min𝟚ab≡a] : {a b : 𝟚} → a ≤₂ b → min𝟚 a b ≡ a
Lemma[a≤₂b→min𝟚ab≡a] {₀} {b} p = refl
Lemma[a≤₂b→min𝟚ab≡a] {₁} {b} p = p refl

Lemma[min𝟚ab≡₀] : {a b : 𝟚} → (a ≡ ₀) + (b ≡ ₀) → min𝟚 a b ≡ ₀
Lemma[min𝟚ab≡₀] {₀} {b} (inl p) = refl
Lemma[min𝟚ab≡₀] {₀} {₀} (inr q) = refl
Lemma[min𝟚ab≡₀] {₁} {₀} (inr q) = refl

lemma[min𝟚ab≡₀] : {a b : 𝟚} → min𝟚 a b ≡ ₀ → (a ≡ ₀) + (b ≡ ₀)
lemma[min𝟚ab≡₀] {₀} {b} p = inl p
lemma[min𝟚ab≡₀] {₁} {b} p = inr p

max𝟚 : 𝟚 → 𝟚 → 𝟚
max𝟚 ₀ b = b
max𝟚 ₁ b = ₁

max𝟚-lemma : (a b : 𝟚) → max𝟚 a b ≡ ₁ → (a ≡ ₁) + (b ≡ ₁)
max𝟚-lemma ₀ b r = inr r
max𝟚-lemma ₁ b r = inl refl

max𝟚-lemma-converse : (a b : 𝟚) → (a ≡ ₁) + (b ≡ ₁) → max𝟚 a b ≡ ₁
max𝟚-lemma-converse ₀ b (inl r) = unique-from-𝟘 (zero-is-not-one r)
max𝟚-lemma-converse ₀ b (inr r) = r
max𝟚-lemma-converse ₁ b x = refl

\end{code}

Addition modulo 2:

\begin{code}

_⊕_ : 𝟚 → 𝟚 → 𝟚
₀ ⊕ x = x
₁ ⊕ x = complement x

complement-of-eq𝟚-is-⊕ : (m n : 𝟚) → complement (eq𝟚 m n) ≡ m ⊕ n
complement-of-eq𝟚-is-⊕ ₀ n = complement-involutive n
complement-of-eq𝟚-is-⊕ ₁ n = refl

Lemma[b⊕b≡₀] : {b : 𝟚} → b ⊕ b ≡ ₀
Lemma[b⊕b≡₀] {₀} = refl
Lemma[b⊕b≡₀] {₁} = refl

Lemma[b≡c→b⊕c≡₀] : {b c : 𝟚} → b ≡ c → b ⊕ c ≡ ₀
Lemma[b≡c→b⊕c≡₀] {b} {c} r = ap (λ - → b ⊕ -) (r ⁻¹) ∙ (Lemma[b⊕b≡₀] {b})

Lemma[b⊕c≡₀→b≡c] : {b c : 𝟚} → b ⊕ c ≡ ₀ → b ≡ c
Lemma[b⊕c≡₀→b≡c] {₀} {₀} r = refl
Lemma[b⊕c≡₀→b≡c] {₀} {₁} r = r ⁻¹
Lemma[b⊕c≡₀→b≡c] {₁} {₀} r = r
Lemma[b⊕c≡₀→b≡c] {₁} {₁} r = refl

Lemma[b≢c→b⊕c≡₁] : {b c : 𝟚} → b ≢ c → b ⊕ c ≡ ₁
Lemma[b≢c→b⊕c≡₁] = different-from-₀-equal-₁ ∘ (contrapositive Lemma[b⊕c≡₀→b≡c])

Lemma[b⊕c≡₁→b≢c] : {b c : 𝟚} → b ⊕ c ≡ ₁ → b ≢ c
Lemma[b⊕c≡₁→b≢c] = (contrapositive Lemma[b≡c→b⊕c≡₀]) ∘ equal-₁-different-from-₀

\end{code}

Order and complements:

\begin{code}

complement-left : {b c : 𝟚} → complement b ≤₂ c → complement c ≤₂ b
complement-left {₀} {₀} f p = f p
complement-left {₀} {₁} f p = p
complement-left {₁} {c} f p = refl

complement-right : {b c : 𝟚} → b ≤₂ complement c → c ≤₂ complement b
complement-right {₀} {c} f p = refl
complement-right {₁} {₀} f p = p
complement-right {₁} {₁} f p = f p

complement-both-left : {b c : 𝟚} → complement b ≤₂ complement c → c ≤₂ b
complement-both-left {₀} {₀} f p = p
complement-both-left {₀} {₁} f p = f p
complement-both-left {₁} {c} f p = refl

complement-both-right : {b c : 𝟚} → b ≤₂ c → complement c ≤₂ complement b
complement-both-right {₀} {c} f p = refl
complement-both-right {₁} {₀} f p = f p
complement-both-right {₁} {₁} f p = p

\end{code}

Fixities and precedences:

\begin{code}

infixr 31 _⊕_

\end{code}
