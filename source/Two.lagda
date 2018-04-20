Martin Escardo 2011.

This module defines the set 𝟚 of binary numbers with elements ₀
and ₁, and a number of operations and relations on them.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Two where

open import SpartanMLTT

data 𝟚 : U₀ ̇ where
 ₀ : 𝟚
 ₁ : 𝟚

zero-is-not-one : ₀ ≢ ₁
zero-is-not-one ()

𝟚-induction : ∀ {U} {A : 𝟚 → U ̇} → A ₀ → A ₁ → (x : 𝟚) → A x
𝟚-induction r s ₀ = r
𝟚-induction r s ₁ = s


𝟚-cases : ∀ {U} {A : U ̇} → A → A → 𝟚 → A
𝟚-cases = 𝟚-induction


two-equality-cases : ∀ {U} {A : U ̇} {b : 𝟚} → (b ≡ ₀ → A) → (b ≡ ₁ → A) → A
two-equality-cases {U} {A} {₀} f₀ f₁ = f₀ refl
two-equality-cases {U} {A} {₁} f₀ f₁ = f₁ refl

two-equality-cases' : ∀ {U} {A₀ A₁ : U ̇} {b : 𝟚} → (b ≡ ₀ → A₀) → (b ≡ ₁ → A₁) → A₀ + A₁
two-equality-cases' {U} {A₀} {A₁} {₀} f₀ f₁ = inl(f₀ refl)
two-equality-cases' {U} {A₀} {A₁} {₁} f₀ f₁ = inr(f₁ refl)


Lemma[b≡₁→b≢₀] : {b : 𝟚} → b ≡ ₁ → b ≢ ₀
Lemma[b≡₁→b≢₀] r s = zero-is-not-one (s ⁻¹ ∙ r)


Lemma[b≢₀→b≡₁] : {b : 𝟚} → b ≢ ₀ → b ≡ ₁
Lemma[b≢₀→b≡₁] f = two-equality-cases (𝟘-elim ∘ f) (λ r → r) 

Lemma[b≢₁→b≡₀] : {b : 𝟚} → b ≢ ₁ → b ≡ ₀
Lemma[b≢₁→b≡₀] f = two-equality-cases (λ r → r) (𝟘-elim ∘ f)

Lemma[b≡₀→b≢₁] : {b : 𝟚} → b ≡ ₀ → b ≢ ₁
Lemma[b≡₀→b≢₁] r s = zero-is-not-one (r ⁻¹ ∙ s)


Lemma[[a≡₁→b≡₁]→b≡₀→a≡₀] : {a b : 𝟚} → (a ≡ ₁ → b ≡ ₁) → b ≡ ₀ → a ≡ ₀
Lemma[[a≡₁→b≡₁]→b≡₀→a≡₀] f = Lemma[b≢₁→b≡₀] ∘ (contrapositive f) ∘ Lemma[b≡₀→b≢₁]


Lemma[[a≡₀→b≡₀]→b≡₁→a≡₁] : {a b : 𝟚} → (a ≡ ₀ → b ≡ ₀) → b ≡ ₁ → a ≡ ₁
Lemma[[a≡₀→b≡₀]→b≡₁→a≡₁] f = Lemma[b≢₀→b≡₁] ∘ (contrapositive f) ∘ Lemma[b≡₁→b≢₀]

\end{code}

Definition (Natural order of binary numbers):

\begin{code}

_≤_ : (a b : 𝟚) → U₀ ̇
a ≤ b = a ≡ ₁ → b ≡ ₁

₁-top : {b : 𝟚} → b ≤ ₁
₁-top r = refl

₀-bottom : {b : 𝟚} → ₀ ≤ b
₀-bottom ()

_≤'_ : (a b : 𝟚) → U₀ ̇
a ≤' b = b ≡ ₀ → a ≡ ₀

≤-gives-≤' : {a b : 𝟚} → a ≤ b → a ≤' b
≤-gives-≤' {₀} {b} f p = refl
≤-gives-≤' {₁} {₀} f p = (f refl)⁻¹
≤-gives-≤' {₁} {₁} f p = p

≤'-gives-≤ : {a b : 𝟚} → a ≤' b → a ≤ b
≤'-gives-≤ {₀} {₀} f p = p
≤'-gives-≤ {₀} {₁} f p = refl
≤'-gives-≤ {₁} {₀} f p = (f refl)⁻¹
≤'-gives-≤ {₁} {₁} f p = p

≤-anti : {a b : 𝟚} → a ≤ b → b ≤ a → a ≡ b
≤-anti {₀} {₀} f g = refl
≤-anti {₀} {₁} f g = g refl
≤-anti {₁} {₀} f g = ≤-gives-≤' f refl
≤-anti {₁} {₁} f g = refl

₁-maximal : {b : 𝟚} → ₁ ≤ b → b ≡ ₁
₁-maximal = ≤-anti ₁-top

_≥_ : (a b : 𝟚) → U₀ ̇
a ≥ b = b ≤ a

min𝟚 : 𝟚 → 𝟚 → 𝟚
min𝟚 ₀ b = ₀
min𝟚 ₁ b = b

Lemma[minab≤a] : {a b : 𝟚} → min𝟚 a b ≤ a
Lemma[minab≤a] {₀} {b} r = 𝟘-elim(Lemma[b≡₁→b≢₀] r refl)
Lemma[minab≤a] {₁} {b} r = refl

Lemma[minab≤b] : {a b : 𝟚} → min𝟚 a b ≤ b
Lemma[minab≤b] {₀} {b} r = 𝟘-elim(Lemma[b≡₁→b≢₀] r refl)
Lemma[minab≤b] {₁} {b} r = r

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

Lemma[a≤b→min𝟚ab≡a] : {a b : 𝟚} → a ≤ b → min𝟚 a b ≡ a
Lemma[a≤b→min𝟚ab≡a] {₀} {b} p = refl
Lemma[a≤b→min𝟚ab≡a] {₁} {b} p = p refl

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

complement : 𝟚 → 𝟚
complement ₀ = ₁
complement ₁ = ₀

infixr 31 _⊕_

_⊕_ : 𝟚 → 𝟚 → 𝟚
₀ ⊕ x = x
₁ ⊕ x = complement x

Lemma[b⊕b≡₀] : {b : 𝟚} → b ⊕ b ≡ ₀
Lemma[b⊕b≡₀] {₀} = refl
Lemma[b⊕b≡₀] {₁} = refl

Lemma[b≡c→b⊕c≡₀] : {b c : 𝟚} → b ≡ c → b ⊕ c ≡ ₀
Lemma[b≡c→b⊕c≡₀] {b} {c} r = ap (λ d → b ⊕ d) (r ⁻¹) ∙ (Lemma[b⊕b≡₀] {b})

Lemma[b⊕c≡₀→b≡c] : {b c : 𝟚} → b ⊕ c ≡ ₀ → b ≡ c
Lemma[b⊕c≡₀→b≡c] {₀} {₀} r = refl
Lemma[b⊕c≡₀→b≡c] {₀} {₁} ()
Lemma[b⊕c≡₀→b≡c] {₁} {₀} () 
Lemma[b⊕c≡₀→b≡c] {₁} {₁} r = refl

Lemma[b≢c→b⊕c≡₁] : {b c : 𝟚} → b ≢ c → b ⊕ c ≡ ₁
Lemma[b≢c→b⊕c≡₁] = Lemma[b≢₀→b≡₁] ∘ (contrapositive Lemma[b⊕c≡₀→b≡c])

Lemma[b⊕c≡₁→b≢c] : {b c : 𝟚} → b ⊕ c ≡ ₁ → b ≢ c
Lemma[b⊕c≡₁→b≢c] = (contrapositive Lemma[b≡c→b⊕c≡₀]) ∘ Lemma[b≡₁→b≢₀]  

\end{code}

Order and complements:

\begin{code}

complement-left : {b c : 𝟚} → complement b ≤ c → complement c ≤ b
complement-left {₀} {₀} f p = f p
complement-left {₀} {₁} f p = p
complement-left {₁} {c} f p = refl

complement-right : {b c : 𝟚} → b ≤ complement c → c ≤ complement b
complement-right {₀} {c} f p = refl
complement-right {₁} {₀} f p = p
complement-right {₁} {₁} f p = f p

complement-both-left : {b c : 𝟚} → complement b ≤ complement c → c ≤ b
complement-both-left {₀} {₀} f p = p
complement-both-left {₀} {₁} f p = f p
complement-both-left {₁} {c} f p = refl

complement-both-right : {b c : 𝟚} → b ≤ c → complement c ≤ complement b
complement-both-right {₀} {c} f p = refl
complement-both-right {₁} {₀} f p = f p
complement-both-right {₁} {₁} f p = p

complement-involutive : (b : 𝟚) → complement(complement b) ≡ b
complement-involutive ₀ = refl
complement-involutive ₁ = refl


\end{code}
