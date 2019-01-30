Martin Escardo, 24th January 2019.

Voedvodsky (Types'2011) considered resizing rules for a type theory
for univalent foundations. These rules govern the syntax of the formal
system, and hence are of a meta-mathematical nature.

Here we instead formulate, in our type theory without such rules, a
mathematical resizing principle. This principle is provable in the
system with Voevodsky's rules. But we don't postulate this principle
as an axiom. Instead, we use it an assumption, when needed, or as a
conclusion, when it follows from stronger principles, such as excluded
middle.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Resizing where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-FunExt
open import UF-EquivalenceExamples
open import UF-ExcludedMiddle

record propositional-resizing (𝓤 𝓥 : Universe) : (𝓤 ⊔ 𝓥)⁺ ̇ where
 field
  resize         : (P : 𝓤 ̇) (i : is-prop P) → 𝓥 ̇
  resize-is-prop : (P : 𝓤 ̇) (i : is-prop P) → is-prop (resize P i)
  to-resize      : (P : 𝓤 ̇) (i : is-prop P) → P → resize P i
  from-resize    : (P : 𝓤 ̇) (i : is-prop P) → resize P i → P

open propositional-resizing public

Propositional-resizing : 𝓤ω
Propositional-resizing = {𝓤 𝓥 : Universe} → propositional-resizing 𝓤 𝓥

\end{code}

This says that any proposition P in the universe 𝓤 ̇ is logically
equivalent to a (resized) proposition in the universe 𝓥.

It is consistent, because it is implied by excluded middle, which is
consistent:

\begin{code}

EM-gives-WPR : EM 𝓤 → propositional-resizing 𝓤 𝓥
EM-gives-WPR {𝓤} {𝓥} em = record {
   resize         = λ P i → Q P i (em P i)
 ; resize-is-prop = λ P i → j P i (em P i)
 ; to-resize      = λ P i → f P i (em P i)
 ; from-resize    = λ P i → g P i (em P i)
 }
 where
  module _ (P : 𝓤 ̇) (i : is-prop P) where
   Q : decidable P → 𝓥 ̇
   Q (inl p) = 𝟙
   Q (inr n) = 𝟘
   j : (d : decidable P) → is-prop (Q d)
   j (inl p) = 𝟙-is-prop
   j (inr n) = 𝟘-is-prop
   f : (d : decidable P) → P → Q d
   f (inl p) p' = *
   f (inr n) p  = 𝟘-elim (n p)
   g : (d : decidable P) → Q d → P
   g (inl p) q = p
   g (inr n) q = 𝟘-elim q

\end{code}

We say that a type X has size 𝓥 if it is equivalent to a type in the
universe 𝓥:

\begin{code}

_has-size_ : 𝓤 ̇ → (𝓥 : Universe) → 𝓥 ⁺  ⊔ 𝓤 ̇
X has-size 𝓥 = Σ \(Y : 𝓥 ̇) → Y ≃ X
\end{code}

TODO. The type "X has-size 𝓥" should be a proposition assuming
univalence (it is contractible if 𝓥 is 𝓤 and 𝓤 is univalent).

\begin{code}

size-upper-closed : (X : 𝓤 ̇) → X has-size (𝓤 ⊔ 𝓥)
size-upper-closed {𝓤} {𝓥} X = (X × 𝟙 {𝓥}) , 𝟙-rneutral

resize-prop : (𝓤 𝓥 : Universe) → propositional-resizing 𝓤 𝓥
            → (P : 𝓤 ̇) → is-prop P → P has-size 𝓥
resize-prop 𝓤 𝓥 ρ P i = resize ρ P i ,
                         qinveq (from-resize ρ P i)
                                (to-resize ρ P i ,
                                 (λ r → resize-is-prop ρ P i _ r) ,
                                 (λ p → i _ p))

\end{code}

Impredicativity. We begin with this strong notion, which says that the
type Ω 𝓤 of truth values in the universe 𝓤 has a copy in any successor
universe (i.e. in all universes except the first).

\begin{code}

is-impredicative+ : (𝓤 : Universe) → 𝓤ω
is-impredicative+ 𝓤 = (𝓥 : Universe) → (Ω 𝓤) has-size (𝓥 ⁺)

universes-are-impredicative+ : Propositional-resizing → PropExt → FunExt
                             → is-impredicative+ 𝓤
universes-are-impredicative+ {𝓤} ρ pe fe 𝓥 = Ω 𝓥 , qinveq φ (γ , γφ , φγ)
 where
  φ : Ω 𝓥 → Ω 𝓤
  φ (Q , j) = resize ρ Q j , resize-is-prop ρ Q j
  γ : Ω 𝓤 → Ω 𝓥
  γ (P , i) = resize ρ P i , resize-is-prop ρ P i
  φγ : (p : Ω 𝓤) → φ (γ p) ≡ p
  φγ (P , i) = Ω-ext (fe 𝓤 𝓤) (pe 𝓤)
               (from-resize ρ P i ∘ from-resize ρ (resize ρ P i) (resize-is-prop ρ P i))
               (to-resize ρ (resize ρ P i) (resize-is-prop ρ P i) ∘ to-resize ρ P i)
  γφ : (q : Ω 𝓥) → γ (φ q) ≡ q
  γφ (Q , j) = Ω-ext (fe 𝓥 𝓥) (pe 𝓥)
               (from-resize ρ Q j ∘ from-resize ρ (resize ρ Q j) (resize-is-prop ρ Q j))
               (to-resize ρ (resize ρ Q j) (resize-is-prop ρ Q j) ∘ to-resize ρ Q j)

\end{code}

A more standard notion of impredicativity is that the type Ω 𝓤 of
truth-values in the universe 𝓤 itself lives in 𝓤.

\begin{code}

is-impredicative : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-impredicative 𝓤 = (Ω 𝓤) has-size 𝓤

\end{code}

Propositional resizing doesn't imply that the first universe 𝓤₀ is
impredicative, but it does imply that all other, successor, universes
𝓤 ⁺ are.

\begin{code}

successor-universes-are-impredicative : Propositional-resizing → PropExt → FunExt
                                      → is-impredicative (𝓤 ⁺)
successor-universes-are-impredicative {𝓤} ρ pe fe = universes-are-impredicative+ ρ pe fe 𝓤

\end{code}

But excluded middle does give the impredicativity of the first
universe, and of all other universes, of course:

\begin{code}

is-globally-impredicative : (𝓤 : Universe) → 𝓤ω
is-globally-impredicative 𝓤 = (𝓥 : Universe) → (Ω 𝓤) has-size 𝓥

universes-impredicative-from-EM : LEM 𝓤 → propext 𝓤 → funext 𝓤 𝓤
                                → is-globally-impredicative 𝓤
universes-impredicative-from-EM {𝓤} em pe fe 𝓥 =
 (𝟙 {𝓥} + 𝟙 {𝓥}) ,
 qinveq φ
 ((λ p → γ p (em p)) ,
  (λ z → γφ z (em (φ z))) ,
  (λ p → φγ p (em p)))
 where
  φ : 𝟙 + 𝟙 → Ω 𝓤
  φ (inl x) = ⊥
  φ (inr y) = ⊤
  γ : (p : Ω 𝓤) → decidable (p holds) → 𝟙 + 𝟙
  γ p (inl h) = inr *
  γ p (inr n) = inl *
  γφ : (z : 𝟙 + 𝟙) (d : decidable ((φ z) holds)) → γ (φ z) d ≡ z
  γφ (inl x) (inl h) = 𝟘-elim h
  γφ (inl x) (inr n) = ap inl (𝟙-is-prop * x)
  γφ (inr y) (inl h) = ap inr (𝟙-is-prop * y)
  γφ (inr y) (inr n) = 𝟘-elim (n *)
  φγ : (p : Ω 𝓤) (d : decidable (p holds)) → φ (γ p d) ≡ p
  φγ p (inl h) = (true-is-equal-⊤  pe fe (p holds) (holds-is-prop p) h)⁻¹
  φγ p (inr n) = (false-is-equal-⊥ pe fe (p holds) (holds-is-prop p) n)⁻¹

is-impredicative₀ : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-impredicative₀ 𝓤 = (Ω 𝓤) has-size 𝓤₀

universes-impredicative-from-EM₀ : LEM 𝓤 → propext 𝓤 → funext 𝓤 𝓤
                                 → is-impredicative₀ 𝓤
universes-impredicative-from-EM₀ {𝓤} em pe fe = universes-impredicative-from-EM em pe fe 𝓤₀

\end{code}

What we get with propositional resizing is that all types of
propositions of any universe 𝓤 are equivalent to Ω 𝓤₀, which lives in
the second universe 𝓤₁:

\begin{code}

is-impredicative₁ : (𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓤₂ ̇
is-impredicative₁ 𝓤 = (Ω 𝓤) has-size 𝓤₁

all-universes-are-impredicative₁ : Propositional-resizing → PropExt → FunExt
                                 → is-impredicative₁ 𝓤
all-universes-are-impredicative₁ {𝓤} ρ pe fe = universes-are-impredicative+ ρ pe fe 𝓤₀

All-universes-are-impredicative₁ : Propositional-resizing → PropExt → FunExt
                                 → Ω 𝓤 ≃ Ω 𝓤₀
All-universes-are-impredicative₁ {𝓤} ρ pe fe = ≃-sym (pr₂ (all-universes-are-impredicative₁ {𝓤} ρ pe fe))

Ω-𝓤₀-lives-in-𝓤₁ : universe-of (Ω 𝓤₀) ≡ 𝓤₁
Ω-𝓤₀-lives-in-𝓤₁ = refl

\end{code}
