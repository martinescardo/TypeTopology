Martin Escardo 29 April 2014.

Micro-Tychonoff Theorem.

A proposition-indexed product of pointed compact types is itself
compact. But the assumption that a proposition-indexed product of
compact types is compact gives weak excluded middle (negative
propositions are decidable).

The definition of compactness-pointedness (or exhaustive
searchability) is

 compact∙ X = (p : X → 𝟚) → Σ x₀ ꞉ X , p x₀ ＝ ₁ → (x : X) → p x ＝ ₁

We refer to such an x₀ as a universal witness.

With excluded middle for propositions, the above claim is not
surprising, because

    (𝟘 → Y) = Y^𝟘 ≃ 𝟙 (which is always compact),
    (𝟙 → Y) = Y^𝟙 ≃ Y (which is compact if Y is),

and excluded middle for a proposition X amounts to X = 𝟘 or X = 𝟙, so
that

    Y^X is compact∙ if Y is compact∙ and X is a proposition.

The point is that

    (1) We can reach this conclusion without excluded middle.

    (2) This also holds for dependent products:

        The type Π x : X , Y x is compact∙ if X is a proposition and
        the type Y x is compact∙ for every x : X.

        (This product is also written (x : X) → Y x or Π Y.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module TypeTopology.MicroTychonoff where

open import MLTT.Two-Properties
open import TypeTopology.CompactTypes
open import UF.Equiv
open import UF.FunExt
open import UF.PropIndexedPiSigma
open import UF.Subsingletons

micro-tychonoff : funext 𝓤 𝓥
                → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                → is-prop X
                → ((x : X) → is-compact∙ (Y x))
                → is-compact∙ (Π Y)
micro-tychonoff {𝓤} {𝓥} fe {X} {Y} X-is-prop ε p = γ
 where
  _ : (x : X) → is-compact∙ (Y x)
  _ = ε

  _ : Π Y → 𝟚
  _ = p

  𝕗 : (x : X) → Π Y ≃ Y x
  𝕗 x = prop-indexed-product x fe X-is-prop

\end{code}

The essence of the first part of the proof is this:

\begin{code}

  crude : X → is-compact∙ (Π Y)
  crude x = compact∙-types-are-closed-under-equiv (≃-sym (𝕗 x)) (ε x)

\end{code}

But this is very crude for our purposes (or so it seems).  So we
instead proceed as follows. We first introduct some abbreviations.

\begin{code}

  f : (x : X) → Π Y → Y x
  f x = ⌜ 𝕗 x ⌝

  _ : (x : X) (φ : Π Y) → f x φ ＝ φ x
  _ = λ x φ → refl

  f⁻¹ : (x : X) → Y x → Π Y
  f⁻¹ x = ⌜ 𝕗 x ⌝⁻¹

\end{code}

We define a predicate q x : Y x → 𝟚, for each x : X, from the
predicate p : Π Y → 𝟚 via the above equivalence:

\begin{code}

  q : (x : X) → Y x → 𝟚
  q x y = p (f⁻¹ x y)

\end{code}

We argue that the following is a universal witness for the
searchability of the type Π Y w.r.t. the predicate p:

\begin{code}

  φ₀ : Π Y
  φ₀ x = universal-witness (ε x) (q x)

\end{code}

By hypothesis, it satisfies:

\begin{code}

  φ₀-universality : (x : X) → q x (φ₀ x) ＝ ₁ → (y : Y x) → q x y ＝ ₁
  φ₀-universality x = witness-universality (ε x) (q x)

\end{code}

By expanding the definitions, this amounts to:

\begin{code}

  φ₀-universality₀ : (x : X) → p (f⁻¹ x (φ₀ x)) ＝ ₁ → (y : Y x) → p (f⁻¹ x y) ＝ ₁
  φ₀-universality₀ = φ₀-universality

\end{code}

Because f x φ = φ x, the above amounts to the following:

\begin{code}

  φ₀-universality₁ : (x : X) → p (f⁻¹ x (f x φ₀)) ＝ ₁ → (y : Y x) → p (f⁻¹ x y) ＝ ₁
  φ₀-universality₁ = φ₀-universality₀

\end{code}

In particular, choosing y = f x φ, we get:

\begin{code}

  φ₀-universality₁-particular-case : (x : X)
                                   → p (f⁻¹ x (f x φ₀)) ＝ ₁
                                   → (φ : Π Y) → p (f⁻¹ x (f x φ)) ＝ ₁
  φ₀-universality₁-particular-case x r φ = φ₀-universality₁ x r (f x φ)

\end{code}

This in turn gives

\begin{code}

  φ₀-is-universal-witness-assuming-X
   : X → p φ₀ ＝ ₁ → (φ : Π Y) → p φ ＝ ₁
  φ₀-is-universal-witness-assuming-X x r φ =
   p φ               ＝⟨ ap p ((inverses-are-retractions' (𝕗 x) φ)⁻¹) ⟩
   p (f⁻¹ x (f x φ)) ＝⟨ φ₀-universality₁-particular-case x s φ ⟩
   ₁                 ∎
   where
    s = p (f⁻¹ x (f x φ₀)) ＝⟨ ap p (inverses-are-retractions' (𝕗 x) φ₀) ⟩
        p φ₀               ＝⟨ r ⟩
        ₁                  ∎

\end{code}

Notice that the point x : X vanishes from the conclusion, and so we
are able to omit it from the hypothesis, which is crucial for what
follows.

We get the same conclusion if X is empty:

\begin{code}

  φ₀-is-universal-witness-assuming-X-empty
   : is-empty X → p φ₀ ＝ ₁ → (φ : Π Y) → p φ ＝ ₁
  φ₀-is-universal-witness-assuming-X-empty u r φ =
   p φ  ＝⟨ ap p (dfunext fe (λ x → unique-from-𝟘 (u x))) ⟩
   p φ₀ ＝⟨ r ⟩
   ₁    ∎

\end{code}

So we would get what we want if we had excluded middle, because X is a
proposition and the above shows that both X and is-empty X := X → 𝟘
give the desired conclusion that φ₀ is a universal witness. But
excluded middle is not needed.

We shuffle the arguments of φ₀-is-universal-witness-assuming-X:

\begin{code}

  claim₀ : p φ₀ ＝ ₁ → (φ : Π Y) → X → p φ ＝ ₁
  claim₀ r φ x = φ₀-is-universal-witness-assuming-X x r φ

\end{code}

We then take the contrapositive of the conclusion X → p φ ＝ ₁, and
use the fact that if a point of the two-point type 𝟚 is ₀, then it is
not ₁:

\begin{code}

  Claim₁ : p φ₀ ＝ ₁ → (φ : Π Y) → p φ ＝ ₀ → (X → 𝟘)
  Claim₁ r φ = contrapositive (claim₀ r φ) ∘ equal-₀-different-from-₁

\end{code}

This concludes the first part of the argument.

We now shuffle the arguments of φ₀-is-universal-witness-assuming-X-empty:

\begin{code}

  Claim₂ : p φ₀ ＝ ₁ → (φ : Π Y) → (X → 𝟘) → p φ ＝ ₁
  Claim₂ r φ u = φ₀-is-universal-witness-assuming-X-empty u r φ

\end{code}

Combining the two last claims, we get:

\begin{code}

  Claim₃ : p φ₀ ＝ ₁ → (φ : Π Y) → p φ ＝ ₀ → p φ ＝ ₁
  Claim₃ r φ = Claim₂ r φ ∘ Claim₁ r φ

\end{code}

Finally, we do case analysis on the value of p φ to get the desired
conclusion:

\begin{code}

  φ₀-is-universal-witness : p φ₀ ＝ ₁ → (φ : Π Y) → p φ ＝ ₁
  φ₀-is-universal-witness r φ = 𝟚-equality-cases (Claim₃ r φ) id

\end{code}

And we are done:

\begin{code}

  γ : Σ φ₀ ꞉ Π Y , (p φ₀ ＝ ₁ → (φ : Π Y) → p φ ＝ ₁)
  γ = φ₀ , φ₀-is-universal-witness

\end{code}


TODO. 9 Sep 2015. We can generalize from X being a subsingleton (or
proposition) to X being subfinite (embedded into a finite type).

A particular case is the following:

\begin{code}

micro-tychonoff-corollary : funext 𝓤 𝓥
                          → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                          → is-prop X
                          → is-compact∙ Y
                          → is-compact∙ (X → Y)
micro-tychonoff-corollary fe X-is-prop ε = micro-tychonoff fe X-is-prop (λ x → ε)

\end{code}

This holds even for undecided X (such as X = LPO), or when we have no
idea whether X or (X → 𝟘) hold, and hence whether (X → Y) is 𝟙 or Y
(or none, if this is undecided)!

Better (9 Sep 2015):

\begin{code}

micro-tychonoff-corollary' : funext 𝓤 𝓥
                           → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                           → is-prop X
                           → (X → is-compact∙ Y)
                           → is-compact∙ (X → Y)
micro-tychonoff-corollary' fe = micro-tychonoff fe

\end{code}

So the function type (LPO → ℕ) is compact! (See the module LPO for a
proof.)

The Tychonoff theorem for prop-indexed products of compact types
doesn't hold. To see this, first notice that a proposition is compact
iff it is decidable. Now, the empty type 𝟘 is compact (but not
compact‌∙), and if 𝟘^P, that is, ¬ P, where compact for a proposition
P, this would imply that ¬ P is decidable for every proposition P,
which is weak excluded middle, which is not provable and doesn't hold
in all models.

\begin{code}

open import UF.ClassicalLogic

compact-micro-tychonoff-gives-WEM : ((X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
                                         → is-prop X
                                         → ((x : X) → is-compact (Y x))
                                         → is-compact (Π Y))
                                  → WEM 𝓤
compact-micro-tychonoff-gives-WEM {𝓤} {𝓥} τ X X-is-prop = δ γ
 where
  Y : X → 𝓥 ̇
  Y x = 𝟘

  negation-compact : is-compact (X → 𝟘 {𝓥})
  negation-compact = τ X Y X-is-prop (λ p → 𝟘-compact)

  γ : is-decidable (X → 𝟘 {𝓥})
  γ = compact-types-are-decidable (X → 𝟘) negation-compact

  δ : is-decidable (X → 𝟘 {𝓥}) → is-decidable (¬ X)
  δ (inl f) = inl (𝟘-elim ∘ f)
  δ (inr ϕ) = inr (contrapositive (λ f → 𝟘-elim ∘ f) ϕ)

\end{code}
