Martin Escardo 29 April 2014.

A proposition-indexed product of pointed compact sets is itself
compact. But the assumption that a proposition-indexed product of
compact sets is compact gives weak excluded middle (negative
propositions are decidable).

The definition of compactness (or exhaustive searchability) is

    compact∙ A = (p : A → 𝟚) → Σ a₀ ꞉ A , p a₀ ＝ ₁ → (a : A) → p a ＝ ₁

With excluded middle for propositions, the above claim is not
surprising, because

    (𝟘 → Y) = Y^𝟘 ≃ 𝟙 (which is always compact),
    (𝟙 → Y) = Y^𝟙 ≃ Y (which is compact if Y is),

and excluded middle for a proposition X amounts to X = 𝟘 or X = 𝟙, so
that

    Y^X is compact if Y is compact and X is a proposition.

The point is that

    (1) We can reach this conclusion without excluded middle.

    (2) This also holds for dependent products:

        Π x : X , Y x is compact if X is a proposition and Y x is
        compact for every x : X.

        (This product is also written (x : X) → Y x or Π Y in Agda.)

Our Agda proof below can be written rather concisely by expanding the
definitions. We deliberately don't do that, so that we have a rigorous
informal proof side-by-side with the formal proof. We proceed in a
series of trivial steps, hopefully in the most natural way (although
we had a convoluted path to this supposedly natural way).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.FunExt

module TypeTopology.PropTychonoff (fe : FunExt) where

open import MLTT.Two-Properties
open import TypeTopology.CompactTypes
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PropIndexedPiSigma
open import UF.Subsingletons

\end{code}

A crucial lemma is

    prop-indexed-product : is-prop X → (a : X) → Π Y ≅ Y a

This is proved in the module Prop-indexed-product. Although it has a
subtle proof, it should be intuitively clear, as X has at most one
element by hypothesis, and if the element is a:X then the product Π Y
should be isomorphic to its only factor Y a.

With this observation, the following proof should be self-contained,
if we recall again the definition of compact set from the module
CompacTypes:

    compact∙ A = (p : A → 𝟚) → Σ a₀ ꞉ A , p a₀ ＝ ₁ → (a : A) → p a ＝ ₁

Recall also that such an a₀ is called a universal witness for the predicate p.

\begin{code}

prop-tychonoff : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
               → is-prop X
               → ((x : X) → is-compact∙ (Y x))
               → is-compact∙ (Π Y)
prop-tychonoff {𝓤} {𝓥} {X} {Y} X-is-prop ε p = γ
 where
  have : (type-of ε ＝ ((x : X) → is-compact∙(Y x)))
       × (type-of p ＝ (Π Y → 𝟚))
  have = refl , refl

  hip : (x : X) → Π Y ≃ Y x
  hip = prop-indexed-product (fe 𝓤 𝓥) X-is-prop

\end{code}

The essence of the first part of the proof is this:

\begin{code}

  crude : X → is-compact∙ (Π Y)
  crude x = compact∙-types-are-closed-under-equiv(≃-sym(hip x)) (ε x)

\end{code}

But this is very crude for our purposes (or so it seems).  So we
instead proceed as follows.

The following is what we get from prop-indexed-product, abstractly:

\begin{code}

  f : (x : X) → Π Y → Y x
  f x = pr₁ (hip x)

  hrf : (x : X) → Σ r ꞉ (Y x → Π Y), r ∘ f x ∼ id
  hrf x = pr₂ (pr₂ (hip x))

  h : (x : X) → Y x → Π Y
  h x = pr₁ (hrf x)

  hf : (x : X) (φ : Π Y) → h x (f x φ) ＝ φ
  hf x = pr₂ (hrf x)

\end{code}

We define a predicate q x : Y x → 𝟚, for each x : X, from the
predicate p : Π Y → 𝟚 via (part of) the above equivalence:

\begin{code}

  q : (x : X) → Y x → 𝟚
  q x y = p (h x y)

\end{code}

We argue that the following is a universal witness for the
searchability of the type Π Y wrt the predicate p:

\begin{code}

  φ₀ : Π Y
  φ₀ x = pr₁ (ε x (q x))

\end{code}

By hypothesis, it satisfies:

\begin{code}

  φ₀-spec : (x : X) → q x (φ₀ x) ＝ ₁ → (y : Y x) → q x y ＝ ₁
  φ₀-spec x = pr₂ (ε x (q x))

\end{code}

By expanding the definitions, this amounts to:

\begin{code}

  φ₀-spec₀ : (x : X) → p (h x (φ₀ x)) ＝ ₁ → (y : Y x) → p (h x y) ＝ ₁
  φ₀-spec₀ = φ₀-spec

\end{code}

By the definition of f in prop-indexed-product (namely f x φ = φ x):

\begin{code}

  φ₀-spec₁ : (x : X) → p (h x (f x φ₀)) ＝ ₁ → (y : Y x) → p (h x y) ＝ ₁
  φ₀-spec₁ = φ₀-spec₀

\end{code}

(So we can't abstract away the construction of prop-indexed-product.)

In particular, with y = f x φ, we get:

\begin{code}

  φ₀-spec₁-particular-case : (x : X)
                           → p (h x (f x φ₀)) ＝ ₁
                           → (φ : Π Y) → p (h x (f x φ)) ＝ ₁
  φ₀-spec₁-particular-case x r φ = φ₀-spec₁ x r (f x φ)

\end{code}

Using the fact that g x (f x φ) = φ for any x:X, we get:

\begin{code}

  φ₀-is-universal-witness-assuming-X : X → p φ₀ ＝ ₁ → (φ : Π Y) → p φ ＝ ₁
  φ₀-is-universal-witness-assuming-X x r φ =
     p φ             ＝⟨ ap p ((hf x φ)⁻¹) ⟩
     p (h x (f x φ)) ＝⟨ φ₀-spec₁-particular-case x s φ ⟩
     ₁               ∎
   where
    s = p (h x (f x φ₀)) ＝⟨ ap p (hf x φ₀) ⟩
        p φ₀             ＝⟨ r ⟩
        ₁                ∎

\end{code}

Notice that the point x : X vanishes from the conclusion, and so we
are able to omit it from the hypothesis, which is crucial for what
follows.

We get the same conclusion if X is empty:

\begin{code}

  φ₀-is-universal-witness-assuming-X→𝟘 : (X → 𝟘) → p φ₀ ＝ ₁ → (φ : Π Y) → p φ ＝ ₁
  φ₀-is-universal-witness-assuming-X→𝟘 u r φ = p φ  ＝⟨ ap p claim ⟩
                                               p φ₀ ＝⟨ r ⟩
                                               ₁    ∎

   where
    claim : φ ＝ φ₀
    claim = dfunext (fe 𝓤 𝓥) (λ x → unique-from-𝟘 (u x))

\end{code}

So we would get what we want if we had excluded middle, because X is a
proposition and the above shows that both X and X → 𝟘 give the desired
conclusion that φ₀ is a universal witness. But excluded middle is not
needed.

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
  Claim₁ r φ = contrapositive(claim₀ r φ) ∘ equal-₀-different-from-₁

\end{code}

This concludes the first part of the argument.

We now shuffle the arguments of φ₀-is-universal-witness-assuming-X→𝟘:

\begin{code}

  Claim₂ : p φ₀ ＝ ₁ → (φ : Π Y) → (X → 𝟘) → p φ ＝ ₁
  Claim₂ r φ u = φ₀-is-universal-witness-assuming-X→𝟘 u r φ

\end{code}

Combining the two last claims, we get:

\begin{code}

  Claim₃ : p φ₀ ＝ ₁ → (φ : Π Y) → p φ ＝ ₀ → p φ ＝ ₁
  Claim₃ r φ = Claim₂ r φ ∘ Claim₁ r φ

\end{code}

Finally, we do case analysis on the value of p φ:

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

prop-tychonoff-corollary : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                         → is-prop X
                         → is-compact∙ Y
                         → is-compact∙ (X → Y)
prop-tychonoff-corollary X-is-prop ε = prop-tychonoff X-is-prop (λ x → ε)

\end{code}

This holds even for undecided X (such as X = LPO), or when we have no
idea whether X or (X → 𝟘), and hence whether (X → Y) is 𝟙 or Y (or
none, if this is undecided)!

Better (9 Sep 2015):

\begin{code}

prop-tychonoff-corollary' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                          → is-prop X
                          → (X → is-compact∙ Y)
                          → is-compact∙ (X → Y)
prop-tychonoff-corollary' = prop-tychonoff

\end{code}

So the function type (LPO → ℕ) is compact! (See the module LPO for a
proof.)

The Tychonoff theorem for prop-indexed products of compact types
doesn't hold. To see this, first notice that a proposition is
compact iff it is decidable. Now, the empty type 𝟘 is compact
(but not compact‌∙), and if 𝟘^P, that is, ¬P, where compact for a
proposition P, this would imply that ¬P is decidable for every
proposition P, which is weak excluded middle, which is not provable.

\begin{code}

open import UF.ExcludedMiddle

compact-prop-tychonoff-gives-WEM : ((X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
                                       → is-prop X
                                       → ((x : X) → is-compact (Y x))
                                       → is-compact (Π Y))
                                 → WEM 𝓤
compact-prop-tychonoff-gives-WEM {𝓤} {𝓥} τ X X-is-prop = δ γ
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
