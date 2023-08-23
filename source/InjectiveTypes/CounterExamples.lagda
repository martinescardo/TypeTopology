Martin Escardo, 23rd August 2023.

Some counterexamples to injectivity.

We already know that if excluded middle holds then all pointed types
are algebraicly injective, and that the converse also holds.

So we can't really give an example of any type which is not
algebraicly injective. The best we can hope is to derive a
constructive taboo, rather than a contradiction, from the assumption
that a type of interest would be injective.

Most types one encounters in practice are "not" injective in the above
sense.

NB. We work with the assumption of algebraic injectivity, rather than
its truncated version (injectivity), but this doesn't matter because
most of our conclusions are propositions, and when they are not we can
consider their truncations, which are also constructive taboos.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc

module InjectiveTypes.CounterExamples
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open import MLTT.Spartan
open import UF.Embeddings
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.Miscelanea
open import UF.Retracts
open import UF.Subsingletons
open import UF.UA-FunExt
open import Taboos.Decomposability ua

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

open import InjectiveTypes.Blackboard fe
open import TypeTopology.SimpleTypes fe pt

\end{code}

The two-point type 𝟚 is not injective in general. It is algebraically
injective if and only if weak excluded middle holds.

\begin{code}

𝟚-injective-gives-WEM : ainjective-type 𝟚 𝓤 𝓤 → WEM 𝓤
𝟚-injective-gives-WEM {𝓤} 𝟚-ainj = I
 where
  d : decomposition 𝟚
  d = id , (₀ , refl) , (₁ , refl)

  I : WEM 𝓤
  I = decomposition-of-ainjective-type-gives-WEM 𝟚 𝟚-ainj d

WEM-gives-𝟚-retract-of-Ω : WEM 𝓤 → retract 𝟚 of Ω 𝓤
WEM-gives-𝟚-retract-of-Ω {𝓤} wem = II
 where
  h : (p : Ω 𝓤) → is-decidable (¬ (p holds)) → 𝟚
  h p (inl _) = ₀
  h p (inr _) = ₁

  Ω-to-𝟚 : Ω 𝓤 → 𝟚
  Ω-to-𝟚 p = h p (wem (p holds) (holds-is-prop p))

  I : (n : 𝟚) (d : is-decidable (¬ (𝟚-to-Ω n holds))) → h (𝟚-to-Ω n) d ＝ n
  I ₀ (inl ϕ) = refl
  I ₁ (inl ϕ) = 𝟘-elim (ϕ ⋆)
  I ₀ (inr ψ) = 𝟘-elim (ψ unique-from-𝟘)
  I ₁ (inr ψ) = refl

  d : (p : Ω 𝓤) → is-decidable (¬ (p holds))
  d p = wem (p holds) (holds-is-prop p)

  II : retract 𝟚 of (Ω 𝓤)
  II = (λ p → h p (d p)) ,
       𝟚-to-Ω ,
       (λ n → I n (d (𝟚-to-Ω n)))

WEM-gives-𝟚-ainjective : WEM 𝓤 → ainjective-type 𝟚 𝓤 𝓤
WEM-gives-𝟚-ainjective {𝓤} wem =
 retract-of-ainjective 𝟚 (Ω 𝓤) (Ω-ainjective pe) (WEM-gives-𝟚-retract-of-Ω wem)

WEM-gives-𝟚-aflabby : WEM 𝓤 → aflabby 𝟚 𝓤
WEM-gives-𝟚-aflabby wem = ainjective-types-are-aflabby 𝟚 (WEM-gives-𝟚-ainjective wem)

\end{code}

The simple types are not injective in general. These are the types
formed by starting with ℕ and closing under function types. We can
also add type 𝟚 to the base case of the definition to get the same
conclusion.

\begin{code}

simple-type₂-injective-gives-WEM : (X : 𝓤₀ ̇) → simple-type₂ X → ainjective-type X 𝓤 𝓤 → WEM 𝓤
simple-type₂-injective-gives-WEM X s X-ainj =
 𝟚-injective-gives-WEM (retract-of-ainjective 𝟚 X X-ainj (simple-types₂-disconnected s))

simple-type₂-injective-gives-WEM-examples
 : (ainjective-type ℕ                   𝓤 𝓤 → WEM 𝓤)
 × (ainjective-type (ℕ → ℕ)             𝓤 𝓤 → WEM 𝓤)
 × (ainjective-type (ℕ → 𝟚)             𝓤 𝓤 → WEM 𝓤)
 × (ainjective-type ((ℕ → ℕ) → ℕ)       𝓤 𝓤 → WEM 𝓤)
 × (ainjective-type ((ℕ → 𝟚) → ℕ)       𝓤 𝓤 → WEM 𝓤)
 × (ainjective-type (((ℕ → ℕ) → ℕ) → ℕ) 𝓤 𝓤 → WEM 𝓤)
simple-type₂-injective-gives-WEM-examples =
 simple-type₂-injective-gives-WEM _ base ,
 simple-type₂-injective-gives-WEM _ (step base base) ,
 simple-type₂-injective-gives-WEM _ (step base base₂) ,
 simple-type₂-injective-gives-WEM _ (step (step base base) base) ,
 simple-type₂-injective-gives-WEM _ (step (step base base₂) base) ,
 simple-type₂-injective-gives-WEM _ (step (step (step base base) base) base)

\end{code}

TODO. We can also close under _×_ and _+_ to get the same result. We
can also close under Π, but maybe not under Σ.

If the type ℝ of Dedekind reals is injective then there are
discontinuous functions ℝ → ℝ, e.g. the Heaviside function, which is
also a constructive taboo. Notice that the type ℝ lives in the
universe 𝓤₁.

\begin{code}

open import DedekindReals.Type fe' pe pt renaming (0ℝ to 0ᴿ ; 1ℝ to 1ᴿ)
open import DedekindReals.Order fe' pe pt
open import Notation.Order

ℝ-ainjective-gives-Heaviside-function : ainjective-type ℝ 𝓤₁ 𝓤₁
                                      → Σ f ꞉ (ℝ → ℝ) ,
                                            ((x : ℝ) → (x < 0ᴿ → f x ＝ 0ᴿ)
                                                     × (x ≥ 0ᴿ → f x ＝ 1ᴿ))
ℝ-ainjective-gives-Heaviside-function ℝ-ainj = f , γ
 where
  j : (Σ x ꞉ ℝ , x < 0ᴿ) + (Σ x ꞉ ℝ , x ≥ 0ᴿ) → ℝ
  j = cases pr₁ pr₁

  j-is-embedding : is-embedding j
  j-is-embedding = disjoint-cases-embedding pr₁ pr₁
                    (pr₁-is-embedding (λ x → <-is-prop x 0ᴿ))
                    (pr₁-is-embedding (λ x → ≤-is-prop 0ᴿ x))
                    d
   where
    d : disjoint-images pr₁ pr₁
    d (x , l) (x , b) refl = <ℝ-irreflexive x (ℝ<-≤-trans x 0ᴿ x l b)

  g : (Σ x ꞉ ℝ , x < 0ᴿ) + (Σ x ꞉ ℝ , x ≥ 0ᴿ) → ℝ
  g = cases (λ _ → 0ᴿ) (λ _ → 1ᴿ)

  f : ℝ → ℝ
  f = pr₁ (ℝ-ainj j j-is-embedding g)

  f-extends-g-along-j : ∀ u → f (j u) ＝ g u
  f-extends-g-along-j = pr₂ (ℝ-ainj j j-is-embedding g)

  γ : (x : ℝ) → (x < 0ᴿ → f x ＝ 0ᴿ)
              × (x ≥ 0ᴿ → f x ＝ 1ᴿ)
  γ x = I , II
   where
    I : x < 0ᴿ → f x ＝ 0ᴿ
    I l = f-extends-g-along-j (inl (x , l))

    II : x ≥ 0ᴿ → f x ＝ 1ᴿ
    II b = f-extends-g-along-j (inr (x , b))

\end{code}

The injectivity of ℕ∞, the conatural numbers, or generic convergent
sequence, gives WLPO. Like in the previous example, we first use
injectivity to define a non-continuous function.

\begin{code}

open import CoNaturals.GenericConvergentSequence
open import Taboos.BasicDiscontinuity fe
open import Taboos.WLPO
open import Notation.CanonicalMap

ℕ∞-injective-gives-WLPO : ainjective-type ℕ∞ 𝓤₀ 𝓤₀ → WLPO
ℕ∞-injective-gives-WLPO ℕ∞-ainj = basic-discontinuity-taboo' f (f₀ , f₁)
 where
  g : ℕ + 𝟙 → ℕ∞
  g (inl _) = ι 0
  g (inr _) = ι 1

  f : ℕ∞ → ℕ∞
  f = pr₁ (ℕ∞-ainj ι𝟙 (ι𝟙-is-embedding fe') g)

  f-extends-g-along-ι𝟙 : ∀ u → f (ι𝟙 u) ＝ g u
  f-extends-g-along-ι𝟙 = pr₂ (ℕ∞-ainj ι𝟙 (ι𝟙-is-embedding fe') g)

  f₀ : (n : ℕ) → f (ι n) ＝ ι 0
  f₀ n = f-extends-g-along-ι𝟙 (inl n)

  f₁ : f ∞ ＝ ι 1
  f₁ = f-extends-g-along-ι𝟙 (inr ⋆)

\end{code}
