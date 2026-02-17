Martin Escardo, 23rd August 2023.

Some counterexamples to injectivity.

We already know that if excluded middle holds then all pointed types
are algebraically injective, and that the converse also holds.

So we can't really give an example of any type which is not
algebraically injective, other than the empty type. The best we can
hope for is to derive a constructive taboo, rather than a
contradiction, from the assumption that a type of interest would be
injective.

Most types one encounters in practice are "not" injective in the above
sense. We can also say "not all types are injective in general", as
there are some ∞-toposes which do satisfy excluded middle, as well as
some ∞-toposes which don't, and we intend TypeTopology to apply to all
∞-toposes, except when special assumptions are made.

NB. We work with the assumption of algebraic injectivity, rather than
its truncated version (injectivity), but this doesn't matter because
most of our conclusions are propositions, and when they are not we can
consider their truncations, which are also constructive taboos.

More counter-examples are in the module InjectiveTypes.Resizing and in
the module InjectiveTypes.InhabitedTypesTaboo.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc

module InjectiveTypes.CounterExamples
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import MLTT.Spartan
open import UF.Equiv
open import UF.Embeddings
open import UF.ClassicalLogic
open import UF.FunExt
open import UF.Retracts
open import UF.Size
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

 pe' : Prop-Ext
 pe' {𝓤} = pe 𝓤

open import Taboos.Decomposability fe
open import InjectiveTypes.Blackboard fe
open import TypeTopology.SimpleTypes fe pt

\end{code}

The two-point type 𝟚 is not injective in general. It is algebraically
injective if and only if weak excluded middle holds.

\begin{code}

𝟚-ainjective-gives-WEM : ainjective-type 𝟚 𝓤 𝓥 → typal-WEM 𝓤
𝟚-ainjective-gives-WEM {𝓤} 𝟚-ainj = I
 where
  d : decomposition 𝟚
  d = id , (₀ , refl) , (₁ , refl)

  I : typal-WEM 𝓤
  I = decomposition-of-ainjective-type-gives-WEM pe' 𝟚 𝟚-ainj d

WEM-gives-𝟚-retract-of-Ω : typal-WEM 𝓤 → retract 𝟚 of Ω 𝓤
WEM-gives-𝟚-retract-of-Ω {𝓤} wem = II
 where
  h : (p : Ω 𝓤) → is-decidable (¬ (p holds)) → 𝟚
  h p (inl _) = ₀
  h p (inr _) = ₁

  Ω-to-𝟚 : Ω 𝓤 → 𝟚
  Ω-to-𝟚 p = h p (wem (p holds))

  I : (n : 𝟚) (d : is-decidable (¬ (𝟚-to-Ω n holds))) → h (𝟚-to-Ω n) d ＝ n
  I ₀ (inl ϕ) = refl
  I ₁ (inl ϕ) = 𝟘-elim (ϕ ⋆)
  I ₀ (inr ψ) = 𝟘-elim (ψ unique-from-𝟘)
  I ₁ (inr ψ) = refl

  d : (p : Ω 𝓤) → is-decidable (¬ (p holds))
  d p = wem (p holds)

  II : retract 𝟚 of (Ω 𝓤)
  II = (λ p → h p (d p)) ,
       𝟚-to-Ω ,
       (λ n → I n (d (𝟚-to-Ω n)))

WEM-gives-𝟚-ainjective : typal-WEM 𝓤 → ainjective-type 𝟚 𝓤 𝓤
WEM-gives-𝟚-ainjective {𝓤} wem =
 retract-of-ainjective 𝟚 (Ω 𝓤) (Ω-ainjective pe') (WEM-gives-𝟚-retract-of-Ω wem)

WEM-gives-𝟚-aflabby : typal-WEM 𝓤 → aflabby 𝟚 𝓤
WEM-gives-𝟚-aflabby wem = ainjective-types-are-aflabby 𝟚 (WEM-gives-𝟚-ainjective wem)

\end{code}

The simple types are not injective in general. These are the types
formed by starting with ℕ and closing under function types. We can
also add the type 𝟚 to the base case of the definition to get the same
conclusion.

\begin{code}

simple-type₂-injective-gives-WEM : (X : 𝓤₀ ̇ )
                                 → simple-type₂ X
                                 → ainjective-type X 𝓤 𝓤
                                 → typal-WEM 𝓤
simple-type₂-injective-gives-WEM X s X-ainj =
 𝟚-ainjective-gives-WEM
  (retract-of-ainjective 𝟚 X X-ainj
  (simple-types₂-disconnected s))

simple-type₂-injective-gives-WEM-examples
 : (ainjective-type ℕ                   𝓤 𝓤 → typal-WEM 𝓤)
 × (ainjective-type (ℕ → ℕ)             𝓤 𝓤 → typal-WEM 𝓤)
 × (ainjective-type (ℕ → 𝟚)             𝓤 𝓤 → typal-WEM 𝓤)
 × (ainjective-type ((ℕ → ℕ) → ℕ)       𝓤 𝓤 → typal-WEM 𝓤)
 × (ainjective-type ((ℕ → 𝟚) → ℕ)       𝓤 𝓤 → typal-WEM 𝓤)
 × (ainjective-type (((ℕ → ℕ) → ℕ) → ℕ) 𝓤 𝓤 → typal-WEM 𝓤)
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

open import DedekindReals.Type fe' pe' pt
open import DedekindReals.Order fe' pe' pt renaming (_♯_ to _♯ℝ_)
open import Notation.Order

ℝ-ainjective-gives-Heaviside-function : ainjective-type ℝ 𝓤₁ 𝓤₁
                                      → Σ H ꞉ (ℝ → ℝ) ,
                                            ((x : ℝ) → (x < 0ℝ → H x ＝ 0ℝ)
                                                     × (x ≥ 0ℝ → H x ＝ 1ℝ))
ℝ-ainjective-gives-Heaviside-function ℝ-ainj = H , γ
 where
  j : (Σ x ꞉ ℝ , x < 0ℝ) + (Σ x ꞉ ℝ , x ≥ 0ℝ) → ℝ
  j = cases pr₁ pr₁

  j-is-embedding : is-embedding j
  j-is-embedding = disjoint-cases-embedding pr₁ pr₁
                    (pr₁-is-embedding (λ x → <-is-prop x 0ℝ))
                    (pr₁-is-embedding (λ x → ≤-is-prop 0ℝ x))
                    d
   where
    d : disjoint-images pr₁ pr₁
    d (x , l) (x , b) refl = <ℝ-irreflexive x (ℝ<-≤-trans x 0ℝ x l b)

  h : (Σ x ꞉ ℝ , x < 0ℝ) + (Σ x ꞉ ℝ , x ≥ 0ℝ) → ℝ
  h = cases (λ _ → 0ℝ) (λ _ → 1ℝ)

  H : ℝ → ℝ
  H = pr₁ (ℝ-ainj j j-is-embedding h)

  H-extends-h-along-j : ∀ u → H (j u) ＝ h u
  H-extends-h-along-j = pr₂ (ℝ-ainj j j-is-embedding h)

  γ : (x : ℝ) → (x < 0ℝ → H x ＝ 0ℝ)
              × (x ≥ 0ℝ → H x ＝ 1ℝ)
  γ x = I , II
   where
    I : x < 0ℝ → H x ＝ 0ℝ
    I l = H-extends-h-along-j (inl (x , l))

    II : x ≥ 0ℝ → H x ＝ 1ℝ
    II b = H-extends-h-along-j (inr (x , b))

\end{code}

But we can do better than that and derive weak excluded middle from
the injectivity of ℝ.

\begin{code}

open import Rationals.Type
open import Rationals.Order

ℝ-ainjective-gives-WEM : ainjective-type ℝ 𝓤 𝓥 → typal-WEM 𝓤
ℝ-ainjective-gives-WEM {𝓤} ℝ-ainj = WEM-gives-typal-WEM fe' XI
 where
  module _ (P : 𝓤 ̇ ) (P-is-prop : is-prop P) where

   q : Ω 𝓤
   q = (P + ¬ P) , decidability-of-prop-is-prop fe' P-is-prop

   ℝ-aflabby : aflabby ℝ 𝓤
   ℝ-aflabby = ainjective-types-are-aflabby ℝ ℝ-ainj

   f : P + ¬ P → ℝ
   f = cases (λ _ → 0ℝ) (λ _ → 1ℝ)

   r : ℝ
   r = aflabby-extension ℝ-aflabby q f

   I : P → r ＝ 0ℝ
   I p = aflabby-extension-property ℝ-aflabby q f (inl p)

   II : ¬ P → r ＝ 1ℝ
   II ν = aflabby-extension-property ℝ-aflabby q f (inr ν)

   I-II : r ≠ 0ℝ → r ≠ 1ℝ → 𝟘
   I-II u v = contrapositive II v (contrapositive I u)

   I-II₀ : r ≠ 1ℝ → r ＝ 0ℝ
   I-II₀ v = ℝ-is-¬¬-separated r 0ℝ (λ u → I-II u v)

   I-II₁ : r ≠ 0ℝ → r ＝ 1ℝ
   I-II₁ u = ℝ-is-¬¬-separated r 1ℝ (I-II u)

   III : (1/4 < r) ∨ (r < 1/2)
   III = ℝ-locatedness r 1/4 1/2 1/4<1/2

   IV : 1/4 < r → r ＝ 1ℝ
   IV l = I-II₁ IV₀
    where
      IV₀ : r ≠ 0ℝ
      IV₀ e = ℚ<-irrefl 1/4 IV₂
       where
        IV₁ : 1/4 < 0ℝ
        IV₁ = transport (1/4 <_) e l
        IV₂ : 1/4 < 1/4
        IV₂ = ℚ<-trans 1/4 0ℚ 1/4 IV₁ 0<1/4

   V : r < 1/2 → r ＝ 0ℝ
   V l = I-II₀ V₀
    where
      V₀ : r ≠ 1ℝ
      V₀ e = ℚ<-irrefl 1/2 V₂
       where
        V₁ : 1ℝ < 1/2
        V₁ = transport (_< 1/2) e l
        V₂ : 1/2 < 1/2
        V₂ = ℚ<-trans 1/2 1ℚ 1/2 1/2<1 V₁

   VI : r ＝ 0ℝ → ¬¬ P
   VI e ν = apartness-gives-inequality 0ℝ 1ℝ
             ℝ-zero-apart-from-one
              (0ℝ ＝⟨ e ⁻¹ ⟩
               r  ＝⟨ II ν ⟩
               1ℝ ∎)

   VII : r ＝ 1ℝ → ¬ P
   VII e p = apartness-gives-inequality 0ℝ 1ℝ
              ℝ-zero-apart-from-one
              (0ℝ ＝⟨ (I p)⁻¹ ⟩
              r   ＝⟨ e ⟩
              1ℝ  ∎)

   VIII : r < 1/2 → ¬¬ P
   VIII l = VI (V l)

   IX :  1/4 ℚ<ℝ r → ¬ P
   IX l = VII (IV l)

   X : ¬ P ∨ ¬¬ P
   X = ∨-functor IX VIII III

   XI : ¬ P + ¬¬ P
   XI = exit-∥∥ (decidability-of-prop-is-prop fe' (negations-are-props fe')) X

\end{code}

TODO. Probably the converse holds.

The injectivity of ℕ∞, the conatural numbers, or generic convergent
sequence, gives WLPO. Like in the previous example, we first use
injectivity to define a non-continuous function.

\begin{code}

open import CoNaturals.Type
open import Taboos.BasicDiscontinuity (fe 𝓤₀ 𝓤₀)
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

The above again illustrates that we can use injectivity to define
discontinuous functions. But we can actually get a stronger
conclusion with a weaker assumption and a simpler proof.

\begin{code}

ℕ∞-injective-gives-WEM : ainjective-type ℕ∞ 𝓤 𝓥 → typal-WEM 𝓤
ℕ∞-injective-gives-WEM ℕ∞-ainj =
 𝟚-ainjective-gives-WEM (retract-of-ainjective 𝟚 ℕ∞ ℕ∞-ainj 𝟚-retract-of-ℕ∞)

\end{code}

Added 6 June 2024 by Tom de Jong during a meeting with Martín Escardó.

A type with a nontrivial apartness relation cannot be injective unless weak
excluded middle holds.

TODO. We could derive ℝ-ainjective-gives-WEM from the below. (Note the
      similarities in the two proofs.)

\begin{code}

open import Apartness.Definition
open import Apartness.Properties pt
open Apartness pt

ainjective-type-with-non-trivial-apartness-gives-WEM
 : {X : 𝓤 ̇ }
 → ainjective-type X 𝓣 𝓦
 → Nontrivial-Apartness X 𝓥
 → typal-WEM 𝓣
ainjective-type-with-non-trivial-apartness-gives-WEM
 {𝓤} {𝓣} {𝓦} {𝓥} {X} ainj ((_♯_ , α) , ((x₀ , x₁) , points-apart))
 = WEM-gives-typal-WEM fe' VII
  where
   module _ (P : 𝓣 ̇ ) (P-is-prop : is-prop P) where

    X-aflabby : aflabby X 𝓣
    X-aflabby = ainjective-types-are-aflabby _ ainj

    f : (P + ¬ P) → X
    f = cases (λ _ → x₀) (λ _ → x₁)

    q : Ω 𝓣
    q = (P + ¬ P) , decidability-of-prop-is-prop fe' P-is-prop

    x : X
    x = aflabby-extension X-aflabby q f

    I : P → x ＝ x₀
    I p = aflabby-extension-property X-aflabby q f (inl p)

    II : ¬ P → x ＝ x₁
    II ν = aflabby-extension-property X-aflabby q f (inr ν)

    III : x ≠ x₀ → ¬ P
    III = contrapositive I

    IV : x ≠ x₁ → ¬¬ P
    IV = contrapositive II

    V : x₀ ♯ x ∨ x₁ ♯ x
    V = apartness-is-cotransitive _♯_ α x₀ x₁ x points-apart

    VI : (x ≠ x₀) ∨ (x ≠ x₁)
    VI = ∨-functor ν ν V
     where
      ν : {x y : X} → x ♯ y → y ≠ x
      ν a refl = apartness-is-irreflexive _♯_ α _ a

    VII : ¬ P + ¬¬ P
    VII = ∨-elim (decidability-of-prop-is-prop fe' (negations-are-props fe'))
                 (inl ∘ III) (inr ∘ IV) VI

\end{code}

In particular, we have the following.

\begin{code}

non-trivial-apartness-on-universe-gives-WEM
 : is-univalent 𝓤
 → Nontrivial-Apartness (𝓤 ̇ ) 𝓥
 → typal-WEM 𝓤
non-trivial-apartness-on-universe-gives-WEM {𝓤} {𝓥} ua =
 ainjective-type-with-non-trivial-apartness-gives-WEM {𝓤 ⁺} {𝓤} {𝓤}
  (universes-are-ainjective ua)

non-trivial-apartness-on-universe-iff-WEM
 : is-univalent 𝓤
 → Nontrivial-Apartness (𝓤 ̇ ) 𝓤 ↔ typal-WEM 𝓤
non-trivial-apartness-on-universe-iff-WEM {𝓤} ua = f , g
 where
  f : Nontrivial-Apartness (𝓤 ̇ ) 𝓤 → typal-WEM 𝓤
  f = non-trivial-apartness-on-universe-gives-WEM ua

  g : typal-WEM 𝓤 → Nontrivial-Apartness (𝓤 ̇ ) 𝓤
  g = WEM-gives-that-type-with-two-distinct-points-has-nontrivial-apartness⁺
       fe'
       (universes-are-locally-small ua)
       universe-has-two-distinct-points

non-trivial-apartness-on-Ω-gives-WEM
 : propext 𝓤
 → Nontrivial-Apartness (Ω 𝓤) 𝓥
 → typal-WEM 𝓤
non-trivial-apartness-on-Ω-gives-WEM {𝓤} {𝓥} pe =
 ainjective-type-with-non-trivial-apartness-gives-WEM {𝓤 ⁺} {𝓤} {𝓤}
  (Ω-ainjective pe)

non-trivial-apartness-on-Ω-iff-WEM
 : propext 𝓤
 → funext 𝓤 𝓤
 → Nontrivial-Apartness (Ω 𝓤) 𝓤 ↔ typal-WEM 𝓤
non-trivial-apartness-on-Ω-iff-WEM {𝓤} pe fe = f , g
 where
  f : Nontrivial-Apartness (Ω 𝓤) 𝓤 → typal-WEM 𝓤
  f = non-trivial-apartness-on-Ω-gives-WEM pe

  g : typal-WEM 𝓤 → Nontrivial-Apartness (Ω 𝓤) 𝓤
  g = WEM-gives-that-type-with-two-distinct-points-has-nontrivial-apartness⁺
       fe'
       (Ω-is-locally-small pe fe)
       ((⊥ , ⊤) , ⊥-is-not-⊤)

\end{code}

Notice that ainjective-type-with-non-trivial-apartness-gives-WEM
subsumes all the previous examples: the type 𝟚, which is a simple
type, the simple types (because they are totally separated and hence
they have a (tight) apartness), the Dedekind reals (with their
standard apartness), ℕ∞ (again because it is totally
separated).

TODO. Maybe we can list a few more interesting examples?

\end{code}

Added 27 January 2025 by Tom de Jong. Revised 6 February 2025.

We generalize non-trivial-totally-separated-ainjective-type-gives-¬¬-WEM from
Taboos.Decomposability, where the notion of total separatedness is exploited
directly, to derive ¬¬ WEM from the assumption of a non-trivial injective type
with a tight apartness.

\begin{code}

non-trivial-ainjective-type-with-tight-apartness-gives-¬¬-WEM
 : (Σ X ꞉ 𝓤 ̇ , ((¬ is-prop X) × ainjective-type X 𝓥 𝓦 × Tight-Apartness X 𝓣))
 → ¬¬ typal-WEM 𝓥
non-trivial-ainjective-type-with-tight-apartness-gives-¬¬-WEM
 {𝓤} {𝓥} {𝓦} {𝓣}
 (X , X-not-prop , X-inj , (_♯_ , ♯-is-apartness , ♯-is-tight)) = III
  where
   I : (x y : X) → x ♯ y → typal-WEM 𝓥
   I x y a = ainjective-type-with-non-trivial-apartness-gives-WEM X-inj
              ((_♯_ , ♯-is-apartness) , (((x , y) , a)))

   II : ¬ typal-WEM 𝓥 → is-prop X
   II ν x y = ♯-is-tight x y (λ (a : x ♯ y) → 𝟘-elim (ν (I x y a)))

   III : ¬¬ typal-WEM 𝓥
   III ν = 𝟘-elim (X-not-prop (II ν))

open import TypeTopology.TotallySeparated

non-trivial-totally-separated-ainjective-type-gives-¬¬-WEM'
 : (Σ X ꞉ 𝓤 ̇ , ((¬ is-prop X) × is-totally-separated X × ainjective-type X 𝓥 𝓦))
 → ¬¬ typal-WEM 𝓥
non-trivial-totally-separated-ainjective-type-gives-¬¬-WEM'
 (X , X-not-prop , X-tot-sep , X-inj) =
  non-trivial-ainjective-type-with-tight-apartness-gives-¬¬-WEM
   (  X , X-not-prop , X-inj
    , _♯₂_ , ♯₂-is-apartness
    , totally-separated-gives-totally-separated₃ X-tot-sep)
    where
     open total-separatedness-via-apartness pt

\end{code}

Added 16 October 2025 by Tom de Jong, formalizing a proof sketches
of 4 and 8 September 2025.

The following theorem is instantiated below to show that the injectivity of the
infinite dimensional real projective space RP∞ implies a weak choice principle
known as the world's simplest axiom of choice.

\begin{code}

open import InjectiveTypes.Subtypes fe
open import UF.ExitPropTrunc
open split-support-and-collapsibility pt

family-has-unspecified-split-support-if-total-space-of-truncation-is-ainjective
 : (D : 𝓤 ̇ )
 → ainjective-type D 𝓥 𝓦
 → (T : D → 𝓣 ̇ )
 → ainjective-type (Σ d ꞉ D , ∥ T d ∥) (𝓣 ⊔ 𝓥') 𝓦'
 → (d : D) → ∥ has-split-support (T d) ∥
family-has-unspecified-split-support-if-total-space-of-truncation-is-ainjective
 D D-inj T E-inj d = I
  where
   E = Σ d ꞉ D , ∥ T d ∥
   lem : Σ f ꞉ (D → D) , ((x : D) → ∥ T (f x) ∥)
                       × ((x : D) → ∥ T x ∥ → f x ＝ x)
   lem = necessary-condition-for-injectivity-of-subtype
          D
          (λ x → ∥ T x ∥)
          (λ x → ∥∥-is-prop)
     E-inj
   f : D → D
   f = pr₁ lem
   f₁ : ∥ T (f d) ∥
   f₁ = pr₁ (pr₂ lem) d
   f₂ : ∥ T d ∥ → f d ＝ d
   f₂ = pr₂ (pr₂ lem) d
   I : ∥ (∥ T d ∥ → T d) ∥
   I = ∥∥-functor II f₁
    where
     II : T (f d) → ∥ T d ∥ → T d
     II t τ = transport T (f₂ τ) t

open import SyntheticHomotopyTheory.RP-infinity pt
open import UF.Choice
open world's-simplest-axiom-of-choice fe pt

ℝP∞-ainjective-implies-WSAC : ainjective-type ℝP∞ 𝓥 𝓦
                            → WSAC' 𝓤₀
ℝP∞-ainjective-implies-WSAC RP∞-inj =
 family-has-unspecified-split-support-if-total-space-of-truncation-is-ainjective
  (𝓤₀ ̇ ) (universes-are-ainjective (ua 𝓤₀)) (λ X → X ≃ 𝟚) RP∞-inj

\end{code}