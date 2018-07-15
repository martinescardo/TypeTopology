Martin Escardo 2011.

See my 2008 LMCS paper "Exhaustible sets in higher-type computation".
And also the work with Oliva on selection functions in proof theory.

Here we don't assume continuity axioms, but all functions are secretly
continuous, and searchable sets are secretly compact.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module SearchableTypes where

open import SpartanMLTT
open import UF-Subsingletons
open import UF-FunExt
open import UF-Retracts
open import UF-Equiv
open import UF-PropTrunc
open import UF-ImageAndSurjection

\end{code}

Because choice holds in MLTT, we can formulate searchability as
follows, rather than using selection functions (see searchable'
below).

The drinker paradox says that in every pub there is a person x
such that if x drinks then everybody drinks.

In the definition below, p x ≡ ₁ means that x drinks, and the people
in the pub are the members of the set X. In general the DP is
non-constructive, as for example for the pub with set of costumers ℕ,
this would amount to LPO (limited principle of omniscience).  But it
is constructive for the larger pub with set of costumers ℕ∞, as shown
in the module ConvergentSequenceSearchable. Of course, it trivially
holds for finite sets.

In this module we investigate some closure properties of searchable
sets, and its relation to the principle of omniscience.

\begin{code}

searchable : ∀ {U} → U ̇ → U ̇
searchable X = (p : X → 𝟚) → Σ \(x₀ : X) → p x₀ ≡ ₁ → (x : X) → p x ≡ ₁

\end{code}

Terminology: we call x₀ the universal witness.

For example, every finite set is searchable, and in particular the
set 𝟚 = { ₀ , ₁ } of binary numerals is searchable. To find x₀ : 𝟚
such that

   (†) p x₀ ≡ ₁ → ∀(x : X) → p x ≡ ₁,

we can check whether p ₀ ≡ ₁ and p ₁ ≡ ₁.

     If this is the case, then ∀(x : X) → p x ≡ ₁ holds, which is
     the conclusion the implication (†), and hence we can take any
     x₀ : 𝟚 to make (†) hold.

     Otherwise, we can take any x₀ such that p x₀ ≡ ₀ so that the
     implication (†) holds vacuously.

That is, either the conclusion ∀(x : X) → p x ≡ ₁ of (†) holds, or
its premise p x₀ ≡ ₁ fails for suitable x₀.

However, there is a more direct proof: we claim that, without
checking the two possibilities, we can always take x₀ = p ₀.
(Cf. Section 8.1 of the LMCS'2008 paper.)

\begin{code}

𝟚-searchable : searchable 𝟚
𝟚-searchable p = x₀ , (λ r → 𝟚-induction (lemma₀ r) (lemma₁ r))
 where
    x₀ : 𝟚
    x₀ = p ₀

    claim : p x₀ ≡ ₁ → p ₀ ≡ ₀ → p ₀ ≡ ₁
    claim r s = transport (λ - → p - ≡ ₁) s r

    lemma₀ : p x₀ ≡ ₁ → p ₀ ≡ ₁
    lemma₀ r = 𝟚-equality-cases (claim r) (λ s → s)

    lemma₁ : p x₀ ≡ ₁ → p ₁ ≡ ₁
    lemma₁ r = transport (λ - → p - ≡ ₁) (lemma₀ r) r

open import UF-SetExamples

\end{code}

Even though excluded middle is undecided, the set of (univalent)
propositions is searchable (assuming propositional extensionality,
which is a consequence of univalence):

\begin{code}

open import UF-Two-Prop-Density

Ω-searchable : funext U₀ U₀ → propext U₀ → searchable Ω
Ω-searchable fe pe p = 𝟚-equality-cases a b
  where
    A = Σ \(x₀ : Ω) → p x₀ ≡ ₁ → (x : Ω) → p x ≡ ₁

    a : p ⊥ ≡ ₀ → A
    a r = ⊥ , λ s → 𝟘-elim (zero-is-not-one (r ⁻¹ ∙ s))

    b : p ⊥ ≡ ₁ → A
    b r = 𝟚-equality-cases c d
      where
        c : p ⊤ ≡ ₀ → A
        c s = ⊤ , λ t → 𝟘-elim (zero-is-not-one (s ⁻¹ ∙ t))

        d : p ⊤ ≡ ₁ → A
        d s = ⊤ , ⊥-⊤-density fe pe p r

\end{code}

We could have used the same idea of proof as for 𝟚-searchable, again
using density.

\begin{code}

𝟙-searchable : ∀ {U} → searchable 𝟙
𝟙-searchable {U} p = * {U} , f
 where
  f : (r : p * ≡ ₁) (x : 𝟙) → p x ≡ ₁
  f r * = r

\end{code}

In this module we prove some closure properties of searchable
sets. Before doing this, we investigate their general nature.

We first show that the universal witness x₀ is a root of p if and
only if p has a root.

\begin{code}

_is-a-root-of_ : ∀ {U} {X : U ̇} → X → (X → 𝟚) → U₀ ̇
x is-a-root-of p = p x ≡ ₀

_has-a-root : ∀ {U} {X : U ̇} → (X → 𝟚) → U ̇
p has-a-root = Σ \x → x is-a-root-of p

putative-root : ∀ {U} {X : U ̇}
              → searchable X → (p : X → 𝟚) → Σ \(x₀ : X) → (p has-a-root) ⇔ (x₀ is-a-root-of p)
putative-root {U} {X} ε p = x₀ , (lemma₀ , lemma₁)
 where
  x₀ : X
  x₀ = pr₁(ε p)

  lemma : ¬((x : X) → p x ≡ ₁) → p x₀ ≡ ₀
  lemma = Lemma[b≢₁→b≡₀] ∘ contrapositive(pr₂(ε p))

  lemma₀ : p has-a-root → x₀ is-a-root-of p
  lemma₀ (x , r) = lemma claim
   where claim : ¬((x : X) → p x ≡ ₁)
         claim f = Lemma[b≡₁→b≢₀] (f x) r

  lemma₁ : x₀ is-a-root-of p → p has-a-root
  lemma₁ h = x₀ , h
\end{code}

We now relate our definition to the original definition using
selection functions. (Possible because choice holds in MLTT.)

\begin{code}

_has-selection_ : ∀ {U} (X : U ̇) → ((X → 𝟚) → X) → U ̇
X has-selection ε = (p : X → 𝟚) → p(ε p) ≡ ₁ → (x : X) → p x ≡ ₁

searchable' : ∀ {U} → U ̇ → U ̇
searchable' X = Σ \(ε : (X → 𝟚) → X) → X has-selection ε

searchable-implies-searchable' : ∀ {U} {X : U ̇} → searchable X → searchable' X
searchable-implies-searchable' {U} {X} ε' = ε , lemma
 where
  ε : (X → 𝟚) → X
  ε p = pr₁(ε' p)

  lemma : (p : X → 𝟚) → p(ε p) ≡ ₁ → (x : X) → p x ≡ ₁
  lemma p = pr₂(ε' p)

\end{code}

In the following we will use ε (rather than ε' as above) to denote
a proof of a proposition of the form (searchable X).

\begin{code}

open import OmniscientTypes

searchable-implies-omniscient : ∀ {U} {X : U ̇} → searchable X → omniscient X
searchable-implies-omniscient {U} {X} ε p = 𝟚-equality-cases case₀ case₁
 where
  x₀ : X
  x₀ = pr₁(ε p)

  lemma : p x₀ ≡ ₁ → (x : X) → p x ≡ ₁
  lemma = pr₂(ε p)

  case₀ : p x₀ ≡ ₀ → (Σ \(x : X) → p x ≡ ₀) + ((x : X) → p x ≡ ₁)
  case₀ r = inl(x₀ , r)

  case₁ : p x₀ ≡ ₁ → (Σ \(x : X) → p x ≡ ₀) + ((x : X) → p x ≡ ₁)
  case₁ r = inr(lemma r)


searchable-implies-inhabited : ∀ {U} {X : U ̇} → searchable X → X
searchable-implies-inhabited ε = pr₁(ε(λ x → ₀))
\end{code}

NB. The empty set is omniscient but of course not inhabited.

It seems unnatural to have a definition of searchability that forces
non-emptiness. There are two cases in which this is natural in our
context: when we show that the searchable sets are precisely the
images of the Cantor space (LMCS'2008), and when we prove the
countable Tychonoff theorem (LMCS'2008) - it is observed in
Escardo-Oliva MSCS'2010 that the inhabitedness of each factor is
absolutely essential. Apart from those cases, we could have formulated
searchability as omniscience (cf. Escardo-Oliva CiE'2010). In fact:

\begin{code}

inhabited-omniscient-implies-searchable : ∀ {U} {X : U ̇} → X → omniscient X → searchable X
inhabited-omniscient-implies-searchable {U} {X} x₀ φ p = lemma(φ p)
 where
  lemma : (Σ \(x : X) → p x ≡ ₀) + ((x : X) → p x ≡ ₁) →
           Σ \(x₀ : X) → p x₀ ≡ ₁ → (x : X) → p x ≡ ₁
  lemma (inl(x , r)) = x , (λ s → 𝟘-elim(Lemma[b≡₀→b≢₁] r s))
  lemma (inr f) = x₀ , (λ r → f)
\end{code}

Some closure properties now:

As a warm-up, we discuss a construction on selection functions
(X → R) → X, and generalized quantifiers (X → R) → R, which we
generalize to get closure of searchable types under Σ.

\begin{code}

module _ {U} {V} {R : V ̇} where

  quantifier : U ̇ → U ⊔ V ̇
  quantifier X = (X → R) → R

  quant-prod : {X : U ̇} {Y : X → U ̇} → quantifier X → ((x : X)  → quantifier (Y x)) → quantifier (Σ Y)
  quant-prod φ γ p = φ(λ x → γ x (λ y → p(x , y)))

  selection : U ̇ → U ⊔ V ̇
  selection X = (X → R) → X

  sel-prod : {X : U ̇} {Y : X → U ̇} → selection X → ((x : X) → selection (Y x)) → selection (Σ Y)
  sel-prod {X} {Y} ε δ p = (x₀ , y₀)
    where
     next : (x : X) → Y x
     next x = δ x (λ y → p(x , y))
     x₀ : X
     x₀ = ε(λ x → p(x , next x))
     y₀ : Y x₀
     y₀ = next x₀

\end{code}

 Alternative, equivalent, construction:

\begin{code}

  overline : {X : U ̇} → selection X → quantifier X
  overline ε p = p(ε p)

  sel-prod' : {X : U ̇} {Y : X → U ̇} → selection X → ((x : X) → selection (Y x)) → selection (Σ Y)
  sel-prod' {X} {Y} ε δ p = (x₀ , y₀)
   where
    x₀ : X
    x₀ = ε(λ x → overline(δ x) (λ y → p(x , y)))
    y₀ : Y x₀
    y₀ = δ x₀ (λ y → p(x₀ , y))

\end{code}

Back to searchable sets:

\begin{code}

Σ-searchable : ∀ {U V} {X : U ̇} {Y : X → V ̇}
             → searchable X → ((x : X) → searchable(Y x)) → searchable(Σ Y)
Σ-searchable {i} {j} {X} {Y} ε δ p = (x₀ , y₀) , correctness
 where
  lemma-next : (x : X) → Σ \(y₀ : Y x) → p(x , y₀) ≡ ₁ → (y : Y x) → p(x , y) ≡ ₁
  lemma-next x = δ x (λ y → p(x , y))

  next : (x : X) → Y x
  next x = pr₁(lemma-next x)

  next-correctness : (x : X) → p(x , next x) ≡ ₁ → (y : Y x) → p(x , y) ≡ ₁
  next-correctness x = pr₂(lemma-next x)

  lemma-first : Σ \(x₀ : X) → p(x₀ , next x₀) ≡ ₁ → (x : X) → p(x , next x) ≡ ₁
  lemma-first = ε(λ x → p(x , next x))

  x₀ : X
  x₀ = pr₁ lemma-first

  first-correctness : p(x₀ , next x₀) ≡ ₁ → (x : X) → p(x , next x) ≡ ₁
  first-correctness = pr₂ lemma-first

  y₀ : Y x₀
  y₀ = next x₀

  correctness : p(x₀ , y₀) ≡ ₁ → (t : (Σ \(x : X) → Y x)) → p t ≡ ₁
  correctness r (x , y) = next-correctness x (first-correctness r x) y

\end{code}

Corollary: Binary products preserve searchability:

\begin{code}

binary-Tychonoff : ∀ {U V} {X : U ̇} {Y : V ̇} → searchable X → searchable Y → searchable(X × Y)
binary-Tychonoff ε δ = Σ-searchable ε (λ i → δ)

\end{code}

Corollary: binary coproducts preserve searchability:

\begin{code}

binary-Σ-searchable' : ∀ {U} {X₀ : U ̇} {X₁ : U ̇}
                                   → searchable X₀ → searchable X₁ → searchable(X₀ +' X₁)
binary-Σ-searchable' {U} {X₀} {X₁} ε₀ ε₁ = Σ-searchable 𝟚-searchable ε
 where
  ε : (i : 𝟚) → _
  ε ₀ = ε₀
  ε ₁ = ε₁

\end{code}

\begin{code}

retractions-preserve-searchability : ∀ {U V} {X : U ̇} {Y : V ̇} {f : X → Y}
                                  → retraction f → searchable X → searchable Y
retractions-preserve-searchability {i} {j} {X} {Y} {f} f-retract ε q = y₀ , h
  where
   p : X → 𝟚
   p x = q(f x)

   x₀ : X
   x₀ = pr₁(ε p)

   y₀ : Y
   y₀ = f x₀

   lemma : p x₀ ≡ ₁ → (x : X) → p x ≡ ₁
   lemma = pr₂(ε p)

   h : q y₀ ≡ ₁ → (a : Y) → q a ≡ ₁
   h r a = fact₁ ⁻¹ ∙ fact₀
    where
     fact : Σ \(x : X) → f x ≡ a
     fact = f-retract a

     x : X
     x = pr₁ fact

     fact₀ : q(f x) ≡ ₁
     fact₀ = lemma r x

     fact₁ : q(f x) ≡ q a
     fact₁ = ap q (pr₂ fact)

retract-searchable : ∀ {U V} {X : U ̇} {Y : V ̇} → retract Y Of X → searchable X → searchable Y
retract-searchable (_ , φ) = retractions-preserve-searchability φ

𝟙+𝟙-searchable : ∀ {U} {V} → searchable (𝟙 {U} + 𝟙 {V})
𝟙+𝟙-searchable = retract-searchable (f , r) 𝟚-searchable
 where
  f : 𝟚 → 𝟙 + 𝟙
  f = 𝟚-cases (inl *) (inr *)
  r : (y : 𝟙 + 𝟙) → Σ \(x : 𝟚) → f x ≡ y
  r (inl *) = ₀ , refl
  r (inr *) = ₁ , refl


equiv-searchable : ∀ {U V} {X : U ̇} {Y : V ̇} → X ≃ Y → searchable X → searchable Y
equiv-searchable (f , (g , fg) , (h , hf)) = retract-searchable (f , (λ y → g y , fg y))

singleton-searchable : ∀ {U} {X : U ̇} → is-singleton X → searchable X
singleton-searchable {U} {X} (x , φ) p = x , g
 where
  g : p x ≡ ₁ → (y : X) → p y ≡ ₁
  g r y = transport (λ - → p - ≡ ₁) (φ y) r

module _ (pt : PropTrunc) where

 open ImageAndSurjection (pt)

 surjection-searchable : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                       → is-surjection f → searchable X → searchable Y
 surjection-searchable {U} {V} {X} {Y} f su ε q = (y₀ , h)
  where
   p : X → 𝟚
   p = q ∘ f

   x₀ : X
   x₀ = pr₁(ε p)

   g : q(f x₀) ≡ ₁ → (x : X) → q(f x) ≡ ₁
   g = pr₂(ε p)

   y₀ : Y
   y₀ = f x₀

   isp : (y : Y) → is-prop (q y ≡ ₁)
   isp y = 𝟚-is-set

   h : q y₀ ≡ ₁ → (y : Y) → q y ≡ ₁
   h r = surjection-induction f su (λ y → q y ≡ ₁) isp (g r)

 image-searchable : ∀ {X Y : U₀ ̇} (f : X → Y)
                 → searchable X → searchable (image f)
 image-searchable f = surjection-searchable (corestriction f)
                                            (corestriction-surjection f)

\end{code}
