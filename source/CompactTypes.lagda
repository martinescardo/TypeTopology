Martin Escardo 2011, reorganized and expanded 2018.

Compact types.

(This is related to my 2008 LMCS paper "Exhaustible sets in higher-type
computation", where compact types correspond to "exhaustible sets" and
compact∙ types (compact-pointed types) correpond to searchable sets.
It is also related to joint work with Oliva on selection functions in
proof theory.)

Here we don't assume continuity axioms, but all functions are secretly
continuous, and compact sets are secretly topologically compact.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module CompactTypes where

open import SpartanMLTT
open import Two
open import Two-Prop-Density
open import DiscreteAndSeparated
open import DecidableAndDetachable
open import UF-Subsingletons
open import UF-FunExt
open import UF-Retracts
open import UF-Equiv
open import UF-PropTrunc
open import UF-ImageAndSurjection
open import UF-Miscelanea

\end{code}

We say that a type is compact if for every 𝟚-valued function defined
on it, it decidable whether it has a root:

\begin{code}

compact : ∀ {U} → U ̇ → U ̇
compact X = (p : X → 𝟚) → (Σ \(x : X) → p x ≡ ₀) + (Π \(x : X) → p x ≡ ₁)

\end{code}

Notice that compactness in this sense is not in general a univalent
proposition (subsingleton). A weaker notion that is always a proposition is
defined and studied in the module WeaklyCompactTypes.

The following notion is logically equivalent to the conjunction of
compactness and pointedness, and hence the notation "compact∙":

\begin{code}

compact∙ : ∀ {U} → U ̇ → U ̇
compact∙ X = (p : X → 𝟚) → Σ \(x₀ : X) → p x₀ ≡ ₁ → (x : X) → p x ≡ ₁

\end{code}

Terminology: we call x₀ the universal witness.

\begin{code}

compact-pointed-gives-compact∙ : ∀ {U} {X : U ̇} → compact X → X → compact∙ X
compact-pointed-gives-compact∙ {U} {X} φ x₀ p = lemma(φ p)
 where
  lemma : (Σ \(x : X) → p x ≡ ₀) + ((x : X) → p x ≡ ₁) →
           Σ \(x₀ : X) → p x₀ ≡ ₁ → (x : X) → p x ≡ ₁
  lemma (inl(x , r)) = x , (λ s → 𝟘-elim(Lemma[b≡₀→b≢₁] r s))
  lemma (inr f) = x₀ , (λ r → f)

compact∙-gives-compact : ∀ {U} {X : U ̇} → compact∙ X → compact X
compact∙-gives-compact {U} {X} ε p = 𝟚-equality-cases case₀ case₁
 where
  x₀ : X
  x₀ = pr₁(ε p)
  lemma : p x₀ ≡ ₁ → (x : X) → p x ≡ ₁
  lemma = pr₂(ε p)
  case₀ : p x₀ ≡ ₀ → (Σ \(x : X) → p x ≡ ₀) + ((x : X) → p x ≡ ₁)
  case₀ r = inl(x₀ , r)
  case₁ : p x₀ ≡ ₁ → (Σ \(x : X) → p x ≡ ₀) + ((x : X) → p x ≡ ₁)
  case₁ r = inr(lemma r)

compact∙-gives-pointed : ∀ {U} {X : U ̇} → compact∙ X → X
compact∙-gives-pointed ε = pr₁(ε(λ x → ₀))

\end{code}

For example, every finite set is compact, and in particular the
set 𝟚 = { ₀ , ₁ } of binary numerals is compact. To find x₀ : 𝟚
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

𝟚-compact∙ : compact∙ 𝟚
𝟚-compact∙ p = x₀ , (λ r → 𝟚-induction (lemma₀ r) (lemma₁ r))
 where
    x₀ : 𝟚
    x₀ = p ₀
    claim : p x₀ ≡ ₁ → p ₀ ≡ ₀ → p ₀ ≡ ₁
    claim r s = transport (λ - → p - ≡ ₁) s r
    lemma₀ : p x₀ ≡ ₁ → p ₀ ≡ ₁
    lemma₀ r = 𝟚-equality-cases (claim r) (λ s → s)
    lemma₁ : p x₀ ≡ ₁ → p ₁ ≡ ₁
    lemma₁ r = transport (λ - → p - ≡ ₁) (lemma₀ r) r

\end{code}

Even though excluded middle is undecided, the set Ω U of univalent
propositions in any universe U is compact (assuming propositional
extensionality, which is a consequence of univalence):

\begin{code}

Ω-compact∙ : ∀ {U} → funext U U → propext U → compact∙ (Ω U)
Ω-compact∙ {U} fe pe p = 𝟚-equality-cases a b
  where
    A = Σ \(x₀ : Ω U) → p x₀ ≡ ₁ → (x : Ω U) → p x ≡ ₁
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

We could have used the same idea of proof as for 𝟚-compact, again
using density.

\begin{code}

𝟙-compact∙ : ∀ {U} → compact∙ (𝟙 {U})
𝟙-compact∙ p = * , f
 where
  f : (r : p * ≡ ₁) (x : 𝟙) → p x ≡ ₁
  f r * = r

\end{code}

In this module we prove some closure properties of compact
sets. Before doing this, we investigate their general nature.

We first show that the universal witness x₀ is a root of p if and
only if p has a root.

\begin{code}

_is-a-root-of_ : ∀ {U} {X : U ̇} → X → (X → 𝟚) → U₀ ̇
x is-a-root-of p = p x ≡ ₀

_has-a-root : ∀ {U} {X : U ̇} → (X → 𝟚) → U ̇
p has-a-root = Σ \x → x is-a-root-of p

putative-root : ∀ {U} {X : U ̇}
              → compact∙ X → (p : X → 𝟚) → Σ \(x₀ : X) → (p has-a-root) ⇔ (x₀ is-a-root-of p)
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
selection functions.

\begin{code}

_has-selection_ : ∀ {U} (X : U ̇) → ((X → 𝟚) → X) → U ̇
X has-selection ε = (p : X → 𝟚) → p(ε p) ≡ ₁ → (x : X) → p x ≡ ₁

compact∙' : ∀ {U} → U ̇ → U ̇
compact∙' X = Σ \(ε : (X → 𝟚) → X) → X has-selection ε

compact∙-gives-compact∙' : ∀ {U} {X : U ̇} → compact∙ X → compact∙' X
compact∙-gives-compact∙' {U} {X} ε' = ε , lemma
 where
  ε : (X → 𝟚) → X
  ε p = pr₁(ε' p)
  lemma : (p : X → 𝟚) → p(ε p) ≡ ₁ → (x : X) → p x ≡ ₁
  lemma p = pr₂(ε' p)

\end{code}

Notice that Bishop's limited principle of omniscience LPO, which is a
taboo, in Aczel's terminology, is the compactness of ℕ. LPO is
independent - it is not provable, and its negation is not provable. In
classical mathematics it is uncomfortable to have independent
propositions, but of course unavoidable. Independence occurs often in
constructive mathematics, particular in classically compatible
constructive mathematics, like Bishop's methamatics and Martin-Löf
type theory (in its various flavours); even the principle of excluded
middle is independent.

We'll see that the infinite set ℕ∞ defined in the module
ConvergentSequenceCompact.

If a set X is compact∙ and a set Y has decidable equality, then the
function space (X → Y) has decidable equality, if we assume function
extensionality. In our topological correspondence, decidable equality
is called discreteness. More generally we have:

\begin{code}

apart-or-equal : ∀ {U V} {X : U ̇} → funext U V → {Y : X → V ̇}
              → compact X → ((x : X) → discrete(Y x))
              → (f g : (x : X) → Y x) → (f ♯ g) + (f ≡ g)
apart-or-equal {U} {V} {X} fe {Y} φ d f g = lemma₂ lemma₁
 where
  claim : (x : X) → (f x ≢ g x) + (f x ≡ g x)
  claim x = +-commutative(d x (f x) (g x))
  lemma₀ : Σ \(p : X → 𝟚) → (x : X) → (p x ≡ ₀ → f x ≢ g x) × (p x ≡ ₁ → f x ≡ g x)
  lemma₀ = indicator claim
  p : X → 𝟚
  p = pr₁ lemma₀
  lemma₁ : (Σ \x → p x ≡ ₀) + ((x : X) → p x ≡ ₁)
  lemma₁ = φ p
  lemma₂ : (Σ \x → p x ≡ ₀) + ((x : X) → p x ≡ ₁) → (f ♯ g) + (f ≡ g)
  lemma₂(inl(x , r)) = inl(x , (pr₁(pr₂ lemma₀ x) r))
  lemma₂(inr h) = inr (dfunext fe (λ x → pr₂(pr₂ lemma₀ x) (h x)))

compact-discrete-discrete : ∀ {U V} {X : U ̇} → funext U V → {Y : X → V ̇} →

   compact X → ((x : X) → discrete(Y x)) → discrete((x : X) → Y x)

compact-discrete-discrete fe φ d f g = h(apart-or-equal fe φ d f g)
 where
  h : (f ♯ g) + (f ≡ g) → (f ≡ g) + (f ≢ g)
  h(inl a) = inr(apart-is-different a)
  h(inr r) = inl r

compact-discrete-discrete' : ∀ {U V} {X : U ̇} {Y : V ̇} → funext U V
                             → compact X → discrete Y → discrete(X → Y)
compact-discrete-discrete' fe φ d = compact-discrete-discrete fe φ (λ x → d)

𝟘-compact : ∀ {U} → compact 𝟘
𝟘-compact {U} p = inr (λ x → 𝟘-elim {U₀} {U} x)

compact-decidable : ∀ {U} (X : U ̇) → compact X → decidable X
compact-decidable X φ = f a
 where
  a : (X × (₀ ≡ ₀)) + (X → ₀ ≡ ₁)
  a = φ (λ x → ₀)
  f : (X × (₀ ≡ ₀)) + (X → ₀ ≡ ₁) → decidable X
  f (inl (x , _)) = inl x
  f (inr u)       = inr (λ x → zero-is-not-one (u x))

decidable-prop-compact : ∀ {U} (X : U ̇) → is-prop X → decidable X → compact X
decidable-prop-compact X isp δ p = g δ
 where
  g : decidable X → (Σ \(x : X) → p x ≡ ₀) + Π \(x : X) → p x ≡ ₁
  g (inl x) = 𝟚-equality-cases b c
   where
    b : p x ≡ ₀ → (Σ \(x : X) → p x ≡ ₀) + Π \(x : X) → p x ≡ ₁
    b r = inl (x , r)
    c : p x ≡ ₁ → (Σ \(x : X) → p x ≡ ₀) + Π \(x : X) → p x ≡ ₁
    c r = inr (λ y → transport (λ - → p - ≡ ₁) (isp x y) r)
  g (inr u) = inr (λ x → 𝟘-elim (u x))

\end{code}

Some closure properties now.

As a warm-up, we discuss a construction on selection functions
(X → R) → X, and generalized quantifiers (X → R) → R, which we
generalize to get closure of compact types under Σ.

\begin{code}

module warmup {U} {V} {R : V ̇} where

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

Back to compact sets:

\begin{code}

Σ-compact∙ : ∀ {U V} {X : U ̇} {Y : X → V ̇}
           → compact∙ X → ((x : X) → compact∙(Y x)) → compact∙(Σ Y)
Σ-compact∙ {i} {j} {X} {Y} ε δ p = (x₀ , y₀) , correctness
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

Corollary: Binary products preserve compactness:

\begin{code}

binary-Tychonoff : ∀ {U V} {X : U ̇} {Y : V ̇} → compact∙ X → compact∙ Y → compact∙(X × Y)
binary-Tychonoff ε δ = Σ-compact∙ ε (λ i → δ)

binary-Σ-compact∙' : ∀ {U} {X₀ : U ̇} {X₁ : U ̇}
                   → compact∙ X₀ → compact∙ X₁ → compact∙(X₀ +' X₁)
binary-Σ-compact∙' {U} {X₀} {X₁} ε₀ ε₁ = Σ-compact∙ 𝟚-compact∙ ε
 where
  ε : (i : 𝟚) → _
  ε ₀ = ε₀
  ε ₁ = ε₁

retractions-preserve-compactness : ∀ {U V} {X : U ̇} {Y : V ̇} {f : X → Y}
                                 → retraction f → compact∙ X → compact∙ Y
retractions-preserve-compactness {i} {j} {X} {Y} {f} f-retract ε q = y₀ , h
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

retract-compact∙ : ∀ {U V} {X : U ̇} {Y : V ̇} → retract Y Of X → compact∙ X → compact∙ Y
retract-compact∙ (_ , φ) = retractions-preserve-compactness φ

𝟙+𝟙-compact∙ : ∀ {U} {V} → compact∙ (𝟙 {U} + 𝟙 {V})
𝟙+𝟙-compact∙ = retract-compact∙ (f , r) 𝟚-compact∙
 where
  f : 𝟚 → 𝟙 + 𝟙
  f = 𝟚-cases (inl *) (inr *)
  r : (y : 𝟙 + 𝟙) → Σ \(x : 𝟚) → f x ≡ y
  r (inl *) = ₀ , refl
  r (inr *) = ₁ , refl

equiv-compact∙ : ∀ {U V} {X : U ̇} {Y : V ̇} → X ≃ Y → compact∙ X → compact∙ Y
equiv-compact∙ (f , (g , fg) , (h , hf)) = retract-compact∙ (f , (λ y → g y , fg y))

singleton-compact∙ : ∀ {U} {X : U ̇} → is-singleton X → compact∙ X
singleton-compact∙ {U} {X} (x , φ) p = x , g
 where
  g : p x ≡ ₁ → (y : X) → p y ≡ ₁
  g r y = transport (λ - → p - ≡ ₁) (φ y) r

module _ (pt : PropTrunc) where

 open ImageAndSurjection (pt)

 surjection-compact∙ : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                     → is-surjection f → compact∙ X → compact∙ Y
 surjection-compact∙ {U} {V} {X} {Y} f su ε q = (y₀ , h)
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

 image-compact∙ : ∀ {X Y : U₀ ̇} (f : X → Y)
                → compact∙ X → compact∙ (image f)
 image-compact∙ f = surjection-compact∙ (corestriction f)
                                        (corestriction-surjection f)

\end{code}

The following is from 2011 originally in the module ExhaustibleTypes,
where "wcompact" was "exhaustible". We should remove this, or move it
to the module WeaklyCompactTypes, as wcompact is equivalent to
Π-compact.

\begin{code}

wcompact : ∀ {U} → U ̇ → U ̇
wcompact X = (p : X → 𝟚) → Σ \(y : 𝟚) → y ≡ ₁ ⇔ ((x : X) → p x ≡ ₁)

\end{code}

Closer to the original definition of exhaustibility in LICS'2007 amd LMCS'2008:

\begin{code}

wcompact' : ∀ {U} → U ̇ → U ̇
wcompact' X = Σ \(A : (X → 𝟚) → 𝟚) → (p : X → 𝟚) → A p ≡ ₁ ⇔ ((x : X) → p x ≡ ₁)

\end{code}

Because the Curry-Howard interpretation of the axiom of choice holds
in MLTT:

\begin{code}

wcompact-implies-wcompact' : ∀ {U} {X : U ̇} → wcompact X → wcompact' X
wcompact-implies-wcompact' {U} {X} φ = A , lemma
 where A : (X → 𝟚) → 𝟚
       A p = pr₁(φ p)
       lemma : (p : X → 𝟚) → A p ≡ ₁ ⇔ ((x : X) → p x ≡ ₁)
       lemma p = pr₂(φ p)

compact-gives-wcompact : ∀ {U} {X : U ̇} → compact∙ X → wcompact X
compact-gives-wcompact {U} {X} ε p = y , (lemma₀ , lemma₁)
 where
  x₀ : X
  x₀ = pr₁(ε p)
  y : 𝟚
  y = p x₀
  lemma₀ :  y ≡ ₁ → (x : X) → p x ≡ ₁
  lemma₀ = pr₂(ε p)
  lemma₁ : ((x : X) → p x ≡ ₁) → y ≡ ₁
  lemma₁ h = h x₀

\end{code}
