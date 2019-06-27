Martin Escardo 2011, reorganized and expanded 2018.

Compact types. We shall call a type compact if it is exhaustibly
searchable. But there are many closely related, but different, notions
of searchability, and we investigate this phenomenon in this module
and the module WeaklyCompactTypes.

Perhaps surprisingly, there are infinite searchable sets, such as ℕ∞
(see the module GenericConvergentSequenceCompact).

It is in general not possible to constructively decide the statement

  Σ \(x : X) → p x ≡ ₀

that a given function p : X → 𝟚 defined on a type X has a root.

We say that a type X is Σ-compact, or simply compact for short, if
this statement is decidable for every p : X → 𝟚. This is equivalent to

  Π \(p : X → 𝟚) → (Σ \(x : X) → p x ≡ ₀) + (Π \(x : X) → p x ≡ ₁).

We can also ask whether the statements

  ∃ \(x : X) → p x ≡ ₀   and   Π \(x : X) → p x ≡ ₀

are decidable for every p, and in these cases we say that X is
∃-compact and Π-compact respectively. We have

  Σ-compact X → ∃-compact X → Π-compact X.

In this module we study Σ-compactness, and in the module
WeaklyCompactTypes we study ∃-compact and Π-compact types.

If X is the finite type Fin n for some n : ℕ, then it is
Σ-compact. But even if X is a subtype of 𝟙 ≃ Fin 1, or a univalent
proposition, this is not possible in general. Even worse, X may be an
infinite set such as ℕ, and the Σ-compactness of ℕ amounts to Bishop's
Limited Principle of Omniscience (LPO), which is not provable in any
variety of constructive mathematics. It is even disprovable in some
varieties of constructive mathematics (e.g. if we have continuity or
computability principles), but not in any variety of constructive
mathematics compatible with non-constructive mathematics, such as
ours, in which LPO is an undecided statement. However, even though ℕ∞
is larger than ℕ, in the sense that we have an embedding ℕ → ℕ∞, it
does satisfy the principle of omniscience, or, using the above
terminology, is Σ-compact.

Because of the relation to LPO, we formerly referred to Σ- or
∃-compact sets as "omniscient" sets:

   Martin H. Escardo, Infinite sets that satisfy the principle of
   omniscience in any variety of constructive mathematics. The Journal
   of Symbolic Logic, Vol 78, September 2013, pp. 764-784.
   https://www.jstor.org/stable/43303679

And because of the connection with computation, we called them
exhaustively searchable, or exhaustible or searchable:

   Martin Escardo. Exhaustible sets in higher-type computation. Logical
   Methods in Computer Science, August 27, 2008, Volume 4, Issue 3.
   https://lmcs.episciences.org/693

The name "compact" is appropriate, because e.g. in the model of
Kleene-Kreisel spaces for simple types, it does correspond to
topological compactness, as proved in the above LMCS paper.

We emphasize that here we don't assume continuity axioms, but all
functions are secretly continuous, and compact sets are secretly
topologically compact, when one reasons constructively.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module CompactTypes where

open import SpartanMLTT

open import Two-Properties
open import Two-Prop-Density
open import Plus-Properties
open import AlternativePlus
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

Σ-compact : 𝓤 ̇ → 𝓤 ̇
Σ-compact X = (p : X → 𝟚) → (Σ \(x : X) → p x ≡ ₀) + (Π \(x : X) → p x ≡ ₁)

compact : 𝓤 ̇ → 𝓤 ̇
compact = Σ-compact

\end{code}

Notice that compactness in this sense is not in general a univalent
proposition (subsingleton). Weaker notions, ∃-compactness and
Π-compactness, that are always propositions are defined and studied in
the module WeaklyCompactTypes.

The following notion is logically equivalent to the conjunction of
compactness and pointedness, and hence the notation "compact∙":

\begin{code}

compact∙ : 𝓤 ̇ → 𝓤 ̇
compact∙ X = (p : X → 𝟚) → Σ \(x₀ : X) → p x₀ ≡ ₁ → (x : X) → p x ≡ ₁

\end{code}

Terminology: we call x₀ the universal witness.

\begin{code}

compact-pointed-gives-compact∙ : {X : 𝓤 ̇ } → compact X → X → compact∙ X
compact-pointed-gives-compact∙ {𝓤} {X} φ x₀ p = lemma(φ p)
 where
  lemma : (Σ \(x : X) → p x ≡ ₀) + ((x : X) → p x ≡ ₁) →
           Σ \(x₀ : X) → p x₀ ≡ ₁ → (x : X) → p x ≡ ₁
  lemma (inl(x , r)) = x , (λ s → 𝟘-elim(equal-₀-different-from-₁ r s))
  lemma (inr f) = x₀ , (λ r → f)

compact∙-gives-compact : {X : 𝓤 ̇ } → compact∙ X → compact X
compact∙-gives-compact {𝓤} {X} ε p = 𝟚-equality-cases case₀ case₁
 where
  x₀ : X
  x₀ = pr₁(ε p)
  lemma : p x₀ ≡ ₁ → (x : X) → p x ≡ ₁
  lemma = pr₂(ε p)
  case₀ : p x₀ ≡ ₀ → (Σ \(x : X) → p x ≡ ₀) + ((x : X) → p x ≡ ₁)
  case₀ r = inl(x₀ , r)
  case₁ : p x₀ ≡ ₁ → (Σ \(x : X) → p x ≡ ₀) + ((x : X) → p x ≡ ₁)
  case₁ r = inr(lemma r)

compact∙-gives-pointed : {X : 𝓤 ̇ } → compact∙ X → X
compact∙-gives-pointed ε = pr₁(ε(λ x → ₀))

\end{code}

There are examples where pointedness is crucial. For instance, the
product of a family of compact-pointed typed indexed by a subsingleton
is always compact (pointed), but the assumption that this holds
without the assumption of pointedness implies weak excluded middle
(the negation of any proposition is decidable).

For example, every finite set is compact, and in particular the set 𝟚
of binary digits ₀ and ₁ is compact. To find x₀ : 𝟚 such that

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

Even though excluded middle is undecided, the set Ω 𝓤 of univalent
propositions in any universe U is compact (assuming propositional
extensionality, which is a consequence of univalence):

\begin{code}

Ω-compact∙ : funext 𝓤 𝓤 → propext 𝓤 → compact∙ (Ω 𝓤)
Ω-compact∙ {𝓤} fe pe p = 𝟚-equality-cases a b
  where
    A = Σ \(x₀ : Ω 𝓤) → p x₀ ≡ ₁ → (x : Ω 𝓤) → p x ≡ ₁
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

𝟙-compact∙ : compact∙ (𝟙 {𝓤})
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

_is-a-root-of_ : {X : 𝓤 ̇ } → X → (X → 𝟚) → 𝓤₀ ̇
x is-a-root-of p = p x ≡ ₀

_has-a-root : {X : 𝓤 ̇ } → (X → 𝟚) → 𝓤 ̇
p has-a-root = Σ \x → x is-a-root-of p

putative-root : {X : 𝓤 ̇ }
              → compact∙ X → (p : X → 𝟚) → Σ \(x₀ : X) → (p has-a-root) ⇔ (x₀ is-a-root-of p)
putative-root {𝓤} {X} ε p = x₀ , (lemma₀ , lemma₁)
 where
  x₀ : X
  x₀ = pr₁(ε p)
  lemma : ¬((x : X) → p x ≡ ₁) → p x₀ ≡ ₀
  lemma = different-from-₁-equal-₀ ∘ contrapositive(pr₂(ε p))
  lemma₀ : p has-a-root → x₀ is-a-root-of p
  lemma₀ (x , r) = lemma claim
   where claim : ¬((x : X) → p x ≡ ₁)
         claim f = equal-₁-different-from-₀ (f x) r
  lemma₁ : x₀ is-a-root-of p → p has-a-root
  lemma₁ h = x₀ , h
\end{code}

We now relate our definition to the original definition using
selection functions.

\begin{code}

_has-selection_ : (X : 𝓤 ̇ ) → ((X → 𝟚) → X) → 𝓤 ̇
X has-selection ε = (p : X → 𝟚) → p(ε p) ≡ ₁ → (x : X) → p x ≡ ₁

compact∙' : 𝓤 ̇ → 𝓤 ̇
compact∙' X = Σ \(ε : (X → 𝟚) → X) → X has-selection ε

compact∙-gives-compact∙' : {X : 𝓤 ̇ } → compact∙ X → compact∙' X
compact∙-gives-compact∙' {𝓤} {X} ε' = ε , lemma
 where
  ε : (X → 𝟚) → X
  ε p = pr₁(ε' p)
  lemma : (p : X → 𝟚) → p(ε p) ≡ ₁ → (x : X) → p x ≡ ₁
  lemma p = pr₂(ε' p)

compact∙'-gives-compact∙ : {X : 𝓤 ̇ } → compact∙' X → compact∙ X
compact∙'-gives-compact∙ {𝓤} {X} ε p = x₀ , lemma
 where
  x₀ : X
  x₀ = pr₁ ε p
  lemma : p x₀ ≡ ₁ → (x : X) → p x ≡ ₁
  lemma u β = pr₂ ε p u β

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

apart-or-equal : {X : 𝓤 ̇ } → funext 𝓤 𝓥 → {Y : X → 𝓥 ̇ }
              → compact X → ((x : X) → is-discrete(Y x))
              → (f g : (x : X) → Y x) → (f ♯ g) + (f ≡ g)
apart-or-equal {𝓤} {𝓥} {X} fe {Y} φ d f g = lemma₂ lemma₁
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

compact-discrete-discrete : {X : 𝓤 ̇ } → funext 𝓤 𝓥 → {Y : X → 𝓥 ̇ } →

   compact X → ((x : X) → is-discrete(Y x)) → is-discrete((x : X) → Y x)

compact-discrete-discrete fe φ d f g = h(apart-or-equal fe φ d f g)
 where
  h : (f ♯ g) + (f ≡ g) → (f ≡ g) + (f ≢ g)
  h(inl a) = inr(apart-is-different a)
  h(inr r) = inl r

compact-discrete-discrete' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → funext 𝓤 𝓥
                           → compact X → is-discrete Y → is-discrete(X → Y)
compact-discrete-discrete' fe φ d = compact-discrete-discrete fe φ (λ x → d)

𝟘-compact : compact (𝟘 {𝓤})
𝟘-compact {𝓤} p = inr (λ x → 𝟘-elim {𝓤₀} {𝓤} x)

compact-decidable : (X : 𝓤 ̇ ) → compact X → decidable X
compact-decidable X φ = f a
 where
  a : (X × (₀ ≡ ₀)) + (X → ₀ ≡ ₁)
  a = φ (λ x → ₀)
  f : (X × (₀ ≡ ₀)) + (X → ₀ ≡ ₁) → decidable X
  f (inl (x , _)) = inl x
  f (inr u)       = inr (λ x → zero-is-not-one (u x))

decidable-prop-compact : (X : 𝓤 ̇ ) → is-prop X → decidable X → compact X
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

module warmup {𝓤} {𝓥} {R : 𝓥 ̇ } where

  quantifier : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
  quantifier X = (X → R) → R

  quant-prod : {X : 𝓤 ̇ } {Y : X → 𝓤 ̇ } → quantifier X → ((x : X)  → quantifier (Y x)) → quantifier (Σ Y)
  quant-prod φ γ p = φ(λ x → γ x (λ y → p(x , y)))

  selection : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
  selection X = (X → R) → X

  sel-prod : {X : 𝓤 ̇ } {Y : X → 𝓤 ̇ } → selection X → ((x : X) → selection (Y x)) → selection (Σ Y)
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

  overline : {X : 𝓤 ̇ } → selection X → quantifier X
  overline ε p = p(ε p)

  sel-prod' : {X : 𝓤 ̇ } {Y : X → 𝓤 ̇ } → selection X → ((x : X) → selection (Y x)) → selection (Σ Y)
  sel-prod' {X} {Y} ε δ p = (x₀ , y₀)
   where
    x₀ : X
    x₀ = ε(λ x → overline(δ x) (λ y → p(x , y)))
    y₀ : Y x₀
    y₀ = δ x₀ (λ y → p(x₀ , y))

\end{code}

Back to compact sets:

\begin{code}

Σ-compact∙ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
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

binary-Tychonoff : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → compact∙ X → compact∙ Y → compact∙(X × Y)
binary-Tychonoff ε δ = Σ-compact∙ ε (λ i → δ)

binary-Σ-compact∙' : {X₀ : 𝓤 ̇ } {X₁ : 𝓤 ̇ }
                   → compact∙ X₀ → compact∙ X₁ → compact∙(X₀ +' X₁)
binary-Σ-compact∙' {𝓤} {X₀} {X₁} ε₀ ε₁ = Σ-compact∙ 𝟚-compact∙ ε
 where
  ε : (i : 𝟚) → _
  ε ₀ = ε₀
  ε ₁ = ε₁

retractions-preserve-compactness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y}
                                 → has-section' f → compact∙ X → compact∙ Y
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

retract-compact∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → retract Y Of X → compact∙ X → compact∙ Y
retract-compact∙ (_ , φ) = retractions-preserve-compactness φ

𝟙+𝟙-compact∙ : compact∙ (𝟙 {𝓤} + 𝟙 {𝓥})
𝟙+𝟙-compact∙ = retract-compact∙ (f , r) 𝟚-compact∙
 where
  f : 𝟚 → 𝟙 + 𝟙
  f = 𝟚-cases (inl *) (inr *)
  r : (y : 𝟙 + 𝟙) → Σ \(x : 𝟚) → f x ≡ y
  r (inl *) = ₀ , refl
  r (inr *) = ₁ , refl

equiv-compact∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → compact∙ X → compact∙ Y
equiv-compact∙ (f , (g , fg) , (h , hf)) = retract-compact∙ (f , (λ y → g y , fg y))

singleton-compact∙ : {X : 𝓤 ̇ } → is-singleton X → compact∙ X
singleton-compact∙ {𝓤} {X} (x , φ) p = x , g
 where
  g : p x ≡ ₁ → (y : X) → p y ≡ ₁
  g r y = transport (λ - → p - ≡ ₁) (φ y) r

module _ (pt : propositional-truncations-exist) where

 open ImageAndSurjection pt

 surjection-compact∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                     → is-surjection f → compact∙ X → compact∙ Y
 surjection-compact∙ {𝓤} {𝓥} {X} {Y} f su ε q = (y₀ , h)
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

 image-compact∙ : ∀ {X Y : 𝓤₀ ̇ } (f : X → Y)
                → compact∙ X → compact∙ (image f)
 image-compact∙ f = surjection-compact∙ (corestriction f)
                                        (corestriction-surjection f)

\end{code}

The following is from 2011 originally in the module ExhaustibleTypes,
where "wcompact" was "exhaustible". We should remove this, or move it
to the module WeaklyCompactTypes, as wcompact is equivalent to
Π-compact.

\begin{code}

wcompact : 𝓤 ̇ → 𝓤 ̇
wcompact X = (p : X → 𝟚) → Σ \(y : 𝟚) → y ≡ ₁ ⇔ ((x : X) → p x ≡ ₁)

\end{code}

Closer to the original definition of exhaustibility in LICS'2007 amd LMCS'2008:

\begin{code}

wcompact' : 𝓤 ̇ → 𝓤 ̇
wcompact' X = Σ \(A : (X → 𝟚) → 𝟚) → (p : X → 𝟚) → A p ≡ ₁ ⇔ ((x : X) → p x ≡ ₁)

\end{code}

Because the Curry-Howard interpretation of the axiom of choice holds
in MLTT:

\begin{code}

wcompact-implies-wcompact' : {X : 𝓤 ̇ } → wcompact X → wcompact' X
wcompact-implies-wcompact' {𝓤} {X} φ = A , lemma
 where
  A : (X → 𝟚) → 𝟚
  A p = pr₁(φ p)
  lemma : (p : X → 𝟚) → A p ≡ ₁ ⇔ ((x : X) → p x ≡ ₁)
  lemma p = pr₂(φ p)

compact-gives-wcompact : {X : 𝓤 ̇ } → compact∙ X → wcompact X
compact-gives-wcompact {𝓤} {X} ε p = y , (lemma₀ , lemma₁)
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
