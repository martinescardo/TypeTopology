Martin Escardo 2011, reorganized and expanded 2018,2019.

Compact types. We shall call a type compact if it is exhaustibly
searchable. But there are many closely related, but different, notions
of searchability, and we investigate this phenomenon in this module
and the module WeaklyCompactTypes.

Perhaps surprisingly, there are infinite searchable sets, such as ℕ∞
(see the module GenericConvergentSequenceCompact).

It is in general not possible to decide constructively the statement

  Σ x ꞉ X , p x ≡ ₀

that a given function p : X → 𝟚 defined on a type X has a root.

We say that a type X is Σ-compact, or simply compact for short, if
this statement is decidable for every p : X → 𝟚. This is equivalent to

  Π p ꞉ X → 𝟚 , (Σ x ꞉ X , p x ≡ ₀) + (Π x ꞉ X , p x ≡ ₁).

We can also ask whether the statements

  ∃ x : X , p x ≡ ₀   and   Π x ꞉ X , p x ≡ ₀

are decidable for every p, and in these cases we say that X is
is ∃-compact and is Π-compact respectively. We have

  Σ-compact X → ∃-compact X → Π-compact X.

In this module we study Σ-compactness, and in the module
WeaklyCompactTypes we study ∃-compact and Π-compact types.

If X is the finite type Fin n for some n : ℕ, then it is
Σ-compact. But even if X is a subtype of Fin 1, or a univalent
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

The name "compact" is also adopted in Longley and Normann's book
"Higher-Order Computability" (Springer 2015).

We emphasize that here we don't assume continuity axioms, but all
functions are secretly continuous, and compact sets are secretly
topologically compact, when one reasons constructively.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module CompactTypes where

open import SpartanMLTT

open import Two-Properties
open import Plus-Properties
open import AlternativePlus
open import DiscreteAndSeparated
open import DecidableAndDetachable public

open import UF-Base
open import UF-Subsingletons renaming (⊤Ω to ⊤ ; ⊥Ω to ⊥)
open import UF-Subsingletons-FunExt
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
Σ-compact X = (p : X → 𝟚) → (Σ x ꞉ X , p x ≡ ₀) + (Π x ꞉ X , p x ≡ ₁)

compact    = Σ-compact

\end{code}

Notice that compactness in this sense is not in general a univalent
proposition (subsingleton). Weaker notions, ∃-compactness and
Π-compactness, that are always propositions are defined and studied in
the module WeaklyCompactTypes.

The following notion is logically equivalent to the conjunction of
compactness and pointedness, and hence the notation "compact∙":

\begin{code}

compact∙ : 𝓤 ̇ → 𝓤 ̇
compact∙ X = (p : X → 𝟚) → Σ x₀ ꞉ X , (p x₀ ≡ ₁ → (x : X) → p x ≡ ₁)

\end{code}

Terminology: we call x₀ the universal witness.

\begin{code}

compact-pointed-gives-compact∙ : {X : 𝓤 ̇ } → compact X → X → compact∙ X
compact-pointed-gives-compact∙ {𝓤} {X} φ x₀ p = γ (φ p)
 where
  γ : (Σ x ꞉ X , p x ≡ ₀) + ((x : X) → p x ≡ ₁)
    → Σ x₀ ꞉ X , (p x₀ ≡ ₁ → (x : X) → p x ≡ ₁)
  γ (inl (x , r)) = x , (λ s → 𝟘-elim (equal-₀-different-from-₁ r s))
  γ (inr f) = x₀ , (λ r → f)

compact∙-gives-compact : {X : 𝓤 ̇ } → compact∙ X → compact X
compact∙-gives-compact {𝓤} {X} ε p = 𝟚-equality-cases case₀ case₁
 where
  x₀ : X
  x₀ = pr₁ (ε p)

  lemma : p x₀ ≡ ₁ → (x : X) → p x ≡ ₁
  lemma = pr₂ (ε p)

  case₀ : p x₀ ≡ ₀ → (Σ x ꞉ X , p x ≡ ₀) + ((x : X) → p x ≡ ₁)
  case₀ r = inl (x₀ , r)

  case₁ : p x₀ ≡ ₁ → (Σ x ꞉ X , p x ≡ ₀) + ((x : X) → p x ≡ ₁)
  case₁ r = inr (lemma r)

compact∙-gives-pointed : {X : 𝓤 ̇ } → compact∙ X → X
compact∙-gives-pointed ε = pr₁ (ε (λ x → ₀))

\end{code}

There are examples where pointedness is crucial. For instance, the
product of a family of compact-pointed types indexed by a subsingleton
is always compact (pointed), but the assumption that this holds
without the assumption of pointedness implies weak excluded middle
(the negation of any proposition is decidable).

For example, every finite set is compact, and in particular the set 𝟚
of binary digits ₀ and ₁ is compact. To find x₀ : 𝟚 such that

   (†) p x₀ ≡ ₁ → ∀ (x : X) → p x ≡ ₁,

we can check whether p ₀ ≡ ₁ and p ₁ ≡ ₁.

     If this is the case, then ∀ (x : X) → p x ≡ ₁ holds, which is
     the conclusion the implication (†), and hence we can take any
     x₀ : 𝟚 to make (†) hold.

     Otherwise, we can take any x₀ such that p x₀ ≡ ₀ so that the
     implication (†) holds vacuously.

That is, either the conclusion ∀ (x : X) → p x ≡ ₁ of (†) holds, or
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

𝟚-compact : compact 𝟚
𝟚-compact = compact∙-gives-compact 𝟚-compact∙

\end{code}

Even though excluded middle is undecided, the set Ω 𝓤 of univalent
propositions in any universe 𝓤 is compact, assuming functional and
propositional extensionality, which are consequences of univalence:

\begin{code}

Ω-compact∙ : funext 𝓤 𝓤 → propext 𝓤 → compact∙ (Ω 𝓤)
Ω-compact∙ {𝓤} fe pe p = γ
  where
    A = Σ x₀ ꞉ Ω 𝓤 , (p x₀ ≡ ₁ → (x : Ω 𝓤) → p x ≡ ₁)

    a : p ⊥ ≡ ₀ → A
    a r = ⊥ , λ s → 𝟘-elim (zero-is-not-one (r ⁻¹ ∙ s))

    b : p ⊥ ≡ ₁ → A
    b r = ⊤ , ⊥-⊤-density fe pe p r

    γ : A
    γ = 𝟚-equality-cases a b

𝟙-compact∙ : compact∙ (𝟙 {𝓤})
𝟙-compact∙ p = ⋆ , f
 where
  f : (r : p ⋆ ≡ ₁) (x : 𝟙) → p x ≡ ₁
  f r ⋆ = r

\end{code}

In this module we prove some closure properties of compact
sets. Before doing this, we investigate their general nature.

We first show that the universal witness x₀ is a root of p if and
only if p has a root.

\begin{code}

_is-a-root-of_ : {X : 𝓤 ̇ } → X → (X → 𝟚) → 𝓤₀ ̇
x is-a-root-of p = p x ≡ ₀

_has-a-root : {X : 𝓤 ̇ } → (X → 𝟚) → 𝓤 ̇
p has-a-root = Σ x ꞉ domain p , x is-a-root-of p

putative-root : {X : 𝓤 ̇ }
              → compact∙ X
              → (p : X → 𝟚)
              → Σ x₀ ꞉ X , (p has-a-root ⇔ x₀ is-a-root-of p)
putative-root {𝓤} {X} ε p = x₀ , lemma₀ , lemma₁
 where
  x₀ : X
  x₀ = pr₁ (ε p)

  lemma : ¬ ((x : X) → p x ≡ ₁) → p x₀ ≡ ₀
  lemma = different-from-₁-equal-₀ ∘ contrapositive (pr₂ (ε p))

  lemma₀ : p has-a-root → x₀ is-a-root-of p
  lemma₀ (x , r) = lemma claim
   where
    claim : ¬ ((x : X) → p x ≡ ₁)
    claim f = equal-₁-different-from-₀ (f x) r

  lemma₁ : x₀ is-a-root-of p → p has-a-root
  lemma₁ h = x₀ , h

\end{code}

We now relate our definition to the original definition using
selection functions.

\begin{code}

_has-selection_ : (X : 𝓤 ̇ ) → ((X → 𝟚) → X) → 𝓤 ̇
X has-selection ε = (p : X → 𝟚) → p (ε p) ≡ ₁ → (x : X) → p x ≡ ₁

compact∙' : 𝓤 ̇ → 𝓤 ̇
compact∙' X = Σ ε ꞉ ((X → 𝟚) → X) , X has-selection ε

compact∙-gives-compact∙' : {X : 𝓤 ̇ } → compact∙ X → compact∙' X
compact∙-gives-compact∙' {𝓤} {X} ε' = ε , lemma
 where
  ε : (X → 𝟚) → X
  ε p = pr₁ (ε' p)

  lemma : (p : X → 𝟚) → p (ε p) ≡ ₁ → (x : X) → p x ≡ ₁
  lemma p = pr₂ (ε' p)

compact∙'-gives-compact∙ : {X : 𝓤 ̇ } → compact∙' X → compact∙ X
compact∙'-gives-compact∙ {𝓤} {X} ε p = x₀ , lemma
 where
  x₀ : X
  x₀ = pr₁ ε p

  lemma : p x₀ ≡ ₁ → (x : X) → p x ≡ ₁
  lemma u β = pr₂ ε p u β

\end{code}

Notice that Bishop's limited principle of omniscience LPO, which is a
constructive taboo, in Aczel's terminology, is the compactness of the
type ℕ. LPO is independent - it is not provable, and its negation is
not provable. In classical mathematics it is uncomfortable to have
independent propositions, but of course unavoidable. Independence
occurs often in constructive mathematics, particularly in classically
compatible constructive mathematics, like Bishop's methamatics and
Martin-Löf type theory (in its various flavours) - even the principle
of excluded middle is independent.

We'll see that the infinite set ℕ∞ defined in the module
ConvergentSequenceCompact is compact.

If a set X is compact∙ and a set Y has decidable equality, then the
function space (X → Y) has decidable equality, if we assume function
extensionality. In our topological correspondence, decidable equality
is called discreteness. More generally we have:

\begin{code}

apart-or-equal : funext 𝓤 𝓥
               → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
               → compact X
               → ((x : X) → is-discrete (Y x))
               → (f g : (x : X) → Y x)
               → (f ♯ g) + (f ≡ g)
apart-or-equal fe {X} {Y} φ d f g = lemma₂ lemma₁
 where
  claim : (x : X) → (f x ≢ g x) + (f x ≡ g x)
  claim x = +-commutative (d x (f x) (g x))

  lemma₀ : Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ≡ ₀ → f x ≢ g x)
                         × (p x ≡ ₁ → f x ≡ g x))
  lemma₀ = indicator claim

  p : X → 𝟚
  p = pr₁ lemma₀

  lemma₁ : (Σ x ꞉ X , p x ≡ ₀) + (Π x ꞉ X , p x ≡ ₁)
  lemma₁ = φ p

  lemma₂ : (Σ x ꞉ X , p x ≡ ₀) + (Π x ꞉ X , p x ≡ ₁) → (f ♯ g) + (f ≡ g)
  lemma₂ (inl (x , r)) = inl (x , (pr₁ (pr₂ lemma₀ x) r))
  lemma₂ (inr h) = inr (dfunext fe (λ x → pr₂ (pr₂ lemma₀ x) (h x)))

compact-discrete-discrete : funext 𝓤 𝓥
                          → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                          → compact X
                          → ((x : X) → is-discrete (Y x))
                          → is-discrete ((x : X) → Y x)

compact-discrete-discrete fe φ d f g = h (apart-or-equal fe φ d f g)
 where
  h : (f ♯ g) + (f ≡ g) → (f ≡ g) + (f ≢ g)
  h (inl a) = inr (apart-is-different a)
  h (inr r) = inl r

compact-discrete-discrete' : funext 𝓤 𝓥
                           → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                           → compact X
                           → is-discrete Y
                           → is-discrete (X → Y)
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
  g : decidable X → (Σ x ꞉ X , p x ≡ ₀) + (Π x ꞉ X , p x ≡ ₁)
  g (inl x) = 𝟚-equality-cases b c
   where
    b : p x ≡ ₀ → (Σ x ꞉ X , p x ≡ ₀) + (Π x ꞉ X , p x ≡ ₁)
    b r = inl (x , r)

    c : p x ≡ ₁ → (Σ x ꞉ X , p x ≡ ₀) + (Π x ꞉ X , p x ≡ ₁)
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

  quant-prod : {X : 𝓤 ̇ } {Y : X → 𝓤 ̇ }
             → quantifier X
             → ((x : X)  → quantifier (Y x))
             → quantifier (Σ Y)
  quant-prod φ γ p = φ (λ x → γ x (λ y → p (x , y)))

  selection : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
  selection X = (X → R) → X

  sel-prod : {X : 𝓤 ̇ } {Y : X → 𝓤 ̇ }
           → selection X
           → ((x : X) → selection (Y x))
           → selection (Σ Y)
  sel-prod {X} {Y} ε δ p = (x₀ , y₀)
    where
     next : (x : X) → Y x
     next x = δ x (λ y → p (x , y))

     x₀ : X
     x₀ = ε (λ x → p (x , next x))

     y₀ : Y x₀
     y₀ = next x₀

\end{code}

 Alternative, equivalent, construction:

\begin{code}

  overline : {X : 𝓤 ̇ } → selection X → quantifier X
  overline ε p = p (ε p)

  sel-prod' : {X : 𝓤 ̇ } {Y : X → 𝓤 ̇ }
            → selection X
            → ((x : X) → selection (Y x))
            → selection (Σ Y)
  sel-prod' {X} {Y} ε δ p = (x₀ , y₀)
   where
    x₀ : X
    x₀ = ε (λ x → overline (δ x) (λ y → p (x , y)))

    y₀ : Y x₀
    y₀ = δ x₀ (λ y → p (x₀ , y))

\end{code}

Back to compact sets:

\begin{code}

Σ-compact∙ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
           → compact∙ X
           → ((x : X) → compact∙ (Y x))
           → compact∙ (Σ Y)
Σ-compact∙ {i} {j} {X} {Y} ε δ p = (x₀ , y₀) , correctness
 where
  lemma-next : (x : X) → Σ y₀ ꞉ Y x , (p (x , y₀) ≡ ₁ → (y : Y x) → p (x , y) ≡ ₁)
  lemma-next x = δ x (λ y → p (x , y))

  next : (x : X) → Y x
  next x = pr₁ (lemma-next x)

  next-correctness : (x : X) → p (x , next x) ≡ ₁ → (y : Y x) → p (x , y) ≡ ₁
  next-correctness x = pr₂ (lemma-next x)

  lemma-first : Σ x₀ ꞉ X , (p (x₀ , next x₀) ≡ ₁ → (x : X) → p (x , next x) ≡ ₁)
  lemma-first = ε (λ x → p (x , next x))

  x₀ : X
  x₀ = pr₁ lemma-first

  first-correctness : p (x₀ , next x₀) ≡ ₁ → (x : X) → p (x , next x) ≡ ₁
  first-correctness = pr₂ lemma-first

  y₀ : Y x₀
  y₀ = next x₀

  correctness : p (x₀ , y₀) ≡ ₁ → (t : (Σ x ꞉ X , Y x)) → p t ≡ ₁
  correctness r (x , y) = next-correctness x (first-correctness r x) y

\end{code}

Corollary: Binary products preserve compactness:

\begin{code}

binary-Tychonoff : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → compact∙ X → compact∙ Y → compact∙ (X × Y)
binary-Tychonoff ε δ = Σ-compact∙ ε (λ i → δ)

×-compact∙ = binary-Tychonoff

+'-compact∙ : {X₀ X₁ : 𝓤 ̇ }
            → compact∙ X₀
            → compact∙ X₁
            → compact∙ (X₀ +' X₁)
+'-compact∙ {𝓤} {X₀} {X₁} ε₀ ε₁ = Σ-compact∙ 𝟚-compact∙ ε
 where
  ε : (i : 𝟚) → _
  ε ₀ = ε₀
  ε ₁ = ε₁

retractions-preserve-compactness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y}
                                 → has-section' f
                                 → compact∙ X
                                 → compact∙ Y
retractions-preserve-compactness {i} {j} {X} {Y} {f} f-retract ε q = y₀ , h
  where
   p : X → 𝟚
   p x = q (f x)

   x₀ : X
   x₀ = pr₁ (ε p)

   y₀ : Y
   y₀ = f x₀

   lemma : p x₀ ≡ ₁ → (x : X) → p x ≡ ₁
   lemma = pr₂ (ε p)

   h : q y₀ ≡ ₁ → (a : Y) → q a ≡ ₁
   h r a = fact₁ ⁻¹ ∙ fact₀
    where
     fact : Σ x ꞉ X , f x ≡ a
     fact = f-retract a

     x : X
     x = pr₁ fact

     fact₀ : q (f x) ≡ ₁
     fact₀ = lemma r x

     fact₁ : q (f x) ≡ q a
     fact₁ = ap q (pr₂ fact)

retract-compact∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → retract Y Of X
                 → compact∙ X
                 → compact∙ Y
retract-compact∙ (_ , φ) = retractions-preserve-compactness φ

+-compact∙ : {X₀ X₁ : 𝓤 ̇ }
            → compact∙ X₀
            → compact∙ X₁
            → compact∙ (X₀ + X₁)
+-compact∙ {𝓤} {X₀} {X₁} ε₀ ε₁ = retract-compact∙
                                   (retract-of-gives-retract-Of +-retract-of-+')
                                   (+'-compact∙ ε₀ ε₁)

𝟙+𝟙-compact∙ : compact∙ (𝟙 {𝓤} + 𝟙 {𝓥})
𝟙+𝟙-compact∙ = retract-compact∙ (f , r) 𝟚-compact∙
 where
  f : 𝟚 → 𝟙 + 𝟙
  f = 𝟚-cases (inl ⋆) (inr ⋆)

  r : (y : 𝟙 + 𝟙) → Σ x ꞉ 𝟚 , f x ≡ y
  r (inl ⋆) = ₀ , refl
  r (inr ⋆) = ₁ , refl

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
                     → is-surjection f
                     → compact∙ X
                     → compact∙ Y
 surjection-compact∙ {𝓤} {𝓥} {X} {Y} f i ε q = (y₀ , h)
  where
   p : X → 𝟚
   p = q ∘ f

   x₀ : X
   x₀ = pr₁ (ε p)

   g : q (f x₀) ≡ ₁ → (x : X) → q (f x) ≡ ₁
   g = pr₂ (ε p)

   y₀ : Y
   y₀ = f x₀

   isp : (y : Y) → is-prop (q y ≡ ₁)
   isp y = 𝟚-is-set

   h : q y₀ ≡ ₁ → (y : Y) → q y ≡ ₁
   h r = surjection-induction f i (λ y → q y ≡ ₁) isp (g r)

 image-compact∙ : {X Y : 𝓤₀ ̇ } (f : X → Y)
                → compact∙ X
                → compact∙ (image f)
 image-compact∙ f = surjection-compact∙
                     (corestriction f)
                     (corestriction-is-surjection f)

\end{code}

TODO. The following old code from 2011 seems to repeat some of the
above. We should deal with this.

\begin{code}

wcompact : 𝓤 ̇ → 𝓤 ̇
wcompact X = (p : X → 𝟚) → Σ y ꞉ 𝟚 , (y ≡ ₁ ⇔ ((x : X) → p x ≡ ₁))

\end{code}

Closer to the original definition of exhaustibility in LICS'2007 amd LMCS'2008:

\begin{code}

wcompact' : 𝓤 ̇ → 𝓤 ̇
wcompact' X = Σ A ꞉ ((X → 𝟚) → 𝟚) , ((p : X → 𝟚) → A p ≡ ₁ ⇔ ((x : X) → p x ≡ ₁))

\end{code}

Because the Curry-Howard interpretation of the axiom of choice holds
in MLTT:

\begin{code}

wcompact-implies-wcompact' : {X : 𝓤 ̇ } → wcompact X → wcompact' X
wcompact-implies-wcompact' {𝓤} {X} φ = A , lemma
 where
  A : (X → 𝟚) → 𝟚
  A p = pr₁ (φ p)

  lemma : (p : X → 𝟚) → A p ≡ ₁ ⇔ ((x : X) → p x ≡ ₁)
  lemma p = pr₂ (φ p)

compact-gives-wcompact : {X : 𝓤 ̇ } → compact∙ X → wcompact X
compact-gives-wcompact {𝓤} {X} ε p = y , (lemma₀ , lemma₁)
 where
  x₀ : X
  x₀ = pr₁ (ε p)

  y : 𝟚
  y = p x₀

  lemma₀ :  y ≡ ₁ → (x : X) → p x ≡ ₁
  lemma₀ = pr₂ (ε p)

  lemma₁ : ((x : X) → p x ≡ ₁) → y ≡ ₁
  lemma₁ h = h x₀

\end{code}

Added 8th November - December 2019. I think the following equivalent
notion of compactness is easier to deal with, and I wish I had used it
in the original development:

\begin{code}

Σ-Compact : 𝓤 ̇ → {𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
Σ-Compact {𝓤} X {𝓥} = (A : X → 𝓥 ̇ ) → detachable A → decidable (Σ A)

Compact = Σ-Compact

Compactness-gives-Markov : {X : 𝓤 ̇ }
                         → Compact X

                         → (A : X → 𝓥 ̇ )
                         → detachable A
                         → ¬¬ Σ A
                         → Σ A
Compactness-gives-Markov {𝓤} {X} c A δ φ = γ (c A δ)
 where
  γ : decidable (Σ A) → Σ A
  γ (inl σ) = σ
  γ (inr u) = 𝟘-elim (φ u)

compact-gives-Compact : {X : 𝓤 ̇ } → compact X → Compact X {𝓥}
compact-gives-Compact {𝓤} {𝓥} {X} c A d = iii
 where
  i : Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ≡ ₀ → A x) × (p x ≡ ₁ → ¬ (A x)))
  i = characteristic-function d

  p : X → 𝟚
  p = pr₁ i

  ii : (Σ x ꞉ X , p x ≡ ₀) + (Π x ꞉ X , p x ≡ ₁) → decidable (Σ A)
  ii (inl (x , r)) = inl (x , pr₁ (pr₂ i x) r)
  ii (inr u)       = inr φ
   where
    φ : ¬ Σ A
    φ (x , a) = pr₂ (pr₂ i x) (u x) a

  iii : decidable (Σ A)
  iii = ii (c p)

Compact-gives-compact : {X : 𝓤 ̇ } → Σ-Compact X → Σ-compact X
Compact-gives-compact {𝓤} {X} C p = iv
 where
  A : X → 𝓤₀ ̇
  A x = p x ≡ ₀

  i : detachable (λ x → p x ≡ ₀) → decidable (Σ x ꞉ X , p x ≡ ₀)
  i = C A

  ii : detachable (λ x → p x ≡ ₀)
  ii x = 𝟚-is-discrete (p x) ₀

  iii : decidable (Σ x ꞉ X , p x ≡ ₀) → (Σ x ꞉ X , p x ≡ ₀) + (Π x ꞉ X , p x ≡ ₁)
  iii (inl σ) = inl σ
  iii (inr u) = inr (λ x → different-from-₀-equal-₁ (λ r → u (x , r)))

  iv : (Σ x ꞉ X , p x ≡ ₀) + (Π x ꞉ X , p x ≡ ₁)
  iv = iii (i ii)

Compact-resizeup : {X : 𝓤 ̇ } → Σ-Compact X {𝓤₀} → Σ-Compact X {𝓥}
Compact-resizeup C = compact-gives-Compact (Compact-gives-compact C)

\end{code}

TODO. Prove the converse of the previous observation, using the fact
that any decidable proposition is logically equivalent to either 𝟘 or
𝟙, and hence to a type in the universe 𝓤₀.

\begin{code}

Π-Compact : 𝓤 ̇ → {𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
Π-Compact {𝓤} X {𝓥} = (A : X → 𝓥 ̇ ) → detachable A → decidable (Π A)

Σ-Compact-gives-Π-Compact : (X : 𝓤 ̇ ) → Σ-Compact X {𝓥} → Π-Compact X {𝓥}
Σ-Compact-gives-Π-Compact X C A d = γ (C (λ x → ¬ (A x)) e)
 where
  e : detachable (λ x → ¬ (A x))
  e x = ¬-preserves-decidability (d x)

  γ : decidable (Σ x ꞉ X , ¬ (A x)) → decidable (Π x ꞉ X , A x)
  γ (inl (x , v)) = inr (λ φ → v (φ x))
  γ (inr u)       = inl (λ x → ¬¬-elim (d x) (λ n → u (x , n)))

𝟘-Compact : Compact (𝟘 {𝓤}) {𝓥}
𝟘-Compact A δ = inr (λ (σ : Σ A) → 𝟘-elim (pr₁ σ))

𝟙-Compact : Compact (𝟙 {𝓤}) {𝓥}
𝟙-Compact A δ = γ (δ ⋆)
 where
  γ : A ⋆ + ¬ A ⋆ → decidable (Σ A)
  γ (inl a) = inl (⋆ , a)
  γ (inr u) = inr (λ {(⋆ , a) → u a})

+-Compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
          → Compact X {𝓦} → Compact Y {𝓦} → Compact (X + Y) {𝓦}
+-Compact c d A δ = γ (c (A ∘ inl) (δ ∘ inl)) (d (A ∘ inr) (δ ∘ inr))
 where
  γ : decidable (Σ (A ∘ inl)) → decidable (Σ (A ∘ inr)) → decidable (Σ A)
  γ (inl (x , a)) _            = inl (inl x , a)
  γ (inr _)      (inl (y , a)) = inl (inr y , a)
  γ (inr u)      (inr v)       = inr w
   where
    w : ¬ Σ A
    w (inl x , a) = u (x , a)
    w (inr y , a) = v (y , a)

Σ-preserves-Compactness : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                        → Compact X {𝓥 ⊔ 𝓦}
                        → ((x : X) → Compact (Y x) {𝓦})
                        → Compact (Σ Y) {𝓦}
Σ-preserves-Compactness {𝓤} {𝓥} {𝓦} {X} {Y} c d A δ = γ e
 where
  B : X → 𝓥 ⊔ 𝓦 ̇
  B x = Σ y ꞉ Y x , A (x , y)

  ζ : (x : X) → detachable (λ y → A (x , y))
  ζ x y = δ (x , y)

  ε : detachable B
  ε x = d x (λ y → A (x , y)) (ζ x)

  e : decidable (Σ B)
  e = c B ε

  γ : decidable (Σ B) → decidable (Σ A)
  γ (inl (x , (y , a))) = inl ((x , y) , a)
  γ (inr u)             = inr (λ {((x , y) , a) → u (x , (y , a))})

\end{code}

TODO. A direct proof of the following would give more general universe
assignments:

\begin{code}

×-Compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
          → Compact X {𝓥 ⊔ 𝓦} → Compact Y {𝓦} → Compact (X × Y) {𝓦}
×-Compact c d = Σ-preserves-Compactness c (λ x → d)


Compact-closed-under-retracts : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                              → retract Y of X
                              → Compact X {𝓦}
                              → Compact Y {𝓦}
Compact-closed-under-retracts {𝓤} {𝓥} {𝓦} {X} {Y} (r , s , η) c A δ = γ (c B ε)
 where
  B : X → 𝓦 ̇
  B = A ∘ r

  ε : detachable B
  ε = δ ∘ r

  γ : decidable (Σ B) → decidable (Σ A)
  γ (inl (x , a)) = inl (r x , a)
  γ (inr u)       = inr (λ (y , a) → u (s y , transport A ((η y)⁻¹) a))

Compact-closed-under-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                       → X ≃ Y
                       → Compact X {𝓦}
                       → Compact Y {𝓦}
Compact-closed-under-≃ e = Compact-closed-under-retracts (≃-gives-▷ e)

module CompactTypesPT (pt : propositional-truncations-exist) where

 open ImageAndSurjection pt

 surjection-Compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → funext 𝓥 𝓤₀
                    → is-surjection f
                    → Compact X {𝓥}
                    → Compact Y {𝓥}
 surjection-Compact {𝓤} {𝓥} {X} {Y} f fe i c A δ = γ (c B ε)
  where
   B : X → 𝓥 ̇
   B = A ∘ f

   ε : detachable B
   ε = δ ∘ f

   γ : decidable (Σ B) → decidable (Σ A)
   γ (inl (x , a)) = inl (f x , a)
   γ (inr u)       = inr v
    where
     u' : (x : X) → ¬ A (f x)
     u' x a = u (x , a)

     v' : (y : Y) → ¬ A y
     v' = surjection-induction f i (λ y → ¬ A y) (λ y → negations-are-props fe) u'

     v : ¬ Σ A
     v (y , a) = v' y a

 image-Compact : funext (𝓤 ⊔ 𝓥) 𝓤₀
               → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
               → Compact X {𝓤 ⊔ 𝓥}
               → Compact (image f) {𝓤 ⊔ 𝓥}
 image-Compact fe f c = surjection-Compact (corestriction f) fe
                         (corestriction-is-surjection f) c


 open PropositionalTruncation pt

 ∃-Compact : 𝓤 ̇ → {𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
 ∃-Compact {𝓤} X {𝓥} = (A : X → 𝓥 ̇ ) → detachable A → decidable (∃ A)

 Compactness-gives-∃-Compactness : {X : 𝓤 ̇ } → Compact X {𝓥} → ∃-Compact X {𝓥}
 Compactness-gives-∃-Compactness {𝓤} {X} c A δ = γ (c A δ)
  where
   γ : decidable (Σ A) → decidable (∃ A)
   γ (inl σ) = inl ∣ σ ∣
   γ (inr u) = inr (empty-is-uninhabited u)


 ∃-Compactness-is-prop : Fun-Ext → {X : 𝓤 ̇ } → is-prop (∃-Compact X {𝓥})
 ∃-Compactness-is-prop {𝓤} {𝓥} fe {X} = Π₂-is-prop fe
                                          (λ A δ → decidability-of-prop-is-prop fe
                                                     ∥∥-is-prop)


 ∃-Compactness-gives-Markov : {X : 𝓤 ̇ }
                            → ∃-Compact X {𝓥}
                            → (A : X → 𝓥 ̇ )
                            → detachable A
                            → ¬¬ ∃ A
                            → ∃ A
 ∃-Compactness-gives-Markov {𝓤} {𝓥} {X} c A δ = ¬¬-elim (c A δ)

 ∥Compact∥-gives-∃-Compact : Fun-Ext → {X : 𝓤 ̇ } → ∥ Compact X {𝓥} ∥ → ∃-Compact X {𝓥}
 ∥Compact∥-gives-∃-Compact fe = ∥∥-rec (∃-Compactness-is-prop fe)
                                     Compactness-gives-∃-Compactness

 ∃-Compact-propositions-are-decidable : {P : 𝓤 ̇ }
                                      → is-prop P
                                      → ∃-Compact P
                                      → decidable P
 ∃-Compact-propositions-are-decidable {𝓤} {P} i κ = γ β
  where
   A : P → 𝓤 ̇
   A p = 𝟙

   α : detachable A
   α p = inl ⋆

   β : decidable (∃ p ꞉ P , A p)
   β = κ A α

   γ : type-of β → decidable P
   γ (inl e) = inl (∥∥-rec i pr₁ e)
   γ (inr ν) = inr (contrapositive (λ p → ∣ p , ⋆ ∣) ν)

\end{code}

Variation:

\begin{code}

 ∃-Compact-propositions-are-decidable' : {P : 𝓤 ̇ }
                                      → is-prop P
                                      → ∃-Compact (P + 𝟙 {𝓥})
                                      → decidable P
 ∃-Compact-propositions-are-decidable' {𝓤} {𝓥} {P} i κ = γ β
  where
   A : P + 𝟙 → 𝓤 ̇
   A (inl p) = 𝟙
   A (inr ⋆) = 𝟘

   α : detachable A
   α (inl p) = inl ⋆
   α (inr ⋆) = inr (λ z → 𝟘-elim z)

   β : decidable (∃ x ꞉ P + 𝟙 , A x)
   β = κ A α

   δ : Σ A → P
   δ (inl p , ⋆) = p
   δ (inr ⋆ , a) = 𝟘-elim a

   ϕ : P → ∃ A
   ϕ p = ∣ inl p , ⋆ ∣

   γ : type-of β → decidable P
   γ (inl e) = inl (∥∥-rec i δ e)
   γ (inr ν) = inr (contrapositive ϕ ν)

\end{code}

Added 10th December 2019.

\begin{code}

Compact∙ : 𝓤 ̇ → {𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
Compact∙ {𝓤} X {𝓥} = (A : X → 𝓥 ̇ ) → detachable A → Σ x₀ ꞉ X , (A x₀ → (x : X) → A x)

Compact-pointed-gives-Compact∙ : {X : 𝓤 ̇ } → Compact X {𝓥} → X → Compact∙ X {𝓥}
Compact-pointed-gives-Compact∙ {𝓤} {𝓥} {X} c x₀ A δ = γ (c A' δ')
 where
  A' : X → 𝓥 ̇
  A' x = ¬ A x

  δ' : detachable A'
  δ' x = ¬-preserves-decidability (δ x)

  γ : decidable (Σ A') → Σ x₀ ꞉ X , (A x₀ → (x : X) → A x)
  γ (inl (x , u)) = x  , (λ (a : A x) → 𝟘-elim (u a))
  γ (inr v)       = x₀ , (λ (a : A x₀) (x : X) → ¬¬-elim (δ x) λ (φ : ¬ A x) → v (x , φ))


Compact∙-gives-Compact : {X : 𝓤 ̇ } → Compact∙ X {𝓥} → Compact X {𝓥}
Compact∙-gives-Compact {𝓤} {𝓥} {X} ε A δ = γ (δ x₀)
 where
  l : Σ x₀ ꞉ X , (¬ A x₀ → (x : X) → ¬ A x)
  l = ε (λ x → ¬ A x) (λ x → ¬-preserves-decidability (δ x))

  x₀ : X
  x₀ = pr₁ l

  i : ¬ A x₀ → ¬ Σ A
  i u (x , a) = pr₂ l u x a

  γ : decidable (A x₀) → decidable (Σ A)
  γ (inl a) = inl (x₀ , a)
  γ (inr u) = inr (i u)

Compact∙-gives-pointed : {X : 𝓤 ̇ } → Compact∙ X {𝓥} → X
Compact∙-gives-pointed ε = pr₁ (ε (λ x → 𝟘) (λ x → 𝟘-decidable))

\end{code}

Based on what was done in the module WeaklyCompactTypes before:

\begin{code}

Compact-types-are-decidable : (X : 𝓤 ̇ ) → Compact X → decidable X
Compact-types-are-decidable X c = γ
 where
  A : X → 𝓤₀ ̇
  A _ = 𝟙

  δ : detachable A
  δ _ = inl ⋆

  a : decidable (X × 𝟙)
  a = c A δ

  f : decidable (X × 𝟙) → decidable X
  f (inl (x , ⋆)) = inl x
  f (inr ν)       = inr (contrapositive (λ x → (x , ⋆)) ν)

  γ : decidable X
  γ = f a

discrete-to-the-power-Compact-is-discrete : funext 𝓤 𝓥
                                          → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                          → Π-Compact X
                                          → is-discrete Y
                                          → is-discrete (X → Y)
discrete-to-the-power-Compact-is-discrete {𝓤} {𝓥} fe {X} {Y} c d f g = γ
 where
  A : X → 𝓥 ̇
  A x = f x ≡ g x

  a : (x : X) → decidable (A x)
  a x = d (f x) (g x)

  b : decidable (Π A)
  b = c A a

  φ : decidable (Π A) → decidable (f ≡ g)
  φ (inl α) = inl (dfunext fe α)
  φ (inr ν) = inr (contrapositive happly ν)

  γ : decidable (f ≡ g)
  γ = φ b

open import TotallySeparated

compact-power-of-𝟚-has-discrete-exponent : {X : 𝓤 ̇ }
                                         → is-totally-separated X
                                         → Π-Compact (X → 𝟚)
                                         → is-discrete X
compact-power-of-𝟚-has-discrete-exponent {𝓤} {X} τ κ x y = γ δ
 where
  d : (p : X → 𝟚) → decidable (p x ≡ p y)
  d p = 𝟚-is-discrete (p x) (p y)

  δ : decidable ((p : X → 𝟚) → p x ≡ p y)
  δ = κ (λ p → p x ≡ p y) d

  α : x ≡ y → (p : X → 𝟚) → p x ≡ p y
  α e p = ap p e

  β : ¬ ((p : X → 𝟚) → p x ≡ p y) → ¬ (x ≡ y)
  β = contrapositive α

  γ : type-of δ → decidable (x ≡ y)
  γ (inl α) = inl (τ α)
  γ (inr u) = inr (β u)

\end{code}

Added 21st October 2021.

\begin{code}

complemented-subset-of-compact-type : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                                    → Compact X {𝓥 ⊔ 𝓦}
                                    → detachable A
                                    → ((x : X) → is-prop (A x))
                                    → Compact (Σ x ꞉ X , A x) {𝓦}
complemented-subset-of-compact-type {𝓤} {𝓥} {𝓦} {X} {A}
                                    X-compact
                                    A-detachable
                                    A-is-prop-valued
                                    B B-detachable = γ II
 where
  I : (x : X) → decidable (Σ a ꞉ A x , B (x , a))
  I x = Cases (A-detachable x)
         (λ (a : A x)
               → Cases (B-detachable (x , a))
                  (λ (b : B (x , a))     → inl (a , b))
                  (λ ν → inr (λ (a' , b) → ν (transport
                                               (λ - → B (x , -))
                                               (A-is-prop-valued x a' a)
                                               b))))
         (λ ν → inr (λ (a , b) → ν a))

  II : decidable (Σ x ꞉ X , Σ a ꞉ A x , B (x , a))
  II = X-compact (λ x → Σ a ꞉ A x , B (x , a)) I

  γ : type-of II → decidable (Σ y ꞉ (Σ x ꞉ X , A x) , B y)
  γ (inl (x , (a , b))) = inl ((x , a) , b)
  γ (inr ν)             = inr (λ ((x , a) , b) → ν (x , (a , b)))

\end{code}

Added 10th January 2022. (Is this somewhere already?)

\begin{code}

compact-gives-Σ+Π : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
                  → compact X
                  → (q : (x : X) → A x + B x)
                  → (Σ x ꞉ X , A x) + (Π x ꞉ X , B x)
compact-gives-Σ+Π X A B κ q = III II
 where
  p : X → 𝟚
  p = pr₁ (indicator q)

  I : (x : X) → (p x ≡ ₀ → A x) × (p x ≡ ₁ → B x)
  I = pr₂ (indicator q)

  II : (Σ x ꞉ X , p x ≡ ₀) + (Π x ꞉ X , p x ≡ ₁)
  II = κ p

  III : type-of II → (Σ x ꞉ X , A x) + (Π x ꞉ X , B x)
  III (inl (x , e)) = inl (x , pr₁ (I x) e)
  III (inr ϕ)       = inr (λ x → pr₂ (I x) (ϕ x))

\end{code}

Added 26th April 2022. All types are compact iff global choice holds:

\begin{code}

open import UF-ExcludedMiddle

all-types-compact-gives-global-choice : ((X : 𝓤 ̇ ) → Compact X {𝓤})
                                      → Global-Choice 𝓤
all-types-compact-gives-global-choice {𝓤} α X =
 Cases (α X (λ _ → 𝟙 {𝓤}) (λ x → 𝟙-decidable))
   (λ (x , _) → inl x)
   (λ ν       → inr (λ x → ν (x , ⋆)))

global-choice-gives-all-types-compact : Global-Choice 𝓤
                                      → ((X : 𝓤 ̇ ) → Compact X {𝓤})
global-choice-gives-all-types-compact gc X A δ = gc (Σ A)


\end{code}
