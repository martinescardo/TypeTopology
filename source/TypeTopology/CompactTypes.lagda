Martin Escardo 2011, reorganized and expanded 2018,2019.

Compact types. We shall call a type compact if it is exhaustibly
searchable. But there are many closely related, but different, notions
of searchability, and we investigate this phenomenon in this module
and the module WeaklyCompactTypes.

Perhaps surprisingly, there are infinite searchable sets, such as ℕ∞
(see the module GenericConvergentSequenceCompactness).

It is in general not possible to decide constructively the statement

  Σ x ꞉ X , p x ＝ ₀

that a given function p : X → 𝟚 defined on a type X has a root.

We say that a type X is Σ-compact, or simply compact for short, if
this statement is decidable for every p : X → 𝟚. This is equivalent to

  Π p ꞉ X → 𝟚 , (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁).

We can also ask whether the statements

  ∃ x : X , p x ＝ ₀   and   Π x ꞉ X , p x ＝ ₀

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

{-# OPTIONS --safe --without-K #-}

module TypeTopology.CompactTypes where

open import MLTT.AlternativePlus
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import MLTT.Two-Properties
open import NotionsOfDecidability.Complemented
open import NotionsOfDecidability.Decidable
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

\end{code}

We say that a type is compact if for every 𝟚-valued function defined
on it, it decidable whether it has a root:

\begin{code}

is-Σ-compact : 𝓤 ̇ → 𝓤 ̇
is-Σ-compact X = (p : X → 𝟚) → (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁)

is-compact  = is-Σ-compact

\end{code}

Notice that compactness in this sense is not in general a univalent
proposition (subsingleton). Weaker notions, ∃-compactness and
Π-compactness, that are always propositions are defined and studied in
the module WeaklyCompactTypes.

The following notion is logically equivalent to the conjunction of
compactness and pointedness, and hence the notation "compact∙":

\begin{code}

is-compact∙ : 𝓤 ̇ → 𝓤 ̇
is-compact∙ X = (p : X → 𝟚) → Σ x₀ ꞉ X , (p x₀ ＝ ₁ → (x : X) → p x ＝ ₁)

universal-witness : {X : 𝓤 ̇ } → is-compact∙ X → (X → 𝟚) → X
universal-witness ε p = pr₁ (ε p)

witness-universality : {X : 𝓤 ̇ }
                       (ε : is-compact∙ X)
                       (p : X → 𝟚)
                     → p (universal-witness ε p) ＝ ₁ → (x : X) → p x ＝ ₁
witness-universality ε p = pr₂ (ε p)

\end{code}

Terminology: we call x₀ the universal witness.

\begin{code}

compact-pointed-types-are-compact∙ : {X : 𝓤 ̇ } → is-compact X → X → is-compact∙ X
compact-pointed-types-are-compact∙ {𝓤} {X} φ x₀ p = γ (φ p)
 where
  γ : (Σ x ꞉ X , p x ＝ ₀) + ((x : X) → p x ＝ ₁)
    → Σ x₀ ꞉ X , (p x₀ ＝ ₁ → (x : X) → p x ＝ ₁)
  γ (inl (x , r)) = x , (λ s → 𝟘-elim (equal-₀-different-from-₁ r s))
  γ (inr f)       = x₀ , (λ r → f)

compact∙-types-are-compact : {X : 𝓤 ̇ } → is-compact∙ X → is-compact X
compact∙-types-are-compact {𝓤} {X} ε p = 𝟚-equality-cases case₀ case₁
 where
  x₀ : X
  x₀ = universal-witness ε p

  case₀ : p x₀ ＝ ₀ → (Σ x ꞉ X , p x ＝ ₀) + ((x : X) → p x ＝ ₁)
  case₀ r = inl (x₀ , r)

  case₁ : p x₀ ＝ ₁ → (Σ x ꞉ X , p x ＝ ₀) + ((x : X) → p x ＝ ₁)
  case₁ r = inr (witness-universality ε p r)

compact∙-types-are-pointed : {X : 𝓤 ̇ } → is-compact∙ X → X
compact∙-types-are-pointed ε = universal-witness ε (λ x → ₀)

\end{code}

There are examples where pointedness is crucial. For instance, the
product of a family of compact-pointed types indexed by a subsingleton
is always compact (pointed), but the assumption that this holds
without the assumption of pointedness implies weak excluded middle
(the negation of any proposition is decidable).

For example, every finite set is compact, and in particular the set 𝟚
of binary digits ₀ and ₁ is compact. To find x₀ : 𝟚 such that

   (†) p x₀ ＝ ₁ → ∀ (x : X) → p x ＝ ₁,

we can check whether p ₀ ＝ ₁ and p ₁ ＝ ₁.

     If this is the case, then ∀ (x : X) → p x ＝ ₁ holds, which is
     the conclusion the implication (†), and hence we can take any
     x₀ : 𝟚 to make (†) hold.

     Otherwise, we can take any x₀ such that p x₀ ＝ ₀ so that the
     implication (†) holds vacuously.

That is, either the conclusion ∀ (x : X) → p x ＝ ₁ of (†) holds, or
its premise p x₀ ＝ ₁ fails for suitable x₀.

However, there is a more direct proof: we claim that, without
checking the two possibilities, we can always take x₀ = p ₀.
(Cf. Section 8.1 of the LMCS'2008 paper.)

\begin{code}

𝟚-is-compact∙ : is-compact∙ 𝟚
𝟚-is-compact∙ p = x₀ , (λ r → 𝟚-induction (lemma₀ r) (lemma₁ r))
 where
  x₀ : 𝟚
  x₀ = p ₀

  claim : p x₀ ＝ ₁ → p ₀ ＝ ₀ → p ₀ ＝ ₁
  claim r s = transport (λ - → p - ＝ ₁) s r

  lemma₀ : p x₀ ＝ ₁ → p ₀ ＝ ₁
  lemma₀ r = 𝟚-equality-cases (claim r) (λ s → s)

  lemma₁ : p x₀ ＝ ₁ → p ₁ ＝ ₁
  lemma₁ r = transport (λ - → p - ＝ ₁) (lemma₀ r) r

𝟚-is-compact : is-compact 𝟚
𝟚-is-compact = compact∙-types-are-compact 𝟚-is-compact∙

\end{code}

Even though excluded middle is undecided, the set Ω 𝓤 of univalent
propositions in any universe 𝓤 is compact, assuming functional and
propositional extensionality, which are consequences of univalence:

\begin{code}

Ω-is-compact∙ : funext 𝓤 𝓤 → propext 𝓤 → is-compact∙ (Ω 𝓤)
Ω-is-compact∙ {𝓤} fe pe p = γ
  where
   A = Σ x₀ ꞉ Ω 𝓤 , (p x₀ ＝ ₁ → (x : Ω 𝓤) → p x ＝ ₁)

   a : p ⊥ ＝ ₀ → A
   a r = ⊥ , λ s → 𝟘-elim (zero-is-not-one (r ⁻¹ ∙ s))

   b : p ⊥ ＝ ₁ → A
   b r = ⊤ , ⊥-⊤-density fe pe p r

   γ : A
   γ = 𝟚-equality-cases a b

𝟙-is-compact∙ : is-compact∙ (𝟙 {𝓤})
𝟙-is-compact∙ p = ⋆ , f
 where
  f : (r : p ⋆ ＝ ₁) (x : 𝟙) → p x ＝ ₁
  f r ⋆ = r

\end{code}

In this module we prove some closure properties of compact
sets. Before doing this, we investigate their general nature.

We first show that the universal witness x₀ is a root of p if and
only if p has a root.

\begin{code}

_is-a-root-of_ : {X : 𝓤 ̇ } → X → (X → 𝟚) → 𝓤₀ ̇
x is-a-root-of p = p x ＝ ₀

_has-a-root : {X : 𝓤 ̇ } → (X → 𝟚) → 𝓤 ̇
p has-a-root = Σ x ꞉ domain p , x is-a-root-of p

putative-root : {X : 𝓤 ̇ }
              → is-compact∙ X
              → (p : X → 𝟚)
              → Σ x₀ ꞉ X , (p has-a-root ↔ x₀ is-a-root-of p)
putative-root {𝓤} {X} ε p = x₀ , lemma₀ , lemma₁
 where
  x₀ : X
  x₀ = universal-witness ε p

  lemma : ¬ ((x : X) → p x ＝ ₁) → p x₀ ＝ ₀
  lemma = different-from-₁-equal-₀
        ∘ contrapositive (witness-universality ε p)

  lemma₀ : p has-a-root → x₀ is-a-root-of p
  lemma₀ (x , r) = lemma claim
   where
    claim : ¬ ((x : X) → p x ＝ ₁)
    claim f = equal-₁-different-from-₀ (f x) r

  lemma₁ : x₀ is-a-root-of p → p has-a-root
  lemma₁ h = x₀ , h

\end{code}

We now relate our definition to the original definition using
selection functions.

\begin{code}

_has-selection_ : (X : 𝓤 ̇ ) → ((X → 𝟚) → X) → 𝓤 ̇
X has-selection ε = (p : X → 𝟚) → p (ε p) ＝ ₁ → (x : X) → p x ＝ ₁

is-compact∙' : 𝓤 ̇ → 𝓤 ̇
is-compact∙' X = Σ ε ꞉ ((X → 𝟚) → X) , X has-selection ε

compact∙-types-are-compact∙' : {X : 𝓤 ̇ } → is-compact∙ X → is-compact∙' X
compact∙-types-are-compact∙' {𝓤} {X} ε' = universal-witness ε' ,
                                          witness-universality ε'

compact∙'-types-are-compact∙ : {X : 𝓤 ̇ } → is-compact∙' X → is-compact∙ X
compact∙'-types-are-compact∙ {𝓤} {X} ε p = x₀ , universality
 where
  x₀ : X
  x₀ = pr₁ ε p

  universality : p x₀ ＝ ₁ → (x : X) → p x ＝ ₁
  universality u β = pr₂ ε p u β

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
               → is-compact X
               → ((x : X) → is-discrete (Y x))
               → (f g : (x : X) → Y x)
               → (f ♯ g) + (f ＝ g)
apart-or-equal fe {X} {Y} φ d f g = lemma₂ lemma₁
 where
  claim : (x : X) → (f x ≠ g x) + (f x ＝ g x)
  claim x = +-commutative (d x (f x) (g x))

  lemma₀ : Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ＝ ₀ → f x ≠ g x)
                         × (p x ＝ ₁ → f x ＝ g x))
  lemma₀ = indicator claim

  p : X → 𝟚
  p = pr₁ lemma₀

  lemma₁ : (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁)
  lemma₁ = φ p

  lemma₂ : (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁)
         → (f ♯ g) + (f ＝ g)
  lemma₂ (inl (x , r)) = inl (x , (pr₁ (pr₂ lemma₀ x) r))
  lemma₂ (inr h)       = inr (dfunext fe (λ x → pr₂ (pr₂ lemma₀ x) (h x)))

discrete-to-power-compact-is-discrete : funext 𝓤 𝓥
                                      → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                                      → is-compact X
                                      → ((x : X) → is-discrete (Y x))
                                      → is-discrete ((x : X) → Y x)
discrete-to-power-compact-is-discrete fe φ d f g = h (apart-or-equal fe φ d f g)
 where
  h : (f ♯ g) + (f ＝ g) → (f ＝ g) + (f ≠ g)
  h (inl a) = inr (apart-is-different a)
  h (inr r) = inl r

discrete-to-power-compact-is-discrete' : funext 𝓤 𝓥
                                       → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                       → is-compact X
                                       → is-discrete Y
                                       → is-discrete (X → Y)
discrete-to-power-compact-is-discrete' fe φ d =
 discrete-to-power-compact-is-discrete fe φ (λ x → d)

𝟘-compact : is-compact (𝟘 {𝓤})
𝟘-compact {𝓤} p = inr (λ x → 𝟘-elim {𝓤₀} {𝓤} x)

compact-types-are-decidable : (X : 𝓤 ̇ ) → is-compact X → is-decidable X
compact-types-are-decidable X φ = f a
 where
  a : (X × (₀ ＝ ₀)) + (X → ₀ ＝ ₁)
  a = φ (λ x → ₀)

  f : (X × (₀ ＝ ₀)) + (X → ₀ ＝ ₁) → is-decidable X
  f (inl (x , _)) = inl x
  f (inr u)       = inr (λ x → zero-is-not-one (u x))

decidable-propositions-are-compact : (X : 𝓤 ̇ )
                                   → is-prop X
                                   → is-decidable X
                                   → is-compact X
decidable-propositions-are-compact X isp δ p = g δ
 where
  g : is-decidable X → (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁)
  g (inl x) = 𝟚-equality-cases b c
   where
    b : p x ＝ ₀ → (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁)
    b r = inl (x , r)

    c : p x ＝ ₁ → (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁)
    c r = inr (λ y → transport (λ - → p - ＝ ₁) (isp x y) r)
  g (inr u) = inr (λ x → 𝟘-elim (u x))

\end{code}

Some closure properties now.

As a warm-up, we discuss a construction on selection functions
(X → R) → X, and generalized quantifiers (X → R) → R, which we
generalize to get closure of compact types under Σ.

\begin{code}

module warm-up {𝓤} {𝓥} {R : 𝓥 ̇ } where

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

Σ-is-compact∙ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
              → is-compact∙ X
              → ((x : X) → is-compact∙ (Y x))
              → is-compact∙ (Σ Y)
Σ-is-compact∙ {i} {j} {X} {Y} ε δ p = (x₀ , y₀) , correctness
 where
  lemma-next : (x : X) → Σ y₀ ꞉ Y x , (p (x , y₀) ＝ ₁ → (y : Y x) → p (x , y) ＝ ₁)
  lemma-next x = δ x (λ y → p (x , y))

  next : (x : X) → Y x
  next x = pr₁ (lemma-next x)

  next-correctness : (x : X) → p (x , next x) ＝ ₁ → (y : Y x) → p (x , y) ＝ ₁
  next-correctness x = pr₂ (lemma-next x)

  lemma-first : Σ x₀ ꞉ X , (p (x₀ , next x₀) ＝ ₁ → (x : X) → p (x , next x) ＝ ₁)
  lemma-first = ε (λ x → p (x , next x))

  x₀ : X
  x₀ = pr₁ lemma-first

  first-correctness : p (x₀ , next x₀) ＝ ₁ → (x : X) → p (x , next x) ＝ ₁
  first-correctness = pr₂ lemma-first

  y₀ : Y x₀
  y₀ = next x₀

  correctness : p (x₀ , y₀) ＝ ₁ → (t : (Σ x ꞉ X , Y x)) → p t ＝ ₁
  correctness r (x , y) = next-correctness x (first-correctness r x) y

\end{code}

Corollary: Binary products preserve compactness:

\begin{code}

binary-Tychonoff : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → is-compact∙ X
                 → is-compact∙ Y
                 → is-compact∙ (X × Y)
binary-Tychonoff ε δ = Σ-is-compact∙ ε (λ i → δ)

×-is-compact∙ = binary-Tychonoff

+'-is-compact∙ : {X₀ X₁ : 𝓤 ̇ }
               → is-compact∙ X₀
               → is-compact∙ X₁
               → is-compact∙ (X₀ +' X₁)
+'-is-compact∙ {𝓤} {X₀} {X₁} ε₀ ε₁ = Σ-is-compact∙ 𝟚-is-compact∙ ε
 where
  ε : (i : 𝟚) → _
  ε ₀ = ε₀
  ε ₁ = ε₁

retractions-preserve-compactness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y}
                                 → has-section' f
                                 → is-compact∙ X
                                 → is-compact∙ Y
retractions-preserve-compactness {i} {j} {X} {Y} {f} f-retract ε q = y₀ , h
  where
   p : X → 𝟚
   p x = q (f x)

   x₀ : X
   x₀ = universal-witness ε p

   y₀ : Y
   y₀ = f x₀

   h : q y₀ ＝ ₁ → (a : Y) → q a ＝ ₁
   h r a = fact₁ ⁻¹ ∙ fact₀
    where
     fact : Σ x ꞉ X , f x ＝ a
     fact = f-retract a

     x : X
     x = pr₁ fact

     fact₀ : q (f x) ＝ ₁
     fact₀ = witness-universality ε p r x

     fact₁ : q (f x) ＝ q a
     fact₁ = ap q (pr₂ fact)

retract-is-compact∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    → retract Y Of X
                    → is-compact∙ X
                    → is-compact∙ Y
retract-is-compact∙ (_ , φ) = retractions-preserve-compactness φ

+-is-compact∙ : {X₀ X₁ : 𝓤 ̇ }
              → is-compact∙ X₀
              → is-compact∙ X₁
              → is-compact∙ (X₀ + X₁)
+-is-compact∙ {𝓤} {X₀} {X₁} ε₀ ε₁ =
 retract-is-compact∙
  (retract-of-gives-retract-Of +-retract-of-+')
  (+'-is-compact∙ ε₀ ε₁)

𝟙+𝟙-is-compact∙ : is-compact∙ (𝟙 {𝓤} + 𝟙 {𝓥})
𝟙+𝟙-is-compact∙ = retract-is-compact∙ (f , r) 𝟚-is-compact∙
 where
  f : 𝟚 → 𝟙 + 𝟙
  f = 𝟚-cases (inl ⋆) (inr ⋆)

  r : (y : 𝟙 + 𝟙) → Σ x ꞉ 𝟚 , f x ＝ y
  r (inl ⋆) = ₀ , refl
  r (inr ⋆) = ₁ , refl

compact∙-types-are-closed-under-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                      → X ≃ Y
                                      → is-compact∙ X
                                      → is-compact∙ Y
compact∙-types-are-closed-under-equiv (f , (g , fg) , (h , hf)) =
 retract-is-compact∙ (f , (λ y → g y , fg y))

singletons-are-compact∙ : {X : 𝓤 ̇ } → is-singleton X → is-compact∙ X
singletons-are-compact∙ {𝓤} {X} (x , φ) p = x , g
 where
  g : p x ＝ ₁ → (y : X) → p y ＝ ₁
  g r y = transport (λ - → p - ＝ ₁) (φ y) r

module _ (pt : propositional-truncations-exist) where

 open import UF.ImageAndSurjection pt

 codomain-of-surjection-is-compact∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                    → is-surjection f
                                    → is-compact∙ X
                                    → is-compact∙ Y
 codomain-of-surjection-is-compact∙ {𝓤} {𝓥} {X} {Y} f i ε q = (y₀ , h)
  where
   p : X → 𝟚
   p = q ∘ f

   x₀ : X
   x₀ = universal-witness ε p

   g : q (f x₀) ＝ ₁ → (x : X) → q (f x) ＝ ₁
   g = witness-universality ε p

   y₀ : Y
   y₀ = f x₀

   isp : (y : Y) → is-prop (q y ＝ ₁)
   isp y = 𝟚-is-set

   h : q y₀ ＝ ₁ → (y : Y) → q y ＝ ₁
   h r = surjection-induction f i (λ - → q - ＝ ₁) isp (g r)

 image-is-compact∙ : {X Y : 𝓤₀ ̇ } (f : X → Y)
                   → is-compact∙ X
                   → is-compact∙ (image f)
 image-is-compact∙ f = codomain-of-surjection-is-compact∙
                        (corestriction f)
                        (corestrictions-are-surjections f)

\end{code}

TODO. The following old code from 2011 seems to repeat some of the
above. We should deal with this.

\begin{code}

is-wcompact : 𝓤 ̇ → 𝓤 ̇
is-wcompact X = (p : X → 𝟚) → Σ y ꞉ 𝟚 , (y ＝ ₁ ↔ ((x : X) → p x ＝ ₁))

\end{code}

Closer to the original definition of exhaustibility in LICS'2007 amd LMCS'2008:

\begin{code}

is-wcompact' : 𝓤 ̇ → 𝓤 ̇
is-wcompact' X = Σ A ꞉ ((X → 𝟚) → 𝟚) , ((p : X → 𝟚) → A p ＝ ₁ ↔ ((x : X) → p x ＝ ₁))

\end{code}

Because the Curry-Howard interpretation of the axiom of choice holds
in MLTT:

\begin{code}

wcompact-types-are-wcompact' : {X : 𝓤 ̇ } → is-wcompact X → is-wcompact' X
wcompact-types-are-wcompact' {𝓤} {X} φ = A , lemma
 where
  A : (X → 𝟚) → 𝟚
  A p = pr₁ (φ p)

  lemma : (p : X → 𝟚) → A p ＝ ₁ ↔ ((x : X) → p x ＝ ₁)
  lemma p = pr₂ (φ p)

compact-gives-wcompact : {X : 𝓤 ̇ } → is-compact∙ X → is-wcompact X
compact-gives-wcompact {𝓤} {X} ε p = y , (lemma₀ , lemma₁)
 where
  x₀ : X
  x₀ = pr₁ (ε p)

  y : 𝟚
  y = p x₀

  lemma₀ :  y ＝ ₁ → (x : X) → p x ＝ ₁
  lemma₀ = pr₂ (ε p)

  lemma₁ : ((x : X) → p x ＝ ₁) → y ＝ ₁
  lemma₁ h = h x₀

\end{code}

Added 8th November - December 2019. I think the following equivalent
notion of compactness is easier to deal with, and I wish I had used it
in the original development:

\begin{code}

is-Σ-Compact : 𝓤 ̇ → {𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
is-Σ-Compact X {𝓥} = (A : X → 𝓥 ̇ ) → is-complemented A → is-decidable (Σ A)

Complemented-choice : 𝓤 ̇ → {𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
Complemented-choice X {𝓥} = (A : X → 𝓥 ̇ ) → is-complemented A → ¬¬ Σ A → Σ A

Σ-Compactness-gives-Complemented-choice : {X : 𝓤 ̇ }
                                        → is-Σ-Compact X {𝓥}
                                        → Complemented-choice X {𝓥}
Σ-Compactness-gives-Complemented-choice {𝓤} {𝓥} {X} c A δ = ¬¬-elim (c A δ)

is-Compact = is-Σ-Compact

Compactness-gives-complemented-choice : {X : 𝓤 ̇ }
                                      → is-Compact X
                                      → Complemented-choice X {𝓥}
Compactness-gives-complemented-choice c A δ = ¬¬-elim (c A δ)

compact-types-are-Compact : {X : 𝓤 ̇ } → is-compact X → is-Compact X {𝓥}
compact-types-are-Compact {𝓤} {𝓥} {X} c A d = iii
 where
  i : Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ＝ ₀ → A x) × (p x ＝ ₁ → ¬ (A x)))
  i = characteristic-function d

  p : X → 𝟚
  p = pr₁ i

  ii : (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁) → is-decidable (Σ A)
  ii (inl (x , r)) = inl (x , pr₁ (pr₂ i x) r)
  ii (inr u)       = inr φ
   where
    φ : ¬ Σ A
    φ (x , a) = pr₂ (pr₂ i x) (u x) a

  iii : is-decidable (Σ A)
  iii = ii (c p)

Compact-types-are-compact : {X : 𝓤 ̇ } → is-Compact X {𝓤₀} → is-compact X
Compact-types-are-compact {𝓤} {X} C p = iv
 where
  A : X → 𝓤₀ ̇
  A x = p x ＝ ₀

  i : is-complemented (λ x → p x ＝ ₀) → is-decidable (Σ x ꞉ X , p x ＝ ₀)
  i = C A

  ii : is-complemented (λ x → p x ＝ ₀)
  ii x = 𝟚-is-discrete (p x) ₀

  iii : is-decidable (Σ x ꞉ X , p x ＝ ₀) → (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁)
  iii (inl σ) = inl σ
  iii (inr u) = inr (λ x → different-from-₀-equal-₁ (λ r → u (x , r)))

  iv : (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁)
  iv = iii (i ii)

Compact-resize-up₀ : {X : 𝓤 ̇ } → is-Compact X {𝓤₀} → is-Compact X {𝓥}
Compact-resize-up₀ C = compact-types-are-Compact
                       (Compact-types-are-compact C)
\end{code}

TODO. Prove the converse of the previous observation, using the fact
that any decidable proposition is logically equivalent to either 𝟘 or
𝟙, and hence to a type in the universe 𝓤₀.

\begin{code}

is-Π-Compact : 𝓤 ̇ → {𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
is-Π-Compact {𝓤} X {𝓥} = (A : X → 𝓥 ̇ ) → is-complemented A → is-decidable (Π A)

Σ-Compact-types-are-Π-Compact : (X : 𝓤 ̇ )
                               → is-Σ-Compact X {𝓥}
                               → is-Π-Compact X {𝓥}
Σ-Compact-types-are-Π-Compact X C A d = γ (C (λ x → ¬ (A x)) e)
 where
  e : is-complemented (λ x → ¬ (A x))
  e x = ¬-preserves-decidability (d x)

  γ : is-decidable (Σ x ꞉ X , ¬ (A x)) → is-decidable (Π x ꞉ X , A x)
  γ (inl (x , v)) = inr (λ φ → v (φ x))
  γ (inr u)       = inl (λ x → ¬¬-elim (d x) (λ n → u (x , n)))

𝟘-is-Compact : is-Compact (𝟘 {𝓤}) {𝓥}
𝟘-is-Compact A δ = inr (λ (σ : Σ A) → 𝟘-elim (pr₁ σ))

𝟙-is-Compact : is-Compact (𝟙 {𝓤}) {𝓥}
𝟙-is-Compact A δ = γ (δ ⋆)
 where
  γ : A ⋆ + ¬ A ⋆ → is-decidable (Σ A)
  γ (inl a) = inl (⋆ , a)
  γ (inr u) = inr (λ {(⋆ , a) → u a})

singletons-are-Compact : {X : 𝓤 ̇ } → is-singleton X → is-Compact X {𝓥}
singletons-are-Compact (* , contraction) A δ = γ (δ *)
 where
  γ : A * + ¬ A * → is-decidable (Σ A)
  γ (inl a) = inl (* , a)
  γ (inr u) = inr (λ (x , a) → u (transport⁻¹ A (contraction x) a))

+-is-Compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → is-Compact X {𝓦}
             → is-Compact Y {𝓦}
             → is-Compact (X + Y) {𝓦}
+-is-Compact c d A δ = γ (c (A ∘ inl) (δ ∘ inl)) (d (A ∘ inr) (δ ∘ inr))
 where
  γ : is-decidable (Σ (A ∘ inl)) → is-decidable (Σ (A ∘ inr)) → is-decidable (Σ A)
  γ (inl (x , a)) _            = inl (inl x , a)
  γ (inr _)      (inl (y , a)) = inl (inr y , a)
  γ (inr u)      (inr v)       = inr w
   where
    w : ¬ Σ A
    w (inl x , a) = u (x , a)
    w (inr y , a) = v (y , a)

Σ-is-Compact : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
             → is-Compact X {𝓥 ⊔ 𝓦}
             → ((x : X) → is-Compact (Y x) {𝓦})
             → is-Compact (Σ Y) {𝓦}
Σ-is-Compact {𝓤} {𝓥} {𝓦} {X} {Y} c d A δ = γ e
 where
  B : X → 𝓥 ⊔ 𝓦 ̇
  B x = Σ y ꞉ Y x , A (x , y)

  ζ : (x : X) → is-complemented (λ y → A (x , y))
  ζ x y = δ (x , y)

  ε : is-complemented B
  ε x = d x (λ y → A (x , y)) (ζ x)

  e : is-decidable (Σ B)
  e = c B ε

  γ : is-decidable (Σ B) → is-decidable (Σ A)
  γ (inl (x , (y , a))) = inl ((x , y) , a)
  γ (inr u)             = inr (λ ((x , y) , a) → u (x , (y , a)))

\end{code}

TODO. A direct proof of the following would give more general universe
assignments:

\begin{code}

×-is-Compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → is-Compact X {𝓥 ⊔ 𝓦}
             → is-Compact Y {𝓦}
             → is-Compact (X × Y) {𝓦}
×-is-Compact c d = Σ-is-Compact c (λ x → d)


Compact-closed-under-retracts : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                              → retract Y of X
                              → is-Compact X {𝓦}
                              → is-Compact Y {𝓦}
Compact-closed-under-retracts {𝓤} {𝓥} {𝓦} {X} {Y} (r , s , η) c A δ = γ (c B ε)
 where
  B : X → 𝓦 ̇
  B = A ∘ r

  ε : is-complemented B
  ε = δ ∘ r

  γ : is-decidable (Σ B) → is-decidable (Σ A)
  γ (inl (x , a)) = inl (r x , a)
  γ (inr u)       = inr (λ (y , a) → u (s y , transport A ((η y)⁻¹) a))

Compact-closed-under-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                       → X ≃ Y
                       → is-Compact X {𝓦}
                       → is-Compact Y {𝓦}
Compact-closed-under-≃ e = Compact-closed-under-retracts (≃-gives-▷ e)

module CompactTypesPT (pt : propositional-truncations-exist) where

 open import UF.ImageAndSurjection pt

 surjection-Compact : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → funext 𝓥 𝓤₀
                    → is-surjection f
                    → is-Compact X {𝓥}
                    → is-Compact Y {𝓥}
 surjection-Compact {𝓤} {𝓥} {X} {Y} f fe i c A δ = γ (c B ε)
  where
   B : X → 𝓥 ̇
   B = A ∘ f

   ε : is-complemented B
   ε = δ ∘ f

   γ : is-decidable (Σ B) → is-decidable (Σ A)
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
               → is-Compact X {𝓤 ⊔ 𝓥}
               → is-Compact (image f) {𝓤 ⊔ 𝓥}
 image-Compact fe f c = surjection-Compact (corestriction f) fe
                         (corestrictions-are-surjections f) c

\end{code}

In `TypeTopology.DenseMapsProperties` a generalization of the above result is
given that applies to all dense maps, and does not use the function
extensionality axiom or existence of propositional truncations.

\begin{code}

 open PropositionalTruncation pt

 is-∃-Compact : 𝓤 ̇ → {𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
 is-∃-Compact {𝓤} X {𝓥} = (A : X → 𝓥 ̇ ) → is-complemented A → is-decidable (∃ A)

 Compactness-gives-∃-Compactness : {X : 𝓤 ̇ }
                                 → is-Compact X {𝓥}
                                 → is-∃-Compact X {𝓥}
 Compactness-gives-∃-Compactness {𝓤} {X} c A δ = γ (c A δ)
  where
   γ : is-decidable (Σ A) → is-decidable (∃ A)
   γ (inl σ) = inl ∣ σ ∣
   γ (inr u) = inr (empty-is-uninhabited u)


 ∃-Compactness-is-prop : Fun-Ext → {X : 𝓤 ̇ } → is-prop (is-∃-Compact X {𝓥})
 ∃-Compactness-is-prop {𝓤} {𝓥} fe {X} =
  Π₂-is-prop fe
   (λ A δ → decidability-of-prop-is-prop fe
             ∃-is-prop)


 ∃-Compactness-gives-Markov
  : {X : 𝓤 ̇ }
  → is-∃-Compact X {𝓥}
  → (A : X → 𝓥 ̇ )
  → is-complemented A
  → ¬¬ ∃ A
  → ∃ A
 ∃-Compactness-gives-Markov {𝓤} {𝓥} {X} c A δ = ¬¬-elim (c A δ)

 ∥Compact∥-gives-∃-Compact : Fun-Ext
                           → {X : 𝓤 ̇ }
                           → ∥ is-Compact X {𝓥} ∥ → is-∃-Compact X {𝓥}
 ∥Compact∥-gives-∃-Compact fe = ∥∥-rec (∃-Compactness-is-prop fe)
                                      Compactness-gives-∃-Compactness

 ∃-Compact-propositions-are-decidable : {P : 𝓤 ̇ }
                                      → is-prop P
                                      → is-∃-Compact P
                                      → is-decidable P
 ∃-Compact-propositions-are-decidable {𝓤} {P} i κ = γ β
  where
   A : P → 𝓤 ̇
   A p = 𝟙

   α : is-complemented A
   α p = inl ⋆

   β : is-decidable (∃ p ꞉ P , A p)
   β = κ A α

   γ : type-of β → is-decidable P
   γ (inl e) = inl (∥∥-rec i pr₁ e)
   γ (inr ν) = inr (contrapositive (λ p → ∣ p , ⋆ ∣) ν)

\end{code}

Variation:

\begin{code}

 ∃-Compact-propositions-are-decidable' : {P : 𝓤 ̇ }
                                      → is-prop P
                                      → is-∃-Compact (P + 𝟙 {𝓥})
                                      → is-decidable P
 ∃-Compact-propositions-are-decidable' {𝓤} {𝓥} {P} i κ = γ β
  where
   A : P + 𝟙 → 𝓤 ̇
   A (inl p) = 𝟙
   A (inr ⋆) = 𝟘

   α : is-complemented A
   α (inl p) = inl ⋆
   α (inr ⋆) = inr (λ z → 𝟘-elim z)

   β : is-decidable (∃ x ꞉ P + 𝟙 , A x)
   β = κ A α

   δ : Σ A → P
   δ (inl p , ⋆) = p
   δ (inr ⋆ , a) = 𝟘-elim a

   ϕ : P → ∃ A
   ϕ p = ∣ inl p , ⋆ ∣

   γ : type-of β → is-decidable P
   γ (inl e) = inl (∥∥-rec i δ e)
   γ (inr ν) = inr (contrapositive ϕ ν)

\end{code}

Added 10th December 2019.

\begin{code}

is-Compact∙ : 𝓤 ̇ → {𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
is-Compact∙ {𝓤} X {𝓥} = (A : X → 𝓥 ̇ ) → is-complemented A → Σ x₀ ꞉ X , (A x₀ → (x : X) → A x)

Compact-pointed-gives-Compact∙ : {X : 𝓤 ̇ } → is-Compact X {𝓥} → X → is-Compact∙ X {𝓥}
Compact-pointed-gives-Compact∙ {𝓤} {𝓥} {X} c x₀ A δ = γ (c A' δ')
 where
  A' : X → 𝓥 ̇
  A' x = ¬ A x

  δ' : is-complemented A'
  δ' x = ¬-preserves-decidability (δ x)

  γ : is-decidable (Σ A') → Σ x₀ ꞉ X , (A x₀ → (x : X) → A x)
  γ (inl (x , u)) = x  , (λ (a : A x) → 𝟘-elim (u a))
  γ (inr v)       = x₀ , (λ (a : A x₀) (x : X) → ¬¬-elim (δ x) λ (φ : ¬ A x) → v (x , φ))


Compact∙-gives-Compact : {X : 𝓤 ̇ } → is-Compact∙ X {𝓥} → is-Compact X {𝓥}
Compact∙-gives-Compact {𝓤} {𝓥} {X} ε A δ = γ (δ x₀)
 where
  l : Σ x₀ ꞉ X , (¬ A x₀ → (x : X) → ¬ A x)
  l = ε (λ x → ¬ A x) (λ x → ¬-preserves-decidability (δ x))

  x₀ : X
  x₀ = pr₁ l

  i : ¬ A x₀ → ¬ Σ A
  i u (x , a) = pr₂ l u x a

  γ : is-decidable (A x₀) → is-decidable (Σ A)
  γ (inl a) = inl (x₀ , a)
  γ (inr u) = inr (i u)

Compact∙-gives-pointed : {X : 𝓤 ̇ } → is-Compact∙ X {𝓥} → X
Compact∙-gives-pointed ε = pr₁ (ε (λ x → 𝟘) (λ x → 𝟘-is-decidable))

\end{code}

Based on what was done in the module WeaklyCompactTypes before:

\begin{code}

Compact-types-are-decidable : (X : 𝓤 ̇ ) → is-Compact X → is-decidable X
Compact-types-are-decidable X c = γ
 where
  A : X → 𝓤₀ ̇
  A _ = 𝟙

  δ : is-complemented A
  δ _ = inl ⋆

  a : is-decidable (X × 𝟙)
  a = c A δ

  f : is-decidable (X × 𝟙) → is-decidable X
  f (inl (x , ⋆)) = inl x
  f (inr ν)       = inr (contrapositive (λ x → (x , ⋆)) ν)

  γ : is-decidable X
  γ = f a

discrete-to-power-Compact-is-discrete' : funext 𝓤 𝓥
                                      → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                                      → is-Π-Compact X
                                      → ((x : X) → is-discrete (Y x))
                                      → is-discrete (Π Y)
discrete-to-power-Compact-is-discrete' {𝓤} {𝓥} fe {X} {Y} c d f g = γ
 where
  A : X → 𝓥 ̇
  A x = f x ＝ g x

  a : (x : X) → is-decidable (A x)
  a x = d x (f x) (g x)

  b : is-decidable (Π A)
  b = c A a

  φ : is-decidable (Π A) → is-decidable (f ＝ g)
  φ (inl α) = inl (dfunext fe α)
  φ (inr ν) = inr (contrapositive happly ν)

  γ : is-decidable (f ＝ g)
  γ = φ b

discrete-to-power-Compact-is-discrete : funext 𝓤 𝓥
                                      → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                      → is-Π-Compact X
                                      → is-discrete Y
                                      → is-discrete (X → Y)
discrete-to-power-Compact-is-discrete {𝓤} {𝓥} fe {X} {Y} c d =
 discrete-to-power-Compact-is-discrete' fe c (λ _ → d)

open import TypeTopology.TotallySeparated

compact-power-of-𝟚-has-discrete-exponent : {X : 𝓤 ̇ }
                                         → is-totally-separated X
                                         → is-Π-Compact (X → 𝟚)
                                         → is-discrete X
compact-power-of-𝟚-has-discrete-exponent {𝓤} {X} τ κ x y = γ δ
 where
  d : (p : X → 𝟚) → is-decidable (p x ＝ p y)
  d p = 𝟚-is-discrete (p x) (p y)

  δ : is-decidable ((p : X → 𝟚) → p x ＝ p y)
  δ = κ (λ p → p x ＝ p y) d

  α : x ＝ y → (p : X → 𝟚) → p x ＝ p y
  α e p = ap p e

  β : ¬ ((p : X → 𝟚) → p x ＝ p y) → ¬ (x ＝ y)
  β = contrapositive α

  γ : type-of δ → is-decidable (x ＝ y)
  γ (inl α) = inl (τ α)
  γ (inr u) = inr (β u)

\end{code}

Added 21st October 2021.

\begin{code}

complemented-subset-of-compact-type : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                                    → is-Compact X {𝓥 ⊔ 𝓦}
                                    → is-complemented A
                                    → ((x : X) → is-prop (A x))
                                    → is-Compact (Σ x ꞉ X , A x) {𝓦}
complemented-subset-of-compact-type {𝓤} {𝓥} {𝓦} {X} {A}
                                    X-compact
                                    A-complemented
                                    A-is-prop-valued
                                    B B-complemented = γ II
 where
  I : (x : X) → is-decidable (Σ a ꞉ A x , B (x , a))
  I x = Cases (A-complemented x)
         (λ (a : A x)
               → Cases (B-complemented (x , a))
                  (λ (b : B (x , a))     → inl (a , b))
                  (λ ν → inr (λ (a' , b) → ν (transport
                                               (λ - → B (x , -))
                                               (A-is-prop-valued x a' a)
                                               b))))
         (λ ν → inr (λ (a , b) → ν a))

  II : is-decidable (Σ x ꞉ X , Σ a ꞉ A x , B (x , a))
  II = X-compact (λ x → Σ a ꞉ A x , B (x , a)) I

  γ : type-of II → is-decidable (Σ y ꞉ (Σ x ꞉ X , A x) , B y)
  γ (inl (x , (a , b))) = inl ((x , a) , b)
  γ (inr ν)             = inr (λ ((x , a) , b) → ν (x , (a , b)))

\end{code}

Added 10th January 2022. (Is this somewhere already?)

\begin{code}

compact-gives-Σ+Π : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
                  → is-compact X
                  → (q : (x : X) → A x + B x)
                  → (Σ x ꞉ X , A x) + (Π x ꞉ X , B x)
compact-gives-Σ+Π X A B κ q = III II
 where
  p : X → 𝟚
  p = indicator-map q

  I : (x : X) → (p x ＝ ₀ → A x) × (p x ＝ ₁ → B x)
  I = indicator-property q

  II : (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁)
  II = κ p

  III : type-of II → (Σ x ꞉ X , A x) + (Π x ꞉ X , B x)
  III (inl (x , e)) = inl (x , pr₁ (I x) e)
  III (inr ϕ)       = inr (λ x → pr₂ (I x) (ϕ x))

\end{code}

Added 26th April 2022. All types are compact iff global choice holds:

\begin{code}

open import UF.ClassicalLogic

all-types-compact-gives-global-choice : ((X : 𝓤 ̇ ) → is-Compact X {𝓤})
                                      → Global-Choice 𝓤
all-types-compact-gives-global-choice {𝓤} α X =
 Cases (α X (λ (_ : X) → 𝟙 {𝓤}) (λ (_ : X) → 𝟙-is-decidable))
   (λ (x , _) → inl x)
   (λ ν       → inr (λ (x : X) → ν (x , ⋆)))

global-choice-gives-all-types-compact : Global-Choice 𝓤
                                      → ((X : 𝓤 ̇ ) → is-Compact X {𝓤})
global-choice-gives-all-types-compact gc X A δ = gc (Σ A)

\end{code}

Added 6th June 2022. Why didn't we require the family A to be
prop-valued? We could have if we wanted to.

\begin{code}

Σ-Compact' : 𝓤 ̇ → {𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
Σ-Compact' {𝓤} X {𝓥} = (A : X → 𝓥 ̇ )
                     → ((x : X) → is-prop (A x))
                     → is-complemented A
                     → is-decidable (Σ A)

Compact' = Σ-Compact'

compact-gives-Compact' : {X : 𝓤 ̇ } → is-compact X → Compact' X {𝓥}
compact-gives-Compact' {𝓤} {𝓥} {X} c A _ d = iii
 where
  i : Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ＝ ₀ → A x) × (p x ＝ ₁ → ¬ (A x)))
  i = characteristic-function d

  p : X → 𝟚
  p = pr₁ i

  ii : (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁) → is-decidable (Σ A)
  ii (inl (x , r)) = inl (x , pr₁ (pr₂ i x) r)
  ii (inr u)       = inr φ
   where
    φ : ¬ Σ A
    φ (x , a) = pr₂ (pr₂ i x) (u x) a

  iii : is-decidable (Σ A)
  iii = ii (c p)

Compact'-types-are-compact : {X : 𝓤 ̇ } → Compact' X → is-compact X
Compact'-types-are-compact {𝓤} {X} C p = iv
 where
  A : X → 𝓤₀ ̇
  A x = p x ＝ ₀

  i : is-complemented (λ x → p x ＝ ₀) → is-decidable (Σ x ꞉ X , p x ＝ ₀)
  i = C A (λ x → 𝟚-is-set)

  ii : is-complemented (λ x → p x ＝ ₀)
  ii x = 𝟚-is-discrete (p x) ₀

  iii : is-decidable (Σ x ꞉ X , p x ＝ ₀) → (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁)
  iii (inl σ) = inl σ
  iii (inr u) = inr (λ x → different-from-₀-equal-₁ (λ r → u (x , r)))

  iv : (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁)
  iv = iii (i ii)

Compact'-types-are-Compact : {X : 𝓤 ̇ } → Compact' X → is-Compact X {𝓦}
Compact'-types-are-Compact C = compact-types-are-Compact
                                (Compact'-types-are-compact C)

Compact-gives-Compact' : {X : 𝓤 ̇ } → is-Compact X {𝓥} → Compact' X {𝓥}
Compact-gives-Compact' C A _ = C A

\end{code}

TODO. (1) is-Compact' X ≃ is-compact X.
      (2) is-Compact' X is a retract of is-Compact X.

Added by Fredrik Bakke on the 2nd of April 2025.

Π-Compact types are closed under sums.

\begin{code}

Σ-is-Π-Compact : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                → is-Π-Compact X {𝓥 ⊔ 𝓦}
                → ((x : X) → is-Π-Compact (Y x) {𝓦})
                → is-Π-Compact (Σ Y) {𝓦}
Σ-is-Π-Compact {𝓤} {𝓥} {𝓦} {X} {Y} cX cY A dA =
 decidable-↔
  ( (λ f (x , y) → f x y) , (λ f x y → f (x , y)))
  ( cX (λ x → (y : Y x) → A (x , y))
       (λ x → cY x (λ y → A (x , y)) (λ y → dA (x , y))))

\end{code}

Π-Compact types have decidable negations.

\begin{code}

Π-Compact-types-have-decidable-negations' : {X : 𝓤 ̇ }
                                          → is-Π-Compact X {𝓦}
                                          → is-decidable (X → 𝟘)
Π-Compact-types-have-decidable-negations' {𝓤} {𝓦} {X} αX =
 αX (λ _ → 𝟘) (λ _ → 𝟘-is-decidable)

Π-Compact-types-have-decidable-negations : {X : 𝓤 ̇ }
                                         → is-Π-Compact X {𝓦}
                                         → is-decidable (¬ X)
Π-Compact-types-have-decidable-negations αX =
 decidable-↔
  ((λ x → 𝟘-elim ∘ x) , (λ x → 𝟘-elim ∘ x))
  (Π-Compact-types-have-decidable-negations' αX)

\end{code}

Added March 2022 by Martin Escardo.

\begin{code}

Σ-isolated-left : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
                → ((x : X) → is-Compact (Y x))
                → is-isolated (x , y)
                → is-isolated x
Σ-isolated-left {𝓤} {𝓥} {X} {Y} {x} {y} κ i x' = γ δ
 where
   A : (y' : Y x') → 𝓤 ⊔ 𝓥 ̇
   A y' = (x , y) ＝ (x' , y')

   d : is-complemented A
   d y' = i (x' , y')

   δ : is-decidable (Σ A)
   δ = κ x' A d

   γ : is-decidable (Σ A) → is-decidable (x ＝ x')
   γ (inl (y' , refl)) = inl refl
   γ (inr ν)           = inr (λ {refl → ν (y , refl)})

\end{code}

Is the compactness assumption needed? Are there better assumptions

\begin{code}

Σ-weakly-isolated-left' : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
                        → ((x : X) → is-Π-Compact (Y x))
                        → is-weakly-isolated (x , y)
                        → is-weakly-isolated x
Σ-weakly-isolated-left' {𝓤} {𝓥} {X} {Y} {x} {y} κ i x' = γ δ
 where
  A : (y' : Y x') → 𝓤 ⊔ 𝓥 ̇
  A y' = (x' , y') ≠ (x , y)

  c : is-complemented A
  c y' = i (x' , y')

  δ : is-decidable (Π A)
  δ = κ x' A c

  γ : is-decidable (Π A) → is-decidable (x' ≠ x)
  γ (inl a) = inl (λ {refl → a y refl})
  γ (inr ν) = inr (λ (d : x' ≠ x)
                   → ν (λ (y' : Y x') (e : (x' , y') ＝ (x , y))
                        → d (ap pr₁ e)))

Σ-weakly-isolated-left : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
                       → ((x : X) → is-Compact (Y x))
                       → is-weakly-isolated (x , y)
                       → is-weakly-isolated x
Σ-weakly-isolated-left {𝓤} {𝓥} {X} {Y} {x} {y} κ =
 Σ-weakly-isolated-left' (λ x → Σ-Compact-types-are-Π-Compact (Y x) (κ x))

\end{code}
