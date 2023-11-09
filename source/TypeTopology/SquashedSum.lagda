Martin Escardo, 2 May 2014.

Squashed sum.

See remarks below for an explanation.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module TypeTopology.SquashedSum (fe : FunExt) where -- move this to compact types

private
 fe₀ : funext 𝓤₀ 𝓤₀
 fe₀ = fe 𝓤₀ 𝓤₀

open import CoNaturals.GenericConvergentSequence
open import InjectiveTypes.Blackboard fe
open import MLTT.Plus-Properties
open import MLTT.Two-Properties
open import Notation.CanonicalMap hiding ([_])
open import TypeTopology.CompactTypes
open import TypeTopology.Density
open import TypeTopology.ExtendedSumCompact fe
open import TypeTopology.GenericConvergentSequenceCompactness fe₀
open import TypeTopology.SigmaDiscreteAndTotallySeparated
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.PairFun
open import UF.Subsingletons
open import UF.Subsingletons-Properties

\end{code}

Recall that the map

  ι : ℕ → ℕ∞

is the canonical embedding. Given a type family X : ℕ → 𝓤 ̇, we take its
right Kan extension

  X / ι : ℕ∞ → 𝓤 ̇

and then its sum, which we call the squashed sum of X and write

  Σ¹ X.

We have that (X / ι) ∞ ≃ 𝟙. What is interesting is that if each
X n is compact then so is its squashed sum Σ¹ X.

\begin{code}

Σ¹ :(ℕ → 𝓤 ̇ ) → 𝓤 ̇
Σ¹ X = Σ (X / ι)

Σ¹-compact∙ : (X : ℕ → 𝓤 ̇ )
            → ((n : ℕ) → is-compact∙(X n))
            → is-compact∙(Σ¹ X)
Σ¹-compact∙ X ε = extended-sum-compact∙
                   ℕ-to-ℕ∞
                   (ℕ-to-ℕ∞-is-embedding fe₀)
                   ε
                   ℕ∞-compact∙
\end{code}

Added 26 July 2018 (implementing ideas of several years ago).

We now develop a discrete (but not compact) version Σ₁ X of Σ¹ X
with a dense embedding into Σ¹ X, where an embedding is called dense
if the complement of its image is empty. Recall that the function

  ι𝟙 : ℕ + 𝟙 → ℕ∞

is the canonical embedding that maps the added isolated point to ∞,
which is dense.

\begin{code}

over : ℕ → ℕ + 𝟙
over = inl {𝓤₀} {𝓤₀}

over-embedding : is-embedding over
over-embedding = inl-is-embedding ℕ 𝟙

Σ₁ :(ℕ → 𝓤 ̇ ) → 𝓤 ̇
Σ₁ X = Σ (X / over)

ι𝟙-over : (n : ℕ) → ι𝟙 (over n) ＝ ι n
ι𝟙-over n = refl

over-is-discrete : (X : ℕ → 𝓤 ̇ )
                 → ((n : ℕ) → is-discrete (X n))
                 → (z : ℕ + 𝟙) → is-discrete ((X / over) z)
over-is-discrete X d (inl n) = retract-is-discrete
                                 (≃-gives-◁
                                   (Π-extension-property X over
                                      over-embedding n))
                                 (d n)
over-is-discrete X d (inr *) = retract-is-discrete {𝓤₀}
                                 (≃-gives-◁
                                   (Π-extension-out-of-range X over (inr *)
                                       (λ n → +disjoint)))
                                 𝟙-is-discrete

Σ₁-is-discrete : (X : ℕ → 𝓤 ̇ )
               → ((n : ℕ) → is-discrete(X n))
               → is-discrete (Σ₁ X)
Σ₁-is-discrete X d = Σ-is-discrete
                       (+-is-discrete ℕ-is-discrete 𝟙-is-discrete)
                       (over-is-discrete X d)
\end{code}

The type (X / over) z is densely embedded into the type (X / ι) (ι𝟙 z):

\begin{code}

over-ι : (X : ℕ → 𝓤 ̇ ) (z : ℕ + 𝟙)
       → (X / over) z ↪ᵈ (X / ι) (ι𝟙 z)
over-ι X (inl n) = equiv-dense-embedding (
 (X / over) (over n)   ≃⟨ Π-extension-property X over over-embedding n ⟩
 X n                   ≃⟨ ≃-sym (Π-extension-property X ℕ-to-ℕ∞ (ℕ-to-ℕ∞-is-embedding fe₀) n) ⟩
 (X / ι) (ι n) ■)
over-ι X (inr *) = equiv-dense-embedding (
 (X / over) (inr *) ≃⟨ Π-extension-out-of-range X over (inr *) (λ x → +disjoint ) ⟩
 𝟙 {𝓤₀}             ≃⟨ ≃-sym (Π-extension-out-of-range X ι ∞ (λ n p → ∞-is-not-finite n (p ⁻¹))) ⟩
 (X / ι) ∞      ■ )

over-ι-map : (X : ℕ → 𝓤 ̇ ) (z : ℕ + 𝟙)
               → (X / over) z → (X / ι) (ι𝟙 z)
over-ι-map X z = detofun (over-ι X z)

over-ι-map-dense : (X : ℕ → 𝓤 ̇ ) (z : ℕ + 𝟙)
                     → is-dense (over-ι-map X z)
over-ι-map-dense X z = is-dense-detofun (over-ι X z)

over-ι-map-left : (X : ℕ → 𝓤 ̇ ) (n : ℕ)
                      (φ : (w : fiber over (inl n)) → X (pr₁ w))
                    → over-ι-map X (inl n) φ (n , refl)
                    ＝ φ (n , refl)
over-ι-map-left X n φ =
 transport
  (λ - → over-ι-map X (inl n) φ (n , refl)
       ＝ transport (λ - → X (pr₁ -)) - (φ (n , refl)))
  (props-are-sets
    (ℕ-to-ℕ∞-is-embedding fe₀ (ι n))
    (ℕ-to-ℕ∞-is-embedding fe₀ (ι n) (n , refl) (n , refl))
    refl)
  (f (n , refl))
 where
  -- We define this for the sake of clarity only:
  f : (t : fiber ι (ι n))
    → over-ι-map X (inl n) φ t
    ＝ transport (λ - → X (pr₁ -))
                 (ℕ-to-ℕ∞-is-embedding fe₀ (ι n) (n , refl) t)
                 (φ (n , refl))
  f t = refl

\end{code}

The discrete type Σ₁ X is densely embedded into
the compact type Σ¹ X:

\begin{code}

Σ-up : (X : ℕ → 𝓤 ̇ ) → Σ₁ X → Σ¹ X
Σ-up X = pair-fun ι𝟙 (over-ι-map X)

Σ-up-embedding : (X : ℕ → 𝓤 ̇ ) → is-embedding (Σ-up X)
Σ-up-embedding X = pair-fun-is-embedding
                    ι𝟙
                    (over-ι-map X)
                    (ι𝟙-is-embedding fe₀)
                    (λ z → is-embedding-detofun (over-ι X z))

Σ-up-dense : (X : ℕ → 𝓤 ̇ ) → is-dense (Σ-up X)
Σ-up-dense X = pair-fun-dense ι𝟙
                (over-ι-map X)
                (ι𝟙-dense fe₀)
                (λ z → is-dense-detofun (over-ι X z))

\end{code}

But this is not enough: we need a map

  Σ↑ : Σ₁ X → Σ¹ Y,

given maps

  f n : X n → Y n,

which has to preserve dense embeddings.

\begin{code}

Over : (X : ℕ → 𝓤 ̇ ) (Y : ℕ → 𝓤 ̇ )
       (f : (n : ℕ) → X n → Y n)
     → (z : ℕ + 𝟙) → (X / over) z → (Y / over) z
Over X Y f (inl n) =
  ⌜ Π-extension-property Y over over-embedding n ⌝⁻¹ ∘
  f n ∘
  ⌜ Π-extension-property X over over-embedding n ⌝
Over X Y f (inr *) =
  _∘_ {_} {𝓤₀}
   ⌜ Π-extension-out-of-range Y over (inr *) (λ _ → +disjoint) ⌝⁻¹
   ⌜ Π-extension-out-of-range X over (inr *) (λ _ → +disjoint) ⌝

Over-inl : (X : ℕ → 𝓤 ̇ ) (Y : ℕ → 𝓤 ̇ ) (f : (n : ℕ) → X n → Y n)
         → (n : ℕ) → Over X Y f (inl n)
         ＝ λ (φ : (X / over) (inl n)) (w : fiber over (inl n)) →
             transport (λ - → Y (pr₁ -))
                       (inl-is-embedding ℕ 𝟙 (inl n) (n , refl) w)
                       (f n (φ (n , refl)))
Over-inl X Y f n = refl

Over-inr : (X : ℕ → 𝓤 ̇ ) (Y : ℕ → 𝓤 ̇ ) (f : (n : ℕ) → X n → Y n)
         → Over X Y f (inr ⋆) ＝ λ φ w → 𝟘-elim (+disjoint (pr₂ w))
Over-inr X Y f = refl

\end{code}

The following two proofs look complicated, but are rather simple:
composition preserves dense maps and embeddings, and equivalences are
dense embeddings.

\begin{code}

Over-dense : (X : ℕ → 𝓤 ̇ ) (Y : ℕ → 𝓤 ̇ )
             (f : (n : ℕ) → X n → Y n)
           → ((n : ℕ) → is-dense (f n))
           → (z : ℕ + 𝟙) → is-dense (Over X Y f z)
Over-dense X Y f d (inl n) =
 comp-is-dense
  (comp-is-dense
    (equivs-are-dense
      ⌜ Π-extension-property X over over-embedding n ⌝
      (⌜⌝-is-equiv (Π-extension-property X over over-embedding n)))
    (d n))
  (equivs-are-dense
    ⌜ Π-extension-property Y over over-embedding n ⌝⁻¹
    (⌜⌝-is-equiv (≃-sym (Π-extension-property Y over over-embedding n))))
Over-dense X Y f d (inr ⋆) =
 comp-is-dense {_} {𝓤₀}
  (equivs-are-dense
    ⌜ Π-extension-out-of-range X over (inr ⋆) (λ x → +disjoint) ⌝
    (⌜⌝-is-equiv (Π-extension-out-of-range X over (inr ⋆) (λ x → +disjoint))))
  (equivs-are-dense
    ⌜ Π-extension-out-of-range Y over (inr ⋆) (λ x → +disjoint) ⌝⁻¹
   (⌜⌝-is-equiv (≃-sym (Π-extension-out-of-range Y over (inr ⋆) (λ x → +disjoint)))))

Over-embedding : (X : ℕ → 𝓤 ̇ ) (Y : ℕ → 𝓤 ̇ )
                 (f : (n : ℕ) → X n → Y n)
               → ((n : ℕ) → is-embedding (f n))
               → (z : ℕ + 𝟙) → is-embedding (Over X Y f z)
Over-embedding {𝓤} X Y f d (inl n) =
 ∘-is-embedding
  (∘-is-embedding
    (equivs-are-embeddings
      ⌜ Π-extension-property X over over-embedding n ⌝
      (⌜⌝-is-equiv (Π-extension-property X over over-embedding n)))
    (d n))
  (equivs-are-embeddings
    ⌜ Π-extension-property Y over over-embedding n ⌝⁻¹
   (⌜⌝-is-equiv (≃-sym (Π-extension-property Y over over-embedding n))))
Over-embedding {𝓤} X Y f d (inr ⋆) =
 ∘-is-embedding {𝓤} {𝓤₀}
  (equivs-are-embeddings
    ⌜ Π-extension-out-of-range X over (inr ⋆) (λ x → +disjoint) ⌝
    (⌜⌝-is-equiv (Π-extension-out-of-range X over (inr ⋆) (λ x → +disjoint))))
  (equivs-are-embeddings
    ⌜ Π-extension-out-of-range Y over (inr ⋆) (λ x → +disjoint) ⌝⁻¹
   (⌜⌝-is-equiv (≃-sym (Π-extension-out-of-range Y over (inr ⋆) (λ x → +disjoint)))))

Σ₁-functor : (X : ℕ → 𝓤 ̇ ) (Y : ℕ → 𝓤 ̇ ) (f : (n : ℕ) → X n → Y n)
           → Σ₁ X → Σ₁ Y
Σ₁-functor X Y f = pair-fun id (Over X Y f)

Σ₁-functor-dense : (X : ℕ → 𝓤 ̇ ) (Y : ℕ → 𝓤 ̇ )
                   (f : (n : ℕ) → X n → Y n)
                 → ((n : ℕ) → is-dense (f n))
                 → is-dense (Σ₁-functor X Y f)
Σ₁-functor-dense X Y f d = pair-fun-dense
                            id
                            (Over X Y f)
                            id-is-dense
                            (Over-dense X Y f d)

Σ₁-functor-embedding : (X : ℕ → 𝓤 ̇ ) (Y : ℕ → 𝓤 ̇ )
                       (f : (n : ℕ) → X n → Y n)
                     → ((n : ℕ) → is-embedding (f n))
                     → is-embedding (Σ₁-functor X Y f)
Σ₁-functor-embedding X Y f e = pair-fun-is-embedding
                                id
                                (Over X Y f)
                                id-is-embedding
                                (Over-embedding X Y f e)

Σ↑ : (X : ℕ → 𝓤 ̇ ) (Y : ℕ → 𝓤 ̇ )
     (f : (n : ℕ) → X n → Y n)
   → Σ₁ X → Σ¹ Y
Σ↑ X Y f = Σ-up Y ∘ Σ₁-functor X Y f

Σ↑-dense : (X : ℕ → 𝓤 ̇ ) (Y : ℕ → 𝓤 ̇ )
           (f : (n : ℕ) → X n → Y n)
         → ((n : ℕ) → is-dense (f n))
         → is-dense (Σ↑ X Y f)
Σ↑-dense X Y f d = comp-is-dense (Σ₁-functor-dense X Y f d) (Σ-up-dense Y)

Σ↑-embedding : (X : ℕ → 𝓤 ̇ ) (Y : ℕ → 𝓤 ̇ )
               (f : (n : ℕ) → X n → Y n)
             → ((n : ℕ) → is-embedding (f n))
             → is-embedding (Σ↑ X Y f)
Σ↑-embedding X Y f d = ∘-is-embedding (Σ₁-functor-embedding X Y f d) (Σ-up-embedding Y)

\end{code}

We don't need this for the moment:

\begin{code}

ι𝟙-over-extension : {X : ℕ → 𝓤 ̇ } (u : ℕ∞)
                      → ((X / over) / ι𝟙) u ≃ (X / ι) u
ι𝟙-over-extension = iterated-extension over ι𝟙

\end{code}

End. What follows is an old version of part of the above.

The original version of the compactness of the squashed sum, given
below was much more convoluted, as it didn't use injective types, but
equivalent, as also shown below.

December 2012, going back to work done circa 2010.

The theorem here is that the "squashed sum" of any countable family of
compact∙ sets is itself compact (see the module CompactTypes,
imported below, for the definition and fundamental facts about the
notion).

(The terminology "squashed sum" comes from the paper "Infinite sets
that satisfy the principle of omniscience in all varieties of
constructive mathematics", where this concept is investigated within
the Cantor type ℕ → ₂, which makes the squashing self-evident.)

Given a countable family of sets.

   X : ℕ → 𝓤₀ ̇,

extend it to a ℕ∞-indexed family of sets as follows

  _[_] : (ℕ → 𝓤₀ ̇ ) → (ℕ∞ → 𝓤₀ ̇ )
  X [ u ] = (k : ℕ) → ι k ＝ u → X k

where u ranges over ℕ∞, the one-point compactification of the natural
numbers ℕ, defined in the module GenericConvergentSequence.

The squashed sum of X : ℕ → 𝓤₀ ̇ is defined to be

   Σᴵ X = Σ u ꞉ ℕ∞ , X [ u ]

Intuitively, the squashed sum is the disjoint sum with an added limit
point at infinity.

Assuming excluded middle, Σᴵ X is isomorphic to (Σ n ꞉ ℕ , X n) ⊎ 1
where 1 is the one-point type.

Assuming Brouwerian continuity axioms, Σᴵ X is the one-point
compactification of the disjoint sum (Σ n ꞉ ℕ , X n).

But we don't assume excluded middle or continuiy axioms here. We work
within intensional MLTT with function extensionality as a postulate
(rather than as a meta-theoretical rule).

\begin{code}

module original-version-and-equivalence-with-new-version where

 _[_] : (ℕ → 𝓤₀ ̇ ) → (ℕ∞ → 𝓤₀ ̇ )
 X [ u ] = (k : ℕ) → ι k ＝ u → X k

 Σᴵ : (ℕ → 𝓤₀ ̇ ) → 𝓤₀ ̇
 Σᴵ X = Σ u ꞉ ℕ∞ , X [ u ]

 ∞₁ : {X : ℕ → 𝓤₀ ̇ } → Σᴵ X
 ∞₁ = ∞ , λ k r → 𝟘-elim (∞-is-not-finite k (r ⁻¹))

\end{code}

 This point at infinity is unique assuming extensionality, because:

\begin{code}

 H : {X : ℕ → 𝓤₀ ̇ } → (u : ℕ∞) → u ＝ ∞ → (y y' : X [ u ]) → y ＝ y'
 H {X} u r y y' = dfunext fe₀ (λ k → dfunext fe₀ (λ s → lemma k s))
  where
   lemma : (k : ℕ) (s : ι k ＝ u) → y k s ＝ y' k s
   lemma k s = 𝟘-elim(∞-is-not-finite k (r ⁻¹ ∙ s ⁻¹))

\end{code}

 Next we have an isomorphism X [ u ] ≅ X n if ι n ＝ u:

\begin{code}

 F : {X : ℕ → 𝓤₀ ̇ } (n : ℕ) (u : ℕ∞) → ι n ＝ u → X n → X [ u ]
 F {X} n u r x k s = transport X (ℕ-to-ℕ∞-lc (r ∙ s ⁻¹)) x

 G : {X : ℕ → 𝓤₀ ̇ } (n : ℕ) (u : ℕ∞) → ι n ＝ u → X [ u ] → X n
 G n u r y = y n r

 FG : {X : ℕ → 𝓤₀ ̇ } (n : ℕ) (u : ℕ∞) (r : ι n ＝ u) (y : (k : ℕ)
   → ι k ＝ u → X k) → F n u r (G n u r y) ＝ y
 FG {X} n u r y = dfunext fe₀ (λ k → dfunext fe₀ (λ s → lemma k s))
  where
   f : {m n : ℕ} → m ＝ n → X m → X n
   f = transport X

   t : (k : ℕ) → ι k ＝ u → n ＝ k
   t k s = ℕ-to-ℕ∞-lc (r ∙ s ⁻¹)

   A :  (n k : ℕ) → n ＝ k → 𝓤₀ ̇
   A n k t = (u : ℕ∞) (r : ι n ＝ u) (s : ι k ＝ u) (y : X [ u ]) → f t (y n r) ＝ y k s

   φ : (n : ℕ) → A n n refl
   φ n = λ u r s y → ap (y n) (ℕ∞-is-set fe₀ r s)

   lemma : (k : ℕ) (s : ι k ＝ u) → f (ℕ-to-ℕ∞-lc (r ∙ s ⁻¹)) (y n r) ＝ y k s
   lemma k s = J A φ {n} {k} (t k s) u r s y

 GF : {X : ℕ → 𝓤₀ ̇ } (n : ℕ) (u : ℕ∞) (r : ι n ＝ u) (x : X n) → G {X} n u r (F n u r x) ＝ x
 GF {X} n u r x = s
  where
   f : {m n : ℕ} → m ＝ n → X m → X n
   f = transport X

   claim₀ : f (ℕ-to-ℕ∞-lc (r ∙ r ⁻¹)) x ＝ f (ℕ-to-ℕ∞-lc refl) x
   claim₀ = ap (λ - → f (ℕ-to-ℕ∞-lc -) x) (trans-sym' r)

   claim₁ : f (ℕ-to-ℕ∞-lc refl) x ＝ x
   claim₁ = ap (λ - → f - x) (ℕ-to-ℕ∞-lc-refl n)

   s : f (ℕ-to-ℕ∞-lc (r ∙ r ⁻¹)) x ＝ x
   s = claim₀ ∙ claim₁

\end{code}

 We now can show that the type X [ u ] is compact for every u : ℕ∞
 provided the type X n is compact for every n : ℕ. This is tricky,
 because a priory it is not enough to consider the cases ι n ＝ u and u ＝ ∞.

 The above isomorphism is used to prove the correctness of the witness
 y₀ below, which is easily defined (using one direction of the
 isomorphism):

\begin{code}

 extension-compact∙ : {X : ℕ → 𝓤₀ ̇ }
                    → ((n : ℕ) → is-compact∙(X n))
                    → (u : ℕ∞) → is-compact∙(X [ u ])
 extension-compact∙ {X} ε u p = y₀ , lemma
  where
   Y : 𝓤₀ ̇
   Y = X [ u ]
   -- ε : (n : ℕ) → compact∙(X n)
   -- u : ℕ∞
   -- p  : Y → ₂

   y₀ : Y
   y₀ n r = pr₁(ε n (p ∘ (F n u r)))

   lemma₁ : (n : ℕ) → ι n ＝ u → p y₀ ＝ ₁ → (y : Y) → p y ＝ ₁
   lemma₁ n r e = claim₃
    where
     claim₀ : (y : Y) → p (F n u r (G n u r y)) ＝ p y
     claim₀ y = ap p (FG n u r y)

     claim₁ : p (F n u r (G n u r y₀)) ＝ ₁ → (x : X n) → p (F n u r x) ＝ ₁
     claim₁ =  pr₂(ε n (p ∘ (F n u r)))

     claim₂ : (x : X n) → p (F n u r x) ＝ ₁
     claim₂ = claim₁ (claim₀ y₀ ∙ e)

     claim₃ : (y : Y) → p y ＝ ₁
     claim₃ y = (claim₀ y)⁻¹ ∙ claim₂ (G n u r y)

   lemma₂ : u ＝ ∞ → p y₀ ＝ ₁ → (y : Y) → p y ＝ ₁
   lemma₂ r e y = ap p (H u r y y₀) ∙ e

   lemma₁' : p y₀ ＝ ₁ → (y : Y) → p y ＝ ₀ → (n : ℕ) → ι n ≠ u
   lemma₁' e y s n r = zero-is-not-one (s ⁻¹ ∙ lemma₁ n r e y)

   lemma₂' : p y₀ ＝ ₁ → (y : Y) → p y ＝ ₀ → u ≠ ∞
   lemma₂' e y s r = zero-is-not-one (s ⁻¹ ∙ lemma₂ r e y)

   lemma : p y₀ ＝ ₁ → (y : Y) → p y ＝ ₁
   lemma r y = different-from-₀-equal-₁
                (λ s → lemma₂' r y s
                        (not-finite-is-∞ fe₀
                          (λ n q → lemma₁' r y s n (q ⁻¹))))

\end{code}

 Finally, we can show that the squashed sum of any sequence of
 compact sets is itself compact, as claimed above:

\begin{code}

 Σᴵ-compact∙ : {X : ℕ → 𝓤₀ ̇ } → ((n : ℕ) → is-compact∙(X n)) → is-compact∙(Σᴵ X)
 Σᴵ-compact∙ {X} f = Σ-is-compact∙ ℕ∞-compact∙ (extension-compact∙ {X} f)

\end{code}

 Added 2 May 2014.

 We show that the old and new squashed sums agree.

\begin{code}

 open import UF.EquivalenceExamples

 agreement-lemma : (X : ℕ → 𝓤₀ ̇ ) (u : ℕ∞)
                 → (X / ι) u ≃ Π (λ x → ι x ＝ u → X x)
 agreement-lemma X = 2nd-Π-extension-formula X ι

 agreement : (X : ℕ → 𝓤₀ ̇ ) → Σ¹ X ≃ Σᴵ X
 agreement X = Σ-cong (agreement-lemma X)

\end{code}
