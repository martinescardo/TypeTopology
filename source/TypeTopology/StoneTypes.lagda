Martin Escardo, 21st October 2026.

We discuss a notion of a Stone type and show as an example that ℕ∞ is
a Stone type, assuming ¬ WLPO. We also discuss that this cannot be
proved without such an assumption. Our definition of Stone type says
that a type is recovered from its boolean algebra of clopens by the
evaluation map. In [1] a type is instead called a Stone type when it
is equivalent to the spectrum of a countably presented boolean
algebra, so that their Stone types are included by ours by their
duality axiom, but not conversely, as discussed at the end of this
module.

[1] Cherubini, Coquand, Geerligs and Moeneclaey, "A Foundation for
    Synthetic Stone Duality", TYPES 2024, LIPIcs 336, pp. 3:1-3:20,
    2025, https://doi.org/10.4230/LIPIcs.TYPES.2024.3.

The clopens of a type X are the 𝟚-valued functions on X, as in the
module TypeTopology.TotallySeparated, and they form a boolean algebra
with the pointwise operations. We say that X is a Stone type if it is
equivalent, via the evaluation map, to the type of boolean algebra
homomorphisms from its clopens to the booleans. The evaluation map
sends a point to the homomorphism that evaluates clopens at it, and in
topological terms the homomorphisms are the ultrafilters of the
boolean algebra of clopens, so that being a Stone type says that every
ultrafilter is given as the clopen neighbourhoods of a unique point.

We first observe that the evaluation map is an embedding if and only
if X is totally separated. We then give a criterion for being a Stone
type and a few facts about it that hold for any type, namely that a
type equivalent to a Stone type is a Stone type, that the empty and
one-point types are Stone types, that Stone types are closed under
binary sums, and that a homomorphism is an evaluation as soon as it
gives the value ₁ to a clopen whose fiber over ₁ is a Stone type. We
also show that the finite types and the two-point type are Stone
types, as is every ¬¬-stable proposition.

We show that ℕ∞ is a Stone type if ¬ WLPO holds, using these facts,
which are also used in the module Ordinals.BrouwerCodesGiveStoneTypes
for the compact totally separated interpretation of the Brouwer
ordinal codes. We also characterize being a Stone type for ℕ∞ as the
condition that every homomorphism giving the value ₁ to all the upper
sets is the evaluation at infinity.

Finally, we establish two constructive taboos. That all Stone types
are Π-compact gives WEM, and that they are closed under Σ gives
¬¬ WLPO, so that if ¬ WLPO holds they are **not** closed under Σ. The
counterexample for the second uses that products indexed by a
proposition are Stone types, and in particular that P → 𝟚 is a Stone
type for a proposition P.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module TypeTopology.StoneTypes (fe : Fun-Ext) where

open import CoNaturals.Type
open import MLTT.Two-Properties
 renaming (max𝟚 to infixl 39 _∨₂_ ;
           min𝟚 to infixl 40 _∧₂_ ;
           complement to infix 41 ¬₂_)
open import Naturals.Order renaming (max to maxℕ)
open import Naturals.Properties
open import Notation.CanonicalMap
open import Notation.Order
open import Taboos.WLPO
open import TypeTopology.DecidabilityOfNonContinuity fe
open import TypeTopology.TotallySeparated
open import UF.Base
open import UF.ClassicalLogic
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.PropIndexedPiSigma
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

We now define the type C X of clopens of a type X and their boolean
operations pointwise. The order ≤̇ is the one of the module
TypeTopology.WeaklyCompactTypes, repeated here because that module is
parametrized by propositional truncations, which are not assumed here.

\begin{code}

C : 𝓤 ̇ → 𝓤 ̇
C X = X → 𝟚

module _ {X : 𝓤 ̇ } where

 infix  41 ¬̇_
 infixl 40 _∧̇_
 infixl 39 _∨̇_
 infix  30 _≤̇_

 0̇ : C X
 0̇ _ = ₀

 1̇ : C X
 1̇ _ = ₁

 _∧̇_ : C X → C X → C X
 (p ∧̇ q) x = p x ∧₂ q x

 _∨̇_ : C X → C X → C X
 (p ∨̇ q) x = p x ∨₂ q x

 ¬̇_ : C X → C X
 (¬̇ p) x = ¬₂ (p x)

 _≤̇_ : C X → C X → 𝓤 ̇
 p ≤̇ q = (x : X) → p x ≤ q x

\end{code}

A homomorphism of boolean algebras from the clopens of X to the
booleans is a map preserving the two constants and the two binary
operations.

\begin{code}

is-bhom : {X : 𝓤 ̇ } → (C X → 𝟚) → 𝓤 ̇
is-bhom {𝓤} {X} h = (h 0̇ ＝ ₀)
                  × (h 1̇ ＝ ₁)
                  × ((p q : C X) → h (p ∧̇ q) ＝ h p ∧₂ h q)
                  × ((p q : C X) → h (p ∨̇ q) ＝ h p ∨₂ h q)

being-bhom-is-prop : {X : 𝓤 ̇ } (h : C X → 𝟚) → is-prop (is-bhom h)
being-bhom-is-prop {𝓤} {X} h =
 ×₄-is-prop
  𝟚-is-set
  𝟚-is-set
  (Π₂-is-prop fe (λ p q → 𝟚-is-set))
  (Π₂-is-prop fe (λ p q → 𝟚-is-set))

\end{code}

Homomorphisms are monotone and preserve complements.

\begin{code}

module bhom-properties
        {X : 𝓤 ̇ }
        (h : C X → 𝟚)
        (i : is-bhom h)
       where

 preserves-₀ : h 0̇ ＝ ₀
 preserves-₀ = pr₁ i

 preserves-₁ : h 1̇ ＝ ₁
 preserves-₁ = pr₁ (pr₂ i)

 preserves-∧ : (p q : C X) → h (p ∧̇ q) ＝ h p ∧₂ h q
 preserves-∧ = pr₁ (pr₂ (pr₂ i))

 preserves-∨ : (p q : C X) → h (p ∨̇ q) ＝ h p ∨₂ h q
 preserves-∨ = pr₂ (pr₂ (pr₂ i))

 monotone : {p q : C X} → p ≤̇ q → h p ≤ h q
 monotone {p} {q} l = transport (λ - → - ≤ h q) II Lemma[minab≤₂b]
  where
   I : p ∧̇ q ＝ p
   I = dfunext fe (λ x → Lemma[a≤₂b→min𝟚ab＝a] (l x))

   II : h p ∧₂ h q ＝ h p
   II = h p ∧₂ h q ＝⟨ (preserves-∧ p q)⁻¹ ⟩
        h (p ∧̇ q)  ＝⟨ ap h I ⟩
        h p        ∎

 preserves-complement : (p : C X) → h (¬̇ p) ＝ ¬₂ (h p)
 preserves-complement p = 𝟚-equality-cases III IV
  where
   I : h p ∧₂ h (¬̇ p) ＝ ₀
   I = h p ∧₂ h (¬̇ p) ＝⟨ (preserves-∧ p (¬̇ p))⁻¹ ⟩
       h (p ∧̇ ¬̇ p)    ＝⟨ ap h i₀ ⟩
       h 0̇            ＝⟨ preserves-₀ ⟩
       ₀              ∎
    where
     i₀ : p ∧̇ ¬̇ p ＝ 0̇
     i₀ = dfunext fe (λ x → min𝟚-complement (p x))

   II : h p ∨₂ h (¬̇ p) ＝ ₁
   II = h p ∨₂ h (¬̇ p) ＝⟨ (preserves-∨ p (¬̇ p))⁻¹ ⟩
        h (p ∨̇ ¬̇ p)    ＝⟨ ap h i₁ ⟩
        h 1̇            ＝⟨ preserves-₁ ⟩
        ₁              ∎
    where
     i₁ : p ∨̇ ¬̇ p ＝ 1̇
     i₁ = dfunext fe (λ x → max𝟚-complement (p x))

   III : h p ＝ ₀ → h (¬̇ p) ＝ ¬₂ (h p)
   III e = h (¬̇ p)        ＝⟨refl⟩
           ₀ ∨₂ h (¬̇ p)   ＝⟨ ap (λ - → - ∨₂ h (¬̇ p)) (e ⁻¹) ⟩
           h p ∨₂ h (¬̇ p) ＝⟨ II ⟩
           ₁              ＝⟨refl⟩
           ¬₂ ₀           ＝⟨ ap (¬₂_) (e ⁻¹) ⟩
           ¬₂ (h p)       ∎

   IV : h p ＝ ₁ → h (¬̇ p) ＝ ¬₂ (h p)
   IV e = h (¬̇ p)        ＝⟨refl⟩
          ₁ ∧₂ h (¬̇ p)   ＝⟨ ap (λ - → - ∧₂ h (¬̇ p)) (e ⁻¹) ⟩
          h p ∧₂ h (¬̇ p) ＝⟨ I ⟩
          ₀              ＝⟨refl⟩
          ¬₂ ₁           ＝⟨ ap (¬₂_) (e ⁻¹) ⟩
          ¬₂ (h p)       ∎

\end{code}

We now define the type of homomorphisms on the clopens of X, the
evaluation map, and the notion of a Stone type.

\begin{code}

H : 𝓤 ̇ → 𝓤 ̇
H X = Σ h ꞉ (C X → 𝟚) , is-bhom h

η : (X : 𝓤 ̇ ) → X → H X
η X x = eval X x , refl , refl , (λ p q → refl) , (λ p q → refl)

is-stone-type : 𝓤 ̇ → 𝓤 ̇
is-stone-type X = is-equiv (η X)

being-stone-type-is-prop : (X : 𝓤 ̇ ) → is-prop (is-stone-type X)
being-stone-type-is-prop X = being-equiv-is-prop'' fe (η X)

\end{code}

The first component of η is the map eval X of the module
TypeTopology.TotallySeparated, which is an embedding precisely when X
is totally separated, and so the same holds for η, as the inclusion of
the homomorphisms into the maps on the clopens is an embedding.

\begin{code}

totally-separated-gives-η-is-embedding
 : {X : 𝓤 ̇ }
 → is-totally-separated X
 → is-embedding (η X)
totally-separated-gives-η-is-embedding {𝓤} {X} τ
 = factor-is-embedding (η X) pr₁
    (totally-separated-gives-totally-separated₂ fe τ)
    (pr₁-is-embedding being-bhom-is-prop)

η-is-embedding-gives-totally-separated
 : {X : 𝓤 ̇ }
 → is-embedding (η X)
 → is-totally-separated X
η-is-embedding-gives-totally-separated e
 = totally-separated₂-gives-totally-separated fe
    (∘-is-embedding e (pr₁-is-embedding being-bhom-is-prop))

η-is-embedding-iff-totally-separated
 : {X : 𝓤 ̇ }
 → is-embedding (η X) ↔ is-totally-separated X
η-is-embedding-iff-totally-separated
 = η-is-embedding-gives-totally-separated ,
    totally-separated-gives-η-is-embedding

\end{code}

We now show that the homomorphisms on the clopens of a Stone type are
evaluations, give a criterion for being a Stone type, and show that
Stone types are totally separated.

\begin{code}

homs-are-evaluations
 : {X : 𝓤 ̇ }
 → is-stone-type X
 → (h : C X → 𝟚)
 → is-bhom h
 → Σ v ꞉ X , ((p : C X) → h p ＝ p v)
homs-are-evaluations {𝓤} {X} ζ h i
 = x , II
 where
  x : X
  x = inverse (η X) ζ (h , i)

  I : η X x ＝ (h , i)
  I = inverses-are-sections (η X) ζ (h , i)

  II : (p : C X) → h p ＝ p x
  II p = (happly (ap pr₁ I) p)⁻¹

stone-criterion
 : {X : 𝓤 ̇ }
 → is-totally-separated X
 → ((h : C X → 𝟚) → is-bhom h → Σ v ꞉ X , ((p : C X) → h p ＝ p v))
 → is-stone-type X
stone-criterion {𝓤} {X} τ ψ
 = vv-equivs-are-equivs (η X) I
 where
  I : (σ : H X) → is-singleton (fiber (η X) σ)
  I (h , i) = II (ψ h i)
   where
    II : (Σ v ꞉ X , ((p : C X) → h p ＝ p v))
       → is-singleton (fiber (η X) (h , i))
    II (v , e) =
     pointed-props-are-singletons
      (v , to-subtype-＝ being-bhom-is-prop
            (dfunext fe (λ p → (e p)⁻¹)))
      (totally-separated-gives-η-is-embedding τ (h , i))

stone-types-are-totally-separated
 : {X : 𝓤 ̇ }
 → is-stone-type X
 → is-totally-separated X
stone-types-are-totally-separated {𝓤} {X} ζ
 = η-is-embedding-gives-totally-separated (equivs-are-embeddings (η X) ζ)

\end{code}

Stone types are closed under equivalence.

\begin{code}

equiv-to-stone-type
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → X ≃ Y
 → is-stone-type Y
 → is-stone-type X
equiv-to-stone-type {𝓤} {𝓥} {X} {Y} 𝕗 ζ
 = stone-criterion I II
 where
  f : X → Y
  f = ⌜ 𝕗 ⌝

  f-is-equiv : is-equiv f
  f-is-equiv = ⌜⌝-is-equiv 𝕗

  g : Y → X
  g = inverse f f-is-equiv

  gf : (x : X) → g (f x) ＝ x
  gf = inverses-are-retractions f f-is-equiv

  I : is-totally-separated X
  I = retract-of-totally-separated
       (g , f , gf)
       (stone-types-are-totally-separated ζ)

  II : (h : C X → 𝟚)
     → is-bhom h
     → Σ v ꞉ X , ((p : C X) → h p ＝ p v)
  II h i = IV (homs-are-evaluations ζ (λ q → h (q ∘ f)) III)
   where
    open bhom-properties h i

    III : is-bhom (λ q → h (q ∘ f))
    III = preserves-₀ ,
          preserves-₁ ,
          (λ q q' → preserves-∧ (q ∘ f) (q' ∘ f)) ,
          (λ q q' → preserves-∨ (q ∘ f) (q' ∘ f))

    IV : (Σ w ꞉ Y , ((q : C Y) → h (q ∘ f) ＝ q w))
       → Σ v ꞉ X , ((p : C X) → h p ＝ p v)
    IV (w , φ) = g w , V
     where
      V : (p : C X) → h p ＝ p (g w)
      V p = h p           ＝⟨ ap h (dfunext fe (λ x → ap p (gf x)⁻¹)) ⟩
            h (p ∘ g ∘ f) ＝⟨ φ (p ∘ g) ⟩
            p (g w)       ∎

\end{code}

The empty type is a Stone type.

\begin{code}

𝟘-is-stone-type : is-stone-type (𝟘 {𝓤})
𝟘-is-stone-type {𝓤} = vv-equivs-are-equivs (η 𝟘) I
 where
  I : (σ : H (𝟘 {𝓤})) → is-singleton (fiber (η 𝟘) σ)
  I (h , i) = zero-is-one-elim III
   where
    open bhom-properties h i

    II : 0̇ ＝ 1̇
    II = dfunext fe (λ x → 𝟘-elim x)

    III : ₀ ＝ ₁
    III = ₀   ＝⟨ preserves-₀ ⁻¹ ⟩
          h 0̇ ＝⟨ ap h II ⟩
          h 1̇ ＝⟨ preserves-₁ ⟩
          ₁   ∎

\end{code}

The one-point type is a Stone type.

\begin{code}

𝟙-is-stone-type : is-stone-type (𝟙 {𝓤})
𝟙-is-stone-type {𝓤} =
 stone-criterion 𝟙-is-totally-separated I
 where
  I : (h : C (𝟙 {𝓤}) → 𝟚)
    → is-bhom h
    → Σ v ꞉ 𝟙 , ((p : C 𝟙) → h p ＝ p v)
  I h i = ⋆ , II
   where
    open bhom-properties h i

    II : (p : C (𝟙 {𝓤})) → h p ＝ p ⋆
    II p = 𝟚-equality-cases III IV
     where
      III : p ⋆ ＝ ₀ → h p ＝ p ⋆
      III e = h p ＝⟨ ap h (dfunext fe (λ _ → e)) ⟩
              h 0̇ ＝⟨ preserves-₀ ⟩
              ₀   ＝⟨ e ⁻¹ ⟩
              p ⋆ ∎

      IV : p ⋆ ＝ ₁ → h p ＝ p ⋆
      IV e = h p ＝⟨ ap h (dfunext fe (λ _ → e)) ⟩
             h 1̇ ＝⟨ preserves-₁ ⟩
             ₁   ＝⟨ e ⁻¹ ⟩
             p ⋆ ∎

\end{code}

We now give a criterion for a homomorphism to be given by evaluation.

\begin{code}

hom-is-evaluation-criterion
 : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
   (q : C X)
   (j : A → X)
   (σ : (x : X) → q x ＝ ₁ → A)
 → ((x : X) (d : q x ＝ ₁) → j (σ x d) ＝ x)
 → is-stone-type A
 → (h : C X → 𝟚)
 → is-bhom h
 → h q ＝ ₁
 → Σ a ꞉ A , ((p : C X) → h p ＝ p (j a))
hom-is-evaluation-criterion {𝓤} {𝓥} {X} {A} q j σ jσ ζ h i e
 = γ (homs-are-evaluations ζ (h ∘ ext) ext-is-bhom)
 where
  open bhom-properties h i

  decide : (x : X) → is-decidable (q x ＝ ₁)
  decide x = 𝟚-is-discrete (q x) ₁

  ext' : C A → (x : X) → is-decidable (q x ＝ ₁) → 𝟚
  ext' r x (inl d) = r (σ x d)
  ext' r x (inr _) = ₀

  ext : C A → C X
  ext r x = ext' r x (decide x)

  ext-₀ : ext 0̇ ＝ 0̇
  ext-₀ = dfunext fe (λ x → I x (decide x))
   where
    I : (x : X) (c : is-decidable (q x ＝ ₁)) → ext' 0̇ x c ＝ ₀
    I x (inl d) = refl
    I x (inr _) = refl

  ext-₁ : ext 1̇ ＝ q
  ext-₁ = dfunext fe (λ x → I x (decide x))
   where
    I : (x : X) (c : is-decidable (q x ＝ ₁)) → ext' 1̇ x c ＝ q x
    I x (inl d) = d ⁻¹
    I x (inr ν) = (different-from-₁-equal-₀ ν)⁻¹

  ext-∧ : (r s : C A) → ext (r ∧̇ s) ＝ ext r ∧̇ ext s
  ext-∧ r s = dfunext fe (λ x → I x (decide x))
   where
    I : (x : X) (c : is-decidable (q x ＝ ₁))
      → ext' (r ∧̇ s) x c ＝ ext' r x c ∧₂ ext' s x c
    I x (inl d) = refl
    I x (inr _) = refl

  ext-∨ : (r s : C A) → ext (r ∨̇ s) ＝ ext r ∨̇ ext s
  ext-∨ r s = dfunext fe (λ x → I x (decide x))
   where
    I : (x : X) (c : is-decidable (q x ＝ ₁))
      → ext' (r ∨̇ s) x c ＝ ext' r x c ∨₂ ext' s x c
    I x (inl d) = refl
    I x (inr _) = refl

  ext-is-bhom : is-bhom (h ∘ ext)
  ext-is-bhom = I , II , III , IV
   where
    I : h (ext 0̇) ＝ ₀
    I = h (ext 0̇) ＝⟨ ap h ext-₀ ⟩
        h 0̇       ＝⟨ preserves-₀ ⟩
        ₀         ∎

    II : h (ext 1̇) ＝ ₁
    II = h (ext 1̇) ＝⟨ ap h ext-₁ ⟩
         h q       ＝⟨ e ⟩
         ₁         ∎

    III : (r s : C A) → h (ext (r ∧̇ s)) ＝ h (ext r) ∧₂ h (ext s)
    III r s = h (ext (r ∧̇ s))        ＝⟨ ap h (ext-∧ r s) ⟩
              h (ext r ∧̇ ext s)      ＝⟨ preserves-∧ (ext r) (ext s) ⟩
              h (ext r) ∧₂ h (ext s) ∎

    IV : (r s : C A) → h (ext (r ∨̇ s)) ＝ h (ext r) ∨₂ h (ext s)
    IV r s = h (ext (r ∨̇ s))        ＝⟨ ap h (ext-∨ r s) ⟩
             h (ext r ∨̇ ext s)      ＝⟨ preserves-∨ (ext r) (ext s) ⟩
             h (ext r) ∨₂ h (ext s) ∎

  γ : (Σ a ꞉ A , ((r : C A) → h (ext r) ＝ r a))
    → Σ a ꞉ A , ((p : C X) → h p ＝ p (j a))
  γ (a , φ) = a , δ
   where
    δ : (p : C X) → h p ＝ p (j a)
    δ p = 𝟚-equality-cases I II
     where
      I : p (j a) ＝ ₀ → h p ＝ p (j a)
      I d = h p     ＝⟨ V ⟩
            ₀       ＝⟨ d ⁻¹ ⟩
            p (j a) ∎
       where
        III : p ≤̇ ext (p ∘ j) ∨̇ ¬̇ q
        III x = ≤₂-criterion (v (decide x))
         where
          v : (c : is-decidable (q x ＝ ₁))
            → p x ＝ ₁ → ext' (p ∘ j) x c ∨₂ ¬₂ (q x) ＝ ₁
          v (inl d) s = max𝟚-lemma-converse (inl vi)
           where
            vi : p (j (σ x d)) ＝ ₁
            vi = p (j (σ x d)) ＝⟨ ap p (jσ x d) ⟩
                 p x           ＝⟨ s ⟩
                 ₁             ∎
          v (inr ν) s = max𝟚-lemma-converse
                         (inr (ap ¬₂_ (different-from-₁-equal-₀ ν)))

        IV : h (ext (p ∘ j) ∨̇ ¬̇ q) ＝ ₀
        IV = h (ext (p ∘ j) ∨̇ ¬̇ q)      ＝⟨ preserves-∨ (ext (p ∘ j)) (¬̇ q) ⟩
             h (ext (p ∘ j)) ∨₂ h (¬̇ q) ＝⟨ ap₂ _∨₂_ v vi ⟩
             ₀ ∨₂ ₀                     ＝⟨refl⟩
             ₀                          ∎
         where
          v : h (ext (p ∘ j)) ＝ ₀
          v = h (ext (p ∘ j)) ＝⟨ φ (p ∘ j) ⟩
              p (j a)         ＝⟨ d ⟩
              ₀               ∎

          vi : h (¬̇ q) ＝ ₀
          vi = h (¬̇ q)  ＝⟨ preserves-complement q ⟩
               ¬₂ (h q) ＝⟨ ap ¬₂_ e ⟩
               ¬₂ ₁     ＝⟨refl⟩
               ₀        ∎

        V : h p ＝ ₀
        V = ₀-minimal (transport (λ - → h p ≤ -) IV (monotone III))

      II : p (j a) ＝ ₁ → h p ＝ p (j a)
      II d = h p     ＝⟨ ₁-maximal IV ⟩
             ₁       ＝⟨ d ⁻¹ ⟩
             p (j a) ∎
       where
        III : ext (p ∘ j) ≤̇ p
        III x = ≤₂-criterion (v (decide x))
         where
          v : (c : is-decidable (q x ＝ ₁)) → ext' (p ∘ j) x c ＝ ₁ → p x ＝ ₁
          v (inl d) s = p x           ＝⟨ (ap p (jσ x d))⁻¹ ⟩
                        p (j (σ x d)) ＝⟨ s ⟩
                        ₁             ∎
          v (inr _) s = zero-is-one-elim s

        IV : ₁ ≤ h p
        IV = transport (λ - → - ≤ h p) v (monotone III)
         where
          v : h (ext (p ∘ j)) ＝ ₁
          v = h (ext (p ∘ j)) ＝⟨ φ (p ∘ j) ⟩
              p (j a)         ＝⟨ d ⟩
              ₁               ∎

\end{code}

Stone types are closed under binary sums.

\begin{code}

+-is-stone-type
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → is-stone-type X
 → is-stone-type Y
 → is-stone-type (X + Y)
+-is-stone-type {𝓤} {𝓥} {X} {Y} ζ₀ ζ₁
 = stone-criterion
    (+-totally-separated X Y
      (stone-types-are-totally-separated ζ₀)
      (stone-types-are-totally-separated ζ₁))
    I
 where
  q : C (X + Y)
  q (inl _) = ₁
  q (inr _) = ₀

  σ₀ : (z : X + Y) → q z ＝ ₁ → X
  σ₀ (inl x) d = x
  σ₀ (inr y) d = zero-is-one-elim d

  σ₁ : (z : X + Y) → (¬̇ q) z ＝ ₁ → Y
  σ₁ (inl x) d = zero-is-one-elim d
  σ₁ (inr y) d = y

  jσ₀ : (z : X + Y) (d : q z ＝ ₁) → inl (σ₀ z d) ＝ z
  jσ₀ (inl x) d = refl
  jσ₀ (inr y) d = zero-is-one-elim d

  jσ₁ : (z : X + Y) (d : (¬̇ q) z ＝ ₁) → inr (σ₁ z d) ＝ z
  jσ₁ (inl x) d = zero-is-one-elim d
  jσ₁ (inr y) d = refl

  I : (h : C (X + Y) → 𝟚)
    → is-bhom h
    → Σ v ꞉ X + Y , ((p : C (X + Y)) → h p ＝ p v)
  I h i = 𝟚-equality-cases II III
   where
    open bhom-properties h i

    II : h q ＝ ₀ → Σ v ꞉ X + Y , ((p : C (X + Y)) → h p ＝ p v)
    II d = V (hom-is-evaluation-criterion (¬̇ q) inr σ₁ jσ₁ ζ₁ h i IV)
     where
      IV : h (¬̇ q) ＝ ₁
      IV = h (¬̇ q)  ＝⟨ preserves-complement q ⟩
           ¬₂ (h q) ＝⟨ ap ¬₂_ d ⟩
           ¬₂ ₀     ＝⟨refl⟩
           ₁        ∎

      V : (Σ a ꞉ Y , ((p : C (X + Y)) → h p ＝ p (inr a)))
        → Σ v ꞉ X + Y , ((p : C (X + Y)) → h p ＝ p v)
      V (a , φ) = inr a , φ

    III : h q ＝ ₁ → Σ v ꞉ X + Y , ((p : C (X + Y)) → h p ＝ p v)
    III d = IV (hom-is-evaluation-criterion q inl σ₀ jσ₀ ζ₀ h i d)
     where
      IV : (Σ a ꞉ X , ((p : C (X + Y)) → h p ＝ p (inl a)))
         → Σ v ꞉ X + Y , ((p : C (X + Y)) → h p ＝ p v)
      IV (a , φ) = inl a , φ

\end{code}

The standard finite types are Stone types.

\begin{code}

open import Fin.Bishop
open import Fin.Type

Fin-is-stone-type : (n : ℕ) → is-stone-type (Fin n)
Fin-is-stone-type 0        = 𝟘-is-stone-type
Fin-is-stone-type (succ n) =
 +-is-stone-type
  (Fin-is-stone-type n)
  (𝟙-is-stone-type {𝓤₀})

finite-linear-orders-are-stone-types
 : {X : 𝓤 ̇ }
 → finite-linear-order X
 → is-stone-type X
finite-linear-orders-are-stone-types (n , 𝕗)
 = equiv-to-stone-type 𝕗 (Fin-is-stone-type n)

\end{code}

The two-point type is a Stone type.

\begin{code}

𝟚-is-stone-type : is-stone-type 𝟚
𝟚-is-stone-type =
 equiv-to-stone-type
  (𝟚-≃-𝟙+𝟙 {𝓤₀})
  (+-is-stone-type
    (𝟙-is-stone-type {𝓤₀})
    (𝟙-is-stone-type {𝓤₀}))

\end{code}

A ¬¬-stable proposition is a Stone type.

\begin{code}

¬¬-stable-props-are-stone-types
 : {P : 𝓤 ̇ }
 → is-prop P
 → ¬¬-stable P
 → is-stone-type P
¬¬-stable-props-are-stone-types {𝓤} {P} P-is-prop P-is-¬¬-stable
 = stone-criterion I II
 where
  I : is-totally-separated P
  I {x} {y} _ = P-is-prop x y

  II : (h : C P → 𝟚)
     → is-bhom h
     → Σ v ꞉ P , ((q : C P) → h q ＝ q v)
  II h i = p , VI
   where
    open bhom-properties h i

    III : ¬ P → 0̇ ＝ 1̇
    III ν = dfunext fe (λ p → 𝟘-elim (ν p))

    IV : ¬¬ P
    IV ν = zero-is-one-elim
            (₀   ＝⟨ preserves-₀ ⁻¹ ⟩
             h 0̇ ＝⟨ ap h (III ν) ⟩
             h 1̇ ＝⟨ preserves-₁ ⟩
             ₁   ∎)

    p : P
    p = P-is-¬¬-stable IV

    V : (q : C P) (b : 𝟚) → q p ＝ b → q ＝ (λ _ → b)
    V q b e = dfunext fe v
     where
      v : (p' : P) → q p' ＝ b
      v p' = q p' ＝⟨ ap q (P-is-prop p' p) ⟩
             q p  ＝⟨ e ⟩
             b    ∎

    VI : (q : C P) → h q ＝ q p
    VI q = 𝟚-equality-cases v vi
     where
      v : q p ＝ ₀ → h q ＝ q p
      v e = h q ＝⟨ ap h (V q ₀ e) ⟩
            h 0̇ ＝⟨ preserves-₀ ⟩
            ₀   ＝⟨ e ⁻¹ ⟩
            q p ∎

      vi : q p ＝ ₁ → h q ＝ q p
      vi e = h q ＝⟨ ap h (V q ₁ e) ⟩
             h 1̇ ＝⟨ preserves-₁ ⟩
             ₁   ＝⟨ e ⁻¹ ⟩
             q p ∎

\end{code}

We now turn to ℕ∞. For a natural number n, the clopen ↑ n is the upper
set of n in ℕ∞.

\begin{code}

infix 50 ↑_

↑_ : ℕ → C ℕ∞
(↑ n) x = ι x n

\end{code}

For a natural number k, the clopen `singleton k` is the characteristic
function of the singleton subset containing the point ι k.

\begin{code}

singleton : ℕ → C ℕ∞
singleton 0        = ¬̇ ↑ 0
singleton (succ j) = ↑ j ∧̇ ¬̇ ↑ (succ j)

singleton-property₀ : (k : ℕ) (x : ℕ∞) → singleton k x ＝ ₁ → x ＝ ι k
singleton-property₀ 0 x e = is-Zero-equal-Zero fe (complement-lc (ι x 0) ₀ e)
singleton-property₀ (succ j) x e =
 Succ-criterion fe
  (Lemma[min𝟚ab＝₁→a＝₁] e)
  (complement-lc (ι x (succ j)) ₀ (Lemma[min𝟚ab＝₁→b＝₁] e))

singleton-property₁ : (k : ℕ) → singleton k (ι k) ＝ ₁
singleton-property₁ 0        = ap (¬₂_) (ℕ-to-ℕ∞-diagonal₀ 0)
singleton-property₁ (succ j) =
 Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
  (ℕ-to-ℕ∞-diagonal₁ j)
  (ap (¬₂_) (ℕ-to-ℕ∞-diagonal₀ (succ j)))

\end{code}

A modulus of a clopen of ℕ∞ is a point beyond which it has the same
value it has at infinity. This is the notion of continuity of the
module TypeTopology.DecidabilityOfNonContinuity, formulated with the
order of ℕ rather than with maximum, and for 𝟚-valued rather than
ℕ-valued functions.

\begin{code}

_is-modulus-of_ : ℕ → C ℕ∞ → 𝓤₀ ̇
m is-modulus-of p = (n : ℕ) → m ≤ n → p (ι n) ＝ p ∞

has-modulus : C ℕ∞ → 𝓤₀ ̇
has-modulus p = Σ m ꞉ ℕ , m is-modulus-of p

¬WLPO-gives-¬¬-has-modulus : ¬ WLPO → (p : C ℕ∞) → ¬¬ has-modulus p
¬WLPO-gives-¬¬-has-modulus nwlpo p = ¬¬-functor II I
 where
  g : 𝟚 → ℕ
  g ₀ = 0
  g ₁ = 1

  g-lc : {b c : 𝟚} → g b ＝ g c → b ＝ c
  g-lc {₀} {₀} r = refl
  g-lc {₀} {₁} r = 𝟘-elim (zero-not-positive 0 r)
  g-lc {₁} {₀} r = 𝟘-elim (zero-not-positive 0 (r ⁻¹))
  g-lc {₁} {₁} r = refl

  f : ℕ∞ → ℕ
  f = g ∘ p

  I : ¬¬ continuous f
  I = ¬WLPO-gives-all-functions-are-not-not-continuous nwlpo f

  II : continuous f → has-modulus p
  II (m , ψ) = m , III
   where
    III : (n : ℕ) → m ≤ n → p (ι n) ＝ p ∞
    III n l = g-lc (f (ι n)             ＝⟨ ap f (IV ⁻¹) ⟩
                    f (max (ι m) (ι n)) ＝⟨ ψ n ⟩
                    f ∞                 ∎)
     where
      IV : max (ι m) (ι n) ＝ ι n
      IV = max (ι m) (ι n) ＝⟨ (max-fin fe m n)⁻¹ ⟩
           ι (maxℕ m n)    ＝⟨ ap ℕ-to-ℕ∞ (max-ord→ m n l) ⟩
           ι n             ∎

\end{code}

Given a homomorphism h of the clopens of ℕ∞ into the booleans, the
sequence of values of h at the upper sets is decreasing, and so it is
an element u of ℕ∞, at which h agrees with the evaluation on the upper
sets by construction.

\begin{code}

module bhom-on-ℕ∞
        (h : C ℕ∞ → 𝟚)
        (i : is-bhom h)
       where

 open bhom-properties h i

 private
  α : ℕ → 𝟚
  α n = h (↑ n)

  α-is-decreasing : is-decreasing α
  α-is-decreasing n = monotone I
   where
    I : ↑ (succ n) ≤̇ ↑ n
    I (β , d) = d n

 u : ℕ∞
 u = (α , α-is-decreasing)

 h-agrees-with-u-at-upper-sets : (n : ℕ) → h (↑ n) ＝ (↑ n) u
 h-agrees-with-u-at-upper-sets n = refl

\end{code}

If u is finite, say u ＝ ι k, then h gives the value ₁ to singleton k,
which is ₁ only at the point ι k. So the criterion above applies
with the one-point type, and h agrees with the evaluation at u on all
clopens.

\begin{code}

 private
  h-at-singleton : (k : ℕ) → u ＝ ι k → h (singleton k) ＝ ₁
  h-at-singleton 0 e =
   h (singleton 0) ＝⟨ preserves-complement (↑ 0) ⟩
   ¬₂ (α 0)        ＝⟨ ap (¬₂_) I ⟩
   ¬₂ ₀            ＝⟨refl⟩
   ₁               ∎
    where
     I : α 0 ＝ ₀
     I = α 0       ＝⟨ ap (λ - → ι - 0) e ⟩
         ι (ι 0) 0 ＝⟨ ℕ-to-ℕ∞-diagonal₀ 0 ⟩
         ₀         ∎
  h-at-singleton (succ j) e =
   h (singleton (succ j))  ＝⟨ i₀ ⟩
   α j ∧₂ h (¬̇ ↑ (succ j)) ＝⟨ i₁ ⟩
   α j ∧₂ ¬₂ (α (succ j))  ＝⟨ i₂ ⟩
   ₁ ∧₂ ¬₂ ₀               ＝⟨refl⟩
   ₁                       ∎
    where
     i₀ = preserves-∧ (↑ j) (¬̇ ↑ (succ j))
     i₁ = ap (λ - → α j ∧₂ -) (preserves-complement (↑ (succ j)))

     I : α j ＝ ₁
     I = α j              ＝⟨ ap (λ - → ι - j) e ⟩
         ι (ι (succ j)) j ＝⟨ ℕ-to-ℕ∞-diagonal₁ j ⟩
         ₁                ∎

     II : α (succ j) ＝ ₀
     II = α (succ j)              ＝⟨ ap (λ - → ι - (succ j)) e ⟩
          ι (ι (succ j)) (succ j) ＝⟨ ℕ-to-ℕ∞-diagonal₀ (succ j) ⟩
          ₀                       ∎

     i₂ = ap₂ (λ - -' → - ∧₂ ¬₂ -') I II

 h-at-finite : (k : ℕ) → u ＝ ι k → (p : C ℕ∞) → h p ＝ p u
 h-at-finite k e p = I (hom-is-evaluation-criterion
                         (singleton k)
                         (λ _ → ι k)
                         (λ _ _ → ⋆)
                         (λ x d → (singleton-property₀ k x d)⁻¹)
                         (𝟙-is-stone-type {𝓤₀})
                         h i
                         (h-at-singleton k e))
  where
   I : (Σ a ꞉ 𝟙 {𝓤₀} , ((q : C ℕ∞) → h q ＝ q (ι k)))
     → h p ＝ p u
   I (a , φ) = h p     ＝⟨ φ p ⟩
               p (ι k) ＝⟨ (ap p e)⁻¹ ⟩
               p u     ∎

 not-evaluation-gives-u-is-∞ : (p : C ℕ∞) → h p ≠ p u → u ＝ ∞
 not-evaluation-gives-u-is-∞ p ν =
  not-finite-is-∞ fe (λ k e → ν (h-at-finite k e p))

\end{code}

If u is the point at infinity, then h gives the value ₁ to every upper
set, and so does a homomorphism that is not the evaluation at u. For
such a homomorphism, a modulus of a clopen decides the value that h
gives to that clopen.

\begin{code}

 h-at-upper-sets : u ＝ ∞ → (n : ℕ) → h (↑ n) ＝ ₁
 h-at-upper-sets e n = ap (λ - → ι - n) e

 not-evaluation-gives-₁-at-upper-sets
  : (p : C ℕ∞) → h p ≠ p u → (n : ℕ) → h (↑ n) ＝ ₁
 not-evaluation-gives-₁-at-upper-sets p ν
  = h-at-upper-sets (not-evaluation-gives-u-is-∞ p ν)

 private
  h-at-∞-₁ : u ＝ ∞
           → (p : C ℕ∞) (m : ℕ)
           → m is-modulus-of p
           → p ∞ ＝ ₁
           → h p ＝ ₁
  h-at-∞-₁ e p m φ r = ≤₂-criterion-converse
                        (monotone II)
                        (h-at-upper-sets e m)
   where
    I : (x : ℕ∞) → ((¬̇ ↑ m) ∨̇ p) x ＝ ₁
    I = ℕ∞-𝟚-density fe III (max𝟚-lemma-converse (inr r))
     where
      III : (n : ℕ) → ((¬̇ ↑ m) ∨̇ p) (ι n) ＝ ₁
      III n = 𝟚-equality-cases
               (λ (s : ι (ι n) m ＝ ₀)
                   → max𝟚-lemma-converse (inl (ap (¬₂_) s)))
               (λ (s : ι (ι n) m ＝ ₁)
                   → max𝟚-lemma-converse (inr (IV s)))
       where
        IV : ι (ι n) m ＝ ₁ → p (ι n) ＝ ₁
        IV s = p (ι n) ＝⟨ φ n (<-coarser-than-≤ m n (⊏-gives-< m n s)) ⟩
                p ∞     ＝⟨ r ⟩
                ₁       ∎

    II : ↑ m ≤̇ p
    II x = ≤₂-criterion III
     where
      III : (↑ m) x ＝ ₁ → p x ＝ ₁
      III s = p x                 ＝⟨refl⟩
              ₀ ∨₂ p x            ＝⟨ IV ⟩
              ¬₂ ((↑ m) x) ∨₂ p x ＝⟨ I x ⟩
              ₁                   ∎
       where
        IV = ap (λ - → ¬₂ - ∨₂ p x) (s ⁻¹)

 h-at-∞ : u ＝ ∞
        → (p : C ℕ∞) (m : ℕ)
        → m is-modulus-of p
        → h p ＝ p u
 h-at-∞ e p m φ = 𝟚-equality-cases II III
  where
   I : p u ＝ p ∞
   I = ap p e

   II : p ∞ ＝ ₀ → h p ＝ p u
   II r = h p ＝⟨ V ⟩
          ₀   ＝⟨ r ⁻¹ ⟩
          p ∞ ＝⟨ I ⁻¹ ⟩
          p u ∎
    where
     IV : h (¬̇ p) ＝ ₁
     IV = h-at-∞-₁ e (¬̇ p) m
           (λ n l → ap (¬₂_) (φ n l))
           (ap (¬₂_) r)

     V : h p ＝ ₀
     V = complement-lc (h p) ₀ VI
      where
       VI : ¬₂ (h p) ＝ ¬₂ ₀
       VI = ¬₂ (h p) ＝⟨ (preserves-complement p)⁻¹ ⟩
            h (¬̇ p)  ＝⟨ IV ⟩
            ₁        ＝⟨refl⟩
            ¬₂ ₀     ∎

   III : p ∞ ＝ ₁ → h p ＝ p u
   III r = h p ＝⟨ h-at-∞-₁ e p m φ r ⟩
           ₁   ＝⟨ r ⁻¹ ⟩
           p ∞ ＝⟨ I ⁻¹ ⟩
           p u ∎

\end{code}

Putting the two cases together, h is the evaluation at u as soon as it
is the evaluation at ∞ when u is ∞, which is the following criterion.
If ¬ WLPO holds then the criterion applies.

\begin{code}

 h-is-evaluation-criterion
  : (u ＝ ∞ → (p : C ℕ∞) → h p ＝ p ∞)
  → (p : C ℕ∞) → h p ＝ p u
 h-is-evaluation-criterion ψ p
  = 𝟚-is-¬¬-separated (h p) (p u) I
  where
   I : ¬¬ (h p ＝ p u)
   I ν = ν (h p ＝⟨ ψ II p ⟩
            p ∞ ＝⟨ (ap p II)⁻¹ ⟩
            p u ∎)
    where
     II : u ＝ ∞
     II = not-evaluation-gives-u-is-∞ p ν

 h-is-evaluation : ¬ WLPO → (p : C ℕ∞) → h p ＝ p u
 h-is-evaluation nwlpo = h-is-evaluation-criterion I
  where
   I : u ＝ ∞ → (p : C ℕ∞) → h p ＝ p ∞
   I e p = 𝟚-is-¬¬-separated (h p) (p ∞) II
    where
     II : ¬¬ (h p ＝ p ∞)
     II ν = ¬WLPO-gives-¬¬-has-modulus nwlpo p III
      where
       III : ¬ has-modulus p
       III (m , φ) = ν (h p ＝⟨ h-at-∞ e p m φ ⟩
                        p u ＝⟨ ap p e ⟩
                        p ∞ ∎)

\end{code}

The criterion above, applied to the total separatedness of ℕ∞, now
gives that ℕ∞ is a Stone type if ¬ WLPO holds.

\begin{code}

ℕ∞-is-stone-type : ¬ WLPO → is-stone-type ℕ∞
ℕ∞-is-stone-type nwlpo =
 stone-criterion (ℕ∞-is-totally-separated fe) I
 where
  I : (h : C ℕ∞ → 𝟚) (i : is-bhom h)
    → Σ v ꞉ ℕ∞ , ((p : C ℕ∞) → h p ＝ p v)
  I h i = u , h-is-evaluation nwlpo
   where
    open bhom-on-ℕ∞ h i

\end{code}

ℕ∞ is a Stone type precisely when every homomorphism that gives the
value ₁ to all the upper sets is the evaluation at ∞.

\begin{code}

Homs-Containing-All-Upper-Sets-Are-Evaluation-At-∞ : 𝓤₀ ̇
Homs-Containing-All-Upper-Sets-Are-Evaluation-At-∞ =
   (h : C ℕ∞ → 𝟚)
 → is-bhom h
 → ((n : ℕ) → h (↑ n) ＝ ₁)
 → (p : C ℕ∞) → h p ＝ p ∞

stone-gives-evaluation-at-∞
 : is-stone-type ℕ∞
 → Homs-Containing-All-Upper-Sets-Are-Evaluation-At-∞
stone-gives-evaluation-at-∞ ζ h i t
 = I (homs-are-evaluations ζ h i)
 where
  I : (Σ v ꞉ ℕ∞ , ((q : C ℕ∞) → h q ＝ q v))
    → (p : C ℕ∞) → h p ＝ p ∞
  I (v , φ) p = h p ＝⟨ φ p ⟩
                p v ＝⟨ ap p II ⟩
                p ∞ ∎
   where
    II : v ＝ ∞
    II = ℕ∞-to-ℕ→𝟚-lc fe (dfunext fe III)
     where
      III : (n : ℕ) → ι v n ＝ ι ∞ n
      III n = ι v n   ＝⟨ (φ (↑ n))⁻¹ ⟩
              h (↑ n) ＝⟨ t n ⟩
              ₁       ∎

evaluation-at-∞-gives-stone
 : Homs-Containing-All-Upper-Sets-Are-Evaluation-At-∞
 → is-stone-type ℕ∞
evaluation-at-∞-gives-stone φ
 = stone-criterion (ℕ∞-is-totally-separated fe) I
 where
  I : (h : C ℕ∞ → 𝟚) (i : is-bhom h)
    → Σ v ꞉ ℕ∞ , ((p : C ℕ∞) → h p ＝ p v)
  I h i = u , h-is-evaluation-criterion (λ e → φ h i (h-at-upper-sets e))
   where
    open bhom-on-ℕ∞ h i

ℕ∞-is-stone-type-iff-evaluation-at-∞
 : is-stone-type ℕ∞
 ↔ Homs-Containing-All-Upper-Sets-Are-Evaluation-At-∞
ℕ∞-is-stone-type-iff-evaluation-at-∞
 = stone-gives-evaluation-at-∞ ,
   evaluation-at-∞-gives-stone

\end{code}

That ℕ∞ is a Stone type is not provable without a hypothesis such as
¬ WLPO. With choice there is a nonprincipal ultrafilter on ℕ, which is
a homomorphism on the clopens of ℕ∞ that is not the evaluation at any
point, so that ℕ∞ is not a Stone type in such a model.

That ¬ WLPO holds is sufficient for ℕ∞ to be a Stone type, but it is not
necessary. It is consistent with ZF that every ultrafilter on every set
is principal, by a model of Blass [2] where the ultrafilters on ℕ are
all principal. In the model of Blass excluded middle holds, and hence so
does WLPO, and ℕ∞ is the set ℕ + 𝟙. Every subset of ℕ + 𝟙 is decidable,
so the clopens of ℕ∞ are the characteristic functions of all the subsets
of ℕ + 𝟙, and the homomorphisms on the clopens are the ultrafilters on
ℕ + 𝟙, which are all evaluations. So ℕ∞ is a Stone type in that model.

[2] Blass, "A model without ultrafilters", Bull. Acad. Polon. Sci. 25,
    1977, pp. 329-331, which extends a model of Feferman, "Some
    applications of the notions of forcing and generic sets",
    Fundamenta Mathematicae 56, 1964, pp. 325-345,
    https://doi.org/10.4064/fm-56-3-325-345.


The module Ordinals.BrouwerCodesGiveStoneTypes generalizes the above
result for ℕ∞, again assuming that ¬ WLPO holds, to the compact
totally separated interpretation of the Brouwer ordinal codes, of
which ℕ∞ is the interpretation of the code for the first infinite
ordinal.


We now show that if all Stone types are Π-compact then WEM holds. A
Π-compact type has decidable emptiness, by the decision for the
constant clopen 0̇, and the negation ¬ Q of a proposition Q is a
¬¬-stable proposition and hence a Stone type, so that the emptiness of
¬ Q, which is ¬¬ Q, would be decidable for every proposition Q. We
repeat the definition of Π-compactness from the module
TypeTopology.WeaklyCompactTypes, which is parametrized by
propositional truncations, which we don't assume here.

\begin{code}

is-Π-compact : 𝓤 ̇ → 𝓤 ̇
is-Π-compact X = (p : C X) → is-decidable ((x : X) → p x ＝ ₁)

Π-compactness-gives-decidable-emptiness
 : {X : 𝓤 ̇ }
 → is-Π-compact X
 → is-decidable (¬ X)
Π-compactness-gives-decidable-emptiness {𝓤} {X} c
 = I (c 0̇)
 where
  I : is-decidable ((x : X) → 0̇ x ＝ ₁) → is-decidable (¬ X)
  I (inl φ) = inl (λ x → zero-is-one-elim (φ x))
  I (inr ν) = inr (λ (f : ¬ X) → ν (λ x → 𝟘-elim (f x)))

Stone-Types-Are-Π-Compact : (𝓤 : Universe) → 𝓤 ⁺ ̇
Stone-Types-Are-Π-Compact 𝓤 = (X : 𝓤 ̇ ) → is-stone-type X → is-Π-compact X

Π-compactness-of-stone-types-gives-WEM
 : Stone-Types-Are-Π-Compact 𝓤
 → WEM 𝓤
Π-compactness-of-stone-types-gives-WEM c Q Q-is-prop
 = I (Π-compactness-gives-decidable-emptiness
      (c (¬ Q)
         (¬¬-stable-props-are-stone-types
           (negations-are-props fe)
           three-negations-imply-one)))
 where
  I : is-decidable (¬ (¬ Q)) → ¬ Q + ¬¬ Q
  I (inl nnq) = inr nnq
  I (inr f)   = inl (three-negations-imply-one f)

\end{code}

A product of Stone types indexed by a proposition is a Stone type,
which is the analogue of the micro Tychonoff theorem of the module
TypeTopology.MicroTychonoff.

In the following proof, the point at which h evaluates has to be given
uniformly in the witness of P, since a point of Π Y is a map assigning
a point of Y p to each witness p. The conclusion h r ＝ r v is an
equation of booleans and hence ¬¬-stable, and P + ¬ P is irrefutable,
so the proof may assume it, and then Π Y is equivalent to Y p or to 𝟙,
both of which are Stone types.

\begin{code}

prop-indexed-products-are-stone-types
 : {P : 𝓤 ̇ } {Y : P → 𝓥 ̇ }
 → is-prop P
 → ((p : P) → is-stone-type (Y p))
 → is-stone-type (Π Y)
prop-indexed-products-are-stone-types {𝓤} {𝓥} {P} {Y} P-is-prop ζ
 = stone-criterion
    (Π-is-totally-separated fe
      (λ p → stone-types-are-totally-separated (ζ p)))
    I
 where
  𝕖 : (p : P) → Π Y ≃ Y p
  𝕖 p = prop-indexed-product p fe P-is-prop

  I : (h : C (Π Y) → 𝟚)
    → is-bhom h
    → Σ v ꞉ Π Y , ((r : C (Π Y)) → h r ＝ r v)
  I h i = f , IV
   where
    open bhom-properties h i

    hₚ : (p : P) → C (Y p) → 𝟚
    hₚ p r = h (r ∘ ⌜ 𝕖 p ⌝)

    hₚ-is-bhom : (p : P) → is-bhom (hₚ p)
    hₚ-is-bhom p = preserves-₀ ,
                   preserves-₁ ,
                   (λ r s → preserves-∧ (r ∘ ⌜ 𝕖 p ⌝) (s ∘ ⌜ 𝕖 p ⌝)) ,
                   (λ r s → preserves-∨ (r ∘ ⌜ 𝕖 p ⌝) (s ∘ ⌜ 𝕖 p ⌝))

    II : (p : P) → Σ x ꞉ Y p , ((r : C (Y p)) → hₚ p r ＝ r x)
    II p = homs-are-evaluations (ζ p) (hₚ p) (hₚ-is-bhom p)

    f : Π Y
    f p = pr₁ (II p)

    f-property : (p : P) (r : C (Y p)) → hₚ p r ＝ r (f p)
    f-property p = pr₂ (II p)

\end{code}

Any point at which h evaluates agrees with v, because the two agree in
each member of the product, where the points are separated by the
clopens.

\begin{code}

    III : (Σ g ꞉ Π Y , ((r : C (Π Y)) → h r ＝ r g))
        → (r : C (Π Y)) → h r ＝ r f
    III (g , φ) r = h r ＝⟨ φ r ⟩
                    r g ＝⟨ ap r (V ⁻¹) ⟩
                    r f ∎
     where
      V : f ＝ g
      V = dfunext fe VI
       where
        VI : (p : P) → f p ＝ g p
        VI p = stone-types-are-totally-separated (ζ p) vi
         where
          vi : (r : C (Y p)) → r (f p) ＝ r (g p)
          vi r = r (f p) ＝⟨ (f-property p r)⁻¹ ⟩
                 hₚ p r  ＝⟨ φ (r ∘ ⌜ 𝕖 p ⌝) ⟩
                 r (g p) ∎

    IV : (r : C (Π Y)) → h r ＝ r f
    IV r = 𝟚-is-¬¬-separated (h r) (r f) V
     where
      V : ¬¬ (h r ＝ r f)
      V ν = VI VIII
       where
        VI : ¬¬ (P + ¬ P)
        VI f = f (inr (λ p → f (inl p)))

        VII : P + ¬ P → is-stone-type (Π Y)
        VII (inl p)  = equiv-to-stone-type (𝕖 p) (ζ p)
        VII (inr ν') = equiv-to-stone-type
                        (empty-indexed-product-is-𝟙 fe ν')
                        (𝟙-is-stone-type {𝓤₀})

        VIII : ¬ (P + ¬ P)
        VIII d = ν (III (homs-are-evaluations (VII d) h i) r)

\end{code}

In particular, P → 𝟚 is a Stone type if P is a proposition. It is not
discrete in general, as the discreteness of P → 𝟚 for all propositions
amounts to WLPO, as discussed in the module Taboos.P2.

\begin{code}

P→𝟚-is-stone-type
 : {P : 𝓤 ̇ }
 → is-prop P
 → is-stone-type (P → 𝟚)
P→𝟚-is-stone-type P-is-prop
 = prop-indexed-products-are-stone-types P-is-prop
    (λ _ → 𝟚-is-stone-type)

\end{code}

We now use this to show that if ¬ WLPO holds then Stone types are
**not** closed under Σ. A counterexample is the type ℕ∞₂ of the
module TypeTopology.FailureOfTotalSeparatedness, whose total
separatedness gives ¬¬ WLPO. Its base ℕ∞ is a Stone type when ¬ WLPO
holds, and its fibers are of the form P → 𝟚 for a proposition P and
hence are Stone types, so that the closure would make ℕ∞₂ a Stone type
and hence totally separated.

\begin{code}

open import TypeTopology.FailureOfTotalSeparatedness fe

Stone-Types-Are-Closed-Under-Σ : 𝓤₁ ̇
Stone-Types-Are-Closed-Under-Σ =
   (X : 𝓤₀ ̇ ) (Y : X → 𝓤₀ ̇ )
 → is-stone-type X
 → ((x : X) → is-stone-type (Y x))
 → is-stone-type (Σ Y)

closure-under-Σ-gives-¬¬-WLPO
 : Stone-Types-Are-Closed-Under-Σ
 → ¬¬ WLPO
closure-under-Σ-gives-¬¬-WLPO c nwlpo
 = ℕ∞₂-is-not-totally-separated-in-general I nwlpo
 where
  I : is-totally-separated ℕ∞₂
  I = stone-types-are-totally-separated
       (c ℕ∞
          (λ u → u ＝ ∞ → 𝟚)
          (ℕ∞-is-stone-type nwlpo)
          (λ u → P→𝟚-is-stone-type (ℕ∞-is-set fe)))

¬WLPO-gives-failure-of-closure-under-Σ
 : ¬ WLPO
 → ¬ Stone-Types-Are-Closed-Under-Σ
¬WLPO-gives-failure-of-closure-under-Σ nwlpo c
 = closure-under-Σ-gives-¬¬-WLPO c nwlpo

\end{code}

The Stone types of [1] are closed under Σ, by their Theorem 4.18, with
the same pointwise hypothesis on the fibers as above. There is no
conflict with our result, because in [1] a type is a Stone type when
it is equivalent to the spectrum of a countably presented boolean
algebra, and such types are Stone types in our sense by their duality
axiom, but not conversely. Since their axioms give ¬ WLPO, our Stone
types are not closed under Σ in their setting, and therefore the
fibers P → 𝟚 of the counterexample are Stone types in our sense but
not in theirs. Because P is an equality in ℕ∞, their Lemma 3.10 and
Corollary 1.22 give that P → 𝟚 is a Stone type in their sense only if
P is decidable.
