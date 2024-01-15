Tom de Jong, 22 & 23 July 2021 (following Andrew Swan)

After a discussion with Dominik Kirst on propositional resizing at FSCD 2021,
Martín Escardó asked the following question on HoTT Zulip [1] and nLab:

  By an inductive well-ordering I mean a well ordering in the sense of the HoTT
  book (accessible, extensional, transitive relation). If we assume that every
  set can be inductively well ordered, can we conclude that excluded middle
  holds?

Andrew Swan quickly answered this question positively, presenting two proofs
(based on the same idea). We formalize both proofs here.

In turns out that transitivity and accessibility are not needed, i.e. Swan
proves the much stronger result:

  If every set has some irreflexive, extensional order, then excluded middle
  follows.

In fact, we don't need full extensionality (as remarked by Dominik Kirst): it
suffices that we have extensionality for minimal elements.

It follows that the inductive well-ordering principle implies, and hence is
equivalent, to the axiom of choice. This is because we can reuse the classical
proof: first you get that inductive well-ordering implies classical well-ordering
(every non-empty subset has a minimal element), using excluded middle via the
argument above. Then we use the classical proof that (any kind of) well-ordering
implies choice.

[1] tinyurl.com/HoTT-Zulip-well-ordering

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.Base hiding (_≈_)
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Ordinals.WellOrderingTaboo
        (fe  : Fun-Ext)
        (pe  : Prop-Ext)
       where

module _
        {X : 𝓤 ̇ } (_≺_ : X → X → 𝓣 ̇ )
       where

 extensionality-for-minimal-elements : 𝓤 ⊔ 𝓣 ̇
 extensionality-for-minimal-elements = (x y : X)
                                     → ((a : X) → ¬ (a ≺ x))
                                     → ((a : X) → ¬ (a ≺ y))
                                     → ((a : X) → a ≺ x ↔ a ≺ y) → x ＝ y

\end{code}

Added 13 March 2022.

Martín Escadó observed that extensionality for minimal elements is logically
equivalent to the arguably simpler condition that there is at most one minimal
element.

This observation was implicitly used in some of the proofs below. Since Martín's
observation and adding a proof of the equivalence, the uses have been made
explicit.

\begin{code}

 having-at-most-one-minimal-element : 𝓤 ⊔ 𝓣 ̇
 having-at-most-one-minimal-element = is-prop (Σ x ꞉ X , ((y : X) → ¬ (y ≺ x)))

 extensionality-for-minimal-elts-if-at-most-one-minimal-elt :
  having-at-most-one-minimal-element → extensionality-for-minimal-elements
 extensionality-for-minimal-elts-if-at-most-one-minimal-elt
  at-most-one-min x y x-min y-min x-y-ext = goal
   where
    claim : (x , x-min ＝ y , y-min)
    claim = at-most-one-min (x , x-min) (y , y-min)
    goal : x ＝ y
    goal =  ap pr₁ claim

 at-most-one-minimal-elt-if-extensionality-for-minimal-elts :
  extensionality-for-minimal-elements → having-at-most-one-minimal-element
 at-most-one-minimal-elt-if-extensionality-for-minimal-elts
  ext (x , x-min) (y , y-min) = goal
   where
    claim : (a : X) → (a ≺ x) ↔ (a ≺ y)
    claim a = (I , II)
     where
      I : a ≺ x → a ≺ y
      I p = 𝟘-elim (x-min a p)
      II : a ≺ y → a ≺ x
      II q = 𝟘-elim (y-min a q)
    goal : (x , x-min) ＝ (y , y-min)
    goal = to-subtype-＝ I II
     where
      I : (b : X) → is-prop ((a : X) → ¬ (a ≺ b))
      I b = Π-is-prop fe (λ a → negations-are-props fe)
      II : x ＝ y
      II = ext x y x-min y-min claim

\end{code}

We first present Andrew Swan's second proof, which is a simplification of his
first proof that does not need exact quotients (we use propositional truncations
to construct quotients).

Because the main results *do* use propositional truncations to have the
existential quantifier ∃ available, we only present those later, in order to
emphasize that Swan's construction does not need propositional truncations.

We construct a family of sets Sₚ indexed by propositions P whose double negation
holds such that if Sₚ can be equipped with an irreflexive and
minimally-extensional order, then the corresponding proposition P must hold.

\begin{code}

module swan
        (P : 𝓤 ̇ )
        (P-is-prop : is-prop P)
        (P-is-not-false : ¬¬ P)
       where

 S : 𝓤 ⁺ ̇
 S = Σ Q ꞉ 𝓤 ̇ , is-prop Q × ¬¬ (Q ＝ P)

 S-is-set : is-set S
 S-is-set = equiv-to-set (≃-sym Σ-assoc) S'-is-set
  where
   S' : 𝓤 ⁺ ̇
   S' = Σ Q ꞉ Ω 𝓤 , ¬¬ (Q holds ＝ P)
   S'-is-set : is-set S'
   S'-is-set = subtypes-of-sets-are-sets' pr₁ (pr₁-lc (negations-are-props fe))
                (Ω-is-set fe pe)

 all-elements-are-¬¬-equal : (x y : S) → ¬¬ (x ＝ y)
 all-elements-are-¬¬-equal (Q , i , t) (Q' , i' , t') = ¬¬-kleisli γ t
  where
   γ : Q ＝ P → ¬¬ ((Q , i , t) ＝ (Q' , i' , t'))
   γ refl = ¬¬-functor h t'
    where
     h : Q' ＝ P → (P , i , t) ＝ (Q' , i' , t')
     h refl = to-subtype-＝
                (λ _ → ×-is-prop
                        (being-prop-is-prop fe)
                        (negations-are-props fe))
                refl

 module _
         (_≺_ : S → S → 𝓣 ̇ )
         (≺-irreflexive : (x : S) → ¬ (x ≺ x))
         (≺-minimally-extensional : extensionality-for-minimal-elements _≺_)
        where

  all-elements-are-minimal : (x y : S) → ¬ (x ≺ y)
  all-elements-are-minimal x y = contrapositive γ (all-elements-are-¬¬-equal x y)
   where
    γ : x ≺ y → ¬ (x ＝ y)
    γ l refl = ≺-irreflexive x l

  all-elements-are-equal : (x y : S) → x ＝ y
  all-elements-are-equal x y = goal
   where
    x-min : (a : S) → ¬ (a ≺ x)
    x-min a = all-elements-are-minimal a x
    y-min : (a : S) → ¬ (a ≺ y)
    y-min a = all-elements-are-minimal a y
    claim : (x , x-min) ＝ (y , y-min)
    claim = at-most-one-minimal-elt-if-extensionality-for-minimal-elts
             _≺_ ≺-minimally-extensional (x , x-min) (y , y-min)
    goal : x ＝ y
    goal = ap pr₁ claim

  P-must-hold : P
  P-must-hold = Idtofun γ ⋆
   where
    γ : 𝟙 ＝ P
    γ = ap pr₁ (all-elements-are-equal 𝟙-in-S P-in-S)
     where
      P-in-S : S
      P-in-S = (P , P-is-prop , ¬¬-intro refl)
      𝟙-in-S : S
      𝟙-in-S = (𝟙 , 𝟙-is-prop , h)
       where
        h : ¬¬ (𝟙 ＝ P)
        h = ¬¬-functor
             (λ p → pe 𝟙-is-prop P-is-prop (λ _ → p) (λ _ → ⋆))
             P-is-not-false

\end{code}

This construction allows us to prove the results announced above.

We first need some definitions.

\begin{code}

module InductiveWellOrder
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt

 open import Ordinals.Notions

 irreflexive-minimally-extensional-order-on-every-set : (𝓤 𝓣 : Universe)
                                                      → (𝓤 ⊔ 𝓣) ⁺ ̇
 irreflexive-minimally-extensional-order-on-every-set 𝓤 𝓣 =
  (X : 𝓤 ̇ ) → is-set X → ∃ _≺_ ꞉ (X → X → 𝓣 ̇ ) , ((x : X) → ¬ (x ≺ x))
                                × (extensionality-for-minimal-elements _≺_)

 irreflexive-extensional-order-on-every-set : (𝓤 𝓣 : Universe) → (𝓤 ⊔ 𝓣) ⁺ ̇
 irreflexive-extensional-order-on-every-set 𝓤 𝓣 =
  (X : 𝓤 ̇ ) → is-set X → ∃ _≺_ ꞉ (X → X → 𝓣 ̇ ) , ((x : X) → ¬ (x ≺ x))
                                                 × (is-extensional _≺_)

 inductive-well-order-on-every-set : (𝓤 𝓣 : Universe) → (𝓤 ⊔ 𝓣) ⁺ ̇
 inductive-well-order-on-every-set 𝓤 𝓣 =
  (X : 𝓤 ̇ ) → is-set X → ∃ _≺_ ꞉ (X → X → 𝓣 ̇ ), (is-well-order _≺_)

\end{code}

The following are the main theorems, which follow directly from Swan's results
above.

\begin{code}

 irreflexive-minimally-extensional-order-on-every-set-gives-excluded-middle :
  {𝓤 𝓣 : Universe} → irreflexive-minimally-extensional-order-on-every-set (𝓤 ⁺) 𝓣
                   → excluded-middle 𝓤
 irreflexive-minimally-extensional-order-on-every-set-gives-excluded-middle
  {𝓤} {𝓣} IMEO = DNE-gives-EM fe γ
   where
    γ : DNE 𝓤
    γ P P-is-prop P-is-not-false = ∥∥-rec P-is-prop h t
     where
      open swan P P-is-prop P-is-not-false
      t : ∃ _≺_ ꞉ (S → S → 𝓣 ̇ ), ((x : S) → ¬ (x ≺ x))
                                × (extensionality-for-minimal-elements _≺_)
      t = IMEO S S-is-set
      h : (Σ _≺_ ꞉ (S → S → 𝓣 ̇ ), ((x : S) → ¬ (x ≺ x))
                                 × (extensionality-for-minimal-elements _≺_))
        → P
      h (_≺_ , ≺-irr , ≺-min-ext) = P-must-hold _≺_ ≺-irr ≺-min-ext


 irreflexive-extensional-order-on-every-set-gives-excluded-middle :
  {𝓤 𝓣 : Universe} → irreflexive-extensional-order-on-every-set (𝓤 ⁺) 𝓣
                   → excluded-middle 𝓤
 irreflexive-extensional-order-on-every-set-gives-excluded-middle {𝓤} {𝓣} IEO =
  irreflexive-minimally-extensional-order-on-every-set-gives-excluded-middle γ
   where
    γ : irreflexive-minimally-extensional-order-on-every-set (𝓤 ⁺) 𝓣
    γ X X-is-set = ∥∥-functor f (IEO X X-is-set)
     where
      f : (Σ _≺_ ꞉ (X → X → 𝓣 ̇ ), ((x : X) → ¬ (x ≺ x)) × (is-extensional _≺_))
        → (Σ _≺_ ꞉ (X → X → 𝓣 ̇ ), ((x : X) → ¬ (x ≺ x))
                                 × (extensionality-for-minimal-elements _≺_))
      f (_≺_ , ≺-irr , ≺-ext) = _≺_ , ≺-irr , ≺-min-ext
       where
        ≺-min-ext : extensionality-for-minimal-elements _≺_
        ≺-min-ext x y _ _ e = extensional-gives-extensional' _≺_ ≺-ext x y e

 inductive-well-order-on-every-set-gives-excluded-middle :
  {𝓤 𝓣 : Universe} → inductive-well-order-on-every-set (𝓤 ⁺) 𝓣
                   → excluded-middle 𝓤
 inductive-well-order-on-every-set-gives-excluded-middle {𝓤} {𝓣} IWO =
  irreflexive-extensional-order-on-every-set-gives-excluded-middle γ
   where
    γ : irreflexive-extensional-order-on-every-set (𝓤 ⁺) 𝓣
    γ X X-is-set = ∥∥-functor f (IWO X X-is-set)
     where
      f : (Σ _≺_ ꞉ (X → X → 𝓣 ̇ ), (is-well-order _≺_))
        → (Σ _≺_ ꞉ (X → X → 𝓣 ̇ ), ((x : X) → ¬ (x ≺ x)) × (is-extensional _≺_))
      f (_≺_ , iwo) = (_≺_ , ≺-irr , extensionality _≺_ iwo)
       where
        ≺-irr : (x : X) → ¬ (x ≺ x)
        ≺-irr x = irreflexive _≺_ x (well-foundedness _≺_ iwo x)

\end{code}

For comparison, we include Andrew Swan's first construction of the family of
sets, which could also be used to derive the above results. This construction
uses quotients, which we constuct using propositional truncations.

\begin{code}

module swan'
        (pt  : propositional-truncations-exist)
        (P : 𝓤 ̇ )
        (P-is-prop : is-prop P)
        (P-is-not-false : ¬¬ P)
       where

 open PropositionalTruncation pt

 open import MLTT.Two-Properties

 open import Quotient.Type
 open import Quotient.Large pt fe pe
 open import UF.ImageAndSurjection pt

 open general-set-quotients-exist large-set-quotients

 _≈_ : 𝟚 → 𝟚 → 𝓤 ̇
 x ≈ y = (x ＝ y) ∨ P

 ≈-is-prop-valued : is-prop-valued _≈_
 ≈-is-prop-valued x y = ∨-is-prop

 ≈-is-reflexive : reflexive _≈_
 ≈-is-reflexive x = ∣ inl refl ∣

 ≈-is-symmetric : symmetric _≈_
 ≈-is-symmetric x y = ∥∥-functor γ
  where
   γ : (x ＝ y) + P → (y ＝ x) + P
   γ (inl e) = inl (e ⁻¹)
   γ (inr p) = inr p

 ≈-is-transitive : transitive _≈_
 ≈-is-transitive x y z = ∥∥-rec (Π-is-prop fe (λ _ → ≈-is-prop-valued x z)) γ
  where
   γ : (x ＝ y) + P → y ≈ z → x ≈ z
   γ (inl e₁) = ∥∥-functor ϕ
    where
     ϕ : (y ＝ z) + P → (x ＝ z) + P
     ϕ (inl e₂) = inl (e₁ ∙ e₂)
     ϕ (inr p)  = inr p
   γ (inr p) _ = ∣ inr p ∣

 ≋ : EqRel 𝟚
 ≋ = (_≈_ , ≈-is-prop-valued , ≈-is-reflexive , ≈-is-symmetric , ≈-is-transitive)

 S : 𝓤 ⁺ ̇
 S = 𝟚 / ≋

 module _
         (_≺_ : S → S → 𝓣 ̇ )
         (≺-minimally-extensional : extensionality-for-minimal-elements _≺_)
         (≺-irreflexive : (x : S) → ¬ (x ≺ x))
        where

  S-is-set : is-set S
  S-is-set = /-is-set ≋

  quotient-lemma : (x : S) → (x ＝ η/ ≋ ₀) ∨ (x ＝ η/ ≋ ₁)
  quotient-lemma x = ∥∥-functor γ (η/-is-surjection ≋ pt x)
   where
    γ : (Σ i ꞉ 𝟚 , η/ ≋ i ＝ x)
      → (x ＝ η/ ≋ ₀) + (x ＝ η/ ≋ ₁)
    γ (₀ , e) = inl (e ⁻¹)
    γ (₁ , e) = inr (e ⁻¹)

  η₀-minimal : (x : S) → ¬ (x ≺ η/ ≋ ₀)
  η₀-minimal x h = ∥∥-rec 𝟘-is-prop γ (quotient-lemma x)
   where
    γ : (x ＝ η/ ≋ ₀) + (x ＝ η/ ≋ ₁) → 𝟘
    γ (inl refl) = ≺-irreflexive (η/ ≋ ₀) h
    γ (inr refl) = P-is-not-false ϕ
     where
      ϕ : ¬ P
      ϕ p = ≺-irreflexive (η/ ≋ ₀) (transport (_≺ (η/ ≋ ₀)) claim h)
       where
        claim : η/ ≋ ₁ ＝ η/ ≋ ₀
        claim = η/-identifies-related-points ≋ ∣ inr p ∣

  η₁-minimal : (x : S) → ¬ (x ≺ η/ ≋ ₁)
  η₁-minimal x h = ∥∥-rec 𝟘-is-prop γ (quotient-lemma x)
   where
    γ : (x ＝ η/ ≋ ₀) + (x ＝ η/ ≋ ₁) → 𝟘
    γ (inr refl) = ≺-irreflexive (η/ ≋ ₁) h
    γ (inl refl) = P-is-not-false ϕ
     where
      ϕ : ¬ P
      ϕ p = ≺-irreflexive (η/ ≋ ₁) (transport (_≺ (η/ ≋ ₁)) claim h)
       where
        claim : η/ ≋ ₀ ＝ η/ ≋ ₁
        claim = η/-identifies-related-points ≋ ∣ inr p ∣

  ≈-identifies-₀-and-₁ : η/ ≋ ₀ ＝ η/ ≋ ₁
  ≈-identifies-₀-and-₁ = goal
   where
    claim : (η/ ≋ ₀ , η₀-minimal) ＝ (η/ ≋ ₁ , η₁-minimal)
    claim = at-most-one-minimal-elt-if-extensionality-for-minimal-elts
             _≺_ ≺-minimally-extensional (η/ ≋ ₀ , η₀-minimal) (η/ ≋ ₁ , η₁-minimal)
    goal : η/ ≋ ₀ ＝ η/ ≋ ₁
    goal = ap pr₁ claim

  P-must-hold : P
  P-must-hold =
   ∥∥-rec P-is-prop γ (large-effective-set-quotients ≋ ≈-identifies-₀-and-₁)
    where
     γ : (₀ ＝ ₁) + P → P
     γ (inl e) = 𝟘-elim (zero-is-not-one e)
     γ (inr p) = p

\end{code}

This concludes the formalization of Andrew Swan's proofs.

Next, we use the above argument to show that inductive well-ordering principle
implies the axiom of choice. This is because we can reuse the classical proof:
first you get the inductive well-ordering implies classical well-ordering (every
non-empty subset has a minimal element), using excluded middle via the argument
above. Then we use the classical proof that (any kind of) well-ordering implies
choice.

We start by defining classical well orders.

\begin{code}

module ClassicalWellOrder
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt

 module _
         {X : 𝓤 ̇ }
         (_≺_ : X → X → 𝓣 ̇ )
       where

  open import Ordinals.Notions _≺_

  is-uniquely-trichotomous : 𝓤 ⊔ 𝓣 ̇
  is-uniquely-trichotomous =
   (x y : X) → is-singleton ((x ≺ y) + (x ＝ y) + (y ≺ x))

  inhabited-has-minimal : (𝓤 ⊔ 𝓣) ⁺ ̇
  inhabited-has-minimal = (A : X → (𝓤 ⊔ 𝓣) ̇ )
                        → ((x : X) → is-prop (A x))
                        → ∃ x ꞉ X , A x
                        → Σ x ꞉ X , A x × ((y : X) → A y → ¬ (y ≺ x))

\end{code}

 The definition inhabtited-has-minimal deserves two remarks:

 (1) One may have expected ∃ rather than Σ in the conclusion, but in the presence
 of trichotomy (which is an axiom of a classical well-order) the type
   Σ x ꞉ X , A x × ((y : X) → A y → ¬ (y ≺ x))
 is a proposition, so there is no need to use ∃ rather than Σ.

 This result is minimal-is-prop below.

 (2) We would like the above to express that every inhabited subset has a
 minimal element, but in the absence of propositional resizing, this is tricky,
 because it would require having an axiom ⋆scheme⋆ consisting of a definition
 referring to families (A : X → 𝓥 ̇ ) for each universe level 𝓥.

 We don't wish to assume propsitional resizing here or have axiom schemes, so we
 make the choice to use the universe 𝓤 ⊔ 𝓣. Recall that X : 𝓤 and that _≺_ has
 values in 𝓣.

\begin{code}

  minimal-is-prop : is-trichotomous-order
                  → (A : X → (𝓤 ⊔ 𝓣) ̇ )
                  → ((x : X) → is-prop (A x))
                  → is-prop (Σ x ꞉ X , A x × ((y : X) → A y → ¬ (y ≺ x)))
  minimal-is-prop trich A A-is-prop-valued (x , a , f) (x' , a' , f') =
   to-subtype-＝ i q
    where
     i : (x : X) → is-prop (A x × ((y : X) → A y → ¬ (y ≺ x)))
     i x = ×-is-prop (A-is-prop-valued x) (Π₃-is-prop fe (λ x a l → 𝟘-is-prop))
     q : x ＝ x'
     q = κ (trich x x')
      where
       κ : (x ≺ x') + (x ＝ x') + (x' ≺ x) → x ＝ x'
       κ (inl k)       = 𝟘-elim (f' x a k)
       κ (inr (inl p)) = p
       κ (inr (inr l)) = 𝟘-elim (f x' a' l)

  is-classical-well-order : (𝓤 ⊔ 𝓣) ⁺ ̇
  is-classical-well-order = is-transitive
                          × is-uniquely-trichotomous
                          × inhabited-has-minimal

\end{code}

Assuming excluded middle (for 𝓤 ⊔ 𝓣), we show

 _≺_ is a classical well-order ↔ _≺_ is an inductive well-order.

A remark on well-order-gives-minimal (see below) is in order.
  It may seem that it repeats nonempty-has-minimal in OrdinalNotions.lagda, but
  nonempty-has-minimal uses ¬¬ and excluded middle in ⋆every⋆ universe to
  construct propositional truncations, and ∃ in particular, but we just assume
  propositional truncations and when we assume excluded middle, we only do so
  for specific universes.

\begin{code}

  module _
          (em : excluded-middle (𝓤 ⊔ 𝓣))
         where

   open import MLTT.Plus-Properties

   well-order-gives-minimal : is-well-order
                            → inhabited-has-minimal
   well-order-gives-minimal iwo A A-is-prop-valued A-is-inhabited = γ
    where
     B : 𝓤 ⊔ 𝓣 ̇
     B = Σ x ꞉ X , A x × ((y : X) → A y → ¬ (y ≺ x))
     B-is-prop : is-prop B
     B-is-prop = minimal-is-prop (trichotomy fe em iwo) A A-is-prop-valued
     δ : ¬¬ B
     δ f = ∥∥-rec 𝟘-is-prop A-is-empty A-is-inhabited
      where
       ϕ : (x : X) → ((y : X) → y ≺ x → ¬ A y) → ¬ A x
       ϕ x h a = ∥∥-rec 𝟘-is-prop x-is-minimal claim
        where
         lemma : ¬ ((y : X) → A y → ¬ (y ≺ x))
         lemma g = f (x , a , g)
         x-is-minimal : ¬ (Σ (y , _) ꞉ Σ A , y ≺ x)
         x-is-minimal ((y , a') , k) = h y k a'
         claim : ∃ σ ꞉ Σ A , pr₁ σ ≺ x
         claim = not-Π-not-implies-∃ pt em lemma'
          where
           lemma' : ¬ ((σ : Σ A) → ¬ (pr₁ σ ≺ x))
           lemma' = contrapositive (λ g' y p' → g' (y , p')) lemma
       A-is-empty : is-empty (Σ A)
       A-is-empty (x , p) = A-is-false x p
        where
         A-is-false : (x : X) → ¬ A x
         A-is-false = transfinite-induction (well-foundedness iwo) (λ x → ¬ A x) ϕ
     γ : B
     γ = EM-gives-DNE em B B-is-prop δ

   inductive-well-order-is-classical : is-well-order
                                     → is-classical-well-order
   inductive-well-order-is-classical iwo =
    (transitivity iwo , uniq-trich , well-order-gives-minimal iwo)
     where
      trich-prop : (x y : X) → is-prop ((x ≺ y) + (x ＝ y) + (y ≺ x))
      trich-prop x y = +-is-prop (prop-valuedness iwo x y)
                        (+-is-prop (well-ordered-types-are-sets (λ _ _ → fe) iwo)
                                   (prop-valuedness iwo y x) σ) τ
         where
          σ : x ＝ y → ¬ (y ≺ x)
          σ refl = irreflexive x (well-foundedness iwo x)
          τ : x ≺ y → ¬ ((x ＝ y) + (y ≺ x))
          τ k (inl refl) = irreflexive x (well-foundedness iwo x) k
          τ k (inr l)    = irreflexive x (well-foundedness iwo x)
                            (transitivity iwo x y x k l)
      uniq-trich : is-uniquely-trichotomous
      uniq-trich x y = pointed-props-are-singletons
                        (trichotomy fe em iwo x y)
                        (trich-prop x y)

   minimal-gives-well-foundedness : inhabited-has-minimal
                                  → is-well-founded
   minimal-gives-well-foundedness min = γ
    where
     δ : (x : X) → ¬¬ (is-accessible x)
     δ x₀ x₀-not-acc = x-not-acc x-acc
      where
       B : X → 𝓤 ⊔ 𝓣 ̇
       B x = ¬ (is-accessible x)
       m : Σ x ꞉ X , B x × ((y : X) → B y → ¬ (y ≺ x))
       m = min B (λ _ → negations-are-props fe) ∣ x₀ , x₀-not-acc ∣
       x : X
       x = pr₁ m
       x-not-acc : B x
       x-not-acc = pr₁ (pr₂ m)
       x-minimal : (y : X) → B y → ¬ (y ≺ x)
       x-minimal = pr₂ (pr₂ m)
       x-acc : is-accessible x
       x-acc = acc ϕ
        where
         ε : (y : X) → y ≺ x → ¬¬ (is-accessible y)
         ε y l y-not-acc = x-minimal y y-not-acc l
         ϕ : (y : X) → y ≺ x → is-accessible y
         ϕ y l = EM-gives-DNE em (is-accessible y) (accessibility-is-prop (λ _ _ → fe) y) (ε y l)
     γ : is-well-founded
     γ x = EM-gives-DNE em (is-accessible x) (accessibility-is-prop (λ _ _ → fe) x) (δ x)

   classical-well-order-is-inductive : is-classical-well-order
                                     → is-well-order
   classical-well-order-is-inductive (trans , trich , min) =
    pv , wf , ext , trans
     where
      pv : is-prop-valued
      pv x y k l = inl-lc (singletons-are-props (trich x y) (inl k) (inl l))
      wf : is-well-founded
      wf = minimal-gives-well-foundedness min
      ext : is-extensional
      ext x y u v = κ (center (trich x y))
       where
        κ : (x ≺ y) + (x ＝ y) + (y ≺ x) → x ＝ y
        κ (inl k)       = 𝟘-elim (irreflexive x (wf x) (v x k))
        κ (inr (inl e)) = e
        κ (inr (inr l)) = 𝟘-elim (irreflexive y (wf y) (u y l))

\end{code}

Having a classical well-order on every set allows us to derive excluded middle
with a fairly direct proof.

\begin{code}

 open import MLTT.Two-Properties
 open import UF.UniverseEmbedding

 classical-well-order-on-every-set : (𝓤 𝓣 : Universe) → (𝓤 ⊔ 𝓣) ⁺ ̇
 classical-well-order-on-every-set 𝓤 𝓣 =
  (X : 𝓤 ̇ ) → is-set X → ∃ _≺_ ꞉ (X → X → 𝓣 ̇ ), (is-classical-well-order _≺_)

 classical-well-order-on-every-set-gives-excluded-middle :
  {𝓤 𝓣 : Universe} → classical-well-order-on-every-set 𝓤 𝓣
                   → excluded-middle (𝓤 ⊔ 𝓣)
 classical-well-order-on-every-set-gives-excluded-middle {𝓤} {𝓣} CWO P P-is-prop =
  ∥∥-rec ρ γ (CWO 𝟚' 𝟚'-is-set)
   where
    𝟚' : 𝓤 ̇
    𝟚' = Lift 𝓤 𝟚
    𝟚'-is-set : is-set 𝟚'
    𝟚'-is-set = equiv-to-set (Lift-≃ 𝓤 𝟚) 𝟚-is-set
    ι : 𝟚 → 𝟚'
    ι = lift 𝓤
    ρ : is-prop (P + ¬ P)
    ρ = +-is-prop P-is-prop (negations-are-props fe) ¬¬-intro
    γ : (Σ _≺_ ꞉ (𝟚' → 𝟚' → 𝓣 ̇ ) , (is-classical-well-order _≺_)) → P + ¬ P
    γ (_≺_ , trans , trich , min) = κ (center (trich (ι ₀) (ι ₁)))
     where
      κ : (ι ₀ ≺ ι ₁) + (ι ₀ ＝ ι ₁) + (ι ₁ ≺ ι ₀)
        → P + ¬ P
      κ (inr (inl e)) = 𝟘-elim (zero-is-not-one (equivs-are-lc ι lift-is-equiv e))
      κ (inl k)       = f (min A A-is-prop-valued A-is-inhabited)
       where
        A : 𝟚' → 𝓤 ⊔ 𝓣 ̇
        A x = 𝟚-cases P 𝟙 (lower x)
        A-is-prop-valued : (x : 𝟚') → is-prop (A x)
        A-is-prop-valued (₀ , _) = P-is-prop
        A-is-prop-valued (₁ , _) = 𝟙-is-prop
        A-is-inhabited : ∃ A
        A-is-inhabited = ∣ ι ₁ , ⋆ ∣
        f : (Σ x ꞉ 𝟚' , A x × ((y : 𝟚') → A y → ¬ (y ≺ x)))
          → P + ¬ P
        f ((₀ , _) , p , _) = inl p
        f ((₁ , _) , _ , m) = inr (λ p → m (ι ₀) p k)
      κ (inr (inr l)) = g (min B B-is-prop-valued B-is-inhabited)
       where
        B : 𝟚' → 𝓤 ⊔ 𝓣 ̇
        B x = 𝟚-cases 𝟙 P (lower x)
        B-is-prop-valued : (x : 𝟚') → is-prop (B x)
        B-is-prop-valued (₀ , _) = 𝟙-is-prop
        B-is-prop-valued (₁ , _) = P-is-prop
        B-is-inhabited : ∃ B
        B-is-inhabited = ∣ ι ₀ , ⋆ ∣
        g : (Σ x ꞉ 𝟚' , B x × ((y : 𝟚') → B y → ¬ (y ≺ x)))
          → P + ¬ P
        g ((₀ , _) , _ , m) = inr (λ p → m (ι ₁) p l)
        g ((₁ , _) , p , _) = inl p

\end{code}

We assumed excluded middle to show that every classical well-order is an
inductive well-order. But if we assume that we have a classical well-order on
every set, then we can derive excluded middle. Hence, if every set admits some
classical well-order, then every set admits some inducive well-order.

\begin{code}

 open import Ordinals.Notions
 open InductiveWellOrder pt

 classical-well-ordering-implies-inductive-well-ordering :
   {𝓤 𝓣 : Universe}
   → classical-well-order-on-every-set 𝓤 𝓣
   → inductive-well-order-on-every-set 𝓤 𝓣
 classical-well-ordering-implies-inductive-well-ordering {𝓤} {𝓣} CWO X X-is-set =
  ∥∥-functor γ (CWO X X-is-set)
   where
    γ : (Σ _≺_ ꞉ (X → X → 𝓣 ̇ ) , (is-classical-well-order _≺_))
      → Σ _≺_ ꞉ (X → X → 𝓣 ̇ ) , (is-well-order _≺_)
    γ (_≺_ , cwo) = (_≺_ , classical-well-order-is-inductive _≺_ em cwo)
     where
      em : excluded-middle (𝓤 ⊔ 𝓣)
      em = classical-well-order-on-every-set-gives-excluded-middle CWO

\end{code}

The converse holds too (but note the change in universe levels) and depends on
the straightforward but tedious lemma lower-inductive-well-order-on-every-set
which expresses that if every set in some large universe can be inductively
well-ordered, then so can every set in a lower universe.

(NB. There are similar, but different technical lemmas in the file
OrdinalsWellOrderTransport.lagda.)

\begin{code}

 inductive-well-ordering-implies-classical-well-ordering :
   {𝓤 𝓣 : Universe}
   → inductive-well-order-on-every-set ((𝓤 ⊔ 𝓣) ⁺) 𝓣
   → classical-well-order-on-every-set 𝓤 𝓣

 lower-inductive-well-order-on-every-set : {𝓤 𝓣 𝓥 : Universe}
                                         → inductive-well-order-on-every-set (𝓤 ⊔ 𝓥) 𝓣
                                         → inductive-well-order-on-every-set 𝓤 𝓣
 lower-inductive-well-order-on-every-set {𝓤} {𝓣} {𝓥} IWO X X-is-set = ∥∥-functor γ iwo
  where
   X' : 𝓤 ⊔ 𝓥 ̇
   X' = Lift 𝓥 X
   ι : X → X'
   ι = lift 𝓥
   X'-is-set : is-set X'
   X'-is-set = equiv-to-set (Lift-≃ 𝓥 X) X-is-set
   iwo : ∃ _≺'_ ꞉ (X' → X' → 𝓣 ̇ ), (is-well-order _≺'_)
   iwo = IWO X' X'-is-set
   γ : (Σ _≺'_ ꞉ (X' → X' → 𝓣 ̇ ), (is-well-order _≺'_))
     → (Σ _≺_ ꞉ (X → X → 𝓣 ̇ ), (is-well-order _≺_))
   γ (_≺'_ , pv' , wf' , ext' , trans') = (_≺_ , pv , wf , ext , trans)
    where
     _≺_ : X → X → 𝓣 ̇
     x ≺ y = ι x ≺' ι y
     pv : is-prop-valued _≺_
     pv x y = pv' (ι x) (ι y)
     wf : is-well-founded _≺_
     wf = transfinite-induction-converse _≺_ ω
      where
       ω : is-Well-founded _≺_
       ω P h x = transfinite-induction _≺'_ wf' P' h' (ι x)
        where
         P' : X' → 𝓤 ⊔ 𝓣 ̇
         P' = P ∘ lower
         h' : (x' : X') → ((y : X') → y ≺' x' → P' y) → P' x'
         h' x' ρ = h (lower x') (λ y k → ρ (ι y) k)
     ext : is-extensional _≺_
     ext x y u v = equivs-are-lc ι lift-is-equiv
                    (ext' (ι x) (ι y)
                      (λ x' k → u (lower x') k)
                      (λ y' l → v (lower y') l))
     trans : is-transitive _≺_
     trans x y z k l = trans' (ι x) (ι y) (ι z) k l

 inductive-well-ordering-implies-classical-well-ordering {𝓤} {𝓣} IWO X X-is-set =
  ∥∥-functor γ (lower-inductive-well-order-on-every-set IWO X X-is-set)
   where
    γ : (Σ _≺_ ꞉ (X → X → 𝓣 ̇ ) , (is-well-order _≺_))
      → Σ _≺_ ꞉ (X → X → 𝓣 ̇ ) , (is-classical-well-order _≺_)
    γ (_≺_ , iwo) = (_≺_ , inductive-well-order-is-classical _≺_ em iwo)
     where
      em : excluded-middle (𝓤 ⊔ 𝓣)
      em = inductive-well-order-on-every-set-gives-excluded-middle IWO

\end{code}

Finally, we use the above to show that having an inductive well-order on every
set implies the axiom of choice.

(In fact, they are equivalent by Zermelo's proof of the Well Ordering Theorem,
but we don't formalize this.)

\begin{code}

module _
        (pt : propositional-truncations-exist)
       where

 open import UF.Retracts
 open import UF.Choice

 open Univalent-Choice (λ _ _ → fe) pt

 open PropositionalTruncation pt

 open ClassicalWellOrder pt
 open InductiveWellOrder pt

 classical-well-ordering-implies-ac : classical-well-order-on-every-set (𝓤 ⊔ 𝓣) 𝓣
                                    → AC {𝓤 ⊔ 𝓣} {𝓤 ⊔ 𝓣}
 classical-well-ordering-implies-ac {𝓤} {𝓣} CWO =
  AC₁-gives-AC (AC₂-gives-AC₁ γ)
   where
    γ : (X : 𝓤 ⊔ 𝓣 ̇ ) (Y : X → 𝓤 ⊔ 𝓣 ̇ )
      → is-set X
      → ((x : X) → is-set (Y x))
      → ∥ ((x : X) → ∥ Y x ∥ → Y x) ∥
    γ X Y X-is-set Y-is-set-valued =
     ∥∥-functor f (CWO (Σ Y) (Σ-is-set X-is-set Y-is-set-valued))
      where
       f : (Σ _≺_ ꞉ (Σ Y → Σ Y → 𝓣 ̇ ) , (is-classical-well-order _≺_))
         → ((x : X) → ∥ Y x ∥ → Y x)
       f (_≺_ , _ , _ , min) x y = transport Y x'-is-x y'
        where
         S : Σ Y → 𝓤 ⊔ 𝓣 ̇
         S (x' , _) = x' ＝ x
         m : Σ σ ꞉ (Σ Y) , S σ × ((τ : Σ Y) → S τ → ¬ (τ ≺ σ))
         m = min S (λ _ → X-is-set) (∥∥-functor (λ y' → (x , y') , refl) y)
         x' : X
         x' = pr₁ (pr₁ m)
         x'-is-x : x' ＝ x
         x'-is-x = pr₁ (pr₂ m)
         y' : Y x'
         y' = pr₂ (pr₁ m)

 classical-well-ordering-implies-ac-corollary :
   classical-well-order-on-every-set 𝓤 𝓤 → AC {𝓤} {𝓤}
 classical-well-ordering-implies-ac-corollary {𝓤} =
   classical-well-ordering-implies-ac {𝓤} {𝓤}

 inductive-well-ordering-implies-ac :
  inductive-well-order-on-every-set ((𝓤 ⁺) ⊔ (𝓣 ⁺)) 𝓣
  → AC {𝓤 ⊔ 𝓣} {𝓤 ⊔ 𝓣}
 inductive-well-ordering-implies-ac {𝓤} {𝓣} =
     classical-well-ordering-implies-ac {𝓤} {𝓣}
   ∘ inductive-well-ordering-implies-classical-well-ordering

 inductive-well-ordering-implies-ac-corollary :
   inductive-well-order-on-every-set (𝓤 ⁺) 𝓤
   → AC {𝓤} {𝓤}
 inductive-well-ordering-implies-ac-corollary {𝓤} =
   inductive-well-ordering-implies-ac {𝓤} {𝓤}

\end{code}
