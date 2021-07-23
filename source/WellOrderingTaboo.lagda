Tom de Jong, 22 & 23 July 2021 (following Andrew Swan)

After a discussion with Dominik Kirst on propositional resizing at FSCD 2021,
Martín Escardó asked the following question on HoTT Zulip and nlab:

  By an inductive well-ordering I mean a well ordering in the sense of the HoTT
  book (accessible, extensional, transitive relation). If we assume that every
  set can be inductively well ordered, can we conclude that excluded middle
  holds?"

Andrew Swan quickly answered this question positively, presenting two proofs
(based on the same idea). We formalize both proofs here.

In turns out that transitivity and accessibility are not needed, i.e. we can
prove the much stronger result:

  If every set has some irreflexive, extensional order, then excluded middle
  follows.

In fact, we don't need full extensionality (as remarked by Dominik Krist): it
suffices that we have extensionality for minimal elements.

We also record the following observation by Martín:

  It follows that the inductive well-ordering principle implies, and hence is
  equivalent, to the axiom of choice. This is because we can reuse the classical
  proof: first you get the inductive well-ordering implies classical
  well-ordering (every non-empty subset has a minimal element), using excluded
  middle via your argument above. Then we use the classical proof that (any kind
  of) well-ordering implies choice.

Link to the discussion on HoTT Zulip: https://hott.zulipchat.com/#narrow/stream/228519-general/topic/inductive.20well-ordering.20gives.20excluded.20middle.3F

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

open import UF-Base hiding (_≈_)
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-PropTrunc
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module WellOrderingTaboo
        (fe  : Fun-Ext)
        (pe  : Prop-Ext)
       where

extensionality-for-minimal-elements : {X : 𝓤 ̇ } (_≺_ : X → X → 𝓣 ̇ )
                                    → 𝓤 ⊔ 𝓣 ̇
extensionality-for-minimal-elements {𝓤} {𝓣} {X} _≺_ =
  (x y : X) → ((a : X) → ¬ (a ≺ x))
            → ((a : X) → ¬ (a ≺ y))
            → ((a : X) → a ≺ x ⇔ a ≺ y) → x ≡ y

\end{code}

We first present Andrew Swan's second proof, which is a simplification of his
first proof that does not need propositional truncations (which were used to
construct quotients).

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
 S = Σ Q ꞉ 𝓤 ̇ , is-prop Q × ¬¬ (Q ≡ P)

 S-is-set : is-set S
 S-is-set = equiv-to-set (≃-sym Σ-assoc) S'-is-set
  where
   S' : 𝓤 ⁺ ̇
   S' = Σ Q ꞉ Ω 𝓤 , ¬¬ (Q holds ≡ P)
   S'-is-set : is-set S'
   S'-is-set = subtypes-of-sets-are-sets pr₁ (pr₁-lc (negations-are-props fe))
                (Ω-is-set fe pe)

 all-elements-are-¬¬-equal : (x y : S) → ¬¬ (x ≡ y)
 all-elements-are-¬¬-equal (Q , i , t) (Q' , i' , t') = ¬¬-kleisli γ t
  where
   γ : Q ≡ P → ¬¬ ((Q , i , t) ≡ (Q' , i' , t'))
   γ refl = ¬¬-functor h t'
    where
     h : Q' ≡ P → (P , i , t) ≡ (Q' , i' , t')
     h refl = to-subtype-≡
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
    γ : x ≺ y → ¬ (x ≡ y)
    γ l refl = ≺-irreflexive x l

  all-elements-are-equal : (x y : S) → x ≡ y
  all-elements-are-equal x y = ≺-minimally-extensional x y
                                (λ s → all-elements-are-minimal s x)
                                (λ s → all-elements-are-minimal s y)
                                γ
   where
    γ : (s : S) → (s ≺ x) ⇔ (s ≺ y)
    γ s = (f , g)
     where
      f : s ≺ x → s ≺ y
      f l = 𝟘-elim (all-elements-are-minimal s x l)
      g : s ≺ y → s ≺ x
      g l = 𝟘-elim (all-elements-are-minimal s y l)

  P-must-hold : P
  P-must-hold = Idtofun γ *
   where
    γ : 𝟙 ≡ P
    γ = ap pr₁ (all-elements-are-equal 𝟙-in-S P-in-S)
     where
      P-in-S : S
      P-in-S = (P , P-is-prop , double-negation-intro refl)
      𝟙-in-S : S
      𝟙-in-S = (𝟙 , 𝟙-is-prop , h)
       where
        h : ¬¬ (𝟙 ≡ P)
        h = ¬¬-functor
             (λ p → pe 𝟙-is-prop P-is-prop (λ _ → p) (λ _ → *))
             P-is-not-false

\end{code}

This construction allows us to prove the results announced above.

\begin{code}

module _
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt

 open import OrdinalNotions
 open import UF-ExcludedMiddle

 irreflexive-minimally-extensional-order-on-every-set : (𝓤 𝓣 : Universe)
                                                      → (𝓤 ⊔ 𝓣) ⁺ ̇
 irreflexive-minimally-extensional-order-on-every-set 𝓤 𝓣 =
  (X : 𝓤 ̇ ) → is-set X → ∃ _≺_ ꞉ (X → X → 𝓣 ̇ ) ,
                                 ((x : X) → ¬ (x ≺ x))
                               × (extensionality-for-minimal-elements _≺_)

 irreflexive-extensional-order-on-every-set : (𝓤 𝓣 : Universe) → (𝓤 ⊔ 𝓣) ⁺ ̇
 irreflexive-extensional-order-on-every-set 𝓤 𝓣 =
  (X : 𝓤 ̇ ) → is-set X → ∃ _≺_ ꞉ (X → X → 𝓣 ̇ ) , ((x : X) → ¬ (x ≺ x))
                                                 × (is-extensional _≺_)

 inductive-well-order-on-every-set : (𝓤 𝓣 : Universe) → (𝓤 ⊔ 𝓣) ⁺ ̇
 inductive-well-order-on-every-set 𝓤 𝓣 =
  (X : 𝓤 ̇ ) → is-set X → ∃ _≺_ ꞉ (X → X → 𝓣 ̇) , (is-well-order _≺_)

 irreflexive-minimally-extensional-order-on-every-set-gives-excluded-middle :
  (𝓤 𝓣 : Universe) → irreflexive-minimally-extensional-order-on-every-set (𝓤 ⁺) 𝓣
                   → excluded-middle 𝓤
 irreflexive-minimally-extensional-order-on-every-set-gives-excluded-middle
  𝓤 𝓣 IMEO = DNE-gives-EM fe γ
   where
    γ : DNE 𝓤
    γ P P-is-prop P-is-not-false = ∥∥-rec P-is-prop h t
     where
      open swan P P-is-prop P-is-not-false
      t : ∃ _≺_ ꞉ (S → S → 𝓣 ̇) , ((x : S) → ¬ (x ≺ x))
                                × (extensionality-for-minimal-elements _≺_)
      t = IMEO S S-is-set
      h : (Σ _≺_ ꞉ (S → S → 𝓣 ̇) , ((x : S) → ¬ (x ≺ x))
                                × (extensionality-for-minimal-elements _≺_))
        → P
      h (_≺_ , ≺-irr , ≺-min-ext) = P-must-hold _≺_ ≺-irr ≺-min-ext


 irreflexive-extensional-order-on-every-set-gives-excluded-middle :
  (𝓤 𝓣 : Universe) → irreflexive-extensional-order-on-every-set (𝓤 ⁺) 𝓣
                   → excluded-middle 𝓤
 irreflexive-extensional-order-on-every-set-gives-excluded-middle 𝓤 𝓣 IEO =
  irreflexive-minimally-extensional-order-on-every-set-gives-excluded-middle 𝓤 𝓣 γ
   where
    γ : irreflexive-minimally-extensional-order-on-every-set (𝓤 ⁺) 𝓣
    γ X X-is-set = ∥∥-functor f (IEO X X-is-set)
     where
      f : (Σ _≺_ ꞉ (X → X → 𝓣 ̇) , ((x : X) → ¬ (x ≺ x)) × (is-extensional _≺_))
        → (Σ _≺_ ꞉ (X → X → 𝓣 ̇) , ((x : X) → ¬ (x ≺ x))
                                × (extensionality-for-minimal-elements _≺_))
      f (_≺_ , ≺-irr , ≺-ext) = _≺_ , ≺-irr , ≺-min-ext
       where
        ≺-min-ext : extensionality-for-minimal-elements _≺_
        ≺-min-ext x y _ _ e = extensional-gives-extensional' _≺_ ≺-ext x y e

 inductive-well-order-on-every-set-gives-excluded-middle :
  (𝓤 𝓣 : Universe) → inductive-well-order-on-every-set (𝓤 ⁺) 𝓣
                   → excluded-middle 𝓤
 inductive-well-order-on-every-set-gives-excluded-middle 𝓤 𝓣 IWO =
  irreflexive-extensional-order-on-every-set-gives-excluded-middle 𝓤 𝓣 γ
   where
    γ : irreflexive-extensional-order-on-every-set (𝓤 ⁺) 𝓣
    γ X X-is-set = ∥∥-functor f (IWO X X-is-set)
     where
      f : (Σ _≺_ ꞉ (X → X → 𝓣 ̇) , (is-well-order _≺_))
        → Σ _≺_ ꞉ (X → X → 𝓣 ̇) , ((x : X) → ¬ (x ≺ x)) × (is-extensional _≺_)
      f (_≺_ , iwo) = (_≺_ , ≺-irr , extensionality _≺_ iwo)
       where
        ≺-irr : (x : X) → ¬ (x ≺ x)
        ≺-irr x = irreflexive _≺_ x (well-foundedness _≺_ iwo x)

\end{code}

Finally, for comparison, we include Andrew Swan's first construction of the
family of sets, which could also be used to derive the above results. This
construction uses quotients, which we constuct using propositional truncations.

\begin{code}

module swan'
        (pt  : propositional-truncations-exist)
        (P : 𝓤 ̇ )
        (P-is-prop : is-prop P)
        (P-is-not-false : ¬¬ P)
       where

 open import Two-Properties

 open import UF-Quotient pt fe pe

 open import UF-ImageAndSurjection
 open ImageAndSurjection pt

 open PropositionalTruncation pt

 _≈_ : 𝟚 → 𝟚 → 𝓤 ̇
 x ≈ y = (x ≡ y) ∨ P

 ≈-is-prop-valued : is-prop-valued _≈_
 ≈-is-prop-valued x y = ∨-is-prop

 ≈-is-reflexive : reflexive _≈_
 ≈-is-reflexive x = ∣ inl refl ∣

 ≈-is-symmetric : symmetric _≈_
 ≈-is-symmetric x y = ∥∥-functor γ
  where
   γ : (x ≡ y) + P → (y ≡ x) + P
   γ (inl e) = inl (e ⁻¹)
   γ (inr p) = inr p

 ≈-is-transitive : transitive _≈_
 ≈-is-transitive x y z = ∥∥-rec (Π-is-prop fe (λ _ → ≈-is-prop-valued x z)) γ
  where
   γ : (x ≡ y) + P → y ≈ z → x ≈ z
   γ (inl e₁) = ∥∥-functor ϕ
    where
     ϕ : (y ≡ z) + P → (x ≡ z) + P
     ϕ (inl e₂) = inl (e₁ ∙ e₂)
     ϕ (inr p)  = inr p
   γ (inr p) _ = ∣ inr p ∣

 open quotient 𝟚 _≈_
  ≈-is-prop-valued ≈-is-reflexive ≈-is-symmetric ≈-is-transitive

 S : 𝓤 ⁺ ̇
 S = X/≈

 module _
         (_≺_ : S → S → 𝓣 ̇ )
         (≺-minimally-extensional : extensionality-for-minimal-elements _≺_)
         (≺-irreflexive : (x : S) → ¬ (x ≺ x))
        where

  S-is-set : is-set S
  S-is-set = X/≈-is-set

  quotient-lemma : (x : S) → (x ≡ η ₀) ∨ (x ≡ η ₁)
  quotient-lemma x = ∥∥-functor γ (η-surjection x)
   where
    γ : (Σ i ꞉ 𝟚 , η i ≡ x)
      → (x ≡ η ₀) + (x ≡ η ₁)
    γ (₀ , e) = inl (e ⁻¹)
    γ (₁ , e) = inr (e ⁻¹)

  η₀-minimal : (x : S) → ¬ (x ≺ η ₀)
  η₀-minimal x h = ∥∥-rec 𝟘-is-prop γ (quotient-lemma x)
   where
    γ : (x ≡ η ₀) + (x ≡ η ₁) → 𝟘
    γ (inl refl) = ≺-irreflexive (η ₀) h
    γ (inr refl) = P-is-not-false ϕ
     where
      ϕ : ¬ P
      ϕ p = ≺-irreflexive (η ₀) (transport (_≺ (η ₀)) claim h)
       where
        claim : η ₁ ≡ η ₀
        claim = η-equiv-equal ∣ inr p ∣

  η₁-minimal : (x : S) → ¬ (x ≺ η ₁)
  η₁-minimal x h = ∥∥-rec 𝟘-is-prop γ (quotient-lemma x)
   where
    γ : (x ≡ η ₀) + (x ≡ η ₁) → 𝟘
    γ (inr refl) = ≺-irreflexive (η ₁) h
    γ (inl refl) = P-is-not-false ϕ
     where
      ϕ : ¬ P
      ϕ p = ≺-irreflexive (η ₁) (transport (_≺ (η ₁)) claim h)
       where
        claim : η ₀ ≡ η ₁
        claim = η-equiv-equal ∣ inr p ∣

  ≈-identifies-₀-and-₁ : η ₀ ≡ η ₁
  ≈-identifies-₀-and-₁ = ≺-minimally-extensional (η ₀) (η ₁)
                          η₀-minimal η₁-minimal γ
   where
    γ : (s : S) → (s ≺ η ₀) ⇔ (s ≺ η ₁)
    γ s = f , g
     where
      f : s ≺ η ₀ → s ≺ η ₁
      f h = 𝟘-elim (η₀-minimal s h)
      g : s ≺ η ₁ → s ≺ η ₀
      g h = 𝟘-elim (η₁-minimal s h)

  P-must-hold : P
  P-must-hold =
   ∥∥-rec P-is-prop γ (η-equal-equiv ≈-identifies-₀-and-₁)
    where
     γ : (₀ ≡ ₁) + P → P
     γ (inl e) = 𝟘-elim (zero-is-not-one e)
     γ (inr p) = p

\end{code}
