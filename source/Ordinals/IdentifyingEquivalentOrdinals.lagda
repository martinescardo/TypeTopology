Written 26 March 2023 by Tom de Jong, following a discussion with Nicolai Kraus
on 24 March 2023, but not completed and merged into TypeTopology master then.
Revisited and updated on 17 February 2026.

--- Summary ---
We show that having an identification of the ordinals (𝟚 , ₀ ≺ ₁) and
(𝟚 , ₁ ≺ ₀) contradicts the K-axiom. It follows that preunivalence, while
sufficient to show that the type of ordinals is a set
(cf. Ordinal-is-set-under-preunivalence in Ordinals.Equivalence), is not enough
to show that the simulation ordering on the type of ordinals is
antisymmetric. Indeed, the ordinals (𝟚 , ₀ ≺ ₁) and (𝟚 , ₁ ≺ ₀) are equivalent,
while preunivalence is derivable from the K-axiom.

--- Proof sketch ---
For any two ordinals α and β, we let α ≃ₒ β denote the type of order
equivalences from α to β. By path induction, the following diagram

                ap ⟨_⟩
   α ＝ β ------------------> ⟨ α ⟩ ＝ ⟨ β ⟩
     |                              |
     | idtoeq                       | idtoeq
     v                              v
   α ≃ₒ β ------------------> ⟨ α ⟩ ≃ ⟨ β ⟩
              ≃ₒ-gives-≃

always commutes.

Taking α = 𝟚ₒ = (𝟚 , ₀ ≺ ₁) and β = 𝟚ₒ' = (𝟚 , ₁ ≺ ₀), we first observe that
(α ≃ₒ β) has a single inhabitant e₀, namely the order equivalence that swaps the
booleans. Therefore, applying ≃ₒ-gives-≃ to *any* element of (α ≃₀ β) always
yields the swapping equivalence (called complement in TypeTopology).

Assuming the K-axiom, all loops are refl, so that any element p : ⟨ α ⟩ = ⟨ β ⟩
must be equal to refl as ⟨ α ⟩ and ⟨ β ⟩ are both just 𝟚. Hence, under the
K-axiom, applying idtoeq to any such element always yields the identity map.

Hence, the commutativity of the diagram then tells us that identifying α and β
must contradict the K-axiom.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Ordinals.IdentifyingEquivalentOrdinals where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import UF.Equiv
open import UF.PreUnivalence
open import UF.Sets
open import UF.Subsingletons

open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.Underlying

idtoeqₒ-naturality
 : (α β : Ordinal 𝓤) (p : α ＝ β)
 → idtoeq ⟨ α ⟩ ⟨ β ⟩ (ap ⟨_⟩ p) ＝ ≃ₒ-gives-≃ α β (idtoeqₒ α β p)
idtoeqₒ-naturality α β refl = refl

\end{code}

We now construct the ordinal 𝟚₀ = (𝟚 , ₀ ≺ ₁).
Note that it is equivalent to 𝟙ₒ +ₒ 𝟙ₒ, but we prefer to work directly with booleans here.

\begin{code}

private

 𝟚ₒ : Ordinal 𝓤₀
 𝟚ₒ = 𝟚 , (_≺_ , p , w , e , t)
  where
   _≺_ : 𝟚 → 𝟚 → 𝓤₀ ̇
   ₀ ≺ ₀ = 𝟘
   ₀ ≺ ₁ = 𝟙
   ₁ ≺ ₀ = 𝟘
   ₁ ≺ ₁ = 𝟘
   p : is-prop-valued _≺_
   p ₀ ₀ = 𝟘-is-prop
   p ₀ ₁ = 𝟙-is-prop
   p ₁ ₀ = 𝟘-is-prop
   p ₁ ₁ = 𝟘-is-prop
   w : is-well-founded _≺_
   w ₀ = acc a
    where
     a : (y : 𝟚) → y ≺ ₀ → is-accessible _≺_ y
     a ₀ l = 𝟘-elim l
     a ₁ l = 𝟘-elim l
   w ₁ = acc a
    where
     a : (y : 𝟚) → y ≺ ₁ → is-accessible _≺_ y
     a ₀ l = w ₀
     a ₁ l = 𝟘-elim l
   e : is-extensional _≺_
   e ₀ ₀ u v = refl
   e ₀ ₁ u v = 𝟘-elim (v ₀ ⋆)
   e ₁ ₀ u v = 𝟘-elim (u ₀ ⋆)
   e ₁ ₁ u v = refl
   t : is-transitive _≺_
   t ₀ ₀ ₀ k l = l
   t ₀ ₁ ₀ k l = l
   t ₁ ₀ ₀ k l = l
   t ₁ ₁ ₀ k l = l
   t ₀ ₀ ₁ k l = l
   t ₀ ₁ ₁ k l = k
   t ₁ ₀ ₁ k l = k
   t ₁ ₁ ₁ k l = l

\end{code}

We now construct the ordinal 𝟚₀' = (𝟚 , ₁ ≺ ₀).
There is some repetition of code which we could avoid by using
transport-well-order (on the complement map) from Ordinals.WellOrderTransport,
but that module requires function extensionality which we prefer not to assume
here for foundational minimalism.

\begin{code}

 𝟚ₒ' : Ordinal 𝓤₀
 𝟚ₒ' = 𝟚 , (_≺_ , p , w , e , t)
  where
   _≺_ : 𝟚 → 𝟚 → 𝓤₀ ̇
   ₀ ≺ ₀ = 𝟘
   ₀ ≺ ₁ = 𝟘
   ₁ ≺ ₀ = 𝟙
   ₁ ≺ ₁ = 𝟘
   p : is-prop-valued _≺_
   p ₀ ₀ = 𝟘-is-prop
   p ₀ ₁ = 𝟘-is-prop
   p ₁ ₀ = 𝟙-is-prop
   p ₁ ₁ = 𝟘-is-prop
   w : is-well-founded _≺_
   w ₀ = acc a
    where
     a : (y : 𝟚) → y ≺ ₀ → is-accessible _≺_ y
     a ₀ l = 𝟘-elim l
     a ₁ l = w ₁
   w ₁ = acc a
    where
     a : (y : 𝟚) → y ≺ ₁ → is-accessible _≺_ y
     a ₀ l = 𝟘-elim l
     a ₁ l = 𝟘-elim l
   e : is-extensional _≺_
   e ₀ ₀ u v = refl
   e ₀ ₁ u v = 𝟘-elim (u ₁ ⋆)
   e ₁ ₀ u v = 𝟘-elim (v ₁ ⋆)
   e ₁ ₁ u v = refl
   t : is-transitive _≺_
   t ₀ ₀ ₀ k l = l
   t ₀ ₁ ₀ k l = k
   t ₁ ₀ ₀ k l = ⋆
   t ₁ ₁ ₀ k l = l
   t ₀ ₀ ₁ k l = l
   t ₀ ₁ ₁ k l = l
   t ₁ ₀ ₁ k l = l
   t ₁ ₁ ₁ k l = l

\end{code}

The two ordinals are equivalent via the complement map and of course this is the
only order equivalence between the two ordinals.

\begin{code}

 𝟚ₒ-≃ₒ-𝟚ₒ' : 𝟚ₒ ≃ₒ 𝟚ₒ'
 𝟚ₒ-≃ₒ-𝟚ₒ' = f , f-preserves-order , f-is-equiv , f-preserves-order'
  where
   f : 𝟚 → 𝟚
   f = complement
   f-preserves-order : is-order-preserving 𝟚ₒ 𝟚ₒ' f
   f-preserves-order ₀ ₁ l = l
   f-preserves-order ₀ ₀ l = 𝟘-elim l
   f-preserves-order ₁ ₀ l = 𝟘-elim l
   f-preserves-order ₁ ₁ l = 𝟘-elim l
   f-is-equiv : is-equiv f
   f-is-equiv = qinvs-are-equivs f (f , complement-involutive , complement-involutive)
   f-preserves-order' : is-order-preserving 𝟚ₒ' 𝟚ₒ f
   f-preserves-order' ₀ ₀ l = 𝟘-elim l
   f-preserves-order' ₀ ₁ l = 𝟘-elim l
   f-preserves-order' ₁ ₀ l = l
   f-preserves-order' ₁ ₁ l = 𝟘-elim l

 complement-is-the-only-ordinal-equivalence-of-𝟚
  : (e : 𝟚ₒ ≃ₒ 𝟚ₒ') → ≃ₒ-to-fun 𝟚ₒ 𝟚ₒ' e ∼ complement
 complement-is-the-only-ordinal-equivalence-of-𝟚 e ₀ = II
   where
    f : 𝟚 → 𝟚
    f = ≃ₒ-to-fun 𝟚ₒ 𝟚ₒ' e
    I : ≃ₒ-to-fun 𝟚ₒ 𝟚ₒ' e ₀ ≠ ₀
    I p = l' (f ₁) (order-equivs-are-order-preserving 𝟚ₒ 𝟚ₒ'
                     (≃ₒ-to-fun-is-order-equiv 𝟚ₒ 𝟚ₒ' e)
                     ₀ ₁ ⋆)
     where
      l : (b : 𝟚) → ¬ (₀ ≺⟨ 𝟚ₒ' ⟩ b)
      l ₀ l = 𝟘-elim l
      l ₁ l = 𝟘-elim l
      l' : (b : 𝟚) → ¬ (f ₀ ≺⟨ 𝟚ₒ' ⟩ b)
      l' b = idtofun _ _ (ap (λ - → ¬ (- ≺⟨ 𝟚ₒ' ⟩ b)) (p ⁻¹)) (l b)
    II : f ₀ ＝ ₁
    II = different-from-₀-equal-₁ I
 complement-is-the-only-ordinal-equivalence-of-𝟚 e ₁ = II
  where
   f : 𝟚 → 𝟚
   f = ≃ₒ-to-fun 𝟚ₒ 𝟚ₒ' e
   I : ≃ₒ-to-fun 𝟚ₒ 𝟚ₒ' e ₁ ≠ ₁
   I p = l' (f ₀) (order-equivs-are-order-preserving 𝟚ₒ 𝟚ₒ'
                    (≃ₒ-to-fun-is-order-equiv 𝟚ₒ 𝟚ₒ' e)
                    ₀ ₁ ⋆)
    where
     l : (b : 𝟚) → ¬ (b ≺⟨ 𝟚ₒ' ⟩ ₁)
     l ₀ l = 𝟘-elim l
     l ₁ l = 𝟘-elim l
     l' : (b : 𝟚) → ¬ (b ≺⟨ 𝟚ₒ' ⟩ f ₁)
     l' b = idtofun _ _ (ap (λ - → ¬ (b ≺⟨ 𝟚ₒ' ⟩ -)) (p ⁻¹)) (l b)
   II : f ₁ ＝ ₀
   II = different-from-₁-equal-₀ I

\end{code}

As announced, identifying the ordinals 𝟚₀ and 𝟚ₒ' contradicts the K-axiom.

\begin{code}

 identification-of-𝟚ₒ-and-𝟚ₒ'-contradicts-K : 𝟚ₒ ＝ 𝟚ₒ' → ¬ K-axiom 𝓤₁
 identification-of-𝟚ₒ-and-𝟚ₒ'-contradicts-K pₒ K =
  p-is-not-refl (K (𝓤₀ ̇  ) p refl)
   where
    p : 𝟚 ＝ 𝟚
    p = ap ⟨_⟩ pₒ

    f : 𝟚 → 𝟚
    f = ⌜ idtoeq 𝟚 𝟚 p ⌝
    f' : 𝟚 → 𝟚
    f' = ⌜ ≃ₒ-gives-≃ 𝟚ₒ 𝟚ₒ' (idtoeqₒ 𝟚ₒ 𝟚ₒ' pₒ) ⌝

    I : f ∼ f'
    I b = ap (λ - → ⌜ - ⌝ b) (idtoeqₒ-naturality 𝟚ₒ 𝟚ₒ' pₒ)

    II : f' ∼ complement
    II = complement-is-the-only-ordinal-equivalence-of-𝟚 (idtoeqₒ 𝟚ₒ 𝟚ₒ' pₒ)

    p-is-not-refl : ¬ (p ＝ refl)
    p-is-not-refl e = zero-is-not-one
     (₀                     ＝⟨ refl ⟩
      ⌜ idtoeq 𝟚 𝟚 refl ⌝ ₀ ＝⟨ ap (λ - → ⌜ idtoeq 𝟚 𝟚 - ⌝ ₀) (e ⁻¹) ⟩
      f ₀                   ＝⟨ I ₀ ⟩
      f' ₀                  ＝⟨ II ₀ ⟩
      ₁                     ∎)

\end{code}

In particular, antisymmetry of the simulation preorder contradicts the K-axiom.
Note that we copied the definition of the simulation preorder ⊴ here from
Ordinals.OrdinalOfOrdinals since that module assumes univalence which we wish to
avoid here.

\begin{code}

 _⊴_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
 α ⊴ β = Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-simulation α β f

 antisymmetry-of-⊴ : (𝓤 : Universe) → 𝓤 ⁺ ̇
 antisymmetry-of-⊴ 𝓤 = (α β : Ordinal 𝓤) → α ⊴ β → β ⊴ α → α ＝ β

antisymmetry-of-⊴-contradicts-K : antisymmetry-of-⊴ 𝓤₀ → ¬ K-axiom 𝓤₁
antisymmetry-of-⊴-contradicts-K ⊴-antisym =
 identification-of-𝟚ₒ-and-𝟚ₒ'-contradicts-K I
  where
   I : 𝟚ₒ ＝ 𝟚ₒ'
   I = ⊴-antisym 𝟚ₒ 𝟚ₒ' I₁ I₂
    where
     I₁ : 𝟚ₒ ⊴ 𝟚ₒ'
     I₁ = (complement ,
            order-equivs-are-simulations 𝟚ₒ 𝟚ₒ' complement (pr₂ 𝟚ₒ-≃ₒ-𝟚ₒ'))
     I₂ : 𝟚ₒ' ⊴ 𝟚ₒ
     I₂ = (complement , order-equivs-are-simulations 𝟚ₒ' 𝟚ₒ complement
                          (pr₂ (≃ₒ-sym 𝟚ₒ 𝟚ₒ' (𝟚ₒ-≃ₒ-𝟚ₒ'))))
\end{code}

Finally, we show that preunivalence cannot prove that ⊴ is antisymmetric.
The argument uses that the K-axiom is not false (in the absence of univalence),
but of course it is not provable either, so we add ¬¬ K-axiom as a hypothesis.

We also need a small technical lemma, K-axiom-lower, that is perhaps better
placed in UF.Sets-Properties which it can't right now because of cyclic module
dependencies (which we could avoid by replacing ≃-Lift with an inline
construction).

\begin{code}

K-axiom-lower : K-axiom (𝓤 ⁺) → K-axiom 𝓤
K-axiom-lower {𝓤} K X = I
 where
  open import UF.Sets-Properties
  open import UF.UniverseEmbedding
  I : is-set X
  I = equiv-to-set (≃-Lift (𝓤 ⁺) X) (K (Lift (𝓤 ⁺) X))

preunivalence-cannot-show-antisymmetry-of-⊴
 : ¬¬ K-axiom 𝓤₁
 → ¬ (is-preunivalent 𝓤₀ → antisymmetry-of-⊴ 𝓤₀)
preunivalence-cannot-show-antisymmetry-of-⊴ K-consistent hyp = V
 where
  I : K-axiom 𝓤₁ → is-preunivalent 𝓤₀
  I K = K-gives-preunivalence (K-axiom-lower K) K

  II : is-preunivalent 𝓤₀ → antisymmetry-of-⊴ 𝓤₀
  II = hyp

  III : antisymmetry-of-⊴ 𝓤₀ → ¬ K-axiom 𝓤₁
  III = antisymmetry-of-⊴-contradicts-K

  IV : K-axiom 𝓤₁ → ¬ K-axiom 𝓤₁
  IV = III ∘ II ∘ I

  V : 𝟘
  V = K-consistent (λ K → IV K K)

\end{code}