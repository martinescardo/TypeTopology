Marc Bezem, Thierry Coquand, Peter Dybjer, Martin Escardo
18th March 2025.

Discussion about whether a certain transport can be performed more
easily using univalence than "by hand". In particular, does
cumulativity help?

This discussion is inconclusive for the moment.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.transport-discussion where

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import UF.Univalence
open import UF.UniverseEmbedding
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.Equivalence

\end{code}

The following transport is performed by hand in the following imported
module.

\begin{code}

module _ (fe : FunExt) where

 open import Ordinals.WellOrderTransport fe

 _ : (X : 𝓤 ̇ ) (α : Ordinal 𝓥)
   → X ≃ ⟨ α ⟩
   → resizable-order α 𝓤
   → Σ s ꞉ OrdinalStructure X , (X , s) ≃ₒ α
 _ = transfer-structure

\end{code}

Can it be done, instead, using univalence in the absence of
cumulativity? If not, would cumulativity help?

We consider a simplified version of the problem to reduce labour. We
could even remove the requirement that there is at most one edge
between any two vertices, but this is useful to prove a no-go theorem
below. We could also require that the type V of vertices is a set, but
we try to keep things as simple as possible.

\begin{code}

reflexive-structure : (𝓦 : Universe) → 𝓣 ̇  → 𝓦 ⁺ ⊔ 𝓣 ̇
reflexive-structure 𝓦 V = Σ _⇒_ ꞉ (V → V → 𝓦 ̇)
                                 , ((v : V) → v ⇒ v)
                                 × ((v v' : V) → is-prop (v ⇒ v'))

Reflexive-Graph : (𝓦 𝓣 : Universe) → (𝓦 ⊔ 𝓣)⁺ ̇
Reflexive-Graph 𝓦 𝓣 = Σ V ꞉ 𝓣 ̇ , reflexive-structure 𝓦 V

\end{code}

We now formulate the notion of reflexive graph equivalence, for the
above notion of reflexive graph. Using SIP, and assuming univalence,
we can show that for graphs in the same universes, identity is
canonically equivalent to this notion of reflexive graph
equivalence. But we won't bother to prove this, at least not for the
moment.

\begin{code}

_≃ʳᵍ_ : {𝓦 𝓣 𝓦' 𝓣' : Universe}
      → Reflexive-Graph 𝓦 𝓣 → Reflexive-Graph 𝓦' 𝓣' → 𝓦 ⊔ 𝓣 ⊔ 𝓦' ⊔ 𝓣' ̇
(V , _⇒_ , _) ≃ʳᵍ (V' , _⇒'_ , _)
 = Σ f ꞉ (V ≃ V'), ((v₀ v₁ : V') → (⌜ f ⌝⁻¹ v₀ ⇒ ⌜ f ⌝⁻¹ v₁) ≃ (v₀ ⇒' v₁))

\end{code}

So here is our experimental discussion.

\begin{code}

module discussion
        (𝓤 𝓥 : Universe)
        (𝓐@(A , _⇒_ , ⇒-refl , ⇒-is-prop-valued) : Reflexive-Graph 𝓥 𝓥)
        (_⇒'_ : A → A → 𝓤 ̇ )
        (resizing-assumption : (a b : A) → (a ⇒ b) ≃ (a ⇒' b))
        (X : 𝓤 ̇ )
        (f : X ≃ A)
        (ua : is-univalent (𝓤 ⊔ 𝓥))
        (sorry : {𝓦 : Universe} {S : 𝓦 ̇} → S)
      where

\end{code}

We don't have cumulativity, so we lift explicitly.

\begin{code}

 X⁺ A⁺ : 𝓤 ⊔ 𝓥 ̇
 X⁺ = Lift (𝓤 ⊔ 𝓥) X
 A⁺ = Lift (𝓤 ⊔ 𝓥) A

 II : X⁺ ≃ A⁺
 II = X⁺ ≃⟨ Lift-≃ (𝓤 ⊔ 𝓥) X ⟩
      X  ≃⟨ f ⟩
      A  ≃⟨ ≃-Lift (𝓤 ⊔ 𝓥) A ⟩
      A⁺ ■

\end{code}

The following apologies can be filled by transporting by hand as in
the function `transfer-structure` mentioned above.

Presumably they don't need proof in a universe-cumulative system,
where X⁺ and A⁺ are simply X and A, so that we have false apologies.

\begin{code}

 _⇒⁺_ : A⁺ → A⁺ → 𝓥 ̇
 a ⇒⁺ b = sorry

 ⇒⁺-refl : (a : A⁺) → a ⇒⁺ a
 ⇒⁺-refl = sorry

 ⇒⁺-is-prop-valued : (a b : A⁺) → is-prop (a ⇒⁺ b)
 ⇒⁺-is-prop-valued = sorry

 rsₐ : reflexive-structure 𝓥 A⁺
 rsₐ = _⇒⁺_ , ⇒⁺-refl , ⇒⁺-is-prop-valued

 I : X⁺ ＝ A⁺
 I = eqtoid ua (X⁺) (A⁺) II

 rsₓ : reflexive-structure 𝓥 X⁺
 rsₓ = transport⁻¹ (reflexive-structure 𝓥) I rsₐ

\end{code}

But there is limit to the number of false apologies one can make.

The following needs more than cumulativity. And this is why we have
the above assumptions `_⇒'_` and `resizing-assumption` (which
correspond to the `resizable-order` condition in `transfer-structure`).
Without them, we get a no-go theorem (see `resizing-taboo` below).

So the following are genuine apologies: They can't just hold on the
nose by cumulativity.

\begin{code}

 _⇒ₓ_ : X → X → 𝓤 ̇
 _⇒ₓ_ = sorry

 ⇒ₓ-refl : (x : X) → x ⇒ₓ x
 ⇒ₓ-refl = sorry

 ⇒ₓ-is-prop-valued : (x y : X) → is-prop (x ⇒ₓ y)
 ⇒ₓ-is-prop-valued = sorry

 𝓧 : Reflexive-Graph 𝓤 𝓤
 𝓧 = X , _⇒ₓ_ , ⇒ₓ-refl , ⇒ₓ-is-prop-valued

 transfer-structure-analogue : 𝓧 ≃ʳᵍ 𝓐
 transfer-structure-analogue = sorry

\end{code}

Of course all the apologies can be removed, even without cumulativity,
by following the strategy of `transfer-structure` by transporting
structure and properties by hand, without univalence.

The question here is whether univalence, perhaps with the help of
cumulativity, can avoid transport by hand.

We now formulate and prove the no-go theorem. Because it holds in the
absence of cumulativity, it also holds in its presence.

The following type is a distilled version of the type of the function
`transfer-structure`, but without the `resizable-order` assumption.

\begin{code}

Transport-Assumption : 𝓤ω
Transport-Assumption =
   {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (A : 𝓥 ̇ )
   (f : X ≃ A)
   (rsₐ : reflexive-structure 𝓥 A)
 → Σ rsₓ ꞉ reflexive-structure 𝓤 X , (X , rsₓ) ≃ʳᵍ (A , rsₐ)

open import UF.Size
open import UF.EquivalenceExamples

resizing-taboo : Transport-Assumption → Propositional-Resizing
resizing-taboo t {𝓥} {𝓤} = γ
 where
  module _ (P : 𝓥 ̇) (P-is-prop : is-prop P) where
   X : 𝓤 ̇
   X = 𝟙 {𝓤} + 𝟙 {𝓤}

   A : 𝓥 ̇
   A = 𝟙 {𝓥} + 𝟙 {𝓥}

   I : X ≃ A
   I = +-cong one-𝟙-only one-𝟙-only

   _⇒_ : A → A → 𝓥 ̇
   inl ⋆ ⇒ inl ⋆ = 𝟙
   inl ⋆ ⇒ inr ⋆ = 𝟙 -- It's not important what we choose in this case.
   inr ⋆ ⇒ inl ⋆ = P
   inr ⋆ ⇒ inr ⋆ = 𝟙

   ⇒-refl : (a : A) → a ⇒ a
   ⇒-refl (inl ⋆) = ⋆
   ⇒-refl (inr ⋆) = ⋆

   ⇒-is-prop-valued : (a b : A) → is-prop (a ⇒ b)
   ⇒-is-prop-valued (inl ⋆) (inl ⋆) = 𝟙-is-prop
   ⇒-is-prop-valued (inl ⋆) (inr ⋆) = 𝟙-is-prop
   ⇒-is-prop-valued (inr ⋆) (inl ⋆) = P-is-prop
   ⇒-is-prop-valued (inr ⋆) (inr ⋆) = 𝟙-is-prop

   rₐ : reflexive-structure 𝓥 A
   rₐ = (_⇒_ , ⇒-refl , ⇒-is-prop-valued)

   II : Σ rₓ ꞉ reflexive-structure 𝓤 X , (X , rₓ) ≃ʳᵍ (A , rₐ)
   II = t X A I rₐ

   III : type-of II → P is 𝓤 small
   III ((_⇒ₓ_ , ⇒ₓ-refl , ⇒ₓ-is-prop-valued) , f , g) =
    Pₓ , IV
    where
     Pₓ : 𝓤 ̇
     Pₓ = ⌜ f ⌝⁻¹ (inr ⋆) ⇒ₓ ⌜ f ⌝⁻¹ (inl ⋆)

     Pₓ-is-prop : is-prop Pₓ
     Pₓ-is-prop = ⇒ₓ-is-prop-valued (⌜ f ⌝⁻¹ (inr ⋆)) (⌜ f ⌝⁻¹ (inl ⋆))

     IV : Pₓ ≃ P
     IV = g (inr ⋆) (inl ⋆)

   γ : P is 𝓤 small
   γ = III II

\end{code}

NB. If we wanted to prove the converse, we would still have to chase
equivalences by hand, as far as we know at the time of writing, unless
we have propositional resizing on-the-nose like UniMath. But notice
that propositional resizing on-the-nose is not unknown to be
consistent.

In other words, there are propositional resizing *axioms* (which are
known to be consistent, and in the above no-go theorem we have a
propositional resizing axiom) and there are propositional resizing
*rules* for the type theory (which are not known to be consistent).

If we hadn't assumed that the edge relation of a reflexive graph is a
proposition, we would instead be able to show that every type in any
universe is equivalent to any type in any universe we wish, which is
of course false, as "there are more types in larger universes".
