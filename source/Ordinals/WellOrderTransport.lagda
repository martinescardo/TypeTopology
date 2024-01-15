Martin Escardo, 23 December 2020.

We discuss how to transport well-orders along equivalences. This cannot
be done with univalence when the types live in different universes.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module Ordinals.WellOrderTransport (fe : FunExt) where

open import Ordinals.Equivalence
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.WellOrderArithmetic
open import UF.Base
open import UF.Equiv
open import UF.Retracts
open import UF.Subsingletons
open import UF.Univalence

\end{code}

Univalence makes the following trivial:

\begin{code}

transport-ordinal-structure : is-univalent 𝓤
                            → (X Y : 𝓤 ̇ )
                            → X ≃ Y
                            → OrdinalStructure X ≃ OrdinalStructure Y
transport-ordinal-structure ua X Y = γ
 where
  δ : X ＝ Y → OrdinalStructure X ＝ OrdinalStructure Y
  δ = ap OrdinalStructure

  γ : X ≃ Y → OrdinalStructure X ≃ OrdinalStructure Y
  γ e = idtoeq (OrdinalStructure X) (OrdinalStructure Y) (δ (eqtoid ua X Y e))

\end{code}

The above can be done without univalence.

We could hope to get, more generally,

                               (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                             → X ≃ Y
                             → OrdinalStructure X ≃ OrdinalStructure Y.

But this not possible, not even assuming univalence.

The reason is that it is not possible to transport an order
_<_ : X → X → 𝓤 to an order _≺_ : Y → Y → 𝓥 along a given equivalence
X ≃ Y without propositional resizing, which we prefer not to assume.

However, if a particular order is resizable we can perform the
transport, although univalence won't help, which is what we do in this
file.

\begin{code}

module order-transfer-lemma₁
         (X : 𝓤 ̇ )
         (Y : 𝓥 ̇ )
         (𝕗 : X ≃ Y)
       where

  private
   f : X → Y
   f = ⌜ 𝕗 ⌝

   f⁻¹ : Y → X
   f⁻¹ = inverse f (⌜⌝-is-equiv 𝕗)

   η : f⁻¹ ∘ f ∼ id
   η = inverses-are-retractions f (⌜⌝-is-equiv 𝕗)

   ε : f ∘ f⁻¹ ∼ id
   ε = inverses-are-sections f (⌜⌝-is-equiv 𝕗)

\end{code}

The point is that the derived relation has values in the universe 𝓤,
but we would need it to have values in the universe 𝓥. If the relation
is proposition-valued and propositional resizing holds, then this is
not a problem, but we prefer not to assume propositional resizing.

So we assume that the order relation on X already has values in 𝓥,
and, as it turns out, this will be enough for our intended application
of this file.

So we make one further assumption and a definition:

\begin{code}

  module _ (_<_ : X → X → 𝓥 ̇ ) where
    private
       _≺_ : Y → Y → 𝓥 ̇
       y ≺ y' = f⁻¹ y < f⁻¹ y'

    order = _≺_

    order-preservation→ : (x x' : X) → x < x' → f x ≺ f x'
    order-preservation→ x x' = transport₂ _<_ ((η x)⁻¹) ((η x')⁻¹)

    order-preservation← : (y y' : Y) → y ≺ y' → f⁻¹ y < f⁻¹ y'
    order-preservation← y y' = id

\end{code}

Then our objective will be to prove the following:

\begin{code}

    transport-well-order : is-well-order _<_ ↔ is-well-order _≺_

\end{code}

This is easy but painful, and will need a number of routine steps.

But notice that

\begin{code}

    private

      NB-< : type-of (is-well-order _<_) ＝ 𝓤 ⊔ 𝓥 ̇
      NB-< = refl

      NB-≺ : type-of (is-well-order _≺_) ＝ 𝓥 ̇
      NB-≺ = refl

\end{code}

So we can't assert that the types (is-well-order _<_) and
(is-well-order _≺_) are equal.

However, we can easily establish their equivalence:

\begin{code}

    transport-well-order-≃ : (is-well-order _<_) ≃ (is-well-order _≺_)
    transport-well-order-≃ = logically-equivalent-props-are-equivalent
                              (being-well-order-is-prop (_<_) fe)
                              (being-well-order-is-prop (_≺_) fe)
                              (lr-implication transport-well-order)
                              (rl-implication transport-well-order)

\end{code}

And now we provide all steps needed to establish transport-well-order.

\begin{code}

    is-prop-valued→ : is-prop-valued _<_ → is-prop-valued _≺_
    is-prop-valued→ j y y' = j (f⁻¹ y) (f⁻¹ y')

    is-prop-valued← : is-prop-valued _≺_ → is-prop-valued _<_
    is-prop-valued← i x x' = γ
     where
      δ : is-prop (f⁻¹ (f x) < f⁻¹ (f x'))
      δ = i (f x) (f x')

      γ : is-prop (x < x')
      γ = transport₂ (λ x x' → is-prop (x < x')) (η x) (η x') δ

    is-well-founded→ : is-well-founded _<_ → is-well-founded _≺_
    is-well-founded→ = retract-well-founded _<_ _≺_ f f⁻¹ ε γ
     where
      γ : (x : X) (y : Y) → y ≺ f x → f⁻¹ y < x
      γ x y = transport ( f⁻¹ y <_) (η x)

    is-well-founded← : is-well-founded _≺_ → is-well-founded _<_
    is-well-founded← = retract-well-founded _≺_ _<_ f⁻¹ f η γ
     where
      γ : (y : Y) (x : X) → x < f⁻¹ y → f x ≺ y
      γ y x = transport (_< f⁻¹ y) ((η x)⁻¹)

    is-extensional→ : is-extensional _<_ → is-extensional _≺_
    is-extensional→ e y y' ϕ γ = p
     where
      I : (x : X) → x < f⁻¹ y → x < f⁻¹ y'
      I x l = transport (_< f⁻¹ y') (η x) a
       where
        a : f⁻¹ (f x) < f⁻¹ y'
        a = ϕ (f x) (transport (_< f⁻¹ y) ((η x)⁻¹) l)

      II : (x : X) → x < f⁻¹ y' → x < f⁻¹ y
      II x l = transport (_< f⁻¹ y) (η x) b
       where
        b : f⁻¹ (f x) < f⁻¹ y
        b = γ (f x) (transport (_< f⁻¹ y') ((η x)⁻¹) l)

      q : f⁻¹ y ＝ f⁻¹ y'
      q = e (f⁻¹ y) (f⁻¹ y') I II

      p : y ＝ y'
      p = sections-are-lc f⁻¹ (f , ε) q

    is-extensional← : is-extensional _≺_ → is-extensional _<_
    is-extensional← e x x' ϕ γ = p
     where
      I : (y : Y) → f⁻¹ y < f⁻¹ (f x) → f⁻¹ y < f⁻¹ (f x')
      I y l = transport (f⁻¹ y <_) ((η x')⁻¹) a
       where
        a : f⁻¹ y < x'
        a = ϕ (f⁻¹ y) (transport (f⁻¹ y <_) (η x) l)

      II : (y : Y) → f⁻¹ y < f⁻¹ (f x') → f⁻¹ y < f⁻¹ (f x)
      II y l = transport (f⁻¹ y <_) ((η x)⁻¹) b
       where
        b : f⁻¹ y < x
        b = γ (f⁻¹ y) (transport (f⁻¹ y <_) (η x') l)

      q : f x ＝ f x'
      q = e (f x) (f x') I II

      p : x ＝ x'
      p = sections-are-lc f (f⁻¹ , η) q

    is-transitive→ : is-transitive _<_ → is-transitive _≺_
    is-transitive→ t x y z = t (f⁻¹ x) (f⁻¹ y) (f⁻¹ z)

    is-transitive← : is-transitive _≺_ → is-transitive _<_
    is-transitive← t x y z = II
     where
      I : f⁻¹ (f x) < f⁻¹ (f y) → f⁻¹ (f y) < f⁻¹ (f z) → f⁻¹ (f x) < f⁻¹ (f z)
      I = t (f x) (f y) (f z)

      II : x < y → y < z → x < z
      II = transport₃ (λ a b c → a < b → b < c → a < c) (η x) (η y) (η z) I

\end{code}

Putting all this together, we get the desired result:

\begin{code}

    well-order→ : is-well-order _<_ → is-well-order _≺_
    well-order→ (p , w , e , t) = is-prop-valued→ p ,
                                  is-well-founded→ w ,
                                  is-extensional→ e ,
                                  is-transitive→ t

    well-order← : is-well-order _≺_ → is-well-order _<_
    well-order← (p , w , e , t) = is-prop-valued← p ,
                                  is-well-founded← w ,
                                  is-extensional← e ,
                                  is-transitive← t

    transport-well-order = well-order→ , well-order←

\end{code}

So we see how much work univalence is performing behind the scenes,
when it is available, as in the construction
transport-ordinal-structure.

\begin{code}

module order-transfer-lemma₂
         (X   : 𝓤 ̇ )
         (_<_ : X → X → 𝓥 ̇ )
         (_≺_ : X → X → 𝓦 ̇ )
         (𝕗 : (x y : X) → (x < y) ≃ (x ≺ y))
       where

    private
      f : {x y : X} → x < y → x ≺ y
      f {x} {y} = ⌜ 𝕗 x y ⌝

      f⁻¹ : {x y : X} → x ≺ y → x < y
      f⁻¹ {x} {y} = inverse (f {x} {y}) (⌜⌝-is-equiv (𝕗 x y))

    is-prop-valued→ : is-prop-valued _<_ → is-prop-valued _≺_
    is-prop-valued→ i x y = equiv-to-prop (≃-sym (𝕗 x y)) (i x y)

    is-well-founded→ : is-well-founded _<_ → is-well-founded _≺_
    is-well-founded→ = retract-well-founded _<_ _≺_ id id
                        (λ x → refl) (λ x y → f⁻¹ {y} {x})

    is-extensional→ : is-extensional _<_ → is-extensional _≺_
    is-extensional→ e x y ϕ γ = p
     where
      I : (u : X) → u < x → u < y
      I u l = f⁻¹ (ϕ u (f l))

      II : (u : X) → u < y → u < x
      II u l = f⁻¹ (γ u (f l))

      p : x ＝ y
      p = e x y I II

    is-transitive→ : is-transitive _<_ → is-transitive _≺_
    is-transitive→ t x y z l m = f (t x y z (f⁻¹ l) (f⁻¹ m))

module order-transfer-lemma₃
         (X   : 𝓤 ̇ )
         (_<_ : X → X → 𝓤 ̇ )
         (_≺_ : X → X → 𝓥 ̇ )
         (𝕗 : (x y : X) → (x < y) ≃ (x ≺ y))
       where

    well-order→ : is-well-order _<_ → is-well-order _≺_
    well-order→ (p , w , e , t) = is-prop-valued→ p ,
                                  is-well-founded→ w ,
                                  is-extensional→ e ,
                                  is-transitive→ t
     where
      open order-transfer-lemma₂ X _<_ _≺_ 𝕗

    well-order← : is-well-order _≺_ → is-well-order _<_
    well-order← (p , w , e , t) = is-prop-valued→ p ,
                                  is-well-founded→ w ,
                                  is-extensional→ e ,
                                  is-transitive→ t
     where
      open order-transfer-lemma₂ X _≺_ _<_ (λ x y → ≃-sym (𝕗 x y))

    transport-well-order : is-well-order _<_ ↔ is-well-order _≺_
    transport-well-order = well-order→ , well-order←

    transport-well-order-≃ : (is-well-order _<_) ≃ (is-well-order _≺_)
    transport-well-order-≃ = logically-equivalent-props-are-equivalent
                               (being-well-order-is-prop (_<_) fe)
                               (being-well-order-is-prop (_≺_) fe)
                               (lr-implication transport-well-order)
                               (rl-implication transport-well-order)
\end{code}

We can transport structures of ordinals with resizable order:

\begin{code}

resizable-order : Ordinal 𝓤 → (𝓥 : Universe) → 𝓤 ⊔ (𝓥 ⁺) ̇
resizable-order α 𝓥 = Σ _<_ ꞉ (⟨ α ⟩ → ⟨ α ⟩ → 𝓥 ̇ ) ,
                              ((x y : ⟨ α ⟩) → (x ≺⟨ α ⟩ y) ≃ (x < y))


transfer-structure : (X : 𝓤 ̇ ) (α : Ordinal 𝓥)
                   → X ≃ ⟨ α ⟩
                   → resizable-order α 𝓤
                   → Σ s ꞉ OrdinalStructure X , (X , s) ≃ₒ α
transfer-structure {𝓤} {𝓥} X α 𝕗 (_<_ , <-is-equivalent-to-≺) = γ
 where
  f : X → ⟨ α ⟩
  f = ⌜ 𝕗 ⌝

  f⁻¹ : ⟨ α ⟩ → X
  f⁻¹ = inverse f (⌜⌝-is-equiv 𝕗)

  ε : f ∘ f⁻¹ ∼ id
  ε = inverses-are-sections f (⌜⌝-is-equiv 𝕗)

  w⁻ : is-well-order _<_
  w⁻ = order-transfer-lemma₃.well-order→ ⟨ α ⟩ (underlying-order α) _<_
                               <-is-equivalent-to-≺ (is-well-ordered α)

  _≺_ : X → X → 𝓤 ̇
  x ≺ y = f x < f y

  w : is-well-order _≺_
  w = order-transfer-lemma₁.well-order→ ⟨ α ⟩ X (≃-sym 𝕗) _<_ w⁻

  f⁻¹-preserves-order : (a b : ⟨ α ⟩) → a ≺⟨ α ⟩ b → f⁻¹ a ≺ f⁻¹ b
  f⁻¹-preserves-order a b l = II
   where
    I : a < b
    I = ⌜ <-is-equivalent-to-≺ a b ⌝ l

    II : f (f⁻¹ a) < f (f⁻¹ b)
    II = transport₂ _<_ ((ε a)⁻¹) ((ε b)⁻¹) I

  f-preserves-order : (x y : X) → x ≺ y → f x ≺⟨ α ⟩ f y
  f-preserves-order x y = ⌜ <-is-equivalent-to-≺ (f x) (f y) ⌝⁻¹

  e : (X , _≺_ , w) ≃ₒ α
  e = (f , f-preserves-order , ⌜⌝-is-equiv 𝕗 , f⁻¹-preserves-order)

  γ : Σ s ꞉ OrdinalStructure X , (X , s) ≃ₒ α
  γ = ((_≺_ , w) , e)

\end{code}
