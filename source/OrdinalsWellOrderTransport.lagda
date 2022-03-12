Martin Escardo, 23 December 2020.

We discuss how to transport well-orders along equivalences. This cannot
be done with univalence when the types live in different universes.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import UF-FunExt

module OrdinalsWellOrderTransport (fe : FunExt) where

open import OrdinalNotions
open import OrdinalsType
open import OrdinalsWellOrderArithmetic
open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Equiv
open import UF-Univalence

\end{code}

Univalence makes the following trivial:

\begin{code}

transport-ordinal-structure : is-univalent 𝓤
                            → (X Y : 𝓤 ̇ )
                            → X ≃ Y
                            → OrdinalStructure X ≃ OrdinalStructure Y
transport-ordinal-structure ua X Y = γ
 where
  δ : X ≡ Y → OrdinalStructure X ≡ OrdinalStructure Y
  δ = ap OrdinalStructure

  γ : X ≃ Y → OrdinalStructure X ≃ OrdinalStructure Y
  γ e = idtoeq (OrdinalStructure X) (OrdinalStructure Y) (δ (eqtoid ua X Y e))

\end{code}

The above can be done without univance.

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

   g : Y → X
   g = inverse f (⌜⌝-is-equiv 𝕗)

   η : g ∘ f ∼ id
   η = inverses-are-retractions f (⌜⌝-is-equiv 𝕗)

   ε : f ∘ g ∼ id
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
       y ≺ y' = g y < g y'

    order = _≺_

    order-preservation→ : (x x' : X) → x < x' → f x ≺ f x'
    order-preservation→ x x' = transport₂ _<_ ((η x)⁻¹) ((η x')⁻¹)

    order-preservation← : (y y' : Y) → y ≺ y' → g y < g y'
    order-preservation← y y' = id

\end{code}

Then our objective will be to prove the following:

\begin{code}

    transport-well-order : is-well-order _<_ ⇔ is-well-order _≺_

\end{code}

This is easy but painful, and will need a number of routine steps.

But notice that

\begin{code}

    private

      NB-< : type-of (is-well-order _<_) ≡ 𝓤 ⊔ 𝓥 ̇
      NB-< = refl

      NB-≺ : type-of (is-well-order _≺_) ≡ 𝓥 ̇
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
    is-prop-valued→ j y y' = j (g y) (g y')

    is-prop-valued← : is-prop-valued _≺_ → is-prop-valued _<_
    is-prop-valued← i x x' = γ
     where
      δ : is-prop (g (f x) < g (f x'))
      δ = i (f x) (f x')

      γ : is-prop (x < x')
      γ = transport₂ (λ x x' → is-prop (x < x')) (η x) (η x') δ

    is-well-founded→ : is-well-founded _<_ → is-well-founded _≺_
    is-well-founded→ = retract-well-founded _<_ _≺_ f g ε γ
     where
      γ : (x : X) (y : Y) → y ≺ f x → g y < x
      γ x y = transport ( g y <_) (η x)

    is-well-founded← : is-well-founded _≺_ → is-well-founded _<_
    is-well-founded← = retract-well-founded _≺_ _<_ g f η γ
     where
      γ : (y : Y) (x : X) → x < g y → f x ≺ y
      γ y x = transport (_< g y) ((η x)⁻¹)

    is-extensional→ : is-extensional _<_ → is-extensional _≺_
    is-extensional→ e y y' ϕ γ = p
     where
      α : (x : X) → x < g y → x < g y'
      α x l = transport (_< g y') (η x) a
       where
        a : g (f x) < g y'
        a = ϕ (f x) (transport (_< g y) ((η x)⁻¹) l)

      β : (x : X) → x < g y' → x < g y
      β x l = transport (_< g y) (η x) b
       where
        b : g (f x) < g y
        b = γ (f x) (transport (_< g y') ((η x)⁻¹) l)

      q : g y ≡ g y'
      q = e (g y) (g y') α β

      p : y ≡ y'
      p = sections-are-lc g (f , ε) q

    is-extensional← : is-extensional _≺_ → is-extensional _<_
    is-extensional← e x x' ϕ γ = p
     where
      α : (y : Y) → g y < g (f x) → g y < g (f x')
      α y l = transport (g y <_) ((η x')⁻¹) a
       where
        a : g y < x'
        a = ϕ (g y) (transport (g y <_) (η x) l)

      β : (y : Y) → g y < g (f x') → g y < g (f x)
      β y l = transport (g y <_) ((η x)⁻¹) b
       where
        b : g y < x
        b = γ (g y) (transport (g y <_) (η x') l)

      q : f x ≡ f x'
      q = e (f x) (f x') α β

      p : x ≡ x'
      p = sections-are-lc f (g , η) q

    is-transitive→ : is-transitive _<_ → is-transitive _≺_
    is-transitive→ t x y z = t (g x) (g y) (g z)

    is-transitive← : is-transitive _≺_ → is-transitive _<_
    is-transitive← t x y z = γ
     where
      δ : g (f x) < g (f y) → g (f y) < g (f z) → g (f x) < g (f z)
      δ = t (f x) (f y) (f z)

      γ : x < y → y < z → x < z
      γ = transport₃ (λ a b c → a < b → b < c → a < c) (η x) (η y) (η z) δ

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

      g : {x y : X} → x ≺ y → x < y
      g {x} {y} = inverse (f {x} {y}) (⌜⌝-is-equiv (𝕗 x y))

    is-prop-valued→ : is-prop-valued _<_ → is-prop-valued _≺_
    is-prop-valued→ i x y = equiv-to-prop (≃-sym (𝕗 x y)) (i x y)

    is-well-founded→ : is-well-founded _<_ → is-well-founded _≺_
    is-well-founded→ = retract-well-founded _<_ _≺_ id id
                        (λ x → refl) (λ x y → g {y} {x})

    is-extensional→ : is-extensional _<_ → is-extensional _≺_
    is-extensional→ e x y ϕ γ = p
     where
      α : (u : X) → u < x → u < y
      α u l = g (ϕ u (f l))

      β : (u : X) → u < y → u < x
      β u l = g (γ u (f l))

      p : x ≡ y
      p = e x y α β

    is-transitive→ : is-transitive _<_ → is-transitive _≺_
    is-transitive→ t x y z l m = f (t x y z (g l) (g m))

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

    transport-well-order : is-well-order _<_ ⇔ is-well-order _≺_
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

  g : ⟨ α ⟩ → X
  g = inverse f (⌜⌝-is-equiv 𝕗)

  ε : f ∘ g ∼ id
  ε = inverses-are-sections f (⌜⌝-is-equiv 𝕗)

  w⁻ : is-well-order _<_
  w⁻ = order-transfer-lemma₃.well-order→ ⟨ α ⟩ (underlying-order α) _<_
                               <-is-equivalent-to-≺ (is-well-ordered α)

  _≺_ : X → X → 𝓤 ̇
  x ≺ y = f x < f y

  w : is-well-order _≺_
  w = order-transfer-lemma₁.well-order→ ⟨ α ⟩ X (≃-sym 𝕗) _<_ w⁻

  g-preserves-order : (a b : ⟨ α ⟩) → a ≺⟨ α ⟩ b → g a ≺ g b
  g-preserves-order a b l = γ
   where
    δ : a < b
    δ = ⌜ <-is-equivalent-to-≺ a b ⌝ l

    γ : f (g a) < f (g b)
    γ = transport₂ _<_ ((ε a)⁻¹) ((ε b)⁻¹) δ

  f-preserves-order : (x y : X) → x ≺ y → f x ≺⟨ α ⟩ f y
  f-preserves-order x y = ⌜ <-is-equivalent-to-≺ (f x) (f y) ⌝⁻¹

  e : (X , _≺_ , w) ≃ₒ α
  e = (f , f-preserves-order , ⌜⌝-is-equiv 𝕗 , g-preserves-order)

  γ : Σ s ꞉ OrdinalStructure X , (X , s) ≃ₒ α
  γ = ((_≺_ , w) , e)

\end{code}
