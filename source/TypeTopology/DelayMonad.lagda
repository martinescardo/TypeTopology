Martin Escardo. 2018, 2023, 2024, 2026.

An incarnation of the delay monad.

The short 2018-2024 code was from from SquashedCantor, moved here on
16th September 2026.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module TypeTopology.DelayMonad (fe : FunExt) where

open import CoNaturals.Type
open import CoNaturals.UniversalProperty fe
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Sequence fe
open import Naturals.UniversalProperty
open import Notation.CanonicalMap
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Sets
open import UF.Sets-Properties
open import UF.Singleton-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

private
 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

\end{code}

A delayed element of X is a "time" u : ℕ∞ together with a partial
element of X, which is defined when u is finite.

\begin{code}

𝔻 : 𝓤 ̇ → 𝓤 ̇
𝔻 X = Σ u ꞉ ℕ∞ , (is-finite u → X)

𝔻-time : {X : 𝓤 ̇ } → 𝔻 X → ℕ∞
𝔻-time (u , π) = u

𝔻-value : {X : 𝓤 ̇ } (𝕕 : 𝔻 X) → is-finite (𝔻-time 𝕕) → X
𝔻-value (u , π) = π

\end{code}

The following two abbreviations for the transport of finiteness, moved
here from SquashedCantor on 17th September 2026, are used repeatedly
below.

\begin{code}

transport-finite : {u v : ℕ∞} (p : u ＝ v) → is-finite u → is-finite v
transport-finite = transport is-finite

transport-finite⁻¹ : {u v : ℕ∞} (p : u ＝ v) → is-finite v → is-finite u
transport-finite⁻¹ = transport⁻¹ is-finite

transport-value : (X : 𝓤 ̇ ) {u v : ℕ∞}
                  (p : u ＝ v)
                → (is-finite u → X)
                → (is-finite v → X)
transport-value X = transport (λ - → is-finite - → X)

\end{code}

Added 20th December 2023.

The delay monad structure.

\begin{code}

η𝔻 : {X : 𝓤 ̇ } → X → 𝔻 X
η𝔻 x = (Zero , λ _ → x)

δ𝔻 : {X : 𝓤 ̇ } → 𝔻 X → 𝔻 X
δ𝔻 (u , f) = (Succ u , f ∘ is-finite-down u)

\end{code}

TODO. Prove the (wild) monad laws.

Added 9th January 2024.

\begin{code}

𝔻-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
          → (X → Y)
          → (𝔻 X → 𝔻 Y)
𝔻-functor f (u , π) = (u , f ∘ π)

𝔻-functor-id : {X : 𝓤 ̇ }
             → 𝔻-functor (𝑖𝑑 X) ∼ 𝑖𝑑 (𝔻 X)
𝔻-functor-id d = refl

𝔻-functor-∘ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
              (f : X → Y) (g : Y → Z)
            → 𝔻-functor (g ∘ f) ＝ 𝔻-functor g ∘ 𝔻-functor f
𝔻-functor-∘ f g = refl

𝔻-functor-id-＝ : {X : 𝓤 ̇ }
               → 𝔻-functor (𝑖𝑑 X) ＝ 𝑖𝑑 (𝔻 X)
𝔻-functor-id-＝ = refl

𝔻-functor-∘-＝ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                (f : X → Y) (g : Y → Z)
               → 𝔻-functor (g ∘ f) ＝ 𝔻-functor g ∘ 𝔻-functor f
𝔻-functor-∘-＝ f g = refl

𝔻-is-set : {X : 𝓤 ̇ }
         → is-set X
         → is-set (𝔻 X)
𝔻-is-set {𝓤} {X} X-is-set = Σ-is-set
                             (ℕ∞-is-set fe')
                             (λ u → Π-is-set fe' (λ φ → X-is-set))

to-𝔻-＝ : {X : 𝓤 ̇ }
          (u u' : ℕ∞)
          (π  : is-finite u  → X)
          (π' : is-finite u' → X)
        → (Σ p ꞉ u ＝ u' , π ＝ π' ∘ transport-finite p)
        → (u , π) ＝[ 𝔻 X ] (u' , π')
to-𝔻-＝ {𝓤} {X} u u π π (refl , refl) = refl

from-𝔻-＝ : {X : 𝓤 ̇ }
            (u u' : ℕ∞)
            (π  : is-finite u  → X)
            (π' : is-finite u' → X)
          → (u , π) ＝[ 𝔻 X ] (u' , π')
          → Σ p ꞉ u ＝ u' , (π ＝ π' ∘ transport-finite p)
from-𝔻-＝ {𝓤} {X} u u π π refl = (refl , refl)

\end{code}

Added 16th September 2026.

A delayed element is either its value, when the time is zero, or the
delayed element with the time decreased by one.

\begin{code}

𝔻-out : {X : 𝓤 ̇ } → 𝔻 X → X + 𝔻 X
𝔻-out (u , π) = 𝟚-equality-cases
                 (λ (z : is-Zero u)
                       → inl (π (Zero-is-finite' fe' u z)))
                 (λ (p : is-positive u)
                       → inr (Pred u , π ∘ is-finite-up' fe' u))

𝔻-out₀ : {X : 𝓤 ̇ } (u : ℕ∞) (π : is-finite u → X) (z : is-Zero u)
       → 𝔻-out (u , π) ＝ inl (π (Zero-is-finite' fe' u z))
𝔻-out₀ u π = 𝟚-equality-cases₀

𝔻-out₁ : {X : 𝓤 ̇ } (u : ℕ∞) (π : is-finite u → X) (p : is-positive u)
       → 𝔻-out (u , π) ＝ inr (Pred u , π ∘ is-finite-up' fe' u)
𝔻-out₁ u π = 𝟚-equality-cases₁

\end{code}

We now show that the type 𝔻 X is a final coalgebra of the functor X + (-),
with the structure map 𝔻-out defined above.

\begin{code}

is-𝔻-coalgebra-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → (Y → X + Y)
                   → (Y → 𝔻 X)
                   → 𝓤 ⊔ 𝓥 ̇
is-𝔻-coalgebra-map k h = 𝔻-out ∘ h ∼ +functor id h ∘ k

\end{code}

That is, h is a coalgebra map when the following diagram commutes.

                     k
          Y ------------------> X + Y
          |                       |
          |                       |
        h |                       | X + h
          |                       |
          |                       |
          v                       v
         𝔻 X -----------------> X + 𝔻 X
                   𝔻-out

The map 𝔻-out is an equivalence, with the following inverse 𝔻-in, so
that a coalgebra map can be presented with 𝔻-in in place of it.

\begin{code}

𝔻-in : {X : 𝓤 ̇ } → X + 𝔻 X → 𝔻 X
𝔻-in (inl x)       = (Zero , λ _ → x)
𝔻-in (inr (u , π)) = (Succ u , π ∘ is-finite-down u)

𝔻-out-𝔻-in : {X : 𝓤 ̇ } (w : X + 𝔻 X) → 𝔻-out (𝔻-in w) ＝ w
𝔻-out-𝔻-in (inl x) = I
 where
  I = 𝔻-out (Zero , (λ _ → x)) ＝⟨ 𝔻-out₀ Zero (λ _ → x) refl ⟩
      inl x                    ∎
𝔻-out-𝔻-in (inr (u , π)) = II
 where
  II = 𝔻-out (Succ u , π ∘ is-finite-down u)                ＝⟨ II₀ ⟩
       (inr (Pred (Succ u) ,
        π ∘ is-finite-down u ∘ is-finite-up' fe' (Succ u))) ＝⟨ II₁ ⟩
       inr (u , π)                                          ∎
      where
       h : (φ : is-finite u)
         → π (is-finite-down u (is-finite-up' fe' (Succ u) φ)) ＝ π φ
       h φ = ap π (being-finite-is-prop fe' u _ _)

       II₀ = 𝔻-out₁ (Succ u) (π ∘ is-finite-down u) refl
       II₁ = ap inr (to-𝔻-＝ _ _ _ _ (refl , dfunext fe' h))

𝔻-in-𝔻-out : {X : 𝓤 ̇ } (d : 𝔻 X) → 𝔻-in (𝔻-out d) ＝ d
𝔻-in-𝔻-out (u , π) = 𝟚-equality-cases I II
 where
  I : is-Zero u → 𝔻-in (𝔻-out (u , π)) ＝ (u , π)
  I z = 𝔻-in (𝔻-out (u , π))                     ＝⟨ ap 𝔻-in (𝔻-out₀ u π z) ⟩
        𝔻-in (inl (π (Zero-is-finite' fe' u z))) ＝⟨ I₀ ⟩
        (u , π)                                  ∎
       where
        I₀ = to-𝔻-＝ _ _ _ _
              (((is-Zero-equal-Zero fe' z)⁻¹) ,
               dfunext fe' (λ φ → ap π (being-finite-is-prop fe' u _ _)))

  II : is-positive u → 𝔻-in (𝔻-out (u , π)) ＝ (u , π)
  II p = 𝔻-in (𝔻-out (u , π))                          ＝⟨ ap 𝔻-in (𝔻-out₁ u π p) ⟩
         𝔻-in (inr (Pred u , π ∘ is-finite-up' fe' u)) ＝⟨ II₀ ⟩
         (u , π)                                       ∎
        where
         II₀ = to-𝔻-＝ _ _ _ _
                (((positive-equal-Succ fe' p)⁻¹) ,
                 dfunext fe' (λ φ → ap π (being-finite-is-prop fe' u _ _)))

𝔻-out-is-equiv : {X : 𝓤 ̇ } → is-equiv (𝔻-out {𝓤} {X})
𝔻-out-is-equiv = qinvs-are-equivs 𝔻-out (𝔻-in , 𝔻-in-𝔻-out , 𝔻-out-𝔻-in)

𝔻-flip : {X : 𝓤 ̇ } (d : 𝔻 X) (w : X + 𝔻 X)
       → (𝔻-out d ＝ w) ≃ (d ＝ 𝔻-in w)
𝔻-flip d w = (𝔻-out d ＝ w)              ≃⟨ I ⟩
             (𝔻-out d ＝ 𝔻-out (𝔻-in w)) ≃⟨ II ⟩
             (d ＝ 𝔻-in w)               ■
            where
             I  = ≃-sym (transport-≃ (λ - → 𝔻-out d ＝ -) (𝔻-out-𝔻-in w))
             II = ≃-sym (ap 𝔻-out , ap-is-equiv 𝔻-out 𝔻-out-is-equiv)

\end{code}

For a coalgebra k : Y → X + Y, we show that the type

  Σ h ꞉ (Y → 𝔻 X) , is-𝔻-coalgebra-map k h

is a singleton, by a chain of type equivalences, as follows, where
item n is established by the definition stepₙ in the code below.

 1. For h : Y → 𝔻 X and y : Y, because 𝔻-out is an equivalence, the type

      𝔻-out (h y) ＝ +functor id h (k y)

    is equivalent to the type

      h y ＝ 𝔻-in (+functor id h (k y)).

 2. A map h : Y → 𝔻 X amounts to a time function t : Y → ℕ∞ together
    with values ν : Value t, where, for any t : Y → ℕ∞,

      Value t = (y : Y) → is-finite (t y) → X,

    via h = pair t ν, with

      pair t ν y = (t y , ν y).

 3. For y : Y, the element

      𝔻-in (+functor id (pair t ν) (k y)) : 𝔻 X

    is equal, by cases on k y, to the pair

      (time t (k y) , value t ν (k y)),

    where the functions

      time t    : X + Y → ℕ∞,
      value t ν : (w : X + Y) → is-finite (time t w) → X

    give the time Zero and the value x for w = inl x, and the time
    Succ (t y') and the value of ν at y' for w = inr y', so that, for
    h = pair t ν, the equation of step 1 becomes

      pair t ν y ＝ (time t (k y) , value t ν (k y)).

 4. Splitting the equation of step 3 into a time part and a value part,
    and collecting the time parts, the type of coalgebra maps becomes the
    type of quadruples (t , e , ν , q), where

      t : Y → ℕ∞,
      e : t ∼ time* t,
      ν : Value t,
      q : value-condition t ν e,

    with time* t y = time t (k y).

 5. The type t ∼ time* t of step 4 is equivalent to the type

      is-homomorphism k̅ t,

    where k̅ : Y → 𝟙 + Y is k followed by the map that forgets values,
    because both types are propositions, as ℕ∞ is a set.

 6. The type of pairs (t , e) is a singleton, which amounts to the
    finality of ℕ∞ as a coalgebra of the functor 1 + (-).

 7. Fix t : Y → ℕ∞ and e : t ∼ time* t. A witness that t y is finite is
    a natural number n together with an identification ι n ＝ t y, and
    so a function ν : Value t amounts to a function a : Π A, whose
    argument is the size n of the witness, where

      A n = (y : Y) → ι n ＝ t y → X.

 8. For ν : Value t, the value condition on ν is equivalent to the
    fixed-point condition

      ν y ψ ＝ value* ν y ψ,

    for all y : Y and all witnesses ψ that t y is finite, where

      value* ν y ψ = value t ν (k y) (e* y ψ)

    and e* y transports such a witness along e y. This condition is
    then split by the size n of ψ into the fixed-point condition at
    size n, for each n : ℕ.

 9. For the function a : Π A of step 7 corresponding to ν, the fixed-point
    conditions at sizes 0 and succ n say that

      a 0        ＝ a₀,
      a (succ n) ＝ σ n (a n),

    where the value

      a₀ : A 0

    and the induction step function

      σ : (n : ℕ) → A n → A (succ n)

    are defined by cases on k y.

10. That is, the function a is defined by induction from a₀ and σ. By
    the dependent universal property of ℕ as a natural numbers object with
    codomain A, for any a₀ : A 0 and any induction step function
    σ : (n : ℕ) → A n → A (succ n), there is a unique a : Π A defined by
    induction from them, and so the type

      Σ ν ꞉ Value t , value-condition t ν e

    of pairs (ν , q) is a singleton.

11. The type

      Σ (t , e) ꞉ (Σ t ꞉ (Y → ℕ∞) , t ∼ time* t) ,
                   Σ ν ꞉ Value t , value-condition t ν e,

    to which the type of coalgebra maps is equivalent by steps 1-4, is a
    sum of the singletons of step 10 over the singleton of step 6, and
    hence is a singleton, which completes the proof.

\begin{code}

private
 forget-value : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X + Y → 𝟙 {𝓤₀} + Y
 forget-value (inl x) = inl ⋆
 forget-value (inr y) = inr y

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (k : Y → X + Y) where

 private
  k̅ : Y → 𝟙 {𝓤₀} + Y
  k̅ = forget-value ∘ k

  Value : (Y → ℕ∞) → 𝓤 ⊔ 𝓥 ̇
  Value t = (y : Y) → is-finite (t y) → X

  time : (Y → ℕ∞) → X + Y → ℕ∞
  time t (inl x)  = Zero
  time t (inr y') = Succ (t y')

  time* : (Y → ℕ∞) → (Y → ℕ∞)
  time* t y = time t (k y)

  value : (t : Y → ℕ∞)
        → Value t
        → (w : X + Y)
        → is-finite (time t w)
        → X
  value t ν (inl x)  φ = x
  value t ν (inr y') φ = ν y' (is-finite-down (t y') φ)

  value-inl : (t : Y → ℕ∞)
              (ν : Value t)
              (y : Y) (x : X)
            → k y ＝ inl x
            → (φ : is-finite (time t (k y)))
            → value t ν (k y) φ ＝ x
  value-inl t ν y x q = transport⁻¹ E q (λ φ → refl)
   where
    E : X + Y → 𝓤 ̇
    E w = (φ : is-finite (time t w)) → value t ν w φ ＝ x

  value-inr : (t : Y → ℕ∞)
              (ν : Value t)
              (y y' : Y)
            → k y ＝ inr y'
            → (φ : is-finite (time t (k y))) (s : time t (k y) ＝ Succ (t y'))
            → value t ν (k y) φ
            ＝ ν y' (is-finite-down (t y') (transport-finite s φ))
  value-inr t ν y y' q = transport⁻¹ E q e
   where
    E : X + Y → 𝓤 ̇
    E w = (φ : is-finite (time t w)) (s : time t w ＝ Succ (t y'))
        → value t ν w φ
        ＝ ν y' (is-finite-down (t y') (transport-finite s φ))

    e : E (inr y')
    e φ s = ap (λ - → ν y' (is-finite-down (t y') -))
               (being-finite-is-prop fe' (Succ (t y'))
                 φ (transport-finite s φ))

  pair : (t : Y → ℕ∞) → Value t → (Y → 𝔻 X)
  pair t ν y = (t y , ν y)

  coalgebra-condition : (Y → 𝔻 X) → 𝓤 ⊔ 𝓥 ̇
  coalgebra-condition h = Π y ꞉ Y , h y ＝ 𝔻-in (+functor id h (k y))

\end{code}

This says the following diagram commutes, which is the diagram for
is-𝔻-coalgebra-map with its bottom arrow inverted.

                     k
          Y ------------------> X + Y
          |                       |
          |                       |
        h |                       | X + h
          |                       |
          |                       |
          v                       v
         𝔻 X <----------------- X + 𝔻 X
                   𝔻-in

\begin{code}

  𝔻-in-equation : (t : Y → ℕ∞)
                  (ν : Value t)
                  (w : X + Y)
                → 𝔻-in (+functor id (pair t ν) w) ＝ (time t w , value t ν w)
  𝔻-in-equation t ν (inl x)  = refl
  𝔻-in-equation t ν (inr y') = refl

\end{code}

When h is pair t ν, so that h has time t and values ν, the composite of
X + h with 𝔻-in, which is the right-hand and bottom edges of the above
diagram, is the pairing of the time map with the value map.

                      X + pair t ν
          X + Y ----------------------> X + 𝔻 X
               \                          |
                \                         |
                 \                        | 𝔻-in
                  \                       |
                   \                      |
                    \                     v
                     ------------------> 𝔻 X
                    (time t , value t ν)

\begin{code}

  step₁ : (h : Y → 𝔻 X) → is-𝔻-coalgebra-map k h ≃ coalgebra-condition h
  step₁ h = Π-cong fe' fe' (λ y → 𝔻-flip (h y) (+functor id h (k y)))

  step₂ : (Σ h ꞉ (Y → 𝔻 X) , coalgebra-condition h)
        ≃ (Σ (t , ν) ꞉ (Σ t ꞉ (Y → ℕ∞) , Value t) ,
             coalgebra-condition (pair t ν))
  step₂ = Σ-bicong _ _ ΠΣ-distr-≃ (λ h → ≃-refl _)

  step₃ : (t : Y → ℕ∞) (ν : Value t) → coalgebra-condition (pair t ν)
        ≃ (Π y ꞉ Y , pair t ν y ＝ (time t (k y) , value t ν (k y)))
  step₃ t ν = Π-cong fe' fe'
               (λ y → transport-≃
                       (λ - → pair t ν y ＝ -)
                       (𝔻-in-equation t ν (k y)))

  value-condition : (t : Y → ℕ∞) → Value t → t ∼ time* t → 𝓤 ⊔ 𝓥 ̇
  value-condition t ν e = Π y ꞉ Y , transport-value X (e y) (ν y)
                                  ＝ value t ν (k y)

  step₄ : (t : Y → ℕ∞) (ν : Value t)
        → (Π y ꞉ Y , pair t ν y ＝ (time t (k y) , value t ν (k y)))
        ≃ (Σ e ꞉ t ∼ time* t , value-condition t ν e)
  step₄ t ν = (Π y ꞉ Y , pair t ν y ＝ (time t (k y) , value t ν (k y))) ≃⟨ I ⟩
              (Π y ꞉ Y , Σ p ꞉ (t y ＝ time* t y) ,
                 transport-value X p (ν y) ＝ value t ν (k y))           ≃⟨ II ⟩
              (Σ e ꞉ t ∼ time* t , value-condition t ν e)                ■
             where
              I  = Π-cong fe' fe' (λ y → Σ-＝-≃)
              II = ΠΣ-distr-≃

  time-SUCC : (t : Y → ℕ∞) (w : X + Y)
            → time t w ＝ SUCC (𝟙+ t (forget-value w))
  time-SUCC t (inl x)  = refl
  time-SUCC t (inr y') = refl

  being-fixed-point-of-time*-is-prop : (t : Y → ℕ∞) → is-prop (t ∼ time* t)
  being-fixed-point-of-time*-is-prop t = Π-is-prop fe' (λ y → ℕ∞-is-set fe')

  being-homomorphism-is-prop : (t : Y → ℕ∞) → is-prop (is-homomorphism k̅ t)
  being-homomorphism-is-prop t =
   Π-is-set fe' (λ _ → +-is-set 𝟙 ℕ∞ (props-are-sets 𝟙-is-prop) (ℕ∞-is-set fe'))

  step₅ : (t : Y → ℕ∞) → (t ∼ time* t) ≃ is-homomorphism k̅ t
  step₅ t = logically-equivalent-props-are-equivalent
             (being-fixed-point-of-time*-is-prop t)
             (being-homomorphism-is-prop t)
             f
             g
   where
    f : t ∼ time* t → is-homomorphism k̅ t
    f e = coalg-mophism← k̅ t (dfunext fe' (λ y →
           t y               ＝⟨ e y ⟩
           time* t y         ＝⟨ time-SUCC t (k y) ⟩
           SUCC (𝟙+ t (k̅ y)) ∎))

    g : is-homomorphism k̅ t → t ∼ time* t
    g a y = t y               ＝⟨ happly (coalg-mophism→ k̅ t a) y ⟩
            SUCC (𝟙+ t (k̅ y)) ＝⟨ (time-SUCC t (k y))⁻¹ ⟩
            time* t y         ∎

  step₆ : ∃! t ꞉ (Y → ℕ∞) , t ∼ time* t
  step₆ = equiv-to-singleton
           (Σ-cong step₅)
           (PRED-is-the-homotopy-final-coalgebra k̅)

  module _ (t : Y → ℕ∞) (e : t ∼ time* t) where

   A : ℕ → 𝓤 ⊔ 𝓥 ̇
   A n = (y : Y) → ι n ＝ t y → X

   step₇ : Value t ≃ ((n : ℕ) → A n)
   step₇ = ((y : Y) → is-finite (t y) → X)    ≃⟨ I ⟩
           ((y : Y) (n : ℕ) → ι n ＝ t y → X) ≃⟨ Π-flip ⟩
           ((n : ℕ) → A n)                    ■
          where
           I = Π-cong fe' fe' (λ y → curry-uncurry fe)

   e* : (y : Y) → is-finite (t y) → is-finite (time* t y)
   e* y = transport-finite (e y)

   value* : Value t → Value t
   value* ν y ψ = value t ν (k y) (e* y ψ)

   value-condition-≃ : (ν : Value t) → value-condition t ν e ≃ (ν ≈ value* ν)
   value-condition-≃ ν = Π-cong fe' fe' IV
    where
     I : (y : Y)
       → (transport-value X (e y) (ν y) ＝ value t ν (k y))
       ≃ (ν y ∘ transport-finite ((e y)⁻¹) ＝ value t ν (k y))
     I y = transport-≃ (λ - → - ＝ value t ν (k y))
            (transport-along-→' is-finite (e y) (ν y))

     II : (y : Y)
        → (ν y ∘ transport-finite ((e y)⁻¹) ＝ value t ν (k y))
        ≃ (Π φ ꞉ is-finite (time t (k y)) ,
             ν y (transport-finite ((e y)⁻¹) φ) ＝ value t ν (k y) φ)
     II y = ≃-funext fe' _ _

     III : (y : Y)
         → (Π φ ꞉ is-finite (time t (k y)) ,
              ν y (transport-finite ((e y)⁻¹) φ) ＝ value t ν (k y) φ)
         ≃ (Π ψ ꞉ is-finite (t y) , ν y ψ ＝ value* ν y ψ)
     III y =
      (Π φ ꞉ is-finite (time t (k y)) ,
         ν y (transport-finite ((e y)⁻¹) φ) ＝ value t ν (k y) φ)   ≃⟨ III₀ ⟩
      (Π ψ ꞉ is-finite (t y) ,
         ν y (transport-finite ((e y)⁻¹) (e* y ψ)) ＝ value* ν y ψ) ≃⟨ III₁ ⟩
      (Π ψ ꞉ is-finite (t y) , ν y ψ ＝ value* ν y ψ)               ■
      where
       III₀ = ≃-sym (Π-change-of-variable-≃ fe _ (transport-≃ is-finite (e y)))
       III₁ = Π-cong fe' fe' (λ ψ →
               transport-≃
                (λ - → - ＝ value* ν y ψ)
                (ap (ν y) (being-finite-is-prop fe' (t y) _ ψ)))

     IV : (y : Y)
        → (transport-value X (e y) (ν y) ＝ value t ν (k y))
        ≃ (Π ψ ꞉ is-finite (t y) , ν y ψ ＝ value* ν y ψ)
     IV y =
      (transport-value X (e y) (ν y) ＝ value t ν (k y))          ≃⟨ I y ⟩
      (ν y ∘ transport-finite ((e y)⁻¹) ＝ value t ν (k y))       ≃⟨ II y ⟩
      (Π φ ꞉ is-finite (time t (k y)) ,
         ν y (transport-finite ((e y)⁻¹) φ) ＝ value t ν (k y) φ) ≃⟨ III y ⟩
      (Π ψ ꞉ is-finite (t y) , ν y ψ ＝ value* ν y ψ)             ■

   fixed-point-of-value*-at : Value t → ℕ → 𝓤 ⊔ 𝓥 ̇
   fixed-point-of-value*-at ν n = Π y ꞉ Y ,
                                  Π p ꞉ (ι n ＝ t y) ,
                                  ν y (n , p) ＝ value* ν y (n , p)

   fixed-point-of-value*-≃ : (ν : Value t)
                           → (ν ≈ value* ν)
                           ≃ (Π n ꞉ ℕ , fixed-point-of-value*-at ν n)
   fixed-point-of-value*-≃ ν =
    ν ≈ value* ν                             ≃⟨ I ⟩
    ((y : Y) (n : ℕ) (p : ι n ＝ t y)
        → ν y (n , p) ＝ value* ν y (n , p)) ≃⟨ Π-flip ⟩
    (Π n ꞉ ℕ , fixed-point-of-value*-at ν n) ■
    where
     I = Π-cong fe' fe' (λ y → curry-uncurry fe)

   step₈ : (ν : Value t)
         → value-condition t ν e ≃ (Π n ꞉ ℕ , fixed-point-of-value*-at ν n)
   step₈ ν =
    value-condition t ν e                    ≃⟨ value-condition-≃ ν ⟩
    ν ≈ value* ν                             ≃⟨ fixed-point-of-value*-≃ ν ⟩
    (Π n ꞉ ℕ , fixed-point-of-value*-at ν n) ■

   zero-impossible : (y y' : Y) → k y ＝ inr y' → ι 0 ≠ t y
   zero-impossible y y' q p = Zero-not-Succ
                               (Zero         ＝⟨ p ⟩
                                t y          ＝⟨ e y ⟩
                                time t (k y) ＝⟨ ap (time t) q ⟩
                                Succ (t y')  ∎)

   succ-impossible : (y : Y) (x : X) → k y ＝ inl x → (n : ℕ) → ι (succ n) ≠ t y
   succ-impossible y x q n p = Succ-not-Zero
                                (ι (succ n)   ＝⟨ p ⟩
                                 t y          ＝⟨ e y ⟩
                                 time t (k y) ＝⟨ ap (time t) q ⟩
                                 Zero         ∎)

   down : (y y' : Y) → k y ＝ inr y' → (n : ℕ) → ι (succ n) ＝ t y → ι n ＝ t y'
   down y y' q n p = Succ-lc
                      (ι (succ n)   ＝⟨ p ⟩
                       t y          ＝⟨ e y ⟩
                       time t (k y) ＝⟨ ap (time t) q ⟩
                       Succ (t y')  ∎)

   a₀-cases : (y : Y) (w : X + Y) → k y ＝ w → ι 0 ＝ t y → X
   a₀-cases y (inl x)  q p = x
   a₀-cases y (inr y') q p = 𝟘-elim (zero-impossible y y' q p)

   a₀ : A 0
   a₀ y = a₀-cases y (k y) refl

   a₀-cases-equation : (y : Y) (w : X + Y) (q : k y ＝ w) (p : ι 0 ＝ t y)
                     → a₀ y p ＝ a₀-cases y w q p
   a₀-cases-equation y w refl p = refl

   σ-cases : (y : Y) (w : X + Y)
           → k y ＝ w → (n : ℕ) → A n → ι (succ n) ＝ t y → X
   σ-cases y (inl x)  q n aₙ p = 𝟘-elim (succ-impossible y x q n p)
   σ-cases y (inr y') q n aₙ p = aₙ y' (down y y' q n p)

   σ : (n : ℕ) → A n → A (succ n)
   σ n aₙ y p = σ-cases y (k y) refl n aₙ p

   σ-cases-equation : (y : Y) (w : X + Y) (q : k y ＝ w)
                      (n : ℕ) (aₙ : A n) (p : ι (succ n) ＝ t y)
                    → σ n aₙ y p ＝ σ-cases y w q n aₙ p
   σ-cases-equation y w refl n aₙ p = refl

   value*-at-0-is-a₀ : (ν : Value t)
                       (y : Y) (p : ι 0 ＝ t y)
                     → value* ν y (0 , p) ＝ a₀ y p
   value*-at-0-is-a₀ ν y p = equality-cases (k y) I II
    where
     I : (x : X) → k y ＝ inl x → value* ν y (0 , p) ＝ a₀ y p
     I x q = value* ν y (0 , p) ＝⟨ value-inl t ν y x q (e* y (0 , p)) ⟩
             x                  ＝⟨ (a₀-cases-equation y (inl x) q p)⁻¹ ⟩
             a₀ y p             ∎

     II : (y' : Y) → k y ＝ inr y' → value* ν y (0 , p) ＝ a₀ y p
     II y' q = 𝟘-elim (zero-impossible y y' q p)

   value*-at-succ-is-σ : (ν : Value t)
                         (n : ℕ) (y : Y) (p : ι (succ n) ＝ t y)
                       → value* ν y (succ n , p)
                       ＝ σ n (λ y₁ p₁ → ν y₁ (n , p₁)) y p
   value*-at-succ-is-σ ν n y p = equality-cases (k y) I II
    where
     aₙ : A n
     aₙ y₁ p₁ = ν y₁ (n , p₁)

     I : (x : X) → k y ＝ inl x → value* ν y (succ n , p) ＝ σ n aₙ y p
     I x q = 𝟘-elim (succ-impossible y x q n p)

     II : (y' : Y) → k y ＝ inr y' → value* ν y (succ n , p) ＝ σ n aₙ y p
     II y' q = value* ν y (succ n , p)        ＝⟨ II₀ ⟩
               ν y' (is-finite-down (t y') φ) ＝⟨ II₁ ⟩
               ν y' (n , down y y' q n p)     ＝⟨ II₂ ⟩
               σ n aₙ y p                     ∎
              where
               φ : is-finite (Succ (t y'))
               φ = transport-finite (ap (time t) q) (e* y (succ n , p))

               II₀ = value-inr t ν y y' q (e* y (succ n , p)) (ap (time t) q)
               II₁ = ap (ν y') (being-finite-is-prop fe' (t y')
                                 (is-finite-down (t y') φ) (n , down y y' q n p))
               II₂ = (σ-cases-equation y (inr y') q n aₙ p)⁻¹

   fixed-point-of-value*-at-0-≃ : (ν : Value t)
                                → fixed-point-of-value*-at ν 0
                                ≃ (⌜ step₇ ⌝ ν 0 ＝ a₀)
   fixed-point-of-value*-at-0-≃ ν =
    fixed-point-of-value*-at ν 0                           ≃⟨ I ⟩
    (Π y ꞉ Y , Π p ꞉ (ι 0 ＝ t y) , ν y (0 , p) ＝ a₀ y p) ≃⟨ ≃-sym II ⟩
    (⌜ step₇ ⌝ ν 0 ＝ a₀)                                  ■
     where
      I = Π-cong fe' fe' (λ y → Π-cong fe' fe' (λ p →
           transport-≃ (λ - → ν y (0 , p) ＝ -) (value*-at-0-is-a₀ ν y p)))

      II : (⌜ step₇ ⌝ ν 0 ＝ a₀)
         ≃ (Π y ꞉ Y , Π p ꞉ (ι 0 ＝ t y) , ν y (0 , p) ＝ a₀ y p)
      II = ≃-funext₂ fe' fe' _ _

   fixed-point-of-value*-at-succ-≃
    : (ν : Value t) (n : ℕ)
    → fixed-point-of-value*-at ν (succ n)
    ≃ (⌜ step₇ ⌝ ν (succ n) ＝ σ n (⌜ step₇ ⌝ ν n))
   fixed-point-of-value*-at-succ-≃ ν n
    = fixed-point-of-value*-at ν (succ n)             ≃⟨ I ⟩
      (Π y ꞉ Y , Π p ꞉ (ι (succ n) ＝ t y) ,
         ν y (succ n , p) ＝ σ n (⌜ step₇ ⌝ ν n) y p) ≃⟨ II ⟩
      (⌜ step₇ ⌝ ν (succ n) ＝ σ n (⌜ step₇ ⌝ ν n))   ■
     where
      I  = Π-cong fe' fe' (λ y → Π-cong fe' fe' (λ p →
            transport-≃
             (λ - → ν y (succ n , p) ＝ -)
             (value*-at-succ-is-σ ν n y p)))
      II = ≃-sym (≃-funext₂ fe' fe' _ _)

   is-defined-by-induction : ((n : ℕ) → A n) → 𝓤 ⊔ 𝓥 ̇
   is-defined-by-induction a = (a 0 ＝ a₀) × ((n : ℕ) → a (succ n) ＝ σ n (a n))

   step₉ : (ν : Value t)
         → (Π n ꞉ ℕ , fixed-point-of-value*-at ν n)
         ≃ is-defined-by-induction (⌜ step₇ ⌝ ν)
   step₉ ν =
    (Π n ꞉ ℕ , fixed-point-of-value*-at ν n)             ≃⟨ I ⟩
    (fixed-point-of-value*-at ν 0
      × (Π n ꞉ ℕ , fixed-point-of-value*-at ν (succ n))) ≃⟨ II ⟩
    is-defined-by-induction (⌜ step₇ ⌝ ν)                ■
    where
     I  = head-tail-≃ {𝓤 ⊔ 𝓥} {fixed-point-of-value*-at ν}
     II = ×-cong
           (fixed-point-of-value*-at-0-≃ ν)
           (Π-cong fe' fe' (fixed-point-of-value*-at-succ-≃ ν))

   step₁₀ : ∃! ν ꞉ Value t , value-condition t ν e
   step₁₀ = equiv-to-singleton (Σ-bicong _ _ step₇ ϕ) (ℕ-is-nno-dep fe' A a₀ σ)
    where
     ϕ : (ν : Value t)
       → value-condition t ν e ≃ is-defined-by-induction (⌜ step₇ ⌝ ν)
     ϕ ν = value-condition t ν e                    ≃⟨ step₈ ν ⟩
           (Π n ꞉ ℕ , fixed-point-of-value*-at ν n) ≃⟨ step₉ ν ⟩
           is-defined-by-induction (⌜ step₇ ⌝ ν)    ■

  step₁₁ : ∃! (t , e) ꞉ (Σ t ꞉ (Y → ℕ∞) , t ∼ time* t) ,
                        Σ ν ꞉ Value t , value-condition t ν e
  step₁₁ = Σ-is-singleton step₆ (λ (t , e) → step₁₀ t e)

\end{code}

Putting the above steps together, we get our desired result.

\begin{code}

 𝔻-is-final-coalgebra : ∃! h ꞉ (Y → 𝔻 X) , is-𝔻-coalgebra-map k h
 𝔻-is-final-coalgebra = s
  where
   e = (Σ h ꞉ (Y → 𝔻 X) , is-𝔻-coalgebra-map k h)                ≃⟨ by-step₁ ⟩
       (Σ h ꞉ (Y → 𝔻 X) , coalgebra-condition h)                 ≃⟨ step₂ ⟩
       (Σ (t , ν) ꞉ (Σ t ꞉ (Y → ℕ∞) , Value t) ,
                    coalgebra-condition (pair t ν))              ≃⟨ Σ-assoc ⟩
       (Σ t ꞉ (Y → ℕ∞) , Σ ν ꞉ Value t ,
                         coalgebra-condition (pair t ν))         ≃⟨ by-step₃ ⟩
       (Σ t ꞉ (Y → ℕ∞) , Σ ν ꞉ Value t , Π y ꞉ Y ,
          pair t ν y ＝ (time t (k y) , value t ν (k y)))        ≃⟨ by-step₄ ⟩
       (Σ t ꞉ (Y → ℕ∞) , Σ ν ꞉ Value t ,
          Σ e ꞉ t ∼ time* t , value-condition t ν e)             ≃⟨ I ⟩
       (Σ t ꞉ (Y → ℕ∞) , Σ e ꞉ t ∼ time* t ,
                         Σ ν ꞉ Value t , value-condition t ν e)  ≃⟨ II ⟩
       (Σ (t , e) ꞉ (Σ t ꞉ (Y → ℕ∞) , t ∼ time* t) ,
                     Σ ν ꞉ Value t , value-condition t ν e)      ■
      where
       by-step₁ = Σ-cong step₁
       by-step₃ = Σ-cong (λ - → Σ-cong (step₃ -))
       by-step₄ = Σ-cong (λ - → Σ-cong (step₄ -))
       I        = Σ-cong (λ - → Σ-flip)
       II       = ≃-sym Σ-assoc

   s : is-singleton (Σ h ꞉ (Y → 𝔻 X) , is-𝔻-coalgebra-map k h)
   s = equiv-to-singleton e step₁₁

\end{code}
