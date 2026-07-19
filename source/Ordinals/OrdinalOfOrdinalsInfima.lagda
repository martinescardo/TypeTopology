Nicolai Kraus, mid 2025 (ideas); mid 2026 (Agda).

We show that the ordinal of ordinals in a universe 𝓤 has small infima. More
precisely, given a univalent universe 𝓤, every family F : I → Ordinal 𝓤 with
I : 𝓤 that is (merely) inhabited has an infimum in Ordinal 𝓤, i.e. a greatest
lower bound with respect to ⊴. This is (for now?) mostly a curiosity; I don't
know what infima could be good for.

Classically, every non-empty family of ordinals has a least element (a minimum).
Thus, classically, one would not ask about infima. However, it's more
interesting constructively. We can't have minima in the "obvious" sense, that
is, we can't have an operation that tells us which ordinal in a family is the
smallest: for a proposition P, the two-element family consisting of 𝟙 and P + P
has such a decidable minimum only if P is decidable. Nevertheless the family
still has an infimum (which we construct here), but constructively, we can't say
that it is in the original family.

The construction is this:

    inf F := Σ f ꞉ ((i : I) → ⟨ F i ⟩) , (∀ j k → F j ↓ f j ≃ₒ F k ↓ f k),

ordered pointwise by (f , _) ≺ (g , _) := ∀ i → f i ≺ g i. This file proves that
inf F is indeed the infimum.

Note: The construction of infima requires only few assumptions, namely
propositional truncation and univalence. The (known) constructions of *suprema*,
implemented in Ordinals.OrdinalOfOrdinalsSuprema, require more:
The construction of upper bounds in [Lemma 10.3.22, Uni2013], which Tom de Jong
proved to be a least upper bound and thus a supremum, requires set quotients.
An alternative constructions of suprema, due to Martin Escardo and implemented
by Tom de Jong, requires set replacement (a condition equivalent to having set
quotients).

In a complete lattice, the infimum of a family can be constructed as the
supremum of all lower bounds of the family. A priori, this construction is
large, as it quantifies over ordinals. Christian Sattler pointed out to me that
this can be phrased in a way that stays small, and the implementation is given
in this file as well. Note that the dual construction, i.e. constructing suprema
from infima, cannot avoid the size problem, and we do not expect that the
additional requirements for the suprema construction discussed above can be
avoided.

Caveat: There is also a different notion of infimum by Martin Escardo in the
file Ordinals.InfProperty.lagda from 2012. This notion refers to an infimum
within an ordinal, not necessarily the ordinal of ordinals.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Univalence

module Ordinals.OrdinalOfOrdinalsInfima
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open import MLTT.Spartan
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.ClassicalLogic
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

open PropositionalTruncation pt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import Ordinals.Arithmetic fe
open import Ordinals.AdditionProperties ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import UF.Size

\end{code}

Some basic lemmas that help proving that a type equipped with a relation is an
ordinal.

It works like this: Let α be an ordinal, X a type with a (prop-valued)
relation, and f : X → α a monotone map. If f is left-cancellable and has the
simulation property, then X is an ordinal.

\begin{code}

module domain-of-order-embedding
        {𝓤 𝓥 𝓦 : Universe}
        (α : Ordinal 𝓥)
        {X : 𝓤 ̇ }
        (_<_ : X → X → 𝓦 ̇ )
        (f : X → ⟨ α ⟩)
        (f-monotone : (x y : X) → x < y → f x ≺⟨ α ⟩ f y)
       where

 <-is-well-founded : is-well-founded _<_
 <-is-well-founded x = is-acc x (Well-foundedness α (f x))
  where
   is-acc : (x : X) → is-accessible (underlying-order α) (f x)
                    → is-accessible _<_ x
   is-acc x (acc s) = acc (λ y l → is-acc y (s (f y) (f-monotone y x l)))

 module _
         (<-prop-valued : is-prop-valued _<_)
         (f-lc          : left-cancellable f)
         (f-simulation  : (x : X) (a : ⟨ α ⟩) → a ≺⟨ α ⟩ f x
                                              → Σ x' ꞉ X , (x' < x)
                                                × (f x' ＝ a))
        where

  <-is-extensional : is-extensional _<_
  <-is-extensional x₁ x₂ u₁ u₂ =
   f-lc (Extensionality α (f x₁) (f x₂) (v x₁ x₂ u₁) (v x₂ x₁ u₂))
    where
     v : (x y : X) → ((z : X) → z < x → z < y)
       → (b : ⟨ α ⟩) → b ≺⟨ α ⟩ f x → b ≺⟨ α ⟩ f y
     v x y u b l = transport (λ - → - ≺⟨ α ⟩ f y) (pr₂ (pr₂ σ))
                    (f-monotone (pr₁ σ) y (u (pr₁ σ) (pr₁ (pr₂ σ))))
      where
       σ : Σ z ꞉ X , (z < x) × (f z ＝ b)
       σ = f-simulation x b l

  <-is-transitive : is-transitive _<_
  <-is-transitive x y z p q =
   transport (_< z) (f-lc (pr₂ (pr₂ σ))) (pr₁ (pr₂ σ))
    where
     σ : Σ x' ꞉ X , (x' < z) × (f x' ＝ f x)
     σ = f-simulation z (f x)
          (Transitivity α (f x) (f y) (f z)
            (f-monotone x y p) (f-monotone y z q))

  <-is-well-order : is-well-order _<_
  <-is-well-order =
   <-prop-valued , <-is-well-founded , <-is-extensional , <-is-transitive

\end{code}

We now state what it means for the ordinal of ordinals to have small infima. As
with small suprema, the statement is a proposition. (Note: I follow the
structure of Tom's OrdinalOfOrdinalsSuprema file.)

\begin{code}

Ordinal-Of-Ordinals-Has-Small-Infima : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ordinal-Of-Ordinals-Has-Small-Infima 𝓤 =
   (I : 𝓤 ̇ ) → ∥ I ∥ → (F : I → Ordinal 𝓤)
 → Σ γ ꞉ Ordinal 𝓤 , ((i : I) → γ ⊴ F i)
                   × ((β : Ordinal 𝓤) → ((i : I) → β ⊴ F i) → β ⊴ γ)

Ordinal-Of-Ordinals-Has-Small-Infima-is-prop :
 {𝓤 : Universe} → is-prop (Ordinal-Of-Ordinals-Has-Small-Infima 𝓤)
Ordinal-Of-Ordinals-Has-Small-Infima-is-prop {𝓤} =
 Π-is-prop fe' (λ I → Π-is-prop fe' (λ δ → Π-is-prop fe' (λ F → h I δ F)))
  where
   h : (I : 𝓤 ̇ ) (δ : ∥ I ∥) (F : I → Ordinal 𝓤)
     → is-prop (Σ γ ꞉ Ordinal 𝓤 , ((i : I) → γ ⊴ F i)
                                × ((β : Ordinal 𝓤) → ((i : I) → β ⊴ F i)
                                                   → β ⊴ γ))
   h I δ F (γ , γ-lb , γ-gt) (γ' , γ'-lb , γ'-gt) =
    to-subtype-＝ (λ γ → ×-is-prop
                         (Π-is-prop  fe' (λ i   → ⊴-is-prop-valued γ (F i)))
                         (Π₂-is-prop fe' (λ β _ → ⊴-is-prop-valued β γ)))
                 (⊴-antisym γ γ' (γ'-gt γ γ-lb) (γ-gt γ' γ'-lb))

\end{code}

The construction. Fix a family F : I → Ordinal 𝓤. The carrier inf, the order ≺,
and the projections (below) do not require I to be inhabited; only the
well-order structure (and hence the ordinal inf-Ord and the (greatest) lower
bound property) does, so those parts take an additional argument ∥ I ∥.

\begin{code}

module inf-construction
        {𝓤 : Universe}
        {I : 𝓤 ̇ }
        (F : I → Ordinal 𝓤)
       where

 is-compatible : ((i : I) → ⟨ F i ⟩) → 𝓤 ̇
 is-compatible f = (j k : I) → (F j ↓ f j) ≃ₒ (F k ↓ f k)

 being-compatible-is-prop : (f : (i : I) → ⟨ F i ⟩) → is-prop (is-compatible f)
 being-compatible-is-prop f =
  Π₂-is-prop fe' (λ j k → ≃ₒ-is-prop-valued fe' (F j ↓ f j) (F k ↓ f k))

 ⟨inf⟩ : 𝓤 ̇
 ⟨inf⟩ = Σ f ꞉ ((i : I) → ⟨ F i ⟩) , is-compatible f

 _≺_ : ⟨inf⟩ → ⟨inf⟩ → 𝓤 ̇
 (f , _) ≺ (g , _) = (i : I) → f i ≺⟨ F i ⟩ g i

 ≺-is-prop-valued : is-prop-valued _≺_
 ≺-is-prop-valued (f , _) (g , _) =
  Π-is-prop fe' (λ i → Prop-valuedness (F i) (f i) (g i))

\end{code}

For every i : I the projection inf-projection : ⟨inf⟩ → ⟨ F i ⟩ is monotone, an
embedding, and satisfies the simulation property.

\begin{code}

 module _ (i : I) where

  inf-projection : ⟨inf⟩ → ⟨ F i ⟩
  inf-projection (f , _) = f i

  inf-projection-monotone : (x y : ⟨inf⟩) → x ≺ y
                          → inf-projection x ≺⟨ F i ⟩ inf-projection y
  inf-projection-monotone (f , _) (g , _) l = l i

  inf-projection-lc : left-cancellable inf-projection
  inf-projection-lc {f , p} {g , q} e =
   to-subtype-＝ being-compatible-is-prop (dfunext fe' ptwise)
    where
     ptwise : (j : I) → f j ＝ g j
     ptwise j = ↓-lc-bis (F j) (f j) (g j) iso
      where
       iso : (F j ↓ f j) ≃ₒ (F j ↓ g j)
       iso = ≃ₒ-trans (F j ↓ f j) (F i ↓ f i) (F j ↓ g j)
              (p j i)
              (≃ₒ-trans (F i ↓ f i) (F i ↓ g i) (F j ↓ g j)
                (idtoeqₒ (F i ↓ f i) (F i ↓ g i) (ap (F i ↓_) e))
                (q i j))

  inf-projection-sim-property : (x : ⟨inf⟩) (a : ⟨ F i ⟩)
                              → a ≺⟨ F i ⟩ inf-projection x
                              → Σ y ꞉ ⟨inf⟩ , (y ≺ x) × (inf-projection y ＝ a)
  inf-projection-sim-property (g , q) a l =
   (h , r) , hb , ↓-lc (F i) (h i) a (key i)
   where
    aₑ : ⟨ F i ↓ g i ⟩
    aₑ = (a , l)
    w : (j : I) → ⟨ F j ↓ g j ⟩
    w j = ≃ₒ-to-fun (F i ↓ g i) (F j ↓ g j) (q i j) aₑ
    h : (j : I) → ⟨ F j ⟩
    h j = pr₁ (w j)
    hb : (j : I) → h j ≺⟨ F j ⟩ g j
    hb j = pr₂ (w j)
    key : (j : I) → (F j ↓ h j) ＝ (F i ↓ a)
    key j =
     (F j ↓ h j)         ＝⟨ ⦅1⦆ ⟩
     ((F j ↓ g j) ↓ w j) ＝⟨ ⦅2⦆ ⟩
     ((F i ↓ g i) ↓ aₑ)  ＝⟨ ⦅3⦆ ⟩
     (F i ↓ a)           ∎
      where
       ⦅1⦆ = (iterated-↓ (F j) (g j) (h j) (hb j)) ⁻¹
       ⦅2⦆ = (simulations-preserve-↓ (F i ↓ g i) (F j ↓ g j)
               (≃ₒ-to-⊴ (F i ↓ g i) (F j ↓ g j) (q i j)) aₑ) ⁻¹
       ⦅3⦆ = iterated-↓ (F i) (g i) a l
    r : is-compatible h
    r j k = idtoeqₒ (F j ↓ h j) (F k ↓ h k) (key j ∙ (key k) ⁻¹)

\end{code}

By the lemma from the beginning, using any i₀ : I extracted from the assumption
that I is inhabited, ≺ is a well-order, so inf is an ordinal
inf-Ord : Ordinal 𝓤.

\begin{code}

 ≺-is-well-order : ∥ I ∥ → is-well-order _≺_
 ≺-is-well-order = ∥∥-rec (being-well-order-is-prop _≺_ fe) γ
  where
   γ : I → is-well-order _≺_
   γ i₀ = domain-of-order-embedding.<-is-well-order
           (F i₀) _≺_ (inf-projection i₀) (inf-projection-monotone i₀)
           ≺-is-prop-valued (inf-projection-lc i₀)
           (inf-projection-sim-property i₀)

 inf-Ord : ∥ I ∥ → Ordinal 𝓤
 inf-Ord δ = ⟨inf⟩ , _≺_ , ≺-is-well-order δ

\end{code}

Each projection inf-projection is a simulation, so inf-Ord is a lower
bound of F.

\begin{code}

 inf-is-lower-bound : (δ : ∥ I ∥) (i : I) → inf-Ord δ ⊴ F i
 inf-is-lower-bound δ i =
  inf-projection i ,
  (inf-projection-sim-property i , inf-projection-monotone i)

\end{code}

inf-Ord is moreover the greatest lower bound. The argument is this:
Given β below every F i via simulations h i, the map m sends b to the compatible
tuple (λ i → h i b), because F i ↓ h i b ＝ β ↓ b ＝ F j ↓ h j b. It is monotone,
and it is a simulation because inf-projection i₀ ∘ m equals the simulation h i₀
and inf-projection i₀ is itself a simulation.

\begin{code}

 inf-is-greatest-lower-bound : (δ : ∥ I ∥) (β : Ordinal 𝓤)
                             → ((i : I) → β ⊴ F i) → β ⊴ inf-Ord δ
 inf-is-greatest-lower-bound δ β h = ∥∥-rec (⊴-is-prop-valued β (inf-Ord δ)) γ δ
  where
   hb : ⟨ β ⟩ → (i : I) → ⟨ F i ⟩
   hb b i = [ β , F i ]⟨ h i ⟩ b
   sp : (b : ⟨ β ⟩) (i : I) → (β ↓ b) ＝ (F i ↓ hb b i)
   sp b i = simulations-preserve-↓ β (F i) (h i) b
   m : ⟨ β ⟩ → ⟨inf⟩
   m b = hb b , (λ j k → idtoeqₒ (F j ↓ hb b j) (F k ↓ hb b k)
                          ((sp b j) ⁻¹ ∙ sp b k))
   m-is-order-preserving : is-order-preserving β (inf-Ord δ) m
   m-is-order-preserving b₁ b₂ l i =
    pr₂ ([ β , F i ]⟨ h i ⟩-is-simulation) b₁ b₂ l
   γ : I → β ⊴ inf-Ord δ
   γ i₀ = m , (m-is-initial-segment , m-is-order-preserving)
    where
     m-is-initial-segment : is-initial-segment β (inf-Ord δ) m
     m-is-initial-segment b (f , p) l =
      pr₁ seg , pr₁ (pr₂ seg) , inf-projection-lc i₀ (pr₂ (pr₂ seg))
       where
        seg : Σ b' ꞉ ⟨ β ⟩ , (b' ≺⟨ β ⟩ b) × (hb b' i₀ ＝ f i₀)
        seg = pr₁ ([ β , F i₀ ]⟨ h i₀ ⟩-is-simulation) b (f i₀) (l i₀)

\end{code}

We assumed that I is inhabited. What happens if we drop the assumption? If I is
empty, then inf F is not an ordinal because the order as defined above is
reflexive, vacuously. (There cannot be a greatest lower bound of the empty set,
because it would have to be an upper bound for all ordinals, which is impossible
by Burali-Forti.) If inf F is an ordinal, we show ¬¬I in the next lemma.
Much further below, we show that the unnegated conclusion is a constructive
taboo.

\begin{code}
 well-founded-gives-¬¬-inhabited : is-well-founded _≺_ → ¬¬ I
 well-founded-gives-¬¬-inhabited w n =
  irreflexive _≺_ x₀ (w x₀) x₀-is-reflexive
   where
    x₀ : ⟨inf⟩
    x₀ = (λ i → 𝟘-elim (n i)) , (λ j k → 𝟘-elim (n j))
    x₀-is-reflexive : x₀ ≺ x₀
    x₀-is-reflexive i = 𝟘-elim (n i)

 well-order-gives-¬¬-inhabited : is-well-order _≺_ → ¬¬ I
 well-order-gives-¬¬-inhabited =
  well-founded-gives-¬¬-inhabited ∘ well-foundedness _≺_

\end{code}

In any case, the above shows that Ord has small infima:

\begin{code}

ordinal-of-ordinals-has-small-infima :
 {𝓤 : Universe} → Ordinal-Of-Ordinals-Has-Small-Infima 𝓤
ordinal-of-ordinals-has-small-infima I δ F =
 inf-Ord δ , inf-is-lower-bound δ , inf-is-greatest-lower-bound δ
  where
   open inf-construction F

\end{code}

We repackage the construction for convenient use, writing inf δ F for the
infimum.

\begin{code}

module _ {𝓤 : Universe} {I : 𝓤 ̇ } (δ : ∥ I ∥) (F : I → Ordinal 𝓤) where

 private
  module IC = inf-construction F

 inf : Ordinal 𝓤
 inf = IC.inf-Ord δ

 inf-is-lower-bound : (i : I) → inf ⊴ F i
 inf-is-lower-bound = IC.inf-is-lower-bound δ

 inf-is-greatest-lower-bound : (β : Ordinal 𝓤)
                             → ((i : I) → β ⊴ F i) → β ⊴ inf
 inf-is-greatest-lower-bound = IC.inf-is-greatest-lower-bound δ

\end{code}

Some further properties of the infimum.

The infimum is monotone: if F i ⊴ G i for every i, then inf F ⊴ inf G.

\begin{code}

module _ {𝓤 : Universe} where

 inf-monotone : {I : 𝓤 ̇ } (δ : ∥ I ∥) (F G : I → Ordinal 𝓤)
              → ((i : I) → F i ⊴ G i)
              → inf δ F ⊴ inf δ G
 inf-monotone δ F G l =
  inf-is-greatest-lower-bound δ G (inf δ F)
   (λ i → ⊴-trans (inf δ F) (F i) (G i) (inf-is-lower-bound δ F i) (l i))

\end{code}

Some more minor observations.

Reindexing along ρ : J → I makes the family only smaller as a lower bound, so
inf F is below inf (F ∘ ρ).

\begin{code}

 inf-reindex : {I J : 𝓤 ̇ } (ε : ∥ J ∥) (ρ : J → I) (F : I → Ordinal 𝓤)
             → inf (∥∥-functor ρ ε) F ⊴ inf ε (F ∘ ρ)
 inf-reindex ε ρ F =
  inf-is-greatest-lower-bound ε (F ∘ ρ) (inf (∥∥-functor ρ ε) F)
   (λ j → inf-is-lower-bound (∥∥-functor ρ ε) F (ρ j))

\end{code}

The "dual" of the standard result for suprema:
Initial segments of the infimum are simultaneously initial segments of
every F i.

\begin{code}

 inf-↓ : {I : 𝓤 ̇ } (δ : ∥ I ∥) (F : I → Ordinal 𝓤) (i : I) (x : ⟨ inf δ F ⟩)
       → (inf δ F ↓ x)
       ＝ (F i ↓ [ inf δ F , F i ]⟨ inf-is-lower-bound δ F i ⟩ x)
 inf-↓ δ F i x =
  simulations-preserve-↓ (inf δ F) (F i) (inf-is-lower-bound δ F i) x

\end{code}

Can the hypothesis ∥ I ∥ be weakened to ¬¬ I in the argument that inf F is an
ordinal? The construction uses inhabitedness only to prove well-foundedness, and
by well-order-gives-¬¬-inhabited the weaker ¬¬ I is at least necessary.

We now show two that the implication
  "inf F is an ordinal => ∥ I ∥"
is a taboo; it implies LEM.

We look at the constant family at the empty ordinal 𝟘ₒ. For the infimum of this
to be an ordinal, ¬¬ I suffices. If we had the implication from above, then this
would imply ∥ I ∥.

(CAVEAT: What we're doing here is probably the wrong statement. We really should
discuss the following instead:
  Is "(∀ F → inf F is an ordinal) => ∥ I ∥" a taboo?
I don't know. Let's do that another time.)

\begin{code}

module _ {𝓤 : Universe} {I : 𝓤 ̇ } where

 open inf-construction (λ (_ : I) → 𝟘ₒ {𝓤})

 ¬¬-inhabited-gives-well-order : ¬¬ I → is-well-order _≺_
 ¬¬-inhabited-gives-well-order nn = ≺-is-prop-valued , wf , ext , tr
  where
   ¬inf : ¬ ⟨inf⟩
   ¬inf (f , _) = nn (λ i → 𝟘-elim (f i))
   wf : is-well-founded _≺_
   wf x = 𝟘-elim (¬inf x)
   ext : is-extensional _≺_
   ext x y _ _ = 𝟘-elim (¬inf x)
   tr : is-transitive _≺_
   tr x y z _ _ = 𝟘-elim (¬inf x)

 well-order-iff-¬¬-inhabited : is-well-order _≺_ ↔ ¬¬ I
 well-order-iff-¬¬-inhabited =
  well-order-gives-¬¬-inhabited , ¬¬-inhabited-gives-well-order

inf-Ordinal-Gives-Inhabited : (𝓤 : Universe) → 𝓤 ⁺ ̇
inf-Ordinal-Gives-Inhabited 𝓤 =
   (I : 𝓤 ̇ ) (F : I → Ordinal 𝓤)
 → is-well-order (inf-construction._≺_ F) → ∥ I ∥

inf-Ordinal-Gives-Inhabited-gives-LEM :
 {𝓤 : Universe} → inf-Ordinal-Gives-Inhabited 𝓤 → EM 𝓤
inf-Ordinal-Gives-Inhabited-gives-LEM {𝓤} b = DNE-gives-EM (fe 𝓤 𝓤₀) DNE-holds
 where
  DNE-holds : DNE 𝓤
  DNE-holds P P-is-prop nnp =
   ∥∥-rec P-is-prop id
    (b P (λ _ → 𝟘ₒ)
       (¬¬-inhabited-gives-well-order {𝓤} {P} nnp))

\end{code}

An alternative construction, following a suggestion by Christian Sattler: the
traditional construction of infima from suprema. The infimum is the supremum of
all ordinals that are ⊴ every member of the family (the "supremum of the lower
bounds"). Stated like this it ranges over a large type, but it can be made
small. Every lower bound β is the supremum of the successors (β ↓ b) +ₒ 𝟙ₒ of
its initial segments. Thus, it suffices to take the supremum of the small family
of those (F i ↓ x) +ₒ 𝟙ₒ that are themselves lower bounds:

    inf-as-sup F := sup (λ ((i , x , _) :
                        Σ i ꞉ I , Σ x ꞉ ⟨ F i ⟩ ,
                        ((j : I) → (F i ↓ x) +ₒ 𝟙ₒ ⊴ F j))
                          → (F i ↓ x) +ₒ 𝟙ₒ)

\begin{code}

module small-supremum-construction (sr : Set-Replacement pt) where

 open suprema pt sr

 module _ {𝓤 : Universe} {I : 𝓤 ̇ } (F : I → Ordinal 𝓤) where

  lb-successors : 𝓤 ̇
  lb-successors =
   Σ i ꞉ I , Σ x ꞉ ⟨ F i ⟩ , ((j : I) → ((F i ↓ x) +ₒ 𝟙ₒ) ⊴ F j)

  lb-successor-family : lb-successors → Ordinal 𝓤
  lb-successor-family (i , x , _) = (F i ↓ x) +ₒ 𝟙ₒ

  inf-as-sup : Ordinal 𝓤
  inf-as-sup = sup lb-successor-family

  inf-as-sup-is-lower-bound : (j : I) → inf-as-sup ⊴ F j
  inf-as-sup-is-lower-bound j =
   sup-is-lower-bound-of-upper-bounds lb-successor-family (F j)
    (λ (i , x , p) → p j)

  inf-as-sup-is-greatest-lower-bound : ∥ I ∥ → (β : Ordinal 𝓤)
                                     → ((j : I) → β ⊴ F j) → β ⊴ inf-as-sup
  inf-as-sup-is-greatest-lower-bound δ β β-lb =
   transport (_⊴ inf-as-sup)
    (supremum-of-successors-of-initial-segments pt sr β ⁻¹)
    (sup-is-lower-bound-of-upper-bounds (λ b → (β ↓ b) +ₒ 𝟙ₒ) inf-as-sup seg-⊴)
    where
     seg-⊴ : (b : ⟨ β ⟩) → ((β ↓ b) +ₒ 𝟙ₒ) ⊴ inf-as-sup
     seg-⊴ b = ∥∥-rec (⊴-is-prop-valued ((β ↓ b) +ₒ 𝟙ₒ) inf-as-sup) γ δ
      where
       γ : I → ((β ↓ b) +ₒ 𝟙ₒ) ⊴ inf-as-sup
       γ i₀ = transport (_⊴ inf-as-sup) (ap (_+ₒ 𝟙ₒ) (key ⁻¹))
               (sup-is-upper-bound lb-successor-family (i₀ , h b , p))
        where
         h : ⟨ β ⟩ → ⟨ F i₀ ⟩
         h = [ β , F i₀ ]⟨ β-lb i₀ ⟩
         key : (β ↓ b) ＝ (F i₀ ↓ h b)
         key = simulations-preserve-↓ β (F i₀) (β-lb i₀) b
         p : (j : I) → ((F i₀ ↓ h b) +ₒ 𝟙ₒ) ⊴ F j
         p j = transport (λ - → (- +ₒ 𝟙ₒ) ⊴ F j) key
                (⊴-trans ((β ↓ b) +ₒ 𝟙ₒ) β (F j)
                  (upper-bound-of-successors-of-initial-segments β b) (β-lb j))

\end{code}

By the uniqueness of greatest lower bounds, this agrees with the direct
construction whenever I is inhabited.

\begin{code}

  inf-as-sup-agrees-with-inf : (δ : ∥ I ∥) → inf-as-sup ＝ inf δ F
  inf-as-sup-agrees-with-inf δ =
   ⊴-antisym inf-as-sup (inf δ F)
    (inf-is-greatest-lower-bound δ F inf-as-sup inf-as-sup-is-lower-bound)
    (inf-as-sup-is-greatest-lower-bound δ (inf δ F) (inf-is-lower-bound δ F))

\end{code}

Yet another construction: The infimum as a greatest common initial segment.

This realises the infimum inside a single F i₀, rather than as a tuple.
Fix i₀ : I. Since inf F ⊴ F i₀, the infimum is (equivalent to) an
initial segment of F i₀; concretely it is the largest one that is simultaneously
an initial segment of every F j. So we keep exactly those x : ⟨ F i₀ ⟩ whose
initial segment F i₀ ↓ x is a common initial segment of the whole family:

    GCIS := Σ x ꞉ ⟨ F i₀ ⟩ , (∀ j → (F i₀ ↓ x) ⊲ F j),

ordered by the restriction of ≺⟨ F i₀ ⟩. This predicate is lower-closed, which
is what makes the induced order extensional (a general subtype order need not
be, see Ordinals.ShulmanTaboo). Like the direct construction, this one needs no
set quotients; it needs i₀ only to name the ambient ordinal. It is the exact
analogue, for the ordinal of ordinals, of describing a greatest common divisor
inside one of its multiples.

\begin{code}

module greatest-common-initial-segment
        {𝓤 : Universe} {I : 𝓤 ̇ }
        (δ : ∥ I ∥) (F : I → Ordinal 𝓤) (i₀ : I)
       where

 open inf-construction F

 is-common-lower-segment : ⟨ F i₀ ⟩ → 𝓤 ̇
 is-common-lower-segment x = (j : I) → Σ y ꞉ ⟨ F j ⟩ , (F i₀ ↓ x) ≃ₒ (F j ↓ y)

 being-common-lower-segment-is-prop : (x : ⟨ F i₀ ⟩)
                                       → is-prop (is-common-lower-segment x)
 being-common-lower-segment-is-prop x = Π-is-prop fe' γ
  where
   γ : (j : I) → is-prop (Σ y ꞉ ⟨ F j ⟩ , (F i₀ ↓ x) ≃ₒ (F j ↓ y))
   γ j (y , e) (y' , e') =
    to-subtype-＝ (λ y → ≃ₒ-is-prop-valued fe' (F i₀ ↓ x) (F j ↓ y))
     (↓-lc-bis (F j) y y'
       (≃ₒ-trans (F j ↓ y) (F i₀ ↓ x) (F j ↓ y')
         (≃ₒ-sym (F i₀ ↓ x) (F j ↓ y) e) e'))

 being-common-lower-segment-is-lower-closed :
    (x : ⟨ F i₀ ⟩) → is-common-lower-segment x
  → (z : ⟨ F i₀ ⟩) → z ≺⟨ F i₀ ⟩ x → is-common-lower-segment z
 being-common-lower-segment-is-lower-closed x cx z l j =
  pr₁ w , idtoeqₒ (F i₀ ↓ z) (F j ↓ pr₁ w) e
   where
    yⱼ : ⟨ F j ⟩
    yⱼ = pr₁ (cx j)
    eⱼ : (F i₀ ↓ x) ≃ₒ (F j ↓ yⱼ)
    eⱼ = pr₂ (cx j)
    w : ⟨ F j ↓ yⱼ ⟩
    w = ≃ₒ-to-fun (F i₀ ↓ x) (F j ↓ yⱼ) eⱼ (z , l)
    e : (F i₀ ↓ z) ＝ (F j ↓ pr₁ w)
    e = (F i₀ ↓ z)             ＝⟨ (iterated-↓ (F i₀) x z l) ⁻¹ ⟩
        ((F i₀ ↓ x) ↓ (z , l)) ＝⟨ simulations-preserve-↓ (F i₀ ↓ x) (F j ↓ yⱼ)
                                     (≃ₒ-to-⊴ (F i₀ ↓ x) (F j ↓ yⱼ) eⱼ)
                                     (z , l) ⟩
        ((F j ↓ yⱼ) ↓ w)       ＝⟨ iterated-↓ (F j) yⱼ (pr₁ w) (pr₂ w) ⟩
        (F j ↓ pr₁ w)          ∎

 GCIS : 𝓤 ̇
 GCIS = Σ x ꞉ ⟨ F i₀ ⟩ , is-common-lower-segment x

 _≪_ : GCIS → GCIS → 𝓤 ̇
 _≪_ = subtype-order (F i₀) is-common-lower-segment

 ≪-is-extensional : is-extensional _≪_
 ≪-is-extensional (x , cx) (y , cy) u v =
  to-subtype-＝ being-common-lower-segment-is-prop
   (Extensionality (F i₀) x y u' v')
   where
    u' : (z : ⟨ F i₀ ⟩) → z ≺⟨ F i₀ ⟩ x → z ≺⟨ F i₀ ⟩ y
    u' z l = u (z , being-common-lower-segment-is-lower-closed x cx z l) l
    v' : (z : ⟨ F i₀ ⟩) → z ≺⟨ F i₀ ⟩ y → z ≺⟨ F i₀ ⟩ x
    v' z l = v (z , being-common-lower-segment-is-lower-closed y cy z l) l

 gcis : Ordinal 𝓤
 gcis = GCIS , _≪_ ,
        subtype-order-is-prop-valued  (F i₀) is-common-lower-segment ,
        subtype-order-is-well-founded (F i₀) is-common-lower-segment ,
        ≪-is-extensional ,
        subtype-order-is-transitive   (F i₀) is-common-lower-segment

\end{code}

The projection (f , p) ↦ f i₀ corestricts to a map inf → GCIS, which is a
simulation. This map has a section which, for each j, reads off the point
realising the common segment. That makes it an order-isomorphism, so gcis is the
infimum.

\begin{code}

 to-gcis : ⟨ inf-Ord δ ⟩ → GCIS
 to-gcis (f , p) = f i₀ , (λ j → f j , p i₀ j)

 to-gcis-is-order-preserving : is-order-preserving (inf-Ord δ) gcis to-gcis
 to-gcis-is-order-preserving (f , p) (g , q) l = l i₀

 to-gcis-is-initial-segment : is-initial-segment (inf-Ord δ) gcis to-gcis
 to-gcis-is-initial-segment (f , p) (y , cy) l =
  pr₁ σ ,
  pr₁ (pr₂ σ) ,
  to-subtype-＝ being-common-lower-segment-is-prop (pr₂ (pr₂ σ))
   where
    σ : Σ z ꞉ ⟨inf⟩ , (z ≺ (f , p)) × (inf-projection i₀ z ＝ y)
    σ = inf-projection-sim-property i₀ (f , p) y l

 inf-⊴-gcis : inf-Ord δ ⊴ gcis
 inf-⊴-gcis = to-gcis , to-gcis-is-initial-segment , to-gcis-is-order-preserving

 from-gcis : GCIS → ⟨ inf-Ord δ ⟩
 from-gcis (x , cx) =
  (λ j → pr₁ (cx j)) ,
  (λ j k → ≃ₒ-trans (F j ↓ pr₁ (cx j)) (F i₀ ↓ x) (F k ↓ pr₁ (cx k))
             (≃ₒ-sym (F i₀ ↓ x) (F j ↓ pr₁ (cx j)) (pr₂ (cx j)))
             (pr₂ (cx k)))

 to-gcis-from-gcis : (w : GCIS) → to-gcis (from-gcis w) ＝ w
 to-gcis-from-gcis (x , cx) =
  to-subtype-＝ being-common-lower-segment-is-prop
   ((↓-lc-bis (F i₀) x (pr₁ (cx i₀)) (pr₂ (cx i₀))) ⁻¹)

 gcis-⊴-inf : gcis ⊴ inf-Ord δ
 gcis-⊴-inf = to-⊴ gcis (inf-Ord δ) ϕ
  where
   ϕ : (w : GCIS) → (gcis ↓ w) ⊲ inf-Ord δ
   ϕ w = from-gcis w ,
         ((gcis ↓ w)                     ＝⟨ ⦅1⦆ ⟩
          (gcis ↓ to-gcis (from-gcis w)) ＝⟨ ⦅2⦆ ⟩
          (inf-Ord δ ↓ from-gcis w)      ∎)
    where
     ⦅1⦆ = ap (gcis ↓_) ((to-gcis-from-gcis w) ⁻¹)
     ⦅2⦆ = (simulations-preserve-↓ (inf-Ord δ) gcis inf-⊴-gcis (from-gcis w)) ⁻¹

 gcis-is-infimum : gcis ＝ inf δ F
 gcis-is-infimum = ⊴-antisym gcis (inf δ F) gcis-⊴-inf inf-⊴-gcis

\end{code}

Another simple observation: infima commute with infima. An infimum over a Σ-type
is the infimum of the infima over the fibres. Everything follows from the
universal property and antisymmetry.

\begin{code}

module _ {𝓤 : Universe} {I : 𝓤 ̇ } {J : I → 𝓤 ̇ }
         (δᴵ : ∥ I ∥) (ε : (i : I) → ∥ J i ∥)
         (F : (Σ i ꞉ I , J i) → Ordinal 𝓤)
       where

 private
  δᴶ : ∥ Σ i ꞉ I , J i ∥
  δᴶ = ∥∥-rec ∥∥-is-prop (λ i → ∥∥-functor (λ j → i , j) (ε i)) δᴵ

  inner : I → Ordinal 𝓤
  inner i = inf (ε i) (λ j → F (i , j))

 inf-Fubini : inf δᴶ F ＝ inf δᴵ inner
 inf-Fubini = ⊴-antisym (inf δᴶ F) (inf δᴵ inner) below above
  where
   below : inf δᴶ F ⊴ inf δᴵ inner
   below = inf-is-greatest-lower-bound δᴵ inner (inf δᴶ F)
            (λ i → inf-is-greatest-lower-bound (ε i) (λ j → F (i , j))
                     (inf δᴶ F)
                     (λ j → inf-is-lower-bound δᴶ F (i , j)))
   above : inf δᴵ inner ⊴ inf δᴶ F
   above = inf-is-greatest-lower-bound δᴶ F (inf δᴵ inner)
            (λ (i , j) → ⊴-trans (inf δᴵ inner) (inner i) (F (i , j))
                           (inf-is-lower-bound δᴵ inner i)
                           (inf-is-lower-bound (ε i) (λ j → F (i , j)) j))

\end{code}
