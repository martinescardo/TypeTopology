Tom de Jong, 11–19 November 2026.

Prompted by a question of Robbert Krebbers (9 November 2026), we explore a
constructive approach to Hessenberg addition.
This binary operation on ordinals, typically denoted by ⊕ or by #, and also
known as the natural sum, is commutative and associative, the former in contrast
to ordinary ordinal addition.

A typical classical definition of Hessenberg addition [Kap. XX, Hes06] goes via
Cantor normal forms, but the Hessenberg sum α ⊕ β can also be characterized, via
transfinite recursion, as the least ordinal strictly above α ⊕ γ and δ ⊕ β for
γ < β and δ < α. This characterization is attributed to Conway, see
[Theorem 2.4, Alt17] (and also [Sta24]).
In what follows we adopt this as a suitable constructive definition, replacing
the (a priori large) quantification over ordinals γ < β and δ < α by a small
quantification over elements b : ⟨ β ⟩ and a : ⟨ α ⟩ (which give rise to
suitable ordinals via their initial segments).

With this definition, we give constructive proofs of the following properties of
Hessenberg addition:
  * commutativity, i.e. α ⊕ β ＝ β ⊕ α;
  * associativity, i.e. (α ⊕ β) ⊕ γ ＝ α ⊕ (β ⊕ γ);
  * neutrality of 𝟘ₒ, i.e. α ⊕ 𝟘ₒ ＝ α;
  * strict order preservation and reflection, i.e. δ ⊕ α ⊲ δ ⊕ β ⇔ α ⊲ β.
These properties were chosen as an axiomatization of "natural sums" by Carruth
[Car42] and Hessenberg addition is shown to be the smallest such natural sum,
see also [HPV23] for a recent take on Carruth's axioms.
In addition to these properties we also show that Hessenberg addition is left
cancellable, i.e. δ ⊕ α ＝ δ ⊕ β implies α ＝ β, as well as strictly
inflationary for a summand with a least element, i.e. 𝟙ₒ ⊴ β implies α ⊲ α ⊕ β.

We characterize the initial segments of α ⊕ β as arising from one of three
(possibly overlapping cases):
   * (α ↓ a) ⊕ β,
   * α ⊕ (β ↓ b),
   * (α ↓ a) ⊕ (β ↓ b).
This gives rise to an induction principle that is used to prove associativity
for instance.

Finally, we show that a few claims about Hessenberg addition are inherently
classical by proving that they imply excluded middle. These include:
  * monotonicity, i.e. α ⊴ β implies δ ⊕ α ⊴ δ ⊕ β;
  * being inflationary, i.e. α ⊴ α ⊕ β;
  * being above ordinary addition, i.e. α +ₒ β ⊴ α ⊕ β;
  * commuting with successors, i.e. α ⊕ (β +ₒ 𝟙ₒ) ＝ (α ⊕ β) +ₒ 𝟙ₒ.
This last property is classically proved as [Lemma 3.3b), dJP77]; the
penultimate property is classically proved as [Proposition 5.1, Alt17] and
[Theorem 1.IV, Car42].

In all cited works, classical logic is assumed. A notable exception is a paper
by Michael Rathjen [Rat16] where he also defines Hessenberg addition by
transfinite recursion [Defintion 7.2, Rat16] and proves that it is commutative
and preserves the strict order [Lemma 7.3, Rat16].
What is new here are constructive proofs of additional properties, like
associativity, as well as the reduction to excluded middle for some statements
that hold classically.
Another, non-fundamental difference (cf. the file Iterative/Ordinals.lagda), is
that Rathjen works with ordinals qua hereditarily transitive sets in CZF,
whereas we work with ordinals qua well-orders in HoTT.

REFERENCES

[Alt17] Harry J. Altman. 'Intermediate airthmetic operations on ordinal numbers'.
        Mathematical Logic Quarterly, vol. 63, issue 3–4, pp. 228–242, 2017.
        https://doi.org/10.1002/malq.201600006
        https://arxiv.org/abs/1501.05747

[Car42] Philip W. Carruth. 'Arithmetic of ordinals with applications to the
        theory of ordered Abelian groups'.
        Bulletin of the American Math. Society, vol. 48, pp. 262–271, 1942.
        https://doi.org/10.1090/S0002-9904-1942-07649-X

[dJP77] D. H. J de Jongh and Rohit Parikh.
        'Well-partial orderings and hierarchies'
        Indagationes Mathematicae (Proceedings), vol. 80, issue 3,
        pp. 195–207, 1977.
        https://doi.org/10.1016/1385-7258(77)90067-1

[Hes06] Gerhard Hessenberg. 'Grundbegriffe der Mengenlehre'.
        Abhandlungen der Fries'schen Schule, I. Band, 4. Heft,
        Vandenhoeck & Ruprecht, 1906.
        https://archive.org/download/grundbegriffede00hessgoog/grundbegriffede00hessgoog.pdf

[HPV23] Lorenz Halbeisen and Pedro Pablo Pérez-Velasco.
        'On Carruth’s axioms for natural sums and products'.
        European Journal of Mathematics, vol. 9, article no. 97, 2023
        https://doi.org/10.1007/s40879-023-00696-z

[Rat16] Michael Rathjen.
        'Remarks on Barr’s Theorem: Proofs in Geometric Theories'.
        In: 'Concepts of Proof in Mathematics, Philosophy, and Computer
        Science', edited by Dieter Probst and Peter Schuster, pp. 347–374,
        De Gruyter, 2016.
        https://doi.org/10.1515/9781501502620-019
        https://arxiv.org/pdf/1603.03374

[Sta24] 'Hessenberg sum/natural sum of ordinals definition'. 2024.
        https://math.stackexchange.com/questions/4852808/hessenberg-sum-natural-sum-of-ordinals-definition

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Hessenberg
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import MLTT.Plus-Properties
open import MLTT.Spartan

open import UF.Base
open import UF.ClassicalLogic
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Maps
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying

open suprema pt sr
open PropositionalTruncation pt

\end{code}

The following is a sufficient binary transfinite induction principle. The most
general version would have (b : ⟨ β ⟩) → P γ (β ↓ b) for an arbitrary ordinal γ
(instead of the fixed α) as an hypothesis, but that isn't needed for our
purposes here.

\begin{code}

double-transfinite-induction-on-OO
 : (P : Ordinal 𝓤 → Ordinal 𝓤 → 𝓥 ̇ )
 → ((α β : Ordinal 𝓤) → ((a : ⟨ α ⟩) → P (α ↓ a) β)
                      → ((b : ⟨ β ⟩) → P α (β ↓ b))
                      → P α β)
 → (α β : Ordinal 𝓤) → P α β
double-transfinite-induction-on-OO {𝓤} {𝓥} P h = λ α β → I (α , β)
 where
  I : ((α , β) : Ordinal 𝓤 × Ordinal 𝓤) → P α β
  I = Transfinite-induction (OO 𝓤 ×ₒ OO 𝓤) (uncurry P)
       (λ (α , β) h' → h α β (λ a → h' ((α ↓ a) , β) (inr (refl , a , refl)))
                             (λ b → h' (α , (β ↓ b)) (inl (b , refl))))

double-transfinite-recursion-on-OO
 : {X : 𝓥 ̇ }
 → ((α β : Ordinal 𝓤) → ((a : ⟨ α ⟩) → X) → ((b : ⟨ β ⟩) → X) → X)
 → Ordinal 𝓤 → Ordinal 𝓤 → X
double-transfinite-recursion-on-OO = double-transfinite-induction-on-OO _

double-transfinite-recursion-on-OO-behaviour
 : {X : 𝓥 ̇ }
 → (r : (α β : Ordinal 𝓤) → ((a : ⟨ α ⟩) → X) → ((b : ⟨ β ⟩) → X) → X)
 → (α β : Ordinal 𝓤)
 → double-transfinite-recursion-on-OO r α β
   ＝ r α β (λ a → double-transfinite-recursion-on-OO r (α ↓ a) β)
            (λ b → double-transfinite-recursion-on-OO r α (β ↓ b))
double-transfinite-recursion-on-OO-behaviour {𝓥} {𝓤} {X} r = λ α β → I (α , β)
 where
  I : ((α , β) : Ordinal 𝓤 × Ordinal 𝓤)
    → double-transfinite-recursion-on-OO r α β ＝ r α β _ _
  I = Transfinite-induction-behaviour fe (OO 𝓤 ×ₒ OO 𝓤) (λ _ → X)
       (λ (α , β) h → r α β (λ a → h ((α ↓ a) , β) (inr (refl , (a , refl))))
                            (λ b → h (α , (β ↓ b)) (inl (b , refl))))

\end{code}

It is also convenient to consider strict suprema, i.e. for a family of
ordinals αᵢ indexed by a small type I, the least ordinal *strictly* above
each αᵢ. The construction for this is simple: take the sup over all successors
of αᵢ.

NB. If this finds application(s) outside this file, it should be factored out.

\begin{code}

module _
        {I : 𝓤 ̇ }
       where

 sup⁺ : (I → Ordinal 𝓤) → Ordinal 𝓤
 sup⁺ α = sup (λ i → α i +ₒ 𝟙ₒ)

 sup⁺-is-strict-upper-bound : {α : I → Ordinal 𝓤} (i : I) → α i ⊲ sup⁺ α
 sup⁺-is-strict-upper-bound {α} i =
  ⊲-⊴-gives-⊲ (α i) (α i +ₒ 𝟙ₒ) (sup⁺ α)
   (successor-increasing (α i))
   (sup-is-upper-bound _ i)

 sup⁺-is-least-strict-upper-bound : (α : I → Ordinal 𝓤) (β : Ordinal 𝓤)
                                  → ((i : I) → α i ⊲ β) → sup⁺ α ⊴ β
 sup⁺-is-least-strict-upper-bound α β h =
  sup-is-lower-bound-of-upper-bounds (λ i → α i +ₒ 𝟙ₒ) β
   (λ i → ⊲-gives-successor-⊴ (α i) β (h i))

\end{code}

We now define the Hessenberg sum α ⊕ β of two ordinals α and β by binary
transfinite recursion as the strict supremum of α ⊕ (β ↓ b) and (α ↓ a) ⊕ β.

For performance reasons, the definition is marked abstract with an explicit
unfolding lemma.

\begin{code}

abstract
 _⊕_ : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤
 _⊕_ {𝓤} = double-transfinite-recursion-on-OO (λ α β r₁ r₂ → sup⁺ (cases r₁ r₂))

 ⊕-behaviour : (α β : Ordinal 𝓤)
             → α ⊕ β ＝ sup⁺ (cases (λ a → (α ↓ a) ⊕ β) (λ b → α ⊕ (β ↓ b)))
 ⊕-behaviour {𝓤} = double-transfinite-recursion-on-OO-behaviour
                    (λ α β r₁ r₂ → sup⁺ (cases r₁ r₂))

\end{code}

Commutativity follows straightforwardly by (double) transfinite induction.

\begin{code}

⊕-is-commutative : (α β : Ordinal 𝓤) → α ⊕ β ＝ β ⊕ α
⊕-is-commutative {𝓤} = double-transfinite-induction-on-OO _ I
 where
  I : (α β : Ordinal 𝓤)
    → ((a : ⟨ α ⟩) → ((α ↓ a) ⊕ β) ＝ (β ⊕ (α ↓ a)))
    → ((b : ⟨ β ⟩) → (α ⊕ (β ↓ b)) ＝ ((β ↓ b) ⊕ α))
    → (α ⊕ β) ＝ (β ⊕ α)
  I α β IH₁ IH₂ =
   α ⊕ β                                                ＝⟨ II  ⟩
   sup⁺ (cases (λ a → (α ↓ a) ⊕ β) (λ b → α ⊕ (β ↓ b))) ＝⟨ III ⟩
   sup⁺ (cases (λ a → β ⊕ (α ↓ a)) (λ b → (β ↓ b) ⊕ α)) ＝⟨ IV  ⟩
   sup⁺ (cases (λ b → (β ↓ b) ⊕ α) (λ a → β ⊕ (α ↓ a))) ＝⟨ V   ⟩
   β ⊕ α                                                ∎
    where
     f = cases (λ a → β ⊕ (α ↓ a)) (λ b → (β ↓ b) ⊕ α)
     g = cases (λ b → (β ↓ b) ⊕ α) (λ a → β ⊕ (α ↓ a))

     II  = ⊕-behaviour α β
     III = ap₂ (λ x y → sup⁺ (cases x y)) (dfunext fe' IH₁) (dfunext fe' IH₂)
     IV  = ⊴-antisym (sup⁺ f) (sup⁺ g)
            (sup⁺-is-least-strict-upper-bound f (sup⁺ g)
              (dep-cases (λ a → sup⁺-is-strict-upper-bound (inr a))
                         (λ b → sup⁺-is-strict-upper-bound (inl b))))
            (sup⁺-is-least-strict-upper-bound g (sup⁺ f)
              (dep-cases (λ b → sup⁺-is-strict-upper-bound (inr b))
                         (λ a → sup⁺-is-strict-upper-bound (inl a))))
     V   = (⊕-behaviour β α) ⁻¹

\end{code}

The following strict order preservation properties hold essentially by
definition of Hessenberg addition.

\begin{code}

⊕-⊲-left : (α β : Ordinal 𝓤) {a : ⟨ α ⟩} → (α ↓ a) ⊕ β ⊲ α ⊕ β
⊕-⊲-left α β {a} = transport⁻¹ ((α ↓ a) ⊕ β ⊲_) (⊕-behaviour α β)
                    (sup⁺-is-strict-upper-bound (inl a))

⊕-⊲-right : (α β : Ordinal 𝓤) {b : ⟨ β ⟩} → α ⊕ (β ↓ b) ⊲ α ⊕ β
⊕-⊲-right α β {b} = transport⁻¹ (α ⊕ (β ↓ b) ⊲_) (⊕-behaviour α β)
                     (sup⁺-is-strict-upper-bound (inr b))

⊕-⊲-mixed : (α β : Ordinal 𝓤) {a : ⟨ α ⟩} {b : ⟨ β ⟩}
          → (α ↓ a) ⊕ (β ↓ b) ⊲ α ⊕ β
⊕-⊲-mixed α β {a} {b} =
 ⊲-is-transitive
  ((α ↓ a) ⊕ (β ↓ b))
  ((α ↓ a) ⊕ β)
  (α ⊕ β)
  (⊕-⊲-right (α ↓ a) β)
  (⊕-⊲-left α β)

⊕-is-order-preserving-left : (α β γ : Ordinal 𝓤) → α ⊲ β → α ⊕ γ ⊲ β ⊕ γ
⊕-is-order-preserving-left α β γ (b , refl) = ⊕-⊲-left β γ

⊕-is-order-preserving-right : (α β γ : Ordinal 𝓤) → β ⊲ γ → α ⊕ β ⊲ α ⊕ γ
⊕-is-order-preserving-right α β γ (c , refl) = ⊕-⊲-right α γ

⊕-is-order-preserving : (α α' β β' : Ordinal 𝓤)
                      → α ⊲ α'
                      → β ⊲ β'
                      → α ⊕ β ⊲ α' ⊕ β'
⊕-is-order-preserving α α' β β' (a' , refl) (b' , refl) = ⊕-⊲-mixed α' β'

\end{code}

Note that ⊕-⊴-left/right/mixed tell us that each of (α ↓ a) ⊕ β, α ⊕ (β ↓ b) and
(α ↓ a) ⊕ (β ↓ b) determine initial segments of α ⊕ β. The following lemma says
that these are *all* initial segments of α ⊕ β.

The truncation is not redundant in the sense that the cases can overlap (for
instance, we can take β := α and we have (α ↓ a) ⊕ α ＝ α ⊕ (α ↓ a) thanks to
commutativity).

\begin{code}

⊕-↓-characterization
 : (α β : Ordinal 𝓤) (x : ⟨ α ⊕ β ⟩)
 → ∥ (Σ a ꞉ ⟨ α ⟩ , (α ⊕ β) ↓ x ＝ (α ↓ a) ⊕ β) +
     (Σ b ꞉ ⟨ β ⟩ , (α ⊕ β) ↓ x ＝ α ⊕ (β ↓ b)) +
     (Σ a ꞉ ⟨ α ⟩ , Σ b ꞉ ⟨ β ⟩ , (α ⊕ β) ↓ x ＝ (α ↓ a) ⊕ (β ↓ b)) ∥
⊕-↓-characterization {𝓤} = double-transfinite-induction-on-OO _ I
 where
  P : (α β γ : Ordinal 𝓤) → 𝓤 ⁺ ̇
  P α β γ =
   (x : ⟨ γ ⟩) → ∥ (Σ a ꞉ ⟨ α ⟩ , γ ↓ x ＝ (α ↓ a) ⊕ β) +
                   (Σ b ꞉ ⟨ β ⟩ , γ ↓ x ＝ α ⊕ (β ↓ b)) +
                   (Σ a ꞉ ⟨ α ⟩ , Σ b ꞉ ⟨ β ⟩ , γ ↓ x ＝ (α ↓ a) ⊕ (β ↓ b)) ∥

  I : (α β : Ordinal 𝓤)
    → ((a : ⟨ α ⟩) → P (α ↓ a) β ((α ↓ a) ⊕ β))
    → ((b : ⟨ β ⟩) → P α (β ↓ b) (α ⊕ (β ↓ b)))
    → P α β (α ⊕ β)
  I α β IH₁ IH₂ = transport⁻¹ (P α β) (⊕-behaviour α β) II
   where
    r₁ : ⟨ α ⟩ → Ordinal 𝓤
    r₁ a = (α ↓ a) ⊕ β
    r₂ : ⟨ β ⟩ → Ordinal 𝓤
    r₂ b = α ⊕ (β ↓ b)
    σ = sup⁺ (cases r₁ r₂)

    II : P α β σ
    II s = ∥∥-rec ∨-is-prop III
             (initial-segment-of-sup-is-initial-segment-of-some-component _ s)
     where
      Tᵃ  = Σ a ꞉ ⟨ α ⟩ , σ ↓ s ＝ (α ↓ a) ⊕ β
      Tᵇ  = Σ b ꞉ ⟨ β ⟩ , σ ↓ s ＝ α ⊕ (β ↓ b)
      Tᵃᵇ = Σ a ꞉ ⟨ α ⟩ , Σ b ꞉ ⟨ β ⟩ , σ ↓ s ＝ (α ↓ a) ⊕ (β ↓ b)

      III : (Σ y ꞉ ⟨ α ⟩ + ⟨ β ⟩ , Σ x ꞉ ⟨ cases r₁ r₂ y +ₒ 𝟙ₒ ⟩ ,
              σ ↓ s ＝ cases r₁ r₂ y +ₒ 𝟙ₒ ↓ x)
          → ∥ Tᵃ + Tᵇ + Tᵃᵇ ∥

      III (inl a , inl x , e) = ∥∥-functor (+functor III₁ III₂) (IH₁ a x)
       where
        p = σ ↓ s                         ＝⟨ e ⟩
            (((α ↓ a) ⊕ β) +ₒ 𝟙ₒ) ↓ inl x ＝⟨ (+ₒ-↓-left x) ⁻¹ ⟩
            ((α ↓ a) ⊕ β) ↓ x             ∎

        III₁ : (Σ a' ꞉ ⟨ α ↓ a ⟩ , ((α ↓ a) ⊕ β) ↓ x ＝ ((α ↓ a ↓ a') ⊕ β)) → Tᵃ
        III₁ ((a' , l) , e') = a' ,
         (σ ↓ s                         ＝⟨ p ⟩
          ((α ↓ a) ⊕ β) ↓ x             ＝⟨ e' ⟩
          ((α ↓ a ↓ (a' , l)) ⊕ β)      ＝⟨ ap (_⊕ β) (iterated-↓ α a a' l) ⟩
          ((α ↓ a') ⊕ β)                ∎)

        III₂ : ((Σ b ꞉ ⟨ β ⟩ , ((α ↓ a) ⊕ β) ↓ x ＝ ((α ↓ a) ⊕ (β ↓ b))) +
                (Σ a' ꞉ ⟨ α ↓ a ⟩ , Σ b ꞉ ⟨ β ⟩
                  , ((α ↓ a) ⊕ β) ↓ x ＝ ((α ↓ a ↓ a') ⊕ (β ↓ b))))
             → Tᵇ + Tᵃᵇ
        III₂ (inl (b , e')) = inr (a , b , (σ ↓ s             ＝⟨ p ⟩
                                            ((α ↓ a) ⊕ β) ↓ x ＝⟨ e' ⟩
                                            (α ↓ a) ⊕ (β ↓ b) ∎))

        III₂ (inr ((a' , l) , b , e')) = inr (a' , b ,
         (σ ↓ s                          ＝⟨ p ⟩
          ((α ↓ a) ⊕ β) ↓ x              ＝⟨ e' ⟩
          ((α ↓ a ↓ (a' , l)) ⊕ (β ↓ b)) ＝⟨ ap (_⊕ (β ↓ b))
                                                (iterated-↓ α a a' l) ⟩
          ((α ↓ a') ⊕ (β ↓ b))           ∎))

      III (inl a , inr u , e) = ∣ inl (a , e') ∣
       where
        e' = σ ↓ s                         ＝⟨ e ⟩
             (((α ↓ a) ⊕ β) +ₒ 𝟙ₒ) ↓ inr u ＝⟨ (+ₒ-↓-right u) ⁻¹ ⟩
             ((α ↓ a) ⊕ β) +ₒ (𝟙ₒ ↓ u)     ＝⟨ ap (((α ↓ a) ⊕ β) +ₒ_) 𝟙ₒ-↓ ⟩
             ((α ↓ a) ⊕ β) +ₒ 𝟘ₒ           ＝⟨ 𝟘ₒ-right-neutral ((α ↓ a) ⊕ β) ⟩
             (α ↓ a) ⊕ β                   ∎

\end{code}

The following is symmetric to the above.

\begin{code}

      III (inr b , inl x , e) = ∥∥-functor III' (IH₂ b x)
       where
        p = σ ↓ s                         ＝⟨ e ⟩
            ((α ⊕ (β ↓ b)) +ₒ 𝟙ₒ) ↓ inl x ＝⟨ (+ₒ-↓-left x) ⁻¹ ⟩
            (α ⊕ (β ↓ b)) ↓ x             ∎

        III' : ((Σ a ꞉ ⟨ α ⟩ , (α ⊕ (β ↓ b)) ↓ x ＝ (α ↓ a) ⊕ (β ↓ b)) +
                (Σ b' ꞉ ⟨ β ↓ b ⟩ , (α ⊕ (β ↓ b)) ↓ x ＝ α ⊕ (β ↓ b ↓ b')) +
                (Σ a ꞉ ⟨ α ⟩ , Σ b' ꞉ ⟨ β ↓ b ⟩ ,
                  (α ⊕ (β ↓ b)) ↓ x ＝ (α ↓ a) ⊕ (β ↓ b ↓ b')))
             → Tᵃ + Tᵇ + Tᵃᵇ

        III' (inl (a , e')) = inr (inr (a , b ,
         (σ ↓ s                         ＝⟨ p ⟩
          (α ⊕ (β ↓ b)) ↓ x             ＝⟨ e' ⟩
          ((α ↓ a) ⊕ (β ↓ b))           ∎)))

        III' (inr (inl ((b' , l) , e'))) = inr (inl (b' ,
         (σ ↓ s                         ＝⟨ p ⟩
          (α ⊕ (β ↓ b)) ↓ x             ＝⟨ e' ⟩
          (α ⊕ (β ↓ b ↓ (b' , l)))      ＝⟨ ap (α ⊕_) (iterated-↓ β b b' l) ⟩
          (α ⊕ (β ↓ b'))                ∎)))

        III' (inr (inr (a , (b' , l) , e'))) = inr (inr (a , b' ,
         (σ ↓ s                          ＝⟨ p ⟩
          (α ⊕ (β ↓ b)) ↓ x              ＝⟨ e' ⟩
          ((α ↓ a) ⊕ (β ↓ b ↓ (b' , l))) ＝⟨ ap ((α ↓ a) ⊕_)
                                                (iterated-↓ β b b' l) ⟩
          ((α ↓ a) ⊕ (β ↓ b'))           ∎)))

      III (inr b , inr u , e) = ∣ inr (inl (b , e')) ∣
       where
        e' = σ ↓ s                         ＝⟨ e ⟩
             ((α ⊕ (β ↓ b)) +ₒ 𝟙ₒ) ↓ inr u ＝⟨ (+ₒ-↓-right u) ⁻¹ ⟩
             (α ⊕ (β ↓ b)) +ₒ (𝟙ₒ ↓ u)     ＝⟨ ap ((α ⊕ (β ↓ b)) +ₒ_) 𝟙ₒ-↓ ⟩
             (α ⊕ (β ↓ b)) +ₒ 𝟘ₒ           ＝⟨ 𝟘ₒ-right-neutral (α ⊕ (β ↓ b)) ⟩
             (α ⊕ (β ↓ b))                 ∎

\end{code}

The characterization of initial segments leads to a convenient "induction"
principle for (initial segments determined by) elements of α ⊕ β.

\begin{code}

⊕-induction : (α β : Ordinal 𝓤) (P : Ordinal 𝓤 → 𝓥 ̇ )
            → ((γ : Ordinal 𝓤) → is-prop (P γ))
            → ((a : ⟨ α ⟩) → P ((α ↓ a) ⊕ β))
            → ((b : ⟨ β ⟩) → P (α ⊕ (β ↓ b)))
            → ((a : ⟨ α ⟩) (b : ⟨ β ⟩) → P ((α ↓ a) ⊕ (β ↓ b)))
            → (x : ⟨ α ⊕ β ⟩) → P ((α ⊕ β) ↓ x)
⊕-induction α β P P-pv f g h x =
 ∥∥-rec (P-pv ((α ⊕ β) ↓ x)) I (⊕-↓-characterization α β x)
  where
   I : ((Σ a ꞉ ⟨ α ⟩ , (α ⊕ β) ↓ x ＝ (α ↓ a) ⊕ β) +
        (Σ b ꞉ ⟨ β ⟩ , (α ⊕ β) ↓ x ＝ α ⊕ (β ↓ b)) +
        (Σ a ꞉ ⟨ α ⟩ , Σ b ꞉ ⟨ β ⟩ , (α ⊕ β) ↓ x ＝ (α ↓ a) ⊕ (β ↓ b)))
     → P ((α ⊕ β) ↓ x)
   I (inl (a , e))           = transport⁻¹ P e (f a)
   I (inr (inl (b , e)))     = transport⁻¹ P e (g b)
   I (inr (inr (a , b , e))) = transport⁻¹ P e (h a b)

\end{code}

With ⊕-induction we are ready to give a proof that ⊕ is associative.
To avoid symmetric cases, we tried to first prove the one-sided version
  (α ⊕ β) ⊕ γ ⊴ α ⊕ (β ⊕ γ),
which, together with commutativity, would be enough to derive the equality.
The problem with that approach is that the induction hypothesis is too weak. So
we prove the equality directly and accept handling some symmetric cases.

\begin{code}

⊕-is-associative : (α β γ : Ordinal 𝓤)
                 → (α ⊕ β) ⊕ γ ＝ α ⊕ (β ⊕ γ)
⊕-is-associative {𝓤} = λ α β γ → Transfinite-induction (OO³) _ I (α , β , γ)
 where
  OO³ = OO 𝓤 ×ₒ (OO 𝓤 ×ₒ OO 𝓤)

  I : (s@(α , β , γ) : ⟨ OO³ ⟩)
    → ((t@(γ , δ , ε) : ⟨ OO³ ⟩)
                      → t ≺⟨ OO³ ⟩ s
                      → (γ ⊕ δ) ⊕ ε ＝ γ ⊕ (δ ⊕ ε))
    → (α ⊕ β) ⊕ γ ＝ α ⊕ (β ⊕ γ)
  I (α , β , γ) IH = ⊴-antisym ((α ⊕ β) ⊕ γ) (α ⊕ (β ⊕ γ))
                               (to-⊴ ((α ⊕ β) ⊕ γ) (α ⊕ (β ⊕ γ)) II)
                               (to-⊴ (α ⊕ (β ⊕ γ)) ((α ⊕ β) ⊕ γ) II')
   where
    II' : (y : ⟨ α ⊕ (β ⊕ γ) ⟩) → (α ⊕ (β ⊕ γ)) ↓ y ⊲ (α ⊕ β) ⊕ γ
    II' = ⊕-induction α (β ⊕ γ) (_⊲ (α ⊕ β) ⊕ γ) (λ _ → ⊲-is-prop-valued _ _)
           IIᵃ
           (III α (inr refl))
           (λ a x → III (α ↓ a) (inl (a , refl)) x)
     where
      IIᵃ : (a : ⟨ α ⟩) → (α ↓ a) ⊕ (β ⊕ γ) ⊲ (α ⊕ β) ⊕ γ
      IIᵃ a = transport (_⊲ (α ⊕ β) ⊕ γ)
               (IH (α ↓ a , β , γ) (inr (refl , (a , refl))))
               (⊕-is-order-preserving-left ((α ↓ a) ⊕ β) (α ⊕ β) γ
                 (⊕-⊲-left α β))

\end{code}

The following captures some of the common ingredients between the cases of II'.

\begin{code}

      III : (δ : Ordinal 𝓤) → ((δ ⊲ α) + (δ ＝ α))
          → (x : ⟨ β ⊕ γ ⟩) → δ ⊕ ((β ⊕ γ) ↓ x) ⊲ (α ⊕ β) ⊕ γ
      III δ s = ⊕-induction β γ (λ - → δ ⊕ - ⊲ (α ⊕ β) ⊕ γ)
                 (λ _ → ⊲-is-prop-valued _ _)
                 IIIᵇ IIIᶜ IIIᵇᶜ
       where
        l : (b : ⟨ β ⟩) → δ ⊕ (β ↓ b) ⊲ α ⊕ β
        l b = h s
         where
          h : ((δ ⊲ α) + (δ ＝ α)) → δ ⊕ (β ↓ b) ⊲ α ⊕ β
          h (inl k) = ⊕-is-order-preserving δ α (β ↓ b) β k (b , refl)
          h (inr refl) = ⊕-⊲-right α β

        IIIᵇ : (b : ⟨ β ⟩) → δ ⊕ ((β ↓ b) ⊕ γ) ⊲ (α ⊕ β) ⊕ γ
        IIIᵇ b = transport (_⊲ (α ⊕ β) ⊕ γ)
                  (IH (δ , β ↓ b , γ) (inl (inr (refl , (b , refl)))))
                  (⊕-is-order-preserving-left _ _ _ (l b))

        IIIᶜ : (c : ⟨ γ ⟩) → δ ⊕ (β ⊕ (γ ↓ c)) ⊲ (α ⊕ β) ⊕ γ
        IIIᶜ c = transport (_⊲ (α ⊕ β) ⊕ γ)
                  (IH (δ , β , γ ↓ c) (inl (inl (c , refl))))
                  (h s)
         where
         h : ((δ ⊲ α) + (δ ＝ α)) → (δ ⊕ β) ⊕ (γ ↓ c) ⊲ (α ⊕ β) ⊕ γ
         h (inl k) = ⊕-is-order-preserving (δ ⊕ β) (α ⊕ β) (γ ↓ c) γ
                      (⊕-is-order-preserving-left δ α β k)
                      (c , refl)
         h (inr refl) = ⊕-⊲-right (α ⊕ β) γ

        IIIᵇᶜ : (b : ⟨ β ⟩) (c : ⟨ γ ⟩) → δ ⊕ ((β ↓ b) ⊕ (γ ↓ c)) ⊲ (α ⊕ β) ⊕ γ
        IIIᵇᶜ b c = transport (_⊲ (α ⊕ β) ⊕ γ)
                     (IH (δ , β ↓ b , γ ↓ c) (inl (inl (c , refl))))
                     (⊕-is-order-preserving _ _ _ _ (l b) (c , refl))

\end{code}

The following is mostly symmetric to the above.

\begin{code}

    II : (y : ⟨ (α ⊕ β) ⊕ γ ⟩) → ((α ⊕ β) ⊕ γ) ↓ y ⊲ α ⊕ (β ⊕ γ)
    II = ⊕-induction (α ⊕ β) γ (_⊲ α ⊕ (β ⊕ γ)) (λ _ → ⊲-is-prop-valued _ _)
          (III γ (inr refl))
          III₂
          (λ x c → III (γ ↓ c) (inl (c , refl)) x)
     where
      III₂ : (c : ⟨ γ ⟩) → (α ⊕ β) ⊕ (γ ↓ c) ⊲ α ⊕ (β ⊕ γ)
      III₂ c = transport⁻¹ (_⊲ α ⊕ (β ⊕ γ))
                (IH (α , β , γ ↓ c) (inl (inl (c , refl))))
                (⊕-is-order-preserving-right α (β ⊕ (γ ↓ c)) (β ⊕ γ)
                  (⊕-⊲-right β γ))

      III : (δ : Ordinal 𝓤) → ((δ ⊲ γ) + (δ ＝ γ))
          → (x : ⟨ α ⊕ β ⟩) → ((α ⊕ β) ↓ x) ⊕ δ ⊲ α ⊕ (β ⊕ γ)
      III δ s = ⊕-induction α β (λ - → - ⊕ δ ⊲ α ⊕ (β ⊕ γ))
                 (λ _ → ⊲-is-prop-valued _ _)
                 IIIᵃ IIIᵇ IIIᵃᵇ
       where
        l : (b : ⟨ β ⟩) → (β ↓ b) ⊕ δ ⊲ β ⊕ γ
        l b = h s
         where
          h : ((δ ⊲ γ) + (δ ＝ γ)) → (β ↓ b) ⊕ δ ⊲ β ⊕ γ
          h (inl k)    = ⊕-is-order-preserving (β ↓ b) β δ γ (b , refl) k
          h (inr refl) = ⊕-⊲-left β γ

        IH-applicable : (b : ⟨ β ⟩) (α' : Ordinal 𝓤)
                      → (α' , β ↓ b , δ) ≺⟨ OO³ ⟩ (α , β , γ)
        IH-applicable b α' = h s
         where
          h : ((δ ⊲ γ) + (δ ＝ γ)) → (α' , β ↓ b , δ) ≺⟨ OO³ ⟩ (α , β , γ)
          h (inl k) = inl (inl k)
          h (inr refl) = inl (inr (refl , (b , refl)))

        IIIᵃ : (a : ⟨ α ⟩) → ((α ↓ a) ⊕ β) ⊕ δ ⊲ α ⊕ (β ⊕ γ)
        IIIᵃ a = transport⁻¹ (_⊲ α ⊕ (β ⊕ γ))
                  (IH (α ↓ a , β , δ) (pr₁ (h s)))
                  (pr₂ (h s))
         where
          h : ((δ ⊲ γ) + (δ ＝ γ))
            → (α ↓ a , β , δ) ≺⟨ OO³ ⟩ (α , β , γ)
            × (α ↓ a) ⊕ (β ⊕ δ) ⊲ α ⊕ (β ⊕ γ)
          h (inl k) = inl (inl k) ,
                      ⊕-is-order-preserving (α ↓ a) α (β ⊕ δ) (β ⊕ γ)
                       (a , refl)
                       (⊕-is-order-preserving-right β δ γ k)
          h (inr refl) = inr (refl , (a , refl)) , ⊕-⊲-left α (β ⊕ γ)

        IIIᵇ : (b : ⟨ β ⟩) → (α ⊕ (β ↓ b)) ⊕ δ ⊲ α ⊕ (β ⊕ γ)
        IIIᵇ b = transport⁻¹ (_⊲ (α ⊕ (β ⊕ γ)))
                  (IH (α , (β ↓ b) , δ) (IH-applicable b α))
                  (⊕-is-order-preserving-right _ _ _ (l b))

        IIIᵃᵇ : (a : ⟨ α ⟩) (b : ⟨ β ⟩) → ((α ↓ a) ⊕ (β ↓ b)) ⊕ δ ⊲ α ⊕ (β ⊕ γ)
        IIIᵃᵇ a b = transport⁻¹ (_⊲ (α ⊕ (β ⊕ γ)))
                     (IH (α ↓ a , β ↓ b , δ) (IH-applicable b (α ↓ a)))
                     (⊕-is-order-preserving _ _ _ _ (a , refl) (l b))

\end{code}

With the main properties, commutativity and associativity, proved, we turn to
𝟘ₒ being neutral for ⊕ and ⊕ being strictly inflationary.

\begin{code}

𝟘ₒ-is-right-neutral-⊕ : (α : Ordinal 𝓤) → α ⊕ 𝟘ₒ ＝ α
𝟘ₒ-is-right-neutral-⊕ {𝓤} = transfinite-induction-on-OO _ I
 where
  I : (α : Ordinal 𝓤) → ((a : ⟨ α ⟩) → (α ↓ a) ⊕ 𝟘ₒ ＝ α ↓ a) → α ⊕ 𝟘ₒ ＝ α
  I α IH = ⊴-antisym (α ⊕ 𝟘ₒ) α (to-⊴ (α ⊕ 𝟘ₒ) α II) (to-⊴ α (α ⊕ 𝟘ₒ) III)
   where
    II : (x : ⟨ α ⊕ 𝟘ₒ ⟩) → (α ⊕ 𝟘ₒ) ↓ x ⊲ α
    II = ⊕-induction α 𝟘ₒ (_⊲ α) (λ _ → ⊲-is-prop-valued _ α)
          (λ a → (a , IH a))
          𝟘-induction
          (λ a → 𝟘-induction)

    III : (a : ⟨ α ⟩) → α ↓ a ⊲ α ⊕ 𝟘ₒ
    III a = transport (_⊲ α ⊕ 𝟘ₒ) (IH a) (⊕-⊲-left α 𝟘ₒ)

𝟘ₒ-is-left-neutral-⊕ : (α : Ordinal 𝓤) → 𝟘ₒ ⊕ α ＝ α
𝟘ₒ-is-left-neutral-⊕ α = 𝟘ₒ ⊕ α  ＝⟨ ⊕-is-commutative 𝟘ₒ α ⟩
                         α  ⊕ 𝟘ₒ ＝⟨ 𝟘ₒ-is-right-neutral-⊕ α ⟩
                         α       ∎

⊕-is-strictly-inflationary : (α β : Ordinal 𝓤) → 𝟙ₒ ⊴ β → α ⊲ α ⊕ β
⊕-is-strictly-inflationary α β 𝕗@(f , f-sim) = transport⁻¹ (_⊲ α ⊕ β) I II
 where
  b : ⟨ β ⟩
  b = f ⋆

  e = β ↓ b  ＝⟨ (simulations-preserve-↓ 𝟙ₒ β 𝕗 ⋆) ⁻¹ ⟩
      𝟙ₒ ↓ ⋆ ＝⟨ 𝟙ₒ-↓ ⟩
      𝟘ₒ     ∎

  I : α ＝ α ⊕ (β ↓ b)
  I = α           ＝⟨ (𝟘ₒ-is-right-neutral-⊕ α) ⁻¹ ⟩
      α ⊕ 𝟘ₒ      ＝⟨ ap (α ⊕_) (e ⁻¹) ⟩
      α ⊕ (β ↓ b) ∎

  II : α ⊕ (β ↓ b) ⊲ α ⊕ β
  II = ⊕-⊲-right α β

⊕𝟙ₒ-is-strictly-inflationary : (α : Ordinal 𝓤) → α ⊲ α ⊕ 𝟙ₒ
⊕𝟙ₒ-is-strictly-inflationary α = ⊕-is-strictly-inflationary α 𝟙ₒ (⊴-refl 𝟙ₒ)

\end{code}

As a final positive result, we show that Hessenberg addition reflects the
(strict) order and is left cancellable (i.e. injective). These properties are
proved *simultaneously* by induction. We include a symmetric version of order
reflection in the statement to ensure a strong enough induction hypothesis.

\begin{code}

private
 ⊕-lc-and-order-reflecting
  : (δ α β : Ordinal 𝓤) → (δ ⊕ α ＝ δ ⊕ β → α ＝ β)
                        × (δ ⊕ α ⊲ δ ⊕ β → α ⊲ β)
                        × (δ ⊕ β ⊲ δ ⊕ α → β ⊲ α)
 ⊕-lc-and-order-reflecting {𝓤} =
  λ δ α β → Transfinite-induction OO³ _ I (δ , α , β)
   where
    OO³ = OO 𝓤 ×ₒ (OO 𝓤 ×ₒ OO 𝓤)
    I : (s@(δ , α , β) : ⟨ OO³ ⟩)
      → ((t@(δ' , α' , β') : ⟨ OO³ ⟩)
                           → t ≺⟨ OO³ ⟩ s
                           → (δ' ⊕ α' ＝ δ' ⊕ β' → α' ＝ β')
                           × (δ' ⊕ α' ⊲ δ' ⊕ β' → α' ⊲ β')
                           × (δ' ⊕ β' ⊲ δ' ⊕ α' → β' ⊲ α'))
      → (δ ⊕ α ＝ δ ⊕ β → α ＝ β)
      × (δ ⊕ α ⊲ δ ⊕ β → α ⊲ β)
      × (δ ⊕ β ⊲ δ ⊕ α → β ⊲ α)
    I (δ , α , β) IH = I₁ , I₂ , I₃
     where
      I₁ : δ ⊕ α ＝ δ ⊕ β → α ＝ β
      I₁ e = ⊴-antisym α β (to-⊴ α β II) (to-⊴ β α II')
       where
        II : (a : ⟨ α ⟩) → α ↓ a ⊲ β
        II a = ih (transport (δ ⊕ (α ↓ a) ⊲_) e (⊕-⊲-right δ α))
         where
          ih : δ ⊕ (α ↓ a) ⊲ δ ⊕ β → α ↓ a ⊲ β
          ih = pr₁ (pr₂ (IH (δ , α ↓ a , β) (inl (inr (refl , (a , refl))))))

\end{code}

At this point we need the symmetric order preservation provided by the induction
hypothesis.

\begin{code}

        II' : (b : ⟨ β ⟩) → β ↓ b ⊲ α
        II' b = ih (transport⁻¹ (δ ⊕ (β ↓ b) ⊲_) e (⊕-⊲-right δ β))
         where
          ih : δ ⊕ (β ↓ b) ⊲ δ ⊕ α → β ↓ b ⊲ α
          ih = pr₂ (pr₂ (IH (δ , α , β ↓ b) (inl (inl (b , refl)))))

      I₂ : δ ⊕ α ⊲ δ ⊕ β → α ⊲ β
      I₂ = uncurry II
       where
        II : (x : ⟨ δ ⊕ β ⟩) → δ ⊕ α ＝ (δ ⊕ β) ↓ x → α ⊲ β
        II = ⊕-induction δ β (λ - → δ ⊕ α ＝ - → α ⊲ β)
              (λ _ → Π-is-prop fe' (λ _ → ⊲-is-prop-valued α β))
              III
              IV
              V
         where
          III : (d : ⟨ δ ⟩) → δ ⊕ α ＝ (δ ↓ d) ⊕ β → α ⊲ β
          III d e = pr₁ (pr₂ (IH (δ ↓ d , α , β) (inr (refl , (d , refl))))) l
           where
            l : (δ ↓ d) ⊕ α ⊲ (δ ↓ d) ⊕ β
            l = transport ((δ ↓ d) ⊕ α ⊲_) e (⊕-⊲-left δ α)

          IV : (b : ⟨ β ⟩) → δ ⊕ α ＝ δ ⊕ (β ↓ b) → α ⊲ β
          IV b e = b , e'
           where
            e' : α ＝ β ↓ b
            e' = pr₁ (IH (δ , α , β ↓ b) (inl (inl (b , refl)))) e

          V : (d : ⟨ δ ⟩) (b : ⟨ β ⟩) → δ ⊕ α ＝ (δ ↓ d) ⊕ (β ↓ b) → α ⊲ β
          V d b e = ⊲-is-transitive α (β ↓ b) β l (b , refl)
           where
            l : α ⊲ β ↓ b
            l = pr₁ (pr₂ (IH (δ ↓ d , α , β ↓ b) (inl (inl (b , refl))))) l'
             where
              l' : (δ ↓ d) ⊕ α ⊲ (δ ↓ d) ⊕ (β ↓ b)
              l' = transport ((δ ↓ d) ⊕ α ⊲_) e (⊕-⊲-left δ α)

\end{code}

The rest of the proof is symmetric to the above.

\begin{code}

      I₃ : δ ⊕ β ⊲ δ ⊕ α → β ⊲ α
      I₃ = uncurry II
       where
        II : (x : ⟨ δ ⊕ α ⟩) → δ ⊕ β ＝ (δ ⊕ α) ↓ x → β ⊲ α
        II = ⊕-induction δ α (λ - → δ ⊕ β ＝ - → β ⊲ α)
              (λ _ → Π-is-prop fe' (λ _ → ⊲-is-prop-valued β α))
              III
              IV
              V
         where
          III : (d : ⟨ δ ⟩) → δ ⊕ β ＝ (δ ↓ d) ⊕ α → β ⊲ α
          III d e = pr₂ (pr₂ (IH (δ ↓ d , α , β) (inr (refl , (d , refl))))) l
           where
            l : (δ ↓ d) ⊕ β ⊲ (δ ↓ d) ⊕ α
            l = transport ((δ ↓ d) ⊕ β ⊲_) e (⊕-⊲-left δ β)

          IV : (a : ⟨ α ⟩) → δ ⊕ β ＝ δ ⊕ (α ↓ a) → β ⊲ α
          IV a e = a , (e' ⁻¹)
           where
            e' : α ↓ a ＝ β
            e' = pr₁ (IH (δ , α ↓ a , β) (inl (inr (refl , (a , refl))))) (e ⁻¹)

          V : (d : ⟨ δ ⟩) (a : ⟨ α ⟩) → δ ⊕ β ＝ (δ ↓ d) ⊕ (α ↓ a) → β ⊲ α
          V d a e = ⊲-is-transitive β (α ↓ a) α l (a , refl)
           where
            l : β ⊲ α ↓ a
            l = pr₂ (pr₂ (IH (δ ↓ d , α ↓ a , β)
                             (inl (inr (refl , (a , refl))))))
                    l'
             where
              l' : ((δ ↓ d) ⊕ β) ⊲ ((δ ↓ d) ⊕ (α ↓ a))
              l' = transport ((δ ↓ d) ⊕ β ⊲_) e (⊕-⊲-left δ β)

⊕-is-left-cancellable : (δ α β : Ordinal 𝓤) → δ ⊕ α ＝ δ ⊕ β → α ＝ β
⊕-is-left-cancellable δ α β = pr₁ (⊕-lc-and-order-reflecting δ α β)

⊕-is-order-reflecting : (δ α β : Ordinal 𝓤) → δ ⊕ α ⊲ δ ⊕ β → α ⊲ β
⊕-is-order-reflecting δ α β = pr₁ (pr₂ (⊕-lc-and-order-reflecting δ α β))

\end{code}

Lastly, we prove that some claims about Hessenberg addition are inherently classical.

\begin{code}

⊕-+ₒ-equal-successors-gives-EM : ((α : Ordinal 𝓤) → α ⊕ 𝟙ₒ ＝ α +ₒ 𝟙ₒ) → EM 𝓤
⊕-+ₒ-equal-successors-gives-EM {𝓤} h =
 successor-is-order-preserving-gives-EM I
  where
   I : (α β : Ordinal 𝓤) → α ⊲ β → α +ₒ 𝟙ₒ ⊲ β +ₒ 𝟙ₒ
   I α β l = transport₂ _⊲_ (h α) (h β)
              (⊕-is-order-preserving-left α β 𝟙ₒ l)

⊕-commutes-with-successor-gives-EM
 : ((α β : Ordinal 𝓤) → α ⊕ (β +ₒ 𝟙ₒ) ＝ (α ⊕ β) +ₒ 𝟙ₒ)
 → EM 𝓤
⊕-commutes-with-successor-gives-EM {𝓤} h = ⊕-+ₒ-equal-successors-gives-EM I
 where
  I : (α : Ordinal 𝓤) → α ⊕ 𝟙ₒ ＝ α +ₒ 𝟙ₒ
  I α = α ⊕ 𝟙ₒ         ＝⟨ ap (α ⊕_) ((𝟘ₒ-left-neutral 𝟙ₒ) ⁻¹) ⟩
        α ⊕ (𝟘ₒ +ₒ 𝟙ₒ) ＝⟨ h α 𝟘ₒ ⟩
        (α ⊕ 𝟘ₒ) +ₒ 𝟙ₒ ＝⟨ ap (_+ₒ 𝟙ₒ) (𝟘ₒ-is-right-neutral-⊕ α) ⟩
        α +ₒ 𝟙ₒ        ∎

\end{code}

While ∀ α . α ⊕ 𝟙ₒ ＝ α +ₒ 𝟙ₒ implies EM, we do have this equality,
constructively, whenever α is a proposition.
This is used to reduce claims about Hessenberg addition to claims about ordinary
ordinal addition and thereby to excluded middle.

\begin{code}

⊕-prop-𝟙ₒ-is-+ₒ : (P : 𝓤 ̇ ) (i : is-prop P)
                → let Pₒ = prop-ordinal P i in
                  Pₒ ⊕ 𝟙ₒ ＝ Pₒ +ₒ 𝟙ₒ
⊕-prop-𝟙ₒ-is-+ₒ {𝓤} P i =
 Pₒ ⊕ 𝟙ₒ  ＝⟨ ⊕-behaviour Pₒ 𝟙ₒ ⟩
 sup f    ＝⟨ sup-pointwise-equal f g H ⟩
 sup g    ＝⟨ I ⟩
 Pₒ +ₒ 𝟙ₒ ∎
  where
   Pₒ : Ordinal 𝓤
   Pₒ = prop-ordinal P i

   f g : P + 𝟙 → Ordinal 𝓤
   f b = (cases (λ p → (Pₒ ↓ p) ⊕ 𝟙ₒ) (λ u → Pₒ ⊕ (𝟙ₒ ↓ u)) b) +ₒ 𝟙ₒ
   g b = cases (λ p → 𝟙ₒ) (λ u → Pₒ) b +ₒ 𝟙ₒ

   H : f ∼ g
   H (inl p) = ((Pₒ ↓ p) ⊕ 𝟙ₒ) +ₒ 𝟙ₒ ＝⟨ I ⟩
               (𝟘ₒ ⊕ 𝟙ₒ) +ₒ 𝟙ₒ       ＝⟨ II ⟩
               𝟙ₒ +ₒ 𝟙ₒ              ∎
    where
     I  = ap (λ - → (- ⊕ 𝟙ₒ) +ₒ 𝟙ₒ) (prop-ordinal-↓ i p)
     II = ap (_+ₒ 𝟙ₒ) (𝟘ₒ-is-left-neutral-⊕ 𝟙ₒ)
   H (inr u) = (Pₒ ⊕ (𝟙ₒ ↓ u)) +ₒ 𝟙ₒ ＝⟨ I ⟩
               (Pₒ ⊕ 𝟘ₒ) +ₒ 𝟙ₒ       ＝⟨ II ⟩
               Pₒ +ₒ 𝟙ₒ              ∎
    where
     I  = ap (λ - → (Pₒ ⊕ -) +ₒ 𝟙ₒ) 𝟙ₒ-↓
     II = ap (_+ₒ 𝟙ₒ) (𝟘ₒ-is-right-neutral-⊕ Pₒ)

   I : sup g ＝ Pₒ +ₒ 𝟙ₒ
   I = ⊴-antisym (sup g) (Pₒ +ₒ 𝟙ₒ)
        (sup-is-lower-bound-of-upper-bounds _ (Pₒ +ₒ 𝟙ₒ) (dep-cases II III))
        (sup-is-upper-bound _ (inr ⋆))
    where
     II : (p : P) → 𝟙ₒ +ₒ 𝟙ₒ ⊴ Pₒ +ₒ 𝟙ₒ
     II p = transport⁻¹ (λ - → 𝟙ₒ +ₒ 𝟙ₒ ⊴ - +ₒ 𝟙ₒ)
             (holds-gives-equal-𝟙ₒ i p)
             (⊴-refl 𝟚ₒ)
     III : (u : 𝟙) → Pₒ +ₒ 𝟙ₒ ⊴ Pₒ +ₒ 𝟙ₒ
     III _ = ⊴-refl (Pₒ +ₒ 𝟙ₒ)

\end{code}

We use the above observation to show that Hessenberg addition, in general, fails
to be monotone, inflationary, or above ordinary addition.

\begin{code}

⊕-monotone-successor-gives-EM
 : ((α β : Ordinal 𝓤) → α ⊴ β → α ⊕ 𝟙ₒ ⊴ β ⊕ 𝟙ₒ)
 → EM 𝓤
⊕-monotone-successor-gives-EM {𝓤} h P i = succ-of-prop-taboo P i I
 where
  Pₒ : Ordinal 𝓤
  Pₒ = prop-ordinal P i

  I : Pₒ +ₒ 𝟙ₒ ⊴ 𝟙ₒ +ₒ 𝟙ₒ
  I = transport₂ _⊴_
       (⊕-prop-𝟙ₒ-is-+ₒ P i)
       (⊕-prop-𝟙ₒ-is-+ₒ 𝟙 𝟙-is-prop)
       (h Pₒ 𝟙ₒ (prop-ordinal-⊴-𝟙ₒ i))

⊕-monotone-gives-EM : ((α β γ : Ordinal 𝓤) → α ⊴ β → α ⊕ γ ⊴ β ⊕ γ) → EM 𝓤
⊕-monotone-gives-EM h = ⊕-monotone-successor-gives-EM (λ α β → h α β 𝟙ₒ)

⊕-inflationary-gives-EM : ((α β : Ordinal 𝓤) → α ⊴ α ⊕ β) → EM 𝓤
⊕-inflationary-gives-EM {𝓤} h P i = II (h 𝟙ₒ Pₒ)
 where
  Pₒ : Ordinal 𝓤
  Pₒ = prop-ordinal P i

  I : 𝟙ₒ ⊴ Pₒ +ₒ 𝟙ₒ → P + ¬ P
  I 𝕗@(f , f-sim) = I' (f ⋆) (simulations-preserve-↓ 𝟙ₒ (Pₒ +ₒ 𝟙ₒ) 𝕗 ⋆)
   where
    I' : (y : P + 𝟙) → 𝟙ₒ ↓ ⋆ ＝ (Pₒ +ₒ 𝟙ₒ) ↓ y → P + ¬ P
    I' (inl p) _ = inl p
    I' (inr u) e = inr (λ p → 𝟘ₒ-is-not-𝟙ₒ (e' p))
     where
      e' : (p : P) → 𝟘ₒ ＝ 𝟙ₒ
      e' p = 𝟘ₒ                 ＝⟨ 𝟙ₒ-↓ ⁻¹ ⟩
             𝟙ₒ ↓ ⋆             ＝⟨ e ⟩
             (Pₒ +ₒ 𝟙ₒ) ↓ inr u ＝⟨ (+ₒ-↓-right u) ⁻¹ ⟩
             Pₒ +ₒ (𝟙ₒ ↓ u)     ＝⟨ ap (Pₒ +ₒ_) 𝟙ₒ-↓ ⟩
             Pₒ +ₒ 𝟘ₒ           ＝⟨ 𝟘ₒ-right-neutral Pₒ ⟩
             Pₒ                 ＝⟨ holds-gives-equal-𝟙ₒ i p ⟩
             𝟙ₒ                 ∎

  II : 𝟙ₒ ⊴ 𝟙ₒ ⊕ Pₒ → P + ¬ P
  II l = I (transport (𝟙ₒ ⊴_) e l)
   where
    e = 𝟙ₒ ⊕ Pₒ  ＝⟨ ⊕-is-commutative 𝟙ₒ Pₒ ⟩
        Pₒ ⊕ 𝟙ₒ  ＝⟨ ⊕-prop-𝟙ₒ-is-+ₒ P i ⟩
        Pₒ +ₒ 𝟙ₒ ∎

⊕-above-+ₒ-gives-EM : ((α β : Ordinal 𝓤) → α +ₒ β ⊴ α ⊕ β) → EM 𝓤
⊕-above-+ₒ-gives-EM {𝓤} h P i = II I
 where
  Pₒ : Ordinal 𝓤
  Pₒ = prop-ordinal P i

  I : 𝟙ₒ +ₒ Pₒ ⊴ Pₒ +ₒ 𝟙ₒ
  I = transport (𝟙ₒ +ₒ Pₒ ⊴_) e (h 𝟙ₒ Pₒ)
   where
    e = 𝟙ₒ ⊕ Pₒ  ＝⟨ ⊕-is-commutative 𝟙ₒ Pₒ ⟩
        Pₒ ⊕ 𝟙ₒ  ＝⟨ ⊕-prop-𝟙ₒ-is-+ₒ P i ⟩
        Pₒ +ₒ 𝟙ₒ ∎

  II : type-of I → P + ¬ P
  II 𝕗@(f , f-sim) = IV (f (inl ⋆)) refl
   where
    III : (p : P) → f (inl ⋆) ＝ inl p
    III p = simulations-preserve-least (𝟙ₒ +ₒ Pₒ) (Pₒ +ₒ 𝟙ₒ)
             (inl ⋆) (inl p)
             f f-sim
             (left-preserves-least 𝟙ₒ Pₒ ⋆ 𝟙ₒ-least)
             (left-preserves-least Pₒ 𝟙ₒ p (prop-ordinal-least i p))
    IV : (x : P + 𝟙) → f (inl ⋆) ＝ x → P + ¬ P
    IV (inl p) e = inl p
    IV (inr ⋆) e = inr (λ p → +disjoint (inl p     ＝⟨ (III p) ⁻¹ ⟩
                                         f (inl ⋆) ＝⟨ e ⟩
                                         inr ⋆     ∎))

\end{code}