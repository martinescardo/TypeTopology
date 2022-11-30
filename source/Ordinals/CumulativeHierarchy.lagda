Tom de Jong, 28 October 2022 - 7 November 2022.
In collaboration with Nicolai Kraus, Fredrik Norvall Forsberg and Chuangjie Xu.

Following [3], in constructive set theory an ordinal is [Definition 9.4.1, 2],
defined as a transitive set of transitive sets.

We consider the subtype 𝕍ᵒʳᵈ of the cumulative hierarchy 𝕍 of set theoretic
ordinals in 𝕍 (see UF/CumulativeHierarchy.lagda and [Section 10.5, 5] for more
on 𝕍).

We show that (𝕍ᵒʳᵈ,∈) is a ordinal, in the type theoretic sense of [5], i.e. it
is a well-founded, extensional and transitive order. Moreover, we prove that
(𝕍ᵒʳᵈ,∈) and the ordinal Ord of type theoretic ordinals are isomorphic.

This is interesting for at least two reasons:
(1) It shows that the set theoretic and type theoretic notions of ordinal
    coincide in HoTT.
(2) It shows that a nontrivial subtype of 𝕍, a complicated HIT, can be defined
    internally in univalent type theory without HITs (†).

    (†): This was also done through other means by Gylterud [4] who gave a
         non-HIT construction of the cumulative hiearchy 𝕍.

After Fredrik Nordvall Forsberg's talk at the workshop in honour of Thorsten
Altenkirch's 60th birthday
(https://www.cs.nott.ac.uk/~psznk/events/thorsten60/#fred), Andreas Abel asked
how/whether we can relate set theoretic ordinals and type theoretic ordinals
through Aczel's [1] type theoretic interpretation of set theory. Since the
cumulative hierarchy 𝕍 may be seen as an internal refinement of Aczel's
interpretation in HoTT, the theorem announced above provides an answer to
Andreas' question.

There are some directions for future work recorded at the end of this file.

References
----------

[1] Peter Aczel
    The type theoretic interpretation of constructive set theory
    In A. MacIntyre, L. Pacholski, and J. Paris (eds.) Logic Colloquium ’77
    Volume 96 of Studies in Logic and the Foundations of Mathematics
    Pages 55–66
    North-Holland Publishing Company
    1978
    doi:10.1016/S0049-237X(08)71989-X

[2] Peter Aczel and Michael Rathjen
    Notes on Constructive Set Theory
    Book draft
    https://www1.maths.leeds.ac.uk/~rathjen/book.pdf
    2010

[3] William C. Powell
    Extending Gödel’s negative interpretation to ZF
    Volume 40, Issue 2 of Journal of Symbolic Logic
    Pages 221─229
    1975
    doi:10.2307/2271902

[4] Håkon Robbestad Gylterud
    From Multisets to Sets in Homotopy Type Theory
    Volue 83, Issue 3 of The Journal Symbol Logic
    Pages 1132─146
    2018
    doi:10.1017/jsl.2017.84

[5] The Univalent Foundations Program
    Homotopy Type Theory: Univalent Foundations of Mathematics
    https://homotopytypetheory.org/book
    Institute for Advanced Study
    2013

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan

open import UF.PropTrunc
open import UF.Univalence

module Ordinals.CumulativeHierarchy
        (pt : propositional-truncations-exist)
        (ua : Univalence)
        (𝓤 : Universe)
       where

open PropositionalTruncation pt

open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' _ _ = fe

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type hiding (Ord)

open import UF.CumulativeHierarchy pt fe pe

module _
        (ch : cumulative-hierarchy-exists 𝓤)
       where

 open cumulative-hierarchy-exists ch

\end{code}

We start by defining a set theoretic ordinal to be a transitive set whose
elements are again transitive sets, as announced above.

\begin{code}

 is-transitive-set : 𝕍 → 𝓤 ⁺ ̇
 is-transitive-set x = (u : 𝕍) (v : 𝕍) → u ∈ x → v ∈ u → v ∈ x

 being-transitive-set-is-prop : {x : 𝕍} → is-prop (is-transitive-set x)
 being-transitive-set-is-prop = Π₄-is-prop fe (λ _ _ _ _ → ∈-is-prop-valued)

 is-set-theoretic-ordinal : 𝕍 → 𝓤 ⁺ ̇
 is-set-theoretic-ordinal x = is-transitive-set x
                            × ((y : 𝕍) → y ∈ x → is-transitive-set y)

 being-set-theoretic-ordinal-is-prop : {x : 𝕍} → is-prop (is-set-theoretic-ordinal x)
 being-set-theoretic-ordinal-is-prop =
  ×-is-prop being-transitive-set-is-prop
            (Π₂-is-prop fe (λ _ _ → being-transitive-set-is-prop))

 transitive-set-if-set-theoretic-ordinal : {x : 𝕍}
                                         → is-set-theoretic-ordinal x
                                         → is-transitive-set x
 transitive-set-if-set-theoretic-ordinal = pr₁

 transitive-set-if-element-of-set-theoretic-ordinal : {x : 𝕍}
                                                    → is-set-theoretic-ordinal x
                                                    → {y : 𝕍} → y ∈ x
                                                    → is-transitive-set y
 transitive-set-if-element-of-set-theoretic-ordinal σ {y} m = pr₂ σ y m

 being-set-theoretic-ordinal-is-hereditary : {x : 𝕍} → is-set-theoretic-ordinal x
                                           → {y : 𝕍}
                                           → y ∈ x → is-set-theoretic-ordinal y
 being-set-theoretic-ordinal-is-hereditary {x} (t , τ) {y} m =
  τ y m , (λ z n → τ z (t y z m n))

\end{code}

Restricting our attention to those elements of 𝕍 that are set theoretic
ordinals, we show that the membership relation ∈ makes this subtype into a type
theoretic ordinal.

\begin{code}

 𝕍ᵒʳᵈ : 𝓤 ⁺ ̇
 𝕍ᵒʳᵈ = Σ x ꞉ 𝕍 , is-set-theoretic-ordinal x

 𝕍ᵒʳᵈ-is-subtype : {x y : 𝕍ᵒʳᵈ} → pr₁ x ＝ pr₁ y → x ＝ y
 𝕍ᵒʳᵈ-is-subtype = to-subtype-＝ (λ _ → being-set-theoretic-ordinal-is-prop)

 _∈ᵒʳᵈ_ : 𝕍ᵒʳᵈ → 𝕍ᵒʳᵈ → 𝓤 ⁺  ̇
 _∈ᵒʳᵈ_ (x , _) (y , _) = x ∈ y

 ∈ᵒʳᵈ-is-extensional : is-extensional _∈ᵒʳᵈ_
 ∈ᵒʳᵈ-is-extensional (x , u) (y , v) s t =
  𝕍ᵒʳᵈ-is-subtype
   (∈-extensionality
     x y
     (λ z m → s (z , being-set-theoretic-ordinal-is-hereditary u m) m)
     (λ z m → t (z , being-set-theoretic-ordinal-is-hereditary v m) m))

 ∈ᵒʳᵈ-is-transitive : is-transitive _∈ᵒʳᵈ_
 ∈ᵒʳᵈ-is-transitive (x , _) (y , _) (z , τ) x-in-y y-in-z =
  transitive-set-if-set-theoretic-ordinal τ y x y-in-z x-in-y

 ∈-is-well-founded : is-well-founded _∈_
 ∈-is-well-founded = ∈-induction (is-accessible _∈_)
                                 (λ x → accessibility-is-prop _∈_ fe' x)
                                 (λ x IH → step IH)

 ∈ᵒʳᵈ-is-well-founded : is-well-founded _∈ᵒʳᵈ_
 ∈ᵒʳᵈ-is-well-founded = transfinite-induction-converse _∈ᵒʳᵈ_ W
  where
   W : Well-founded _∈ᵒʳᵈ_
   W P IH = (λ (x , σ) → Q-holds-everywhere x σ)
    where
     Q : 𝕍 → 𝓤 ⁺ ̇
     Q x = (σ : is-set-theoretic-ordinal x) → P (x , σ)
     Q-holds-everywhere : (x : 𝕍) → Q x
     Q-holds-everywhere = transfinite-induction _∈_ ∈-is-well-founded Q f
      where
       f : (x : 𝕍) → ((y : 𝕍) → y ∈ x → Q y) → Q x
       f x IH' σ = IH (x , σ) g
        where
         g : (y : 𝕍ᵒʳᵈ) → y ∈ᵒʳᵈ (x , σ) → P y
         g (y , τ) y-in-x = IH' y y-in-x τ

 𝕍ᴼᴿᴰ : Ordinal (𝓤 ⁺)
 𝕍ᴼᴿᴰ = 𝕍ᵒʳᵈ , _∈ᵒʳᵈ_
             , (λ x y → ∈-is-prop-valued)
             , ∈ᵒʳᵈ-is-well-founded
             , ∈ᵒʳᵈ-is-extensional
             , ∈ᵒʳᵈ-is-transitive

\end{code}

We now work towards proving that 𝕍ᴼᴿᴰ and Ord, the ordinal of type theoretic
ordinals, are isomorphic (as type theoretic ordinals).

We start by defining a map Ord → 𝕍 by transfinite recursion on Ord.

\begin{code}

 private
  Ord : 𝓤 ⁺ ̇
  Ord = Ordinal 𝓤

 Ord-to-𝕍 : Ord → 𝕍
 Ord-to-𝕍 = transfinite-recursion-on-OO 𝕍 (λ α f → 𝕍-set f)

 Ord-to-𝕍-behaviour : (α : Ord) → Ord-to-𝕍 α ＝ 𝕍-set (λ a → Ord-to-𝕍 (α ↓ a))
 Ord-to-𝕍-behaviour = transfinite-recursion-on-OO-behaviour 𝕍 (λ a f → 𝕍-set f)

 ∈-of-Ord-to-𝕍 : (α : Ord) (x : 𝕍)
                → x ∈ Ord-to-𝕍 α ＝ (∃ a ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ a) ＝ x)
 ∈-of-Ord-to-𝕍 α x =
  x ∈ Ord-to-𝕍 α                        ＝⟨ ap (x ∈_) (Ord-to-𝕍-behaviour α) ⟩
  x ∈ 𝕍-set (λ a → Ord-to-𝕍 (α ↓ a))    ＝⟨ ∈-for-𝕍-sets x _ ⟩
  (∃ a ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ a) ＝ x) ∎

 to-∈-of-Ord-to-𝕍 : (α : Ord) {x : 𝕍}
                  → (∃ a ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ a) ＝ x) → x ∈ Ord-to-𝕍 α
 to-∈-of-Ord-to-𝕍 α {x} = back-Idtofun (∈-of-Ord-to-𝕍 α x)

 from-∈-of-Ord-to-𝕍 : (α : Ord) {x : 𝕍}
                    → x ∈ Ord-to-𝕍 α → (∃ a ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ a) ＝ x)
 from-∈-of-Ord-to-𝕍 α {x} = Idtofun (∈-of-Ord-to-𝕍 α x)

\end{code}

The map Ord → 𝕍 preserves the strict and weak order.

\begin{code}

 Ord-to-𝕍-preserves-strict-order : (α β : Ord) → α ⊲ β → Ord-to-𝕍 α ∈ Ord-to-𝕍 β
 Ord-to-𝕍-preserves-strict-order α β (b , refl) = to-∈-of-Ord-to-𝕍 β ∣ b , refl ∣

 Ord-to-𝕍-preserves-weak-order : (α β : Ord) → α ⊴ β → Ord-to-𝕍 α ⊆ Ord-to-𝕍 β
 Ord-to-𝕍-preserves-weak-order α β l x m = to-∈-of-Ord-to-𝕍 β m'
  where
   l' : (a : ⟨ α ⟩) → Σ b ꞉ ⟨ β ⟩ , α ↓ a ＝ β ↓ b
   l' = from-≼ (⊴-gives-≼ α β l)
   m' : ∃ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ x
   m' = ∥∥-functor h (from-∈-of-Ord-to-𝕍 α m)
    where
     h : (Σ a ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ a) ＝ x)
       → (Σ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ x)
     h (a , refl) = (b , ap Ord-to-𝕍 (e ⁻¹))
      where
       b : ⟨ β ⟩
       b = pr₁ (l' a)
       e : α ↓ a ＝ β ↓ b
       e = pr₂ (l' a)

\end{code}

An argument by transfinite induction shows that the map Ord-to-𝕍 is left
cancellable, which yields a quick proof that Ord-to-𝕍 not only preserves the
strict order, but also reflects it. It follows that Ord-to-𝕍 also reflects the
weak order.

\begin{code}

 Ord-to-𝕍-is-left-cancellable : (α β : Ord) → Ord-to-𝕍 α ＝ Ord-to-𝕍 β → α ＝ β
 Ord-to-𝕍-is-left-cancellable = transfinite-induction-on-OO _ f
  where
   f : (α : Ord)
     → ((a : ⟨ α ⟩) (β : Ord) → Ord-to-𝕍 (α ↓ a) ＝ Ord-to-𝕍 β → (α ↓ a) ＝ β)
     → (β : Ord) → Ord-to-𝕍 α ＝ Ord-to-𝕍 β → α ＝ β
   f α IH β e = ⊴-antisym α β (to-⊴ α β g₁) (to-⊴ β α g₂)
    where
     g₁ : (a : ⟨ α ⟩) → (α ↓ a) ⊲ β
     g₁ a = ∥∥-rec (⊲-is-prop-valued (α ↓ a) β) h (from-∈-of-Ord-to-𝕍 β m)
      where
       h : (Σ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ Ord-to-𝕍 (α ↓ a)) → (α ↓ a) ⊲ β
       h (b , e) = (b , (IH a (β ↓ b) (e ⁻¹)))
       m : Ord-to-𝕍 (α ↓ a) ∈ Ord-to-𝕍 β
       m = transport (Ord-to-𝕍 (α ↓ a) ∈_) e
                     (to-∈-of-Ord-to-𝕍 α ∣ a , refl ∣)
     g₂ : (b : ⟨ β ⟩) → (β ↓ b) ⊲ α
     g₂ b = ∥∥-rec (⊲-is-prop-valued (β ↓ b) α) h (from-∈-of-Ord-to-𝕍 α m)
      where
       h : (Σ a ꞉ ⟨ α ⟩ , Ord-to-𝕍 (α ↓ a) ＝ Ord-to-𝕍 (β ↓ b)) → (β ↓ b) ⊲ α
       h (a , e) = (a , ((IH a (β ↓ b) e) ⁻¹))
       m : Ord-to-𝕍 (β ↓ b) ∈ Ord-to-𝕍 α
       m = transport (Ord-to-𝕍 (β ↓ b) ∈_) (e ⁻¹)
                     (to-∈-of-Ord-to-𝕍 β ∣ b , refl ∣)

 Ord-to-𝕍-reflects-strict-order : (α β : Ord) → Ord-to-𝕍 α ∈ Ord-to-𝕍 β → α ⊲ β
 Ord-to-𝕍-reflects-strict-order α β m = ∥∥-rec (⊲-is-prop-valued α β) h m'
  where
   h : (Σ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ Ord-to-𝕍 α) → α ⊲ β
   h (b , e) = (b , ((Ord-to-𝕍-is-left-cancellable (β ↓ b) α e) ⁻¹))
   m' : ∃ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ Ord-to-𝕍 α
   m' = from-∈-of-Ord-to-𝕍 β m

 Ord-to-𝕍-reflects-weak-order : (α β : Ord) → Ord-to-𝕍 α ⊆ Ord-to-𝕍 β → α ⊴ β
 Ord-to-𝕍-reflects-weak-order α β s = to-⊴ α β h
  where
   h : (a : ⟨ α ⟩) → (α ↓ a) ⊲ β
   h a = Ord-to-𝕍-reflects-strict-order (α ↓ a) β m
    where
     m : Ord-to-𝕍 (α ↓ a) ∈ Ord-to-𝕍 β
     m = s (Ord-to-𝕍 (α ↓ a)) (to-∈-of-Ord-to-𝕍 α ∣ a , refl ∣)

\end{code}

The map Ord → 𝕍 constructed above actually factors through the subtype 𝕍ᵒʳᵈ.

(The proof is quite straightforward, but the formal proof is slightly long,
because we need to use from-∈-of-Ord-to-𝕍 and to-∈-of-Ord-to-𝕍 as we don't have
judgemental computation rules for 𝕍.)

\begin{code}

 Ord-to-𝕍ᵒʳᵈ : Ord → 𝕍ᵒʳᵈ
 Ord-to-𝕍ᵒʳᵈ α = (Ord-to-𝕍 α , ρ α)
  where
   τ : (β : Ord) → is-transitive-set (Ord-to-𝕍 β)
   τ β x y x-in-β y-in-x = to-∈-of-Ord-to-𝕍 β (∥∥-rec ∃-is-prop lemma x-in-β')
    where
     x-in-β' : ∃ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ x
     x-in-β' = from-∈-of-Ord-to-𝕍 β x-in-β
     lemma : (Σ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ x)
           → ∃ c ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ c) ＝ y
     lemma (b , refl) = ∥∥-functor h y-in-β↓b
      where
       h : (Σ c ꞉ ⟨ β ↓ b ⟩ , Ord-to-𝕍 ((β ↓ b) ↓ c) ＝ y)
         → Σ d ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ d) ＝ y
       h ((c , l) , refl) = (c , ap Ord-to-𝕍 ((iterated-↓ β b c l) ⁻¹))
       y-in-β↓b : ∃ c ꞉ ⟨ β ↓ b ⟩ , Ord-to-𝕍 ((β ↓ b) ↓ c) ＝ y
       y-in-β↓b = from-∈-of-Ord-to-𝕍 (β ↓ b) y-in-x

   ρ : (β : Ord) → is-set-theoretic-ordinal (Ord-to-𝕍 β)
   ρ = transfinite-induction-on-OO
        (λ - → is-set-theoretic-ordinal (Ord-to-𝕍 -))
        ρ'
    where
     ρ' : (β : Ord)
        → ((b : ⟨ β ⟩) → is-set-theoretic-ordinal (Ord-to-𝕍 (β ↓ b)))
        → is-set-theoretic-ordinal (Ord-to-𝕍 β)
     ρ' β IH = (τ β , τ')
      where
       τ' : (y : 𝕍) → y ∈ Ord-to-𝕍 β → is-transitive-set y
       τ' y m = ∥∥-rec being-transitive-set-is-prop h (from-∈-of-Ord-to-𝕍 β m)
        where
         h : (Σ b ꞉ ⟨ β ⟩ , Ord-to-𝕍 (β ↓ b) ＝ y) → is-transitive-set y
         h (b , refl) = τ (β ↓ b)

 Ord-to-𝕍ᵒʳᵈ-is-left-cancellable : {α β : Ord}
                                 → Ord-to-𝕍ᵒʳᵈ α ＝ Ord-to-𝕍ᵒʳᵈ β → α ＝ β
 Ord-to-𝕍ᵒʳᵈ-is-left-cancellable {α} {β} e =
  Ord-to-𝕍-is-left-cancellable α β (ap pr₁ e)

\end{code}

To show that Ord-to-𝕍ᵒʳᵈ is an isomorphism of ordinals it now suffices to prove
that it is split surjective.

We construct a map 𝕍 → Ord by recursion on 𝕍 by sending 𝕍-set {A} f to the
supremum of ordinals ⋁ (ψ (f a) + 𝟙) indexed by a : A.

This is a familiar construction in set theory, see e.g. [Definition 9.3.4, 2],
where the ordinal above is the "rank" of the set.

\begin{code}

 open import Ordinals.Arithmetic fe'
 open import Ordinals.Arithmetic-Properties ua hiding (lemma₁ ; lemma₂)
 open import Ordinals.OrdinalOfOrdinalsSuprema ua

 open import UF.Quotient hiding (is-prop-valued)

 module _
         (sq : set-quotients-exist)
        where

  open suprema pt (set-replacement-from-set-quotients sq pt)

  private
   𝕍-to-Ord-aux : {A : 𝓤 ̇ } → (A → 𝕍) → (A → Ord) → Ord
   𝕍-to-Ord-aux _ r = sup (λ a → r a +ₒ 𝟙ₒ)

   𝕍-to-Ord-packaged : Σ ϕ ꞉ (𝕍 → Ord) , ({A : 𝓤 ̇} (f : A → 𝕍)
                                          (r : A → Ordinal 𝓤)
                                       → ϕ (𝕍-set f) ＝ 𝕍-to-Ord-aux f r)
   𝕍-to-Ord-packaged =
    𝕍-recursion-with-computation the-type-of-ordinals-is-a-set ρ τ
    where
     ρ = 𝕍-to-Ord-aux
     monotone-lemma : {A B : 𝓤 ̇} (f : A → 𝕍) (g : B → 𝕍)
                    → (r₁ : A → Ord) (r₂ : B → Ord)
                    → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , r₁ a ＝ r₂ b ∥)
                    → ρ f r₁ ⊴ ρ g r₂
     monotone-lemma {A} {B} f g r₁ r₂ e =
      sup-is-lower-bound-of-upper-bounds (λ a → r₁ a +ₒ 𝟙ₒ) (ρ g r₂) ϕ
       where
        ϕ : (a : A) → (r₁ a +ₒ 𝟙ₒ) ⊴ ρ g r₂
        ϕ a = ∥∥-rec (⊴-is-prop-valued _ _) ψ (e a)
         where
          ψ : (Σ b ꞉ B , Σ p ꞉ f a ＝ g b , r₁ a ＝ r₂ b)
            → (r₁ a +ₒ 𝟙ₒ) ⊴ ρ g r₂
          ψ (b , _ , q) = ⊴-trans _ (r₂ b +ₒ 𝟙ₒ) _ k l
           where
            k : (r₁ a +ₒ 𝟙ₒ) ⊴ (r₂ b +ₒ 𝟙ₒ)
            k = ≃ₒ-to-⊴ _ _ (idtoeqₒ _ _ (ap (_+ₒ 𝟙ₒ) q))
            l : (r₂ b +ₒ 𝟙ₒ) ⊴ ρ g r₂
            l = sup-is-upper-bound _ b
     τ : {A B : 𝓤 ̇} (f : A → 𝕍) (g : B → 𝕍)
       → (r₁ : A → Ord) (r₂ : B → Ord)
       → ((a : A) → ∥ Σ b ꞉ B , Σ p ꞉ f a ＝ g b , r₁ a ＝ r₂ b ∥)
       → ((b : B) → ∥ Σ a ꞉ A , Σ p ꞉ g b ＝ f a , r₂ b ＝ r₁ a ∥)
       → f ≈ g
       → ρ f r₁ ＝ ρ g r₂
     τ {A} {B} f g r₁ r₂ e₁ e₂ _ =
      ⊴-antisym (ρ f r₁) (ρ g r₂)
                (monotone-lemma f g r₁ r₂ e₁)
                (monotone-lemma g f r₂ r₁ e₂)

  𝕍-to-Ord : 𝕍 → Ord
  𝕍-to-Ord = pr₁ (𝕍-to-Ord-packaged)

\end{code}

The below records the behaviour on 𝕍-sets that we announced above.

\begin{code}

  𝕍-to-Ord-behaviour-on-𝕍-sets :
     {A : 𝓤 ̇ } (f : A → 𝕍)
   → 𝕍-to-Ord (𝕍-set f) ＝ sup (λ a → 𝕍-to-Ord (f a) +ₒ 𝟙ₒ)
  𝕍-to-Ord-behaviour-on-𝕍-sets f = pr₂ 𝕍-to-Ord-packaged f (λ a → 𝕍-to-Ord (f a))

  𝕍ᵒʳᵈ-to-Ord : 𝕍ᵒʳᵈ → Ord
  𝕍ᵒʳᵈ-to-Ord = 𝕍-to-Ord ∘ pr₁

\end{code}

We show that Ord-to-𝕍 is a split surjection by showing that 𝕍ᵒʳᵈ-to-Ord is a
section of it. The fact that we are restricting the inputs to set theoretic
ordinals is crucial in proving one of the inequalities.

\begin{code}

  𝕍-to-Ord-is-section-of-Ord-to-𝕍 : (x : 𝕍)
                                  → is-set-theoretic-ordinal x
                                  → Ord-to-𝕍 (𝕍-to-Ord x) ＝ x
  𝕍-to-Ord-is-section-of-Ord-to-𝕍 =
   𝕍-prop-induction _ (λ x → Π-is-prop fe (λ _ → 𝕍-is-large-set)) ρ
    where
     ρ : {A : 𝓤 ̇} (f : A → 𝕍)
       → ((a : A) → is-set-theoretic-ordinal (f a)
                  → Ord-to-𝕍 (𝕍-to-Ord (f a)) ＝ f a)
       → is-set-theoretic-ordinal (𝕍-set f)
       → Ord-to-𝕍 (𝕍-to-Ord (𝕍-set f)) ＝ 𝕍-set f
     ρ {A} f IH σ =
      Ord-to-𝕍 (𝕍-to-Ord (𝕍-set f))  ＝⟨ ⦅1⦆ ⟩
      Ord-to-𝕍 s                     ＝⟨ ⦅2⦆ ⟩
      𝕍-set (λ y → Ord-to-𝕍 (s ↓ y)) ＝⟨ ⦅3⦆ ⟩
      𝕍-set f                        ∎
       where
        s : Ord
        s = sup (λ a → 𝕍-to-Ord (f a) +ₒ 𝟙ₒ)
        ⦅1⦆ = ap Ord-to-𝕍 (𝕍-to-Ord-behaviour-on-𝕍-sets f)
        ⦅2⦆ = Ord-to-𝕍-behaviour s
        ⦅3⦆ = 𝕍-set-ext _ _ (e₁ , e₂)
          {- The proof of e₂ and especially e₁ are the only hard parts. We set
             up two lemmas and some abbreviations to get e₁ and e₂. -}
         where
          c : (a : A) → Ord
          c a = 𝕍-to-Ord (f a) +ₒ 𝟙ₒ
          abstract -- For performance
           u : (a : A) → ⟨ c a ⟩  → ⟨ s ⟩
           u a = pr₁ (sup-is-upper-bound _ a)

           IH' : (a : A) → Ord-to-𝕍 (𝕍-to-Ord (f a)) ＝ f a
           IH' a = IH a (being-set-theoretic-ordinal-is-hereditary σ
                          (to-∈-of-𝕍-set ∣ a , refl ∣))

           lemma₁ : (a : A) → Ord-to-𝕍 (c a ↓ inr ⋆) ＝ f a
           lemma₁ a = Ord-to-𝕍 (c a ↓ inr ⋆)     ＝⟨ ap Ord-to-𝕍 ⦅e⦆ ⟩
                      Ord-to-𝕍 (𝕍-to-Ord (f a)) ＝⟨ IH' a            ⟩
                      f a ∎
            where
             ⦅e⦆ : c a ↓ inr ⋆ ＝ 𝕍-to-Ord (f a)
             ⦅e⦆ = +ₒ-𝟙ₒ-↓-right (𝕍-to-Ord (f a))

           lemma₂ : (a : A) → Ord-to-𝕍 (s ↓ u a (inr ⋆)) ＝ f a
           lemma₂ a = Ord-to-𝕍 (s ↓ u a (inr ⋆)) ＝⟨ ap Ord-to-𝕍 ⦅e⦆ ⟩
                      Ord-to-𝕍 (c a ↓ inr ⋆)     ＝⟨ lemma₁ a ⟩
                      f a                        ∎
            where
             ⦅e⦆ : s ↓ u a (inr ⋆) ＝ c a ↓ inr ⋆
             ⦅e⦆ = initial-segment-of-sup-at-component _ a (inr ⋆)

          e₂ : f ≲ (λ y → Ord-to-𝕍 (s ↓ y))
          e₂ a = ∣ u a (inr ⋆) , lemma₂ a ∣

          e₁ : (λ y → Ord-to-𝕍 (s ↓ y)) ≲ f
          e₁ y =
           ∥∥-rec ∃-is-prop h
            (initial-segment-of-sup-is-initial-segment-of-some-component _ y)
            where
             h : (Σ a ꞉ A , Σ x ꞉ ⟨ c a ⟩ , s ↓ y ＝ c a ↓ x)
               → ∃ a ꞉ A , f a ＝ Ord-to-𝕍 (s ↓ y)
             h (a , inr ⋆ , e) = ∣ a , (e' ⁻¹) ∣
              where
               e' = Ord-to-𝕍 (s ↓ y)       ＝⟨ ap Ord-to-𝕍 e ⟩
                    Ord-to-𝕍 (c a ↓ inr ⋆) ＝⟨ lemma₁ a ⟩
                    f a                    ∎
             h (a , inl x , e) = goal
              where
               ∈-claim₁ : Ord-to-𝕍 (𝕍-to-Ord (f a) ↓ x) ∈ f a
               ∈-claim₁ = transport (Ord-to-𝕍 (𝕍-to-Ord (f a) ↓ x) ∈_)
                                    (IH' a)
                                    (Ord-to-𝕍-preserves-strict-order
                                      (𝕍-to-Ord (f a) ↓ x)
                                      (𝕍-to-Ord (f a))
                                      (x , refl))
               ∈-claim₂ : Ord-to-𝕍 (𝕍-to-Ord (f a) ↓ x) ∈ 𝕍-set f
               ∈-claim₂ = transitive-set-if-set-theoretic-ordinal σ
                            (f a)
                            (Ord-to-𝕍 (𝕍-to-Ord (f a) ↓ x))
                            (to-∈-of-𝕍-set ∣ a , refl ∣)
                            ∈-claim₁

               goal : ∃ a' ꞉ A , f a' ＝ Ord-to-𝕍 (s ↓ y)
               goal = ∥∥-functor g (from-∈-of-𝕍-set ∈-claim₂)
                where
                 g : (Σ a' ꞉ A , f a' ＝ Ord-to-𝕍 (𝕍-to-Ord (f a) ↓ x))
                   → Σ a' ꞉ A , f a' ＝ Ord-to-𝕍 (s ↓ y)
                 g (a' , p) = (a' , q)
                  where
                   q = f a'                          ＝⟨ p  ⟩
                       Ord-to-𝕍 (𝕍-to-Ord (f a) ↓ x) ＝⟨ e' ⟩
                       Ord-to-𝕍 (s ↓ y)              ∎
                    where
                     ↓-fact : c a ↓ inl x ＝ 𝕍-to-Ord (f a) ↓ x
                     ↓-fact = +ₒ-↓-left x ⁻¹
                     e' = ap Ord-to-𝕍 (↓-fact ⁻¹ ∙ e ⁻¹)


  𝕍ᵒʳᵈ-to-Ord-is-section-of-Ord-to-𝕍ᵒʳᵈ : Ord-to-𝕍ᵒʳᵈ ∘ 𝕍ᵒʳᵈ-to-Ord ∼ id
  𝕍ᵒʳᵈ-to-Ord-is-section-of-Ord-to-𝕍ᵒʳᵈ (x , σ) =
   𝕍ᵒʳᵈ-is-subtype (𝕍-to-Ord-is-section-of-Ord-to-𝕍 x σ)

\end{code}

Finally we obtain the result that ordinal of type theoretic ordinals is
isomorphic to the (type theoretic) ordinal 𝕍ᴼᴿᴰ of set theoretic ordinals.

\begin{code}

  𝕍ᵒʳᵈ-isomorphic-to-Ord : OO 𝓤 ≃ₒ 𝕍ᴼᴿᴰ
  𝕍ᵒʳᵈ-isomorphic-to-Ord =
   Ord-to-𝕍ᵒʳᵈ , order-preserving-reflecting-equivs-are-order-equivs
                  (OO 𝓤) 𝕍ᴼᴿᴰ Ord-to-𝕍ᵒʳᵈ
                  Ord-to-𝕍ᵒʳᵈ-is-equiv
                  Ord-to-𝕍-preserves-strict-order
                  Ord-to-𝕍-reflects-strict-order
    where
     Ord-to-𝕍ᵒʳᵈ-is-split-surjective : (x : 𝕍ᵒʳᵈ)
                                     → Σ α ꞉ Ord , Ord-to-𝕍ᵒʳᵈ α ＝ x
     Ord-to-𝕍ᵒʳᵈ-is-split-surjective x = 𝕍ᵒʳᵈ-to-Ord x
                                       , 𝕍ᵒʳᵈ-to-Ord-is-section-of-Ord-to-𝕍ᵒʳᵈ x

     Ord-to-𝕍ᵒʳᵈ-is-equiv : is-equiv (Ord-to-𝕍ᵒʳᵈ)
     Ord-to-𝕍ᵒʳᵈ-is-equiv = lc-split-surjections-are-equivs
                             Ord-to-𝕍ᵒʳᵈ
                             Ord-to-𝕍ᵒʳᵈ-is-left-cancellable
                             Ord-to-𝕍ᵒʳᵈ-is-split-surjective


\end{code}

Future work
-----------

(1) The recursive nature of 𝕍-to-Ord is convenient because it allows us to prove
    properties by induction. Moreover, the supremum yields an ordinal by
    construction. It is possible to give a more direct presentation of
    𝕍-to-Ord (𝕍-set {A} f) however, that is nonrecursive.

    Namely, we can show that 𝕍-to-Ord (𝕍-set {A} f) ＝ (A/~ , <), where ~
    identifies elements of A that have the same image under f and [a] < [a'] is
    defined as f a ∈ f a'.

    It is straightforward to see that (A/~ , <) is in fact equivalent (but not
    equal for size reasons) to the image of f, which in turn is equivalent to
    the total space (Σ y ꞉ 𝕍 , y ∈ 𝕍-set f), so that the map 𝕍-to-Ord can be
    described (up to equivalence) as x ↦ Σ y ꞉ 𝕍 , y ∈ x.

(2) We are currently working out the details of a related presentation for all
    of 𝕍.

\begin{code}

 module _
         (sq : set-quotients-exist)
         {A : 𝓤 ̇ }
         (f : A → 𝕍)
        where

  open set-quotients-exist sq
  open extending-relations-to-quotient fe pe

  _~_ : A → A → 𝓤 ⁺ ̇
  a ~ b = f a ＝ f b

  ~EqRel : EqRel A
  ~EqRel = _~_ , (λ a b → 𝕍-is-large-set)
               , (λ a → refl)
               , (λ a b e → e ⁻¹)
               , (λ a b c e₁ e₂ → e₁ ∙ e₂)

  A/~ : 𝓤 ⁺ ̇
  A/~ = A / ~EqRel

  [_] : A → A/~
  [_] = η/ ~EqRel

  -- TO DO: Use bisimilation relation on 𝕍 instead to have A/~ in 𝓤

  _≺[Ω]_ : A/~ → A/~ → Ω (𝓤 ⁺)
  _≺[Ω]_ = extension-rel₂ ~EqRel (λ a b → f a ∈[Ω] f b) ρ
   where
    ρ : {a b a' b' : A}
      → a ~ a' → b ~ b' → f a ∈[Ω] f b ＝ f a' ∈[Ω] f b'
    ρ {a} {b} {a'} {b'} e e' =
     Ω-extensionality fe pe (transport₂ _∈_ e e')
                            (transport₂ _∈_ (e ⁻¹) (e' ⁻¹))

  _≺_ : A/~ → A/~ → 𝓤 ⁺ ̇
  a ≺ b = (a ≺[Ω] b) holds

  ≺-is-prop-valued : is-prop-valued _≺_
  ≺-is-prop-valued a b = holds-is-prop (a ≺[Ω] b)

  ≺-＝-∈ : {a b : A} → [ a ] ≺ [ b ] ＝ f a ∈ f b
  ≺-＝-∈ {a} {b} = ap (_holds) (extension-rel-triangle₂ ~EqRel _ _ a b)

  ∈-to-≺ : {a b : A} → f a ∈ f b → [ a ] ≺ [ b ]
  ∈-to-≺ = back-Idtofun ≺-＝-∈

  ≺-to-∈ : {a b : A} → [ a ] ≺ [ b ] → f a ∈ f b
  ≺-to-∈ = Idtofun ≺-＝-∈

  ≺-is-transitive : is-set-theoretic-ordinal (𝕍-set f)
                  → is-transitive _≺_
  ≺-is-transitive σ = /-induction₃ fe ~EqRel prop-valued trans
    where
     prop-valued : (x y z : A / ~EqRel) → is-prop (x ≺ y → y ≺ z → x ≺ z)
     prop-valued x y z = Π₂-is-prop fe (λ _ _ → ≺-is-prop-valued x z)
     trans : (a b c : A) → [ a ] ≺ [ b ] → [ b ] ≺ [ c ] → [ a ] ≺ [ c ]
     trans a b c m n = ∈-to-≺ (τ (f a) (≺-to-∈ n) (≺-to-∈ m))
      where
       τ : (v : 𝕍) → f b ∈ f c → v ∈ f b → v ∈ f c
       τ = transitive-set-if-element-of-set-theoretic-ordinal σ
            (to-∈-of-𝕍-set ∣ c , refl ∣) (f b)

  ≺-is-extensional : is-transitive-set (𝕍-set f)
                   → is-extensional _≺_
  ≺-is-extensional τ =
   /-induction₂ fe ~EqRel (λ x y → Π₂-is-prop fe (λ _ _ → /-is-set ~EqRel))
                ext
    where
     ext : (a b : A)
         → ((x : A/~) → x ≺ [ a ] → x ≺ [ b ])
         → ((x : A/~) → x ≺ [ b ] → x ≺ [ a ])
         → [ a ] ＝ [ b ]
     ext a b s t = η/-identifies-related-points ~EqRel e'
      where
       e' : a ~ b
       e' = ∈-extensionality (f a) (f b) s' t'
        where
         lem : (x : 𝕍) (c : A) → x ∈ f c → ∃ d ꞉ A , f d ＝ x
         lem x c m = from-∈-of-𝕍-set (τ (f c) x (to-∈-of-𝕍-set ∣ c , refl ∣) m)
         s' : f a ⊆ f b
         s' x m = ∥∥-rec ∈-is-prop-valued h (lem x a m)
          where
           h : (Σ c ꞉ A , f c ＝ x) → x ∈ f b
           h (c , refl) = ≺-to-∈ (s [ c ] (∈-to-≺ m))
         t' : f b ⊆ f a
         t' x m = ∥∥-rec ∈-is-prop-valued h (lem x b m)
          where
           h : (Σ c ꞉ A , f c ＝ x) → x ∈ f a
           h (c , refl) = ≺-to-∈ (t [ c ] (∈-to-≺ m))

  ≺-is-well-founded : is-well-founded _≺_
  ≺-is-well-founded = /-induction ~EqRel acc-is-prop acc
   where
    acc-is-prop : (x : A/~) → is-prop (is-accessible _≺_ x)
    acc-is-prop = accessibility-is-prop _≺_ fe'
    acc' : (x : 𝕍) → ((a : A) → f a ＝ x → is-accessible _≺_ [ a ])
    acc' = transfinite-induction _∈_ ∈-is-well-founded _ h
     where
      h : (x : 𝕍)
        → ((y : 𝕍) → y ∈ x → (a : A) → f a ＝ y → is-accessible _≺_ [ a ])
        → (a : A) → f a ＝ x → is-accessible _≺_ [ a ]
      h x IH a refl =
       step (/-induction ~EqRel (λ _ → Π-is-prop fe (λ _ → acc-is-prop _)) α)
        where
         α : (b : A) → [ b ] ≺ [ a ] → is-accessible _≺_ [ b ]
         α b m = IH (f b) (≺-to-∈ m) b refl
    acc : (a : A) → is-accessible _≺_ [ a ]
    acc a = acc' (f a) a refl

  module construct-ordinal-as-quotient
          (σ : is-set-theoretic-ordinal (𝕍-set f))
         where

   A/~ᵒʳᵈ : Ordinal (𝓤 ⁺)
   A/~ᵒʳᵈ = A/~ , _≺_
                , ≺-is-prop-valued
                , ≺-is-well-founded
                , ≺-is-extensional (transitive-set-if-set-theoretic-ordinal σ)
                , ≺-is-transitive σ

\end{code}

Now we show that A/~ is equivalent to a type in 𝓤 which then gives us an ordinal
in 𝓤 equivalent to A/~ᵒʳᵈ.

\begin{code}

  _~⁻_ : A → A → 𝓤 ̇
  a ~⁻ b = f a ＝⁻ f b

  ~⁻EqRel : EqRel A
  ~⁻EqRel = _~⁻_ , (λ a b → ＝⁻-is-prop-valued)
                 , (λ a → ＝⁻-is-reflexive)
                 , (λ a b → ＝⁻-is-symmetric)
                 , (λ a b c → ＝⁻-is-transitive)

  A/~⁻ : 𝓤 ̇
  A/~⁻ = A / ~⁻EqRel

  A/~-≃-A/~⁻ : A/~ ≃ A/~⁻
  A/~-≃-A/~⁻ = quotients-equivalent A ~EqRel ~⁻EqRel (＝-to-＝⁻ , ＝⁻-to-＝)

  open import UF.Size -- TO DO: Move imports
  open import Ordinals.WellOrderTransport (λ _ _ → fe)

  ≺-has-small-values : (x y : A/~) → is-small (x ≺ y)
  ≺-has-small-values =
   /-induction₂ fe ~EqRel
                (λ x y → being-small-is-prop ua (x ≺ y) 𝓤)
                (λ a b → (f a ∈⁻ f b)
                       , ((f a ∈⁻ f b)    ≃⟨ ∈⁻-≃-∈ ⟩
                          (f a ∈ f b)     ≃⟨ idtoeq _ _ (≺-＝-∈ ⁻¹) ⟩
                          ([ a ] ≺ [ b ]) ■))

  _≺⁻_ : A/~ → A/~ → 𝓤 ̇
  x ≺⁻ y = pr₁ (≺-has-small-values x y)

  ≺-≃-≺⁻ : {x y : A/~} → x ≺ y ≃ x ≺⁻ y
  ≺-≃-≺⁻ {x} {y} = ≃-sym (pr₂ (≺-has-small-values x y))

  module _
          (σ : is-set-theoretic-ordinal (𝕍-set f))
         where

   open construct-ordinal-as-quotient σ

   private
    resize-ordinal : Σ s ꞉ OrdinalStructure A/~⁻ , (A/~⁻ , s) ≃ₒ A/~ᵒʳᵈ
    resize-ordinal = transfer-structure A/~⁻ A/~ᵒʳᵈ (≃-sym A/~-≃-A/~⁻)
                      (_≺⁻_ , (λ x y → ≺-≃-≺⁻))

   A/~⁻ᵒʳᵈ : Ordinal 𝓤
   A/~⁻ᵒʳᵈ = A/~⁻ , pr₁ resize-ordinal

   A/~⁻ᵒʳᵈ-≃ₒ-A/~ᵒʳᵈ : A/~⁻ᵒʳᵈ ≃ₒ A/~ᵒʳᵈ
   A/~⁻ᵒʳᵈ-≃ₒ-A/~ᵒʳᵈ = pr₂ resize-ordinal

   A/~ᵒʳᵈ--≃ₒ-A/~⁻ᵒʳᵈ : A/~ᵒʳᵈ ≃ₒ A/~⁻ᵒʳᵈ
   A/~ᵒʳᵈ--≃ₒ-A/~⁻ᵒʳᵈ = ≃ₒ-sym A/~⁻ᵒʳᵈ A/~ᵒʳᵈ A/~⁻ᵒʳᵈ-≃ₒ-A/~ᵒʳᵈ

   [_]⁻ : A → A/~⁻
   [_]⁻ = ⌜ A/~-≃-A/~⁻ ⌝ ∘ [_]

\end{code}

    PROOF OUTLINE (TODO: FINISH)
    We prove that A/~ is the supremum defined above by showing that
      Ord-to-𝕍 (A/~ᵒʳᵈ) ＝ 𝕍-set f.
    This boils down to proving
      (a : A) → f a ＝ Ord-to-𝕍 (A/~ ↓ [ a ]) (module size issues)
    which we "Yoneda-fy" in the following lemma (which needs renaming) so that
    it allows for a quick proof by ∈-induction.

\begin{code}

   key-lemma : (x : 𝕍) (a : A) → x ＝ f a ⇔ x ＝ Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ a ]⁻)
   key-lemma = {!!}

\end{code}
