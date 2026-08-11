Martin Escardo, Added 21st April 2022.

Limit ordinals and suprema of families of ordinals.

(Moved from another file to this new file 15th October 2024.)

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.Limit
       (ua : Univalence)
       where

open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.PropTrunc
open import UF.Size

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

open import MLTT.Spartan
open import Notation.CanonicalMap
open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.ConvergentSequence ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Type
open import Ordinals.Underlying

\end{code}

One possible classical definition of limit ordinal.

\begin{code}

is-limit-ordinal⁺ : Ordinal 𝓤 → 𝓤 ⁺ ̇
is-limit-ordinal⁺ {𝓤} α = (β : Ordinal 𝓤)
                         → ((γ : Ordinal 𝓤) → γ ⊲ α → γ ⊴ β)
                         → α ⊴ β
\end{code}

We give an equivalent definition below.

Recall from the modules Quotient.FromSetReplacement and
Quotient.GivesSetReplacement that the existence propositional
truncations and the set-replacement property are together equivalent
to the existence of small quotients. With them we can construct
suprema of families of ordinals.

\begin{code}

module _ (pt : propositional-truncations-exist)
         (sr : Set-Replacement pt)
       where

 open suprema pt sr

\end{code}

Recall that, by definition, γ ⊲ α iff γ is of the form α ↓ x for some
x : ⟨ α ⟩. We define the "floor" of an ordinal to be the supremum of
its predecessors:

\begin{code}

 ⌊_⌋ : Ordinal 𝓤 → Ordinal 𝓤
 ⌊ α ⌋ = sup (α ↓_)

 ⌊⌋-lower-bound : (α : Ordinal 𝓤) → ⌊ α ⌋ ⊴ α
 ⌊⌋-lower-bound α = sup-is-lower-bound-of-upper-bounds _ α (segment-⊴ α)

 is-limit-ordinal : Ordinal 𝓤 → 𝓤 ̇
 is-limit-ordinal α = α ⊴ ⌊ α ⌋

 is-limit-ordinal-fact : (α : Ordinal 𝓤)
                       → is-limit-ordinal α
                       ↔ α ＝ ⌊ α ⌋
 is-limit-ordinal-fact α = (λ ℓ → ⊴-antisym _ _ ℓ (⌊⌋-lower-bound α)) ,
                           (λ p → transport (α ⊴_) p (⊴-refl α))

 ⌊⌋-of-successor : (α : Ordinal 𝓤)
                 → ⌊ α +ₒ 𝟙ₒ ⌋ ⊴ α
 ⌊⌋-of-successor α = sup-is-lower-bound-of-upper-bounds _ α h
  where
   h : (x : ⟨ α +ₒ 𝟙ₒ ⟩) → ((α +ₒ 𝟙ₒ) ↓ x) ⊴ α
   h (inl x) = successor-lemma-left α x
   h (inr ⋆) = transport⁻¹ (_⊴ α) (successor-lemma-right α) (⊴-refl α)

 ⌊⌋-of-successor' : (α : Ordinal 𝓤)
                  → ⌊ α +ₒ 𝟙ₒ ⌋ ＝ α
 ⌊⌋-of-successor' α = III
  where
   I : ((α +ₒ 𝟙ₒ) ↓ inr ⋆) ⊴ ⌊ α +ₒ 𝟙ₒ ⌋
   I = sup-is-upper-bound _ (inr ⋆)

   II : α ⊴ ⌊ α +ₒ 𝟙ₒ ⌋
   II = transport (_⊴ ⌊ α +ₒ 𝟙ₒ ⌋) (successor-lemma-right α) I

   III : ⌊ α +ₒ 𝟙ₒ ⌋ ＝ α
   III = ⊴-antisym _ _ (⌊⌋-of-successor α) II

 successors-are-not-limit-ordinals : (α : Ordinal 𝓤)
                                   → ¬ is-limit-ordinal (α +ₒ 𝟙ₒ)
 successors-are-not-limit-ordinals α le = irrefl (OO _) α II
  where
   I : (α +ₒ 𝟙ₒ) ⊴ α
   I = ⊴-trans (α +ₒ 𝟙ₒ) ⌊ α +ₒ 𝟙ₒ ⌋ α le (⌊⌋-of-successor α)

   II : α ⊲ α
   II = ⊴-gives-≼ _ _ I α (successor-increasing α)

\end{code}

TODO (easy). Show that is-limit-ordinal⁺ α is logically equivalent to
is-limit-ordinal α.

\begin{code}

 ⌊⌋-monotone : (α β : Ordinal 𝓤) → α ⊴ β → ⌊ α ⌋ ⊴ ⌊ β ⌋
 ⌊⌋-monotone α β le = V
  where
   I : (y : ⟨ β ⟩) → (β ↓ y) ⊴ ⌊ β ⌋
   I = sup-is-upper-bound (β ↓_)

   II : (x : ⟨ α ⟩) → (α ↓ x) ⊲ β
   II x = ⊴-gives-≼ _ _ le (α ↓ x) (x , refl)

   III : (x : ⟨ α ⟩) → Σ y ꞉ ⟨ β ⟩ , (α ↓ x) ＝ (β ↓ y)
   III = II

   IV : (x : ⟨ α ⟩) → (α ↓ x) ⊴ ⌊ β ⌋
   IV x = transport⁻¹ (_⊴ ⌊ β ⌋) (pr₂ (III x)) (I (pr₁ (III x)))

   V : sup (α ↓_) ⊴ ⌊ β ⌋
   V = sup-is-lower-bound-of-upper-bounds (α ↓_) ⌊ β ⌋ IV

\end{code}

We now give an example of an ordinal which is not a limit ordinal and
also is not a successor ordinal unless LPO holds:

\begin{code}

 open import CoNaturals.Type
 open import Notation.Order
 open import Naturals.Order

 ⌊⌋-of-ℕ∞ : ⌊ ℕ∞ₒ ⌋ ＝ ω
 ⌊⌋-of-ℕ∞ = c
  where
   a : ⌊ ℕ∞ₒ ⌋ ⊴ ω
   a = sup-is-lower-bound-of-upper-bounds (ℕ∞ₒ ↓_) ω I
    where
     I : (u : ⟨ ℕ∞ₒ ⟩) → (ℕ∞ₒ ↓ u) ⊴ ω
     I u = ≼-gives-⊴ (ℕ∞ₒ ↓ u) ω II
      where
       II : (α : Ordinal 𝓤₀) → α ⊲ (ℕ∞ₒ ↓ u) → α ⊲ ω
       II .((ℕ∞ₒ ↓ u) ↓ (ι n , n , refl , p)) ((.(ι n) , n , refl , p) , refl) =
        XI
        where
         III : ι n ≺ u
         III = n , refl , p

         IV : ((ℕ∞ₒ ↓ u) ↓ (ι n , n , refl , p)) ＝ ℕ∞ₒ ↓ ι n
         IV = iterated-↓ ℕ∞ₒ u (ι n) III

         V : (ℕ∞ₒ ↓ ι n) ≃ₒ (ω ↓ n)
         V = f , fop , qinvs-are-equivs f (g , gf , fg) , gop
          where
           f : ⟨ ℕ∞ₒ ↓ ι n ⟩ → ⟨ ω ↓ n ⟩
           f (.(ι k) , k , refl , q) = k , ⊏-gives-< _ _ q

           g : ⟨ ω ↓ n ⟩ → ⟨ ℕ∞ₒ ↓ ι n ⟩
           g (k , l) = (ι k , k , refl , <-gives-⊏ _ _ l)

           fg : f ∘ g ∼ id
           fg (k , l) = to-subtype-＝ (λ k → <-is-prop-valued k n) refl

           gf : g ∘ f ∼ id
           gf (.(ι k) , k , refl , q) = to-subtype-＝
                                         (λ u → ≺-prop-valued fe' u (ι n))
                                         refl

           fop : is-order-preserving (ℕ∞ₒ ↓ ι n) (ω ↓ n) f
           fop (.(ι k) , k , refl , q) (.(ι k') , k' , refl , q') (m , r , cc) =
            VIII
            where
             VI : k ＝ m
             VI = ℕ-to-ℕ∞-lc r

             VII : m < k'
             VII = ⊏-gives-< _ _ cc

             VIII : k < k'
             VIII = transport⁻¹ (_< k') VI VII

           gop : is-order-preserving (ω ↓ n) (ℕ∞ₒ ↓ ι n)  g
           gop (k , l) (k' , l') ℓ = k , refl , <-gives-⊏ _ _ ℓ

         IX : ℕ∞ₒ ↓ ι n ＝ ω ↓ n
         IX = eqtoidₒ (ua 𝓤₀) fe' _ _ V

         X : (ℕ∞ₒ ↓ (ι n)) ⊲ ω
         X = n , IX

         XI : ((ℕ∞ₒ ↓ u) ↓ (ι n , n , refl , p)) ⊲ ω
         XI = transport⁻¹ (_⊲ ω) IV X

   b : ω ⊴ ⌊ ℕ∞ₒ ⌋
   b = transport (_⊴ ⌊ ℕ∞ₒ ⌋) (⌊⌋-of-successor' ω) I
    where
     I : ⌊ ω +ₒ 𝟙ₒ ⌋ ⊴ ⌊ ℕ∞ₒ ⌋
     I = ⌊⌋-monotone (ω +ₒ 𝟙ₒ) ℕ∞ₒ ω+𝟙-is-⊴-ℕ∞

   c : ⌊ ℕ∞ₒ ⌋ ＝ ω
   c = ⊴-antisym _ _ a b

 ℕ∞-is-not-limit : ¬ is-limit-ordinal ℕ∞ₒ
 ℕ∞-is-not-limit ℓ = III II
  where
   I = ℕ∞ₒ     ＝⟨ lr-implication (is-limit-ordinal-fact ℕ∞ₒ) ℓ ⟩
       ⌊ ℕ∞ₒ ⌋ ＝⟨ ⌊⌋-of-ℕ∞  ⟩
       ω       ∎

   II : ℕ∞ₒ ≃ₒ ω
   II = idtoeqₒ _ _ I

   III : ¬ (ℕ∞ₒ ≃ₒ ω)
   III (f , e) = irrefl ω (f ∞) VII
    where
     IV : is-largest ω (f ∞)
     IV = order-equivs-preserve-largest ℕ∞ₒ ω f e ∞
           (λ u t l → ≺≼-gives-≺ t u ∞ l (∞-largest u))

     V : f ∞ ≺⟨ ω ⟩ succ (f ∞)
     V = <-succ (f ∞)

     VI : succ (f ∞) ≼⟨ ω ⟩ f ∞
     VI = IV (succ (f ∞))

     VII : f ∞ ≺⟨ ω ⟩ f ∞
     VII = VI (f ∞) V

 open import Taboos.LPO

 ℕ∞-successor-gives-LPO : (Σ α ꞉ Ordinal 𝓤₀ , (ℕ∞ₒ ＝ (α +ₒ 𝟙ₒ))) → LPO
 ℕ∞-successor-gives-LPO (α , p) = IV
  where
   I = α           ＝⟨ (⌊⌋-of-successor' α)⁻¹ ⟩
       ⌊ α +ₒ 𝟙ₒ ⌋ ＝⟨ ap ⌊_⌋ (p ⁻¹) ⟩
       ⌊ ℕ∞ₒ ⌋     ＝⟨ ⌊⌋-of-ℕ∞ ⟩
       ω           ∎

   II : ℕ∞ₒ ＝ (ω +ₒ 𝟙ₒ)
   II = transport (λ - → ℕ∞ₒ ＝ (- +ₒ 𝟙ₒ)) I p

   III : ℕ∞ₒ ⊴ (ω +ₒ 𝟙ₒ)
   III = transport (ℕ∞ₒ ⊴_) II (⊴-refl ℕ∞ₒ)

   IV : LPO
   IV = ℕ∞-⊴-ω+𝟙-gives-LPO III

 open PropositionalTruncation pt

 ℕ∞-successor-gives-LPO' : (∃ α ꞉ Ordinal 𝓤₀ , (ℕ∞ₒ ＝ (α +ₒ 𝟙ₒ))) → LPO
 ℕ∞-successor-gives-LPO' = ∥∥-rec (LPO-is-prop fe') ℕ∞-successor-gives-LPO

 LPO-gives-ℕ∞-successor : LPO → (Σ α ꞉ Ordinal 𝓤₀ , (ℕ∞ₒ ＝ (α +ₒ 𝟙ₒ)))
 LPO-gives-ℕ∞-successor lpo = ω , ℕ∞-is-successor₃ lpo

\end{code}

Therefore, constructively, it is not necessarily the case that every
ordinal is either a successor or a limit.

TODO (1st June 2023). A classically equivalently definition of limit
ordinal α is that there is some β < α, and for every β < α there is γ
with β < γ < α. We have that ℕ∞ is a limit ordinal in this sense.
