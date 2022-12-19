Martin Escardo, 17th December 2022.

Proof that in HoTT/UF the axiom of choice implies that every set can
be well-ordered, written in Agda.

This is not a new result. The HoTT book from 2013 already has a proof,
and perhaps it has already been formalized in Coq. What I did was to
stare at various proofs in set theory, and then adapt the one I
liked most to HoTT/UF.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan
open import NotionsOfDecidability.Decidable
open import Ordinals.Arithmetic
open import Ordinals.Notions
open import Ordinals.Type
open import UF.Base
open import UF.Choice
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.Logic
open import UF.Powerset
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Univalence

\end{code}

We work in a Spartan Martin-Löf type theory and assume that the
univalence axiom holds and that propositional truncations exist:

\begin{code}

module Ordinals.WellOrderingPrinciple
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.BuraliForti ua

\end{code}

We then derive function extensionality and propositional
extensionality from univalence:

\begin{code}

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

 pe' : PropExt
 pe' 𝓤 = pe {𝓤}

open PropositionalTruncation pt
open UF.Choice.EM-and-choice-functions pt pe' fe

\end{code}

We now state the main theorem of this file, where the axiom of choice
is formulated as in the HoTT book.

\begin{code}

Choice-gives-well-ordering : Choice
                           → {X : 𝓤 ̇ }
                           → is-set X
                           → ∃ _<_ ꞉ (X → X → 𝓤 ̇) , (is-well-order _<_)
\end{code}

This is proved at the very end of this file. We first prove that,
under excluded middle, if a set has a given choice function, then it
can be equipped with a well ordering. Later we will derive excluded
middle from choice in order to apply this to prove the main theorem.

\begin{code}

open import Ordinals.WellOrderTransport fe
open import UF.ImageAndSurjection pt

open UF.Powerset.inhabited-subsets pt
open UF.Logic.AllCombinators pt fe'

choice-function-gives-well-ordering :

        Excluded-Middle
      → {X : 𝓤 ̇ }
      → is-set X
      → (Σ ε ꞉ (𝓟 X → X) , ((A : 𝓟 X) → is-inhabited A → ε A ∈ A))
      → Σ _<_ ꞉ (X → X → 𝓤 ̇) , (is-well-order _<_)

choice-function-gives-well-ordering {𝓤} em {X} X-is-set (ε , ε-behaviour) = W
 where

\end{code}

We first define a function f : Ordinal 𝓤 → X by transfinite recursion
as follows:

\begin{code}

   ϕ : (α : Ordinal 𝓤) → (⟨ α ⟩ → X) → X
   ϕ α s = ε ⁅ x ꞉ X ∣ Ɐ a ∶ ⟨ α ⟩ , s a ≢ x ⁆

   f : Ordinal 𝓤 → X
   f = transfinite-recursion-on-OO X ϕ

\end{code}

For an ordinal α and a point a in the underlying set ⟨ α ⟩ of α, we
denote by α ↓ a the down set of a in α. This is an ordinal on its own,
and, by univalence, every ordinal β ≺ α is of the form α ↓ a. Using
this construction, we define a subset A α of X for each ordinal α, and
with this we can specify the recursive behaviour of f as follows:

\begin{code}

   A : Ordinal 𝓤 → 𝓟 X
   A α = ⁅ x ꞉ X ∣ Ɐ a ∶ ⟨ α ⟩ , f (α ↓ a) ≢ x ⁆

   f-behaviour : (α : Ordinal 𝓤) → f α ＝ ε (A α)
   f-behaviour = transfinite-recursion-on-OO-behaviour X ϕ

\end{code}

The following properties of f should be self-explanatory:

\begin{code}

   f-lemma : (α : Ordinal 𝓤) → is-inhabited (A α) → (β : Ordinal 𝓤) → β ⊲ α → f α ≠ f β
   f-lemma α i β (a , refl) p = III
    where
     I = ε (A α)   ＝⟨ (f-behaviour α)⁻¹ ⟩
         f α       ＝⟨ p ⟩
         f (α ↓ a) ∎


     II : f (α ↓ a) ∈ A α
     II = transport (_∈ A α) I (ε-behaviour (A α) i)

     III : 𝟘
     III = II a refl

   f-is-conditionally-1-1 : (α β : Ordinal 𝓤)
                          → is-inhabited (A α)
                          → is-inhabited (A β)
                          → α ≠ β
                          → f α ≠ f β
   f-is-conditionally-1-1 α β i j ν = I (trichotomy _⊲_ fe' em ⊲-is-well-order α β)
    where
     I : (α ⊲ β) + (α ＝ β) + (β ⊲ α) → f α ≠ f β
     I (inl l)       = ≠-sym (f-lemma β j α l)
     I (inr (inl p)) = 𝟘-elim (ν p)
     I (inr (inr m)) = f-lemma α i β m

   f-is-conditionally-lc : (α β : Ordinal 𝓤)
                         → is-inhabited (A α)
                         → is-inhabited (A β)
                         → f α ＝ f β
                         → α ＝ β
   f-is-conditionally-lc α β i j p =
     ¬¬-elim
       (em (α ＝ β)
           (extensionally-ordered-types-are-sets _⊲_ fe
             ⊲-is-prop-valued ⊲-is-extensional))
           (λ (ν : α ≠ β) → f-is-conditionally-1-1 α β i j ν p)

\end{code}

A crucial property of the family A α of subsets of X is that it is
eventually empty. We first prove that it is somewhere empty by
contradiction, using the fact that the type of ordinals is large (by
the Burali-Forti argument). We need to use propositional resizing for
this purpose, which follows from excluded middle, which we are
assuming.

\begin{code}

   A-is-somewhere-empty : ∃ α ꞉ Ordinal 𝓤 , is-empty-subset (A α)
   A-is-somewhere-empty = III
    where
     I : ¬ ((α : Ordinal 𝓤) → is-inhabited (A α))
     I ϕ = absurd
      where
       f-lc : left-cancellable f
       f-lc {α} {β} = f-is-conditionally-lc α β (ϕ α) (ϕ β)

       f-is-embedding : is-embedding f
       f-is-embedding = lc-maps-into-sets-are-embeddings f f-lc X-is-set

       X' : 𝓤 ⁺ ̇
       X' = image f

       f' : Ordinal 𝓤 → X'
       f' = corestriction f

       f'-is-equiv : is-equiv f'
       f'-is-equiv = corestriction-of-embedding-is-equivalence f f-is-embedding

       B : X → 𝓤 ⁺ ̇
       B x = x ∈image f

       B-is-prop : (x : X) → is-prop (B x)
       B-is-prop x = being-in-the-image-is-prop x f

       ρ : Propositional-Resizing
       ρ = EM-gives-PR em

       C : X → 𝓤 ̇
       C x = resize ρ (B x) (B-is-prop x)

       τ : Nat C B
       τ x = from-resize ρ (B x) (B-is-prop x)

       τ-is-equiv : (x : X) → is-equiv (τ x)
       τ-is-equiv x = from-resize-is-equiv ρ (B x) (B-is-prop x)

       X'' : 𝓤 ̇
       X'' = Σ x ꞉ X , C x

       e = X''       ≃⟨ NatΣ τ , NatΣ-equiv C B τ τ-is-equiv ⟩
           X'        ≃⟨ ≃-sym (f' , f'-is-equiv) ⟩
           Ordinal 𝓤 ■

       the-type-of-ordinals-is-small : is-small (Ordinal 𝓤)
       the-type-of-ordinals-is-small = X'' , e

       absurd : 𝟘
       absurd = the-type-of-ordinals-is-large the-type-of-ordinals-is-small

     II : ∃ α ꞉ Ordinal 𝓤 , ¬ is-inhabited (A α)
     II = not-Π-implies-∃-not pt em (λ x → being-inhabited-is-prop (A x)) I

     III : ∃ α ꞉ Ordinal 𝓤 , is-empty-subset (A α)
     III = Nat∃ (λ α → non-inhabited-subsets-are-empty (A α)) II

\end{code}

It follows from the above and excluded middle that there is a least
such α, which we will call α₀:

\begin{code}

   A-is-eventually-empty : Σ α₀ ꞉ Ordinal 𝓤
                                , is-empty-subset (A α₀)
                                × ((α : Ordinal 𝓤) → is-empty-subset (A α) → α₀ ≼ α)
   A-is-eventually-empty = nonempty-has-minimal _⊲_ fe' em pt ⊲-is-well-order _
                            (λ α → being-empty-subset-is-prop fe' (A α))
                            A-is-somewhere-empty

   α₀ : Ordinal 𝓤
   e₀ : is-empty-subset (A α₀)
   m₀ : (α : Ordinal 𝓤) → is-empty-subset (A α) → α₀ ≼ α

   α₀ = pr₁ A-is-eventually-empty
   e₀ = pr₁ (pr₂ A-is-eventually-empty)
   m₀ = pr₂ (pr₂ A-is-eventually-empty)

   n₀ : (α : Ordinal 𝓤) → α ⊲ α₀ → is-inhabited (A α)
   n₀ α l = non-empty-subsets-are-inhabited em
             (A α)
             (contrapositive (m₀ α) (λ (m : α₀ ≼ α) → irrefl (OO 𝓤) α (m α l)))

\end{code}

We now restrict f to α₀ as follows, and show that the resulting map is
a surjection and an injection, and hence an equivalence, and we use
this to transport the well-ordering of α₀ to X to establish the
desired result:

\begin{code}

   f₀ : ⟨ α₀ ⟩ → X
   f₀ a = f (α₀ ↓ a)

   f₀-is-surjection : is-surjection f₀
   f₀-is-surjection x = not-Π-not-implies-∃ pt em (e₀ x)

   f₀-lc : left-cancellable f₀
   f₀-lc {a} {b} p = II
    where
     Ia : is-inhabited (A (α₀ ↓ a))
     Ia = n₀ (α₀ ↓ a) (a , refl)

     Ib : is-inhabited (A (α₀ ↓ b))
     Ib = n₀ (α₀ ↓ b) (b , refl)

     I : (α₀ ↓ a) ＝ (α₀ ↓ b)
     I = f-is-conditionally-lc (α₀ ↓ a) (α₀ ↓ b) Ia Ib p

     II : a ＝ b
     II = ↓-lc α₀ a b I

   f₀-is-embedding : is-embedding f₀
   f₀-is-embedding = lc-maps-into-sets-are-embeddings f₀ f₀-lc X-is-set

   f₀-is-equiv : is-equiv f₀
   f₀-is-equiv = surjective-embeddings-are-equivs f₀ f₀-is-embedding f₀-is-surjection

   structure-equiv : OrdinalStructure ⟨ α₀ ⟩ ≃ OrdinalStructure X
   structure-equiv = transport-ordinal-structure (ua 𝓤) ⟨ α₀ ⟩ X (f₀ , f₀-is-equiv)

\end{code}

And our desired results follows directly from this:

\begin{code}

   W : Σ _<_ ꞉ (X → X → 𝓤 ̇) , (is-well-order _<_)
   W = ⌜ structure-equiv ⌝ (structure α₀)

\end{code}

Using this we can prove the theorem stated above, and restated below,
as follows. We first obtain a choice function conditionally to the
inhabitedness of X from the axiom of choice, and also the principle of
excluded middle. We then use excluded middle to check whether X is
inhabited. If it is, we apply the above lemma. Otherwise it is empty
and hence clearly well-ordered.

\begin{code}

Choice-gives-well-ordering = restatement
 where
  restatement : Choice
              → {X : 𝓤 ̇ }
              → is-set X
              → ∃ _<_ ꞉ (X → X → 𝓤 ̇) , (is-well-order _<_)
  restatement {𝓤} ac {X} X-is-set = III
   where
    choice-function : ∥ X ∥ → ∃ ε ꞉ (𝓟 X → X) , ((A : 𝓟 X) → is-inhabited A → ε A ∈ A)
    choice-function = Choice-gives-Choice₄ ac X X-is-set

    em : Excluded-Middle
    em = Choice-gives-Excluded-Middle ac

    I : ∥ X ∥ → ∃ _<_ ꞉ (X → X → 𝓤 ̇) , (is-well-order _<_)
    I s = ∥∥-functor
            (choice-function-gives-well-ordering em X-is-set)
            (choice-function s)

    II : ¬ ∥ X ∥ → ∃ _<_ ꞉ (X → X → 𝓤 ̇) , (is-well-order _<_)
    II ν = ∣ structure (prop-ordinal fe X (empty-types-are-props (ν ∘ ∣_∣))) ∣

    III : ∃ _<_ ꞉ (X → X → 𝓤 ̇) , (is-well-order _<_)
    III = cases I II (em ∥ X ∥ ∥∥-is-prop)

\end{code}
