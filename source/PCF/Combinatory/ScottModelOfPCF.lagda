Tom de Jong, 31 May 2019
Updated comments on 21 June 2022.
Added examples at the end on 22 December 2022.

The denotational semantics of PCF based on pointed directed complete posets.

The flag --lossy-unification significantly speeds up the
typechecking of the line ⟦ S {ρ} {σ} {τ} ⟧ₑ = Sᵈᶜᵖᵒ⊥ ⟦ ρ ⟧ ⟦ σ ⟧ ⟦ τ ⟧ below.
(https://agda.readthedocs.io/en/latest/language/lossy-unification.html)


We consider the combinatory version of PCF here. This development was extended
to PCF with variables and λ-abstraction by Brendan Hart in a final year project
supervised by Martín Escardó and myself. Notably, Brendan's extension contains
an Agda formalization of soundness and computational adequacy.

Brendan's code, using a previous version of our library, can be found
here: https://github.com/BrendanHart/Investigating-Properties-of-PCF.

Ported to TypeTopology by Martin Escardo in 17-18 May 2023.
https://martinescardo.github.io/TypeTopology/PCF.Lambda.index.html

Brendan's repository also contains his report describing the project:
https://github.com/BrendanHart/Investigating-Properties-of-PCF/blob/master/InvestigatingPropertiesOfPCFInAgda.pdf.


\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons

module PCF.Combinatory.ScottModelOfPCF
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import Naturals.Properties
open import UF.Base
open import UF.DiscreteAndSeparated

open import PCF.Combinatory.PCF pt
open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
open import DomainTheory.Basics.Exponential pt fe 𝓤₀
open import DomainTheory.Basics.LeastFixedPoint pt fe 𝓤₀
open import DomainTheory.Basics.Pointed pt fe 𝓤₀

open import PCF.Combinatory.PCFCombinators pt fe 𝓤₀
open IfZeroDenotationalSemantics pe

open import DomainTheory.Lifting.LiftingSet pt fe 𝓤₀ pe

open import Lifting.Construction 𝓤₀ renaming (⊥ to 𝓛⊥)
open import Lifting.Miscelanea 𝓤₀
open import Lifting.Miscelanea-PropExt-FunExt 𝓤₀ pe fe
open import Lifting.Monad 𝓤₀ hiding (μ)

⟦_⟧ : type → DCPO⊥ {𝓤₁} {𝓤₁}
⟦ ι ⟧     = 𝓛-DCPO⊥ ℕ-is-set
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ ⟹ᵈᶜᵖᵒ⊥ ⟦ τ ⟧

⟦_⟧ₑ : {σ : type} (t : PCF σ) → ⟪ ⟦ σ ⟧ ⟫
⟦ Zero ⟧ₑ            = η zero
⟦ Succ ⟧ₑ            = 𝓛̇ succ , 𝓛̇-continuous ℕ-is-set ℕ-is-set succ
⟦ Pred ⟧ₑ            = 𝓛̇ pred , 𝓛̇-continuous ℕ-is-set ℕ-is-set pred
⟦ ifZero ⟧ₑ          = ⦅ifZero⦆
⟦ Fix {σ} ⟧ₑ         = μ ⟦ σ ⟧
⟦ K {σ} {τ} ⟧ₑ       = Kᵈᶜᵖᵒ⊥ ⟦ σ ⟧ ⟦ τ ⟧
⟦ S {ρ} {σ} {τ} ⟧ₑ   = Sᵈᶜᵖᵒ⊥ ⟦ ρ ⟧ ⟦ σ ⟧ ⟦ τ ⟧
⟦ _·_ {σ} {τ} s t ⟧ₑ = [ ⟦ σ ⟧ ⁻ ,  ⟦ τ ⟧ ⁻ ]⟨ ⟦ s ⟧ₑ ⟩ ⟦ t ⟧ₑ

\end{code}

Because Agda is a computational system, we can use it to directly compute the
value of terms in the model. We showcase a few examples illustrating this, as
suggested by Andrej Bauer during my viva on 20 December 2022.

\begin{code}

private
 t₁ : PCF ι
 t₁ = ⌜ 7 ⌝

 recall-the-interpretation-of-ι : ⟪ ⟦ ι ⟧ ⟫ ＝ 𝓛 ℕ
 recall-the-interpretation-of-ι = refl

 ⟦t₁⟧-is-a-triple-representing-a-partial-element : ⟦ t₁ ⟧ₑ
                                                 ＝ 𝟙 , (λ _ → 7) , 𝟙-is-prop
 ⟦t₁⟧-is-a-triple-representing-a-partial-element = refl

 compute-the-value-of-⟦t₁⟧ : value ⟦ t₁ ⟧ₑ ⋆ ＝ 7
 compute-the-value-of-⟦t₁⟧ = refl


 t₂ : PCF ι
 t₂ = Pred · (Pred · (Succ · ⌜ 3 ⌝))

 ⟦t₂⟧-is-a-triple-representing-a-partial-element : ⟦ t₂ ⟧ₑ
                                                 ＝ 𝟙 , (λ _ → 2) , 𝟙-is-prop
 ⟦t₂⟧-is-a-triple-representing-a-partial-element = refl

\end{code}

We let Agda compute the witness (indicated by _) that ⟦ t₂ ⟧ₑ is total.

\begin{code}

 compute-the-value-of-⟦t₂⟧ : value ⟦ t₂ ⟧ₑ _ ＝ 2
 compute-the-value-of-⟦t₂⟧ = refl

\end{code}

By computational adequacy (see the comments at the top of this file) and the
computation above, the term t₂ reduces to the numeral ⌜ 2 ⌝ in PCF.

The term t₃ encodes the program [λ x . (if (0 == x) then 2 else (pred 5)) 3].
Notice how the extent of the partial element is no longer given by 𝟙 but, as a
consequence of the constructions in our model, by the product 𝟙 × 𝟙.

We let Agda compute the witness (indicated by _) that the type 𝟙 × 𝟙 is a
proposition.

\begin{code}

 t₃ : PCF ι
 t₃ = ifZero · ⌜ 2 ⌝ · (Pred · ⌜ 5 ⌝) · ⌜ 3 ⌝

 ⟦t₃⟧-is-a-triple-representing-a-partial-element : ⟦ t₃ ⟧ₑ
                                                 ＝ (𝟙 × 𝟙) , (λ _ → 4) , _
 ⟦t₃⟧-is-a-triple-representing-a-partial-element = refl

 compute-the-value-of-⟦t₃⟧ : value ⟦ t₃ ⟧ₑ _ ＝ 4
 compute-the-value-of-⟦t₃⟧ = refl

\end{code}

Next we show two examples using the S and K combinators. We first construct the
identity function I on an arbitrary type σ of PCF using the well-known
definition I = S · K · K.

\begin{code}

 I : {σ : type} → PCF (σ ⇒ σ)
 I {σ} = (S {σ} {σ ⇒ σ} {σ}) · K · K

 t₄ : PCF ι
 t₄ = I · ⌜ 7 ⌝

 compute-the-value-of-⟦t₄⟧ : value ⟦ t₄ ⟧ₑ _ ＝ 7
 compute-the-value-of-⟦t₄⟧ = refl

 t₅ : PCF ι
 t₅ = (I · Succ) · ⌜ 11 ⌝

 compute-the-value-of-⟦t₅⟧ : value ⟦ t₅ ⟧ₑ _ ＝ 12
 compute-the-value-of-⟦t₅⟧ = refl

\end{code}

Finally, here are two examples that use the Fix combinator. We explain why we
can't quite compute results in these examples.
Note that this has been updated on 3 March 2026 by Tom de Jong. I am grateful to
Cass Alexandru for questions that led to these updates.

\begin{code}

 t₆ : PCF ι
 t₆ = Fix · (K · ⌜ 0 ⌝)

\end{code}

Recall that least fixed points are constructed by iterating an endomap and
starting with ⊥. In the general case of a 𝓥-dcpo we need to lift the type of
natural numbers to a copy in 𝓥, which is why we have the type ℕ' below. Of
course, since we are dealing with 𝓤₀-dcpos this lifing is unnecessary here, but
it is a consequence of applying the more general constructions.

\begin{code}

 open import UF.UniverseEmbedding
 ℕ' : 𝓤₀ ̇
 ℕ' = Lift 𝓤₀ ℕ
 _′ : ℕ' → ℕ
 _′ = lower
 ′_ : ℕ → ℕ'
 ′_ = lift 𝓤₀

 t₆-note₁ : is-defined ⟦ t₆ ⟧ₑ
            ＝ (∃ n ꞉ ℕ' , is-defined (iter ⟦ ι ⟧ (n ′) ⟦ K · ⌜ 0 ⌝ ⟧ₑ))
 t₆-note₁ = refl

 t₆-note₂ : (n : ℕ') → iter ⟦ ι ⟧ (succ (n ′)) ⟦ K · ⌜ 0 ⌝ ⟧ₑ ＝ η 0
 t₆-note₂ _ = refl

 t₆-is-defined : is-defined ⟦ t₆ ⟧ₑ
 t₆-is-defined = ∣ ′ 1 , ⋆ ∣

\end{code}

The below computation does not work, because extracting the value employs the
fact that we can factor a certain map through the proposition truncation and the
truncation is assumed axiomatically in our development. I would expect it to
work in Cubical Agda though.

 compute-the-value-of-⟦t₆⟧ : value ⟦ t₆ ⟧ₑ t₆-is-defined ＝ 0
 compute-the-value-of-⟦t₆⟧ = refl

But it is provable of course:

\begin{code}

 value-of-⟦t₆⟧ₑ : value ⟦ t₆ ⟧ₑ t₆-is-defined ＝ 0
 value-of-⟦t₆⟧ₑ = ＝-of-values-from-＝ (eq ⁻¹)
  where
   eq : η 0 ＝ ⟦ t₆ ⟧ₑ
   eq = family-defined-somewhere-sup-＝ ℕ-is-set _ (′ 1) ⋆

\end{code}

The interpretation of t₇ is equal to ⊥, because it is the least fixed point of
the identity on ⟦ ι ⟧, but the issue is that iter is defined by pattern
matching, so while each application iter n is equal to 𝟘, we cannot
definitionally replace it by 𝟘.

\begin{code}

 t₇ : PCF ι
 t₇ = Fix · (I {ι})

 t₇-note₁ : is-defined ⟦ t₇ ⟧ₑ
            ＝ (∃ n ꞉ ℕ' , is-defined (iter ⟦ ι ⟧ (n ′) ⟦ I ⟧ₑ))
 t₇-note₁ = refl

 t₇-note₂ : (n : ℕ) → is-defined (iter ⟦ ι ⟧ n ⟦ I ⟧ₑ) ＝ 𝟘
 t₇-note₂ zero     = refl
 t₇-note₂ (succ n) = t₇-note₂ n

 t₇-note₃ : (n : ℕ') → is-defined (iter ⟦ ι ⟧ (n ′) ⟦ I ⟧ₑ) ＝ 𝟘
 t₇-note₃ n = t₇-note₂ (n ′)

\end{code}

But the following fails:
 t₇-note₄ : (n : ℕ') → is-defined (iter ⟦ ι ⟧ (n ′) ⟦ I ⟧ₑ) ＝ 𝟘
 t₇-note₄ n = refl

Therefore we cannot simply compute is-defined ⟦ t₇ ⟧ₑ to be (Σ n ꞉ ℕ' , 𝟘),
i.e. ℕ' × 𝟘, which is equivalent to 𝟘 of course.

\begin{code}

 ⟦t₇⟧-is-not-defined : ¬ (is-defined ⟦ t₇ ⟧ₑ)
 ⟦t₇⟧-is-not-defined = ∥∥-rec 𝟘-is-prop h
  where
   h : (Σ n ꞉ ℕ' , is-defined (iter ⟦ ι ⟧ (n ′) ⟦ I ⟧ₑ)) → 𝟘
   h (n , d) = Idtofun (t₇-note₃ n) d

 ⟦t₇⟧-is-⊥ : ⟦ t₇ ⟧ₑ ＝ 𝓛⊥
 ⟦t₇⟧-is-⊥ = not-defined-⊥-＝ ⟦t₇⟧-is-not-defined

\end{code}
