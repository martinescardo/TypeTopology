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

The repository also contains Brendan's report describing the project:
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
open import UF.DiscreteAndSeparated

open import PCF.Combinatory.PCF pt
open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
open import DomainTheory.Basics.Exponential pt fe 𝓤₀
open import DomainTheory.Basics.LeastFixedPoint pt fe
open import DomainTheory.Basics.Miscelanea pt fe 𝓤₀
open import DomainTheory.Basics.Pointed pt fe 𝓤₀

open import PCF.Combinatory.PCFCombinators pt fe 𝓤₀
open IfZeroDenotationalSemantics pe

open import DomainTheory.Lifting.LiftingSet pt fe 𝓤₀ pe

open import Lifting.Lifting 𝓤₀
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

  -- We let Agda compute the witness (indicated by _) that ⟦ t₂ ⟧ₑ is total.
 compute-the-value-of-⟦t₂⟧ : value ⟦ t₂ ⟧ₑ _ ＝ 2
 compute-the-value-of-⟦t₂⟧ = refl

\end{code}

By computational adequacy (see the comments at the top of this file) and the
computation above, the term t₂ reduces to the numeral ⌜ 2 ⌝ in PCF.

\begin{code}

 -- t₃ encodes the program [λ x . (if (0 == x) then 2 else (pred 5)) 3]
 t₃ : PCF ι
 t₃ = ifZero · ⌜ 2 ⌝ · (Pred · ⌜ 5 ⌝) · ⌜ 3 ⌝

 -- Notice how the extent of the partial element is no longer given by 𝟙 but, as
 -- a consequence of the constructions in our model, by the product 𝟙 × 𝟙.
 --
 -- We let Agda compute the witness (indicated by _) that the type 𝟙 × 𝟙 is a
 -- proposition.
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

Finally, here are two examples that use the Fix combinator where Agda cannot
normalise the term within reasonable time, which is why these lines are
commented out.

\begin{code}
 t₆ : PCF ι
 t₆ = Fix · (K · ⌜ 0 ⌝)

 -- The value of ⟦ t₆ ⟧ is 0, but the computation takes an unreasonable amount
 -- of time.
 --
 -- compute-the-value-of-⟦t₆⟧ : value ⟦ t₆ ⟧ₑ _ = 0
 -- compute-the-value-of-⟦t₆⟧ = refl

 t₇ : PCF ι
 t₇ = Fix · (I {ι})

 -- The interpretation of t₇ is equal to ⊥, because it is the least fixed point
 -- of the identity on ⟦ ι ⟧, but Agda cannot normalise (is-defined (⟦ t₇ ⟧ₑ) in
 -- reasonable time.
 --
 -- ⟦t₇⟧-is-not-defined : ¬ (is-defined ⟦ t₇ ⟧ₑ)
 -- ⟦t₇⟧-is-not-defined = {!!}

\end{code}
