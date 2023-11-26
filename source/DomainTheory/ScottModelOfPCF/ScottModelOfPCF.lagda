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

module DomainTheory.ScottModelOfPCF.ScottModelOfPCF
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where


open import PCF.Combinatory.ScottModelOfPCF pt fe pe public

\end{code}
