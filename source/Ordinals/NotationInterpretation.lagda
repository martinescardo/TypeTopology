Martin Escardo, 2012, 2018, 2022, 2026.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Ordinals.NotationInterpretation where

import Ordinals.BrouwerCodesInterpretations            -- 2022
import Ordinals.FailureOfTrichotomy                    -- 2026
import Ordinals.FailureOfTotalSeparatedness            -- 2026
import Ordinals.BrouwerCodesVariationInterpretations   -- 2018
import Ordinals.InductiveRecursiveCodesInterpretations -- 2022

\end{code}

  1. The file BrouwerCodesInterpretations interprets Brouwer
     ordinal codes, inductively defined by constructors

       Z : B,
       S : B → B,
       L : (ℕ → B) → B,

     in four ways,

       ⟦_⟧₀ : B → Ordinal 𝓤₀   (standard interpretation, with L = sup)
       ⟦_⟧₁ : B → Ordinalᵀ 𝓤₀  (compact∙ totally separated interpretation)
       ⟦_⟧₂ : B → Ordinal 𝓤₀   (compact interpretation)
       ⟦_⟧₃ : B → Ordinal₃ 𝓤₀  (trichotomous interpretation),

     which are also related to each other.


  2. FailureOfTrichotomy shows that if ⟦_⟧₀ gives trichotomous
     ordinals then LPO holds. It is evident that if it gives compact
     ordinals then LPO holds, because the interpretation of the code
     Brouwer code L (n ↦ Sⁿ Z) gives ω with underlying set ℕ, which is
     compact iff and only if LPO holds.

  3. FailureOfTotalSeparatedness shows that if ⟦_⟧₂ gives totally
     separated types then ¬¬ WLPO holds, and also gives positive
     information that is interesting in its own right.

  4. BrouwerCodesVariationInterpretations gives a mild generalization
     of Brouwer codes and interpretations corresponding to ⟦_⟧₁ and
     ⟦_⟧₃ and further connects the two interpretations with an
     embeddings of the former into the latter which has empty
     complement, and gives further information.

  5. InductiveRecursiveCodesInterpretations again generalizes Brouwer
     codes, by allowing ℕ in the constructor L to be replaced by
     ordinal codes defined in previous stages, again giving versions
     of ⟦_⟧₁ and ⟦_⟧₃ with a map from the latter to the
     former. Additionally, it describes which elements of the
     interpretation ⟦_⟧₁ are isolated points or limit points, by a
     boolean valued function.

See also the MFPS'2026 talk slides

  An inductive-recursive universe of searchable ordinals
  https://martinescardo.github.io/.talks/mfps2026.pdf
  https://ul-fmf.github.io/mfps-sstt-2026/

where what is answered in (2) and (3) above was left open.
