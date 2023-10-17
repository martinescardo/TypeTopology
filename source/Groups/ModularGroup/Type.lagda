Lane Biocini
21 January 2026

The modular group PSL(2,ℤ) ≅ ⟨s, r | s² = r³ = 1⟩ defined as a mutual
inductive type. Rather than constructing PSL(2,ℤ) as a quotient of matrices
or a free group modulo relations, we internalize its Cayley graph structure
directly as the type.

The Cayley graph for the presentation ⟨s, r | s² = r³ = 1⟩ has a natural
bipartite structure: vertices partition into those reachable from the
identity without a "pending" rotation (S-edges) and those with a pending
r or r² (R-edges). The mutual recursion captures that s toggles between
these classes (since s² = 1), while r cycles through rotation states
(since r³ = 1).

This encoding makes the defining relations s² = 1 and r³ = 1 hold
definitionally. They compute by the structure of pattern matching rather
than requiring propositional proofs.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module Groups.ModularGroup.Type where

open import MLTT.Spartan
open import UF.Base

R-sgn : 𝓤₀ ̇
R-sgn = 𝟚

pattern cw  = ₀
pattern ccw = ₁

data S-edge : 𝓤₀ ̇
data R-edge : 𝓤₀ ̇

data S-edge where
  e₀    : S-edge
  e₁    : S-edge
  cross : R-edge → S-edge

data R-edge where
  step : R-sgn → S-edge → R-edge

PSL2Z : 𝓤₀ ̇
PSL2Z = S-edge + R-edge

\end{code}

The injection patterns η and θ distinguish the two vertex classes.
The derived patterns (s∙, r∙, r²∙, sr∙, sr²∙, etc.) provide readable
notation matching the group element naming conventions.

\begin{code}

pattern η_ se = inl se
pattern θ_ re = inr re

pattern ρ i se = θ step i se
pattern σ i se = η cross (step i se)

pattern r+_ se = step cw se
pattern r-_ se = step ccw se

pattern s∙_ re   = η cross re
pattern r∙_ se   = ρ cw se
pattern r²∙_ se  = ρ ccw se

pattern sr∙_ se  = s∙ r+ se
pattern sr²∙_ se = s∙ r- se
pattern rs∙_ re  = r∙ cross re
pattern r²s∙_ re = r²∙ cross re

E S R R² : PSL2Z
E  = η e₀
S  = η e₁
R  = r∙ e₀
R² = r²∙ e₀

SR SR² RS R²S : PSL2Z
SR  = sr∙ e₀
SR² = sr²∙ e₀
RS  = r∙ e₁
R²S = r²∙ e₁

SRS SR²S RSR R²SR RSR² R²SR² : PSL2Z
SRS   = sr∙ e₁
SR²S  = sr²∙ e₁
RSR   = rs∙ r+ e₀
R²SR  = r²s∙ r+ e₀
RSR²  = rs∙ r- e₀
R²SR² = r²s∙ r- e₀

\end{code}
