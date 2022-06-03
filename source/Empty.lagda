Empty type.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Empty where

open import Empty-Type public

\end{code}

This should be the only use of the () pattern in this development:

\begin{code}

𝟘-induction : {A : 𝟘 {𝓤} → 𝓥 ̇ } → (x : 𝟘) → A x
𝟘-induction = λ ()

unique-from-𝟘 : {A : 𝓥 ̇ } → 𝟘 {𝓤} → A
unique-from-𝟘 = 𝟘-induction

𝟘-elim = unique-from-𝟘

\end{code}
