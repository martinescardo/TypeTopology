Adapted by Martin Escardo, 22 October 2018, from code
https://github.com/agda/cubical by

  Anders Mörtberg
  Andrea Vezzosi

This is a small HoTT-UF library based on cubical type theory, where
the cubical machinery is hidden.

The point is that function extensionality, propositional truncation
and univalence compute.

For the moment this requires the development version of Agda.

\begin{code}

{-# OPTIONS --cubical --exact-split --safe #-}

module Cubical-HoTT-UF where

open import Cubical public
     using ( _≡_            -- The identity type.
           ; refl           -- Unfortunately, pattern matching on refl is not available.
           ; J              -- Until it is, you have to use the induction principle J.

           ; funext         -- Function extensionality (can also be derived from univalence).

           ; Σ              -- Sum type. Needed to define equivalences and univalence.
           ; pr₁
           ; pr₂

           ; is-prop        -- The usual notions of proposition, contractible type, set.
           ; is-contr
           ; is-set
           ; is-equiv       -- A map with contractible fibers (Voevodsky version of the notion).

           ; _≃_            -- The type of equivalences between two given types.
           ; univalence     -- Click to navigate to the adopted formulation of univalence.

           ; ∥_∥             -- Propositional truncation.
           ; ∣_∣            -- Map into the propositional truncation.
           ; ∥∥-is-prop      -- A truncated type is a proposition.
           ; ∥∥-recursion    -- Non-dependent elimination.
           ; ∥∥-induction    -- Dependent elimination.

           ; Universe       -- The type of universes (originally called Level).
           ; U₀             -- The first universe (originally called lzero).
           ; _̇              -- We write X : U ̇ to say that X is in the universe U (originally X : Set U).
           ; _′             -- The successor of a universe (originally called lsucc).
           )

\end{code}

If you prefer the traditional universe handling using the keyword
"Set" and the type "Level", simply hide the above universe constructs
when importing this module.
