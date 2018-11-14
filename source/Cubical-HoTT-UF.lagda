Adapted by Martin Escardo, 22 October 2018, from code
https://github.com/agda/cubical by

  Anders Mörtberg
  Andrea Vezzosi

This is a small HoTT-UF library based on cubical type theory, where
the cubical machinery is hidden.

The point is that function extensionality, propositional truncation
and univalence compute (an example is given below).

For the moment this requires the development version of Agda.

\begin{code}

{-# OPTIONS --cubical --exact-split --safe #-}

module Cubical-HoTT-UF where

open import Cubical public
     using ( _≡_            -- The identity type.
           ; refl           -- Unfortunately, pattern matching on refl is not available.
           ; J              -- Until it is, you have to use the induction principle J.

           ; transport      -- As in the HoTT book, here defined from J.
           ; _∙_            -- Path composition, here defined from transport.
           ; _⁻¹            -- Path inversion, here defined from transport.
           ; ap             -- As in the HoTT book, here defined from transport.

           ; _≡⟨_⟩_         -- Equational reasoning.
           ; _∎

           ; funext         -- Function extensionality
                            -- (can also be derived from univalence).

           ; Σ              -- Sum type. Needed to define contractible types, equivalences
           ; _,_            -- and univalence.
           ; pr₁            -- The eta rule is available.
           ; pr₂

           ; is-prop        -- The usual notions of proposition, contractible type, set.
           ; is-contr
           ; is-set

           ; is-equiv       -- A map with contractible fibers
                            -- (Voevodsky's version of the notion).
           ; _≃_            -- The type of equivalences between two given types.
           ; univalence     -- Click to navigate to the adopted formulation of univalence.

           ; ∥_∥             -- Propositional truncation.
           ; ∣_∣            -- Map into the propositional truncation.
           ; ∥∥-is-prop      -- A truncated type is a proposition.
           ; ∥∥-recursion    -- Non-dependent elimination.
           ; ∥∥-induction    -- Dependent elimination.

           ; Universe       -- The type of universes (originally called Level).
           ; 𝓤₀             -- The first universe (originally called lzero).
           ; _̇              -- We write X : 𝓤 ̇ to say that X is in the universe U
                            -- (originally X : Set U).
           ; _⁺             -- The successor of a universe (originally called lsucc).
           ; _⊔_            -- 𝓤 ⊔ 𝓥 is the first universe above or equal U and V.
           )

\end{code}

If you prefer the traditional universe handling using the keyword
"Set" and the terminology "Level", simply hide or rename the above
universe constructs when importing this module.

Here is an illustration of how function extensionality computes.

\begin{code}

private

  data ℕ : 𝓤₀ ̇ where
   zero : ℕ
   succ : ℕ → ℕ

  f g : ℕ → ℕ

  f n = n

  g zero = zero
  g (succ n) = succ (g n)

  h : (n : ℕ) → f n ≡ g n
  h zero = refl
  h (succ n) = ap succ (h n)

  p : f ≡ g
  p = funext h

  five : ℕ
  five = succ (succ (succ (succ (succ zero))))

  a : Σ \(n : ℕ) → f n ≡ five
  a = five , refl

  b : Σ \(n : ℕ) → g n ≡ five
  b = transport (λ - → Σ \(n : ℕ) → - n ≡ five) p a

  c : pr₁ b ≡ five
  c = refl

\end{code}

If we had funext as a postulate, then the definition of c would not
type check. Moreover, the term pr₁ b would not evaluate to five, as it
does with the cubical type theory implementation of funext.

TODO. A similar example with univalence.
