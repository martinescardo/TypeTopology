Martin Escardo and Paulo Oliva, May-August 2024.

For some applications to combinatorial game theory, we need affine
monads, namely monads T such that

 η : 𝟙 → T 𝟙

is an isomorphism.

Counter-examples include the list monad. But if we restrict to
non-empty lists without repetitions, we do get an affine monad.

However, to work with a monad of lists without repetitions we need
decidable equality on the types under consideration. This leads us to
consider relative monads on strutured types, where in this example the
structure is actually property, namely decidability of equality. In
this example, we need decidable equality on X to be able to form T X,
but we don't need to consider decidable equality on T X, so our monads
don't need to be endofunctors, in the sense of [1].

[1] Thorsten Altenkirch, James Chapman, Tarmo Uustalu, Monads need not
    be endofunctors, Logical Methods in Computer Science 11 1:3 (2015)
    1–40 [arXiv:1412.7148, doi:10.2168/LMCS-11(1:3)2015]

\begin{code}

{-# OPTIONS --safe --without-K #-}

module RelativeMonadOnStructuredTypes.index where

import RelativeMonadOnStructuredTypes.OneSigmaStructure -- (1)
import RelativeMonadOnStructuredTypes.Monad             -- (2)
import RelativeMonadOnStructuredTypes.NELWR             -- (3)
import RelativeMonadOnStructuredTypes.J-transf          -- (4)

\end{code}

 1. This defines the notion of structure we consider, which is
    required to be closed under 𝟙 and Σ.

 2. This defines relative monads on types equipped with the structure
    defined in (1).  Because we also want to eventually consider
    relative monads such as e.g. non-empty powersets over types with
    some structure, which changes universe level, our monads are
    parametrized by a function ℓ : Universe → Universe (this requires
    using the Agda flag no-level-universe). For example, for lists
    without repetitions, we have ℓ 𝓤 = 𝓤, but for powersets we have
    ℓ 𝓤 = 𝓤⁺.

 3. This defines an affine relative monad of non-empty lists without
    repetitions on types with decidable equality. This crucially
    relies on a file that considers discrete graphic monoids in the
    sense of Lawvere.

 4. This defines a (relative) monad transformer which given a monad T
    and a notion of structured type, produces a new monad JT by
    JT X = (X → T R) → T X.
