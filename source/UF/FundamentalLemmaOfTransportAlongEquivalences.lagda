Martin Escardo, 20 Jun 2025.

Copied from a 16th August 2023 file in this repository on injectivity
of mathematical structures, because it deserves a better and more
general home.

We formulate and prove what we call here the "Fundamental Lemma of
transport along equivalences".

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.FundamentalLemmaOfTransportAlongEquivalences where

open import MLTT.Spartan
open import UF.Equiv
open import UF.Univalence

\end{code}

In the presence of univalence, we can transport along equivalences in
the following sense.

\begin{code}

transport-along-≃ : is-univalent 𝓤
                  → (S : 𝓤 ̇ → 𝓥 ̇ )
                    {X Y : 𝓤 ̇ }
                  → X ≃ Y → S X → S Y
transport-along-≃ ua S {X} {Y} 𝕗 = transport S (eqtoid ua X Y 𝕗)

\end{code}

That is, this construction converts the equivalence to an
identification, using univalence, and then uses standard transport.

Because the function transport-along-≃ uses univalence as a
hypothesis, it is difficult to reason with, and also to compute with.

However, if we can guess *any* functions

   T      : {X Y : 𝓤 ̇ } → X ≃ Y → S X → S Y
   T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id,

which we are very often able to do in practice, then it becomes
trivial to reason with, and also to compute with, thanks to the
following fundamental lemma of transport along equivalences.

This says that, for any equivalence

  𝕗 : X ≃ Y

we have that

  T 𝕗 ∼ transport-along-≃ ua S 𝕗,

so that we can work with T rather than with the more awkward
transport-along-≃.

What is perhaps surprising is that no conditions on T and T-refl are
needed. Any T and T-refl with the given types work, without the need
of any further condition.

The proof is by equivalence induction (called JEq).

\begin{code}

fundamental-transport-along-≃-lemma
 : {𝓤 𝓥 : Universe}
   (S      : 𝓤 ̇ → 𝓥 ̇ )
   (T      : {X Y : 𝓤 ̇ } → X ≃ Y → S X → S Y)
   (T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id)
   (ua     : is-univalent 𝓤)
   {X Y : 𝓤 ̇ }
   (𝕗 : X ≃ Y)
 → T 𝕗 ∼ transport-along-≃ ua S 𝕗
fundamental-transport-along-≃-lemma {𝓤} {𝓥} S T T-refl ua {X} {Y} 𝕗 s
 = JEq ua X A I Y 𝕗
 where
  A : (Y : 𝓤 ̇ ) (𝕗 : X ≃ Y) → 𝓥 ̇
  A Y 𝕗 = T 𝕗 s ＝ transport-along-≃ ua S 𝕗 s

  I : A X (≃-refl X)
  I = T (≃-refl X) s                                ＝⟨ T-refl s ⟩
      s                                             ＝⟨ refl ⟩
      transport S refl s                            ＝⟨ II ⟩
      transport S (eqtoid ua X X (≃-refl X)) s  ＝⟨ refl ⟩
      transport-along-≃ ua S (≃-refl X) s                             ∎
    where
     II = (ap (λ - → transport S - s) (eqtoid-refl ua X))⁻¹

\end{code}

I am not sure if this lemma has been formulated and proved before, but
I won't be surprised if it has. But it does follow from what Egbert
Rijke calls "The Fundamental Theorem of identity types", although here
we are giving a direct proof by equivalence induction.

In any case, we have found it to be really useful in practice.
