-------------------------------------------------------------------------------
authors:      [Ayberk Tosun]
date-started: 2024-05-02
--------------------------------------------------------------------------------

\begin{code}

open import MLTT.Spartan
open import UF.Embeddings
open import UF.SubtypeClassifier
open import UF.FunExt
open import UF.PropTrunc
open import UF.Classifiers
open import UF.Subsingletons

module SyntheticTopology.SierpinskiObject
        (𝓤  : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist) where

open import UF.Logic
open import UF.ImageAndSurjection pt

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

What is a Sierpiński object? In Definition 2.4 of Davorin Lesnik's thesis, it is
defined simply as a subobject of the subobject classifier.

\begin{code}

Sierpinski-Object : 𝓤 ⁺  ̇
Sierpinski-Object = Subtypes' 𝓤  (Ω 𝓤)

Sierpinski-Object′ : 𝓤 ⁺  ̇
Sierpinski-Object′ = Ω 𝓤 → Ω 𝓤

index : Sierpinski-Object → 𝓤  ̇
index (I , α , _) = I

sierpinski-fun : (𝕊 : Sierpinski-Object) → index 𝕊 → Ω 𝓤
sierpinski-fun (_ , α , _) = α

\end{code}

In the module below, we assume the existence of a Sierpiński object `𝕊` and
define some notions _synthetically_. The meaning of "synthetic" here can be
understood through its contradiction with the analytic [1]. Instead of analyzing
topological notions, we synthesize them: we formulate them in terms of the
Sierpiński object.

\begin{code}

module _ (𝕊 : Sierpinski-Object) where

 ι : index 𝕊 → Ω 𝓤
 ι = sierpinski-fun 𝕊

 S : 𝓤  ̇
 S = index 𝕊

\end{code}

The propositions in `Ω` that fall in the subset delineated by the Sierpiński
object are called _affirmable.

\begin{code}

 is-affirmable : Ω 𝓤 → Ω (𝓤 ⁺)
 is-affirmable P = P ∈image ι , ∃-is-prop

\end{code}

\begin{code}

 is-intrinsically-open′ : {X : 𝓤  ̇} → (X → Ω 𝓤) → Ω (𝓤 ⁺)
 is-intrinsically-open′ {X} P = Ɐ x ꞉ X , is-affirmable (P x)

\end{code}

\begin{code}

 is-intrinsically-open : {X : 𝓤  ̇} → (X → Ω 𝓤) → Ω 𝓤
 is-intrinsically-open {X} P =
  Ǝₚ h ꞉ (X → S) , (Ɐ x ꞉ X , P x ⇔ ι (h x))

\end{code}

\begin{code}

 open-implies-open′ : {X : 𝓤  ̇} → (P : X → Ω 𝓤)
                    → (is-intrinsically-open  P ⇒ is-intrinsically-open′ P) holds
 open-implies-open′ {X} P = ∥∥-rec (holds-is-prop (is-intrinsically-open′ P)) †
  where
   † : (Σ h ꞉ (X → S) , ((x : X) → P x holds ↔ ι (h x) holds))
     → is-intrinsically-open′ P holds
   † (h , φ) x = transport (_holds ∘ is-affirmable) (q ⁻¹) ∣ (h x) , refl ∣
    where
     p : (P x ⇔ ι (h x)) holds
     p = φ x

     q : P x ＝ ι (h x)
     q = ⇔-gives-＝ pe (P x) (ι (h x)) (holds-gives-equal-⊤ pe fe (P x ⇔ ι (h x)) p)

\end{code}

Question: are these two definitions equivalent?

[1]: https://ncatlab.org/nlab/show/analytic+versus+synthetic
