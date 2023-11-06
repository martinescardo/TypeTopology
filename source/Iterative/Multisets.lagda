Martin Escardo & Tom de Jong, June 2023.

Iterative multisets.

See the module Iterative.index for bibliographic references regarding
this file. All the results of this file are in Håkon Gylterud [3].

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module Iterative.Multisets
        (𝓤 : Universe)
       where

open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

open import W.Type
open import W.Properties (𝓤 ̇) id

private
 𝓤⁺ : Universe
 𝓤⁺ = 𝓤 ⁺

\end{code}

The type of iterative multisets:

\begin{code}

𝕄 : 𝓤⁺ ̇
𝕄 = W (𝓤 ̇ ) id

\end{code}

This is equivalent to the following alternative definition.

\begin{code}

private

 data 𝕄' : 𝓤⁺ ̇ where
  ssup : (X : 𝓤 ̇ ) (φ : X → 𝕄') → 𝕄'

 𝕄-to-𝕄' : 𝕄 → 𝕄'
 𝕄-to-𝕄' (ssup X φ) = ssup X (λ x → 𝕄-to-𝕄' (φ x))

 𝕄'-to-𝕄 : 𝕄' → 𝕄
 𝕄'-to-𝕄 (ssup X φ) = ssup X (λ x → 𝕄'-to-𝕄 (φ x))

\end{code}

Maybe add the proof that the above two functions are mutually
inverse. But the only point of adding them is to make sure that the
above comment remains valid if any change is made in the code, and the
above two definitions seem to be enough for that purpose.

Aside. Every W-type can be mapped to 𝕄 as follows:

\begin{code}

W-to-𝕄 : {X : 𝓤 ̇ } {A : X → 𝓤 ̇ }
       → W X A → 𝕄
W-to-𝕄 {X} {A} (ssup x f) = ssup (A x) (λ a → W-to-𝕄 (f a))

\end{code}

TODO. Is the above remark relevant in any way?

In the case of ordinals, "ssup" stands for "strong supremum", "strict
supremum" or "supremum of successors". See the module Iterative.Ordinals.

The two destructors:

\begin{code}

𝕄-root : 𝕄 → 𝓤 ̇
𝕄-root = W-root

𝕄-forest : (M : 𝕄) → 𝕄-root M → 𝕄
𝕄-forest = W-forest

\end{code}

The following properties of the above two destructors hold
definitionally;

\begin{code}

𝕄-ssup-root : (X : 𝓤 ̇ ) (φ : X → 𝕄)
            → 𝕄-root (ssup X φ) ＝ X
𝕄-ssup-root = W-ssup-root

𝕄-ssup-forest : (X : 𝓤 ̇ ) (φ : X → 𝕄)
              → 𝕄-forest (ssup X φ) ＝ φ
𝕄-ssup-forest = W-ssup-forest

\end{code}

But the η-law holds only up to an identification:

\begin{code}

𝕄-η : (M : 𝕄)
    → ssup (𝕄-root M) (𝕄-forest M) ＝ M
𝕄-η = W-η

\end{code}

The membership relation for multisets:

\begin{code}

_⁅_ : 𝕄 → 𝕄 → 𝓤⁺ ̇
M ⁅ N = Σ x ꞉ 𝕄-root N , 𝕄-forest N x ＝ M

\end{code}

The relation M ⁅ N can hold in multiple ways in general. We can think
of M ⁅ N as measuring how many times M occurs as an element on N.

Notice the following:

\begin{code}

private
 ⁅-remark : (M N : 𝕄)
          → (M ⁅ N) ＝ fiber (𝕄-forest N) M
 ⁅-remark M N = refl

\end{code}

In particular, if 𝕄-forest N is an embedding, then M ⁅ N holds in at
most one way. This situation is investigated in the module
Iterative.Sets.

The following fact is trivial, but it is good to have a name for it
for the sake of clarity.

\begin{code}

𝕄-forest-⁅ : (M : 𝕄) (x : 𝕄-root M) → 𝕄-forest M x ⁅ M
𝕄-forest-⁅ _ x = x , refl

\end{code}

The induction principle for 𝕄, and particular cases:

\begin{code}

𝕄-induction : (P : 𝕄 → 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) (φ : X → 𝕄)
                  → ((x : X) → P (φ x))
                  → P (ssup X φ))
            → (M : 𝕄) → P M
𝕄-induction = W-induction

𝕄-recursion : (P : 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) → (X → 𝕄) → (X → P) → P)
            → 𝕄 → P
𝕄-recursion = W-recursion

𝕄-iteration : (P : 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) → (X → P) → P)
            → 𝕄 → P
𝕄-iteration = W-iteration

\end{code}

A criterion for equality in 𝕄:

\begin{code}

to-𝕄-＝ : {X Y : 𝓤 ̇ }
          {φ : X → 𝕄}
          {γ : Y → 𝕄}
        → (Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p)
        → ssup X φ ＝[ 𝕄 ] ssup Y γ
to-𝕄-＝ = to-W-＝

from-𝕄-＝ : {X Y : 𝓤 ̇ }
            {φ : X → 𝕄}
            {γ : Y → 𝕄}
          → ssup X φ ＝[ 𝕄 ] ssup Y γ
          → Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p
from-𝕄-＝ = from-W-＝

from-to-𝕄-＝ : {X Y : 𝓤 ̇ }
               {φ : X → 𝕄}
               {γ : Y → 𝕄}
               (σ : Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p)
             → from-𝕄-＝ {X} {Y} {φ} {γ} (to-𝕄-＝ σ) ＝ σ
from-to-𝕄-＝ = from-to-W-＝

to-from-𝕄-＝ : {X Y : 𝓤 ̇ }
            {φ : X → 𝕄}
            {γ : Y → 𝕄}
            (p : ssup X φ ＝ ssup Y γ)
          → to-𝕄-＝ (from-𝕄-＝ p) ＝ p
to-from-𝕄-＝ = to-from-W-＝

𝕄-＝ : {X Y : 𝓤 ̇ }
       {φ : X → 𝕄}
       {γ : Y → 𝕄}
     → (ssup X φ ＝[ 𝕄 ] ssup Y γ)
     ≃ (Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p)
𝕄-＝ = W-＝

𝕄-＝' : (M N : 𝕄) → (M ＝ N) ≃ (fiber ((𝕄-forest N ∘_) ∘ Idtofun) (𝕄-forest M))
𝕄-＝'  M@(ssup X φ) N@(ssup Y γ) =
 (ssup X φ ＝ ssup Y γ)              ≃⟨ 𝕄-＝ ⟩
 (Σ p ꞉ X ＝ Y , φ ＝ γ ∘ Idtofun p) ≃⟨ Σ-cong (λ p → ＝-flip) ⟩
 (Σ p ꞉ X ＝ Y , γ ∘ Idtofun p ＝ φ) ≃⟨ ≃-refl _ ⟩
 fiber ((γ ∘_) ∘ Idtofun) φ          ■

\end{code}

The above works in pure MLTT without any HoTT/UF assumptions.

We now show that 𝕄 is locally small assuming univalence. For this
purpose, we characterize identification of multisets as follows.

TODO. Notice that there is some ammount of repetition compared with
Iterative.W-Properties. Can we avoid it by proving something more
general that subsumes both cases?

\begin{code}

_≃ᴹ_ : 𝕄 → 𝕄 → 𝓤 ̇
ssup X φ ≃ᴹ ssup X' φ' = Σ 𝕗 ꞉ X ≃ X' , ((x : X) → φ x ≃ᴹ φ' (⌜ 𝕗 ⌝ x))

≃ᴹ-refl : (M : 𝕄) → M ≃ᴹ M
≃ᴹ-refl (ssup X φ) = ≃-refl X , (λ x → ≃ᴹ-refl (φ x))

singleton-typeᴹ : 𝕄 → 𝓤⁺ ̇
singleton-typeᴹ M = Σ t ꞉ 𝕄 , M ≃ᴹ t

M-center : (M : 𝕄) → singleton-typeᴹ M
M-center M = M , ≃ᴹ-refl M

M-centrality : Univalence
             → (M : 𝕄) (σ : singleton-typeᴹ M) → M-center M ＝ σ
M-centrality ua (ssup X φ) (ssup Y γ , 𝕗 , u) =
 V (eqtoid (ua 𝓤) X Y 𝕗) (idtoeq-eqtoid (ua 𝓤) X Y 𝕗 ⁻¹)
 where
  V : (p : X ＝ Y) → 𝕗 ＝ idtoeq X Y p → M-center (ssup X φ) ＝ ssup Y γ , 𝕗 , u
  V refl refl = IV
   where
    IH : (x : X) → M-center (φ x) ＝ γ (⌜ 𝕗 ⌝ x) , u x
    IH x = M-centrality ua (φ x) (γ (⌜ 𝕗 ⌝ x) , u x)

    I : (λ x → M-center (φ x)) ＝ (λ x → γ (⌜ 𝕗 ⌝ x) , u x)
    I = dfunext (Univalence-gives-Fun-Ext ua) IH

    π : (Σ δ ꞉ (X → 𝕄) , ((x : X) → φ x ≃ᴹ δ x))
      → singleton-typeᴹ (ssup X φ)
    π (δ , v) = ssup X δ , ≃-refl X , v

    II : (φ , λ x → ≃ᴹ-refl (φ x)) ＝ (γ ∘ ⌜ 𝕗 ⌝ , u)
    II = ap ΠΣ-distr I

    III : (ssup X φ ,           ≃-refl X , λ x → ≃ᴹ-refl (φ x))
       ＝ (ssup X (γ ∘ ⌜ 𝕗 ⌝) , ≃-refl X , u)
    III = ap π II

    IV =
     M-center (ssup X φ)                         ＝⟨ refl ⟩
     ssup X φ , ≃-refl X , (λ x → ≃ᴹ-refl (φ x)) ＝⟨ III ⟩
     ssup X (γ ∘ ⌜ 𝕗 ⌝) , ≃-refl X , u           ＝⟨ refl ⟩
     ssup Y γ , 𝕗 , u                            ∎

singleton-typesᴹ-are-singletons : Univalence
                                → (M : 𝕄) → is-singleton (singleton-typeᴹ M)
singleton-typesᴹ-are-singletons ua M = M-center M , M-centrality ua M

idtoeqᴹ : (M N : 𝕄) → M ＝ N → M ≃ᴹ N
idtoeqᴹ M M refl = ≃ᴹ-refl M

idtoeqᴹ-is-equiv : Univalence
                 → (M t : 𝕄) → is-equiv (idtoeqᴹ M t)
idtoeqᴹ-is-equiv ua M = I
 where
  f : singleton-type M → singleton-typeᴹ M
  f = NatΣ (idtoeqᴹ M)

  f-is-equiv : is-equiv f
  f-is-equiv = maps-of-singletons-are-equivs f
                (singleton-types-are-singletons M)
                (singleton-typesᴹ-are-singletons ua M)

  I : (t : 𝕄) → is-equiv (idtoeqᴹ M t)
  I = NatΣ-equiv-gives-fiberwise-equiv (idtoeqᴹ M) f-is-equiv

𝕄-＝-≃ : Univalence
      → (M N : 𝕄) → (M ＝ N) ≃ (M ≃ᴹ N)
𝕄-＝-≃ ua M N = idtoeqᴹ M N , idtoeqᴹ-is-equiv ua M N

\end{code}

And here is the desired conclusion:

\begin{code}

𝕄-is-locally-small : Univalence
                   → is-locally-small 𝕄
𝕄-is-locally-small ua M N = M ≃ᴹ N , ≃-sym (𝕄-＝-≃ ua M N)

\end{code}

Not only the type of identifications of elements of 𝕄 has a small
copy, but also so does the (multi-valued) membership relation:

\begin{code}

_⁅⁻_ : 𝕄 → 𝕄 → 𝓤 ̇
M ⁅⁻ N = Σ x ꞉ 𝕄-root N , 𝕄-forest N x ≃ᴹ M

⁅⁻≃⁅ : Univalence
     → (M N : 𝕄) → (M ⁅ N) ≃ (M ⁅⁻ N)
⁅⁻≃⁅ ua M N = Σ-cong (λ x → 𝕄-＝-≃ ua (𝕄-forest N x) M)

\end{code}
