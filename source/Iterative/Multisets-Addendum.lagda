Martin Escardo and Tom de Jong, July 2023.

Some constructions with iterative multisets.

 * The universe is a retract of the type 𝕄 of iterative multisets.
 * 𝕄 is algebraically injective.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_^_)
open import UF.Sets-Properties
open import UF.Univalence
open import UF.Universes

module Iterative.Multisets-Addendum
        (ua : Univalence)
        (𝓤 : Universe)
       where

open import Iterative.Multisets 𝓤
open import Iterative.Sets ua 𝓤
open import Taboos.Decomposability ua
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.HedbergApplications
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Sets
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import W.Type

private
 𝓤⁺ : Universe
 𝓤⁺ = 𝓤 ⁺

 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import InjectiveTypes.Blackboard fe'

\end{code}

The universe 𝓤 is embedded as a retract of 𝕄. This seems to be a new
observation.

\begin{code}

𝟘ᴹ : 𝕄
𝟘ᴹ = ssup 𝟘 unique-from-𝟘

𝟘ᴹ-is-iset : is-iterative-set 𝟘ᴹ
𝟘ᴹ-is-iset = unique-from-𝟘-is-embedding , (λ (x : 𝟘) → 𝟘-elim x)

𝟘ᴹ-is-h-isolated : is-h-isolated 𝟘ᴹ
𝟘ᴹ-is-h-isolated {ssup X φ} = isets-are-h-isolated 𝟘ᴹ 𝟘ᴹ-is-iset

𝟙ᴹ : 𝕄
𝟙ᴹ = ssup 𝟙 λ ⋆ → 𝟘ᴹ

𝟙ᴹ-is-iset : is-iterative-set 𝟙ᴹ
𝟙ᴹ-is-iset = global-point-is-embedding (λ ⋆ → 𝟘ᴹ) 𝟘ᴹ-is-h-isolated ,
             λ ⋆ → 𝟘ᴹ-is-iset

𝟙ᴹ-is-h-isolated : is-h-isolated 𝟙ᴹ
𝟙ᴹ-is-h-isolated {ssup X φ} = isets-are-h-isolated 𝟙ᴹ 𝟙ᴹ-is-iset

𝟘ᴹ-is-not-𝟙ᴹ : 𝟘ᴹ ≠ 𝟙ᴹ
𝟘ᴹ-is-not-𝟙ᴹ p = 𝟘-is-not-𝟙 (ap 𝕄-root p)

𝟚ᴹ : 𝕄
𝟚ᴹ = ssup (𝟙 {𝓤} + 𝟙 {𝓤}) (cases (λ _ → 𝟘ᴹ) (λ _ → 𝟙ᴹ))

universe-to-𝕄 : 𝓤 ̇ → 𝕄
universe-to-𝕄 X = ssup X (λ x → 𝟘ᴹ)

universe-to-𝕄-is-section : 𝕄-root ∘ universe-to-𝕄 ∼ id
universe-to-𝕄-is-section X = refl

universe-is-retract-of-𝕄 : retract (𝓤 ̇ ) of 𝕄
universe-is-retract-of-𝕄 = 𝕄-root , universe-to-𝕄 , universe-to-𝕄-is-section

𝕄-is-not-set : ¬ is-set 𝕄
𝕄-is-not-set i = universes-are-not-sets (ua 𝓤)
                  (retract-of-set universe-is-retract-of-𝕄 i)

\end{code}

Although a section is not an embedding in general, in this case it is.

\begin{code}

universe-to-𝕄-is-embedding : is-embedding universe-to-𝕄
universe-to-𝕄-is-embedding M@(ssup Y φ) = II
 where
  I = fiber universe-to-𝕄 M                                           ≃⟨ ≃-refl _ ⟩
      (Σ X ꞉ 𝓤 ̇ , ssup X (λ x → 𝟘ᴹ) ＝ (ssup Y φ))                    ≃⟨ I₀ ⟩
      (Σ X ꞉ 𝓤 ̇ , Σ p ꞉ X ＝ Y , (λ x → 𝟘ᴹ) ＝ φ ∘ Idtofun p)         ≃⟨ I₁ ⟩
      (Σ (X , p) ꞉ (Σ X ꞉ 𝓤 ̇ , X ＝ Y) , (λ x → 𝟘ᴹ) ＝ φ ∘ Idtofun p) ■
   where
    I₀ = Σ-cong (λ X → 𝕄-＝)
    I₁ = ≃-sym Σ-assoc

  II : is-prop (fiber universe-to-𝕄 M)
  II = equiv-to-prop I
        (subsets-of-props-are-props _ _
          (singleton-types'-are-props Y)
          (constant-maps-are-h-isolated fe 𝟘ᴹ 𝟘ᴹ-is-h-isolated))

\end{code}

Submultisets.

\begin{code}

𝕄-separation : (M : 𝕄) (P : 𝕄 → 𝓤 ̇ )
             → Σ M' ꞉ 𝕄 , ((N : 𝕄) → (N ⁅ M') ≃ (N ⁅ M × P N))
𝕄-separation M@(ssup X φ) P = M' , Q
 where
  M' : 𝕄
  M' = ssup (Σ x ꞉ X , P (φ x)) (λ (x , p) → φ x)

  Q→ : (N : 𝕄) → N ⁅ M' → N ⁅ M × P N
  Q→ N ((x , p) , refl) = (x , refl) , p

  Q← : (N : 𝕄) → N ⁅ M × P N → N ⁅ M'
  Q← N ((x , refl) , p) = (x , p) , refl

  η : (N : 𝕄) → Q← N ∘ Q→ N ∼ id
  η N ((x , p) , refl) = refl

  ε : (N : 𝕄) → Q→ N ∘ Q← N ∼ id
  ε N ((x , refl) , p) = refl

  Q : (N : 𝕄) → N ⁅ M' ≃ (N ⁅ M × P N)
  Q N = qinveq (Q→ N) (Q← N , η N , ε N)

submultiset : 𝕄 → (𝕄 → 𝓤 ̇ ) → 𝕄
submultiset M P = pr₁ (𝕄-separation M P)

submultiset-≃ : (M : 𝕄) (P : 𝕄 → 𝓤 ̇ )
              → (N : 𝕄) → (N ⁅ submultiset M P) ≃ (N ⁅ M × P N)
submultiset-≃ M P = pr₂ (𝕄-separation M P)

\end{code}

The type of multisets is large, in the sense that it doesn' have a
small copy. This is proved using Russell's Paradox technique, using
separation as defined above.

\begin{code}

𝕄-is-large : is-large 𝕄
𝕄-is-large (X , 𝕗) = III
 where
  have-𝕗 : X ≃ 𝕄
  have-𝕗 = 𝕗

  private
   remark-X : 𝓤 ̇
   remark-X = X

   remark-𝕄 : 𝓤⁺ ̇
   remark-𝕄 = 𝕄

  M : 𝕄
  M = ssup X ⌜ 𝕗 ⌝

  M-universal : (N : 𝕄) → N ⁅ M
  M-universal N = ⌜ 𝕗 ⌝⁻¹ N , inverses-are-sections' 𝕗 N

  P : (N : 𝕄) → 𝓤 ̇
  P N = ¬ (N ⁅⁻ N)

  R : 𝕄
  R = submultiset M P

  g : (N : 𝕄) → (N ⁅ R) ≃ (N ⁅ M × ¬ (N ⁅⁻ N))
  g = submultiset-≃ M P

  h : (R ⁅ R) ≃ (R ⁅⁻ R)
  h = ⁅⁻≃⁅ ua R R

  I : R ⁅⁻ R → ¬ (R ⁅⁻ R)
  I i = pr₂ (⌜ g R ⌝ (⌜ h ⌝⁻¹ i))

  II : ¬ (R ⁅⁻ R) → R ⁅⁻ R
  II ν = ⌜ h ⌝ (⌜ g R ⌝⁻¹ (M-universal R , ν))

  III : 𝟘
  III = not-equivalent-to-own-negation (I , II)

\end{code}

The above is Russell's paradox adapted to multisets. But we also have
the following alternative proof:

\begin{code}

𝕄-is-large' : is-large 𝕄
𝕄-is-large' 𝕄-is-small = II
 where
  I : (𝓤 ̇) is 𝓤 small
  I = embedded-retract-is-small
       universe-is-retract-of-𝕄
       universe-to-𝕄-is-embedding
       𝕄-is-small

  II : 𝟘
  II = universes-are-large I

\end{code}

However, this proof, when expanded, is essentially the same as
that of Russell's paradox.

The type of multisets is algebraically injective, which is a new
result. We give two constructions, using Σᴹ and Πᴹ defined below.

\begin{code}

Σᴹ : {X : 𝓤 ̇ } → (X → 𝕄) → 𝕄
Σᴹ {X} A = ssup
            (Σ x ꞉ X , 𝕄-root (A x))
            (λ (x , y) → 𝕄-forest (A x) y)

_+ᴹ_ : 𝕄 → 𝕄 → 𝕄
M +ᴹ N = Σᴹ (cases (λ (_ : 𝟙 {𝓤}) → M) (λ (_ : 𝟙 {𝓤}) → N))

prop-indexed-sumᴹ : {X : 𝓤 ̇ } {A : X → 𝕄}
                  → is-prop X
                  → (x₀ : X) → Σᴹ A ＝ A x₀
prop-indexed-sumᴹ {X} {A} i x₀ = IV
 where
  𝕗 = (Σ x ꞉ X , 𝕄-root (A x)) ≃⟨ prop-indexed-sum i x₀ ⟩
      𝕄-root (A x₀)            ■

  remark : ⌜ 𝕗 ⌝ ＝ (λ (x , y) → transport (λ - → 𝕄-root (A -)) (i x x₀) y)
  remark = refl

  I : ((x , y) : Σ x ꞉ X , 𝕄-root (A x))
      (p : x ＝ x₀)
    → 𝕄-forest (A x) y ＝ 𝕄-forest (A x₀) (transport (λ - → 𝕄-root (A -)) p y)
  I _ refl = refl

  II : ((x , y) : Σ x ꞉ X , 𝕄-root (A x))
     → 𝕄-forest (A x) y ＝ 𝕄-forest (A x₀) (⌜ 𝕗 ⌝ (x , y))
  II (x , y) = I (x , y) (i x x₀)

  III : Σᴹ A ≃ᴹ ssup (𝕄-root (A x₀)) (𝕄-forest (A x₀))
  III = 𝕗 , (λ σ → idtoeqᴹ _ _ (II σ))

  IV = Σᴹ A                                    ＝⟨ ⌜ 𝕄-＝-≃ ua _ _ ⌝⁻¹ III ⟩
       ssup (𝕄-root (A x₀)) (𝕄-forest (A x₀)) ＝⟨ 𝕄-η (A x₀) ⟩
       A x₀                                    ∎

𝕄-is-aflabby-Σ : aflabby 𝕄 𝓤
𝕄-is-aflabby-Σ P P-is-prop f = Σᴹ f , prop-indexed-sumᴹ P-is-prop

𝕄-is-ainjective-Σ : ainjective-type 𝕄 𝓤 𝓤
𝕄-is-ainjective-Σ = aflabby-types-are-ainjective 𝕄 𝕄-is-aflabby-Σ

\end{code}

Notice that we use Σᴹ (as well as Π) in the following definition of Πᴹ.

\begin{code}

Πᴹ : {X : 𝓤 ̇ } → (X → 𝕄) → 𝕄
Πᴹ {X} A = ssup
            (Π x ꞉ X , 𝕄-root (A x))
            (λ g → Σᴹ (λ x → 𝕄-forest (A x) (g x)))

_×ᴹ_ : 𝕄 → 𝕄 → 𝕄
M ×ᴹ N = Πᴹ (cases (λ (_ : 𝟙 {𝓤}) → M) (λ (_ : 𝟙 {𝓤}) → N))

\end{code}

Question. Is there a function Πᴹ of the above type that satisfies the
following equation? It seems that this possible for finite X. We guess
there isn't such a function for general X, including X = ℕ.

\begin{code}

Question =
   {X : 𝓤 ̇ }
 → Σ Πᴹ ꞉ ((X → 𝕄) → 𝕄)
        , ((A : X → 𝕄) → Πᴹ A ＝ ssup
                                  (Π x ꞉ X , 𝕄-root (A x))
                                  (λ g → Πᴹ (λ x → 𝕄-forest (A x) (g x))))
\end{code}

Here is the answer for X = 𝟚, up to equivalence:

\begin{code}

_×ᴹ'_ : 𝕄 → 𝕄 → 𝕄
(ssup X φ) ×ᴹ' (ssup Y γ) = ssup (X × Y) (λ (x , y) → (φ x) ×ᴹ' (γ y))

prop-indexed-productᴹ : {X : 𝓤 ̇ } {A : X → 𝕄}
                      → is-prop X
                      → (x₀ : X) → Πᴹ A ＝ A x₀
prop-indexed-productᴹ {X} {A} i x₀ = IV
 where
  𝕗 = (Π x ꞉ X , 𝕄-root (A x)) ≃⟨ prop-indexed-product fe i x₀ ⟩
      𝕄-root (A x₀)            ■

  remark : ⌜ 𝕗 ⌝ ＝ λ g → g x₀
  remark = refl

  I : (g : (x : X) → 𝕄-root (A x))
      (x : X) (p : x ＝ x₀)
    → 𝕄-forest (A x) (g x) ＝ 𝕄-forest (A x₀) (g x₀)
  I g x refl = refl

  II : (g : (x : X) → 𝕄-root (A x))
     → Σᴹ (λ x → 𝕄-forest (A x) (g x)) ＝ 𝕄-forest (A x₀) (⌜ 𝕗 ⌝ g)
  II g = Σᴹ (λ x → 𝕄-forest (A x) (g x))   ＝⟨ II₀ ⟩
         Σᴹ (λ x → 𝕄-forest (A x₀) (g x₀)) ＝⟨ II₁ ⟩
         𝕄-forest (A x₀) (g x₀)            ＝⟨ refl ⟩
         𝕄-forest (A x₀) (⌜ 𝕗 ⌝ g)         ∎
          where
           II₀ = ap Σᴹ (dfunext fe (λ x → I g x (i x x₀)))
           II₁ = prop-indexed-sumᴹ {X} {λ x → 𝕄-forest (A x₀) (g x₀)} i x₀

  III : Πᴹ A ≃ᴹ ssup (𝕄-root (A x₀)) (𝕄-forest (A x₀))
  III = 𝕗 , λ g → idtoeqᴹ _ _ (II g)

  IV : Πᴹ A ＝ A x₀
  IV = Πᴹ A                                   ＝⟨ ⌜ 𝕄-＝-≃ ua _ _ ⌝⁻¹ III ⟩
       ssup (𝕄-root (A x₀)) (𝕄-forest (A x₀)) ＝⟨ 𝕄-η (A x₀) ⟩
       A x₀                                   ∎

𝕄-is-aflabby-Π : aflabby 𝕄 𝓤
𝕄-is-aflabby-Π P P-is-prop f = Πᴹ f , prop-indexed-productᴹ P-is-prop

𝕄-is-ainjective-Π : ainjective-type 𝕄 𝓤 𝓤
𝕄-is-ainjective-Π = aflabby-types-are-ainjective 𝕄 𝕄-is-aflabby-Π

𝕄-is-ainjective : ainjective-type 𝕄 𝓤 𝓤
𝕄-is-ainjective = 𝕄-is-ainjective-Σ

\end{code}

It follows that 𝕄 has no non-trivial decidable properties unless weak
excluded middle holds, which also seems to be a new result.

\begin{code}

decomposition-of-𝕄-gives-WEM : decomposition 𝕄 → WEM 𝓤
decomposition-of-𝕄-gives-WEM =
 decomposition-of-ainjective-type-gives-WEM
  𝕄
  𝕄-is-ainjective

\end{code}
