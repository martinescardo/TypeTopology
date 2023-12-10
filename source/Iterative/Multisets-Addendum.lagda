Martin Escardo and Tom de Jong, July 2023.

Some constructions with iterative multisets.

 * The universe is a retract of the type 𝕄 of iterative multisets.
 * 𝕄 is algebraically injective.


\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

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

𝕄-is-not-set : ¬ (is-set 𝕄)
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
result.

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

\end{code}

Notice that we use Σᴹ (as well as Π) in the following definition of Πᴹ.

\begin{code}

Πᴹ : {X : 𝓤 ̇ } → (X → 𝕄) → 𝕄
Πᴹ {X} A = ssup
            (Π x ꞉ X , 𝕄-root (A x))
            (λ g → Σᴹ (λ x → 𝕄-forest (A x) (g x)))


_×ᴹ_ : 𝕄 → 𝕄 → 𝕄
M ×ᴹ N = Πᴹ (cases (λ (_ : 𝟙 {𝓤}) → M) (λ (_ : 𝟙 {𝓤}) → N))

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

𝕄-is-ainjective-Σ : ainjective-type 𝕄 𝓤 𝓤
𝕄-is-ainjective-Σ {X} {Y} j j-emb f = f\j , f\j-ext
 where
  A : (y : Y) → fiber j y → 𝕄
  A y (x , _) = f x

  f\j : Y → 𝕄
  f\j y = Σᴹ (A y)

  f\j-ext : f\j ∘ j ∼ f
  f\j-ext x = prop-indexed-sumᴹ
               {fiber j (j x)} {A (j x)} (j-emb (j x)) (x , refl)

𝕄-is-ainjective-Π : ainjective-type 𝕄 𝓤 𝓤
𝕄-is-ainjective-Π {X} {Y} j j-emb f = f/j , f/j-ext
 where
  A : (y : Y) → fiber j y → 𝕄
  A y (x , _) = f x

  f/j : Y → 𝕄
  f/j y = Πᴹ (A y)

  f/j-ext : f/j ∘ j ∼ f
  f/j-ext x = prop-indexed-productᴹ
               {fiber j (j x)} {A (j x)} (j-emb (j x)) (x , refl)

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

Added 9th December 2023.

We discuss "hereditarily finitely linearly ordered iterative
multisets". Notice that this is data, rather then property.

\begin{code}

open import Fin.Bishop
open import Fin.Type

hflo-data : 𝕄 → 𝓤 ̇
hflo-data (ssup X φ) = finite-linear-order X
                     × ((x : X) → hflo-data (φ x))

hflo-data-gives-finite-linear-order
 : (M : 𝕄)
 → hflo-data M
 → finite-linear-order (𝕄-root M)
hflo-data-gives-finite-linear-order (ssup x φ) = pr₁

𝕄-subtrees-have-hflo-data
 : (M : 𝕄)
 → hflo-data M
 → (x : 𝕄-root M) → hflo-data (𝕄-forest M x)
𝕄-subtrees-have-hflo-data (ssup x φ) = pr₂

ℍ : 𝓤⁺ ̇
ℍ = Σ M ꞉ 𝕄 , hflo-data M

ℍ-underlying-mset : ℍ → 𝕄
ℍ-underlying-mset = pr₁

hflo-structure : (H : ℍ) → hflo-data (ℍ-underlying-mset H)
hflo-structure = pr₂

\end{code}

Examples. We will use the superscript H to indicate elements of the
type ℍ.

\begin{code}

𝟘ᴹ-hflo-data : hflo-data 𝟘ᴹ
𝟘ᴹ-hflo-data = (0 , I) , (λ (x : 𝟘) → 𝟘-elim x)
 where
  I : 𝟘 {𝓤} ≃ 𝟘 {𝓤₀}
  I = one-𝟘-only

𝟘ᴴ : ℍ
𝟘ᴴ = 𝟘ᴹ , 𝟘ᴹ-hflo-data

open import UF.Equiv-FunExt

𝟘ᴴ-equality : (H : ℍ)
            → is-empty (𝕄-root (ℍ-underlying-mset H))
            → 𝟘ᴴ ＝ H
𝟘ᴴ-equality (ssup X φ , (0 , f) , ψ) e =
 to-Σ-＝
  ((to-𝕄-＝
     (eqtoid (ua 𝓤) 𝟘 X (≃-sym (f ● one-𝟘-only)) ,
      dfunext fe (λ (x : 𝟘) → 𝟘-elim x))) ,
    I)
 where
  I : {d : hflo-data (ssup X φ)} → d ＝ (zero , f) , ψ
  I {(zero , f') , ψ'} =
    to-Σ-＝
     (to-Σ-＝
       (refl ,
        to-subtype-＝
         (being-equiv-is-prop fe')
         (dfunext fe (λ x → 𝟘-elim (⌜ f ⌝ x)))) ,
      dfunext fe (λ x → 𝟘-elim (⌜ f ⌝ x)))
  I {(succ n' , f') , ψ'} = 𝟘-elim (e (⌜ f' ⌝⁻¹ 𝟎))
𝟘ᴴ-equality (ssup X φ , (succ n , f) , ψ) e = 𝟘-elim (e (⌜ f ⌝⁻¹ 𝟎))

𝟙ᴹ-hflo-data : hflo-data 𝟙ᴹ
𝟙ᴹ-hflo-data = (1 , I) , (λ ⋆ → 𝟘ᴹ-hflo-data)
 where
  I : 𝟙 {𝓤} ≃ 𝟘 {𝓤₀} + 𝟙 {𝓤₀}
  I = 𝟘-lneutral''

𝟙ᴴ : ℍ
𝟙ᴴ = 𝟙ᴹ , 𝟙ᴹ-hflo-data

𝟚ᴹ-hflo-data : hflo-data 𝟚ᴹ
𝟚ᴹ-hflo-data = 𝟙+𝟙-finite-linear-order ,
               dep-cases (λ _ → 𝟘ᴹ-hflo-data) (λ _ → 𝟙ᴹ-hflo-data)

𝟚ᴴ : ℍ
𝟚ᴴ = 𝟚ᴹ , 𝟚ᴹ-hflo-data

open import Fin.ArithmeticViaEquivalence

Σᴹ-hflo-data : {X : 𝓤 ̇ }
               (A : X → 𝕄)
             → finite-linear-order X
             → ((x : X) → hflo-data (A x))
             → hflo-data (Σᴹ A)
Σᴹ-hflo-data {X} A (n , f) A-hflo = (∑ a , h) , ψ
 where
  u : (x : X) → Σ m ꞉ ℕ , 𝕄-root (A x) ≃ Fin m
  u x = hflo-data-gives-finite-linear-order (A x) (A-hflo x)

  a : Fin n → ℕ
  a i = pr₁ (u (⌜ f ⌝⁻¹ i))

  b : (i : Fin n) → 𝕄-root (A (⌜ f ⌝⁻¹ i)) ≃ Fin (a i)
  b i = pr₂ (u (⌜ f ⌝⁻¹ i))

  h = (Σ x ꞉ X , 𝕄-root (A x))               ≃⟨ h₀ ⟩
      (Σ i ꞉ Fin n , 𝕄-root (A (⌜ f ⌝⁻¹ i))) ≃⟨ h₁ ⟩
      (Σ i ꞉ Fin n , Fin (a i))              ≃⟨ h₂ ⟩
      Fin (∑ a)                              ■
       where
        h₀ = ≃-sym (Σ-change-of-variable-≃ (λ x → 𝕄-root (A x)) (≃-sym f))
        h₁ = Σ-cong b
        h₂ = ≃-sym (∑-property a)

  ψ : ((x , y) : Σ x ꞉ X , 𝕄-root (A x)) → hflo-data (𝕄-forest (A x) y)
  ψ (x , y) = 𝕄-subtrees-have-hflo-data (A x) (A-hflo x) y

Πᴹ-hflo-data : {X : 𝓤 ̇ }
               (A : X → 𝕄)
             → finite-linear-order X
             → ((x : X) → hflo-data (A x))
             → hflo-data (Πᴹ A)
Πᴹ-hflo-data {X} A (n , f) A-hflo = (∏ fe a , h) , ψ
 where
  u : (x : X) → Σ m ꞉ ℕ , 𝕄-root (A x) ≃ Fin m
  u x = hflo-data-gives-finite-linear-order (A x) (A-hflo x)

  a : Fin n → ℕ
  a i = pr₁ (u (⌜ f ⌝⁻¹ i))

  b : (i : Fin n) → 𝕄-root (A (⌜ f ⌝⁻¹ i)) ≃ Fin (a i)
  b i = pr₂ (u (⌜ f ⌝⁻¹ i))

  h = (Π x ꞉ X , 𝕄-root (A x))               ≃⟨ h₀ ⟩
      (Π i ꞉ Fin n , 𝕄-root (A (⌜ f ⌝⁻¹ i))) ≃⟨ h₁ ⟩
      (Π i ꞉ Fin n , Fin (a i))              ≃⟨ h₂ ⟩
      Fin (∏ fe a)                              ■
       where
        h₀ = ≃-sym (Π-change-of-variable-≃ fe' (λ x → 𝕄-root (A x)) (≃-sym f))
        h₁ = Π-cong fe fe b
        h₂ = ≃-sym (∏-property fe a)

  v : (x : X) (y : 𝕄-root (A x)) → hflo-data (𝕄-forest (A x) y)
  v x = 𝕄-subtrees-have-hflo-data (A x) (A-hflo x)

  ψ : (g : Π x ꞉ X , 𝕄-root (A x)) → hflo-data (Σᴹ (λ x → 𝕄-forest (A x) (g x)))
  ψ g = Σᴹ-hflo-data (λ x → 𝕄-forest (A x) (g x)) (n , f) (λ x → v x (g x))

+ᴹ-hflo-data : (M N : 𝕄)
             → hflo-data M
             → hflo-data N
             → hflo-data (M +ᴹ N)
+ᴹ-hflo-data M N h k =
 Σᴹ-hflo-data (cases (λ (_ : 𝟙 {𝓤}) → M) (λ (_ : 𝟙 {𝓤}) → N))
  𝟙+𝟙-finite-linear-order
  (dep-cases (λ _ → h) (λ _ → k))

×ᴹ-hflo-data : (M N : 𝕄)
             → hflo-data M
             → hflo-data N
             → hflo-data (M ×ᴹ N)
×ᴹ-hflo-data M N h k =
 Πᴹ-hflo-data (cases (λ (_ : 𝟙 {𝓤}) → M) (λ (_ : 𝟙 {𝓤}) → N))
  𝟙+𝟙-finite-linear-order
  (dep-cases (λ _ → h) (λ _ → k))

_+ᴴ_ _×ᴴ_ : ℍ → ℍ → ℍ
(M , h) +ᴴ (N , k) = M +ᴹ N , +ᴹ-hflo-data M N h k
(M , h) ×ᴴ (N , k) = M ×ᴹ N , ×ᴹ-hflo-data M N h k

\end{code}

TODO. Define Σᴴ and Πᴴ. (Boilerplate.)

We now develop a representation of elements of ℍ for the sake of being
able to exhibit examples explicitly. Notice that this is like LISP's
type of S-expressions but without atoms.

\begin{code}

data 𝕊 : 𝓤₀ ̇ where
 []  : 𝕊
 _∷_ : 𝕊 → 𝕊 → 𝕊

infixr 3 _∷_

branch : (n : ℕ) → (Fin n → 𝕊) → 𝕊
branch 0        f = []
branch (succ n) f = f 𝟎 ∷ branch n (f ∘ suc)

to-𝕊' : (M : 𝕄) → hflo-data M → 𝕊
to-𝕊' (ssup X φ) ((n , f) , ψ) = branch n (IH ∘ ⌜ f ⌝⁻¹)
 where
  IH : X → 𝕊
  IH x = to-𝕊' (φ x) (ψ x)

to-𝕊 : ℍ → 𝕊
to-𝕊 = uncurry to-𝕊'

_::_ : ℍ → ℍ → ℍ
H :: (ssup X φ , (n , f) , ψ) =
 ssup (X + 𝟙) φ' , (succ n , f') , ψ'
 where
  φ' : X + 𝟙 → 𝕄
  φ' = cases φ (λ _ → ℍ-underlying-mset H)

  f' : X + 𝟙 ≃ Fin (succ n)
  f' = +-cong f (≃-refl 𝟙)

  ψ' : (y : X + 𝟙) → hflo-data (φ' y)
  ψ' = dep-cases ψ (λ _ → hflo-structure H)

from-𝕊 : 𝕊 → ℍ
from-𝕊 []      = 𝟘ᴴ
from-𝕊 (s ∷ t) = from-𝕊 s :: from-𝕊 t

to-𝕊-base : to-𝕊 𝟘ᴴ ＝ []
to-𝕊-base = refl

to-𝕊-step : (H K : ℍ) → to-𝕊 (H :: K) ＝ to-𝕊 H ∷ to-𝕊 K
to-𝕊-step H (ssup X φ , (n , f) , ψ) = refl

ε-𝕊 : to-𝕊 ∘ from-𝕊 ∼ id
ε-𝕊 []      = to-𝕊-base
ε-𝕊 (s ∷ t) =
 (to-𝕊 ∘ from-𝕊) (s ∷ t)           ＝⟨ refl ⟩
 to-𝕊 (from-𝕊 s :: from-𝕊 t)       ＝⟨ to-𝕊-step (from-𝕊 s) (from-𝕊 t) ⟩
 to-𝕊 (from-𝕊 s) ∷ to-𝕊 (from-𝕊 t) ＝⟨ ap₂ _∷_ (ε-𝕊 s) (ε-𝕊 t) ⟩
 s ∷ t                              ∎

from-𝕊-base : from-𝕊 [] ＝ 𝟘ᴴ
from-𝕊-base = refl

from-𝕊-step : (s t : 𝕊) → from-𝕊 (s ∷ t) ＝ from-𝕊 s :: from-𝕊 t
from-𝕊-step s t = refl

{-
η-𝕊 : from-𝕊 ∘ to-𝕊 ∼ id
η-𝕊 (ssup X φ , (0      , f) , ψ) = 𝟘ᴴ-equality _ ⌜ f ⌝
η-𝕊 (ssup X φ , (succ n , f) , ψ) = {!!}
 where
  IH : {!!}
  IH = {!!}

to-𝕊-is-equiv : is-equiv to-𝕊
to-𝕊-is-equiv = qinvs-are-equivs to-𝕊
                 (from-𝕊 , η-𝕊 , ε-𝕊)
-}
\end{code}

The length function counts the number of elements, including
repetitions. For multisets that are sets, it gives their
cardinality. The size function gives a kind of hereditary cardinality.

\begin{code}

open import Naturals.Addition renaming (_+_ to _∔_)

𝕊-length : 𝕊 → ℕ
𝕊-length [] = 0
𝕊-length (_ ∷ t) = succ (𝕊-length t)

𝕊-size : 𝕊 → ℕ
𝕊-size [] = 0
𝕊-size (s ∷ t) = succ (𝕊-size s ∔ 𝕊-size t)

{- TODO. Just for the sake of illustration.

ℍ-length : ℍ → ℕ
ℍ-length = {!!}

ℍ-size : ℍ → ℕ
ℍ-size = {!!}
-}

\end{code}

Examples.

\begin{code}

private
 t : ℍ → 𝕊 × ℕ × ℕ
 t H = S , 𝕊-length S , 𝕊-size S
  where
   S = to-𝕊 H

 𝟘ᴴ-explicitly : t 𝟘ᴴ ＝ [] , 0 , 0
 𝟘ᴴ-explicitly = refl

 𝟙ᴴ-explicitly : t 𝟙ᴴ ＝ ([] ∷ []) , 1 , 1
 𝟙ᴴ-explicitly = refl

 𝟚ᴴ-explicitly : t 𝟚ᴴ ＝ (([] ∷ []) ∷ [] ∷ []) , 2 , 3
 𝟚ᴴ-explicitly = refl

 𝟚ᴴ×𝟚ᴴ-explicitly : t (𝟚ᴴ ×ᴴ 𝟚ᴴ)
                 ＝ (([] ∷ [] ∷ []) ∷ ([] ∷ []) ∷ ([] ∷ []) ∷ [] ∷ []) ,
                    4 ,
                    8
 𝟚ᴴ×𝟚ᴴ-explicitly = refl

 𝟛ᴴ : ℍ
 𝟛ᴴ = 𝟚ᴴ +ᴴ 𝟙ᴴ

 𝟛ᴴ-explicitly : t 𝟛ᴴ ＝ (([] ∷ []) ∷ [] ∷ [] ∷ []) , 3 , 4
 𝟛ᴴ-explicitly = refl

 𝟛ᴴ×𝟛ᴴ-explicitly
  : t (𝟛ᴴ ×ᴴ 𝟛ᴴ)
  ＝ (([] ∷ [] ∷ []) ∷
     ([] ∷ []) ∷
     ([] ∷ []) ∷
     ([] ∷ []) ∷ [] ∷ [] ∷ ([] ∷ []) ∷ [] ∷ [] ∷ []) ,
    9 , 15
 𝟛ᴴ×𝟛ᴴ-explicitly = refl

 another-example
  : t ((𝟛ᴴ +ᴴ 𝟚ᴴ) ×ᴴ (𝟛ᴴ +ᴴ 𝟛ᴴ))
  ＝ (([] ∷ [] ∷ []) ∷
     ([] ∷ []) ∷
     ([] ∷ []) ∷
     ([] ∷ [] ∷ []) ∷
     ([] ∷ []) ∷
     ([] ∷ []) ∷
     ([] ∷ []) ∷
     [] ∷
     [] ∷
     ([] ∷ []) ∷
     [] ∷
     [] ∷
     ([] ∷ []) ∷
     [] ∷
     [] ∷
     ([] ∷ []) ∷
     [] ∷
     [] ∷
     ([] ∷ [] ∷ []) ∷
     ([] ∷ []) ∷
     ([] ∷ []) ∷
     ([] ∷ [] ∷ []) ∷
     ([] ∷ []) ∷
     ([] ∷ []) ∷ ([] ∷ []) ∷ [] ∷ [] ∷ ([] ∷ []) ∷ [] ∷ [] ∷ [])
    , 30 , 52
 another-example = refl

\end{code}

TODO. Indent the above examples to reflect their tree structure.
