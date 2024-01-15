Ayberk Tosun, 21 April 2022 (date completed)

Based on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Pi
open import UF.Size
open import MLTT.Spartan
open import Slice.Family
open import UF.Base
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.UA-FunExt
open import UF.Univalence

\end{code}

\begin{code}

module Locales.PatchLocale
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
       where

open import UF.Subsingletons
open import UF.Logic
open import UF.Equiv using (_≃_; logically-equivalent-props-give-is-equiv)
open import Locales.Frame pt fe

open AllCombinators pt fe
open PropositionalTruncation pt
open import Locales.Nucleus pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Compactness pt fe
open import Locales.Spectrality.SpectralLocale pt fe

\end{code}

We fix a locale `X` for the remainder of this module.

\begin{code}

open Locale

module PatchConstruction (X : Locale 𝓤 𝓥 𝓦) (σ : is-spectral X holds) where

 _≤_ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → Ω 𝓥
 U ≤ V = U ≤[ poset-of (𝒪 X) ] V

 open Meets _≤_

 _⊓_ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩
 U ⊓ V = U ∧[ 𝒪 X ] V

 ⋁_ : Fam 𝓦 ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩
 ⋁ S = ⋁[ 𝒪 X ] S

\end{code}

A nucleus is called perfect iff it is Scott-continuous:

\begin{code}

 is-perfect : (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
 is-perfect = is-scott-continuous (𝒪 X) (𝒪 X)

\end{code}

\begin{code}

 Perfect-Nucleus : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
 Perfect-Nucleus = Σ j ꞉ (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) ,
                    ((is-nucleus (𝒪 X) j ∧ is-perfect j) holds)

\end{code}

\begin{code}

 nucleus-of : Perfect-Nucleus → Nucleus (𝒪 X)
 nucleus-of (j , ζ , _) = j , ζ

\end{code}

\section{Poset of perfect nuclei}

\begin{code}

 _$_ : Perfect-Nucleus → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩
 (j , _) $ U = j U

\end{code}

\begin{code}

 perfect-nuclei-eq : (𝒿 𝓀 : Perfect-Nucleus) → 𝒿 $_ ＝ 𝓀 $_ → 𝒿 ＝ 𝓀
 perfect-nuclei-eq 𝒿 𝓀 = to-subtype-＝ γ
  where
   γ : (j : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
     → is-prop ((is-nucleus (𝒪 X) j ∧ is-perfect j) holds)
   γ j = holds-is-prop (is-nucleus (𝒪 X) j ∧ is-perfect j)

 perfect-nuclei-eq-inverse : (𝒿 𝓀 : Perfect-Nucleus) → 𝒿 ＝ 𝓀 → 𝒿 $_ ∼ 𝓀 $_
 perfect-nuclei-eq-inverse 𝒿 𝓀 p =
  transport (λ - → 𝒿 $_ ∼ - $_) p λ _ → refl
   where
    † : 𝒿 .pr₁ ＝ 𝓀 .pr₁
    † = pr₁ (from-Σ-＝ p)

\end{code}

Nuclei are ordered pointwise.

\begin{code}

 _≼₀_ : (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → Ω (𝓤 ⊔ 𝓥)
 _≼₀_ j k = Ɐ U ꞉ ⟨ 𝒪 X ⟩ , (j U) ≤[ poset-of (𝒪 X) ] (k U)

 _≼₁_ : Prenucleus (𝒪 X) → Prenucleus (𝒪 X) → Ω (𝓤 ⊔ 𝓥)
 𝒿 ≼₁ 𝓀 = pr₁ 𝒿 ≼₀ pr₁ 𝓀

 _≼_ : Perfect-Nucleus → Perfect-Nucleus → Ω (𝓤 ⊔ 𝓥)
 𝒿 ≼ 𝓀 = (λ x → 𝒿 $ x) ≼₀ (λ x → 𝓀 $ x)

\end{code}

\begin{code}

 ≼-is-reflexive : is-reflexive _≼_ holds
 ≼-is-reflexive 𝒿 U = ≤-is-reflexive (poset-of (𝒪 X)) (𝒿 $ U)

\end{code}

\begin{code}

 ≼-is-transitive : is-transitive _≼_ holds
 ≼-is-transitive 𝒾 𝒿 𝓀 φ ψ U = 𝒾 $ U ≤⟨ φ U ⟩ 𝒿 $ U ≤⟨ ψ U ⟩ 𝓀 $ U ■
  where
   open PosetReasoning (poset-of (𝒪 X))

\end{code}

\begin{code}

 ≼-is-preorder : is-preorder _≼_ holds
 ≼-is-preorder = ≼-is-reflexive , ≼-is-transitive

\end{code}

\begin{code}

 ≼-is-antisymmetric : is-antisymmetric _≼_
 ≼-is-antisymmetric {x = 𝒿} {𝓀} φ ψ = perfect-nuclei-eq 𝒿 𝓀 (dfunext fe γ)
  where
   γ : 𝒿 $_ ∼ 𝓀 $_
   γ U = ≤-is-antisymmetric (poset-of (𝒪 X)) (φ U) (ψ U)

\end{code}

\begin{code}

 patch-poset : Poset (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) (𝓤 ⊔ 𝓥)
 patch-poset = Perfect-Nucleus , _≼_ , ≼-is-preorder , ≼-is-antisymmetric

\end{code}

\section{Meet-semilattice of perfect nuclei}

\begin{code}

 _⋏₀_ : (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → (⟨ 𝒪 X ⟩  → ⟨ 𝒪 X ⟩)
 j ⋏₀ k = λ x → j x ∧[ 𝒪 X ] k x

 ⋏₀-inflationary : (j k : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
                 → is-inflationary (𝒪 X) j holds
                 → is-inflationary (𝒪 X) k holds
                 → is-inflationary (𝒪 X) (j ⋏₀ k) holds
 ⋏₀-inflationary j k p q U =
  ∧[ 𝒪 X ]-greatest (j U) (k U) U (p U) (q U)

 ⋏₀-idempotent : (j k : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
               → preserves-binary-meets (𝒪 X) (𝒪 X) j holds
               → preserves-binary-meets (𝒪 X) (𝒪 X) k holds
               → is-idempotent (𝒪 X) j holds
               → is-idempotent (𝒪 X) k holds
               → is-idempotent (𝒪 X) (j ⋏₀ k) holds
 ⋏₀-idempotent j k ζj ζk ϑj ϑk U =
  (j ⋏₀ k) ((j ⋏₀ k) U)                                          ＝⟨ refl ⟩ₚ
  (j ⋏₀ k) (j U ∧[ 𝒪 X ] k U)                                    ＝⟨ refl ⟩ₚ
  j (j U ∧[ 𝒪 X ] k U) ∧[ 𝒪 X ] k (j U ∧[ 𝒪 X ] k U)             ＝⟨ i    ⟩ₚ
  (j (j U) ∧[ 𝒪 X ] j (k U)) ∧[ 𝒪 X ] k (j U ∧[ 𝒪 X ] k U)       ＝⟨ ii   ⟩ₚ
  (j (j U) ∧[ 𝒪 X ] j (k U)) ∧[ 𝒪 X ] (k (j U) ∧[ 𝒪 X ] k (k U)) ≤⟨ iii  ⟩
  j (j U) ∧[ 𝒪 X ] (k (j U) ∧[ 𝒪 X ] k (k U))                    ≤⟨ iv   ⟩
  j (j U) ∧[ 𝒪 X ] k (k U)                                       ≤⟨ v    ⟩
  j U ∧[ 𝒪 X ] k (k U)                                           ≤⟨ vi   ⟩
  (j ⋏₀ k) U ■
   where
    open PosetReasoning (poset-of (𝒪 X))

    i   = ap (λ - → - ∧[ 𝒪 X ] k (j U ∧[ 𝒪 X ] k U)) (ζj (j U) (k U))
    ii  = ap (λ - → (j (j U) ∧[ 𝒪 X ] j (k U)) ∧[ 𝒪 X ] -) (ζk (j U) (k U))
    iii = ∧[ 𝒪 X ]-left-monotone (∧[ 𝒪 X ]-lower₁ (j (j U)) (j (k U)))
    iv  = ∧[ 𝒪 X ]-right-monotone (∧[ 𝒪 X ]-lower₂ (k (j U)) (k (k U)))
    v   = ∧[ 𝒪 X ]-left-monotone (ϑj U)
    vi  = ∧[ 𝒪 X ]-right-monotone (ϑk U)

 ⋏₀-is-meet-preserving : (j k : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
                       → preserves-binary-meets (𝒪 X) (𝒪 X) j holds
                       → preserves-binary-meets (𝒪 X) (𝒪 X) k holds
                       → preserves-binary-meets (𝒪 X) (𝒪 X) (j ⋏₀ k) holds
 ⋏₀-is-meet-preserving j k ζⱼ ζₖ U V =
  (j ⋏₀ k) (U ∧[ 𝒪 X ] V)                        ＝⟨ refl  ⟩
  j (U ∧[ 𝒪 X ] V) ∧[ 𝒪 X ] k (U ∧[ 𝒪 X ] V)     ＝⟨ i     ⟩
  (j U ∧[ 𝒪 X ] j V) ∧[ 𝒪 X ] k (U ∧[ 𝒪 X ] V)   ＝⟨ ii    ⟩
  (j U ∧[ 𝒪 X ] j V) ∧[ 𝒪 X ] (k U ∧[ 𝒪 X ] k V) ＝⟨ iii   ⟩
  j U ∧[ 𝒪 X ] ((j V ∧[ 𝒪 X ] k U) ∧[ 𝒪 X ] k V) ＝⟨ iv    ⟩
  j U ∧[ 𝒪 X ] ((k U ∧[ 𝒪 X ] j V) ∧[ 𝒪 X ] k V) ＝⟨ v     ⟩
  j U ∧[ 𝒪 X ] (k U ∧[ 𝒪 X ] (j V ∧[ 𝒪 X ] k V)) ＝⟨ vi     ⟩
  (j U ∧[ 𝒪 X ] k U) ∧[ 𝒪 X ] (j V ∧[ 𝒪 X ] k V) ＝⟨ refl  ⟩
  ((j ⋏₀ k) U) ∧[ 𝒪 X ] ((j ⋏₀ k) V)             ∎
   where
    †   = ∧[ 𝒪 X ]-is-associative (j U) (j V) (k U ∧[ 𝒪 X ] k V) ⁻¹
    ‡   = ap (λ - → j U ∧[ 𝒪 X ] -) (∧[ 𝒪 X ]-is-associative (j V) (k U) (k V))
    i   = ap (λ - → - ∧[ 𝒪 X ] k (U ∧[ 𝒪 X ] V)) (ζⱼ U V)
    ii  = ap (λ - → (j U ∧[ 𝒪 X ] j V) ∧[ 𝒪 X ] -) (ζₖ U V)
    iii = (j U ∧[ 𝒪 X ] j V) ∧[ 𝒪 X ] (k U ∧[ 𝒪 X ] k V)  ＝⟨ † ⟩
          j U ∧[ 𝒪 X ] (j V ∧[ 𝒪 X ] (k U ∧[ 𝒪 X ] k V))  ＝⟨ ‡ ⟩
          j U ∧[ 𝒪 X ] ((j V ∧[ 𝒪 X ] k U) ∧[ 𝒪 X ] k V)  ∎
    iv  = ap
           (λ - → j U ∧[ 𝒪 X ] (- ∧[ 𝒪 X ] k V))
           (∧[ 𝒪 X ]-is-commutative (j V) (k U))
    v   = ap (λ - → j U ∧[ 𝒪 X ] -) (∧[ 𝒪 X ]-is-associative (k U) (j V) (k V) ⁻¹)
    vi  = ∧[ 𝒪 X ]-is-associative (j U) (k U) (j V ∧[ 𝒪 X ] k V)

 _⋏₁_ : Nucleus (𝒪 X) → Nucleus (𝒪 X) → Nucleus (𝒪 X)
 𝒿@(j , jn) ⋏₁ 𝓀@(k , kn) = (j ⋏₀ k) , ⋏-𝓃₁ , ⋏-𝓃₂ , ⋏-𝓃₃
  where
   ⋏-𝓃₁ = ⋏₀-inflationary j k (𝓃₁ (𝒪 X) 𝒿) (𝓃₁ (𝒪 X) 𝓀)
   ⋏-𝓃₂ = ⋏₀-idempotent j k (𝓃₃ (𝒪 X) 𝒿) (𝓃₃ (𝒪 X) 𝓀) (𝓃₂ (𝒪 X) 𝒿) (𝓃₂ (𝒪 X) 𝓀)
   ⋏-𝓃₃ = ⋏₀-is-meet-preserving j k (𝓃₃ (𝒪 X) 𝒿) (𝓃₃ (𝒪 X) 𝓀)

 ⋏₀-perfect : (j k : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
            → let P = poset-of (𝒪 X) in
              is-monotonic P P j holds
            → is-monotonic P P k holds
            → is-perfect j holds
            → is-perfect k holds
            → is-perfect (j ⋏₀ k) holds
 ⋏₀-perfect j k μj μk ζj ζk S δ = β , γ
  where
   open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
   open PosetReasoning (poset-of (𝒪 X))
   open JoinNotation (λ S → ⋁[ 𝒪 X ] S)

   β : ((j ⋏₀ k) (⋁[ 𝒪 X ] S) is-an-upper-bound-of ⁅ (j ⋏₀ k) s ∣ s ε S ⁆) holds
   β l = (j ⋏₀ k) (S [ l ])                       ＝⟨ refl ⟩ₚ
         j (S [ l ]) ∧[ 𝒪 X ] k (S [ l ])         ≤⟨ i    ⟩
         j (⋁[ 𝒪 X ] S) ∧[ 𝒪 X ] k (S [ l ])      ≤⟨ ii   ⟩
         j (⋁[ 𝒪 X ] S) ∧[ 𝒪 X ] k (⋁[ 𝒪 X ] S)   ＝⟨ refl ⟩ₚ
         (j ⋏₀ k) (⋁[ 𝒪 X ] S)                    ■
          where
           †  = ⋁[ 𝒪 X ]-upper S l
           ‡  = ⋁[ 𝒪 X ]-upper S l
           i  = ∧[ 𝒪 X ]-left-monotone  (μj (S [ l ] , ⋁[ 𝒪 X ] S) †)
           ii = ∧[ 𝒪 X ]-right-monotone (μk (S [ l ] , ⋁[ 𝒪 X ] S) ‡)

   γ : (Ɐ (u , _) ꞉ upper-bound ⁅ (j ⋏₀ k) s ∣ s ε S ⁆ ,
         (j ⋏₀ k) (⋁[ 𝒪 X ] S) ≤[ poset-of (𝒪 X) ] u) holds
   γ 𝓊@(u , _) =
    (j ⋏₀ k) (⋁[ 𝒪 X ] S)                                           ＝⟨ refl ⟩ₚ
    j (⋁[ 𝒪 X ] S) ∧[ 𝒪 X ] k (⋁[ 𝒪 X ] S)                          ≤⟨ i    ⟩
    (⋁[ 𝒪 X ] ⁅ j s ∣ s ε S ⁆) ∧[ 𝒪 X ] k (⋁[ 𝒪 X ] S)              ≤⟨ ii   ⟩
    (⋁[ 𝒪 X ] ⁅ j s ∣ s ε S ⁆) ∧[ 𝒪 X ] (⋁[ 𝒪 X ] ⁅ k s ∣ s ε S ⁆)  ＝⟨ iii  ⟩ₚ
    ⋁[ 𝒪 X ] ⁅ 𝒮 m n ∣ (m , n) ∶ I × I ⁆                            ≤⟨ iv   ⟩
    ⋁⟨ i ∶ I ⟩ j (S [ i ]) ∧[ 𝒪 X ] k (S [ i ])                     ≤⟨ v    ⟩
    u                                                               ■
     where
      I  = index S

      𝒮 : I → I → ⟨ 𝒪 X ⟩
      𝒮 m n = j (S [ m ]) ∧[ 𝒪 X ] k (S [ n ])

      † : j (⋁[ 𝒪 X ] S) ＝ ⋁[ 𝒪 X ] ⁅ j s ∣ s ε S ⁆
      † = scott-continuous-join-eq (𝒪 X) (𝒪 X) j ζj S δ

      ‡ : k (⋁[ 𝒪 X ] S) ＝ ⋁[ 𝒪 X ] ⁅ k s ∣ s ε S ⁆
      ‡ = scott-continuous-join-eq (𝒪 X) (𝒪 X) k ζk S δ

      ※ : ((⋁⟨ i ∶ I ⟩ j (S [ i ]) ∧[ 𝒪 X ] k (S [ i ]))
            is-an-upper-bound-of
           ⁅ 𝒮 m n ∣ (m , n) ∶ I × I ⁆) holds
      ※ (m , n) = ∥∥-rec (holds-is-prop P) ε (pr₂ δ m n)
       where
        P : Ω 𝓥
        P = 𝒮 m n
             ≤[ poset-of (𝒪 X) ]
            (⋁⟨ i ∶ I ⟩ j (S [ i ]) ∧[ 𝒪 X ] k (S [ i ]))

        ε : Σ i ꞉ I , ((S [ m ]) ≤[ poset-of (𝒪 X) ] (S [ i ])
                    ∧ ((S [ n ]) ≤[ poset-of (𝒪 X) ] (S [ i ]))) holds
          → P holds
        ε (i , p , q) =
         𝒮 m n                                        ＝⟨ refl ⟩ₚ
         j (S [ m ]) ∧[ 𝒪 X ] k (S [ n ])             ≤⟨ ♢    ⟩
         j (S [ i ]) ∧[ 𝒪 X ] k (S [ n ])             ≤⟨ ♥    ⟩
         j (S [ i ]) ∧[ 𝒪 X ] k (S [ i ])             ≤⟨ ♠    ⟩
         ⋁⟨ i ∶ I ⟩ j (S [ i ]) ∧[ 𝒪 X ] k (S [ i ])  ■
          where
           ♢ = ∧[ 𝒪 X ]-left-monotone  (μj (S [ m ] , S [ i ]) p)
           ♥ = ∧[ 𝒪 X ]-right-monotone (μk (S [ n ] , S [ i ]) q)
           ♠ = ⋁[ 𝒪 X ]-upper ⁅ (j (S [ i ])) ∧[ 𝒪 X ] (k (S [ i ])) ∣ i ∶ I ⁆ i

      i   = ∧[ 𝒪 X ]-left-monotone  (reflexivity+ (poset-of (𝒪 X)) †)
      ii  = ∧[ 𝒪 X ]-right-monotone (reflexivity+ (poset-of (𝒪 X)) ‡)

      iii = distributivity+ (𝒪 X) ⁅ j s ∣ s ε S ⁆ ⁅ k s ∣ s ε S ⁆


      iv  = ⋁[ 𝒪 X ]-least
             ⁅ 𝒮 m n ∣ (m , n) ∶ I × I ⁆
             ((⋁⟨ i ∶ I ⟩ j (S [ i ]) ∧[ 𝒪 X ] k (S [ i ])) , ※)

      v   = ⋁[ 𝒪 X ]-least ⁅ j (S [ i ]) ∧[ 𝒪 X ] k (S [ i ]) ∣ i ∶ I ⁆ 𝓊

 _⋏_ : Perfect-Nucleus → Perfect-Nucleus → Perfect-Nucleus
 (𝒿 , νj , ζj) ⋏ (𝓀 , νk , ζk) = pr₁ Σ-assoc (((𝒿 , νj) ⋏₁ (𝓀 , νk)) , γ)
  where
   μj = nuclei-are-monotone (𝒪 X) (𝒿 , νj)
   μk = nuclei-are-monotone (𝒪 X) (𝓀 , νk)

   γ : is-perfect (𝒿 ⋏₀ 𝓀) holds
   γ = ⋏₀-perfect 𝒿 𝓀 μj μk ζj ζk

 idₙ : Perfect-Nucleus
 idₙ = id , pr₂ (identity-nucleus (𝒪 X)) , ζ
  where
   ζ : is-perfect id holds
   ζ S δ = ⋁[ 𝒪 X ]-upper S , ⋁[ 𝒪 X ]-least S

\end{code}

\section{Construction of the join}

The construction of the join is the nontrivial component of this development.
Given a family `S ∶＝ { fᵢ : A → A | i ∶ I }` of endofunctions on some type `A`,
and a list `i₀, …, iₙ` of indices (of type `I`), the function `sequence gives
the composition of all `fᵢₙ ∘ ⋯ ∘ fᵢ₀`:

\begin{code}

 sequence : {A : 𝓤 ̇ } → (S : Fam 𝓦 (A → A)) → List (index S) → A → A
 sequence S []       = id
 sequence S (i ∷ is) = sequence S is ∘ S [ i ]

\end{code}

Using `sequence`, we define the following functio that will help us “directify”
a given family:

\begin{code}

 𝔡𝔦𝔯 : {A : 𝓤 ̇ } (S : Fam 𝓦 (A → A)) → Fam 𝓦 (A → A)
 𝔡𝔦𝔯 S = List (index S) , sequence S

\end{code}

The first lemma we prove about `𝔡𝔦𝔯` is the fact that, given a family

```
S ∶＝ { jᵢ : 𝒪 X → 𝒪 X ∣ i ∶ I }
```

of prenuclei, `sequence S is` is a prenuclei for any given list `is : List I` of
indices.

\begin{code}

 𝔡𝔦𝔯-prenuclei : (K : Fam 𝓦 (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩))
                → (Ɐ i ꞉ index K , is-prenucleus (𝒪 X) (K [ i ])) holds
                → (Ɐ is ꞉ List (index K) , is-prenucleus (𝒪 X) (𝔡𝔦𝔯 K [ is ])) holds
 𝔡𝔦𝔯-prenuclei K ϑ []       = pr₂ (nucleus-pre (𝒪 X) (identity-nucleus (𝒪 X)))
 𝔡𝔦𝔯-prenuclei K ϑ (j ∷ js) = n₁ , n₂
  where
   open PosetReasoning (poset-of (𝒪 X))

   IH = 𝔡𝔦𝔯-prenuclei K ϑ js

   n₁ : is-inflationary (𝒪 X) (𝔡𝔦𝔯 K [ j ∷ js ]) holds
   n₁ x = x                             ≤⟨ i    ⟩
          (K [ j ]) x                   ≤⟨ ii   ⟩
          (𝔡𝔦𝔯 K [ js ]) ((K [ j ]) x)  ＝⟨ refl ⟩ₚ
          (𝔡𝔦𝔯 K [ j ∷ js ]) x          ■
           where
            i  = pr₁ (ϑ j) x
            ii = pr₁ IH ((K [ j ]) x)

   n₂ : preserves-binary-meets (𝒪 X) (𝒪 X) (𝔡𝔦𝔯 K [ j ∷ js ]) holds
   n₂ x y = (𝔡𝔦𝔯 K [ j ∷ js ]) (x ∧[ 𝒪 X ] y)                   ＝⟨ refl ⟩
            (𝔡𝔦𝔯 K [ js ]) ((K [ j ]) (x ∧[ 𝒪 X ] y))           ＝⟨ i    ⟩
            (𝔡𝔦𝔯 K [ js ]) ((K [ j ]) x ∧[ 𝒪 X ] (K [ j ]) y)   ＝⟨ ii   ⟩
            (𝔡𝔦𝔯 K [ j ∷ js ]) x ∧[ 𝒪 X ] (𝔡𝔦𝔯 K [ j ∷ js ]) y  ∎
             where
              i   = ap (𝔡𝔦𝔯 K [ js ]) (pr₂ (ϑ j) x y)
              ii  = pr₂ IH ((K [ j ]) x) ((K [ j ]) y)

\end{code}

\begin{code}

 _^** : Fam 𝓦 (Nucleus (𝒪 X)) → Fam 𝓦 (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
 _^** K = 𝔡𝔦𝔯 ⁅ k ∣ (k , _) ε K ⁆

 ^**-functorial : (K : Fam 𝓦 (Nucleus (𝒪 X)))
                → (is js : List (index K))
                →  K ^** [ is ++ js ] ∼ K ^** [ js ] ∘ K ^** [ is ]
 ^**-functorial K []       js _ = refl
 ^**-functorial K (i ∷ is) js x = ^**-functorial K is js ((K [ i ]) .pr₁ x)

 _^* : Fam 𝓦 (Nucleus (𝒪 X)) → Fam 𝓦 (Prenucleus (𝒪 X))
 _^* K = (List (index K)) , α
  where
   α : List (index K) → Prenucleus (𝒪 X)
   α is = 𝔡𝔦𝔯 ⁅ k ∣ (k , _) ε K ⁆ [ is ]
        , 𝔡𝔦𝔯-prenuclei ⁅ k ∣ (k , _) ε K ⁆ † is
    where
     † : (i : index K) → is-prenucleus (𝒪 X) (pr₁ (K [ i ])) holds
     † = pr₂ ∘ nucleus-pre (𝒪 X) ∘ (λ - → K [ - ])

\end{code}

\begin{code}

 ^*-inhabited : (K : Fam 𝓦 (Nucleus (𝒪 X))) → ∥ index (K ^*) ∥
 ^*-inhabited K = ∣ [] ∣

 ^*-upwards-directed : (K : Fam 𝓦 (Nucleus (𝒪 X)))
                     → (is : index (K ^*))
                     → (js : index (K ^*))
                     → Σ ks ꞉ index (K ^*) ,
                          (((K ^* [ is ]) ≼₁ (K ^* [ ks ]))
                        ∧ ((K ^* [ js ]) ≼₁ (K ^* [ ks ])))
                       holds
 ^*-upwards-directed K is js = (is ++ js) , β , γ
  where
   open PosetReasoning (poset-of (𝒪 X))
   open PrenucleusApplicationSyntax (𝒪 X) using (_$ₚ_)

   β : (((K ^*) [ is ]) ≼₁ (K ^* [ is ++ js ])) holds
   β U = K ^* [ is ] $ₚ U                 ≤⟨ i  ⟩
         K ^* [ js ] $ₚ K ^* [ is ] $ₚ U  ＝⟨ ii ⟩ₚ
         K ^* [ is ++ js ] $ₚ U           ■
          where
           i  = prenucleus-property₂ (𝒪 X) (K ^* [ js ]) (K ^* [ is ]) U
           ii = ^**-functorial K is js U ⁻¹

   γ : ((K ^* [ js ]) ≼₁ (K ^* [ is ++ js ])) holds
   γ U = K ^* [ js ] $ₚ U                 ≤⟨ i  ⟩
         K ^* [ js ] $ₚ K ^* [ is ] $ₚ U  ＝⟨ ii ⟩ₚ
         K ^* [ is ++ js ] $ₚ U           ■
          where
           i  = prenucleus-property₁ (𝒪 X) (K ^* [ js ]) (K ^* [ is ]) U
           ii = ^**-functorial K is js U ⁻¹

\end{code}

\begin{code}

 ^*-scott-continuous : (K : Fam 𝓦 (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩))
                     → (Ɐ i ꞉ index K ,
                         is-scott-continuous (𝒪 X) (𝒪 X) (K [ i ])) holds
                     → (Ɐ is ꞉ List (index K) ,
                         is-scott-continuous (𝒪 X) (𝒪 X) (𝔡𝔦𝔯 K [ is ])) holds
 ^*-scott-continuous K ϑ []       = id-is-scott-continuous (𝒪 X)
 ^*-scott-continuous K ϑ (i ∷ is) = ∘-of-scott-cont-is-scott-cont (𝒪 X) (𝒪 X) (𝒪 X)
                                     (𝔡𝔦𝔯 K [ is ])
                                     (K [ i ])
                                     (^*-scott-continuous K ϑ is)
                                     (ϑ i)

\end{code}

\begin{code}

 joins-commute : (J : Fam 𝓦 (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)) (S : Fam 𝓦 ⟨ 𝒪 X ⟩)
               → ⋁ ⁅ ⋁ ⁅ α U ∣ α ε 𝔡𝔦𝔯 J ⁆ ∣ U ε S ⁆
               ＝ ⋁ ⁅ ⋁ ⁅ α U ∣ U ε S ⁆ ∣ α ε 𝔡𝔦𝔯 J ⁆
 joins-commute J S =
  ⋁ ⁅ ⋁ ⁅ α U ∣ α ε 𝔡𝔦𝔯 J ⁆ ∣ U ε S ⁆                                ＝⟨ i   ⟩
  ⋁ ⁅ (𝔡𝔦𝔯 J [ j ]) (S [ i ]) ∣ (i , j) ∶ index S × index (𝔡𝔦𝔯 J) ⁆  ＝⟨ ii  ⟩
  ⋁ ⁅ (𝔡𝔦𝔯 J [ j ]) (S [ i ]) ∣ (j , i) ∶ index (𝔡𝔦𝔯 J) × index S ⁆  ＝⟨ iii ⟩
  ⋁ ⁅ ⋁ ⁅ α U ∣ U ε S ⁆ ∣ α ε 𝔡𝔦𝔯 J ⁆                                ∎
   where
    T = ⁅ (𝔡𝔦𝔯 J [ j ]) (S [ i ]) ∣ (i , j) ∶ index S × index (𝔡𝔦𝔯 J) ⁆
    U = ⁅ (𝔡𝔦𝔯 J [ j ]) (S [ i ]) ∣ (j , i) ∶ index (𝔡𝔦𝔯 J) × index S ⁆

    † = ⋁[ 𝒪 X ]-least T (⋁ U , λ (i , j) → ⋁[ 𝒪 X ]-upper U (j , i))
    ‡ = ⋁[ 𝒪 X ]-least U (⋁ T , λ (j , i) → ⋁[ 𝒪 X ]-upper T (i , j))

    i   = (⋁[ 𝒪 X ]-iterated-join (index S) κ λ i j → (𝔡𝔦𝔯 J [ j ]) (S [ i ])) ⁻¹
           where
            κ : index S → 𝓦 ̇
            κ = λ _ → index (𝔡𝔦𝔯 J)
    ii  = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
    iii = ⋁[ 𝒪 X ]-iterated-join
           (index (𝔡𝔦𝔯 J))
           (λ _ → index S)
           λ j i → (𝔡𝔦𝔯 J [ j ]) (S [ i ])

\end{code}

The definition of the join:

\begin{code}

 join : Fam 𝓦 (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩
 join K = λ U → ⋁ ⁅ α U ∣ α ε 𝔡𝔦𝔯 K ⁆

 ⋁ₙ : Fam 𝓦 Perfect-Nucleus → Perfect-Nucleus
 ⋁ₙ K = join K₀ , (n₁ , n₂ , n₃) , γ
  where
   open PosetReasoning (poset-of (𝒪 X))
   open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

   K₀ : Fam 𝓦 (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
   K₀ = ⁅ pr₁ j ∣ j ε K ⁆

   ϑ : (Ɐ i ꞉ index K₀ , is-scott-continuous (𝒪 X) (𝒪 X) (K₀ [ i ])) holds
   ϑ i = pr₂ (pr₂ (K [ i ]))

   K₁ : Fam 𝓦 (Nucleus (𝒪 X))
   K₁ = ⁅ nucleus-of k ∣ k ε K ⁆

   n₁ : is-inflationary (𝒪 X) (join K₀) holds
   n₁ U = ⋁[ 𝒪 X ]-upper ⁅ α U ∣ α ε 𝔡𝔦𝔯 K₀ ⁆ []

   n₂ : is-idempotent (𝒪 X) (join K₀) holds
   n₂ U =
    join K₀ (join K₀ U)                                             ＝⟨ refl ⟩ₚ
    ⋁ ⁅ α (⋁ ⁅ β U ∣ β ε 𝔡𝔦𝔯 K₀ ⁆) ∣ α ε 𝔡𝔦𝔯 K₀ ⁆                   ＝⟨ i    ⟩ₚ
    ⋁ ⁅ ⋁ ⁅ α (β U) ∣ β ε 𝔡𝔦𝔯 K₀ ⁆ ∣ α ε 𝔡𝔦𝔯 K₀ ⁆                   ＝⟨ ii   ⟩ₚ
    ⋁ ⁅ (𝔡𝔦𝔯 K₀ [ js ]) ((𝔡𝔦𝔯 K₀ [ is ]) U) ∣ (js , is) ∶ (_ × _) ⁆ ≤⟨ iii  ⟩
    join K₀ U                                                       ■
     where
      S   = ⁅ (𝔡𝔦𝔯 K₀ [ j ]) ((𝔡𝔦𝔯 K₀ [ i ]) U) ∣ (j , i) ∶ (_ × _) ⁆

      † : ((join K₀ U) is-an-upper-bound-of S) holds
      † (js , is) =
       transport
        (λ - →  (- ≤[ poset-of (𝒪 X) ] (join K₀ U)) holds)
        (^**-functorial K₁ is js U)
        (⋁[ 𝒪 X ]-upper _ (is ++ js))

      δ : is-directed (𝒪 X) ⁅ pr₁ α U ∣ α ε K₁ ^* ⁆ holds
      δ = (^*-inhabited K₁) , γ
           where
            γ : _
            γ is js = ∣ ks , υ₁ , υ₂ ∣
             where
              ks = pr₁ (^*-upwards-directed K₁ is js)
              υ₁ = pr₁ (pr₂ (^*-upwards-directed K₁ is js)) U
              υ₂ = pr₂ (pr₂ (^*-upwards-directed K₁ is js)) U

      i   = ap
             (λ - → ⋁ (index (𝔡𝔦𝔯 K₀) , -))
             (dfunext fe λ is →
               scott-continuous-join-eq (𝒪 X) (𝒪 X)
                (𝔡𝔦𝔯 K₀ [ is ])
                (^*-scott-continuous K₀ ϑ is) ⁅ β U ∣ β ε 𝔡𝔦𝔯 K₀ ⁆ δ)
      ii  = ⋁[ 𝒪 X ]-iterated-join
             (index (𝔡𝔦𝔯 K₀))
             (λ _ → index (K₁ ^*))
             (λ j i → (K₁ ^* [ j ]) .pr₁ ((K₁ ^* [ i ]) .pr₁ U)) ⁻¹
      iii = ⋁[ 𝒪 X ]-least S (join K₀ U , †)

   μ : (is : List (index K₀)) → preserves-binary-meets (𝒪 X) (𝒪 X) (𝔡𝔦𝔯 K₀ [ is ]) holds
   μ is = pr₂ (𝔡𝔦𝔯-prenuclei K₀ (λ i → pr₂ (nucleus-pre (𝒪 X) (K₁ [ i ]))) is)

   n₃ : preserves-binary-meets (𝒪 X) (𝒪 X) (join K₀) holds
   n₃ U V =
    join K₀ (U ∧[ 𝒪 X ] V)                                                 ＝⟨ refl ⟩
    ⋁ ⁅ α (U ∧[ 𝒪 X ] V) ∣ α ε 𝔡𝔦𝔯 K₀ ⁆                                    ＝⟨ i    ⟩
    ⋁ ⁅ (α U) ∧[ 𝒪 X ] (α V) ∣ α ε 𝔡𝔦𝔯 K₀ ⁆                                ＝⟨ ii   ⟩
    ⋁ ⁅ (𝔡𝔦𝔯 K₀ [ is ]) U ∧[ 𝒪 X ] (𝔡𝔦𝔯 K₀ [ js ]) V ∣ (is , js) ∶ _ × _ ⁆ ＝⟨ iii  ⟩
    join K₀ U ∧[ 𝒪 X ] join K₀ V                                           ∎
     where
      S = ⁅ (𝔡𝔦𝔯 K₀ [ is ]) U ∧[ 𝒪 X ] (𝔡𝔦𝔯 K₀ [ js ]) V ∣ (is , js) ∶ _ × _ ⁆
      † : ((⋁ ⁅ (α U) ∧[ 𝒪 X ] (α V) ∣ α ε 𝔡𝔦𝔯 K₀ ⁆)
           ≤[ poset-of (𝒪 X) ]
           (⋁ ⁅ (𝔡𝔦𝔯 K₀ [ is ]) U ∧[ 𝒪 X ] (𝔡𝔦𝔯 K₀ [ js ]) V ∣ (is , js) ∶ _ × _ ⁆))
          holds
      † = ⋁[ 𝒪 X ]-least ⁅ (α U) ∧[ 𝒪 X ] (α V) ∣ α ε 𝔡𝔦𝔯 K₀ ⁆ (_ , ※)
           where
            ※ : _
            ※ i = ⋁[ 𝒪 X ]-upper S (i , i)

      ψ : ((⋁ ⁅ (α U) ∧[ 𝒪 X ] (α V) ∣ α ε 𝔡𝔦𝔯 K₀ ⁆) is-an-upper-bound-of S) holds
      ψ (is , js) =
       S [ is , js ]                                  ＝⟨ refl ⟩ₚ
       (𝔡𝔦𝔯 K₀ [ is ]) U ∧[ 𝒪 X ] (𝔡𝔦𝔯 K₀ [ js ]) V   ≤⟨ ♠    ⟩
       (𝔡𝔦𝔯 K₀ [ ks ]) U ∧[ 𝒪 X ] (𝔡𝔦𝔯 K₀ [ js ]) V   ≤⟨ ♣    ⟩
       (𝔡𝔦𝔯 K₀ [ ks ]) U ∧[ 𝒪 X ] (𝔡𝔦𝔯 K₀ [ ks ]) V   ≤⟨ ♦    ⟩
       ⋁ ⁅ (α U) ∧[ 𝒪 X ] (α V) ∣ α ε 𝔡𝔦𝔯 K₀ ⁆        ■
        where
         ks = pr₁ (^*-upwards-directed K₁ is js)

         ♠ = ∧[ 𝒪 X ]-left-monotone (pr₁ (pr₂ (^*-upwards-directed K₁ is js)) U)
         ♣ = ∧[ 𝒪 X ]-right-monotone (pr₂ (pr₂ (^*-upwards-directed K₁ is js)) V)
         ♦ = ⋁[ 𝒪 X ]-upper ⁅ (α U) ∧[ 𝒪 X ] (α V) ∣ α ε 𝔡𝔦𝔯 K₀ ⁆ ks

      ‡ : ((⋁ ⁅ (𝔡𝔦𝔯 K₀ [ is ]) U ∧[ 𝒪 X ] (𝔡𝔦𝔯 K₀ [ js ]) V ∣ (is , js) ∶ _ × _ ⁆)
            ≤[ poset-of (𝒪 X) ]
           (⋁ ⁅ (α U) ∧[ 𝒪 X ] (α V) ∣ α ε 𝔡𝔦𝔯 K₀ ⁆)) holds
      ‡ = ⋁[ 𝒪 X ]-least
           (⁅ (𝔡𝔦𝔯 K₀ [ is ]) U ∧[ 𝒪 X ] (𝔡𝔦𝔯 K₀ [ js ]) V ∣ (is , js) ∶ _ × _ ⁆)
           (_ , ψ)

      i   = ap (λ - → ⋁ (index (𝔡𝔦𝔯 K₀) , -)) (dfunext fe λ is → μ is U V)
      ii  = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
      iii = distributivity+ (𝒪 X) ⁅ α U ∣ α ε 𝔡𝔦𝔯 K₀ ⁆ ⁅ β V ∣ β ε 𝔡𝔦𝔯 K₀ ⁆ ⁻¹

   γ : is-perfect (join K₀) holds
   γ S δ = transport
            (λ - → (- is-lub-of T) holds)
            (※ ⁻¹)
            (⋁[ 𝒪 X ]-upper T , ⋁[ 𝒪 X ]-least T)
    where
     T = ⁅ join K₀ s ∣ s ε S ⁆
     ※ : join K₀ (⋁ S) ＝ ⋁ ⁅ join K₀ s ∣ s ε S ⁆
     ※ = join K₀ (⋁ S)                         ＝⟨ refl ⟩
         ⋁ ⁅ α (⋁ S) ∣ α ε 𝔡𝔦𝔯 K₀ ⁆            ＝⟨ i    ⟩
         ⋁ ⁅ ⋁ ⁅ α s ∣ s ε S ⁆ ∣ α ε 𝔡𝔦𝔯 K₀ ⁆  ＝⟨ ii   ⟩
         ⋁ ⁅ join K₀ s ∣ s ε S ⁆               ∎
          where
           †  = dfunext fe λ is →
                 scott-continuous-join-eq (𝒪 X) (𝒪 X)
                  (𝔡𝔦𝔯 K₀ [ is ]) (^*-scott-continuous K₀ ϑ is) S δ

           i  = ap (λ - → ⋁ (index (𝔡𝔦𝔯 K₀) , -)) †
           ii = joins-commute K₀ S ⁻¹

\end{code}

## The definition of the patch locale

\begin{code}

 𝟏ₚ : Perfect-Nucleus
 𝟏ₚ = 𝟏 , (n₁ , n₂ , n₃) , ζ
       where
        open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

        𝟏 = λ _ → 𝟏[ 𝒪 X ]

        n₁ : is-inflationary (𝒪 X) 𝟏 holds
        n₁ = 𝟏-is-top (𝒪 X)

        n₂ : is-idempotent (𝒪 X) 𝟏 holds
        n₂ _ = ≤-is-reflexive (poset-of (𝒪 X)) 𝟏[ 𝒪 X ]

        n₃ : preserves-binary-meets (𝒪 X) (𝒪 X) 𝟏 holds
        n₃ _ _ = ∧[ 𝒪 X ]-is-idempotent 𝟏[ 𝒪 X ]

        ζ : is-perfect 𝟏 holds
        ζ S δ = † , ‡
         where
          P = poset-of (𝒪 X)

          † : (𝟏 (⋁[ 𝒪 X ] S) is-an-upper-bound-of ⁅ 𝟏[ 𝒪 X ] ∣ _ ε S ⁆) holds
          † i = 𝟏-is-top (𝒪 X) 𝟏[ 𝒪 X ]

          ‡ : (Ɐ (u , _) ꞉ upper-bound ⁅ 𝟏[ 𝒪 X ] ∣ _ ε S ⁆ , 𝟏[ 𝒪 X ] ≤[ P ] u) holds
          ‡ (u , φ) = ∥∥-rec (holds-is-prop (𝟏[ 𝒪 X ] ≤[ P ] u)) φ (pr₁ δ)

 𝟏ₚ-is-top : Meets.is-top (λ 𝒿 𝓀 → 𝒿 ≼ 𝓀) 𝟏ₚ holds
 𝟏ₚ-is-top 𝒿 U = 𝟏-is-top (𝒪 X) (𝒿 $ U)

 ⋏-is-meet : (Ɐ (𝒿 , 𝓀) ꞉ Perfect-Nucleus × Perfect-Nucleus ,
               Meets._is-glb-of_ _≼_ (𝒿 ⋏ 𝓀) (𝒿 , 𝓀)) holds
 ⋏-is-meet (𝒿 , 𝓀) = β , γ
  where
   β : (Meets._is-a-lower-bound-of_ _≼_ (𝒿 ⋏ 𝓀)) (𝒿 , 𝓀) holds
   β = (λ U → ∧[ 𝒪 X ]-lower₁ (𝒿 $ U) (𝓀 $ U))
     , (λ U → ∧[ 𝒪 X ]-lower₂ (𝒿 $ U) (𝓀 $ U))

   γ : (Ɐ (𝒾 , _) ꞉ (Meets.lower-bound _≼_ (𝒿 , 𝓀)) , 𝒾 ≼ (𝒿 ⋏ 𝓀)) holds
   γ (𝒾 , φ , ϑ) U = ∧[ 𝒪 X ]-greatest (𝒿 $ U) (𝓀 $ U) (𝒾 $ U) (φ U) (ϑ U)

 ⋁ₙ-is-join : (Ɐ K ꞉ Fam 𝓦 Perfect-Nucleus , Joins._is-lub-of_ _≼_ (⋁ₙ K) K) holds
 ⋁ₙ-is-join K = β , γ
  where
   K₀ : Fam 𝓦 (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
   K₀ = ⁅ pr₁ j ∣ j ε K ⁆

   K₁ : Fam 𝓦 (Nucleus (𝒪 X))
   K₁ = ⁅ nucleus-of 𝒿 ∣ 𝒿 ε K ⁆

   β : Joins._is-an-upper-bound-of_ _≼_ (⋁ₙ K) K holds
   β i U = ⋁[ 𝒪 X ]-upper ⁅ α U ∣ α ε 𝔡𝔦𝔯 K₀ ⁆ (i ∷ [])

   γ : (Ɐ (𝒾 , _) ꞉ Joins.upper-bound _≼_ K , (⋁ₙ K) ≼ 𝒾) holds
   γ (𝓀@(k , (n₁ , n₂ , n₃) , _) , φ) U =
    ⋁[ 𝒪 X ]-least ⁅ α U ∣ α ε 𝔡𝔦𝔯 K₀ ⁆ (𝓀 $ U , λ is → † is U)
     where
      open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
      open PosetReasoning (poset-of (𝒪 X))

      † : (is : (index (𝔡𝔦𝔯 K₀))) → ((𝔡𝔦𝔯 K₀ [ is ]) ≼₀ k) holds
      † []       U = n₁ U
      † (j ∷ js) U = (𝔡𝔦𝔯 K₀ [ js ]) ((K₀ [ j ]) U)  ≤⟨ ♠           ⟩
                     (𝔡𝔦𝔯 K₀ [ js ]) (k U)           ≤⟨ † js (k U)  ⟩
                     k (k U)                         ≤⟨ n₂ U        ⟩
                     k U                             ■
                      where
                       ♠ = prenuclei-are-monotone (𝒪 X) (K₁ ^* [ js ]) _ (φ j U)

\end{code}

It's hard to find a good name for the following two lemmas, which are crucial
when proving distributivity.

\begin{code}

 lemma-δ : (j : Nucleus (𝒪 X)) (K : Fam 𝓦 (Nucleus (𝒪 X)))
         → (is : index (K ^*))
         → ((⁅ j ⋏₁ k ∣ k ε K ⁆ ^* [ is ]) ≼₁ nucleus-pre (𝒪 X) j) holds
 lemma-δ 𝒿@(j , n₁ , n₂ , n₃) K []       U = n₁ U
 lemma-δ 𝒿@(j , n₁ , n₂ , n₃) K (i ∷ is) U =
  (⁅ 𝒿 ⋏₁ 𝓀 ∣ 𝓀 ε K ⁆ ^** [ i ∷ is ]) U                            ＝⟨ refl ⟩ₚ
  (⁅ 𝒿 ⋏₁ 𝓀 ∣ 𝓀 ε K ⁆ ^** [ is ]) (j U ∧[ 𝒪 X ] (K [ i ]) .pr₁ U)  ≤⟨ ♠    ⟩
  j ((j U) ∧[ 𝒪 X ] ((K [ i ]) .pr₁ U))                            ＝⟨ ♥    ⟩ₚ
  j (j U) ∧[ 𝒪 X ] j ((K [ i ]) .pr₁ U)                            ≤⟨ ♣    ⟩
  j (j U)                                                          ≤⟨ n₂ U ⟩
  j U                                                              ■
   where
    open PosetReasoning (poset-of (𝒪 X))

    ♠ = lemma-δ 𝒿 K is (j U ∧[ 𝒪 X ] ((K [ i ]) .pr₁ U))
    ♥ = n₃ (j U) ((K [ i ]) .pr₁ U)
    ♣ = ∧[ 𝒪 X ]-lower₁ (j (j U)) (j ((K [ i ]) .pr₁ U))

 lemma-γ : (j : Nucleus (𝒪 X)) (K : Fam 𝓦 (Nucleus (𝒪 X)))
         → (is : index (K ^*))
         → ((⁅ j ⋏₁ k ∣ k ε K ⁆ ^* [ is ]) ≼₁ (K ^* [ is ])) holds
 lemma-γ j         K []       U = ≤-is-reflexive (poset-of (𝒪 X)) U
 lemma-γ 𝒿@(j , _) K (i ∷ is) U =
  _                                                     ≤⟨ ih ⟩
  (K ^** [ is ]) (j U ⊓ (K₀ [ i ]) U)                   ＝⟨ †  ⟩ₚ
  (K ^** [ is ]) (j U) ⊓ (K ^** [ is ]) ((K₀ [ i ]) U)  ≤⟨ ‡  ⟩
  (K ^** [ i ∷ is ]) U                                  ■
   where
    open PosetReasoning (poset-of (𝒪 X))

    K₀ = ⁅ pr₁ k ∣ k ε K ⁆

    φ : (i : index K₀) → is-prenucleus (𝒪 X) (K₀ [ i ]) holds
    φ i = pr₂ (nucleus-pre (𝒪 X) (K [ i ]))

    ih = lemma-γ 𝒿 K is (j U ⊓ (K₀ [ i ]) U )
    †  = pr₂ (𝔡𝔦𝔯-prenuclei K₀ φ is) (j U) ((K₀ [ i ]) U)
    ‡  = ∧[ 𝒪 X ]-lower₂ ((K ^** [ is ]) (j U)) (((K ^**) [ is ]) ((K₀ [ i ]) U))

\end{code}

\begin{code}

 lemma : (𝒿 : Perfect-Nucleus) (𝒦 : Fam 𝓦 Perfect-Nucleus)
       → let 𝒦₀ = ⁅ pr₁ j ∣ j ε 𝒦 ⁆ in
         (V : ⟨ 𝒪 X ⟩)
       → cofinal-in (𝒪 X)
           ⁅ (𝒿 $ V) ∧[ 𝒪 X ] α V ∣ α ε 𝔡𝔦𝔯 𝒦₀ ⁆
           ⁅ α V ∣ α ε 𝔡𝔦𝔯 ⁅ pr₁ (𝒿 ⋏ 𝓀) ∣ 𝓀 ε 𝒦 ⁆ ⁆
         holds
 lemma 𝒿                          𝒦 U []       = ∣ [] , ∧[ 𝒪 X ]-lower₂ (𝒿 $ U) U ∣
 lemma 𝒿@(j , (n₁ , n₂ , n₃) , ζ) 𝒦 U (i ∷ is) = ∥∥-rec ∃-is-prop † ih
   where
    open PosetReasoning (poset-of (𝒪 X))

    ih = lemma 𝒿 𝒦 ((𝒿 $ U) ∧[ 𝒪 X ] ((𝒦 [ i ]) .pr₁ U)) is

    𝒦₀ = ⁅ pr₁ j ∣ j ε 𝒦 ⁆
    𝒦₁ = ⁅ nucleus-of 𝒿 ∣ 𝒿 ε 𝒦 ⁆

    μ : (i : index 𝒦₀) → is-prenucleus (𝒪 X) (𝒦₀ [ i ]) holds
    μ i = pr₂ (nucleus-pre (𝒪 X) (𝒦₁ [ i ]))

    ξ : (is : index (𝔡𝔦𝔯 𝒦₀)) (U : ⟨ 𝒪 X ⟩) → (U ≤ ((𝔡𝔦𝔯 𝒦₀) [ is ]) U) holds
    ξ is U = pr₁ (𝔡𝔦𝔯-prenuclei 𝒦₀ μ is) U

    α = (𝔡𝔦𝔯 𝒦₀) [ is ]

    † : _
    † (js , ϑ) = ∣ (i ∷ js) , ※ ∣
     where
      Kᵢ = 𝒦₀ [ i ]

      p : ((j U ∧[ 𝒪 X ] α (Kᵢ U)) ≤ (j (j U) ∧[ 𝒪 X ] j (Kᵢ U))) holds
      p = (𝒿 $ U) ∧[ 𝒪 X ] (α ((𝒦₀ [ i ]) U))    ≤⟨ Ⅰ ⟩
          j U                                    ≤⟨ Ⅱ ⟩
          (j (j U)) ∧[ 𝒪 X ] (j ((𝒦₀ [ i ]) U))  ■
           where
            Ⅰ = ∧[ 𝒪 X ]-lower₁ (𝒿 $ U) (α ((𝒦₀ [ i ]) U))
            Ⅱ = ∧[ 𝒪 X ]-greatest
                 (j (j U))
                 (j ((𝒦₀ [ i ]) U))
                 (j U)
                 (n₁ (j U))
                 (nuclei-are-monotone (𝒪 X) (nucleus-of 𝒿) _ (pr₁ (pr₂ (𝒦₁ [ i ])) U))

      q : ((𝒿 $ U ∧[ 𝒪 X ] ((𝔡𝔦𝔯 𝒦₀) [ is ]) ((𝒦₀ [ i ]) U))
            ≤
           (((𝔡𝔦𝔯 𝒦₀) [ is ]) (𝒿 $ U) ⊓ ((𝔡𝔦𝔯 𝒦₀) [ is ]) ((𝒦₀ [ i ]) U)))
          holds
      q = ∧[ 𝒪 X ]-greatest _ _ _ Ⅰ Ⅱ
       where
        Ⅰ = j U ⊓ (𝔡𝔦𝔯 𝒦₀ [ is ]) ((𝒦₀ [ i ]) U)  ≤⟨ ∧[ 𝒪 X ]-lower₁ _ _ ⟩
            j U                                   ≤⟨ ξ is (j U)          ⟩
            α (j U)                               ■
        Ⅱ = ∧[ 𝒪 X ]-lower₂ (j U) ((𝔡𝔦𝔯 𝒦₀ [ is ]) ((𝒦₀ [ i ]) U))

      ♥ = ∧[ 𝒪 X ]-greatest _ _ _ p q
      ♠ = ap
            (λ - → (j (j U) ⊓ j (Kᵢ U)) ⊓ -)
            ((pr₂ (𝔡𝔦𝔯-prenuclei 𝒦₀ μ is) (j U) (Kᵢ U)) ⁻¹)
      ♣ = ap (λ - → - ∧[ 𝒪 X ] (α (j U ⊓ Kᵢ U))) (n₃ (j U) (Kᵢ U) ⁻¹)

      ※ = (j U) ∧[ 𝒪 X ] α (Kᵢ U)                                            ≤⟨ ♥ ⟩
          ((j (j U) ∧[ 𝒪 X ] j (Kᵢ U))) ∧[ 𝒪 X ] (α (j U) ∧[ 𝒪 X ] α (Kᵢ U)) ＝⟨ ♠ ⟩ₚ
          ((j (j U) ∧[ 𝒪 X ] j (Kᵢ U))) ∧[ 𝒪 X ] α (j U ∧[ 𝒪 X ] Kᵢ U)       ＝⟨ ♣ ⟩ₚ
          (j (j U ∧[ 𝒪 X ] (Kᵢ U))) ∧[ 𝒪 X ] α (j U ∧[ 𝒪 X ] Kᵢ U)           ≤⟨ ϑ ⟩
          ((𝔡𝔦𝔯 ⁅ pr₁ (𝒿 ⋏ 𝓀) ∣ 𝓀 ε 𝒦 ⁆) [ i ∷ js ]) U                       ■

 distributivityₚ : (𝒿 : Perfect-Nucleus) (𝒦 : Fam 𝓦 Perfect-Nucleus)
                 → 𝒿 ⋏ (⋁ₙ 𝒦) ＝ ⋁ₙ ⁅ 𝒿 ⋏ 𝓀 ∣ 𝓀 ε 𝒦 ⁆
 distributivityₚ 𝒿 𝒦 =
  perfect-nuclei-eq (𝒿 ⋏ ⋁ₙ 𝒦) (⋁ₙ ⁅ 𝒿 ⋏ 𝓀 ∣ 𝓀 ε 𝒦 ⁆) (dfunext fe γ)
   where
    𝒦₀ : Fam 𝓦 (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
    𝒦₀ = ⁅ pr₁ j ∣ j ε 𝒦 ⁆

    γ : (U : ⟨ 𝒪 X ⟩) → (𝒿 ⋏ (⋁ₙ 𝒦)) $ U ＝ (⋁ₙ ⁅ 𝒿 ⋏ 𝓀 ∣ 𝓀 ε 𝒦 ⁆) $ U
    γ U = ((𝒿 ⋏ (⋁ₙ 𝒦)) $ U)                               ＝⟨ refl ⟩
          (𝒿 $ U) ∧[ 𝒪 X ] ((⋁ₙ 𝒦) $ U)                    ＝⟨ refl ⟩
          (𝒿 $ U) ∧[ 𝒪 X ] (⋁[ 𝒪 X ] ⁅ α U ∣ α ε 𝔡𝔦𝔯 𝒦₀ ⁆) ＝⟨ i    ⟩
          ⋁[ 𝒪 X ] ⁅ (𝒿 $ U) ∧[ 𝒪 X ] α U ∣ α ε 𝔡𝔦𝔯 𝒦₀ ⁆   ＝⟨ ii   ⟩
          (⋁ₙ ⁅ 𝒿 ⋏ 𝓀 ∣ 𝓀 ε 𝒦 ⁆) $ U                       ∎
           where

            δ : cofinal-in (𝒪 X)
                 ⁅ (𝒿 $ U) ∧[ 𝒪 X ] α U ∣ α ε 𝔡𝔦𝔯 𝒦₀ ⁆
                 ⁅ α U ∣ α ε 𝔡𝔦𝔯 ⁅ pr₁ (𝒿 ⋏ 𝓀) ∣ 𝓀 ε 𝒦 ⁆ ⁆
                holds
            δ = lemma 𝒿 𝒦 U

            ε : cofinal-in (𝒪 X)
                 ⁅ α U ∣ α ε 𝔡𝔦𝔯 ⁅ pr₁ (𝒿 ⋏ 𝓀) ∣ 𝓀 ε 𝒦 ⁆ ⁆
                 ⁅ (𝒿 $ U) ∧[ 𝒪 X ] α U ∣ α ε 𝔡𝔦𝔯 𝒦₀ ⁆
                holds
            ε is = ∣ is , ※ ∣
             where
              † = lemma-δ (nucleus-of 𝒿) ⁅ nucleus-of 𝓀 ∣ 𝓀 ε 𝒦 ⁆ is U
              ‡ = lemma-γ (nucleus-of 𝒿) ⁅ nucleus-of 𝓀 ∣ 𝓀 ε 𝒦 ⁆ is U

              ※ = ∧[ 𝒪 X ]-greatest (𝒿 $ U) ((𝔡𝔦𝔯 𝒦₀ [ is ]) U) _ † ‡

            i  = distributivity (𝒪 X) (𝒿 $ U) ⁅ α U ∣ α ε 𝔡𝔦𝔯 𝒦₀ ⁆
            ii = bicofinal-implies-same-join (𝒪 X)
                  ⁅ (𝒿 $ U) ∧[ 𝒪 X ] α U ∣ α ε 𝔡𝔦𝔯 𝒦₀ ⁆
                  ⁅ α U ∣ α ε 𝔡𝔦𝔯 ⁅ pr₁ (𝒿 ⋏ 𝓀) ∣ 𝓀 ε 𝒦 ⁆ ⁆
                  δ
                  ε

\end{code}

\begin{code}

 Patch : Locale (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) (𝓤 ⊔ 𝓥) 𝓦
 Patch = record { ⟨_⟩ₗ         = Perfect-Nucleus
                ; frame-str-of = (_≼_ , 𝟏ₚ , _⋏_ , ⋁ₙ)
                               , (≼-is-preorder , ≼-is-antisymmetric)
                               , 𝟏ₚ-is-top
                               , ⋏-is-meet
                               , ⋁ₙ-is-join
                               , λ { (𝒿 , 𝒦) → distributivityₚ 𝒿 𝒦 }
                }

\end{code}

\section{Small version of Patch}

\begin{code}

module SmallPatchConstruction (X : Locale 𝓤 𝓥 𝓦) (σᴰ : spectralᴰ X) where

 ℬ : Fam 𝓦 ⟨ 𝒪 X ⟩
 ℬ = basisₛ X σᴰ

 ℬₖ : Fam 𝓦 (Σ C ꞉ ⟨ 𝒪 X ⟩ , is-compact-open X C holds)
 ℬₖ = index ℬ , λ i → ℬ [ i ] , pr₁ (pr₂ (pr₂ σᴰ)) i

 ℬ-is-basis : basis-forᴰ (𝒪 X) ℬ
 ℬ-is-basis = basisₛ-is-basis X σᴰ

 cover : (U : ⟨ 𝒪 X ⟩) → Fam 𝓦 ⟨ 𝒪 X ⟩
 cover U =
  let
   𝒥 = covering-index-family (𝒪 X) ℬ ℬ-is-basis U
  in
   ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆

 covers-are-directed′ : (U : ⟨ 𝒪 X ⟩)
                     → is-directed (𝒪 X) (cover U) holds
 covers-are-directed′ = basisₛ-covers-are-directed X σᴰ

 X-is-spectral : is-spectral X holds
 X-is-spectral = spectralᴰ-gives-spectrality X σᴰ

 open PatchConstruction X X-is-spectral renaming (Perfect-Nucleus
                                                   to Perfect-Nucleus-on-X)

 _≼ᵏ_ : Perfect-Nucleus-on-X → Perfect-Nucleus-on-X → Ω (𝓥 ⊔ 𝓦)
 _≼ᵏ_ (j , ζⱼ) (k , ζₖ) =
  Ɐ i ꞉ index ℬ , j (ℬ [ i ]) ≤[ poset-of (𝒪 X) ] k (ℬ [ i ])

 _＝ᵏ_ : Perfect-Nucleus-on-X → Perfect-Nucleus-on-X → Ω (𝓥 ⊔ 𝓦)
 _＝ᵏ_ 𝒿@(j , ζⱼ) 𝓀@(k , ζₖ) = (𝒿 ≼ᵏ 𝓀) ∧ (𝓀 ≼ᵏ 𝒿)

 open Meets (λ 𝒿 𝓀 → 𝒿 ≼ᵏ 𝓀)
  using ()
  renaming (is-top to is-topₖ;
            _is-glb-of_ to _is-glb-ofₖ_;
            _is-a-lower-bound-of_ to _is-a-lower-bound-ofₖ_;
            lower-bound to lower-boundₖ)

 ≼-implies-≼ᵏ : (𝒿 𝓀 : Perfect-Nucleus-on-X) → (𝒿 ≼ 𝓀 ⇒ 𝒿 ≼ᵏ 𝓀) holds
 ≼-implies-≼ᵏ 𝒿 𝓀 p i = p (ℬ [ i ])

 ≼ᵏ-implies-≼ : (𝒿 𝓀 : Perfect-Nucleus-on-X) → (𝒿 ≼ᵏ 𝓀 ⇒ 𝒿 ≼ 𝓀) holds
 ≼ᵏ-implies-≼ 𝒿@(j , νⱼ , ζⱼ) 𝓀@(k , νₖ , ζₖ) p U =
  j U                                ＝⟨ i   ⟩ₚ
  j (⋁[ 𝒪 X ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆)   ＝⟨ ii  ⟩ₚ
  ⋁[ 𝒪 X ] ⁅ j (ℬ [ i ]) ∣ i ε 𝒥 ⁆   ≤⟨ iii ⟩
  ⋁[ 𝒪 X ] ⁅ k (ℬ [ i ]) ∣ i ε 𝒥 ⁆   ＝⟨ iv  ⟩ₚ
  k (⋁[ 𝒪 X ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆)   ＝⟨ v   ⟩ₚ
  k U ■
   where
    open PosetReasoning (poset-of (𝒪 X))

    𝒥 : Fam 𝓦 (index ℬ)
    𝒥 = cover-indexₛ X σᴰ U

    δ : is-directed (𝒪 X) ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ holds
    δ = covers-are-directed′ U

    i   = ap j (covers (𝒪 X) ℬ ℬ-is-basis U)
    ii  = scott-continuous-join-eq (𝒪 X) (𝒪 X) j ζⱼ ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ δ
    iii = cofinal-implies-join-covered
           (𝒪 X)
           ⁅ j (ℬ [ i ]) ∣ i ε 𝒥 ⁆
           ⁅ k (ℬ [ i ]) ∣ i ε 𝒥 ⁆
           λ i → ∣ i , p (𝒥 [ i ]) ∣
    iv  = scott-continuous-join-eq (𝒪 X) (𝒪 X) k ζₖ ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ δ ⁻¹
    v   = ap k (covers (𝒪 X) ℬ ℬ-is-basis U) ⁻¹

 ≼-iff-≼ᵏ : (𝒿 𝓀 : Perfect-Nucleus-on-X) → (𝒿 ≼ 𝓀 ⇔ 𝒿 ≼ᵏ 𝓀) holds
 ≼-iff-≼ᵏ 𝒿 𝓀 = ≼-implies-≼ᵏ 𝒿 𝓀 , ≼ᵏ-implies-≼ 𝒿 𝓀

 ≼ᵏ-is-reflexive : is-reflexive _≼ᵏ_ holds
 ≼ᵏ-is-reflexive 𝒿 = ≼-implies-≼ᵏ 𝒿 𝒿 (≼-is-reflexive 𝒿)

 ≼ᵏ-is-transitive : is-transitive _≼ᵏ_ holds
 ≼ᵏ-is-transitive 𝒿 𝓀 𝓁 p₀ q₀ = ≼-implies-≼ᵏ 𝒿 𝓁 (≼-is-transitive 𝒿 𝓀 𝓁 p q)
  where
   p : (𝒿 ≼ 𝓀) holds
   p = ≼ᵏ-implies-≼ 𝒿 𝓀 p₀

   q : (𝓀 ≼ 𝓁) holds
   q = ≼ᵏ-implies-≼ 𝓀 𝓁 q₀

 ≼ᵏ-is-preorder : is-preorder _≼ᵏ_ holds
 ≼ᵏ-is-preorder = ≼ᵏ-is-reflexive , ≼ᵏ-is-transitive

 ≼ᵏ-is-antisymmetric : is-antisymmetric _≼ᵏ_
 ≼ᵏ-is-antisymmetric {x = 𝒿} {y = 𝓀} p₀ q₀ = ≼-is-antisymmetric p q
  where
   p : (𝒿 ≼ 𝓀) holds
   p = ≼ᵏ-implies-≼ 𝒿 𝓀 p₀

   q : (𝓀 ≼ 𝒿) holds
   q = ≼ᵏ-implies-≼ 𝓀 𝒿 q₀

 𝟏ₚ-is-topₖ : is-topₖ 𝟏ₚ holds
 𝟏ₚ-is-topₖ 𝒿 = ≼-implies-≼ᵏ 𝒿 𝟏ₚ (𝟏ₚ-is-top 𝒿)

 ⋏-is-meetₖ : (𝒿 𝓀 : Perfect-Nucleus-on-X)
            → ((𝒿 ⋏ 𝓀) is-glb-ofₖ (𝒿 , 𝓀)) holds
 ⋏-is-meetₖ 𝒿 𝓀 = β , γ
  where
   μ = ⋏-is-meet (𝒿 , 𝓀)

   β : ((𝒿 ⋏ 𝓀) is-a-lower-bound-ofₖ (𝒿 , 𝓀)) holds
   β = ≼-implies-≼ᵏ (𝒿 ⋏ 𝓀) 𝒿 β₁ , ≼-implies-≼ᵏ (𝒿 ⋏ 𝓀) 𝓀 β₂
    where
      β₁ : ((𝒿 ⋏ 𝓀) ≼ 𝒿) holds
      β₁ = pr₁ (pr₁ (⋏-is-meet (𝒿 , 𝓀)))

      β₂ : ((𝒿 ⋏ 𝓀) ≼ 𝓀) holds
      β₂ = pr₂ (pr₁ (⋏-is-meet (𝒿 , 𝓀)))

   γ : (Ɐ (𝒾 , _) ꞉ (Meets.lower-bound _≼ᵏ_ (𝒿 , 𝓀)) , 𝒾 ≼ᵏ (𝒿 ⋏ 𝓀)) holds
   γ (𝒾 , φ , ψ) = ≼-implies-≼ᵏ 𝒾 (𝒿 ⋏ 𝓀) δ
    where
     † = pr₂ (⋏-is-meet (𝒿 , 𝓀))

     δ : (𝒾 ≼ (𝒿 ⋏ 𝓀)) holds
     δ = † (𝒾 , ≼ᵏ-implies-≼ 𝒾 𝒿 φ , ≼ᵏ-implies-≼ 𝒾 𝓀 ψ)

 ⋁ₙ-is-joinₖ : (Ɐ K ꞉ Fam 𝓦 Perfect-Nucleus-on-X , Joins._is-lub-of_ _≼ᵏ_ (⋁ₙ K) K) holds
 ⋁ₙ-is-joinₖ 𝒦 = β , γ
  where
   β : (_≼ᵏ_ Joins.is-an-upper-bound-of ⋁ₙ 𝒦) 𝒦 holds
   β i = ≼-implies-≼ᵏ (𝒦 [ i ] ) (⋁ₙ 𝒦) †
    where
     † : ((𝒦 [ i ]) ≼ ⋁ₙ 𝒦) holds
     † = pr₁ (⋁ₙ-is-join 𝒦) i

   γ : (Ɐ (𝒾 , _) ꞉ Joins.upper-bound _≼ᵏ_ 𝒦 , (⋁ₙ 𝒦) ≼ᵏ 𝒾) holds
   γ (𝒾 , φ) = ≼-implies-≼ᵏ (⋁ₙ 𝒦) 𝒾 (pr₂ (⋁ₙ-is-join 𝒦) (𝒾 , †))
    where
     † : (_≼_ Joins.is-an-upper-bound-of 𝒾) 𝒦 holds
     † j = ≼ᵏ-implies-≼ (𝒦 [ j ]) 𝒾 (φ j)

 SmallPatch : Locale (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) (𝓥 ⊔ 𝓦) 𝓦
 SmallPatch = record { ⟨_⟩ₗ = Perfect-Nucleus-on-X
                     ; frame-str-of = (_≼ᵏ_ , 𝟏ₚ , _⋏_ , ⋁ₙ)
                     , (≼ᵏ-is-preorder , ≼ᵏ-is-antisymmetric)
                     , 𝟏ₚ-is-topₖ
                     , (λ { (𝒿 , 𝓀) → ⋏-is-meetₖ 𝒿 𝓀 })
                     , ⋁ₙ-is-joinₖ
                     , λ { (𝒿 , 𝒦) → distributivityₚ 𝒿 𝒦 }
                     }


 𝟎-is-id : 𝟎[ 𝒪 SmallPatch ] $_ ∼ id
 𝟎-is-id U = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
  where
   open PosetReasoning (poset-of (𝒪 X))

   † : ((𝟎[ 𝒪 SmallPatch ] $ U) ≤[ poset-of (𝒪 X) ] U) holds
   † = 𝟎-is-bottom (𝒪 Patch) idₙ U

   ‡ : (U ≤[ poset-of (𝒪 X) ] (𝟎[ 𝒪 SmallPatch ] $ U)) holds
   ‡ = U                             ≤⟨ ※ ⟩
       (⋁[ 𝒪 SmallPatch ] ∅ 𝓦) $ U   ＝⟨ refl ⟩ₚ
       𝟎[ 𝒪 SmallPatch ] $ U         ■
        where
         ※ = ⋁[ 𝒪 X ]-upper ⁅ α U ∣ α ε 𝔡𝔦𝔯 (∅ 𝓦) ⁆ []

\end{code}
