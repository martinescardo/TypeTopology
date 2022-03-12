Ayberk Tosun, 3 January 2022

Based on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-PropTrunc
open import UF-FunExt
open import UF-Univalence
open import UF-UA-FunExt
open import UF-EquivalenceExamples
open import List hiding ([_])

\end{code}

\begin{code}

module PatchTopology
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import UF-Subsingletons
open import UF-Subsingleton-Combinators
open import UF-Equiv using (_≃_; logically-equivalent-props-give-is-equiv)
open import Frame pt fe hiding (is-directed)

open AllCombinators pt fe
open PropositionalTruncation pt
open import Nucleus pt fe
open import CompactRegular pt fe

\end{code}

A _locale_ is a type that has a frame of opens.

\begin{code}

record locale (𝓤 𝓥 𝓦 : Universe) : 𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇  where
 field
  ⟨_⟩ₗ         : 𝓤 ̇
  frame-str-of : frame-structure 𝓥 𝓦 ⟨_⟩ₗ

 𝒪 : frame 𝓤 𝓥 𝓦
 𝒪 = ⟨_⟩ₗ , frame-str-of

\end{code}

We fix a locale `X` for the remainder of this module.

\begin{code}

open locale

module PatchConstruction (X : locale 𝓤 𝓥 𝓦) (σ : is-spectral (𝒪 X) holds) where

 _≤_ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → Ω 𝓥
 U ≤ V = U ≤[ poset-of (𝒪 X) ] V

 open Meets _≤_

 _⊓_ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩
 U ⊓ V = U ∧[ 𝒪 X ] V

\end{code}

A nucleus is called perfect iff it is Scott-continuous:

\begin{code}

 is-perfect : (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
 is-perfect = is-scott-continuous (𝒪 X) (𝒪 X)

\end{code}

\begin{code}

 perfect-nucleus : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
 perfect-nucleus = Σ j ꞉ (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) ,
                    ((is-nuclear (𝒪 X) j ∧ is-perfect j) holds)

\end{code}

\section{Poset of perfect nuclei}

\begin{code}

 _$_ : perfect-nucleus → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩
 (j , _) $ U = j U

\end{code}

\begin{code}

 perfect-nuclei-eq : (𝒿 𝓀 : perfect-nucleus) → 𝒿 $_ ≡ 𝓀 $_ → 𝒿 ≡ 𝓀
 perfect-nuclei-eq 𝒿 𝓀 = to-subtype-≡ γ
  where
   γ : (j : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
     → is-prop ((is-nuclear (𝒪 X) j ∧ is-perfect j) holds)
   γ j = holds-is-prop (is-nuclear (𝒪 X) j ∧ is-perfect j)

\end{code}

Nuclei are ordered pointwise.

\begin{code}

 _≼_ : perfect-nucleus → perfect-nucleus → Ω (𝓤 ⊔ 𝓥)
 𝒿 ≼ 𝓀 = Ɐ U ∶ ⟨ 𝒪 X ⟩ , (𝒿 $ U) ≤ (𝓀 $ U)

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

 patch-poset : poset (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) (𝓤 ⊔ 𝓥)
 patch-poset = perfect-nucleus , _≼_ , ≼-is-preorder , ≼-is-antisymmetric

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
               → preserves-meets (𝒪 X) (𝒪 X) j holds
               → preserves-meets (𝒪 X) (𝒪 X) k holds
               → is-idempotent (𝒪 X) j holds
               → is-idempotent (𝒪 X) k holds
               → is-idempotent (𝒪 X) (j ⋏₀ k) holds
 ⋏₀-idempotent j k ζj ζk ϑj ϑk U =
  (j ⋏₀ k) ((j ⋏₀ k) U)                                          ≡⟨ refl ⟩ₚ
  (j ⋏₀ k) (j U ∧[ 𝒪 X ] k U)                                    ≡⟨ refl ⟩ₚ
  j (j U ∧[ 𝒪 X ] k U) ∧[ 𝒪 X ] k (j U ∧[ 𝒪 X ] k U)             ≡⟨ i    ⟩ₚ
  (j (j U) ∧[ 𝒪 X ] j (k U)) ∧[ 𝒪 X ] k (j U ∧[ 𝒪 X ] k U)       ≡⟨ ii   ⟩ₚ
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
                       → preserves-meets (𝒪 X) (𝒪 X) j holds
                       → preserves-meets (𝒪 X) (𝒪 X) k holds
                       → preserves-meets (𝒪 X) (𝒪 X) (j ⋏₀ k) holds
 ⋏₀-is-meet-preserving j k ζⱼ ζₖ U V =
  (j ⋏₀ k) (U ∧[ 𝒪 X ] V)                        ≡⟨ refl  ⟩
  j (U ∧[ 𝒪 X ] V) ∧[ 𝒪 X ] k (U ∧[ 𝒪 X ] V)     ≡⟨ i     ⟩
  (j U ∧[ 𝒪 X ] j V) ∧[ 𝒪 X ] k (U ∧[ 𝒪 X ] V)   ≡⟨ ii    ⟩
  (j U ∧[ 𝒪 X ] j V) ∧[ 𝒪 X ] (k U ∧[ 𝒪 X ] k V) ≡⟨ iii   ⟩
  j U ∧[ 𝒪 X ] ((j V ∧[ 𝒪 X ] k U) ∧[ 𝒪 X ] k V) ≡⟨ iv    ⟩
  j U ∧[ 𝒪 X ] ((k U ∧[ 𝒪 X ] j V) ∧[ 𝒪 X ] k V) ≡⟨ v     ⟩
  j U ∧[ 𝒪 X ] (k U ∧[ 𝒪 X ] (j V ∧[ 𝒪 X ] k V)) ≡⟨ vi     ⟩
  (j U ∧[ 𝒪 X ] k U) ∧[ 𝒪 X ] (j V ∧[ 𝒪 X ] k V) ≡⟨ refl  ⟩
  ((j ⋏₀ k) U) ∧[ 𝒪 X ] ((j ⋏₀ k) V)             ∎
   where
    †   = ∧[ 𝒪 X ]-is-associative (j U) (j V) (k U ∧[ 𝒪 X ] k V) ⁻¹
    ‡   = ap (λ - → j U ∧[ 𝒪 X ] -) (∧[ 𝒪 X ]-is-associative (j V) (k U) (k V))
    i   = ap (λ - → - ∧[ 𝒪 X ] k (U ∧[ 𝒪 X ] V)) (ζⱼ U V)
    ii  = ap (λ - → (j U ∧[ 𝒪 X ] j V) ∧[ 𝒪 X ] -) (ζₖ U V)
    iii = (j U ∧[ 𝒪 X ] j V) ∧[ 𝒪 X ] (k U ∧[ 𝒪 X ] k V)  ≡⟨ † ⟩
          j U ∧[ 𝒪 X ] (j V ∧[ 𝒪 X ] (k U ∧[ 𝒪 X ] k V))  ≡⟨ ‡ ⟩
          j U ∧[ 𝒪 X ] ((j V ∧[ 𝒪 X ] k U) ∧[ 𝒪 X ] k V)  ∎
    iv  = ap
           (λ - → j U ∧[ 𝒪 X ] (- ∧[ 𝒪 X ] k V))
           (∧[ 𝒪 X ]-is-commutative (j V) (k U))
    v   = ap (λ - → j U ∧[ 𝒪 X ] -) (∧[ 𝒪 X ]-is-associative (k U) (j V) (k V) ⁻¹)
    vi  = ∧[ 𝒪 X ]-is-associative (j U) (k U) (j V ∧[ 𝒪 X ] k V)

 _⋏₁_ : nucleus (𝒪 X) → nucleus (𝒪 X) → nucleus (𝒪 X)
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
   β l = (j ⋏₀ k) (S [ l ])                       ≡⟨ refl ⟩ₚ
         j (S [ l ]) ∧[ 𝒪 X ] k (S [ l ])         ≤⟨ i    ⟩
         j (⋁[ 𝒪 X ] S) ∧[ 𝒪 X ] k (S [ l ])      ≤⟨ ii   ⟩
         j (⋁[ 𝒪 X ] S) ∧[ 𝒪 X ] k (⋁[ 𝒪 X ] S)   ≡⟨ refl ⟩ₚ
         (j ⋏₀ k) (⋁[ 𝒪 X ] S)                    ■
          where
           †  = ⋁[ 𝒪 X ]-upper S l
           ‡  = ⋁[ 𝒪 X ]-upper S l
           i  = ∧[ 𝒪 X ]-left-monotone  (μj (S [ l ] , ⋁[ 𝒪 X ] S) †)
           ii = ∧[ 𝒪 X ]-right-monotone (μk (S [ l ] , ⋁[ 𝒪 X ] S) ‡)

   γ : (Ɐ (u , _) ∶ upper-bound ⁅ (j ⋏₀ k) s ∣ s ε S ⁆ ,
         (j ⋏₀ k) (⋁[ 𝒪 X ] S) ≤[ poset-of (𝒪 X) ] u) holds
   γ 𝓊@(u , _) =
    (j ⋏₀ k) (⋁[ 𝒪 X ] S)                                           ≡⟨ refl ⟩ₚ
    j (⋁[ 𝒪 X ] S) ∧[ 𝒪 X ] k (⋁[ 𝒪 X ] S)                          ≤⟨ i    ⟩
    (⋁[ 𝒪 X ] ⁅ j s ∣ s ε S ⁆) ∧[ 𝒪 X ] k (⋁[ 𝒪 X ] S)              ≤⟨ ii   ⟩
    (⋁[ 𝒪 X ] ⁅ j s ∣ s ε S ⁆) ∧[ 𝒪 X ] (⋁[ 𝒪 X ] ⁅ k s ∣ s ε S ⁆)  ≡⟨ iii  ⟩ₚ
    ⋁[ 𝒪 X ] ⁅ 𝒮 m n ∣ (m , n) ∶ I × I ⁆                            ≤⟨ iv   ⟩
    ⋁⟨ i ∶ I ⟩ j (S [ i ]) ∧[ 𝒪 X ] k (S [ i ])                     ≤⟨ v    ⟩
    u                                                               ■
     where
      I  = index S

      𝒮 : I → I → ⟨ 𝒪 X ⟩
      𝒮 m n = j (S [ m ]) ∧[ 𝒪 X ] k (S [ n ])

      † : j (⋁[ 𝒪 X ] S) ≡ ⋁[ 𝒪 X ] ⁅ j s ∣ s ε S ⁆
      † = scott-continuous-join-eq (𝒪 X) (𝒪 X) j ζj S δ

      ‡ : k (⋁[ 𝒪 X ] S) ≡ ⋁[ 𝒪 X ] ⁅ k s ∣ s ε S ⁆
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
         𝒮 m n                                        ≡⟨ refl ⟩ₚ
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

 _⋏_ : perfect-nucleus → perfect-nucleus → perfect-nucleus
 (𝒿 , νj , ζj) ⋏ (𝓀 , νk , ζk) = pr₁ Σ-assoc (((𝒿 , νj) ⋏₁ (𝓀 , νk)) , γ)
  where
   μj = nuclei-are-monotone (𝒪 X) (𝒿 , νj)
   μk = nuclei-are-monotone (𝒪 X) (𝓀 , νk)

   γ : is-perfect (𝒿 ⋏₀ 𝓀) holds
   γ = ⋏₀-perfect 𝒿 𝓀 μj μk ζj ζk

\end{code}
