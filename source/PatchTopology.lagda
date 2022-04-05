Ayberk Tosun, 3 January 2022

Based on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

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

 ⋁_ : Fam 𝓦 ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩
 ⋁ S = ⋁[ 𝒪 X ] S

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

\begin{code}

 nucleus-of : perfect-nucleus → nucleus (𝒪 X)
 nucleus-of (j , ζ , _) = j , ζ

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

 _≼₀_ : (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → Ω (𝓤 ⊔ 𝓥)
 _≼₀_ j k = Ɐ U ∶ ⟨ 𝒪 X ⟩ , (j U) ≤[ poset-of (𝒪 X) ] (k U)

 _≼₁_ : prenucleus (𝒪 X) → prenucleus (𝒪 X) → Ω (𝓤 ⊔ 𝓥)
 𝒿 ≼₁ 𝓀 = pr₁ 𝒿 ≼₀ pr₁ 𝓀

 _≼_ : perfect-nucleus → perfect-nucleus → Ω (𝓤 ⊔ 𝓥)
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

\section{Construction of the join}

The construction of the join is the nontrivial component of this development.
Given a family `S ∶≡ { fᵢ : A → A | i ∶ I }` of endofunctions on some type `A`,
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
S ∶≡ { jᵢ : 𝒪 X → 𝒪 X ∣ i ∶ I }
```

of prenuclei, `sequence S is` is a prenuclei for any given list `is : List I` of
indices.

\begin{code}

 𝔡𝔦𝔯-prenuclear : (K : Fam 𝓦 (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩))
                → (Ɐ i ∶ index K , is-prenuclear (𝒪 X) (K [ i ])) holds
                → (Ɐ is ∶ List (index K) , is-prenuclear (𝒪 X) (𝔡𝔦𝔯 K [ is ])) holds
 𝔡𝔦𝔯-prenuclear K ϑ []       = pr₂ (nucleus-pre (𝒪 X) (identity-nucleus (𝒪 X)))
 𝔡𝔦𝔯-prenuclear K ϑ (j ∷ js) = n₁ , n₂
  where
   open PosetReasoning (poset-of (𝒪 X))

   IH = 𝔡𝔦𝔯-prenuclear K ϑ js

   n₁ : is-inflationary (𝒪 X) (𝔡𝔦𝔯 K [ j ∷ js ]) holds
   n₁ x = x                             ≤⟨ i    ⟩
          (K [ j ]) x                   ≤⟨ ii   ⟩
          (𝔡𝔦𝔯 K [ js ]) ((K [ j ]) x)  ≡⟨ refl ⟩ₚ
          (𝔡𝔦𝔯 K [ j ∷ js ]) x          ■
           where
            i  = pr₁ (ϑ j) x
            ii = pr₁ IH ((K [ j ]) x)

   n₂ : preserves-meets (𝒪 X) (𝒪 X) (𝔡𝔦𝔯 K [ j ∷ js ]) holds
   n₂ x y = (𝔡𝔦𝔯 K [ j ∷ js ]) (x ∧[ 𝒪 X ] y)                   ≡⟨ refl ⟩
            (𝔡𝔦𝔯 K [ js ]) ((K [ j ]) (x ∧[ 𝒪 X ] y))           ≡⟨ i    ⟩
            (𝔡𝔦𝔯 K [ js ]) ((K [ j ]) x ∧[ 𝒪 X ] (K [ j ]) y)   ≡⟨ ii   ⟩
            (𝔡𝔦𝔯 K [ j ∷ js ]) x ∧[ 𝒪 X ] (𝔡𝔦𝔯 K [ j ∷ js ]) y  ∎
             where
              i   = ap (𝔡𝔦𝔯 K [ js ]) (pr₂ (ϑ j) x y)
              ii  = pr₂ IH ((K [ j ]) x) ((K [ j ]) y)

\end{code}

\begin{code}

 _^** : Fam 𝓦 (nucleus (𝒪 X)) → Fam 𝓦 (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
 _^** K = 𝔡𝔦𝔯 ⁅ k ∣ (k , _) ε K ⁆

 ^**-functorial : (K : Fam 𝓦 (nucleus (𝒪 X)))
                → (is js : List (index K))
                →  K ^** [ is ++ js ] ∼ K ^** [ js ] ∘ K ^** [ is ]
 ^**-functorial K []       js _ = refl
 ^**-functorial K (i ∷ is) js x = ^**-functorial K is js ((K [ i ]) .pr₁ x)

 _^* : Fam 𝓦 (nucleus (𝒪 X)) → Fam 𝓦 (prenucleus (𝒪 X))
 _^* K = (List (index K)) , α
  where
   α : List (index K) → prenucleus (𝒪 X)
   α is = 𝔡𝔦𝔯 ⁅ k ∣ (k , _) ε K ⁆ [ is ]
        , 𝔡𝔦𝔯-prenuclear ⁅ k ∣ (k , _) ε K ⁆ † is
    where
     † : (i : index K) → is-prenuclear (𝒪 X) (pr₁ (K [ i ])) holds
     † = pr₂ ∘ nucleus-pre (𝒪 X) ∘ (λ - → K [ - ])

\end{code}

\begin{code}

 ^*-inhabited : (K : Fam 𝓦 (nucleus (𝒪 X))) → ∥ index (K ^*) ∥
 ^*-inhabited K = ∣ [] ∣

 ^*-upwards-directed : (K : Fam 𝓦 (nucleus (𝒪 X)))
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
         K ^* [ js ] $ₚ K ^* [ is ] $ₚ U  ≡⟨ ii ⟩ₚ
         K ^* [ is ++ js ] $ₚ U           ■
          where
           i  = prenucleus-property₂ (𝒪 X) (K ^* [ js ]) (K ^* [ is ]) U
           ii = ^**-functorial K is js U ⁻¹

   γ : ((K ^* [ js ]) ≼₁ (K ^* [ is ++ js ])) holds
   γ U = K ^* [ js ] $ₚ U                 ≤⟨ i  ⟩
         K ^* [ js ] $ₚ K ^* [ is ] $ₚ U  ≡⟨ ii ⟩ₚ
         K ^* [ is ++ js ] $ₚ U           ■
          where
           i  = prenucleus-property₁ (𝒪 X) (K ^* [ js ]) (K ^* [ is ]) U
           ii = ^**-functorial K is js U ⁻¹

\end{code}

\begin{code}

 ^*-scott-continuous : (K : Fam 𝓦 (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩))
                     → (Ɐ i ∶ index K ,
                         is-scott-continuous (𝒪 X) (𝒪 X) (K [ i ])) holds
                     → (Ɐ is ∶ List (index K) ,
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
               ≡ ⋁ ⁅ ⋁ ⁅ α U ∣ U ε S ⁆ ∣ α ε 𝔡𝔦𝔯 J ⁆
 joins-commute J S =
  ⋁ ⁅ ⋁ ⁅ α U ∣ α ε 𝔡𝔦𝔯 J ⁆ ∣ U ε S ⁆                                ≡⟨ i   ⟩
  ⋁ ⁅ (𝔡𝔦𝔯 J [ j ]) (S [ i ]) ∣ (i , j) ∶ index S × index (𝔡𝔦𝔯 J) ⁆  ≡⟨ ii  ⟩
  ⋁ ⁅ (𝔡𝔦𝔯 J [ j ]) (S [ i ]) ∣ (j , i) ∶ index (𝔡𝔦𝔯 J) × index S ⁆  ≡⟨ iii ⟩
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

 ⋁ₙ : Fam 𝓦 perfect-nucleus → perfect-nucleus
 ⋁ₙ K = join K₀ , (n₁ , n₂ , n₃) , {!!}
  where
   open PosetReasoning (poset-of (𝒪 X))
   open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

   K₀ : Fam 𝓦 (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
   K₀ = ⁅ pr₁ j ∣ j ε K ⁆

   ϑ : ∀[∶]-syntax (index K₀) (λ i → is-scott-continuous (𝒪 X) (𝒪 X) (K₀ [ i ])) holds
   ϑ i = pr₂ (pr₂ (K [ i ]))

   K₁ : Fam 𝓦 (nucleus (𝒪 X))
   K₁ = {!⁅!}

   n₁ : is-inflationary (𝒪 X) (join K₀) holds
   n₁ U = ⋁[ 𝒪 X ]-upper ⁅ α U ∣ α ε 𝔡𝔦𝔯 K₀ ⁆ []

   n₂ : is-idempotent (𝒪 X) (join K₀) holds
   n₂ U =
    join K₀ (join K₀ U)                                             ≡⟨ refl ⟩ₚ
    ⋁ ⁅ α (⋁ ⁅ β U ∣ β ε 𝔡𝔦𝔯 K₀ ⁆) ∣ α ε 𝔡𝔦𝔯 K₀ ⁆                   ≡⟨ i    ⟩ₚ
    ⋁ ⁅ ⋁ ⁅ α (β U) ∣ β ε 𝔡𝔦𝔯 K₀ ⁆ ∣ α ε 𝔡𝔦𝔯 K₀ ⁆                   ≡⟨ ii   ⟩ₚ
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

      δ : is-directed (poset-of (𝒪 X)) ⁅ pr₁ α U ∣ α ε K₁ ^* ⁆ holds
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

   n₃ : {!!}
   n₃ = {!!}

\end{code}
