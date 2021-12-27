Ayberk Tosun, 9 December 2021

Based on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-PropTrunc
open import UF-FunExt
open import UF-Univalence
open import UF-UA-FunExt

module CompactRegular
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import UF-Subsingletons
open import UF-Subsingleton-Combinators
open import UF-Equiv using (_≃_; logically-equivalent-props-give-is-equiv)
open import Frame pt fe hiding (is-directed)

open AllCombinators pt fe
open PropositionalTruncation pt

open import InitialFrame pt fe

\end{code}

\section{The way below relation}

We first define the notion of a directed family. This is actually
defined in the `Dcpo` module but I am redefining it here to avoid
importing the `Dcpo` module. There are also some things about that
definition that make it a bit inconvenient to work with. It might be
good idea to address this duplication at some point.

\begin{code}

is-directed : (P : poset 𝓤 𝓥) → (S : Fam 𝓦 ∣ P ∣ₚ) → Ω (𝓥 ⊔ 𝓦)
is-directed P (I , s) =
   ∥ I ∥Ω
 ∧ (Ɐ i ∶ I , Ɐ j ∶ I , Ǝ k ∶ I , ((s i ≤ s k) ∧ (s j ≤ s k)) holds)
  where open PosetNotation P using (_≤_)

\end{code}

\begin{code}

way-below : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
way-below {𝓤 = 𝓤} {𝓦 = 𝓦} F U V =
 Ɐ S ∶ Fam 𝓦 ⟨ F ⟩ , is-directed (poset-of F) S ⇒
  V ≤ (⋁[ F ] S) ⇒ (Ǝ i ∶ index S , (U ≤ S [ i ]) holds)
   where
    open PosetNotation (poset-of F) using (_≤_)

infix 5 way-below

syntax way-below F U V = U ≪[ F ] V

\end{code}

A compact open is one that is way below itself.

\begin{code}

is-compact-open : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-compact-open F U = U ≪[ F ] U

\end{code}

A compact frame is simply a frame whose top element is finite.

\begin{code}

is-compact : frame 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-compact F = is-compact-open F 𝟏[ F ]

\end{code}

Compacts opens are always closed undery binary joins.

\begin{code}

compacts-are-closed-under-joins : (F : frame 𝓤 𝓥 𝓦)
                                → (U V : ⟨ F ⟩)
                                → is-compact-open F U holds
                                → is-compact-open F V holds
                                → is-compact-open F (U ∨[ F ] V) holds
compacts-are-closed-under-joins F U V κ₁ κ₂ S dir@(_ , up) p =
 ∥∥-rec₂ ∃-is-prop γ s₁′ s₂′
  where
   open PosetNotation  (poset-of F) using (_≤_)
   open PosetReasoning (poset-of F)

\end{code}

We know that both `U` and `V` are covered by `S` by the assumption that `U ∨ V`
is covered by `S`

\begin{code}

   q₁ : (U ≤ (⋁[ F ] S)) holds
   q₁ = U ≤⟨ ∨[ F ]-upper₁ U V ⟩ U ∨[ F ] V ≤⟨ p ⟩ ⋁[ F ] S ■

   q₂ : (V ≤ (⋁[ F ] S)) holds
   q₂ = V ≤⟨ ∨[ F ]-upper₂ U V ⟩ U ∨[ F ] V ≤⟨ p ⟩ ⋁[ F ] S ■

\end{code}

Therefore there must exist indices `i₁` and `i₂` such that `U ≤ Sᵢ₁` and `V ≤
Sᵢ₂`.

\begin{code}

   s₁′ : ∥ Σ i₁ ꞉ index S , (U ≤ S [ i₁ ]) holds ∥
   s₁′ = κ₁ S dir q₁

   s₂′ : ∥ Σ i₂ ꞉ index S , (V ≤ S [ i₂ ]) holds ∥
   s₂′ = κ₂ S dir q₂

   γ : (Σ i₁ ꞉ index S , (U ≤ S [ i₁ ]) holds)
     → (Σ i₂ ꞉ index S , (V ≤ S [ i₂ ]) holds)
     → ∃ i ꞉ index S , ((U ∨[ F ] V) ≤ S [ i ]) holds
   γ (i₁ , s₁) (i₂ , s₂) = ∥∥-rec ∃-is-prop δ (up i₁ i₂)
    where
     δ : Σ i ꞉ index S , ((S [ i₁ ] ≤ S [ i ]) ∧ (S [ i₂ ] ≤ S [ i ])) holds
       → ∃ i ꞉ index S , ((U ∨[ F ] V) ≤ S [ i ]) holds
     δ (i , r₁ , r₂) = ∣ i , ∨[ F ]-least ε ζ ∣
      where
       ε : (U ≤ S [ i ]) holds
       ε = U ≤⟨ s₁ ⟩ S [ i₁ ] ≤⟨ r₁ ⟩ S [ i ] ■

       ζ : (V ≤ S [ i ]) holds
       ζ = V ≤⟨ s₂ ⟩ S [ i₂ ] ≤⟨ r₂ ⟩ S [ i ] ■

\end{code}

\section{Well Inside}

`well-inside₀` is the type family expressing that a given open of a frame is
clopen.

\begin{code}

well-inside₀ : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → 𝓤 ̇ 
well-inside₀ F U V =
 Σ W ꞉ ⟨ F ⟩ , (U ∧[ F ] W ≡ 𝟎[ F ]) × (V ∨[ F ] W ≡ 𝟏[ F ])

infix 4 well-inside₀

syntax well-inside₀ F U V = U ⋜₀[ F ] V

\end{code}

The well inside relation is not propositional in general, even though the “has
complement” predicate (i.e. is well inside itself) is propositional.

\begin{code}

well-inside₀-is-not-prop : is-univalent 𝓤₀
                        → Σ F ꞉ frame 𝓤₁ 𝓤₀ 𝓤₀ ,
                           (¬ ((U V : ⟨ F ⟩) → is-prop (U ⋜₀[ F ] V)))
well-inside₀-is-not-prop ua = IF , ε
 where
  IF : frame 𝓤₁ 𝓤₀ 𝓤₀ -- “IF” standing for “initial frame”.
  IF = 𝟎-𝔽𝕣𝕞 ua

  γ₂ : 𝟎[ IF ] ⋜₀[ IF ] 𝟏[ IF ]
  γ₂ = 𝟏[ IF ] , (β , γ)
        where
         abstract
          β : 𝟎[ IF ] ∧[ IF ] 𝟏[ IF ] ≡ 𝟎[ IF ]
          β = 𝟎-left-annihilator-for-∧ IF 𝟏[ IF ]

          γ : 𝟏[ IF ] ∨[ IF ] 𝟏[ IF ] ≡ 𝟏[ IF ]
          γ = 𝟏-right-annihilator-for-∨ IF 𝟏[ IF ]

  γ₁ : 𝟎[ IF ] ⋜₀[ IF ] 𝟏[ IF ]
  γ₁ = 𝟎[ IF ] , (β , γ)
        where
         abstract
          β : 𝟎[ IF ] ∧[ IF ] 𝟎[ IF ] ≡ 𝟎[ IF ]
          β = 𝟎-right-annihilator-for-∧ IF 𝟎[ IF ]

          γ : 𝟏[ IF ] ∨[ IF ] 𝟎[ IF ] ≡ 𝟏[ IF ]
          γ = 𝟏-left-annihilator-for-∨ IF 𝟎[ IF ]

  𝟎-is-not-𝟏 : ¬ (𝟎[ IF ] ≡ 𝟏[ IF ])
  𝟎-is-not-𝟏 p = γ
   where
    γ : ⊥Ω holds
    γ = transport _holds (𝟏[ IF ] ≡⟨ p ⁻¹ ⟩ 𝟎[ IF ] ≡⟨ 𝟎-of-IF-is-⊥ ua ⟩ ⊥Ω ∎) *

  ε : ¬ ((U V : ⟨ IF ⟩) → is-prop (well-inside₀ IF U V))
  ε ψ = 𝟎-is-not-𝟏 (pr₁ (from-Σ-≡ δ))
   where
    δ : γ₁ ≡ γ₂
    δ = ψ 𝟎[ IF ] 𝟏[ IF ] γ₁ γ₂

\end{code}

Because well inside is not propositional, we have to truncate it to get a
relation.

\begin{code}

well-inside : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → Ω 𝓤
well-inside F U V = ∥ U ⋜₀[ F ] V ∥Ω

infix 4 well-inside

syntax well-inside F U V = U ⋜[ F ] V

\end{code}

\begin{code}

well-inside-implies-below : (F : frame 𝓤 𝓥 𝓦)
                          → (U V : ⟨ F ⟩)
                          → (U ⋜[ F ] V ⇒ (U ≤[ poset-of F ] V)) holds
well-inside-implies-below F U V = ∥∥-rec (holds-is-prop (U ≤[ poset-of F ] V)) γ
 where
  _⊓_ = λ U V → U ∧[ F ] V

  γ : U ⋜₀[ F ] V → (U ≤[ poset-of F ] V) holds
  γ (W , c₁ , c₂) = connecting-lemma₂ F δ
   where
    δ : U ≡ U ∧[ F ] V
    δ = U                        ≡⟨ 𝟏-right-unit-of-∧ F U ⁻¹              ⟩
        U ⊓ 𝟏[ F ]               ≡⟨ ap (U ⊓_) (c₂ ⁻¹)                     ⟩
        U ⊓ (V ∨[ F ] W)         ≡⟨ binary-distributivity F U V W         ⟩
        (U ⊓ V) ∨[ F ] (U ⊓ W)   ≡⟨ ap (λ - → binary-join F (U ⊓ V) -) c₁ ⟩
        (U ⊓ V) ∨[ F ] 𝟎[ F ]    ≡⟨ 𝟎-left-unit-of-∨ F (U ⊓ V)            ⟩
        U ⊓ V                    ∎

\end{code}

\begin{code}

T≤U⋜V≤W-implies-T⋜W : (F : frame 𝓤 𝓥 𝓦)
                    → {T U V W : ⟨ F ⟩}
                    → (T ≤[ poset-of F ] U) holds
                    → (U ⋜[ F ] V) holds
                    → (V ≤[ poset-of F ] W) holds
                    → (T ⋜[ F ] W) holds
T≤U⋜V≤W-implies-T⋜W F {T} {U} {V} {W} p q r =
 ∥∥-rec (holds-is-prop (T ⋜[ F ] W)) γ q
  where
   γ : U ⋜₀[ F ] V → (T ⋜[ F ] W) holds
   γ (S , c₁ , c₂) = ∣ S , δ , ε ∣
    where
     open PosetReasoning (poset-of F)

     δ : T ∧[ F ] S ≡ 𝟎[ F ]
     δ = only-𝟎-is-below-𝟎 F (T ∧[ F ] S) δ₁
      where
       δ₁ : ((T ∧[ F ] S) ≤[ poset-of F ] 𝟎[ F ]) holds
       δ₁ = T ∧[ F ] S  ≤⟨ ∧[ F ]-left-monotone p ⟩
            U ∧[ F ] S  ≡⟨ c₁                     ⟩ₚ
            𝟎[ F ]      ■

     ε : W ∨[ F ] S ≡ 𝟏[ F ]
     ε = only-𝟏-is-above-𝟏 F (W ∨[ F ] S) ε₁
      where
       ε₁ : (𝟏[ F ] ≤[ poset-of F ] (W ∨[ F ] S)) holds
       ε₁ = 𝟏[ F ]      ≡⟨ c₂ ⁻¹                  ⟩ₚ
            V ∨[ F ] S  ≤⟨ ∨[ F ]-left-monotone r ⟩
            W ∨[ F ] S  ■

\end{code}

An open _U_ in a frame _A_ is *clopen* iff it is well-inside itself.

\begin{code}

is-clopen₀ : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → 𝓤 ̇ 
is-clopen₀ F U = Σ W ꞉ ⟨ F ⟩ , (U ∧[ F ] W ≡ 𝟎[ F ]) × (U ∨[ F ] W ≡ 𝟏[ F ])

is-clopen₀-is-prop : (F : frame 𝓤 𝓥 𝓦) → (U : ⟨ F ⟩) → is-prop (is-clopen₀ F U)
is-clopen₀-is-prop F U (W₁ , p₁ , q₁) (W₂ , p₂ , q₂) = to-subtype-≡ β γ
 where
  P = poset-of F -- we refer to the underlying poset of F as P.

  β : (W : ⟨ F ⟩) → is-prop ((U ∧[ F ] W ≡ 𝟎[ F ]) × (U ∨[ F ] W ≡ 𝟏[ F ]))
  β W = ×-is-prop carrier-of-[ P ]-is-set carrier-of-[ P ]-is-set

  γ : W₁ ≡ W₂
  γ = W₁                                  ≡⟨ (𝟏-right-unit-of-∧ F W₁) ⁻¹       ⟩
      W₁ ∧[ F ] 𝟏[ F ]                    ≡⟨ ap (λ - → meet-of F W₁ -) (q₂ ⁻¹) ⟩
      W₁ ∧[ F ] (U ∨[ F ] W₂)             ≡⟨ binary-distributivity F W₁ U W₂   ⟩
      (W₁ ∧[ F ] U) ∨[ F ] (W₁ ∧[ F ] W₂) ≡⟨ i                                 ⟩
      (U ∧[ F ] W₁) ∨[ F ] (W₁ ∧[ F ] W₂) ≡⟨ ii                                ⟩
      𝟎[ F ] ∨[ F ] (W₁ ∧[ F ] W₂)        ≡⟨ iii                               ⟩
      (U ∧[ F ] W₂) ∨[ F ] (W₁ ∧[ F ] W₂) ≡⟨ iv                                ⟩
      (W₂ ∧[ F ] U) ∨[ F ] (W₁ ∧[ F ] W₂) ≡⟨ v                                 ⟩
      (W₂ ∧[ F ] U) ∨[ F ] (W₂ ∧[ F ] W₁) ≡⟨ vi                                ⟩
      W₂ ∧[ F ] (U ∨[ F ] W₁)             ≡⟨ vii                               ⟩
      W₂ ∧[ F ] 𝟏[ F ]                    ≡⟨ viii                              ⟩
      W₂                                  ∎
       where
        i    = ap (λ - → - ∨[ F ] (W₁ ∧[ F ] W₂)) (∧[ F ]-is-commutative W₁ U)
        ii   = ap (λ - → - ∨[ F ] (W₁ ∧[ F ] W₂)) p₁
        iii  = ap (λ - → - ∨[ F ] (W₁ ∧[ F ] W₂)) (p₂ ⁻¹)
        iv   = ap (λ - → - ∨[ F ] (W₁ ∧[ F ] W₂)) (∧[ F ]-is-commutative U W₂)
        v    = ap (λ - → (W₂ ∧[ F ] U) ∨[ F ] -) (∧[ F ]-is-commutative W₁ W₂)
        vi   = binary-distributivity F W₂ U W₁ ⁻¹
        vii  = ap (λ - → W₂ ∧[ F ] -) q₁
        viii = 𝟏-right-unit-of-∧ F W₂

is-clopen : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → Ω 𝓤
is-clopen F U = is-clopen₀ F U , is-clopen₀-is-prop F U

clopen-implies-well-inside-itself : (F : frame 𝓤 𝓥 𝓦)
                                   → (U : ⟨ F ⟩)
                                   → (is-clopen F U ⇒ U ⋜[ F ] U) holds
clopen-implies-well-inside-itself F U = ∣_∣

well-inside-itself-implies-clopen : (F : frame 𝓤 𝓥 𝓦)
                                          → (U : ⟨ F ⟩)
                                          → (U ⋜[ F ] U ⇒ is-clopen F U) holds
well-inside-itself-implies-clopen F U =
 ∥∥-rec (holds-is-prop (is-clopen F U)) id

clopenness-equivalent-to-well-inside-itself : (F : frame 𝓤 𝓥 𝓦)
                                             → (U : ⟨ F ⟩)
                                             → (U ⋜[ F ] U) holds
                                             ≃ is-clopen F U holds
clopenness-equivalent-to-well-inside-itself F U =
   well-inside-itself-implies-clopen F U
 , logically-equivalent-props-give-is-equiv
    (holds-is-prop (U ⋜[ F ] U))
    (holds-is-prop (is-clopen F U))
    (well-inside-itself-implies-clopen F U)
    (clopen-implies-well-inside-itself F U)

\end{code}

\begin{code}

𝟎-is-clopen : (F : frame 𝓤 𝓥 𝓦) → 𝟎[ F ] ⋜₀[ F ] 𝟎[ F ]
𝟎-is-clopen F = 𝟏[ F ] , β , γ
 where
  β : 𝟎[ F ] ∧[ F ] 𝟏[ F ] ≡ 𝟎[ F ]
  β = 𝟎-left-annihilator-for-∧ F 𝟏[ F ]

  γ : 𝟎[ F ] ∨[ F ] 𝟏[ F ] ≡ 𝟏[ F ]
  γ = 𝟏-right-annihilator-for-∨ F 𝟎[ F ]

\end{code}

\begin{code}

𝟎-is-well-inside-anything : (F : frame 𝓤 𝓥 𝓦) (U : ⟨ F ⟩)
                          → (𝟎[ F ] ⋜[ F ] U) holds
𝟎-is-well-inside-anything F U = T≤U⋜V≤W-implies-T⋜W F β ∣ 𝟎-is-clopen F ∣ γ
 where
  β : (𝟎[ F ] ≤[ poset-of F ] 𝟎[ F ]) holds
  β = ≤-is-reflexive (poset-of F) 𝟎[ F ]

  γ : (𝟎[ F ] ≤[ poset-of F ] U) holds
  γ = 𝟎-is-bottom F U

\end{code}

\begin{code}

well-inside-upwards : (F : frame 𝓤 𝓥 𝓦) (U₁ U₂ V : ⟨ F ⟩)
                    → (U₁ ⋜[ F ] V) holds
                    → (U₂ ⋜[ F ] V) holds
                    → ((U₁ ∨[ F ] U₂) ⋜[ F ] V) holds
well-inside-upwards F U₁ U₂ V =
 ∥∥-rec₂ (holds-is-prop ((U₁ ∨[ F ] U₂) ⋜[ F ] V)) γ
  where
   open PosetReasoning (poset-of F)

   γ : U₁ ⋜₀[ F ] V → U₂ ⋜₀[ F ] V → ((U₁ ∨[ F ] U₂) ⋜[ F ] V) holds
   γ (W₁ , c₁ , d₁) (W₂ , c₂ , d₂) = ∣ (W₁ ∧[ F ] W₂) , c , d ∣
    where
     δ : (W₁ ∧[ F ] W₂) ∧[ F ] U₂ ≡ 𝟎[ F ]
     δ = (W₁ ∧[ F ] W₂) ∧[ F ] U₂  ≡⟨ (∧[ F ]-is-associative W₁ W₂ U₂) ⁻¹ ⟩
         W₁ ∧[ F ] (W₂ ∧[ F ] U₂)  ≡⟨ †                                   ⟩
         W₁ ∧[ F ] (U₂ ∧[ F ] W₂)  ≡⟨ ap (λ - → meet-of F W₁ -) c₂        ⟩
         W₁ ∧[ F ] 𝟎[ F ]          ≡⟨ 𝟎-right-annihilator-for-∧ F W₁      ⟩
         𝟎[ F ]                    ∎
          where
           † = ap (λ - → W₁ ∧[ F ] -) (∧[ F ]-is-commutative W₂ U₂)

     ε : ((W₁ ∧[ F ] W₂) ∧[ F ] U₁) ≡ 𝟎[ F ]
     ε = (W₁ ∧[ F ] W₂) ∧[ F ] U₁  ≡⟨ †                                   ⟩
         (W₂ ∧[ F ] W₁) ∧[ F ] U₁  ≡⟨ (∧[ F ]-is-associative W₂ W₁ U₁) ⁻¹ ⟩
         W₂ ∧[ F ] (W₁ ∧[ F ] U₁)  ≡⟨ ‡                                   ⟩
         W₂ ∧[ F ] (U₁ ∧[ F ] W₁)  ≡⟨ ap (λ - → W₂ ∧[ F ] -) c₁           ⟩
         W₂ ∧[ F ] 𝟎[ F ]          ≡⟨ 𝟎-right-annihilator-for-∧ F W₂      ⟩
         𝟎[ F ]                    ∎
          where
           † = ap (λ - → - ∧[ F ] U₁) (∧[ F ]-is-commutative W₁ W₂)
           ‡ = ap (λ - → W₂ ∧[ F ] -) (∧[ F ]-is-commutative W₁ U₁)

     c : ((U₁ ∨[ F ] U₂) ∧[ F ] (W₁ ∧[ F ] W₂)) ≡ 𝟎[ F ]
     c = (U₁ ∨[ F ] U₂) ∧[ F ] (W₁ ∧[ F ] W₂)                          ≡⟨ i    ⟩
         (W₁ ∧[ F ] W₂) ∧[ F ] (U₁ ∨[ F ] U₂)                          ≡⟨ ii   ⟩
         ((W₁ ∧[ F ] W₂) ∧[ F ] U₁) ∨[ F ] ((W₁ ∧[ F ] W₂) ∧[ F ] U₂)  ≡⟨ iii  ⟩
         ((W₁ ∧[ F ] W₂) ∧[ F ] U₁) ∨[ F ] 𝟎[ F ]                      ≡⟨ iv   ⟩
         (W₁ ∧[ F ] W₂) ∧[ F ] U₁                                      ≡⟨ ε    ⟩
         𝟎[ F ]                                                        ∎
          where
           i   = ∧[ F ]-is-commutative (U₁ ∨[ F ] U₂) (W₁ ∧[ F ] W₂)
           ii  = binary-distributivity F (W₁ ∧[ F ] W₂) U₁ U₂
           iii = ap (λ - → ((W₁ ∧[ F ] W₂) ∧[ F ] U₁) ∨[ F ] -) δ
           iv  = 𝟎-left-unit-of-∨ F ((W₁ ∧[ F ] W₂) ∧[ F ] U₁)

     d : V ∨[ F ] (W₁ ∧[ F ] W₂) ≡ 𝟏[ F ]
     d = V ∨[ F ] (W₁ ∧[ F ] W₂)            ≡⟨ i   ⟩
         (V ∨[ F ] W₁) ∧[ F ] (V ∨[ F ] W₂) ≡⟨ ii  ⟩
         𝟏[ F ] ∧[ F ] (V ∨[ F ] W₂)        ≡⟨ iii ⟩
         𝟏[ F ] ∧[ F ] 𝟏[ F ]               ≡⟨ iv  ⟩
         𝟏[ F ] ∎
          where
           i   = binary-distributivity-op F V W₁ W₂
           ii  = ap (λ - → - ∧[ F ] (V ∨[ F ] W₂)) d₁
           iii = ap (λ - → 𝟏[ F ] ∧[ F ] -) d₂
           iv  = 𝟏-right-unit-of-∧ F 𝟏[ F ]

\end{code}

\section{Definition of regularity}

\begin{code}

↓↓[_] : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → Fam 𝓤 ⟨ F ⟩
↓↓[ F ] U = (Σ V ꞉ ⟨ F ⟩ , (V ⋜[ F ] U) holds) , pr₁

\end{code}

\begin{code}

↓↓[_]-is-directed : (F : frame 𝓤 𝓥 𝓦)
                  → (U : ⟨ F ⟩) → is-directed (poset-of F) (↓↓[ F ] U) holds
↓↓[_]-is-directed F U = β , γ
 where
  β : ∥ index (↓↓[ F ] U) ∥
  β = ∣ 𝟎[ F ] , 𝟎-is-well-inside-anything F U  ∣

\end{code}

We now want to prove that this set is upwards-closed.

\begin{code}

  Ψ = Ɐ i ∶ index (↓↓[ F ] U) ,
       Ɐ j ∶ index (↓↓[ F ] U) ,
        Ǝ k ∶ index (↓↓[ F ] U) ,
           ((↓↓[ F ] U [ i ]) ≤[ poset-of F ] (↓↓[ F ] U [ k ])) holds
         × ((↓↓[ F ] U [ j ]) ≤[ poset-of F ] (↓↓[ F ] U [ k ])) holds

  γ : Ψ holds
  γ i@(V₁ , p₁) j@(V₂ , p₂) =
   ∣ ((V₁ ∨[ F ] V₂) , δ) , ∨[ F ]-upper₁ V₁ V₂ , ∨[ F ]-upper₂ V₁ V₂ ∣
    where
     δ : ((V₁ ∨[ F ] V₂) ⋜[ F ] U) holds
     δ = well-inside-upwards F V₁ V₂ U p₁ p₂

\end{code}

\begin{code}

is-regular : frame 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥)
is-regular F = Ɐ U ∶ ⟨ F ⟩ , U is-lub-of (↓↓[ F ] U)
 where
  open Joins (λ U V → U ≤[ poset-of F ] V)

\end{code}

\section{Some properties}

\begin{code}

∨-is-scott-continuous : (F : frame 𝓤 𝓥 𝓦)
                      → (U : ⟨ F ⟩)
                      → is-scott-continuous F F (λ - → U ∨[ F ] -) holds
∨-is-scott-continuous F U S dir = β , γ
 where
  open PosetNotation  (poset-of F) using (_≤_)
  open PosetReasoning (poset-of F)
  open Joins _≤_

  β : ((U ∨[ F ] (⋁[ F ] S)) is-an-upper-bound-of ⁅ U ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆) holds
  β i = ∨[ F ]-right-monotone (⋁[ F ]-upper S i)

  γ : (Ɐ (U′ , _) ∶ upper-bound ⁅ U ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆ ,
        ((U ∨[ F ] (⋁[ F ] S)) ≤ U′)) holds
  γ (u′ , p) = ∨[ F ]-least γ₁ γ₂
   where
    δ₁ : index S → (U ≤ u′) holds
    δ₁ i = U                  ≤⟨ ∨[ F ]-upper₁ U (S [ i ]) ⟩
           U ∨[ F ] (S [ i ]) ≤⟨ p i                       ⟩
           u′                 ■

    γ₁ : (U ≤[ poset-of F ] u′) holds
    γ₁ = ∥∥-rec (holds-is-prop (U ≤[ poset-of F ] u′)) δ₁ (pr₁ dir)

    γ₂ : ((⋁[ F ] S) ≤[ poset-of F ] u′) holds
    γ₂ = ⋁[ F ]-least S (u′ , δ₂)
     where
      δ₂ : (u′ is-an-upper-bound-of S) holds
      δ₂ i = S [ i ]                         ≤⟨ ∨[ F ]-upper₂ U (S [ i ]) ⟩
             U ∨[ F ] (S [ i ])              ≤⟨ p i                       ⟩
             u′                              ■

∨-is-scott-continuous-eq : (F : frame 𝓤 𝓥 𝓦)
                         → (U : ⟨ F ⟩)
                         → (S : Fam 𝓦 ⟨ F ⟩)
                         → (is-directed (poset-of F) S) holds
                         → U ∨[ F ] (⋁[ F ] S) ≡ ⋁[ F ] ⁅ U ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆
∨-is-scott-continuous-eq F U S dir =
 ⋁[ F ]-unique ⁅ U ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆ (U ∨[ F ] (⋁[ F ] S)) (γ , δ)
  where
   γ = pr₁ ((∨-is-scott-continuous F U) S dir)
   δ = pr₂ ((∨-is-scott-continuous F U) S dir)

⋜₀-implies-≪-in-compact-frames : (F : frame 𝓤 𝓥 𝓦)
                               → is-compact F holds
                               → (U V : ⟨ F ⟩)
                               → U ⋜₀[ F ] V
                               → (U ≪[ F ] V) holds
⋜₀-implies-≪-in-compact-frames {𝓦 = 𝓦} F κ U V (W , c₁ , c₂) S d q =
 ∥∥-rec ∃-is-prop θ ζ
  where
   open PosetNotation  (poset-of F)
   open PosetReasoning (poset-of F)

   T : Fam 𝓦 ⟨ F ⟩
   T = ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆

   δ : (𝟏[ F ] ≤ (⋁[ F ] T)) holds
   δ = 𝟏[ F ]                           ≡⟨ c₂ ⁻¹                              ⟩ₚ
       V ∨[ F ] W                       ≤⟨ ∨[ F ]-left-monotone q             ⟩
       (⋁[ F ] S) ∨[ F ] W              ≡⟨ ∨[ F ]-is-commutative (⋁[ F ] S) W ⟩ₚ
       W ∨[ F ] (⋁[ F ] S)              ≡⟨ ∨-is-scott-continuous-eq F W S d   ⟩ₚ
       ⋁[ F ] ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆  ■

   ε : ((W ∨[ F ] (⋁[ F ] S)) ≤ (⋁[ F ] T)) holds
   ε = W ∨[ F ] (⋁[ F ] S)              ≤⟨ 𝟏-is-top F (W ∨[ F ] (⋁[ F ] S)) ⟩
       𝟏[ F ]                           ≤⟨ δ                                ⟩
       ⋁[ F ] ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆  ■

\end{code}

The family `T` we defined is also directed by the directedness of `S`.

\begin{code}

   up : (Ɐ i , Ɐ j ,
           Ǝ k , (T [ i ] ≤ T [ k ]) holds × (T [ j ] ≤ T [ k ]) holds) holds
   up i j = ∥∥-rec ∃-is-prop r (pr₂ d i j)
    where
     r  = λ (k , p , q) → ∣ k , ∨[ F ]-right-monotone p , ∨[ F ]-right-monotone q ∣

\end{code}

\begin{code}

   T-is-directed : (is-directed (poset-of F) ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆) holds
   T-is-directed = pr₁ d , up

   ζ : ∥ Σ i ꞉ index S , (𝟏[ F ] ≤ (W ∨[ F ] (S [ i ]))) holds ∥
   ζ = κ ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆ T-is-directed δ

   θ : Σ i ꞉ index S , (𝟏[ F ] ≤ (W ∨[ F ] S [ i ])) holds
     → ∃ i ꞉ index S , (U ≤ S [ i ]) holds
   θ (i , p) = ∣ i , well-inside-implies-below F U (S [ i ]) ∣ W , c₁ , ι ∣ ∣
    where
     η = 𝟏[ F ]              ≤⟨ p                                 ⟩
         W ∨[ F ] (S [ i ])  ≡⟨ ∨[ F ]-is-commutative W (S [ i ]) ⟩ₚ
         (S [ i ]) ∨[ F ] W  ■

     ι = only-𝟏-is-above-𝟏 F ((S [ i ]) ∨[ F ] W) η

⋜-implies-≪-in-compact-frames : (F : frame 𝓤 𝓥 𝓦)
                              → is-compact F holds
                              → (U V : ⟨ F ⟩) → (U ⋜[ F ] V ⇒ U ≪[ F ] V) holds
⋜-implies-≪-in-compact-frames F κ U V =
 ∥∥-rec (holds-is-prop (U ≪[ F ] V)) (⋜₀-implies-≪-in-compact-frames F κ U V)

clopens-are-compact-in-compact-frames : (F : frame 𝓤 𝓥 𝓦)
                                      → is-compact F holds
                                      → (U : ⟨ F ⟩)
                                      → is-clopen F U holds
                                      → is-compact-open F U holds
clopens-are-compact-in-compact-frames F κ U =
 ⋜₀-implies-≪-in-compact-frames F κ  U U

\end{code}

\section{Regularity}

\begin{code}

is-regular : (F : frame 𝓤 𝓥 𝓦) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-regular {𝓤 = 𝓤} {𝓥} {𝓦} F =
 let
  open Joins (λ x y → x ≤[ poset-of F ] y)

  P : Fam 𝓦 ⟨ F ⟩ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇ 
  P ℬ = Π x ꞉ ⟨ F ⟩ ,
         Σ J ꞉ Fam 𝓦 (index ℬ) ,
            (x is-lub-of ⁅ ℬ [ j ] ∣ j ε J ⁆) holds
          × (Π i ꞉ index J , (ℬ [ J [ i ] ] ⋜[ F ] x) holds)
 in
  Ǝ ℬ ∶ Fam 𝓦 ⟨ F ⟩ , P ℬ

is-regular-basis : (F : frame 𝓤 𝓥 𝓦)
                 → (ℬ : Fam 𝓦 ⟨ F ⟩) → (β : is-basis-for F ℬ) → Ω (𝓤 ⊔ 𝓦)
is-regular-basis F ℬ β =
 Ɐ U ∶ ⟨ F ⟩ ,
  let 𝒥 = pr₁ (β U) in
   Ɐ j ∶ (index 𝒥) , ℬ [ 𝒥 [ j ] ] ⋜[ F ] U

is-regular₀ : (F : frame 𝓤 𝓥 𝓦) → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) ̇ 
is-regular₀ {𝓤 = 𝓤} {𝓥} {𝓦} F =
 let
  open Joins (λ x y → x ≤[ poset-of F ] y)

  P : Fam 𝓦 ⟨ F ⟩ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇ 
  P ℬ = Π x ꞉ ⟨ F ⟩ ,
         Σ J ꞉ Fam 𝓦 (index ℬ) ,
            (x is-lub-of ⁅ ℬ [ j ] ∣ j ε J ⁆) holds
          × (Π i ꞉ index J , (ℬ [ J [ i ] ] ⋜[ F ] x) holds)
 in
  Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ , P ℬ

basis-of-regular-frame : (F : frame 𝓤 𝓥 𝓦)
                       → (is-regular F ⇒ has-basis F) holds
basis-of-regular-frame F r = ∥∥-rec (holds-is-prop (has-basis F)) γ r
 where
  γ : is-regular₀ F → has-basis F holds
  γ (ℬ , δ)= ∣ ℬ , (λ U → pr₁ (δ U) , pr₁ (pr₂ (δ U))) ∣

\end{code}
≪-implies-⋜-in-regular-frames : (F : frame 𝓤 𝓥 𝓦)
                              → is-regular F holds
                              → (U V : ⟨ F ⟩)
                              → (U ≪[ F ] V) holds
                              → (U ⋜[ F ] V) holds
≪-implies-⋜-in-regular-frames F ρ U V κ =
 ∥∥-rec (holds-is-prop ((U ⋜[ F ] V))) {!!} (κ {!↓↓[ F ] V!} {!!} {!!})
  where
   -- Stone Spaces pg. 303 (PDF pg. 324)
   W : ⟨ F ⟩
   W = {!!}

   p : (W ⋜[ F ] V) holds
   p = {!T≤U⋜V≤W-implies-T⋜W!}

   β : (U ≤[ poset-of F ] {!!}) holds
   β = {!!}

   γ : {!!}
   γ = {!!}

\end{code}
