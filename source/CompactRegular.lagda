Ayberk Tosun, 9 December 2021

Based on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import UF-Base
open import UF-PropTrunc
open import UF-FunExt
open import UF-Univalence
open import UF-UA-FunExt
open import List hiding ([_])

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

is-directed : (P : Poset 𝓤 𝓥) → (S : Fam 𝓦 ∣ P ∣ₚ) → Ω (𝓥 ⊔ 𝓦)
is-directed P (I , s) =
   ∥ I ∥Ω
 ∧ (Ɐ i ∶ I , Ɐ j ∶ I , Ǝ k ∶ I , ((s i ≤ s k) ∧ (s j ≤ s k)) holds)
  where open PosetNotation P using (_≤_)

\end{code}

\begin{code}

way-below : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
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

is-compact-open : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-compact-open F U = U ≪[ F ] U

\end{code}

A compact frame is simply a frame whose top element is finite.

\begin{code}

is-compact : Frame 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-compact F = is-compact-open F 𝟏[ F ]

\end{code}

Compacts opens are always closed undery binary joins.

\begin{code}

compacts-are-closed-under-joins : (F : Frame 𝓤 𝓥 𝓦)
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

well-inside₀ : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → 𝓤 ̇
well-inside₀ F U V =
 Σ W ꞉ ⟨ F ⟩ , (U ∧[ F ] W ≡ 𝟎[ F ]) × (V ∨[ F ] W ≡ 𝟏[ F ])

infix 4 well-inside₀

syntax well-inside₀ F U V = U ⋜₀[ F ] V

\end{code}

The well inside relation is not propositional in general, even though the “has
complement” predicate (i.e. is well inside itself) is propositional.

\begin{code}

well-inside₀-is-not-prop : is-univalent 𝓤₀
                        → Σ F ꞉ Frame 𝓤₁ 𝓤₀ 𝓤₀ ,
                           (¬ ((U V : ⟨ F ⟩) → is-prop (U ⋜₀[ F ] V)))
well-inside₀-is-not-prop ua = IF , ε
 where
  IF : Frame 𝓤₁ 𝓤₀ 𝓤₀ -- “IF” standing for “initial frame”.
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
    γ = transport _holds (𝟏[ IF ] ≡⟨ p ⁻¹ ⟩ 𝟎[ IF ] ≡⟨ 𝟎-of-IF-is-⊥ ua ⟩ ⊥Ω ∎) ⋆

  ε : ¬ ((U V : ⟨ IF ⟩) → is-prop (well-inside₀ IF U V))
  ε ψ = 𝟎-is-not-𝟏 (pr₁ (from-Σ-≡ δ))
   where
    δ : γ₁ ≡ γ₂
    δ = ψ 𝟎[ IF ] 𝟏[ IF ] γ₁ γ₂

\end{code}

Because well inside is not propositional, we have to truncate it to get a
relation.

\begin{code}

well-inside : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → Ω 𝓤
well-inside F U V = ∥ U ⋜₀[ F ] V ∥Ω

infix 4 well-inside

syntax well-inside F U V = U ⋜[ F ] V

\end{code}

\begin{code}

well-inside-implies-below : (F : Frame 𝓤 𝓥 𝓦)
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

↑↑-is-upwards-closed : (F : Frame 𝓤 𝓥 𝓦)
                     → {U V W : ⟨ F ⟩}
                     → (U ⋜[ F ] V) holds
                     → (V ≤[ poset-of F ] W) holds
                     → (U ⋜[ F ] W) holds
↑↑-is-upwards-closed F {U} {V} {W} p q =
 ∥∥-rec (holds-is-prop (U ⋜[ F ] W)) γ p
  where
   open PosetReasoning (poset-of F)

   γ : U ⋜₀[ F ] V → (U ⋜[ F ] W) holds
   γ (T , c₁ , c₂) = ∣ T , c₁ , d₂ ∣
    where
     β : (𝟏[ F ] ≤[ poset-of F ] (W ∨[ F ] T)) holds
     β = 𝟏[ F ]      ≡⟨ c₂ ⁻¹                  ⟩ₚ
         V ∨[ F ] T  ≤⟨ ∨[ F ]-left-monotone q ⟩
         W ∨[ F ] T  ■

     d₂ : W ∨[ F ] T ≡ 𝟏[ F ]
     d₂ = only-𝟏-is-above-𝟏 F (W ∨[ F ] T) β

↓↓-is-downwards-closed : (F : Frame 𝓤 𝓥 𝓦)
                       → {U V W : ⟨ F ⟩}
                       → (V ⋜[ F ] W) holds
                       → (U ≤[ poset-of F ] V) holds
                       → (U ⋜[ F ] W) holds
↓↓-is-downwards-closed F {U} {V} {W} p q = ∥∥-rec ∥∥-is-prop γ p
 where
  open PosetReasoning (poset-of F)

  γ : V ⋜₀[ F ] W → (U ⋜[ F ] W) holds
  γ (T , c₁ , c₂) = ∣ T , (only-𝟎-is-below-𝟎 F (U ∧[ F ] T) β , c₂) ∣
   where
    β : ((U ∧[ F ] T) ≤[ poset-of F ] 𝟎[ F ]) holds
    β = U ∧[ F ] T  ≤⟨ ∧[ F ]-left-monotone q ⟩
        V ∧[ F ] T  ≡⟨ c₁                     ⟩ₚ
        𝟎[ F ]      ■

\end{code}

An open _U_ in a frame _A_ is *clopen* iff it is well-inside itself.

\begin{code}

is-clopen₀ : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → 𝓤 ̇
is-clopen₀ F U = Σ W ꞉ ⟨ F ⟩ , (U ∧[ F ] W ≡ 𝟎[ F ]) × (U ∨[ F ] W ≡ 𝟏[ F ])

is-clopen₀-is-prop : (F : Frame 𝓤 𝓥 𝓦) → (U : ⟨ F ⟩) → is-prop (is-clopen₀ F U)
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

is-clopen : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → Ω 𝓤
is-clopen F U = is-clopen₀ F U , is-clopen₀-is-prop F U

clopen-implies-well-inside-itself : (F : Frame 𝓤 𝓥 𝓦)
                                   → (U : ⟨ F ⟩)
                                   → (is-clopen F U ⇒ U ⋜[ F ] U) holds
clopen-implies-well-inside-itself F U = ∣_∣

well-inside-itself-implies-clopen : (F : Frame 𝓤 𝓥 𝓦)
                                          → (U : ⟨ F ⟩)
                                          → (U ⋜[ F ] U ⇒ is-clopen F U) holds
well-inside-itself-implies-clopen F U =
 ∥∥-rec (holds-is-prop (is-clopen F U)) id

clopenness-equivalent-to-well-inside-itself : (F : Frame 𝓤 𝓥 𝓦)
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

𝟎-is-clopen : (F : Frame 𝓤 𝓥 𝓦) → 𝟎[ F ] ⋜₀[ F ] 𝟎[ F ]
𝟎-is-clopen F = 𝟏[ F ] , β , γ
 where
  β : 𝟎[ F ] ∧[ F ] 𝟏[ F ] ≡ 𝟎[ F ]
  β = 𝟎-left-annihilator-for-∧ F 𝟏[ F ]

  γ : 𝟎[ F ] ∨[ F ] 𝟏[ F ] ≡ 𝟏[ F ]
  γ = 𝟏-right-annihilator-for-∨ F 𝟎[ F ]

\end{code}

\begin{code}

𝟎-is-well-inside-anything : (F : Frame 𝓤 𝓥 𝓦) (U : ⟨ F ⟩)
                          → (𝟎[ F ] ⋜[ F ] U) holds
𝟎-is-well-inside-anything F U =
 ↑↑-is-upwards-closed F ∣ 𝟎-is-clopen F ∣ (𝟎-is-bottom F U)

\end{code}

\begin{code}

well-inside-is-join-stable : (F : Frame 𝓤 𝓥 𝓦) {U₁ U₂ V : ⟨ F ⟩}
                           → (U₁ ⋜[ F ] V) holds
                           → (U₂ ⋜[ F ] V) holds
                           → ((U₁ ∨[ F ] U₂) ⋜[ F ] V) holds
well-inside-is-join-stable F {U₁} {U₂} {V} =
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

\section{Some properties}

\begin{code}

∨-is-scott-continuous : (F : Frame 𝓤 𝓥 𝓦)
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

∨-is-scott-continuous-eq : (F : Frame 𝓤 𝓥 𝓦)
                         → (U : ⟨ F ⟩)
                         → (S : Fam 𝓦 ⟨ F ⟩)
                         → (is-directed (poset-of F) S) holds
                         → U ∨[ F ] (⋁[ F ] S) ≡ ⋁[ F ] ⁅ U ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆
∨-is-scott-continuous-eq F U S dir =
 ⋁[ F ]-unique ⁅ U ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆ (U ∨[ F ] (⋁[ F ] S)) (γ , δ)
  where
   γ = pr₁ ((∨-is-scott-continuous F U) S dir)
   δ = pr₂ ((∨-is-scott-continuous F U) S dir)

⋜₀-implies-≪-in-compact-frames : (F : Frame 𝓤 𝓥 𝓦)
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

⋜-implies-≪-in-compact-frames : (F : Frame 𝓤 𝓥 𝓦)
                              → is-compact F holds
                              → (U V : ⟨ F ⟩) → (U ⋜[ F ] V ⇒ U ≪[ F ] V) holds
⋜-implies-≪-in-compact-frames F κ U V =
 ∥∥-rec (holds-is-prop (U ≪[ F ] V)) (⋜₀-implies-≪-in-compact-frames F κ U V)

clopens-are-compact-in-compact-frames : (F : Frame 𝓤 𝓥 𝓦)
                                      → is-compact F holds
                                      → (U : ⟨ F ⟩)
                                      → is-clopen F U holds
                                      → is-compact-open F U holds
clopens-are-compact-in-compact-frames F κ U =
 ⋜₀-implies-≪-in-compact-frames F κ  U U

\end{code}

\section{Regularity}

We would like to be able to express regularity using `↓↓` defined as:

\begin{code}

↓↓[_] : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → Fam 𝓤 ⟨ F ⟩
↓↓[ F ] U = (Σ V ꞉ ⟨ F ⟩ , (V ⋜[ F ] U) holds) , pr₁

\end{code}

but there are size problems with this. Therefore, we define regularity as
follows:

\begin{code}

is-regular₀ : (F : Frame 𝓤 𝓥 𝓦) → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) ̇
is-regular₀ {𝓤 = 𝓤} {𝓥} {𝓦} F =
 let
  open Joins (λ U V → U ≤[ poset-of F ] V)

  P : Fam 𝓦 ⟨ F ⟩ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
  P ℬ = Π U ꞉ ⟨ F ⟩ ,
         Σ J ꞉ Fam 𝓦 (index ℬ) ,
            (U is-lub-of ⁅ ℬ [ j ] ∣ j ε J ⁆) holds
          × (Π i ꞉ index J , (ℬ [ J [ i ] ] ⋜[ F ] U) holds)
 in
  Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ , P ℬ

\end{code}

\begin{code}

is-regular : (F : Frame 𝓤 𝓥 𝓦) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-regular {𝓤 = 𝓤} {𝓥} {𝓦} F = ∥ is-regular₀ F ∥Ω

\end{code}

Even though this definition is a bit more convenient to work with, it simply
asserts the existence of a regular basis i.e. a basis in which every open in a
basic covering family for some open `U` is well inside `U`.

\begin{code}

is-regular-basis : (F : Frame 𝓤 𝓥 𝓦)
                 → (ℬ : Fam 𝓦 ⟨ F ⟩) → (β : is-basis-for F ℬ) → Ω (𝓤 ⊔ 𝓦)
is-regular-basis F ℬ β =
 Ɐ U ∶ ⟨ F ⟩ , let 𝒥 = pr₁ (β U) in Ɐ j ∶ (index 𝒥) , ℬ [ 𝒥 [ j ] ] ⋜[ F ] U

\end{code}

A projection for easily referring to the basis of a regular frame:

\begin{code}

basisᵣ : (F : Frame 𝓤 𝓥 𝓦)
       → (is-regular F ⇒ has-basis F) holds
basisᵣ F r = ∥∥-rec (holds-is-prop (has-basis F)) γ r
 where
  γ : is-regular₀ F → has-basis F holds
  γ (ℬ , δ)= ∣ ℬ , (λ U → pr₁ (δ U) , pr₁ (pr₂ (δ U))) ∣

\end{code}

When we directify the basis of a regular frame, the directified basis is also
regular:

\begin{code}

directification-preserves-regularity : (F : Frame 𝓤 𝓥 𝓦)
                                     → (ℬ : Fam 𝓦 ⟨ F ⟩)
                                     → (β : is-basis-for F ℬ)
                                     → is-regular-basis F ℬ β holds
                                     → let
                                        ℬ↑ = directify F ℬ
                                        β↑ = directified-basis-is-basis F ℬ β
                                       in
                                        is-regular-basis F ℬ↑ β↑ holds
directification-preserves-regularity F ℬ β r U = γ
 where
  ℬ↑ = directify F ℬ
  β↑ = directified-basis-is-basis F ℬ β

  𝒥  = pr₁ (β U)
  𝒥↑ = pr₁ (β↑ U)

  γ : (Ɐ js ∶ index 𝒥↑ , ℬ↑ [ 𝒥↑ [ js ] ] ⋜[ F ] U) holds
  γ []       = 𝟎-is-well-inside-anything F U
  γ (j ∷ js) = well-inside-is-join-stable F (r U j) (γ js)

\end{code}

This gives us that covering families in a regular frame are directed from
which the result we are interested in follows:

\begin{code}

≪-implies-⋜-in-regular-frames : (F : Frame 𝓤 𝓥 𝓦)
                              → (is-regular F) holds
                              → (U V : ⟨ F ⟩)
                              → (U ≪[ F ] V ⇒ U ⋜[ F ] V) holds
≪-implies-⋜-in-regular-frames {𝓦 = 𝓦} F r U V =
 ∥∥-rec (holds-is-prop (U ≪[ F ] V ⇒ U ⋜[ F ] V)) γ r
  where
   γ : is-regular₀ F → (U ≪[ F ] V ⇒ U ⋜[ F ] V) holds
   γ (ℬ , δ) κ = ∥∥-rec (holds-is-prop (U ⋜[ F ] V)) ζ (κ S ε c)
    where
     ℬ↑ : Fam 𝓦 ⟨ F ⟩
     ℬ↑ = directify F ℬ

     β : is-basis-for F ℬ
     β U = pr₁ (δ U) , pr₁ (pr₂ (δ U))

     β↑ : is-basis-for F ℬ↑
     β↑ = directified-basis-is-basis F ℬ β

     ρ : is-regular-basis F ℬ β holds
     ρ U = pr₂ (pr₂ (δ U))

     ρ↑ : is-regular-basis F ℬ↑ β↑ holds
     ρ↑ = directification-preserves-regularity F ℬ β ρ

     𝒥 : Fam 𝓦 (index ℬ↑)
     𝒥 = pr₁ (β↑ V)

     S : Fam 𝓦 ⟨ F ⟩
     S = ⁅ ℬ↑ [ i ] ∣ i ε 𝒥 ⁆

     ε : is-directed (poset-of F) S holds
     ε = covers-of-directified-basis-are-directed F ℬ β V

     c : (V ≤[ poset-of F ] (⋁[ F ] S)) holds
     c = reflexivity+ (poset-of F) (⋁[ F ]-unique S V (pr₂ (β↑ V)))

     ζ : Σ k ꞉ index S , (U ≤[ poset-of F ] (S [ k ])) holds → (U ⋜[ F ] V) holds
     ζ (k , q) = ↓↓-is-downwards-closed F (ρ↑ V k) q

\end{code}

\begin{code}

compacts-are-clopen-in-regular-frames : (F : Frame 𝓤 𝓥 𝓦)
                                      → is-regular F holds
                                      → (Ɐ U ∶ ⟨ F ⟩ ,
                                          is-compact-open F U ⇒ is-clopen F U) holds
compacts-are-clopen-in-regular-frames F r U =
 well-inside-itself-implies-clopen F U ∘ ≪-implies-⋜-in-regular-frames F r U U

\end{code}

\section{Zero-dimensionality}

A locale L is said to be zero-dimensional iff it has a basis consisting of
clopen elements.

\begin{code}

consists-of-clopens : (F : Frame 𝓤 𝓥 𝓦) → (S : Fam 𝓦 ⟨ F ⟩) → Ω (𝓤 ⊔ 𝓦)
consists-of-clopens F S = Ɐ i ∶ index S , is-clopen F (S [ i ])

zero-dimensionalᴰ : Frame 𝓤 𝓥 𝓦 → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) ̇
zero-dimensionalᴰ {𝓦 = 𝓦} F =
 Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ , is-basis-for F ℬ × consists-of-clopens F ℬ holds

is-zero-dimensional : Frame 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-zero-dimensional {𝓦 = 𝓦} F =
 Ǝ ℬ ∶ Fam 𝓦 ⟨ F ⟩ , is-basis-for F ℬ × consists-of-clopens F ℬ holds

basis-of-zero-dimensional-frame : (F : Frame 𝓤 𝓥 𝓦)
                                → (is-zero-dimensional F ⇒ has-basis F) holds
basis-of-zero-dimensional-frame F =
 ∥∥-rec (holds-is-prop (has-basis F)) λ { (ℬ , δ , _) → ∣ ℬ , δ ∣ }

\end{code}

Every zero-dimensional locale is regular.

\begin{code}

zero-dimensional-locales-are-regular : (F : Frame 𝓤 𝓥 𝓦)
                                     → is-zero-dimensional F holds
                                     → is-regular F holds
zero-dimensional-locales-are-regular {𝓦 = 𝓦} F =
 ∥∥-rec (holds-is-prop (is-regular F)) γ
  where
   open Joins (λ x y → x ≤[ poset-of F ] y)

   γ : zero-dimensionalᴰ F → is-regular F holds
   γ (ℬ , β , ξ) = ∣ ℬ , δ ∣
    where
     δ : Π U ꞉ ⟨ F ⟩ ,
          Σ J ꞉ Fam 𝓦 (index ℬ) ,
             (U is-lub-of (fmap-syntax (_[_] ℬ) J)) holds
           × (Π i ꞉ index J , (ℬ [ J [ i ] ] ⋜[ F ] U) holds)
     δ U = 𝒥 , c , ε
      where
       𝒥 = pr₁ (β U)

       c : (U is-lub-of ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆) holds
       c = pr₂ (β U)

       ε : Π i ꞉ index 𝒥 , (ℬ [ 𝒥 [ i ] ] ⋜[ F ] U) holds
       ε i = ↑↑-is-upwards-closed F ∣ ξ (𝒥 [ i ]) ∣ (pr₁ c i)
        where
         η : ((ℬ [ 𝒥 [ i ] ]) ≤[ poset-of F ] (ℬ [ 𝒥 [ i ] ])) holds
         η = ≤-is-reflexive (poset-of F) (ℬ [ 𝒥 [ i ] ])

\end{code}

\section{Stone Locales}

A frame F is called Stone iff it is compact and zero-dimensional.

\begin{code}

is-stone : (F : Frame 𝓤 𝓥 𝓦) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-stone F = is-compact F ∧ is-zero-dimensional F

\end{code}

In a Stone locale, an open is a clopen iff it is compact.

\begin{code}

clopen-iff-compact-in-stone-frame : (F : Frame 𝓤 𝓥 𝓦)
                                  → is-stone F holds
                                  → (U : ⟨ F ⟩)
                                  → (is-clopen F U holds)
                                  ⇔ (is-compact-open F U holds)
clopen-iff-compact-in-stone-frame F (κ , ζ) U = β , γ
 where
  β : (is-clopen F U ⇒ is-compact-open F U) holds
  β = clopens-are-compact-in-compact-frames F κ U

  ρ : is-regular F holds
  ρ = zero-dimensional-locales-are-regular F ζ

  γ : (is-compact-open F U ⇒ is-clopen F U) holds
  γ = compacts-are-clopen-in-regular-frames F ρ U

\end{code}

\section{Spectrality}

\begin{code}

consists-of-compact-opens : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
consists-of-compact-opens F U = Ɐ i ∶ index U , is-compact-open F (U [ i ])

contains-top : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
contains-top F U = Ǝ t ∶ index U , is-top F (U [ t ]) holds

closed-under-binary-meets : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
closed-under-binary-meets F 𝒮 =
 Ɐ i ∶ index 𝒮 , Ɐ j ∶ index 𝒮 ,
  Ǝ k ∶ index 𝒮 , ((𝒮 [ k ]) is-glb-of (𝒮 [ i ] , 𝒮 [ k ])) holds
   where
    open Meets (λ x y → x ≤[ poset-of F ] y)

closed-under-finite-meets : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
closed-under-finite-meets F S = contains-top F S ∧ closed-under-binary-meets F S

spectralᴰ : Frame 𝓤 𝓥 𝓦 → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) ̇
spectralᴰ {𝓤 = 𝓤} {𝓥} {𝓦} F =
 Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ , is-basis-for F ℬ
                   × consists-of-compact-opens F ℬ holds
                   × closed-under-finite-meets F ℬ holds

basisₛ : (F : Frame 𝓤 𝓥 𝓦) → spectralᴰ F → Fam 𝓦 ⟨ F ⟩
basisₛ F (ℬ , _) = ℬ

is-spectral : Frame 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-spectral F = ∥ spectralᴰ F ∥Ω

spectral-frames-have-bases : (F : Frame 𝓤 𝓥 𝓦) → (is-spectral F ⇒ has-basis F) holds
spectral-frames-have-bases F σ = ∥∥-rec ∥∥-is-prop γ σ
 where
  γ : spectralᴰ F → ∥ Σ ℬ ꞉ Fam _ ⟨ F ⟩ , is-basis-for F ℬ ∥
  γ (ℬ , p) = ∣ ℬ , pr₁ p ∣

\end{code}

\begin{code}

cofinal-in : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Fam 𝓦 ⟨ F ⟩ → Ω (𝓥 ⊔ 𝓦)
cofinal-in F R S =
 Ɐ i ∶ index R , Ǝ j ∶ index S , ((R [ i ]) ≤[ poset-of F ] (S [ j ])) holds

cofinal-implies-join-covered : (F : Frame 𝓤 𝓥 𝓦) (R S : Fam 𝓦 ⟨ F ⟩)
                             → cofinal-in F R S holds
                             → ((⋁[ F ] R) ≤[ poset-of F ] (⋁[ F ] S)) holds
cofinal-implies-join-covered F R S φ = ⋁[ F ]-least R ((⋁[ F ] S) , β)
 where
  open PosetReasoning (poset-of F)

  β : (i : index R) → ((R [ i ]) ≤[ poset-of F ] (⋁[ F ] S)) holds
  β i = ∥∥-rec (holds-is-prop ((R [ i ]) ≤[ poset-of F ] (⋁[ F ] S))) γ (φ i)
   where
    γ : Σ j ꞉ index S , ((R [ i ]) ≤[ poset-of F ] (S [ j ])) holds
        → ((R [ i ]) ≤[ poset-of F ] (⋁[ F ] S)) holds
    γ (j , p) = R [ i ] ≤⟨ p ⟩ S [ j ] ≤⟨ ⋁[ F ]-upper S j ⟩ ⋁[ F ] S ■

bicofinal-implies-same-join : (F : Frame 𝓤 𝓥 𝓦) (R S : Fam 𝓦 ⟨ F ⟩)
                            → cofinal-in F R S holds
                            → cofinal-in F S R holds
                            → ⋁[ F ] R ≡ ⋁[ F ] S
bicofinal-implies-same-join F R S φ ψ =
 ≤-is-antisymmetric
  (poset-of F)
  (cofinal-implies-join-covered F R S φ)
  (cofinal-implies-join-covered F S R ψ)

compact-rel-syntax : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
compact-rel-syntax F U V =
 Ɐ W ∶ ⟨ F ⟩ , is-compact-open F W ⇒ W ≤[ poset-of F ] U ⇒ W ≤[ poset-of F ] V

syntax compact-rel-syntax F U V = U ≤ₖ[ F ] V

spectral-yoneda : (F : Frame 𝓤 𝓥 𝓦) → is-spectral F holds → (U V : ⟨ F ⟩)
                → (U ≤ₖ[ F ] V ⇒ U ≤[ poset-of F ] V) holds
spectral-yoneda {𝓦 = 𝓦} F σ U V χ =
 ∥∥-rec (holds-is-prop (U ≤[ poset-of F ] V)) γ σ
  where
   open PosetReasoning (poset-of F)
   open Joins (λ x y → x ≤[ poset-of F ] y)
   open JoinNotation (λ - → ⋁[ F ] -)

   γ : spectralᴰ F → (U ≤[ poset-of F ] V) holds
   γ (ℬ , υ , φ , ψ) =
    U                            ≡⟨ I  ⟩ₚ
    ⋁[ F ] ⁅ ℬ [ i ] ∣ i ε ℐ ⁆   ≤⟨ ii ⟩
    V                            ■
    where
     ℐ : Fam 𝓦 (index ℬ)
     ℐ = pr₁ (υ U)

     I : U ≡ ⋁[ F ] ⁅ ℬ [ i ] ∣ i ε ℐ ⁆
     I = ⋁[ F ]-unique ⁅ ℬ [ i ] ∣ i ε ℐ ⁆ U (pr₂ (υ U))

     ϑ : (i : index ℐ) → ((ℬ [ ℐ [ i ] ]) ≤[ poset-of F ] U) holds
     ϑ i = ℬ [ ℐ [ i ] ]               ≤⟨ ⋁[ F ]-upper ⁅ ℬ [ i ] ∣ i ε ℐ ⁆ i ⟩
           ⋁[ F ] ⁅ ℬ [ i ] ∣ i ε ℐ ⁆  ≡⟨ I ⁻¹                               ⟩ₚ
           U                           ■

     ξ : (V is-an-upper-bound-of ⁅ ℬ [ i ] ∣ i ε ℐ ⁆) holds
     ξ i = χ (ℬ [ ℐ [ i ] ]) (φ (ℐ [ i ])) (ϑ i)

     ii : ((⋁[ F ] ⁅ ℬ [ i ] ∣ i ε ℐ ⁆) ≤[ poset-of F ] V) holds
     ii = ⋁[ F ]-least ⁅ ℬ [ i ] ∣ i ε ℐ ⁆ (V , ξ)

\end{code}

\begin{code}

compacts-are-basic-in-spectralᴰ-frames : (F : Frame 𝓤 𝓥 𝓦)
                                       → (σ : spectralᴰ F)
                                       → (U : ⟨ F ⟩)
                                       → is-compact-open F U holds
                                       → let
                                          ℬ  = basisₛ F σ
                                          ℬ↑ = directify F ℬ
                                          I  = index ℬ↑
                                         in
                                          ∥ Σ i ꞉ I , U ≡ ℬ↑ [ i ] ∥
compacts-are-basic-in-spectralᴰ-frames {𝓦 = 𝓦} F σ U κ =
 ∥∥-rec ∥∥-is-prop γ (κ ⁅ ℬ↑ [ i ] ∣ i ε ℐ ⁆ δ c)
  where
   open PosetReasoning (poset-of F)

   ℬ  = basisₛ F σ
   ℬ↑ = directify F ℬ

   b : is-basis-for F ℬ
   b = pr₁ (pr₂ σ)

   b↑ : is-basis-for F ℬ↑
   b↑ = directified-basis-is-basis F ℬ b

   𝒥 = covering-index-family F ℬ  b  U
   ℐ = covering-index-family F ℬ↑ b↑ U

   δ : is-directed (poset-of F) ⁅ ℬ↑ [ i ] ∣ i ε ℐ ⁆ holds
   δ = covers-of-directified-basis-are-directed F ℬ b U

   υ = pr₂ (pr₁ (pr₂ σ) U)

   c : (U ≤[ poset-of F ] (⋁[ F ] ⁅ ℬ↑ [ i ] ∣ i ε ℐ ⁆)) holds
   c = reflexivity+ (poset-of F) (covers F ℬ↑ b↑ U)

   γ : (Σ k ꞉ index ℐ , (U ≤[ poset-of F ] (ℬ↑ [ ℐ [ k ] ])) holds)
     → ∥ Σ i ꞉ index ℬ↑ , U ≡ ℬ↑ [ i ] ∥
   γ (k , p) = ∣ ℐ [ k ] , ≤-is-antisymmetric (poset-of F) p β ∣
    where
     β : ((ℬ↑ [ ℐ [ k ] ]) ≤[ poset-of F ] U) holds
     β = ℬ↑ [ ℐ [ k ] ]              ≤⟨ ⋁[ F ]-upper ⁅ ℬ↑ [ i ] ∣ i ε ℐ ⁆ k ⟩
         ⋁[ F ] ⁅ ℬ↑ [ i ] ∣ i ε ℐ ⁆ ≡⟨ covers F ℬ↑ b↑ U ⁻¹                 ⟩ₚ
         U                           ■

-- TODO: it's not clear if this lemma will be needed. Think more about this and
-- remove it if it turns out that it won't be needed.
compact-meet-lemma : (F : Frame 𝓤 𝓥 𝓦)
                   → (U V K : ⟨ F ⟩)
                   → is-compact-open F K holds
                   → (K ≤[ poset-of F ] (U ∧[ F ] V)) holds
                   → Σ K₁ ꞉ ⟨ F ⟩ ,  Σ K₂ ꞉ ⟨ F ⟩ ,
                       is-compact-open F K₁ holds
                     × is-compact-open F K₂ holds
                     × ((K ≤[ poset-of F ] (K₁ ∧[ F ] K₂)) holds)
                     × (((K₁ ≤[ poset-of F ] U) ∧ (K₂ ≤[ poset-of F ] V)) holds)
compact-meet-lemma F U V K κ p = K , K , κ , κ , γ , p₁ , p₂
  where
   open PosetReasoning (poset-of F)

   γ : (K ≤[ poset-of F ] (K ∧[ F ] K)) holds
   γ = ∧[ F ]-greatest K K K
        (≤-is-reflexive (poset-of F) K)
        (≤-is-reflexive (poset-of F) K)

   p₁ : (K ≤[ poset-of F ] U) holds
   p₁ = K ≤⟨ p ⟩ U ∧[ F ] V ≤⟨ ∧[ F ]-lower₁ U V ⟩ U ■

   p₂ : (K ≤[ poset-of F ] V) holds
   p₂ = K ≤⟨ p ⟩ U ∧[ F ] V ≤⟨ ∧[ F ]-lower₂ U V ⟩ V ■

\end{code}
