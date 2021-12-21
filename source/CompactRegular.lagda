Ayberk Tosun, 9 December 2021

Based on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]
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
way-below : (F : frame 𝓤 𝓥 𝓦) → (x y : ⟨ F ⟩) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
way-below {𝓤 = 𝓤} {𝓦 = 𝓦} F x y =
 Ɐ S ∶ Fam 𝓦 ⟨ F ⟩ , is-directed (poset-of F) S ⇒
  y ≤ (⋁[ F ] S) ⇒ (Ǝ i ∶ index S , (x ≤ S [ i ]) holds)
   where
    open PosetNotation (poset-of F) using (_≤_)

infix 5 way-below

syntax way-below F x y = x ≪[ F ] y
\end{code}

\begin{code}

isCompactOpen : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
isCompactOpen F x = x ≪[ F ] x

\end{code}

A compact frame is simply a frame whose top element is finite.

\begin{code}

isCompact : frame 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
isCompact F = isCompactOpen F 𝟏[ F ]

\end{code}

\begin{code}

compacts-are-closed-under-joins : (F : frame 𝓤 𝓥 𝓦)
                                → (U V : ⟨ F ⟩)
                                → isCompactOpen F U holds
                                → isCompactOpen F V holds
                                → isCompactOpen F (U ∨[ F ] V) holds
compacts-are-closed-under-joins F U V κ₁ κ₂ S dir@(_ , up) p =
 ∥∥-rec₂ ∃-is-prop γ s₁′ s₂′
  where
   open PosetNotation  (poset-of F) using (_≤_)
   open PosetReasoning (poset-of F)

   -- S covers U.
   q₁ : (U ≤ (⋁[ F ] S)) holds
   q₁ = U ≤⟨ ∨[ F ]-upper₁ U V ⟩ U ∨[ F ] V ≤⟨ p ⟩ ⋁[ F ] S ■

   -- S covers V.
   q₂ : (V ≤ (⋁[ F ] S)) holds
   q₂ = V ≤⟨ ∨[ F ]-upper₂ U V ⟩ U ∨[ F ] V ≤⟨ p ⟩ ⋁[ F ] S ■

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

\begin{code}

well-inside : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → 𝓤 ̇ 
well-inside F U V =
 Σ W ꞉ ⟨ F ⟩ , (U ∧[ F ] W ≡ 𝟎[ F ]) × (V ∨[ F ] W ≡ 𝟏[ F ])

infix 4 well-inside

syntax well-inside F U V = U ⋜[ F ] V

-- The well inside relation is not propositional in general, even though the
-- “has complement” (i.e. is well inside itself) is propositional.
well-inside-is-not-prop : is-univalent 𝓤₀
                        → Σ F ꞉ frame 𝓤₁ 𝓤₀ 𝓤₀ ,
                           (¬ ((x y : ⟨ F ⟩) → is-prop (x ⋜[ F ] y)))
well-inside-is-not-prop ua = IF , ε
 where
  IF : frame 𝓤₁ 𝓤₀ 𝓤₀ -- “IF” standing for “initial frame”.
  IF = 𝟎-𝔽𝕣𝕞 ua

  γ₂ : 𝟎[ IF ] ⋜[ IF ] 𝟏[ IF ]
  γ₂ = 𝟏[ IF ] , (β , γ)
        where
         abstract
          β : 𝟎[ IF ] ∧[ IF ] 𝟏[ IF ] ≡ 𝟎[ IF ]
          β = 𝟎-left-annihilator-for-∧ IF 𝟏[ IF ]

          γ : 𝟏[ IF ] ∨[ IF ] 𝟏[ IF ] ≡ 𝟏[ IF ]
          γ = 𝟏-right-annihilator-for-∨ IF 𝟏[ IF ]

  γ₁ : 𝟎[ IF ] ⋜[ IF ] 𝟏[ IF ]
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

  ε : ¬ ((x y : ⟨ IF ⟩) → is-prop (well-inside IF x y))
  ε ψ = 𝟎-is-not-𝟏 (pr₁ (from-Σ-≡ δ))
   where
    δ : γ₁ ≡ γ₂
    δ = ψ 𝟎[ IF ] 𝟏[ IF ] γ₁ γ₂

well-inside-implies-below : (F : frame 𝓤 𝓥 𝓦)
                          → (U V : ⟨ F ⟩)
                          → U ⋜[ F ] V
                          → (U ≤[ poset-of F ] V) holds
well-inside-implies-below F U V (W , c₁ , c₂) = connecting-lemma₂ F γ
 where
  _⊓_ = λ x y → x ∧[ F ] y

  γ : U ≡ U ∧[ F ] V
  γ = U                        ≡⟨ 𝟏-right-unit-of-∧ F U ⁻¹              ⟩
      U ⊓ 𝟏[ F ]               ≡⟨ ap (U ⊓_) (c₂ ⁻¹)                     ⟩
      U ⊓ (V ∨[ F ] W)         ≡⟨ binary-distributivity F U V W         ⟩
      (U ⊓ V) ∨[ F ] (U ⊓ W)   ≡⟨ ap (λ - → binary-join F (U ⊓ V) -) c₁ ⟩
      (U ⊓ V) ∨[ F ] 𝟎[ F ]    ≡⟨ 𝟎-left-unit-of-∨ F (U ⊓ V)            ⟩
      U ⊓ V                    ∎

\end{code}

An open x in a frame F is *clopen* iff it is well-inside itself.

\begin{code}

is-clopen′ : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → 𝓤 ̇ 
is-clopen′ F U = Σ W ꞉ ⟨ F ⟩ , (U ∧[ F ] W ≡ 𝟎[ F ]) × (U ∨[ F ] W ≡ 𝟏[ F ])

is-clopen′-is-prop : (F : frame 𝓤 𝓥 𝓦) → (U : ⟨ F ⟩) → is-prop (is-clopen′ F U)
is-clopen′-is-prop F U (W₁ , p₁ , q₁) (W₂ , p₂ , q₂) = to-subtype-≡ β γ
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
        i   = ap (λ - → - ∨[ F ] (W₁ ∧[ F ] W₂)) (∧[ F ]-is-commutative W₁ U)
        ii  = ap (λ - → - ∨[ F ] (W₁ ∧[ F ] W₂)) p₁
        iii = ap (λ - → - ∨[ F ] (W₁ ∧[ F ] W₂)) (p₂ ⁻¹)
        iv  = ap (λ - → - ∨[ F ] (W₁ ∧[ F ] W₂)) (∧[ F ]-is-commutative U W₂)
        v   = ap (λ - → (W₂ ∧[ F ] U) ∨[ F ] -) (∧[ F ]-is-commutative W₁ W₂)
        vi  = binary-distributivity F W₂ U W₁ ⁻¹
        vii = ap (λ - → W₂ ∧[ F ] -) q₁
        viii = 𝟏-right-unit-of-∧ F W₂

is-clopen : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → Ω 𝓤
is-clopen F U = is-clopen′ F U , is-clopen′-is-prop F U

\end{code}

\section{Definition of regularity}

\begin{code}

↓↓[_] : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → Fam (𝓤 ⊔ 𝓥) ⟨ F ⟩
↓↓[ F ] x = (Σ y ꞉ ⟨ F ⟩ , (y ≤[ poset-of F ] x) holds) , pr₁

\end{code}

\begin{code}

isRegular : frame 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥)
isRegular F = Ɐ x ∶ ⟨ F ⟩ , x is-lub-of (↓↓[ F ] x)
  where
  open Joins (λ x y → x ≤[ poset-of F ] y)

\end{code}

\section{Some properties}

\begin{code}
∨-is-scott-continuous : (F : frame 𝓤 𝓥 𝓦)
                      → (x : ⟨ F ⟩)
                      → is-scott-continuous F F (λ - → x ∨[ F ] -) holds
∨-is-scott-continuous F x S dir = β , γ
 where
 open PosetNotation  (poset-of F) using (_≤_)
 open PosetReasoning (poset-of F)
 open Joins _≤_

 β : ((x ∨[ F ] (⋁[ F ] S)) is-an-upper-bound-of ⁅ x ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆) holds
 β i = ∨[ F ]-right-mono (⋁[ F ]-upper S i)

 γ : (Ɐ (u′ , _) ∶ upper-bound ⁅ x ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆ ,
       ((x ∨[ F ] (⋁[ F ] S)) ≤ u′)) holds
 γ (u′ , p) = ∨[ F ]-least γ₁ γ₂
  where
   δ₁ : index S → (x ≤ u′) holds
   δ₁ i = x                  ≤⟨ ∨[ F ]-upper₁ x (S [ i ]) ⟩
          x ∨[ F ] (S [ i ]) ≤⟨ p i                       ⟩
          u′                 ■

   γ₁ : (x ≤[ poset-of F ] u′) holds
   γ₁ = ∥∥-rec (holds-is-prop (x ≤[ poset-of F ] u′)) δ₁ (pr₁ dir)

   γ₂ : ((⋁[ F ] S) ≤[ poset-of F ] u′) holds
   γ₂ = ⋁[ F ]-least S (u′ , δ₂)
    where
     δ₂ : (u′ is-an-upper-bound-of S) holds
     δ₂ i = S [ i ]                         ≤⟨ ∨[ F ]-upper₂ x (S [ i ]) ⟩
            x ∨[ F ] (S [ i ])              ≤⟨ p i                       ⟩
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

⋜-implies-≪-in-compact-frames : (F : frame 𝓤 𝓥 𝓦)
                              → isCompact F holds
                              → (U V : ⟨ F ⟩)
                              → U ⋜[ F ] V
                              → (U ≪[ F ] V) holds
⋜-implies-≪-in-compact-frames {𝓦 = 𝓦} F κ U V (W , c₁ , c₂) S d q =
 ∥∥-rec ∃-is-prop θ ζ
  where
   open PosetNotation  (poset-of F)
   open PosetReasoning (poset-of F)

   T : Fam 𝓦 ⟨ F ⟩
   T = ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆

   δ : (𝟏[ F ] ≤ (⋁[ F ] T)) holds
   δ = 𝟏[ F ]                          ≡⟨ c₂ ⁻¹                              ⟩ₚ
       V ∨[ F ] W                      ≤⟨ ∨[ F ]-left-mono q                 ⟩
       (⋁[ F ] S) ∨[ F ] W             ≡⟨ ∨[ F ]-is-commutative (⋁[ F ] S) W ⟩ₚ
       W ∨[ F ] (⋁[ F ] S)             ≡⟨ ∨-is-scott-continuous-eq F W S d   ⟩ₚ
       ⋁[ F ] ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆ ■

   ε : ((W ∨[ F ] (⋁[ F ] S)) ≤ (⋁[ F ] T)) holds
   ε = W ∨[ F ] (⋁[ F ] S)              ≤⟨ 𝟏-is-top F (W ∨[ F ] (⋁[ F ] S)) ⟩
       𝟏[ F ]                           ≤⟨ δ                                ⟩
       ⋁[ F ] ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆  ■

   -- T is closed under binary upper bounds.
   up : (Ɐ i , Ɐ j ,
           Ǝ k , (T [ i ] ≤ T [ k ]) holds × (T [ j ] ≤ T [ k ]) holds) holds
   up i j = ∥∥-rec ∃-is-prop r (pr₂ d i j)
    where
     r  = λ (k , p , q) → ∣ k , ∨[ F ]-right-mono p , ∨[ F ]-right-mono q ∣

   T-is-directed : (is-directed (poset-of F) ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆) holds
   T-is-directed = pr₁ d , up

   ζ : ∥ Σ i ꞉ index S , (𝟏[ F ] ≤ (W ∨[ F ] (S [ i ]))) holds ∥
   ζ = κ ⁅ W ∨[ F ] Sᵢ ∣ Sᵢ ε S ⁆ T-is-directed δ

   θ : Σ i ꞉ index S , (𝟏[ F ] ≤ (W ∨[ F ] S [ i ])) holds
     → ∃ i ꞉ index S , (U ≤ S [ i ]) holds
   θ (i , p) = ∣ i , well-inside-implies-below F U (S [ i ]) (W , (c₁ , ι)) ∣
    where
     η = 𝟏[ F ]              ≤⟨ p                                 ⟩
         W ∨[ F ] (S [ i ])  ≡⟨ ∨[ F ]-is-commutative W (S [ i ]) ⟩ₚ
         (S [ i ]) ∨[ F ] W  ■

     ι = only-𝟏-is-above-𝟏 F ((S [ i ]) ∨[ F ] W) η

clopens-are-compact-in-compact-frames : (F : frame 𝓤 𝓥 𝓦)
                                      → isCompact F holds
                                      → (x : ⟨ F ⟩)
                                      → is-clopen F x holds
                                      → isCompactOpen F x holds
clopens-are-compact-in-compact-frames F κ x = ⋜-implies-≪-in-compact-frames F κ x x

\end{code}
