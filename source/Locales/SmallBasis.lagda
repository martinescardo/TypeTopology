Ayberk Tosun, 21 August 2023

These used to live in the `CompactRegular` module which is now deprecated and
will be broken down into smaller modules.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons
open import UF.Logic
open import MLTT.Spartan
open import UF.Size
open import UF.Base
open import UF.EquivalenceExamples using (Σ-assoc)

module Locales.SmallBasis (pt : propositional-truncations-exist)
                          (fe : Fun-Ext)
                          (sr : Set-Replacement pt) where

open import Locales.Frame       pt fe hiding (has-directed-basis₀)
open import Locales.Compactness pt fe
open import Locales.Spectrality pt fe
open import Slice.Family
open import UF.ImageAndSurjection pt
open import UF.Equiv renaming (_■ to _𝒬ℰ𝒟)
open import MLTT.List using (List; map; _<$>_; []; _∷_)

open PropositionalTruncation pt

open AllCombinators pt fe

open Locale

\end{code}

We start by defining the structure of having a basis. The superscript _ᴰ is our
notational convention for marking that we are working with the structural
version of a notion.

\begin{code}

basis-forᴰ : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
basis-forᴰ {𝓦 = 𝓦} F (I , β) =
 (U : ⟨ F ⟩) → Σ J ꞉ Fam 𝓦 I , (U is-lub-of ⁅ β j ∣ j ε J ⁆) holds
  where
   open Joins (λ x y → x ≤[ poset-of F ] y)

basisᴰ : (F : Frame 𝓤 𝓥 𝓦) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
basisᴰ {𝓤} {𝓥} {𝓦} F = Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ , basis-forᴰ F ℬ

\end{code}

We will often have to talk about "directed bases": bases in which the covering
families are directed.

\begin{code}

directed-basis-forᴰ : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
directed-basis-forᴰ {𝓤} {𝓥} {𝓦} F ℬ@(I , β) =
 (U : ⟨ F ⟩) →
  Σ J ꞉ Fam 𝓦 I ,
   (U is-lub-of ⁅ β j ∣ j ε J ⁆ ∧ is-directed F ⁅ β j ∣ j ε J ⁆) holds
    where
     open Joins (λ x y → x ≤[ poset-of F ] y)

directed-basisᴰ : (F : Frame 𝓤 𝓥 𝓦) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
directed-basisᴰ {𝓤} {𝓥} {𝓦} F =
 Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ , directed-basis-forᴰ F ℬ

directed-basis-is-basis : (F : Frame 𝓤 𝓥 𝓦) (ℬ : Fam 𝓦 ⟨ F ⟩)
                        → directed-basis-forᴰ F ℬ
                        → basis-forᴰ F ℬ
directed-basis-is-basis {_} {_} {𝓦} F ℬ β U = † (β U)
 where
  open Joins (λ x y → x ≤[ poset-of F ] y)

  † : Σ J ꞉ Fam 𝓦 (index ℬ) ,
       (U is-lub-of ⁅ ℬ [ j ] ∣ j ε J ⁆ ∧ is-directed F ⁅ ℬ [ j ] ∣ j ε J ⁆)
        holds
    → Σ J ꞉ Fam 𝓦 (index ℬ) , (U is-lub-of ⁅ ℬ [ j ] ∣ j ε J ⁆) holds
  † (J , c , _)= J , c

\end{code}

In `spectralₛᴰ`, we give the old definition of a spectral locale that bakes in
the small basis assumption. We use the `ₛ` subscript to differentiate it from
the new one.

\begin{code}

contains-top : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
contains-top F U = Ǝ t ꞉ index U , is-top F (U [ t ]) holds

closed-under-binary-meets : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
closed-under-binary-meets F 𝒮 =
 Ɐ i ꞉ index 𝒮 , Ɐ j ꞉ index 𝒮 ,
  Ǝ k ꞉ index 𝒮 , ((𝒮 [ k ]) is-glb-of (𝒮 [ i ] , 𝒮 [ j ])) holds
   where
    open Meets (λ x y → x ≤[ poset-of F ] y)

closed-under-finite-meets : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
closed-under-finite-meets F S = contains-top F S ∧ closed-under-binary-meets F S

spectralₛᴰ : Locale 𝓤 𝓥 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
spectralₛᴰ {_} {_} {𝓦} X =
  Σ ℬ ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ ,
     is-directed-basis (𝒪 X) ℬ
   × consists-of-compact-opens X ℬ holds
   × closed-under-finite-meets (𝒪 X) ℬ holds

\end{code}

The previous definition of spectrality was the truncation of `spectralₛᴰ`:

\begin{code}

is-spectralₛ : Locale 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-spectralₛ X = ∥ spectralₛᴰ X ∥Ω

\end{code}

Compact opens are basic:

\begin{code}

is-basic : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → directed-basisᴰ (𝒪 X) → Ω (𝓤 ⊔ 𝓦)
is-basic X U (ℬ , β) = U ∈image (ℬ [_]) , ∃-is-prop

compact-opens-are-basic : (X : Locale 𝓤 𝓥 𝓦)
                        → (b : directed-basisᴰ (𝒪 X))
                        → (K : ⟨ 𝒪 X ⟩)
                        → is-compact-open X K holds
                        → is-basic X K b holds
compact-opens-are-basic {_} {_} {𝓦} X (ℬ , β) K κ = ‡ (β K)
 where
  open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

  ‡ : (Σ 𝒥 ꞉ Fam 𝓦 (index ℬ) , (K is-lub-of ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ ∧ is-directed (𝒪 X) ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆) holds)
    → is-basic X K (ℬ , β) holds
  ‡ (𝒥 , c , d) =
   ∥∥-rec (holds-is-prop (is-basic X K (ℬ , β))) † (κ ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ d q)
    where
     q : (K ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆)) holds
     q = reflexivity+ (poset-of (𝒪 X)) (⋁[ 𝒪 X ]-unique ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ K c)

     † : Σ j ꞉ index 𝒥 , (K ≤[ poset-of (𝒪 X) ] ℬ [ 𝒥 [ j ] ]) holds
       → is-basic X K (ℬ , β) holds
     † (j , φ) = ∣ 𝒥 [ j ] , ≤-is-antisymmetric (poset-of (𝒪 X)) ψ φ ∣
      where
       open PosetReasoning (poset-of (𝒪 X))

       Ⅰ = ⋁[ 𝒪 X ]-upper ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ j
       Ⅱ = reflexivity+ (poset-of (𝒪 X)) ((⋁[ 𝒪 X ]-unique ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ K c) ⁻¹)

       ψ : (ℬ [ 𝒥 [ j ] ] ≤[ poset-of (𝒪 X) ] K) holds
       ψ = ℬ [ 𝒥 [ j ] ] ≤⟨ Ⅰ ⟩ ⋁[ 𝒪 X ] ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ ≤⟨ Ⅱ ⟩ K ■

\end{code}

One of the things that we show in this module is that this truncation was
unnecessary as the basis is unique in the presence of a small basis.

We now define the following crucial predicate expressing what it means for the
type of compact opens of a locale to be small:

\begin{code}

has-small-𝒦 : Locale 𝓤 𝓥 𝓦 → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)  ̇
has-small-𝒦 {_} {_} {𝓦} X = 𝒦 X is 𝓦 small

\end{code}

\begin{code}

basis-is-unique : (X : Locale 𝓤 𝓥 𝓦)
                → ((ℬ , _) : directed-basisᴰ (𝒪 X))
                → consists-of-compact-opens X ℬ holds
                → image (ℬ-compact X [_]) ≃ image (ℬ [_])
basis-is-unique X (ℬ , b) κ =
 r , (s , s-is-section-of-r) , s , r-is-retract-of-s
  where
   r : image (ℬ-compact X [_]) → image (ℬ [_])
   r (K , p) = K , K-is-basic
    where
     K-is-compact : is-compact-open X K holds
     K-is-compact = ∥∥-rec (holds-is-prop (is-compact-open X K)) † p
      where
       † : Σ (λ x → ℬ-compact X [ x ] ＝ K) → is-compact-open X K holds
       † ((K′ , κ′) , q) = transport (λ - → is-compact-open X - holds) q κ′

     K-is-basic : K ∈image (ℬ [_])
     K-is-basic =
      ∥∥-rec ∃-is-prop † (compact-opens-are-basic X (ℬ , b) K K-is-compact)
       where
        † : Σ i ꞉ index ℬ , ℬ [ i ] ＝ K → ∃ j ꞉ index ℬ , ℬ [ j ] ＝ K
        † (i , p) = ∣ i , p ∣

   s : image (ℬ [_]) → image (ℬ-compact X [_])
   s (K , p) = K , ∥∥-rec ∃-is-prop † p
    where
     † : Σ i ꞉ index ℬ , ℬ [ i ] ＝ K → ∃ (K′ , _) ꞉ index (ℬ-compact X) , K′ ＝ K
     † (i , q) = ∣ (ℬ [ i ] , κ i) , q ∣

   s-is-section-of-r : r ∘ s ∼ id
   s-is-section-of-r (U , p) = to-subtype-＝ (λ _ → ∃-is-prop) refl

   r-is-retract-of-s : s ∘ r ∼ id
   r-is-retract-of-s (K , p) = to-subtype-＝ (λ _ → ∃-is-prop) refl

\end{code}

Having a directed basis is a proposition under certain favourable conditions.

\begin{code}

basic-iso-to-𝒦 : (X : Locale 𝓤 𝓥 𝓦)
               → ((ℬ , b) : directed-basisᴰ (𝒪 X))
               → consists-of-compact-opens X ℬ holds
               → image (ℬ [_]) ≃ 𝒦 X
basic-iso-to-𝒦 X (ℬ , β) κ =
 image (ℬ [_])             ≃⟨ Ⅰ ⟩
 image (ℬ-compact X [_])   ≃⟨ Ⅱ ⟩
 𝒦 X                       𝒬ℰ𝒟
  where
   Ⅰ : image (ℬ [_]) ≃ image (ℬ-compact X [_])
   Ⅰ = ≃-sym (basis-is-unique X (ℬ , β) κ)

   Ⅱ : image (ℬ-compact X [_]) ≃ 𝒦 X
   Ⅱ = s , (r , ψ) , (r , ϑ)
    where
     s : image (ℬ-compact X [_]) → 𝒦 X
     s (K , c) = K , ∥∥-rec (holds-is-prop (is-compact-open X K)) † c
      where
       † : Σ i ꞉ index (ℬ-compact X) , ℬ-compact X [ i ] ＝ K
         → is-compact-open X K holds
       † ((K′ , φ) , p) = transport (λ - → is-compact-open X - holds) p φ

     r : 𝒦 X → image (ℬ-compact X [_])
     r (K , p) = K , ∣ (K , p) , refl ∣

     ψ : s ∘ r ∼ id
     ψ (K , p) = to-subtype-＝ (holds-is-prop ∘ is-compact-open X) refl

     ϑ : (r ∘ s) ∼ id
     ϑ (K , p) = to-subtype-＝ (λ _ → ∃-is-prop) refl

\end{code}

\begin{code}

local-smallness : (X : Locale 𝓤 𝓦 𝓦)
                → ⟨ 𝒪 X ⟩ is-locally 𝓦 small
local-smallness {𝓤} {𝓦} X = †
 where
  _≡ₓ_ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → Ω 𝓦
  U ≡ₓ V = (U ≤[ poset-of (𝒪 X) ] V) ∧ (V ≤[ poset-of (𝒪 X) ] U)

  † : ⟨ 𝒪 X ⟩ is-locally 𝓦 small
  † U V = (U ≡ₓ V) holds , e
   where
    e : (U ≡ₓ V) holds ≃ (U ＝ V)
    e = logically-equivalent-props-are-equivalent
         (holds-is-prop (U ≡ₓ V))
         carrier-of-[ poset-of (𝒪 X) ]-is-set
         (λ (p , q) → ≤-is-antisymmetric (poset-of (𝒪 X)) p q)
         λ p → (reflexivity+ (poset-of (𝒪 X)) p) , reflexivity+ (poset-of (𝒪 X)) (p ⁻¹)

\end{code}

\begin{code}

basic-is-small : (X : Locale 𝓤 𝓥 𝓦)
               → ((ℬ , b) : directed-basisᴰ (𝒪 X))
               → ⟨ 𝒪 X ⟩ is-locally 𝓦 small
               → (image (ℬ [_])) is 𝓦 small
basic-is-small X (ℬ , b) ψ =
 sr (ℬ [_]) (index ℬ , ≃-refl (index ℬ)) ψ carrier-of-[ poset-of (𝒪 X) ]-is-set

\end{code}

\begin{code}

𝒦-is-small : (X : Locale 𝓤 𝓥 𝓦)
           → ((ℬ , b) : directed-basisᴰ (𝒪 X))
           → consists-of-compact-opens X ℬ holds
           → ⟨ 𝒪 X ⟩ is-locally 𝓦 small
           → (𝒦 X) is 𝓦 small
𝒦-is-small {𝓤} {𝓥} {𝓦} X (ℬ , b) κ ψ = B₀ , e
 where
  σ : image (ℬ [_]) is 𝓦 small
  σ = basic-is-small X (ℬ , b) ψ

  B₀ : 𝓦  ̇
  B₀ = pr₁ σ

  Ⅰ = pr₂ σ
  Ⅱ = basic-iso-to-𝒦 X (ℬ , b) κ

  e : B₀ ≃ 𝒦 X
  e = B₀ ≃⟨ Ⅰ ⟩ image (ℬ [_]) ≃⟨ Ⅱ ⟩ 𝒦 X 𝒬ℰ𝒟

\end{code}

\begin{code}

spectral-yoneda : (X : Locale 𝓤 𝓥 𝓦)
                → is-spectral X holds
                → (U V : ⟨ 𝒪 X ⟩)
                → (((K , _) : 𝒦 X) → (K ≤[ poset-of (𝒪 X) ] U) holds → (K ≤[ poset-of (𝒪 X) ] V) holds)
                → (U ≤[ poset-of (𝒪 X) ] V) holds
spectral-yoneda {_} {_} {𝓦} X (_ , c) U V φ =
 ∥∥-rec (holds-is-prop (U ≤[ poset-of (𝒪 X) ] V)) † (c U)
  where
   open PosetReasoning (poset-of (𝒪 X))

   † : Σ S ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ ,
        consists-of-compact-opens X S holds × (is-directed (𝒪 X) S holds) × (U ＝ ⋁[ 𝒪 X ] S)
     → (U ≤[ poset-of (𝒪 X) ] V) holds
   † (S , κ , d , c) = U            ≤⟨ Ⅰ ⟩
                       ⋁[ 𝒪 X ] S   ≤⟨ Ⅱ ⟩
                       V            ■
                        where
                         Ⅰ = reflexivity+ (poset-of (𝒪 X)) c
                         Ⅱ = ⋁[ 𝒪 X ]-least S (V , (λ i → φ (S [ i ] , κ i) (S [ i ] ≤⟨ ⋁[ 𝒪 X ]-upper S i ⟩ ⋁[ 𝒪 X ] S ＝⟨ c ⁻¹ ⟩ₚ U ■)))

\end{code}

\begin{code}

spectral-and-small-𝒦-gives-basis : (X : Locale 𝓤 𝓦 𝓦)
                                 → is-spectral X holds
                                 → 𝒦 X is 𝓦 small
                                 → basisᴰ (𝒪 X)
spectral-and-small-𝒦-gives-basis {𝓤} {𝓦} X 𝕤 (𝒦₀ , e) = (𝒦₀ , α) , β
 where
  open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
  open PosetReasoning (poset-of (𝒪 X))

  sec : 𝒦₀ → 𝒦 X
  sec = pr₁ e

  ret : 𝒦 X → 𝒦₀
  ret = pr₁ (pr₁ (pr₂ e))

  α : 𝒦₀ → ⟨ 𝒪 X ⟩
  α = pr₁ ∘ sec

  β : basis-forᴰ (𝒪 X) (𝒦₀ , α)
  β U = 𝒥 , † , ‡
   where
    𝒥 : Fam 𝓦 𝒦₀
    𝒥 = (Σ k ꞉ 𝒦₀ , (α k ≤[ poset-of (𝒪 X) ] U) holds) , pr₁

    † : (U is-an-upper-bound-of ⁅ α j ∣ j ε 𝒥 ⁆) holds
    † = pr₂

    ‡ : ((u , _) : upper-bound ⁅ α j ∣ j ε 𝒥 ⁆) → (U ≤[ poset-of (𝒪 X) ] u) holds
    ‡ (V , ψ) = spectral-yoneda X 𝕤 U V λ { (K , p) → ♣ K p }
     where
      ♣ : (K : ⟨ 𝒪 X ⟩)
        → (is-compact-open X K ⇒ K ≤[ poset-of (𝒪 X) ] U ⇒ K ≤[ poset-of (𝒪 X) ] V) holds
      ♣ K κ p = K ≤⟨ c₀ ⟩ ⋁[ 𝒪 X ] ⁅ α j ∣ j ε 𝒥 ⁆ ≤⟨ ⋁[ 𝒪 X ]-least ⁅ α j ∣ j ε 𝒥 ⁆ (V , (λ i → ψ i)) ⟩ V ■
       where
        iₖ : 𝒦₀
        iₖ = ret (K , κ)

        tmp : sec (ret (K , κ)) ＝ (K , κ)
        tmp = pr₂ (pr₁ (pr₂ e)) (K , κ)

        ϑ : (α iₖ ≤[ poset-of (𝒪 X) ] U) holds
        ϑ = α iₖ                    ＝⟨ refl ⟩ₚ
            pr₁ (sec (ret (K , κ))) ＝⟨ ap pr₁ tmp ⟩ₚ
            K                       ≤⟨ p ⟩
            U                       ■

        c₀ : (K ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] ⁅ α j ∣ j ε 𝒥 ⁆)) holds
        c₀ = K                       ＝⟨ pr₁ (from-Σ-＝ tmp) ⁻¹ ⟩ₚ
             pr₁ (sec (ret (K , κ))) ＝⟨ refl ⟩ₚ
             α iₖ                    ≤⟨ ⋁[ 𝒪 X ]-upper ⁅ α j ∣ j ε 𝒥 ⁆ (iₖ , ϑ) ⟩
             ⋁[ 𝒪 X ] (fmap-syntax (λ j → α j) 𝒥) ■


\end{code}

\begin{code}

spectral-and-small-𝒦-gives-directed-basis : (X : Locale 𝓤 𝓦 𝓦)
                                          → is-spectral X holds
                                          → 𝒦 X is 𝓦 small
                                          → directed-basisᴰ (𝒪 X)
spectral-and-small-𝒦-gives-directed-basis {_} {𝓦} X σ 𝕤 =
 ℬ↑ , ℬ↑-is-directed-basis-for-X
  where
   basis-X : basisᴰ (𝒪 X)
   basis-X = spectral-and-small-𝒦-gives-basis X σ 𝕤

   ℬ : Fam 𝓦 ⟨ 𝒪 X ⟩
   ℬ = pr₁ basis-X

   β : basis-forᴰ (𝒪 X) ℬ
   β = pr₂ basis-X

   ℬ↑ : Fam 𝓦 ⟨ 𝒪 X ⟩
   ℬ↑ = directify (𝒪 X) ℬ

   β↑ : basis-forᴰ (𝒪 X) ℬ↑
   β↑ = directified-basis-is-basis (𝒪 X) ℬ β

   ℬ↑-is-directed-basis-for-X : directed-basis-forᴰ (𝒪 X) ℬ↑
   ℬ↑-is-directed-basis-for-X U = pr₁ Σ-assoc (β↑ U , d)
    where
     𝒥 : Fam 𝓦 (index ℬ↑)
     𝒥 = pr₁ (β↑ U)

     d : is-directed (𝒪 X) ⁅ ℬ↑ [ j ] ∣ j ε 𝒥 ⁆ holds
     d = covers-of-directified-basis-are-directed (𝒪 X) ℬ β U

\end{code}

\begin{code}

spectralᴰ : Locale 𝓤 𝓥 𝓦 → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) ̇
spectralᴰ {𝓤 = 𝓤} {𝓥} {𝓦} X =
 Σ ℬ ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ , directed-basis-forᴰ (𝒪 X) ℬ
                     × consists-of-compact-opens X ℬ holds
                     × closed-under-finite-meets (𝒪 X) ℬ holds

basisₛ : (X : Locale 𝓤 𝓥 𝓦) → spectralᴰ X → Fam 𝓦 ⟨ 𝒪 X ⟩
basisₛ {𝓤} {𝓥} {𝓦} X = pr₁

basisₛ-is-basis : (X : Locale 𝓤 𝓥 𝓦) (σᴰ : spectralᴰ X)
                → basis-forᴰ (𝒪 X) (basisₛ X σᴰ)
basisₛ-is-basis X σᴰ = directed-basis-is-basis (𝒪 X) (basisₛ X σᴰ) (pr₁ (pr₂ σᴰ))

cover-indexₛ : (X : Locale 𝓤 𝓥 𝓦) (σᴰ : spectralᴰ X)
             → let
                ℬ = basisₛ X σᴰ
               in
                ⟨ 𝒪 X ⟩ → Fam 𝓦 (index ℬ)
cover-indexₛ X σᴰ U = pr₁ (basisₛ-is-basis X σᴰ U)

basisₛ-covers-are-directed : (X : Locale 𝓤 𝓥 𝓦) (σᴰ : spectralᴰ X) (U : ⟨ 𝒪 X ⟩)
                           → let
                              ℬ = basisₛ X σᴰ
                              𝒥 = cover-indexₛ X σᴰ U
                             in
                              is-directed (𝒪 X) ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ holds
basisₛ-covers-are-directed X σᴰ U = pr₂ (pr₂ (pr₁ (pr₂ σᴰ) U))

basisₛ-contains-top : {!!}
basisₛ-contains-top = {!!}

\end{code}

Spectrality structure gives `is-spectral`.

\begin{code}

spectralᴰ-gives-spectrality : (X : Locale 𝓤 𝓥 𝓦) (σᴰ : spectralᴰ X)
                            → is-spectral X holds
spectralᴰ-gives-spectrality X σᴰ = ⦅𝟏⦆ , {!!}
 where
  κ : is-compact X holds
  κ = {!pr₁ (pr₂ (pr₂ (pr₂ σᴰ)))!}

  ⦅𝟏⦆ : compacts-of-[ X ]-are-closed-under-finite-meets holds
  ⦅𝟏⦆ = κ , {!!}

\end{code}
