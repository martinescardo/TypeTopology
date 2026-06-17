Ayberk Tosun, 10 March 2021.

Based in part on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.FunExt
open import UF.PropTrunc

module Locales.InitialFrame
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame pt fe
open import Slice.Family
open import UF.Logic
open import UF.Sets
open import UF.Subsingletons
open import UF.SubtypeClassifier

open AllCombinators pt fe

\end{code}

\section{The underlying poset}

We start with the partial ordering on `Ω`:

\begin{code}

_⊑_ : Ω 𝓥 → Ω 𝓦 → Ω (𝓥 ⊔ 𝓦)
P ⊑ Q = P ⇒ Q

⊑-is-reflexive : is-reflexive {A = Ω 𝓤} _⊑_ holds
⊑-is-reflexive P = id

⊑-is-transitive : is-transitive {A = Ω 𝓤} _⊑_ holds
⊑-is-transitive _ _ _ p q = q ∘ p

⊑-is-antisymmetric : {𝓤 : Universe} → propext 𝓤 → is-antisymmetric {A = Ω 𝓤} _⊑_
⊑-is-antisymmetric pe {P} {Q} φ ψ = Ω-ext pe fe † ‡
 where
  † : P ＝ ⊤ → Q ＝ ⊤
  † = holds-gives-equal-⊤ pe fe Q ∘ φ ∘ equal-⊤-gives-true (P holds) (holds-is-prop P)

  ‡ : Q ＝ ⊤ → P ＝ ⊤
  ‡ = holds-gives-equal-⊤ pe fe P ∘ ψ ∘ equal-⊤-gives-true (Q holds) (holds-is-prop Q)

⊑-is-partial-order : {𝓤 : Universe} → propext 𝓤 → is-partial-order (Ω 𝓤) _⊑_
⊑-is-partial-order pe =
 (⊑-is-reflexive , ⊑-is-transitive) , ⊑-is-antisymmetric pe

\end{code}

This gives us a poset structure at universe 𝓤:

\begin{code}

𝟎F-poset-str : {𝓤 : Universe} → propext 𝓤 → poset-structure 𝓤 (Ω 𝓤)
𝟎F-poset-str pe = _⊑_
                , (⊑-is-reflexive , ⊑-is-transitive)
                , ⊑-is-antisymmetric pe

𝟎F-poset : {𝓤 : Universe} → propext 𝓤 → Poset (𝓤 ⁺) 𝓤
𝟎F-poset {𝓤 = 𝓤} pe = Ω 𝓤 , 𝟎F-poset-str pe

\end{code}

\section{Definition of the initial frame}

\begin{code}

open propositional-truncations-exist pt

𝟎-𝔽𝕣𝕞 : {𝓤 : Universe} → propext 𝓤 → Frame (𝓤 ⁺) 𝓤 𝓤
𝟎-𝔽𝕣𝕞 {𝓤 = 𝓤} pe = Ω 𝓤 , (_⊑_ , ⊤ {𝓤} , _∧_ , ⋁_)
      , ⊑-is-partial-order pe , top , meet , join , dist
 where
  ⋁_ : Fam 𝓤 (Ω 𝓤) → Ω 𝓤
  ⋁ U = Ǝ i ꞉ index U , ((U [ i ]) holds)

  open Meets _⊑_ renaming (is-top to is-the-top)

  top : is-the-top (⊤ {𝓤}) holds
  top _ _ = ⋆

  meet : (Ɐ (P , Q) , (P ∧ Q) is-glb-of (P , Q)) holds
  meet (P , Q) = β , γ
   where
    β : ((P ∧ Q) is-a-lower-bound-of (P , Q)) holds
    β = pr₁ , pr₂

    γ : (Ɐ (R , _) ꞉ lower-bound (P , Q ) , R ⊑ (P ∧ Q)) holds
    γ (R , ϕ , ψ) r = ϕ r , ψ r

  open Joins        _⊑_
  open JoinNotation ⋁_

  join : (Ɐ U ꞉ Fam 𝓤 (Ω 𝓤) , ((⋁ U) is-lub-of U)) holds
  join U = (λ i u → ∣ i , u ∣) , γ
   where
    γ : (Ɐ (P , _) ꞉ upper-bound U , (⋁ U) ⊑ P) holds
    γ ((A , A-prop) , q) r = ∥∥-rec A-prop (uncurry q) r

  abstract
   iss : is-set (Ω 𝓤)
   iss = carrier-of-[ 𝟎F-poset pe ]-is-set

   dist : (Ɐ(P , U) ꞉ Ω 𝓤 × Fam 𝓤 (Ω 𝓤) ,
           (P ∧ (⋁ U) ＝[ iss ]＝  ⋁⟨ i ⟩ P ∧ U [ i ])) holds
   dist (P , U) = ≤-is-antisymmetric (𝟎F-poset pe) β γ
    where
     β : (P ∧ ⋁ U ⇒ (⋁⟨ i ⟩ (P ∧ U [ i ]))) holds
     β (p , u) = ∥∥-rec (holds-is-prop (⋁⟨ i ⟩ (P ∧ U [ i ]))) α u
      where
       α : Σ i ꞉ index U , (U [ i ]) holds → (⋁⟨ i ⟩ P ∧ U [ i ]) holds
       α (i , uᵢ) = ∣ i , p , uᵢ ∣

     γ : ((⋁⟨ i ⟩ P ∧ U [ i ]) ⇒ P ∧ ⋁ U) holds
     γ p = ∥∥-rec (holds-is-prop (P ∧ (⋁ U))) δ p
      where
       δ : Sigma (index (index U , (λ i → P ∧ U [ i ])))
             (λ i → ((index U , (λ i₁ → P ∧ U [ i₁ ])) [ i ]) holds) →
             (P ∧ (⋁ U)) holds
       δ (i , q , uᵢ) = q , ∣ i , uᵢ ∣

\end{code}

\begin{code}
𝟎-of-IF-is-⊥ : {𝓦 : Universe} → (pe : propext 𝓦) → 𝟎[ 𝟎-𝔽𝕣𝕞 pe ] ＝ ⊥
𝟎-of-IF-is-⊥ pe =
 ≤-is-antisymmetric (poset-of (𝟎-𝔽𝕣𝕞 pe)) γ λ ()
 where
  γ : (𝟎[ 𝟎-𝔽𝕣𝕞 pe ] ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ]  ⊥) holds
  γ x = ∥∥-rec 𝟘-is-prop (λ ()) x
\end{code}

\section{Proof of initiality}

\begin{code}

f : {𝓦 : Universe} → (pe : propext 𝓦) → (A : Frame 𝓤 𝓥 𝓦) → ⟨ 𝟎-𝔽𝕣𝕞 pe ⟩ → ⟨ A ⟩
f pe A P = ⋁[ A ] ⁅ 𝟏[ A ] ∣ x ∶ P holds ⁆

\end{code}

\begin{code}

f-respects-⊤ : {𝓦 : Universe} (pe : propext 𝓦) (A : Frame 𝓤 𝓥 𝓦)
             → f pe A 𝟏[ 𝟎-𝔽𝕣𝕞 pe ] ＝ 𝟏[ A ]
f-respects-⊤ pe A = ≤-is-antisymmetric (poset-of A) α β
 where
  open PosetNotation (poset-of A) renaming (_≤_ to _≤A_)

  α : (f pe A 𝟏[ 𝟎-𝔽𝕣𝕞 pe ] ≤A 𝟏[ A ]) holds
  α = 𝟏-is-top A (f pe A 𝟏[ 𝟎-𝔽𝕣𝕞 pe ])

  β : (𝟏[ A ] ≤A f pe A 𝟏[ 𝟎-𝔽𝕣𝕞 pe ]) holds
  β = ⋁[ A ]-upper (⁅ 𝟏[ A ] ∣ x ∶ ⊤ holds ⁆) ⋆

\end{code}

\begin{code}

f-respects-∧ : {𝓦 : Universe} (pe : propext 𝓦)
             → (A : Frame 𝓤 𝓥 𝓦)
             → (P Q : Ω 𝓦)
             → f pe A (P ∧ Q) ＝ (f pe A P) ∧[ A ] (f pe A Q)
f-respects-∧ pe A P Q =
 f pe A (P ∧ Q)                                      ＝⟨refl⟩
 ⋁[ A ] ⁅ 𝟏[ A ] ∣ _ ∶ (P ∧ Q) holds ⁆               ＝⟨ i    ⟩
 ⋁[ A ] ⁅ 𝟏[ A ] ∧[ A ] 𝟏[ A ] ∣ _ ∶ (P ∧ Q) holds ⁆ ＝⟨ ii   ⟩
 (f pe A P) ∧[ A ] (f pe A Q)                        ∎
 where
  i  = ap (λ - → ⋁[ A ] ⁅ - ∣ _ ∶ _ ⁆) (∧[ A ]-is-idempotent 𝟏[ A ])
  ii = distributivity+ A ⁅ 𝟏[ A ] ∣ _ ∶ P holds ⁆ ⁅ 𝟏[ A ] ∣ _ ∶ Q holds ⁆ ⁻¹

\end{code}

\begin{code}

f-respects-⋁ : {𝓦 : Universe} → (pe : propext 𝓦)
             → (A : Frame 𝓤 𝓥 𝓦) (U : Fam 𝓦 (Ω 𝓦))
             → let open Joins (λ x y → x ≤[ poset-of A ] y) in
               ((f pe A (⋁[ 𝟎-𝔽𝕣𝕞 pe ] U)) is-lub-of ⁅ f pe A x ∣ x ε U ⁆) holds
f-respects-⋁ pe A U = β , γ
 where
  open Joins (λ x y → x ≤[ poset-of A ] y)
  open PosetReasoning (poset-of A) renaming (_■ to _QED)
  open PosetNotation (poset-of A)

  β : ((f pe A (⋁[ 𝟎-𝔽𝕣𝕞 pe ] U))
       is-an-upper-bound-of
       ⁅ f pe A x ∣ x ε U ⁆) holds
  β i = ⋁[ A ]-least
         ⁅ 𝟏[ A ] ∣ _ ∶ (U [ i ]) holds ⁆
         (_ , λ p → ⋁[ A ]-upper _ ∣ i , p ∣)

  γ : (Ɐ (x , _) ꞉ upper-bound ⁅ f pe A u ∣ u ε U ⁆ ,
        f pe A (⋁[ 𝟎-𝔽𝕣𝕞 pe ] U) ≤ x) holds
  γ (x , p) =
   ⋁[ A ]-least _ (_ , ∥∥-rec (holds-is-prop (_ ≤ _)) ι)
   where
    ι : (Σ i ꞉ index U , (U [ i ]) holds) → (𝟏[ A ] ≤ x) holds
    ι (i , uᵢ) = 𝟏[ A ] ≤⟨ ⋁[ A ]-upper _ uᵢ ⟩ _ ≤⟨ p i ⟩ x QED


\end{code}

\begin{code}

open FrameHomomorphisms
open FrameHomomorphismProperties

𝒻 : {𝓦 : Universe} (pe : propext 𝓦) (F : Frame 𝓤 𝓥 𝓦)
  → (𝟎-𝔽𝕣𝕞 pe) ─f→ F
𝒻 pe F = (f pe F)
       , f-respects-⊤ pe F
       , f-respects-∧ pe F
       , f-respects-⋁ pe F

\end{code}

\begin{code}

main-lemma : {𝓦 : Universe} (pe : propext 𝓦) (P : Ω 𝓦)
           → (P ⊑ (⋁[ 𝟎-𝔽𝕣𝕞 pe ] ⁅ 𝟏[ 𝟎-𝔽𝕣𝕞 pe ] ∣ x ∶ P holds ⁆)) holds
main-lemma pe P p =
 ⋁[ 𝟎-𝔽𝕣𝕞 pe ]-upper (⁅ 𝟏[ 𝟎-𝔽𝕣𝕞 pe ] ∣ x ∶ P holds ⁆) p ⋆

\end{code}

\begin{code}

𝒻-is-unique : {𝓦 : Universe} (pe : propext 𝓦) (F : Frame 𝓤 𝓥 𝓦)
            → (ℊ : (𝟎-𝔽𝕣𝕞 pe) ─f→ F)
            → 𝒻 pe F ＝ ℊ
𝒻-is-unique pe F ℊ@ (g , ζ@ (ϕ , χ , ψ)) =
 to-subtype-＝ (holds-is-prop ∘ is-a-frame-homomorphism (𝟎-𝔽𝕣𝕞 pe) F) β
 where
  open Joins (λ x y → x ≤[ poset-of F ] y)
  open PosetReasoning (poset-of F) renaming (_■ to _QED)

  g-is-monotonic : is-monotonic (𝟎F-poset pe) (poset-of F) g holds
  g-is-monotonic =
   frame-morphisms-are-monotonic (𝟎-𝔽𝕣𝕞 pe) F g ζ

  γ : f pe F ∼ g
  γ P = ⋁[ F ]-unique _ _ (δ , ε) ⁻¹
   where
    δ : (g P is-an-upper-bound-of (P holds , λ _ → 𝟏[ F ])) holds
    δ p = 𝟏[ F ] ≤⟨ reflexivity+ (poset-of F) (ϕ ⁻¹)  ⟩
          g ⊤   ≤⟨ g-is-monotonic (⊤ , P) (λ _ → p) ⟩
          g P    QED


    ε : (Ɐ (u , _) ꞉ upper-bound (P holds , λ _ → 𝟏[ F ]) ,
          g P ≤[ poset-of F ] u) holds
    ε (u , q) =
     g P                                   ≤⟨ i                      ⟩
     g (⋁[ 𝟎-𝔽𝕣𝕞 pe ] ⁅ ⊤ ∣ _ ∶ P holds ⁆) ≤⟨ ii                     ⟩
     ⋁[ F ] ⁅ g ⊤ ∣ _ ∶ P holds ⁆          ≤⟨ iii                    ⟩
     ⋁[ F ] ⁅ 𝟏[ F ] ∣ _ ∶ P holds ⁆       ≤⟨ ⋁[ F ]-least _ (u , q) ⟩
     u                                     QED
     where
      i  = g-is-monotonic
            (P , (⋁[ 𝟎-𝔽𝕣𝕞 pe ] ⁅ ⊤ ∣ _ ∶ (P holds) ⁆))
            (main-lemma pe P)
      ii  = reflexivity+
             (poset-of F)
             ((⋁[ F ]-unique _ _ (ψ (⁅ ⊤ ∣ _ ∶ (P holds) ⁆))))
      iii = reflexivity+
             (poset-of F)
             (ap (λ - → ⋁[ F ] (P holds , -)) (dfunext fe υ))
       where
        υ : (λ _ → g ⊤) ∼ (λ _ → 𝟏[ F ])
        υ _ = ϕ

  β : f pe F ＝ g
  β = dfunext fe γ

\end{code}

\begin{code}

𝟎-𝔽𝕣𝕞-initial : {𝓦 : Universe} (pe : propext 𝓦) (F : Frame 𝓤 𝓥 𝓦)
              → is-singleton (𝟎-𝔽𝕣𝕞 pe ─f→ F)
𝟎-𝔽𝕣𝕞-initial pe F = (𝒻 pe F) , 𝒻-is-unique pe F

\end{code}

The initial frame is the terminal locale

\begin{code}

𝟏Loc : {𝓤 : Universe} (pe : propext 𝓤) → Locale (𝓤 ⁺) 𝓤 𝓤
𝟏Loc {𝓤} pe = record { ⟨_⟩ₗ = Ω 𝓤 ; frame-str-of = pr₂ (𝟎-𝔽𝕣𝕞 pe)}

\end{code}

\section{Spectrality}

\begin{code}

module Spectrality-of-𝟎 (𝓤 : Universe) (pe : propext 𝓤) where

 ℬ𝟎 : Fam 𝓤 ⟨ 𝟎-𝔽𝕣𝕞 pe ⟩
 ℬ𝟎 = 𝟚 𝓤 , h
  where
   h : 𝟚 𝓤 → ⟨ 𝟎-𝔽𝕣𝕞 pe ⟩
   h (inl ⋆) = ⊥
   h (inr ⋆) = ⊤

\end{code}

\begin{code}

 𝒮 : ⟨ 𝟎-𝔽𝕣𝕞 pe ⟩ → Fam 𝓤 (𝟚 𝓤)
 𝒮 (P , p) = ⁅ inr ⋆ ∣ _ ∶ P ⁆

 ℬ𝟎-is-basis-for-𝟎 : is-basis-for (𝟎-𝔽𝕣𝕞 pe) ℬ𝟎
 ℬ𝟎-is-basis-for-𝟎 (P , p) = 𝒮 (P , p) , β , γ
  where
   open Joins (λ x y → x ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ] y)

   β : ((P , p) is-an-upper-bound-of ⁅ ℬ𝟎 [ b ] ∣ b ε 𝒮 (P , p) ⁆) holds
   β p ⋆ = p

   open PosetReasoning (poset-of (𝟎-𝔽𝕣𝕞 pe))

   γ : ((u , _) : upper-bound ⁅ ℬ𝟎 [ b ] ∣ b ε 𝒮 (P , p) ⁆)
     → ((P , p) ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ] u) holds
   γ (U , q) p = q p ⋆

 ℬ𝟎↑ : Fam 𝓤 ⟨ 𝟎-𝔽𝕣𝕞 pe ⟩
 ℬ𝟎↑ = directify (𝟎-𝔽𝕣𝕞 pe) ℬ𝟎

 ℬ𝟎↑-is-basis : is-basis-for (𝟎-𝔽𝕣𝕞 pe) ℬ𝟎↑
 ℬ𝟎↑-is-basis = directified-basis-is-basis (𝟎-𝔽𝕣𝕞 pe) ℬ𝟎 ℬ𝟎-is-basis-for-𝟎

 𝒮↑ : ⟨ 𝟎-𝔽𝕣𝕞 pe ⟩ → Fam 𝓤 ⟨ 𝟎-𝔽𝕣𝕞 pe ⟩
 𝒮↑ U = ⁅ ℬ𝟎↑ [ b ] ∣ b ε pr₁ (ℬ𝟎↑-is-basis U) ⁆

\end{code}

\begin{code}

 ℬ𝟎-is-directed-basis-for-𝟎 : is-directed-basis (𝟎-𝔽𝕣𝕞 pe) ℬ𝟎↑
 ℬ𝟎-is-directed-basis-for-𝟎 = ℬ𝟎↑-is-basis , d
  where
   d : (U : ⟨ 𝟎-𝔽𝕣𝕞 pe ⟩) → is-directed (𝟎-𝔽𝕣𝕞 pe) (𝒮↑ U) holds
   d = covers-of-directified-basis-are-directed (𝟎-𝔽𝕣𝕞 pe) ℬ𝟎 ℬ𝟎-is-basis-for-𝟎

\end{code}

Added on 2024-05-17.

It is sometimes convenient to refer to the initial frame as “Ω viewed as a
frame”, and we add some notation to highlight this.

\begin{code}

 Ω-Frm : Frame (𝓤 ⁺) 𝓤 𝓤
 Ω-Frm = 𝟎-𝔽𝕣𝕞 pe

\end{code}
