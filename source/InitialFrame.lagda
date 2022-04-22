Ayberk Tosun, 10 March 2021.

Based in part on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import UF-Base
open import UF-PropTrunc
open import UF-FunExt
open import UF-Univalence
open import UF-UA-FunExt

module InitialFrame
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import UF-Subsingletons
open import UF-Subsingleton-Combinators
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import Frame pt fe
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

⊑-is-antisymmetric : {𝓤 : Universe} → is-univalent 𝓤 → is-antisymmetric {A = Ω 𝓤} _⊑_
⊑-is-antisymmetric ua = Ω-ext-from-univalence ua

⊑-is-partial-order : {𝓤 : Universe} → is-univalent 𝓤 → is-partial-order (Ω 𝓤) _⊑_
⊑-is-partial-order ua = (⊑-is-reflexive , ⊑-is-transitive) , ⊑-is-antisymmetric ua

\end{code}

This gives us a poset structure at universe 𝓤:

\begin{code}

𝟎F-poset-str : {𝓤 : Universe} → is-univalent 𝓤 → poset-structure 𝓤 (Ω 𝓤)
𝟎F-poset-str ua = _⊑_
                , (⊑-is-reflexive , ⊑-is-transitive)
                , ⊑-is-antisymmetric ua

𝟎F-poset : {𝓤 : Universe} → is-univalent 𝓤 → Poset (𝓤 ⁺) 𝓤
𝟎F-poset {𝓤 = 𝓤} ua = Ω 𝓤 , 𝟎F-poset-str ua

\end{code}

\section{Definition of the initial frame}

\begin{code}

open propositional-truncations-exist pt

𝟎-𝔽𝕣𝕞 : {𝓤 : Universe} → is-univalent 𝓤 → Frame (𝓤 ⁺) 𝓤 𝓤
𝟎-𝔽𝕣𝕞 {𝓤 = 𝓤} ua = Ω 𝓤 , (_⊑_ , ⊤Ω {𝓤} , _∧_ , ⋁_)
      , ⊑-is-partial-order ua , top , meet , join , dist
 where
  ⋁_ : Fam 𝓤 (Ω 𝓤) → Ω 𝓤
  ⋁ U = Ǝ i ∶ index U , ((U [ i ]) holds)

  open Meets _⊑_ renaming (is-top to is-the-top)

  top : is-the-top (⊤Ω {𝓤}) holds
  top _ _ = ⋆

  meet : (Ɐ (P , Q) , (P ∧ Q) is-glb-of (P , Q)) holds
  meet (P , Q) = β , γ
   where
    β : ((P ∧ Q) is-a-lower-bound-of (P , Q)) holds
    β = pr₁ , pr₂

    γ : (Ɐ (R , _) ∶ lower-bound (P , Q ) , R ⊑ (P ∧ Q)) holds
    γ (R , ϕ , ψ) r = ϕ r , ψ r

  open Joins        _⊑_
  open JoinNotation ⋁_

  join : (Ɐ U ∶ Fam 𝓤 (Ω 𝓤) , ((⋁ U) is-lub-of U)) holds
  join U = (λ i u → ∣ i , u ∣) , γ
   where
    γ : (Ɐ (P , _) ∶ upper-bound U , (⋁ U) ⊑ P) holds
    γ ((A , A-prop) , q) r = ∥∥-rec A-prop (uncurry q) r

  abstract
   iss : is-set (Ω 𝓤)
   iss = carrier-of-[ 𝟎F-poset ua ]-is-set

   dist : (Ɐ(P , U) ∶ Ω 𝓤 × Fam 𝓤 (Ω 𝓤) ,
           (P ∧ (⋁ U) ≡[ iss ]≡  ⋁⟨ i ⟩ P ∧ U [ i ])) holds
   dist (P , U) = Ω-ext-from-univalence ua β γ
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
𝟎-of-IF-is-⊥ : {𝓦 : Universe} → (ua : is-univalent 𝓦) → 𝟎[ 𝟎-𝔽𝕣𝕞 ua ] ≡ ⊥Ω
𝟎-of-IF-is-⊥ ua =
 ≤-is-antisymmetric (poset-of (𝟎-𝔽𝕣𝕞 ua)) γ λ ()
 where
  γ : (𝟎[ 𝟎-𝔽𝕣𝕞 ua ] ≤[ poset-of (𝟎-𝔽𝕣𝕞 ua) ]  ⊥Ω) holds
  γ x = ∥∥-rec 𝟘-is-prop (λ ()) x
\end{code}

\section{Proof of initiality}

\begin{code}

f : {𝓦 : Universe} → (ua : is-univalent 𝓦) → (A : Frame 𝓤 𝓥 𝓦) → ⟨ 𝟎-𝔽𝕣𝕞 ua ⟩ → ⟨ A ⟩
f ua A P = ⋁[ A ] ⁅ 𝟏[ A ] ∣ x ∶ P holds ⁆

\end{code}

\begin{code}

f-respects-⊤ : {𝓦 : Universe} (ua : is-univalent 𝓦) (A : Frame 𝓤 𝓥 𝓦)
             → f ua A 𝟏[ 𝟎-𝔽𝕣𝕞 ua ] ≡ 𝟏[ A ]
f-respects-⊤ ua A = ≤-is-antisymmetric (poset-of A) α β
 where
  open PosetNotation (poset-of A) renaming (_≤_ to _≤A_)

  α : (f ua A 𝟏[ 𝟎-𝔽𝕣𝕞 ua ] ≤A 𝟏[ A ]) holds
  α = 𝟏-is-top A (f ua A 𝟏[ 𝟎-𝔽𝕣𝕞 ua ])

  β : (𝟏[ A ] ≤A f ua A 𝟏[ 𝟎-𝔽𝕣𝕞 ua ]) holds
  β = ⋁[ A ]-upper (⁅ 𝟏[ A ] ∣ x ∶ ⊤Ω holds ⁆) ⋆

\end{code}

\begin{code}

f-respects-∧ : {𝓦 : Universe} (ua : is-univalent 𝓦)
             → (A : Frame 𝓤 𝓥 𝓦)
             → (P Q : Ω 𝓦)
             → f ua A (P ∧ Q) ≡ (f ua A P) ∧[ A ] (f ua A Q)
f-respects-∧ ua A P Q =
 f ua A (P ∧ Q)                                      ≡⟨ refl ⟩
 ⋁[ A ] ⁅ 𝟏[ A ] ∣ _ ∶ (P ∧ Q) holds ⁆               ≡⟨ i    ⟩
 ⋁[ A ] ⁅ 𝟏[ A ] ∧[ A ] 𝟏[ A ] ∣ _ ∶ (P ∧ Q) holds ⁆ ≡⟨ ii   ⟩
 (f ua A P) ∧[ A ] (f ua A Q)                        ∎
 where
  i  = ap (λ - → ⋁[ A ] ⁅ - ∣ _ ∶ _ ⁆) (∧[ A ]-is-idempotent 𝟏[ A ])
  ii = distributivity+ A ⁅ 𝟏[ A ] ∣ _ ∶ P holds ⁆ ⁅ 𝟏[ A ] ∣ _ ∶ Q holds ⁆ ⁻¹

\end{code}

\begin{code}

f-respects-⋁ : {𝓦 : Universe} → (ua : is-univalent 𝓦)
             → (A : Frame 𝓤 𝓥 𝓦) (U : Fam 𝓦 (Ω 𝓦))
             → let open Joins (λ x y → x ≤[ poset-of A ] y) in
               ((f ua A (⋁[ 𝟎-𝔽𝕣𝕞 ua ] U)) is-lub-of ⁅ f ua A x ∣ x ε U ⁆) holds
f-respects-⋁ ua A U = β , γ
 where
  open Joins (λ x y → x ≤[ poset-of A ] y)
  open PosetReasoning (poset-of A) renaming (_■ to _QED)
  open PosetNotation (poset-of A)

  β : ((f ua A (⋁[ 𝟎-𝔽𝕣𝕞 ua ] U))
       is-an-upper-bound-of
       ⁅ f ua A x ∣ x ε U ⁆) holds
  β i = ⋁[ A ]-least
         ⁅ 𝟏[ A ] ∣ _ ∶ (U [ i ]) holds ⁆
         (_ , λ p → ⋁[ A ]-upper _ ∣ i , p ∣)

  γ : (Ɐ (x , _) ∶ upper-bound ⁅ f ua A u ∣ u ε U ⁆ ,
        f ua A (⋁[ 𝟎-𝔽𝕣𝕞 ua ] U) ≤ x) holds
  γ (x , p) =
   ⋁[ A ]-least _ (_ , ∥∥-rec (holds-is-prop (_ ≤ _)) ι)
   where
    ι : (Σ i ꞉ index U , (U [ i ]) holds) → (𝟏[ A ] ≤ x) holds
    ι (i , uᵢ) = 𝟏[ A ] ≤⟨ ⋁[ A ]-upper _ uᵢ ⟩ _ ≤⟨ p i ⟩ x QED


\end{code}

\begin{code}

𝒻 : {𝓦 : Universe} (ua : is-univalent 𝓦) (F : Frame 𝓤 𝓥 𝓦)
  → (𝟎-𝔽𝕣𝕞 ua) ─f→ F
𝒻 ua F = (f ua F)
       , f-respects-⊤ ua F
       , f-respects-∧ ua F
       , f-respects-⋁ ua F

\end{code}

\begin{code}

main-lemma : {𝓦 : Universe} (ua : is-univalent 𝓦) (P : Ω 𝓦)
           → (P ⊑ (⋁[ 𝟎-𝔽𝕣𝕞 ua ] ⁅ 𝟏[ 𝟎-𝔽𝕣𝕞 ua ] ∣ x ∶ P holds ⁆)) holds
main-lemma ua P p =
 ⋁[ 𝟎-𝔽𝕣𝕞 ua ]-upper (⁅ 𝟏[ 𝟎-𝔽𝕣𝕞 ua ] ∣ x ∶ P holds ⁆) p ⋆

\end{code}

\begin{code}

𝒻-is-unique : {𝓦 : Universe} (ua : is-univalent 𝓦) (F : Frame 𝓤 𝓥 𝓦)
            → (ℊ : (𝟎-𝔽𝕣𝕞 ua) ─f→ F)
            → 𝒻 ua F ≡ ℊ
𝒻-is-unique ua F ℊ@ (g , ζ@ (ϕ , χ , ψ)) =
 to-subtype-≡ (holds-is-prop ∘ is-a-frame-homomorphism (𝟎-𝔽𝕣𝕞 ua) F) β
 where
  open Joins (λ x y → x ≤[ poset-of F ] y)
  open PosetReasoning (poset-of F) renaming (_■ to _QED)

  g-is-monotonic : is-monotonic (𝟎F-poset ua) (poset-of F) g holds
  g-is-monotonic =
   frame-morphisms-are-monotonic (𝟎-𝔽𝕣𝕞 ua) F g ζ

  γ : f ua F ∼ g
  γ P = ⋁[ F ]-unique _ _ (δ , ε) ⁻¹
   where
    δ : (g P is-an-upper-bound-of (P holds , λ _ → 𝟏[ F ])) holds
    δ p = 𝟏[ F ] ≤⟨ reflexivity+ (poset-of F) (ϕ ⁻¹)  ⟩
          g ⊤Ω   ≤⟨ g-is-monotonic (⊤Ω , P) (λ _ → p) ⟩
          g P    QED


    ε : (Ɐ (u , _) ∶ upper-bound (P holds , λ _ → 𝟏[ F ]) ,
          g P ≤[ poset-of F ] u) holds
    ε (u , q) =
     g P                                    ≤⟨ i                      ⟩
     g (⋁[ 𝟎-𝔽𝕣𝕞 ua ] ⁅ ⊤Ω ∣ _ ∶ P holds ⁆) ≤⟨ ii                     ⟩
     ⋁[ F ] ⁅ g ⊤Ω ∣ _ ∶ P holds ⁆          ≤⟨ iii                    ⟩
     ⋁[ F ] ⁅ 𝟏[ F ] ∣ _ ∶ P holds ⁆        ≤⟨ ⋁[ F ]-least _ (u , q) ⟩
     u                                      QED
     where
      i  = g-is-monotonic
            (P , (⋁[ 𝟎-𝔽𝕣𝕞 ua ] ⁅ ⊤Ω ∣ _ ∶ (P holds) ⁆))
            (main-lemma ua P)
      ii  = reflexivity+
             (poset-of F)
             ((⋁[ F ]-unique _ _ (ψ (⁅ ⊤Ω ∣ _ ∶ (P holds) ⁆))))
      iii = reflexivity+
             (poset-of F)
             (ap (λ - → ⋁[ F ] (P holds , -)) (dfunext fe υ))
       where
        υ : (λ _ → g ⊤Ω) ∼ (λ _ → 𝟏[ F ])
        υ _ = ϕ

  β : f ua F ≡ g
  β = dfunext fe γ

\end{code}

\begin{code}

𝟎-𝔽𝕣𝕞-initial : {𝓦 : Universe} (ua : is-univalent 𝓦) (F : Frame 𝓤 𝓥 𝓦)
              → is-singleton (𝟎-𝔽𝕣𝕞 ua ─f→ F)
𝟎-𝔽𝕣𝕞-initial ua F = (𝒻 ua F) , 𝒻-is-unique ua F

\end{code}
