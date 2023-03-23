Andrew Sneap, 10 March 2022

This file is a work in progress. I define continuity, and prove that
the embedding ι : ℚ → ℝ is continuous. There are many sketch proofs
towards proving the continuous extension theorem.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.CanonicalMap
open import UF.Base
open import UF.Subsingletons
open import UF.FunExt
open import UF.PropTrunc
open import Notation.Order

open import Rationals.Type
open import Rationals.Order
open import Rationals.Multiplication


module MetricSpaces.ContinuousExtensionTheorem
 (fe : Fun-Ext)
 (pe : Prop-Ext)
 (pt : propositional-truncations-exist)
  where

open PropositionalTruncation pt

open import DedekindReals.Type pe pt fe
open import MetricSpaces.Definition pt fe pe
open import MetricSpaces.DedekindReals pt fe pe
open import MetricSpaces.Rationals fe pt pe
open import Rationals.Limits fe pt pe
open import DedekindReals.Properties fe pt pe

\end{code}

The goal of this file is to prove the continous extension theorem constructively.

This is challenging. Classical proofs of continuous extension use the idea that every Real is the limit of some Cauchy sequence of rationals. This is not valid constructively.

\begin{code}

open import Notation.Order
open import Naturals.Order

{-
ℚ-converges-to-point-in-ℝ : (x : ℝ) → Σ S ꞉ (ℕ → ℚ) , (c : ?) → (embedding-ℚ-to-ℝ {!!} ＝ x)
ℚ-converges-to-point-in-ℝ S = {!!}
-}

{-
    S' : ℕ → ℝ
    S' _ = ι x

    ι-sequence-cauchy' : cauchy-sequence ℝ ℝ-metric-space S'
    ι-sequence-cauchy' (ε , l) = 0 , sequence-is-cauchy'
     where
      sequence-is-cauchy' : (m n : ℕ) → 0 ≤ m → 0 ≤ n → B-ℝ (S' m) (S' n) ε l
      sequence-is-cauchy' m n l₁ l₂ = ℝ-m1b (ι x) ε l

    sequence-converges' : convergent-sequence ℝ ℝ-metric-space S'
    sequence-converges' = ℝ-cauchy-sequences-are-convergent S' ι-sequence-cauchy'
 -}

-- This is standard continuity
-- May not be possible to prove with this. Should consider uniform continuity and\bishop continuity

continuous : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ }
           → (m₁ : metric-space M₁)
           → (m₂ : metric-space M₂)
           → (f : M₁ → M₂)
           → 𝓤 ̇
continuous {𝓤} {𝓥} {M₁} {M₂} (B₁ , _) (B₂ , _) f =
 (c : M₁) → ((ε , l) : ℚ₊) → Σ (δ , l₂) ꞉ ℚ₊ , ((x : M₁) → B₁ c x δ l₂ → B₂ (f c) (f x) ε l)

obtain-delta : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ } → (m₁ : metric-space M₁) → (m₂ : metric-space M₂) → (f : M₁ → M₂) → continuous m₁ m₂ f → (M₁ → ℚ₊ → ℚ₊)
obtain-delta _ _ f f-cont x ε = pr₁ (f-cont x ε)

{-
continuous→continuous' : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ } → (m₁ : metric-space M₁) → (m₂ : metric-space M₂) → (f : M₁ → M₂) → continuous m₁ m₂ f → continuous' m₁ m₂ f
continuous→continuous' m₁ m₂ f f-cont (ε , l) = δ , λ c x B → {!!}
 where
  δ : ℚ₊
  δ = {!!}
-}
open import Rationals.Negation
open import Rationals.MinMax fe renaming (max to ℚ-max ; min to ℚ-min)
open import Rationals.Abs
open import Rationals.Addition

 -- This needs to be cleaned up, abstract two proofs to chop proof in half

ι-continuous : continuous ℚ-metric-space ℝ-metric-space ι
ι-continuous c (ε , 0<ε) = (ε' , 0<ε') , I
 where
  ε' : ℚ
  ε' = 1/2 * ε
  0<ε' : 0ℚ < ε'
  0<ε' = halving-preserves-order' ε 0<ε
  I : (x : ℚ)
    → B-ℚ c x ε' 0<ε'
    → B-ℝ (ι c) (ι x) ε 0<ε
  I x B = ∣ (c - 1/4 * ε , c + 1/4 * ε , x - 1/4 * ε , x + 1/4 * ε) , (l₁ , l₂ , l₃ , l₄ , II (min-to-≤ (c - 1/4 * ε) (x - 1/4 * ε)) (max-to-≤ (c + 1/4 * ε) (x + 1/4 * ε))) ∣
   where
     general-rearrange : {a b c d : ℚ} → a + b - (c + d) ＝ a - c + (b - d)
     general-rearrange {a} {b} {c} {d} = a + b - (c + d)         ＝⟨ ℚ+-assoc fe a b (- (c + d)) ⟩
                                         a + (b + (- (c + d)))   ＝⟨ ap (λ α → a + (b + α)) (ℚ-minus-dist fe c d ⁻¹) ⟩
                                         a + (b + ((- c) - d))   ＝⟨ ap (a +_) (ℚ+-assoc fe b (- c) (- d) ⁻¹) ⟩
                                         a + (b - c - d)         ＝⟨ ap (λ α → a + (α - d)) (ℚ+-comm b (- c)) ⟩
                                         a + ((- c) + b - d)     ＝⟨ ap (a +_) (ℚ+-assoc fe (- c) b (- d)) ⟩
                                         a + ((- c) + (b - d))   ＝⟨ ℚ+-assoc fe a (- c) (b - d) ⁻¹ ⟩
                                         a - c + (b - d) ∎

     II : c - 1/4 * ε ≤ x - 1/4 * ε × (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε) ＝ c - 1/4 * ε ) ∔ x - 1/4 * ε ≤ c - 1/4 * ε × (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε) ＝ x - 1/4 * ε)
        → c + 1/4 * ε ≤ x + 1/4 * ε × (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε) ＝ x + 1/4 * ε ) ∔ x + 1/4 * ε ≤ c + 1/4 * ε × (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε) ＝ c + 1/4 * ε)
        → B-ℚ (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε)) (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) ε 0<ε
     II (inl (l₁ , e₁)) (inl (l₂ , e₂)) = transport (_< ε) (ℚ-metric-commutes (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε))) i
      where
       i : B-ℚ (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε)) ε 0<ε
       i = transport₂ (λ α β → B-ℚ α β ε 0<ε) (e₂ ⁻¹) (e₁ ⁻¹) (ℚ≤-<-trans fe (ℚ-metric (x + 1/4 * ε) (c - 1/4 * ε)) (abs (x - c) + 1/2 * ε) ε v vi)
        where
         ii : ℚ-metric (x + 1/4 * ε) (c - 1/4 * ε) ＝ ℚ-metric (x - c) (- 1/2 * ε)
         ii = ap abs (x + 1/4 * ε - (c - 1/4 * ε)    ＝⟨ general-rearrange ⟩
                     x - c + (1/4 * ε - (- 1/4 * ε)) ＝⟨ ap (λ α → x - c + (1/4 * ε + α)) (ℚ-minus-minus fe (1/4 * ε) ⁻¹) ⟩
                     x - c + (1/4 * ε + 1/4 * ε)     ＝⟨ ap (x - c +_) (ℚ-distributivity' fe ε 1/4 1/4 ⁻¹) ⟩
                     x - c + (1/4 + 1/4) * ε         ＝⟨ ap (λ α → x - c + α * ε ) (1/4+1/4 fe) ⟩
                     x - c + 1/2 * ε                 ＝⟨ ap (x - c +_) (ℚ-minus-minus fe (1/2 * ε)) ⟩
                     x - c - (- 1/2 * ε)  ∎)
         iii : ℚ-metric (x - c) (- 1/2 * ε) ≤ abs (x - c) + abs (- (- 1/2 * ε))
         iii = ℚ-triangle-inequality fe (x - c) (- (- 1/2 * ε))
         iv : abs (- (- 1/2 * ε)) ＝ 1/2 * ε
         iv = ap abs (ℚ-minus-minus fe (1/2 * ε) ⁻¹) ∙ abs-of-pos-is-pos' fe (1/2 * ε) 0<ε'
         v : ℚ-metric (x + 1/4 * ε) (c - 1/4 * ε) ≤ abs (x - c) + 1/2 * ε
         v = transport₂ (λ α β → β ≤ abs (x - c) + α) iv (ii ⁻¹) iii
         vi : abs (x - c) + 1/2 * ε < ε
         vi = transport (abs (x - c) + 1/2 * ε <_) vii (ℚ<-addition-preserves-order (abs (x - c)) (1/2 * ε) (1/2 * ε) (transport (_< 1/2 * ε) (ℚ-metric-commutes c x) B))
          where
           vii : 1/2 * ε + 1/2 * ε ＝ ε
           vii = ap₂ _+_ (ℚ*-comm 1/2 ε) (ℚ*-comm 1/2 ε) ∙ ℚ-into-half fe ε ⁻¹

     II (inl (l₁ , e₁)) (inr (l₂ , e₂)) = transport (_< ε) (ℚ-metric-commutes (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε))) i
      where
       i : B-ℚ (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε)) ε 0<ε
       i = transport₂ (λ α β → B-ℚ α β ε 0<ε) (e₂ ⁻¹) (e₁ ⁻¹) (transport (_< ε) (ii ⁻¹) (half-of-pos-is-less fe ε 0<ε))
        where
         ii : ℚ-metric (c + 1/4 * ε) (c - 1/4 * ε) ＝ 1/2 * ε
         ii = ap abs (c + 1/4 * ε - (c - 1/4 * ε)       ＝⟨ general-rearrange ⟩
                      (c - c) + (1/4 * ε - (- 1/4 * ε)) ＝⟨ ap₂ _+_ (ℚ-inverse-sum-to-zero fe c) (ap (1/4 * ε +_) (ℚ-minus-minus fe (1/4 * ε) ⁻¹)) ⟩
                      0ℚ + (1/4 * ε + 1/4 * ε)          ＝⟨ ℚ-zero-left-neutral fe (1/4 * ε + 1/4 * ε) ⟩
                      1/4 * ε + 1/4 * ε                 ＝⟨ ℚ-distributivity' fe ε 1/4 1/4 ⁻¹ ⟩
                      (1/4 + 1/4) * ε                   ＝⟨ ap (_* ε) (1/4+1/4 fe) ⟩
                      1/2 * ε ∎) ∙ abs-of-pos-is-pos' fe (1/2 * ε) 0<ε'
     II (inr (l₁ , e₁)) (inl (l₂ , e₂)) = transport (_< ε) (ℚ-metric-commutes (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε))) i
      where
       i :  B-ℚ (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε)) ε 0<ε
       i = transport₂ (λ α β → B-ℚ α β ε 0<ε) (e₂ ⁻¹) (e₁ ⁻¹) (transport (_< ε) (ii ⁻¹) (half-of-pos-is-less fe ε 0<ε))
        where
         ii : ℚ-metric (x + 1/4 * ε) (x - 1/4 * ε) ＝ 1/2 * ε
         ii = ap abs (x + 1/4 * ε - (x - 1/4 * ε)       ＝⟨ general-rearrange ⟩
                      (x - x) + (1/4 * ε - (- 1/4 * ε)) ＝⟨ ap₂ _+_ (ℚ-inverse-sum-to-zero fe x) (ap (1/4 * ε +_) (ℚ-minus-minus fe (1/4 * ε) ⁻¹)) ⟩
                      0ℚ + (1/4 * ε + 1/4 * ε)          ＝⟨ ℚ-zero-left-neutral fe (1/4 * ε + 1/4 * ε) ⟩
                      1/4 * ε + 1/4 * ε                 ＝⟨ ℚ-distributivity' fe ε 1/4 1/4 ⁻¹ ⟩
                      (1/4 + 1/4) * ε                   ＝⟨ ap (_* ε) (1/4+1/4 fe) ⟩
                      1/2 * ε ∎) ∙ abs-of-pos-is-pos' fe (1/2 * ε) 0<ε'
     II (inr (l₁ , e₁)) (inr (l₂ , e₂)) = transport (_< ε) (ℚ-metric-commutes (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε))) i
      where
       i : B-ℚ (ℚ-max (c + 1/4 * ε) (x + 1/4 * ε)) (ℚ-min (c - 1/4 * ε) (x - 1/4 * ε)) ε 0<ε
       i = transport₂ (λ α β → B-ℚ α β ε 0<ε) (e₂ ⁻¹) (e₁ ⁻¹) (ℚ≤-<-trans fe (ℚ-metric (c + 1/4 * ε) (x - 1/4 * ε)) (abs (c - x) + 1/2 * ε) ε v vi)
        where
         ii : ℚ-metric (c + 1/4 * ε) (x - 1/4 * ε) ＝ ℚ-metric (c - x) (- 1/2 * ε)
         ii = ap abs (c + 1/4 * ε - (x - 1/4 * ε)    ＝⟨ general-rearrange ⟩
                     c - x + (1/4 * ε - (- 1/4 * ε)) ＝⟨ ap (λ α → c - x + (1/4 * ε + α)) (ℚ-minus-minus fe (1/4 * ε) ⁻¹) ⟩
                     c - x + (1/4 * ε + 1/4 * ε)     ＝⟨ ap (c - x +_) (ℚ-distributivity' fe ε 1/4 1/4 ⁻¹) ⟩
                     c - x + (1/4 + 1/4) * ε         ＝⟨ ap (λ α → c - x + α * ε ) (1/4+1/4 fe) ⟩
                     c - x + 1/2 * ε                 ＝⟨ ap (c - x +_) (ℚ-minus-minus fe (1/2 * ε)) ⟩
                     c - x - (- 1/2 * ε)  ∎)
         iii : ℚ-metric (c - x) (- 1/2 * ε) ≤ abs (c - x) + abs (- (- 1/2 * ε))
         iii = ℚ-triangle-inequality fe (c - x) (- (- 1/2 * ε))
         iv : abs (- (- 1/2 * ε)) ＝ 1/2 * ε
         iv = ap abs (ℚ-minus-minus fe (1/2 * ε) ⁻¹) ∙ abs-of-pos-is-pos' fe (1/2 * ε) 0<ε'
         v : ℚ-metric (c + 1/4 * ε) (x - 1/4 * ε) ≤ abs (c - x) + 1/2 * ε
         v = transport₂ (λ α β → β ≤ abs (c - x) + α) iv (ii ⁻¹) iii
         vi : abs (c - x) + 1/2 * ε < ε
         vi = transport (abs (c - x) + 1/2 * ε <_) vii (ℚ<-addition-preserves-order (abs (c - x)) (1/2 * ε) (1/2 * ε) B)
          where
           vii : 1/2 * ε + 1/2 * ε ＝ ε
           vii = ap₂ _+_ (ℚ*-comm 1/2 ε) (ℚ*-comm 1/2 ε) ∙ ℚ-into-half fe ε ⁻¹

     abstract

      0<ε'' : 0ℚ <ℚ 1/4 * ε
      0<ε'' = quarter-preserves-order' ε 0<ε
      l₁ : c - 1/4 * ε <ℚ c
      l₁ = ℚ<-subtraction-preserves-order fe c (1/4 * ε) 0<ε''
      l₂ : x - 1/4 * ε <ℚ x
      l₂ = ℚ<-subtraction-preserves-order fe x (1/4 * ε) 0<ε''
      l₃ : c <ℚ c + 1/4 * ε
      l₃ = ℚ<-addition-preserves-order'' fe c (1/4 * ε) 0<ε''
      l₄ : x <ℚ x + 1/4 * ε
      l₄ = ℚ<-addition-preserves-order'' fe x (1/4 * ε) 0<ε''

{-
ℚ*-continuous : (y : ℚ) → ¬ (y ＝ 0ℚ) → continuous ℚ-metric-space ℚ-metric-space λ q → y * q
ℚ*-continuous y nz q (ε , l) = I (get-inverse)
 where
  get-inverse : Σ 1/absy ꞉ ℚ , abs y * 1/absy ＝ 1ℚ
  get-inverse = ℚ*-inverse fe (abs y) {!!}

  I : Σ 1/absy ꞉ ℚ , abs y * 1/absy ＝ 1ℚ →  Σ (δ , l₂) ꞉ ℚ₊ , ((x : ℚ) → B-ℚ q x δ l₂ → B-ℚ (y * q) (y * x) ε l)
  I (1/absy , e) = (ε * 1/absy , {!!}) , II
   where
    II : (x : ℚ) → B-ℚ q x (ε * 1/absy) {!!} → B-ℚ (y * q) (y * x) ε l
    II x B = transport₂ _<_ III IV (ℚ<-pos-multiplication-preserves-order' fe (abs (q - x)) (ε * 1/absy) (abs y) B {!!})
     where
      III : abs (q - x) * abs y ＝ abs (y * q - y * x)
      III = abs (q - x) * abs y     ＝⟨ abs-mult fe  (q - x) y ⟩
            abs ((q - x) * y)       ＝⟨ ap abs (ℚ*-comm (q - x) y) ⟩
            abs (y * (q - x))       ＝⟨ ap abs (ℚ-distributivity fe y q (- x)) ⟩
            abs (y * q + y * (- x)) ＝⟨ ap (λ α → abs (y * q + α)) (ℚ*-comm y (- x)) ⟩
            abs (y * q + (- x) * y) ＝⟨ ap (λ α → abs (y * q + α)) (ℚ-subtraction-dist-over-mult fe x y) ⟩
            abs (y * q - x * y)     ＝⟨ ap (λ α → abs (y * q - α)) (ℚ*-comm x y) ⟩
            abs (y * q - y * x)     ∎

      IV : ε * 1/absy * abs y ＝ ε
      IV = ε * 1/absy * abs y   ＝⟨ ℚ*-assoc fe ε (1/absy) (abs y)     ⟩
           ε * (1/absy * abs y) ＝⟨ ap (ε *_) (ℚ*-comm 1/absy (abs y)) ⟩
           ε * (abs y * 1/absy) ＝⟨ ap (ε *_) e                        ⟩
           ε * 1ℚ               ＝⟨ ℚ-mult-right-id fe ε               ⟩
           ε                    ∎
-}
composition-preserves-continuity : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ } {M₃ : 𝓦 ̇ }
                                 → (m₁ : metric-space M₁)
                                 → (m₂ : metric-space M₂)
                                 → (m₃ : metric-space M₃)
                                 → (f : M₁ → M₂)
                                 → (g : M₂ → M₃)
                                 → continuous m₁ m₂ f
                                 → continuous m₂ m₃ g
                                 → continuous m₁ m₃ (g ∘ f)

composition-preserves-continuity  {𝓤} {𝓥} {𝓦} {M₁} {M₂} {M₃} (B₁ , m₁) (B₂ , m₂) (B₃ , m₃) f g c₁ c₂ c (ε , l) = I (c₂ (f c) (ε , l))
 where
  I : Σ (δ , 0<δ) ꞉ ℚ₊ , ((y : M₂) → B₂ (f c) y δ 0<δ → B₃ (g (f c)) (g y) ε l)
    → Σ (κ , 0<κ) ꞉ ℚ₊ , ((x : M₁) → B₁ c x κ 0<κ → B₃ (g (f c)) (g (f x)) ε l)
  I ((δ , 0<δ) , τ) = II (c₁ c (δ , 0<δ))
   where
    II : (Σ (δ₁ , 0<δ₁) ꞉ ℚ₊ , ((z : M₁) → B₁ c z δ₁ 0<δ₁ → B₂ (f c) (f z) δ 0<δ))
        → Σ (κ , 0<κ) ꞉ ℚ₊ , ((x : M₁) → B₁ c x κ 0<κ → B₃ (g (f c)) (g (f x)) ε l)
    II ((δ₁ , 0<δ₁) , τ₁) = (δ₁ , 0<δ₁) , λ x B → τ (f x) (τ₁ x B)

\end{code}

I am first going to try and show that certain functions are continuous, and attempt to extend them directly, as a proof of concept.

\begin{code}
id-continuous : continuous ℚ-metric-space ℚ-metric-space id
id-continuous c (ε , 0<ε) = (ε , 0<ε) , λ _ B → B

ℚ-ℝ-id-continuous : continuous ℚ-metric-space ℝ-metric-space (ι ∘ id)
ℚ-ℝ-id-continuous = composition-preserves-continuity ℚ-metric-space ℚ-metric-space ℝ-metric-space id ι id-continuous ι-continuous
\end{code}
}
Now we have that the function from ℚ-ℝ-id is continuous. We want to extend this function from the rationals to the reals.

\begin{code}

open import DedekindReals.Order pe pt fe
-- open import Addition pe pt fe renaming (_+_ to _ℝ+_)
{-
ℝ-no-maximum : (x : ℝ) → Σ y ꞉ ℝ , y < x ∔ x < y
ℝ-no-maximum x = {!weak-linearity ? ? ? ?!}

ℝ-id : ℝ → ℝ
ℝ-id r = ℚ-ℝ-id (I by-ℚ-ℝ-id-continuity)
 where
  S : ℕ → ℚ
  S = ⟨1/sn⟩

  by-ℚ-ℝ-id-continuity : (c : ℚ) → ((ε , l) : ℚ₊) → Σ (δ , l₂) ꞉ ℚ₊ , ((x : ℚ) → B-ℚ c x δ l₂ → B-ℝ (ℚ-ℝ-id c) (ℚ-ℝ-id x) ε l)
  by-ℚ-ℝ-id-continuity = ℚ-ℝ-id-continuous

  I : ((c : ℚ) → ((ε , l) : ℚ₊) → Σ (δ , l₂) ꞉ ℚ₊ , ((x : ℚ) → B-ℚ c x δ l₂ → B-ℝ (ℚ-ℝ-id c) (ℚ-ℝ-id x) ε l)) → ℚ
  I f = {!!}
   where
    II : {!!}
    II = {!f 0 1!}


ℝ-id' : ℝ → ℝ
ℝ-id' r = I (by-ℚ-ℝ-id-continuity)
 where

  by-ℚ-ℝ-id-continuity : (c : ℚ) → ((ε , l) : ℚ₊) → Σ (δ , l₂) ꞉ ℚ₊ , ((x : ℚ) → B-ℚ c x δ l₂ → B-ℝ (ℚ-ℝ-id c) (ℚ-ℝ-id x) ε l)
  by-ℚ-ℝ-id-continuity = ℚ-ℝ-id-continuous

  I : ((c : ℚ) → ((ε , l) : ℚ₊) → Σ (δ , l₂) ꞉ ℚ₊ , ((x : ℚ) → B-ℚ c x δ l₂ → B-ℝ (ℚ-ℝ-id c) (ℚ-ℝ-id x) ε l)) → ℝ
  I f = (left , right) , {!!}
   where
    left : ℚ-subset-of-propositions
    left p = B-ℝ {!!} {!!} {!!} {!!} , {!!}
    right : ℚ-subset-of-propositions
v    right = {!!}
-}
\end{code}

The problem goes even further. There is no way to find a q in relation to r without q being truncated, and we cannot escape truncations since neither Q or R are subsingletons.
That is, not only can I not find a q close to r (without truncation), I cannot find a q any distance from r without truncation.

So how do we find to find a q close to r? We cannot.

The only way I see to get access to values is by defining the "fbar" function.

\begin{code}

open import Rationals.Multiplication
open import Rationals.Negation
open import UF.Powerset

{-
ℚ-continuous-has-inverse :  (f : ℚ → ℚ) → continuous ℚ-metric-space ℚ-metric-space f
                         → Σ g ꞉ (ℚ → ℚ) , continuous ℚ-metric-space ℚ-metric-space g × (g ∘ f ＝ id)
ℚ-continuous-has-inverse f cont = I , II
 where
  I : ℚ → ℚ
  I q = i {!by-f-continuity q!}
   where
    i : {!!}
    i = {!!}
  II : continuous ℚ-metric-space ℚ-metric-space I × (I ∘ f ＝ id)
  II = {!!}
  by-f-continuity : (c : ℚ) → ((ε , 0<ε) : ℚ₊) → Σ (δ , 0<δ) ꞉ ℚ₊ , ((x : ℚ) → B-ℚ c x δ 0<δ → B-ℚ (f c) (f x) ε 0<ε)
  by-f-continuity = cont
-}
{-
f^ : (f g : ℚ → ℚ)
   → continuous ℚ-metric-space ℚ-metric-space f
   → continuous ℚ-metric-space ℚ-metric-space g
   → ((k : ℚ) → (f ∘ g) k ＝ k)
   → ((k : ℚ) → (g ∘ f) k ＝ k)
   → ℝ → ℝ
f^ f g f-cont g-cont e₁ e₂ r = z
 where
  z : ℝ
  z =  (L , R) , inhabited-left-z , inhabited-right-z , rounded-left-z , rounded-right-z , disjoint-z , located-z
   where
-}
\end{code}

So we adopt the same strategy as we used to show that monotonic functions can be extended. Now we have access to some p and q.

My initial thought is to use the same condition as we used before. The idea is the since we have continuity, this property allows us to extract the reals conditions.
Working in reverse, we impose conditions base on (g p) < r, (since we can obtain p' < r → g p' ＝ g (f p') ＝ p').

However, I actually think this is not a strong enough condition. We don't know how f p behaves, so some of the conditions are now not automatic.
The monotinicity result is extremely strong, since it gives us order on g.

I believe we need to design a condition L and R, which is related to continuity.

We have that ∀ ε , δ > 0 , ∀ x c →  | x - c | < δ  → | f x - f c | < ε
                                    | x - c | < δ →  | g x - g c | < ε

We have some r , mapping to r' , but we are defining r'.

                         p < r' → condition    with     condition ⇔ ?

                         We require that if a < r then f a < r' . But I see here that a = g b for some b. b = f a.
                         So we want b < r' ⇔ g b < r. This is fine by bijectivity of f , g.

So then, the question is, is continuity strong enough to be able to construct this real?

\begin{code}
{-
    L : ℚ-subset-of-propositions
    L p = (g p < r) , ∈-is-prop (lower-cut-of r) (g p)
    R : ℚ-subset-of-propositions
    R q = (r < g q) , ∈-is-prop (upper-cut-of r) (g q)
    inhabited-left-z : inhabited-left L
    inhabited-left-z = ∥∥-functor I (inhabited-from-real-L r)
     where
      I : Σ p ꞉ ℚ , p < r → Σ p' ꞉ ℚ , g p' < r
      I (p , p<r) = (f p) ,  transport (_< r) (e₂ p ⁻¹) p<r

    inhabited-right-z : inhabited-right R
    inhabited-right-z = ∥∥-functor I (inhabited-from-real-R r)
     where
      I : Σ q ꞉ ℚ , r < q → Σ q' ꞉ ℚ , r < g q'
      I (q , r<q) = f q ,  transport (r <_) (e₂ q ⁻¹) r<q
-}
\end{code}

Inhabitedness is trivial and is lifted from the monotonicity proof. It doesn't make use of monotonicity/continuity properties.

Roundedness is where the problem begins. Following the same proof pattern, this reduces to proving:

 Given that

 g p < p' < r

 is p < f p'?

 The only thing we have is continuity of f and g. I don't think this is possible.

 But we have not considered the standard theorem, which perhaps we could introduce at this point now that we have access to p and p'.

 Cauchy sequences on rationals?
 Different condition for z (I believe the current condition would have to be extended rather than replaced)?
 Or perhaps the above is easilu provable and I'm not seeing it.

\begin{code}
{-
    rounded-left-z : rounded-left L
    rounded-left-z p = ltr , rtl
     where
      ltr : {!!}
      ltr = {!!}

      rtl : {!!}
      rtl = {!!}


    rounded-right-z : rounded-right R
    rounded-right-z = {!!}

    disjoint-z : disjoint L R
    disjoint-z = {!!}

    located-z : located L R
    located-z = {!!}

-}


{-
continuous-extension-theorem : (f : ℚ → ℝ)
                             → continuous ℚ-metric-space ℝ-metric-space f
                             → ∃! g ꞉ (ℝ → ℝ) , (continuous ℝ-metric-space ℝ-metric-space g)
continuous-extension-theorem f f-continuous = (g , g-continuous) , g-unique
 where
  g : ℝ → ℝ
  g x = {!!}
   where
    Sl : ℕ → ℝ
    Sl n = embedding-ℚ-to-ℝ {!!}
     where
      I : {!!}
      I = ℝ-arithmetically-located x (⟨1/sn⟩ n) {!!}
    res1 : (S : ℕ → ℝ) → cauchy→convergent ℝ ℝ-metric-space S
    res1 = ℝ-cauchy-sequences-are-convergent

  g-continuous : continuous ℝ-metric-space ℝ-metric-space g
  g-continuous = {!!}

  g-unique : is-central (Σ (continuous ℝ-metric-space ℝ-metric-space)) (g , g-continuous)
  g-unique (g' , g'-continuous) = {!!}
-}

{-
ℚ-addition-to-ℝ : ℚ → ℚ → ℝ
ℚ-addition-to-ℝ p q = embedding-ℚ-to-ℝ (p + q)

ℚ-succ : ℚ → ℚ
ℚ-succ q = q + 1ℚ

ℚ-succ-to-ℝ : ℚ → ℝ
ℚ-succ-to-ℝ q = embedding-ℚ-to-ℝ (ℚ-succ q)
-}
{-
ℚ-succ-to-ℝ-continuous : continuous ℚ-metric-space ℝ-metric-space ℚ-succ-to-ℝ
ℚ-succ-to-ℝ-continuous c ε = {!!}

rationals-extension : (ℚ → ℚ) → ℝ → ℝ
rationals-extension f = {!!}

ℝ-succ : ℝ → ℝ
ℝ-succ = rationals-extension ℚ-succ
 where
  this : {!!}
  this = {!!}
-}

open import UF.Subsingletons-FunExt

\end{code}

I believe the conditions below are along the right lines.

Do need to find a way to seperate the b out.

Roundedness, disjointedness seem trivial... by density of rationals.

Roundedness :

Locatedness could be difficult. I cannot get inhabitedness.


Left Cut  : (b ε : ℚ) → 0ℚ < ε → ∃ δ ꞉ ℚ , ((l₁ : 0ℚ < δ) → B-ℝ x (ι b) δ l₁ → p < f b - ε)
Right Cut : (b ε : ℚ) → 0ℚ < ε → ∃ δ ꞉ ℚ , ((l₁ : 0ℚ < δ) → B-ℝ x (ι b) δ l₁ → q < f b + ε)

I believe these are along the lines of the condition.
Maybe the b need to be existential instead universal.

Motivation for these cuts:

We want : f̂ (ι p) ＝ ι (f p)
          ∀ ε > 0 , ∃ δ > 0 , | x - a | < δ → | f̂ x - f̂ a | < ε

In particular, specialising to rationals, we want:
          ∀ b , ∀ ε > 0 , ∃ δ > 0 , | x - (ι b) | < δ → | f̂ x - f̂ (ι b) | < ε

                                                      → | f̂ x - ι (f b) | < ε
                                                      → ι (f b) - ε < f̂ x  < ι (f b) + ε
                                                      → ι (f b - ε) < f̂ x  < ι (f b + ε)   <- reals order
                                                      → f b - ε     < f̂ x  < f b + ε       <- cuts

This gives us a clue as to what the cuts should be. In particular, consider p and q as follows:

Perhaps the idea is to let p = f b - ε, and manipulate expressions.
I believe the following is equivalent:

                  p < f b - ε < f̂ x < f b + ε < q




I have new propositions for cuts :

 L q = ∃ (u , v) ꞉ ℚ × ℚ , Σ (ε , _) ꞉ ℚ₊ , u < x × x < v × p < ℚ-min (f u) (f v) - ε
 R q = ∃ (u , v) ꞉ ℚ × ℚ , Σ (ε , _) ꞉ ℚ₊ , u < x × x < v × ℚ-max (f u) (f v) + ε < q

Unfortunately these are not sound. I need to enforce that (f u) (f v) are ε close to (f x).

I think these needs to be the δ generated by (f u - f v) < δ

 L q = ∃ (u , v) ꞉ ℚ × ℚ , Σ (ε , _) ꞉ ℚ₊ , Σ (δ , _) : ℚ₊ , u < x × x < v × p < ℚ-min (f u) (f v) - ε


\begin{code}
{-
f^' : (f : ℚ → ℚ)
    → continuous ℚ-metric-space ℚ-metric-space f
    → ℝ → ℝ
f^' f f-cont x = z
 where
  z : ℝ
  z = (L , R) , inhabited-left-z , inhabited-right-z , rounded-left-z , rounded-right-z , disjoint-z , located-z
   where
    by-continuity : ℚ → ℚ₊ → ℚ₊
    by-continuity z ε = obtain-delta ℚ-metric-space ℚ-metric-space f f-cont z ε

    L : 𝓟 ℚ
    L p = condition , ∃-is-prop
     where
     condition : 𝓤₀ ̇
     condition = ∃ (u , v) ꞉ ℚ × ℚ , Σ (ε , l) ꞉ ℚ₊ , u < x × x < v × p < f u - ε × B-ℚ u v (pr₁ (by-continuity u (ε , l))) (pr₂ (by-continuity u (ε , l)))


    R : 𝓟 ℚ
    R q = condition , ∃-is-prop
     where
      condition : 𝓤₀ ̇
      condition = ∃ (u , v) ꞉ ℚ × ℚ , Σ (ε , l) ꞉ ℚ₊ , u < x × x < v × q < f u + ε × B-ℚ u v (pr₁ (by-continuity u (ε , l))) (pr₂ (by-continuity u (ε , l)))

    inhabited-left-z : inhabited-left L
    inhabited-left-z = {!!}

    inhabited-right-z : inhabited-right R
    inhabited-right-z = {!!}

    rounded-left-z : rounded-left L
    rounded-left-z = {!!}

    rounded-right-z : rounded-right R
    rounded-right-z = {!!}

    located-z : located L R
    located-z p q l = {!!}

    disjoint-z : disjoint L R
    disjoint-z p q p<fx = {!!}

diagram-commutes : (f : ℚ → ℚ) → (c : continuous ℚ-metric-space ℚ-metric-space f)
                               → (q : ℚ)
                               → (f^' f c) (ι q) ＝ ι (f q)
diagram-commutes f c q = ℝ-equality-from-left-cut' (f^' f c (ι q)) (ι (f q)) I II
 where
  I : (p : ℚ)
    → (∃ (u , v) ꞉ ℚ × ℚ , Σ (ε , l) ꞉ ℚ₊ , u < q × q < v × p < f u - ε × B-ℚ u v (pr₁ (obtain-delta ℚ-metric-space ℚ-metric-space f c u (ε , l))) (pr₂ (obtain-delta ℚ-metric-space ℚ-metric-space f c u (ε , l))))
    → p < f q
  I p = {!!}
  II : {!!}
  II = {!!}
-}
\end{code}

f^' : (f : ℚ → ℚ)
    → continuous ℚ-metric-space ℚ-metric-space f
    → ℝ → ℝ
f^' f f-cont x = z
 where
  z : ℝ
  z = (L , R) , inhabited-left-z , inhabited-right-z , rounded-left-z , rounded-right-z , disjoint-z , located-z
   where
    L : 𝓟 ℚ
    L p = condition , ∃-is-prop
     where
     condition : 𝓤₀ ̇
     condition = ∃ (u , v) ꞉ ℚ × ℚ , Σ (ε , _) ꞉ ℚ₊ , u < x × x < v × p < ℚ-min (f u) (f v) - ε

    R : 𝓟 ℚ
    R q = condition , ∃-is-prop
     where
      condition : 𝓤₀ ̇
      condition = ∃ (u , v) ꞉ ℚ × ℚ , Σ (ε , _) ꞉ ℚ₊ , u < x × x < v × ℚ-max (f u) (f v) + ε < q

    inhabited-left-z : inhabited-left L
    inhabited-left-z = ∥∥-rec (inhabited-left-is-prop L) I (ℝ-arithmetically-located x 1/2 (0 , refl))
     where
      I : Σ (u , v) ꞉ ℚ × ℚ , u < x × x < v × 0ℚ < v - u × v - u < 1/2
        → ∃ p ꞉ ℚ , ∃ (u , v) ꞉ ℚ × ℚ , Σ (ε , _) ꞉ ℚ₊ , u < x × x < v × p < ℚ-min (f u) (f v) - ε
      I ((u , v) , u<x , x<v , l₁ , l₂) = ∣ (ℚ-min (f u) (f v) - 1/2) - 1/2 , ∣ (u , v) , (1/2 , 0<1/2) , u<x , x<v , ℚ<-subtraction-preserves-order fe (ℚ-min (f u) (f v) - 1/2) 1/2 (0 , refl) ∣ ∣

    inhabited-right-z : inhabited-right R
    inhabited-right-z = {!!}

    rounded-left-z : rounded-left L
    rounded-left-z p = ltr , rtl
     where
      ltr : ∃ (u , v) ꞉ ℚ × ℚ , Σ (ε , _) ꞉ ℚ₊ , u < x × x < v × p < ℚ-min (f u) (f v) - ε
          → ∃ p' ꞉ ℚ , p < p' × (∃ (u , v) ꞉ ℚ × ℚ , Σ (ε , _) ꞉ ℚ₊ , u < x × x < v × p' < ℚ-min (f u) (f v) - ε)
      ltr  = ∥∥-functor I
       where
        I : Σ (u , v) ꞉ ℚ × ℚ , Σ (ε , _) ꞉ ℚ₊ , u < x × x < v × p < ℚ-min (f u) (f v) - ε
          → Σ p' ꞉ ℚ , p < p' × (∃ (u , v) ꞉ ℚ × ℚ , Σ (ε , _) ꞉ ℚ₊ , u < x × x < v × p' < ℚ-min (f u) (f v) - ε)
        I ((u , v) , (ε , l) , u<x , x<v , p<m) = II (ℚ-dense fe p (ℚ-min (f u) (f v) - ε) p<m)
         where
          II : Σ p' ꞉ ℚ , p < p' × p' < ℚ-min (f u) (f v) - ε
             → Σ p' ꞉ ℚ , p < p' × (∃ (u , v) ꞉ ℚ × ℚ , Σ (ε , _) ꞉ ℚ₊ , u < x × x < v × p' < ℚ-min (f u) (f v) - ε)
          II (p' , p<p' , p'<m) = p' , p<p' , ∣ (u , v) , (ε , l) , (u<x , x<v , p'<m) ∣

      rtl : ∃ p' ꞉ ℚ , p < p' × p' ∈ L → p ∈ L
      rtl = ∥∥-rec ∃-is-prop I
       where
        I : Σ p' ꞉ ℚ , p < p' × p' ∈ L → p ∈ L
        I (p' , p<p' , p'<fx) = ∥∥-functor II p'<fx
         where
          II : Σ (u , v) ꞉ ℚ × ℚ , Σ (ε , _) ꞉ ℚ₊ , u < x × x < v × p' < ℚ-min (f u) (f v) - ε
             → Σ (u , v) ꞉ ℚ × ℚ , Σ (ε , _) ꞉ ℚ₊ , u < x × x < v × p < ℚ-min (f u) (f v) - ε
          II ((u , v) , (ε , l) , u<x , x<v , p'<m) = ((u , v) , (ε , l) , u<x , x<v , ℚ<-trans p p' (ℚ-min (f u) (f v) - ε) p<p' p'<m)

    rounded-right-z : rounded-right R
    rounded-right-z = {!!}

    located-z : located L R
    located-z p q l = {!!}

    disjoint-z : disjoint L R
    disjoint-z p q p<fx = {!!}

f^' : (f : ℚ → ℚ)
    → continuous ℚ-metric-space ℚ-metric-space f
    → ℝ → ℝ
f^' f f-cont e x = z
 where
  z : ℝ
  z = (L , R) , inhabited-left-z , inhabited-right-z , rounded-left-z , rounded-right-z , disjoint-z , located-z
   where
    L : 𝓟 ℚ
    L p = condition , ∃-is-prop
     where
     condition : 𝓤₀ ̇
     condition = ∃ b ꞉ ℚ , ((ε : ℚ) → 0ℚ < ε → Σ δ ꞉ ℚ , ((l₁ : 0ℚ < δ) → B-ℝ x (ι b) δ l₁ → p < f b - ε))

    R : 𝓟 ℚ
    R q = condition , ∃-is-prop
     where
      condition : 𝓤₀ ̇
      condition = ∃ b ꞉ ℚ , ((ε : ℚ) → 0ℚ < ε → Σ δ ꞉ ℚ , ((l₁ : 0ℚ < δ) → B-ℝ x (ι b) δ l₁ → q < f b + ε))

    inhabited-left-z : inhabited-left L
    inhabited-left-z = {!!}
     where
      t : ∃ p ꞉ ℚ , p ∈ lower-cut-of x
     t = inhabited-from-real-L x

    inhabited-right-z : inhabited-right R
    inhabited-right-z = {!!}


    rounded-left-z : rounded-left L
    rounded-left-z p = ltr , rtl
     where
      ltr : p ∈ L → ∃ p' ꞉ ℚ , p < p' × p' ∈ L
      ltr p<x = ∥∥-functor I p<x
       where
        I : Σ b ꞉ ℚ , ((ε : ℚ) → 0ℚ < ε → Σ δ ꞉ ℚ , ((l₁ : 0ℚ < δ) → B-ℝ x (ι b) δ l₁ → p < f b - ε))
          → Σ p' ꞉ ℚ , p < p' × p' ∈ L
        I (b , f) = {!!} , {!!}
         where
          using-b : {!!}
          using-b = {!!}
          by-density : {!!}
          by-density = {!!}

      rtl : {!!}
      rtl = {!!}


    rounded-right-z : rounded-right R
    rounded-right-z = {!!}

    located-z : located L R
    located-z = {!!}

    disjoint-z : disjoint L R
    disjoint-z = disjoint→trans L R located-z I
     where
      I : (q : ℚ) → ¬ (q ∈ L × q ∈ R)
      I q (q<z , z<q) = ∥∥-rec 𝟘-is-prop II (binary-choice q<z z<q)
       where
        II : (Σ b ꞉ ℚ , ((ε : ℚ) → 0ℚ < ε → Σ δ ꞉ ℚ , ((l₁ : 0ℚ < δ) → B-ℝ x (ι b) δ l₁ → q < f b - ε)))
           × (Σ c ꞉ ℚ , ((ε : ℚ) → 0ℚ < ε → Σ δ ꞉ ℚ , ((l₁ : 0ℚ < δ) → B-ℝ x (ι c) δ l₁ → q < f c + ε)))
           → 𝟘
        II ((b , h) , c , g) = V (h 1ℚ (0 , refl)) (g 1ℚ (0 , refl))
         where
          III : Σ δ ꞉ ℚ , ((l₁ : 0ℚ < δ) → B-ℝ x (ι b) δ l₁ → q < f b - 1ℚ)
          III = h 1ℚ (0 , refl)
          IV : {!!}
          IV = {!!}
          V : (Σ δ ꞉ ℚ , ((l₁ : 0ℚ < δ) → B-ℝ x (ι b) δ l₁ → q < f b - 1ℚ))
            → (Σ δ ꞉ ℚ , ((l₁ : 0ℚ < δ) → B-ℝ x (ι c) δ l₁ → q < f c + 1ℚ))
          → {!!}
          V = {!!}

     where
      I : ∃ (a , b) ꞉ ℚ × ℚ , a < x × x < b × 0ℚ < b - a × b - a < 1ℚ
      I = ℝ-arithmetically-located x 1ℚ (0 , refl)
      II : Σ (a , b) ꞉ ℚ × ℚ , a < x × x < b × 0ℚ < b - a × b - a < 1ℚ
         → Σ p ꞉ ℚ , ((a ε : ℚ) → 0ℚ < ε → ∃ δ ꞉ ℚ , ((l₁ : 0ℚ < δ) → B-ℝ x (ι a) δ l₁ → p < f a - ε))
      II ((a , b) , a<x , x<b , l₁ , l₂) = (f a) , III
       where
        III : (a' ε : ℚ) → 0ℚ < ε → ∃ δ ꞉ ℚ , ((l₁ : 0ℚ < δ) → B-ℝ x (ι a') δ l₁ → f a < f a' - ε)
        III a' ε l = ∣ 1ℚ , (λ l₃ B → {!!}) ∣
\end{code}
