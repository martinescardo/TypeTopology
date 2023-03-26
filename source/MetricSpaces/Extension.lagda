\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --lossy-unification --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.Order
open import Notation.CanonicalMap
open import Rationals.Abs
open import Rationals.Addition
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import UF.FunExt
open import UF.Subsingletons
open import UF.Base
open import UF.PropTrunc
open import UF.Powerset

module MetricSpaces.Extension
  (fe : Fun-Ext)
  (pe : Prop-Ext)
  (pt : propositional-truncations-exist)
 where

open PropositionalTruncation pt

open import Rationals.MinMax fe
open import DedekindReals.Type pe pt fe
open import DedekindReals.Properties fe pt pe
open import MetricSpaces.Definition pt fe pe
open import MetricSpaces.Rationals fe pt pe
open import MetricSpaces.DedekindReals pt fe pe


\end{code}

The goal of this file is implement an extension theorem which takes
certain continuous functions defined on rationals to continuous
functions defined on reals.

Note that we do not restrict ourselves to uniformly continuous
functions, but we must consider the set of continuous which satisfies
the following:

Let δ : ℚ₊ → ℚ₊ be a modulus of continuity of a function.

Then for ε₁ ε₂ : ℚ₊, We require that δ(ε₁) + δ(ε₂) ≤ δ(ε₁ + ε₂).

This holds for various functions (-, + , *, _², sin, cos), doesn't seem to be too restricting.

\begin{code}

is-continuous : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ }
           → (m₁ : metric-space M₁)
           → (m₂ : metric-space M₂)
           → (f : M₁ → M₂)
           → 𝓤 ̇
is-continuous {𝓤} {𝓥} {M₁} {M₂} (B₁ , _) (B₂ , _) f =
 (x y : M₁) → ((ε , ε>0) : ℚ₊) → Σ (δ , δ>0) ꞉ ℚ₊ , (B₁ x y δ δ>0 → B₂ (f x) (f y) ε ε>0)

is-uniformly-continuous : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ }
           → (m₁ : metric-space M₁)
           → (m₂ : metric-space M₂)
           → (f : M₁ → M₂)
           → 𝓤 ̇
is-uniformly-continuous {𝓤} {𝓥} {M₁} {M₂} (B₁ , _) (B₂ , _) f =
 ((ε , ε>0) : ℚ₊) → Σ (δ , δ>0) ꞉ ℚ₊ , ((x y : M₁) → (B₁ x y δ δ>0 → B₂ (f x) (f y) ε ε>0))

uniform-modulus : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ }
        → (m₁ : metric-space M₁)
        → (m₂ : metric-space M₂)
        → (f : M₁ → M₂)
        → is-uniformly-continuous m₁ m₂ f
        → ((ε , ε>0) : ℚ₊)
        → ℚ₊
uniform-modulus _ _ f is-cont ε = pr₁ (is-cont ε)

modulus : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ }
        → (m₁ : metric-space M₁)
        → (m₂ : metric-space M₂)
        → (f : M₁ → M₂)
        → is-continuous m₁ m₂ f
        → (x y : M₁)
        → ((ε , ε>0) : ℚ₊)
        → ℚ₊
modulus {𝓤} {𝓥} {M₁} {M₂} _ _ f is-cont x y ε = pr₁ (is-cont x y ε)

_ℚ₊≤_ : ℚ₊ → ℚ₊ → 𝓤₀ ̇
(a , _) ℚ₊≤ (b , _) = a ≤ b

_ℚ₊+_ : ℚ₊ → ℚ₊ → ℚ₊
(ε₁ , 0<ε₁) ℚ₊+ (ε₂ , 0<ε₂) = (ε₁ + ε₂) , ℚ<-adding-zero ε₁ ε₂ 0<ε₁ 0<ε₂

modulus-superadditive : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ }
                      → (m₁ : metric-space M₁)
                      → (m₂ : metric-space M₂)
                      → (f : M₁ → M₂)
                      → is-continuous m₁ m₂ f
                      → (x y : M₁)
                      → (ε₁ ε₂ : ℚ₊)
                      → 𝓤₀ ̇
modulus-superadditive m₁ m₂ f is-cont  = λ x y ε₁ ε₂ →
 (modulus m₁ m₂ f is-cont x y ε₁ ℚ₊+ modulus m₁ m₂ f is-cont x y ε₂) ℚ₊≤ modulus m₁ m₂ f is-cont x y (ε₁ ℚ₊+ ε₂)

uniform-modulus-superadditive : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ }
                              → (m₁ : metric-space M₁)
                              → (m₂ : metric-space M₂)
                              → (f : M₁ → M₂)
                              → is-uniformly-continuous m₁ m₂ f
                              → (ε₁ ε₂ : ℚ₊)
                              → 𝓤₀ ̇
uniform-modulus-superadditive m₁ m₂ f is-cont ε₁ ε₂ = (uniform-modulus m₁ m₂ f is-cont ε₁ ℚ₊+ uniform-modulus m₁ m₂ f is-cont ε₂) ℚ₊≤ uniform-modulus m₁ m₂ f is-cont (ε₁ ℚ₊+ ε₂)

\end{code}

Any continuous rational function which satisfies modulus of continuity
superadditivity can be extended to the Dedekind Reals.

Let (f : ℚ → ℚ) be a continuous function which satisifies δ-superadditive.

Then we want to define (f̂ : ℝ → ℝ) which
 A) is continuous,
 B) satisfies ι (f q) ＝ f̂ (ι q).

Let x ∈ ℝ be given. Then define f̂(x) ≔ (L , R), with
 L p ≔ ∃ (u , v , ε₊) : ℚ × ℚ × ℚ₊ , (u < x < v) × (|u - v| < δ⦅ ε ⦆) × p < f u - ε
 R q ≔ ∃ (u , v , ε₊) : ℚ × ℚ × ℚ₊ , (u < x < v) × (|u - v| < δ⦅ ε ⦆) × f v + ε < q

To show that these cuts indeed defined a real number, we must check
they satisfy the properties.

Inhabited:

 Choose ε = 1. By real arithmetic locatedness, we find u and v with u < x < v, |u - v| < 1.
 Let p = (f u - ε) - 1,
     q = (f v + ε) + 1.
 Hence f̂(x) is inhabited.

Rounded:

 Let p' be given, with p < p' < f̂(x).
 Then ∃ (u , v , ε₊) : ℚ × ℚ × ℚ₊ , (u < x < v) × (|u - v| < δ⦅ ε ⦆) × p' < f u - ε.
 Hence, ∃ (u , v , ε₊) : ℚ × ℚ × ℚ₊ , (u < x < v) × (|u - v| < δ⦅ ε ⦆) × p < f u - ε,
 since p < p' < f u - ε.

 Let p < f̂(x) be given.
 Then ∃ (u , v , ε₊) : ℚ × ℚ × ℚ₊ , (u < x < v) × (|u - v| < δ⦅ ε ⦆) × p < f u - ε.
 Then there exists p' with p < p' < f u - ε by order density of rationals.
 Hence, ∃ (u , v , ε₊) : ℚ × ℚ × ℚ₊ , (u < x < v) × (|u - v| < δ⦅ ε ⦆) × p' < f u - ε.

 R is rounded using an analagous argument for upper cuts.

Located:

 Let p q be given with p < q.

 Choose ε = (q - p) / 4.
 Using arithmetic locatedness of real numbers, find u, v with (u < x < v) × (|u - v| < δ⦅ ε ⦆).
 By continuity of f, we have that |f u - f v| < ε.
 Now, f u - ε < f v + ε, and 0 < f v - f u + 2ε < 3ε < 4ε = q - p.

 It follows that (f v + ε) - (f u - ε) < q - p, and consequently, p < f u - ε or f v + ε < q.
 In case p < f u - ε, p < f̂ x.
 In case f v + ε < q, f̂ x < q.

 Hence, f̂ x is located.

Disjoint:

 In the presence of locatedness, is suffices to prove that ¬ (p < f̂ x < p).
 Suppose that p < f̂ x < p.
 Then ∃ (u  , v  , ε₊ ) : ℚ × ℚ × ℚ₊ , (u  < x < v ) × (|u  - v | < δ⦅ ε  ⦆) × p < f u - ε, and
      ∃ (u' , v' , ε'₊) : ℚ × ℚ × ℚ₊ , (u' < x < v') × (|u' - v'| < δ⦅ ε' ⦆) × f v' + ε' < p.

 Hence, f v' + ε' < f u - ε, so ε + ε' < f u - f v'.
 Consequently, it must be the case by trichotomy that |u - v'| ≥ δ(ε + ε'), since |u - v'| < δ(ε + ε')
 is a contradiction.

 We also have that |u - v'| = |u - x + x - v'| ≤ |u - x| + |x - v'| < |u - v|  + |u'- v'| < δ(ε₁) + δ(ε₂).
                                                                    < |u - v'| + |u - v'|
 Since δ is superadditive, δ(ε') + δ(ε) ≤ δ(ε + ε')
                                        ≤ |u - v'| (trichotomy)
                                        < δ(ε') + δ(ε)
 < |u, and we have a contradiction.

 Hence, f̂ x is disjoint.

\begin{code}

distance-ℚ-ℝ : (x y : ℚ) ((ε , 0<ε) : ℚ₊) → B-ℝ (ι x) (ι y) ε 0<ε → B-ℚ x y ε 0<ε
distance-ℚ-ℝ x y (ε , 0<ε) l = ∥∥-rec (ℚ<-is-prop (abs (x - y)) ε) I l
 where
  I : (Σ (p , q , u , v) ꞉ ℚ × ℚ × ℚ × ℚ , (p < x)
                                         × (u < y)
                                         × (x < q)
                                         × (y < v)
                                         × B-ℚ (min p u) (max q v) ε 0<ε)
    → abs (x - y) < ε
  I ((p , q , u , v) , p<x , u<y , x<q , y<v , l₁) = II (ℚ-trichotomous fe x y)
   where
    l₂ : min p u < x
    l₂ = ℚ≤-<-trans fe (min p u) p x (min≤ p u) p<x
    l₃ : x < max q v
    l₃ = ℚ<-≤-trans fe x q (max q v) x<q (max≤ q v)
    l₄ : min p u < y
    l₄ = ℚ≤-<-trans fe (min p u) u y (transport (_≤ u) (min-comm u p) (min≤ u p)) u<y
    l₅ : y < max q v
    l₅ = ℚ<-≤-trans fe y v (max q v) y<v (transport (v ≤_) (max-comm v q) (max≤ v q))
    III : (a b  : ℚ) → min p u < a → b < max q v
                     → a < b
                     → B-ℚ a b ε 0<ε
    III a b l₂ l₃ l₄ = ℚ<-trans (abs (a - b)) (abs (min p u - max q v)) ε V l₁
     where
      IV : b - a < max q v - min p u
      IV = inequality-chain-outer-bounds-inner fe (min p u) a b (max q v) l₂ l₄ l₃
      V : abs (a - b) < abs (min p u - max q v)
      V = transport₂ _<_ (ℚ<-abs fe a b l₄) (ℚ<-abs fe (min p u) (max q v) (ℚ<-trans₂ (min p u) a b (max q v) l₂ l₄ l₃)) IV

    II : (x < y) ∔ (x ＝ y) ∔ (y < x) → abs (x - y) < ε
    II (inl x<y) = III x y l₂ l₅ x<y
    II (inr (inl e)) = transport (_< ε) i 0<ε
     where
      i : 0ℚ ＝ abs (x - y)
      i = 0ℚ          ＝⟨ refl ⟩
          abs 0ℚ      ＝⟨ ap abs (ℚ-inverse-sum-to-zero fe x ⁻¹) ⟩
          abs (x - x) ＝⟨ ap (λ z → abs (x - z)) e ⟩
          abs (x - y) ∎
    II (inr (inr y<x)) = ℚ-m2 y x ε 0<ε (III y x l₄ l₃ y<x)

distance-ℚ-ℝ-ℚ : (u v : ℚ) ((ε , 0<ε) : ℚ₊) (x : ℝ) → (u < x) × (x < v) → B-ℚ u v ε 0<ε → B-ℝ (ι u) x ε 0<ε
distance-ℚ-ℝ-ℚ u v (ε , 0<ε) x (u<x , x<v) l = ∥∥-functor I (rounded-right-b (upper-cut-of x) (rounded-from-real-R x) v x<v)
 where
  I : Σ v' ꞉ ℚ , v' < v × x < v' → Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , (a < u) × (c < x) × (u < b) × (x < d) × B-ℚ (min a c) (max b d) ε 0<ε
  I (v' , v'<v , x<v') = (u - (v - v') , v' , u - (v - v') , v')
                       , l₁
                       , rounded-left-c (lower-cut-of x) (rounded-from-real-L x) (u - (v - v')) u l₁ u<x
                       , disjoint-from-real x u v' (u<x , x<v')
                       , x<v'
                       , transport (_< ε) (II ⁻¹) l
   where
    l₁ : u - (v - v') < u
    l₁ = ℚ<-subtraction-preserves-order fe u (v - v') (ℚ<-difference-positive fe v' v v'<v)
    II : abs (min (u - (v - v')) (u - (v - v')) - (max v' v')) ＝ abs (u - v)
    II = abs (min (u - (v - v')) (u - (v - v')) - max v' v') ＝⟨ ap₂ (λ z z' → abs (z - z')) (min-refl (u - (v - v'))) (max-refl v') ⟩
         abs (u - (v - v') - v')                             ＝⟨ ap (λ z → abs (u + z - v')) (ℚ-minus-dist fe v (- v') ⁻¹) ⟩
         abs (u + ((- v) + (- (- v'))) - v')                 ＝⟨ ap (λ z → abs (z - v')) (ℚ+-assoc fe u (- v) (- (- v')) ⁻¹) ⟩
         abs (u - v + (- (- v')) - v')                       ＝⟨ ap abs (ℚ+-assoc fe (u - v) ((- (- v'))) ((- v'))) ⟩
         abs (u - v + (((- (- v')) - v')))                   ＝⟨ ap (λ z → abs (u - v + z)) (ℚ-inverse-sum-to-zero' fe ((- v'))) ⟩
         abs (u - v + 0ℚ)                                    ＝⟨ ap abs (ℚ-zero-right-neutral fe (u - v)) ⟩
         abs (u - v) ∎

distance-ℚ-ℝ-ℚ' : (u v : ℚ) ((ε , 0<ε) : ℚ₊) (x : ℝ) → (u < x) × (x < v) → B-ℚ u v ε 0<ε → B-ℝ x (ι v) ε 0<ε
distance-ℚ-ℝ-ℚ' u v (ε , 0<ε) x (u<x , x<v) l = ∥∥-functor I (rounded-left-b (lower-cut-of x) (rounded-from-real-L x) u u<x)
 where
  I : Σ u' ꞉ ℚ , u < u' × u' < x → Σ (a , b , c , d) ꞉ ℚ × ℚ × ℚ × ℚ , (a < x) × (c < v) × (x < b) × (v < d) × B-ℚ (min a c) (max b d) ε 0<ε
  I (u' , u<u' , u'<x) = (u' , v + (u' - u) , u' , v + (u' - u))
                       , u'<x
                       , disjoint-from-real x u' v (u'<x , x<v)
                       , rounded-right-c (upper-cut-of x) (rounded-from-real-R x) v (v + (u' - u)) l₁ x<v
                       , l₁
                       , transport (_< ε) (II ⁻¹) l
   where
    l₁ : v < v + (u' - u)
    l₁ = ℚ<-addition-preserves-order'' fe v (u' - u) (ℚ<-difference-positive fe u u' u<u')
    II : abs (min u' u' - max (v + (u' - u)) (v + (u' - u))) ＝ abs (u - v)
    II = abs (min u' u' - max (v + (u' - u)) (v + (u' - u))) ＝⟨ ap₂ (λ z z' → abs (z - z')) (min-refl u') (max-refl (v + (u' - u))) ⟩
         abs (u' - (v + (u' - u)))                           ＝⟨ ap (λ z → abs (u' + z)) (ℚ-minus-dist fe v (u' - u) ⁻¹) ⟩
         abs (u' + ((- v) + (- (u' - u))))                   ＝⟨ ap (λ z → abs (u' + z)) (ℚ+-comm (- v) (- (u' - u))) ⟩
         abs (u' + ((- (u' - u)) - v))                       ＝⟨ ap abs (ℚ+-assoc fe u' (- (u' - u)) (- v) ⁻¹) ⟩
         abs (u' - (u' - u) - v)                             ＝⟨ ap (λ z → abs (u' + z - v)) (ℚ-minus-dist fe u' (- u) ⁻¹) ⟩
         abs (u' + ((- u') - (- u)) - v)                     ＝⟨ ap (λ z → abs (z - v)) ( ℚ+-assoc fe u' (- u') (- (- u)) ⁻¹) ⟩
         abs (u' - u' - (- u) - v)                           ＝⟨ ap (λ z → abs (z - (- u) - v)) (ℚ-inverse-sum-to-zero fe u' ) ⟩
         abs (0ℚ - (- u) - v)                                ＝⟨ ap (λ z → abs (z - v)) (ℚ-zero-left-neutral fe (- (- u))) ⟩
         abs ((- (- u)) - v)                                 ＝⟨ ap (λ z → abs (z - v)) (ℚ-minus-minus fe u ⁻¹) ⟩
         abs (u - v) ∎

extension-theorem : 𝓤₁ ̇
extension-theorem = (f : ℚ → ℚ)
                  → (ic : is-uniformly-continuous ℚ-metric-space ℚ-metric-space f)
                  → (δ-sup : (ε₁ ε₂ : ℚ₊) → uniform-modulus-superadditive ℚ-metric-space ℚ-metric-space f ic ε₁ ε₂)
                  → ℝ → ℝ

f→f̂ : extension-theorem
f→f̂ f is-continuous δ-sup x = (L , R) , inhabited-l , inhabited-r , rounded-l , rounded-r , is-disjoint , is-located
 where
  L R : 𝓟 ℚ
  L p = (∃ (u , v , (ε , 0<ε)) ꞉ ℚ × ℚ × ℚ₊ , (u < x) × (x < v) × B-ℚ u v (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) × p + ε < f u) , ∃-is-prop
  R q = (∃ (u , v , (ε , 0<ε)) ꞉ ℚ × ℚ × ℚ₊ , (u < x) × (x < v) × B-ℚ u v (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) × f v < q - ε) , ∃-is-prop

  δ' : ℚ
  δ' = pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (1ℚ , 0 , refl))
  0<δ' : 0ℚ < δ'
  0<δ' = pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (1ℚ , 0 , refl))
  find-uv : ∃ (u , v) ꞉ ℚ × ℚ , (u < x) × (x < v) × (0ℚ < v - u) × (v - u < δ')
  find-uv = ℝ-arithmetically-located x δ' 0<δ'

  inhabited-l : inhabited-left L
  inhabited-l = ∥∥-rec ∃-is-prop I find-uv
   where
    I : (Σ (u , v) ꞉ ℚ × ℚ , (u < x) × (x < v) × (0ℚ < v - u) × (v - u < δ')) → ∃ p ꞉ ℚ , p ∈ L
    I ((u , v) , u<x , x<v , l₁ , l₂) = ∣ f u - 1ℚ - 1ℚ , ∣ (u , v , 1ℚ , 0 , refl) , u<x , x<v , IV , V ∣ ∣
     where
      II : f u - 1ℚ ＝ f u - 1ℚ - 1ℚ + 1ℚ
      II = f u - 1ℚ                   ＝⟨ ℚ-zero-right-neutral fe (f u - 1ℚ) ⁻¹ ⟩
           f u - 1ℚ + 0ℚ              ＝⟨ ap (f u - 1ℚ +_) (ℚ-inverse-sum-to-zero' fe 1ℚ ⁻¹) ⟩
           f u - 1ℚ + ((- 1ℚ) + 1ℚ)   ＝⟨ ℚ+-assoc fe (f u - 1ℚ) (- 1ℚ) 1ℚ ⁻¹ ⟩
           f u - 1ℚ - 1ℚ + 1ℚ         ∎
      III : abs (v - u) < δ'
      III = pos-abs-no-increase fe (v - u) δ' (l₁ , l₂)
      IV : abs (u - v) < δ'
      IV = transport (_< δ') (ℚ-metric-commutes v u) III
      V : f u - 1ℚ - 1ℚ + 1ℚ < f u
      V = transport (_< f u) II (order1ℚ' fe (f u))

  inhabited-r : inhabited-right R
  inhabited-r = ∥∥-rec ∃-is-prop I find-uv
   where
    I : (Σ (u , v) ꞉ ℚ × ℚ , (u < x) × (x < v) × (0ℚ < v - u) × (v - u < δ')) → ∃ q ꞉ ℚ , q ∈ R
    I ((u , v) , u<x , x<v , l₁ , l₂) = ∣ (f v + 1ℚ + 1ℚ) , ∣ (u , v , 1ℚ , 0 , refl) , u<x , x<v , IV , V ∣ ∣
     where
      II : f v + 1ℚ ＝ f v + 1ℚ + 1ℚ - 1ℚ
      II = f v + 1ℚ              ＝⟨ ℚ-zero-right-neutral fe (f v + 1ℚ) ⁻¹ ⟩
           f v + 1ℚ + 0ℚ         ＝⟨ ap (f v + 1ℚ +_) (ℚ-inverse-sum-to-zero fe 1ℚ ⁻¹) ⟩
           f v + 1ℚ + (1ℚ - 1ℚ)  ＝⟨ ℚ+-assoc fe (f v + 1ℚ) 1ℚ (- 1ℚ) ⁻¹ ⟩
           f v + 1ℚ + 1ℚ - 1ℚ    ∎
      III : abs (v - u) < δ'
      III = pos-abs-no-increase fe (v - u) δ' (l₁ , l₂)
      IV : abs (u - v) < δ'
      IV = transport (_< δ') (ℚ-metric-commutes v u) III
      V : f v < f v + 1ℚ + 1ℚ - 1ℚ
      V = transport (f v <_) II (order1ℚ fe (f v))


  rounded-l : rounded-left L
  rounded-l p = ltr , rtl
   where
    ltr : ∃ (u , v , (ε , 0<ε)) ꞉ ℚ × ℚ × ℚ₊ , (u < x) × (x < v) × B-ℚ u v (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) × p + ε < f u
        → ∃ p' ꞉ ℚ , p < p' × p' ∈ L
    ltr = ∥∥-functor I
     where

      I : Σ (u , v , (ε , 0<ε)) ꞉ ℚ × ℚ × ℚ₊ , (u < x) × (x < v) × B-ℚ u v (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) × p + ε < f u
        → Σ p' ꞉ ℚ , p < p' × p' ∈ L
      I ((u , v , (ε , 0<ε)) , u<x , x<v , u-v<δ , l) = II (ℚ-dense fe (p + ε) (f u) l)
       where
        δ : ℚ
        δ = pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))
        0<δ : 0ℚ < δ
        0<δ = pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))
        II : (Σ p' ꞉ ℚ , p + ε < p' × p' < f u) → Σ p' ꞉ ℚ , p < p' × p' ∈ L
        II (p' , l₁ , l₂) = p' - ε , (ℚ<-subtraction-preserves-order''' fe p ε p' l₁ , ∣ (u , v , ε , 0<ε) , u<x , x<v , u-v<δ , i ∣)
         where
          ii : p' ＝ p' - ε + ε
          ii = p'               ＝⟨ ℚ-zero-right-neutral fe p' ⁻¹ ⟩
               p' + 0ℚ          ＝⟨ ap (p' +_) (ℚ-inverse-sum-to-zero' fe ε ⁻¹) ⟩
               p' + ((- ε) + ε) ＝⟨ ℚ+-assoc fe p' (- ε) ε ⁻¹ ⟩
               p' - ε + ε ∎
          i : p' - ε + ε <ℚ f u
          i = transport (_< f u) ii l₂
    rtl : ∃ p' ꞉ ℚ , p < p' × p' ∈ L → p ∈ L
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ p' ꞉ ℚ , p < p' × p' ∈ L → p ∈ L
      I (p' , p<p' , p'<x) = ∥∥-functor II p'<x
       where
        II : Σ (u , v , (ε , 0<ε)) ꞉ ℚ × ℚ × ℚ₊ , (u < x) × (x < v) × B-ℚ u v (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) × p' + ε < f u
           → Σ (u , v , (ε , 0<ε)) ꞉ ℚ × ℚ × ℚ₊ , (u < x) × (x < v) × B-ℚ u v (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) × p + ε < f u
        II ((u , v , (ε , 0<ε)) , u<x , x<v , u-v<δ , l) = (u , v , ε , 0<ε) , u<x , x<v , u-v<δ , i
         where
          i : (p + ε) <ℚ f u
          i = ℚ<-trans (p + ε) (p' + ε) (f u) (ℚ<-addition-preserves-order p p' ε p<p') l
  rounded-r : rounded-right R
  rounded-r q = ltr , rtl
   where
    ltr : ∃ (u , v , (ε , 0<ε)) ꞉ ℚ × ℚ × ℚ₊ , (u < x) × (x < v) × B-ℚ u v (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) × f v < q - ε
        → ∃ q' ꞉ ℚ , q' < q × q' ∈ R
    ltr = ∥∥-functor I
     where
      I : Σ (u , v , (ε , 0<ε)) ꞉ ℚ × ℚ × ℚ₊ , (u < x) × (x < v) × B-ℚ u v (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) × f v < q - ε
        → Σ q' ꞉ ℚ , q' < q × q' ∈ R
      I ((u , v , (ε , 0<ε)) , u<x , x<v , u-v<δ , l) = II (ℚ-dense fe (f v) (q - ε) l)
       where
        II : (Σ q' ꞉ ℚ , f v < q' × q' < q - ε) → Σ q' ꞉ ℚ , q' < q × q' ∈ R
        II (q' , l₁ , l₂) = q' + ε , (ℚ<-subtraction-preserves-order'' fe q' q ε l₂ , ∣ (u , v , ε , 0<ε) , u<x , x<v , u-v<δ , transport (f v <_) ii l₁ ∣)
         where
          ii : q' ＝ q' + ε - ε
          ii = q'            ＝⟨ ℚ-zero-right-neutral fe q' ⁻¹ ⟩
               q' + 0ℚ       ＝⟨ ap (q' +_) (ℚ-inverse-sum-to-zero fe ε ⁻¹) ⟩
               q' + (ε - ε) ＝⟨ ℚ+-assoc fe q' ε (- ε) ⁻¹ ⟩
               q' + ε - ε ∎
    rtl : ∃ q' ꞉ ℚ , q' < q × q' ∈ R → q ∈ R
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ q' ꞉ ℚ , q' < q × q' ∈ R → q ∈ R
      I (q' , q'<q , x<q') = ∥∥-functor II x<q'
       where
        II : Σ (u , v , (ε , 0<ε)) ꞉ ℚ × ℚ × ℚ₊ , (u < x) × (x < v) × B-ℚ u v (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) × f v < q' - ε
           → Σ (u , v , (ε , 0<ε)) ꞉ ℚ × ℚ × ℚ₊ , (u < x) × (x < v) × B-ℚ u v (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))) × f v < q - ε
        II ((u , v , (ε , 0<ε)) , u<x , x<v , u-v<δ , l) = (u , v , ε , 0<ε) , u<x , x<v , u-v<δ , i
         where
          i : f v < q - ε
          i = ℚ<-trans (f v) (q' - ε) (q - ε) l (ℚ<-addition-preserves-order q' q (- ε) q'<q)
  is-located : located L R
  is-located p q p<q = ∥∥-functor
                        I
                         (ℝ-arithmetically-located x
                           (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (1/4 * (q - p) , ℚ<-pos-multiplication-preserves-order 1/4 (q - p) (0 , refl) (ℚ<-difference-positive fe p q p<q))))
                            (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (1/4 * (q - p) , ℚ<-pos-multiplication-preserves-order 1/4 (q - p) (0 , refl) (ℚ<-difference-positive fe p q p<q)))))
   where
    0<1/4q-p : 0ℚ < 1/4 * (q - p)
    0<1/4q-p = ℚ<-pos-multiplication-preserves-order 1/4 (q - p) (0 , refl) (ℚ<-difference-positive fe p q p<q)
    I : Σ (u , v) ꞉ ℚ × ℚ , (u < x) × (x < v) × (0ℚ < v - u) × (v - u < pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (1/4 * (q - p) , ℚ<-pos-multiplication-preserves-order 1/4 (q - p) (0 , refl) (ℚ<-difference-positive fe p q p<q)))) → p ∈ L ∔ q ∈ R
    I ((u , v) , u<x , x<v , 0<v-u , v-u<δ) = Cases II III IV
     where
      vu : B-ℚ v u (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (1/4 * (q - p) , 0<1/4q-p)))
                   (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (1/4 * (q - p) , 0<1/4q-p)))
      vu = (pos-abs-no-increase fe (v - u)
            (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (1/4 * (q - p) , 0<1/4q-p)))
             (0<v-u , v-u<δ))
      uv : B-ℚ u v (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (1/4 * (q - p) , 0<1/4q-p)))
                   (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (1/4 * (q - p) , 0<1/4q-p)))
      uv = ℚ-m2 v u (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (1/4 * (q - p) , 0<1/4q-p)))
                    (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (1/4 * (q - p) , 0<1/4q-p)))
                     vu

      ii : f v - f u + (1/4 * (q - p) + 1/4 * (q - p)) ＝ (f v + 1/4 * (q - p)) - (f u - 1/4 * (q - p))
      ii = f v - f u + (1/4 * (q - p) + 1/4 * (q - p))         ＝⟨ ℚ+-assoc fe (f v - f u) (1/4 * (q - p)) (1/4 * (q - p)) ⁻¹ ⟩
            f v - f u + 1/4 * (q - p) + 1/4 * (q - p)           ＝⟨ ap (_+ 1/4 * (q - p)) (ℚ+-assoc fe (f v) (- f u) (1/4 * (q - p))) ⟩
            f v + ((- f u) + 1/4 * (q - p)) + 1/4 * (q - p)     ＝⟨ ℚ+-assoc fe (f v) ((- f u) + (1/4 * (q - p))) (1/4 * (q - p)) ⟩
            f v + ((- f u) + 1/4 * (q - p) + 1/4 * (q - p))     ＝⟨ ap (f v +_) (ℚ+-comm ((- f u) + (1/4 * (q - p))) (1/4 * (q - p))) ⟩
            f v + (1/4 * (q - p) + ((- f u) + 1/4 * (q - p)))   ＝⟨ ℚ+-assoc fe (f v) (1/4 * (q - p)) ((- f u) + (1/4 * (q - p))) ⁻¹ ⟩
            f v + 1/4 * (q - p) + ((- f u) + 1/4 * (q - p))     ＝⟨ ap (λ z → f v + 1/4 * (q - p) + ((- f u) + z)) (ℚ-minus-minus fe (1/4 * (q - p))) ⟩
            f v + 1/4 * (q - p) + ((- f u) - (- 1/4 * (q - p))) ＝⟨ ap (f v + 1/4 * (q - p) +_) (ℚ-minus-dist fe (f u) (- 1/4 * (q - p))) ⟩
            f v + 1/4 * (q - p) - (f u - 1/4 * (q - p)) ∎
      iv : f v - f u + (1/4 * (q - p) + 1/4 * (q - p)) < 1/4 * (q - p) + (1/4 * (q - p) + 1/4 * (q - p))
      iv = ℚ<-addition-preserves-order (f v - f u) (1/4 * (q - p)) (1/4 * (q - p) + 1/4 * (q - p)) (pr₂ (ℚ-abs-<-unpack fe (f v - f u) (1/4 * (q - p)) (pr₂ (is-continuous (1/4 * (q - p) , 0<1/4q-p)) v u vu)))
      xi : 3/4 * (q - p) ＝ 1/4 * (q - p) + (1/4 * (q - p) + 1/4 * (q - p))
      xi = 3/4 * (q - p)                                   ＝⟨ ℚ-distributivity' fe (q - p) 1/4 1/2 ⟩
           1/4 * (q - p) + 1/2 * (q - p)                   ＝⟨ ap (1/4 * (q - p) +_) (ℚ-distributivity' fe (q - p) 1/4 1/4) ⟩
           1/4 * (q - p) + (1/4 * (q - p) + 1/4 * (q - p)) ∎
      xii : 3/4 * (q - p) < (q - p)
      xii = transport (3/4 * (q - p) <_)
               (ℚ-mult-left-id fe (q - p)) (
                (ℚ<-pos-multiplication-preserves-order' fe 3/4 1ℚ (q - p) (0 , refl) (ℚ<-difference-positive fe p q p<q)))
      vi : 1/4 * (q - p) + (1/4 * (q - p) + 1/4 * (q - p)) < q - p
      vi = transport (_< q - p) xi xii
      iii : f v - f u + (1/4 * (q - p) + 1/4 * (q - p)) < q - p
      iii = ℚ<-trans (f v - f u + (1/4 * (q - p) + 1/4 * (q - p))) (1/4 * (q - p) + (1/4 * (q - p) + 1/4 * (q - p))) (q - p) iv vi
      i : (f v + 1/4 * (q - p) - (f u - 1/4 * (q - p))) <ℚ (q - p)
      i = transport (_< q - p) ii iii
      II : p < f u - 1/4 * (q - p) ∔ f v + 1/4 * (q - p) < q
      II = order-lemma fe (f v + 1/4 * (q - p)) (f u - 1/4 * (q - p)) q p i
      III : p < f u - 1/4 * (q - p) → p ∈ L ∔ q ∈ R
      III l = inl ∣ (u , v , 1/4 * (q - p) , 0<1/4q-p) , u<x , x<v , uv , (ℚ<-subtraction-preserves-order'' fe p (f u) (1/4 * (q - p)) l) ∣
      IV : f v + 1/4 * (q - p) < q → p ∈ L ∔ q ∈ R
      IV l = inr ∣ (u , v , 1/4 * (q - p) , 0<1/4q-p) , u<x , x<v , uv , (ℚ<-subtraction-preserves-order''' fe (f v) (1/4 * (q - p)) q l) ∣

  is-disjoint : disjoint L R
  is-disjoint = disjoint→trans L R is-located I
   where
    I : (p : ℚ) → ¬ (p ∈ L × p ∈ R)
    I p (p<fx , fx<p) = ∥∥-rec 𝟘-is-prop II (binary-choice p<fx fx<p)
     where
      II : (Σ (u  , v  , (ε  , 0<ε )) ꞉ ℚ × ℚ × ℚ₊ , (u  < x) × (x < v ) ×  B-ℚ u v   (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε  , 0<ε ))) (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε  , 0<ε ))) × p + ε < f u)
         × (Σ (u' , v' , (ε' , 0<ε')) ꞉ ℚ × ℚ × ℚ₊ , (u' < x) × (x < v') ×  B-ℚ u' v' (pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε' , 0<ε'))) (pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε' , 0<ε'))) × f v' < p - ε')
         → 𝟘
      II (((u , v , (ε , 0<ε)) , u<x , x<v , l₁ , l₂) , (u' , v' , (ε' , 0<ε')) , u'<x , x<v' , l₃ , l₄)
       = III (ℚ-trichotomous fe (abs (u - v')) δ)
        where
         δ δ₁ δ₂ : ℚ
         δ  = pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous ((ε , 0<ε) ℚ₊+ ((ε' , 0<ε'))))
         δ₁ = pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε))
         δ₂ = pr₁ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε' , 0<ε'))
         0<δ : 0ℚ < δ
         0<δ = pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous ((ε , 0<ε) ℚ₊+ ((ε' , 0<ε'))))
         0<δ₁ = pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε  , 0<ε))
         0<δ₂ = pr₂ (uniform-modulus ℚ-metric-space ℚ-metric-space f is-continuous (ε' , 0<ε'))
         cont : B-ℚ u v' δ 0<δ → B-ℚ (f u) (f v') (ε + ε') (ℚ<-adding-zero ε ε' 0<ε 0<ε')
         cont = pr₂ (is-continuous ((ε , 0<ε) ℚ₊+ (ε' , 0<ε'))) u v'
         III : abs (u - v') < δ ∔ (abs (u - v') ＝ δ) ∔ δ < abs (u - v') → 𝟘
         III (inl l₅)       = ℚ<-not-itself (ε + ε') (ℚ<-trans (ε + ε') (abs (f u - f v')) (ε + ε') iv using-continuity)
          where
           using-continuity : abs (f u - f v') < (ε + ε')
           using-continuity = cont l₅
           i : f v' + ε' < f u - ε
           i = ℚ<-trans (f v' + ε') p (f u - ε)
               (ℚ<-subtraction-preserves-order'' fe (f v') p ε' l₄)
                (ℚ<-subtraction-preserves-order''' fe p ε (f u) l₂)
           ii : ε + ε' < f u - f v'
           ii = transport₂ _<_ α β (ℚ<-addition-preserves-order (f v' + ε') (f u - ε) (ε - f v') i)
            where
             α : f v' + ε' + (ε - f v') ＝ ε + ε'
             α = f v' + ε' + (ε - f v')     ＝⟨ ℚ+-assoc fe (f v' + ε') ε (- f v') ⁻¹                    ⟩
                 f v' + ε' + ε - f v'       ＝⟨ ap (_- f v') (ℚ+-assoc fe (f v') ε' ε)                   ⟩
                 f v' + (ε' + ε) - f v'     ＝⟨ ap (_- f v') (ℚ+-comm (f v') (ε' + ε))                   ⟩
                 ε' + ε + f v' - f v'       ＝⟨ ℚ+-assoc fe (ε' + ε) (f v') (- f v')                     ⟩
                 ε' + ε + (f v' - f v')     ＝⟨ ap₂ _+_ (ℚ+-comm ε' ε) (ℚ-inverse-sum-to-zero fe (f v')) ⟩
                 ε + ε' + 0ℚ                ＝⟨ ℚ-zero-right-neutral fe (ε + ε')                         ⟩
                 ε + ε'                     ∎
             β : f u - ε + (ε - f v') ＝ f u - f v'
             β = f u - ε + (ε - f v')     ＝⟨ ℚ+-assoc fe (f u - ε) ε (- f v') ⁻¹                     ⟩
                 f u - ε + ε - f v'       ＝⟨ ap (_- f v') (ℚ+-assoc fe (f u) (- ε) ε)                ⟩
                 f u + ((- ε) + ε) - f v' ＝⟨ ap (λ z → f u + z - f v') (ℚ-inverse-sum-to-zero' fe ε) ⟩
                 f u + 0ℚ - f v'          ＝⟨ ap (_- f v') (ℚ-zero-right-neutral fe (f u))            ⟩
                 f u - f v'               ∎
           iv : ε + ε' < abs (f u - f v')
           iv = ℚ<-≤-trans fe (ε + ε') (f u - f v') (abs (f u - f v')) ii (pr₂ (ℚ-abs-≤  fe (f u - f v')))
         III (inr l₅)  = ℚ<-not-itself (δ₁ + δ₂) (ℚ≤-<-trans fe (δ₁ + δ₂) (abs (u - v')) (δ₁ + δ₂) iv ii)
          where
           i : B-ℝ (ι u) (ι v') (δ₁ + δ₂) (ℚ<-adding-zero δ₁ δ₂ 0<δ₁ 0<δ₂)
           i = ℝ-m4 (ι u) x (ι v') δ₁ δ₂ 0<δ₁ 0<δ₂ ii iii
            where
             ii : B-ℝ (ι u) x δ₁ 0<δ₁
             ii = distance-ℚ-ℝ-ℚ u v (δ₁ , 0<δ₁) x (u<x , x<v) l₁
             iii : B-ℝ x (ι v') δ₂ 0<δ₂
             iii = distance-ℚ-ℝ-ℚ' u' v' (δ₂ , 0<δ₂) x (u'<x , x<v') l₃
           ii : B-ℚ u v' (δ₁ + δ₂) (ℚ<-adding-zero δ₁ δ₂ 0<δ₁ 0<δ₂)
           ii = distance-ℚ-ℝ u v' (δ₁ + δ₂ , ℚ<-adding-zero δ₁ δ₂ 0<δ₁ 0<δ₂) i
           iii : uniform-modulus-superadditive ℚ-metric-space ℚ-metric-space f is-continuous (ε , 0<ε) (ε' , 0<ε')
           iii = (δ-sup (ε , 0<ε) (ε' , 0<ε'))
           l₆ : δ ≤ abs (u - v')
           l₆ = Cases l₅ (λ e → transport (δ ≤_) (e ⁻¹) (ℚ≤-refl δ)) (ℚ<-coarser-than-≤ δ (abs (u - v')))
           iv : δ₁ + δ₂ ≤ abs (u - v')
           iv = ℚ≤-trans fe (δ₁ + δ₂) δ (abs (u - v')) iii l₆

\end{code}
