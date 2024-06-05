Martin Escardo

In univalent logic, as opposed to Curry-Howard logic, a proposition is
a subsingleton or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Subsingletons where

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import MLTT.Unit-Properties
open import UF.Base

is-prop : 𝓤 ̇ → 𝓤 ̇
is-prop X = (x y : X) → x ＝ y

is-prop-valued-family : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-prop-valued-family A = ∀ x → is-prop (A x)

\end{code}

And of course we could adopt a terminology borrowed from topos logic:

\begin{code}

is-truth-value is-subsingleton : 𝓤 ̇ → 𝓤 ̇
is-truth-value  = is-prop
is-subsingleton = is-prop

Σ-is-prop : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
          → is-prop X
          → ((x : X) → is-prop (A x))
          → is-prop (Σ A)
Σ-is-prop {𝓤} {𝓥} {X} {A} i j (x , a) (y , b) =
 to-Σ-＝ (i x y , j y (transport A (i x y) a) b)

\end{code}

Next we define singleton (or contractible types). The terminology
"contractible" is due to Voevodsky. I currently prefer the terminology
"singleton type", because it makes more sense when we consider
univalent type theory as interesting on its own right independently of
its homotopical (originally motivating) models. Also it emphasizes
that we don't require homotopy theory as a prerequisite to understand
univalent type theory.

\begin{code}

is-central : (X : 𝓤 ̇ ) → X → 𝓤 ̇
is-central X c = (x : X) → c ＝ x

is-singleton : 𝓤 ̇ → 𝓤 ̇
is-singleton X = Σ c ꞉ X , is-central X c

center : {X : 𝓤 ̇ } → is-singleton X → X
center = pr₁

centrality : {X : 𝓤 ̇ } (i : is-singleton X) → is-central X (center i)
centrality = pr₂

\end{code}

For compatibility with the homotopical terminology:

\begin{code}

is-center-of-contraction-of : (X : 𝓤 ̇ ) → X → 𝓤 ̇
is-center-of-contraction-of = is-central

is-contr : 𝓤 ̇ → 𝓤 ̇
is-contr = is-singleton

𝟙-is-singleton : is-singleton (𝟙 {𝓤})
𝟙-is-singleton = ⋆ , (λ (x : 𝟙) → (𝟙-all-⋆ x)⁻¹)

singletons-are-props : {X : 𝓤 ̇ } → is-singleton X → is-prop X
singletons-are-props (c , φ) x y = x ＝⟨ (φ x) ⁻¹ ⟩
                                   c ＝⟨ φ y ⟩
                                   y ∎

prop-criterion' : {X : 𝓤 ̇ }
                → (X → is-singleton X)
                → is-prop X
prop-criterion' φ x = singletons-are-props (φ x) x

prop-criterion : {X : 𝓤 ̇ } → (X → is-prop X) → is-prop X
prop-criterion φ x = φ x x

pointed-props-are-singletons : {X : 𝓤 ̇ }
                             → X
                             → is-prop X
                             → is-singleton X
pointed-props-are-singletons x h = x , h x

\end{code}

The two prototypical propositions:

\begin{code}

𝟘-is-prop : is-prop (𝟘 {𝓤})
𝟘-is-prop {𝓤} x y = unique-from-𝟘 {𝓤} {𝓤} x

𝟙-is-prop : is-prop (𝟙 {𝓤})
𝟙-is-prop {𝓤} ⋆ ⋆ = refl {𝓤}

singleton-type : {X : 𝓤 ̇ } (x : X) → 𝓤 ̇
singleton-type x = Σ y ꞉ type-of x , x ＝ y

singleton-center : {X : 𝓤 ̇ } (x : X) → singleton-type x
singleton-center x = (x , refl)

singleton-types-are-singletons'' : {X : 𝓤 ̇ } {x x' : X} (r : x ＝ x')
                                 → singleton-center x ＝ (x' , r)
singleton-types-are-singletons'' {𝓤} {X} = J A (λ x → refl)
 where
  A : (x x' : X) → x ＝ x' → 𝓤 ̇
  A x x' r = singleton-center x ＝[ Σ x' ꞉ X , x ＝ x' ] (x' , r)

singleton-types-are-singletons : {X : 𝓤 ̇ } (x₀ : X)
                               → is-singleton (singleton-type x₀)
singleton-types-are-singletons x₀ = singleton-center x₀ , (λ t → singleton-types-are-singletons'' (pr₂ t))

singleton-types-are-singletons' : {X : 𝓤 ̇ } {x : X}
                                → is-central (singleton-type x) (x , refl)
singleton-types-are-singletons' {𝓤} {X} (y , refl) = refl

singleton-types-are-props : {X : 𝓤 ̇ } (x : X) → is-prop (singleton-type x)
singleton-types-are-props x = singletons-are-props (singleton-types-are-singletons x)

singleton-type' : {X : 𝓤 ̇ } → X → 𝓤 ̇
singleton-type' x = Σ y ꞉ type-of x , y ＝ x

singleton'-center : {X : 𝓤 ̇ } (x : X) → singleton-type' x
singleton'-center x = (x , refl)

×-prop-criterion-necessity : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                           → is-prop (X × Y) → (Y → is-prop X) × (X → is-prop Y)
×-prop-criterion-necessity i = (λ y x x' → ap pr₁ (i (x , y) (x' , y ))) ,
                               (λ x y y' → ap pr₂ (i (x , y) (x  , y')))

×-prop-criterion : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → (Y → is-prop X) × (X → is-prop Y) → is-prop (X × Y)
×-prop-criterion (i , j) (x , y) (x' , y') = to-Σ-＝ (i y x x' , j x _ _)

×-𝟘-is-prop : {X : 𝓤 ̇ } → is-prop (X × 𝟘 {𝓥})
×-𝟘-is-prop (x , z) _ = 𝟘-elim z

𝟘-×-is-prop : {X : 𝓤 ̇ } → is-prop (𝟘 {𝓥} × X)
𝟘-×-is-prop (z , x) _ = 𝟘-elim z

×-is-prop : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
          → is-prop X
          → is-prop Y
          → is-prop (X × Y)
×-is-prop i j = ×-prop-criterion ((λ _ → i) , (λ _ → j))

to-subtype-＝ : {X : 𝓦 ̇ } {A : X → 𝓥 ̇ }
               {x y : X} {a : A x} {b : A y}
             → ((x : X) → is-prop (A x))
             → x ＝ y
             → (x , a) ＝ (y , b)
to-subtype-＝ {𝓤} {𝓥} {X} {A} {x} {y} {a} {b} s p =
 to-Σ-＝ (p , s y (transport A p a) b)

subtypes-of-props-are-props' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
                             → left-cancellable m
                             → is-prop Y
                             → is-prop X
subtypes-of-props-are-props' m lc i x x' = lc (i (m x) (m x'))

pr₁-lc : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
       → ({x : X} → is-prop (Y x))
       → left-cancellable (pr₁ {𝓤} {𝓥} {X} {Y})
pr₁-lc f p = to-Σ-＝ (p , (f _ _))

subsets-of-props-are-props : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
                         → is-prop X
                         → ({x : X} → is-prop (Y x))
                         → is-prop (Σ x ꞉ X , Y x)
subsets-of-props-are-props X Y h p = subtypes-of-props-are-props' pr₁ (pr₁-lc p) h

inl-lc-is-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    {x x' : X}
                    (p : inl {𝓤} {𝓥} {X} {Y} x ＝ inl x')
                  → p ＝ ap inl (inl-lc p)
inl-lc-is-section refl = refl

inr-lc-is-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {y y' : Y}
                    (p : inr {𝓤} {𝓥} {X} {Y} y ＝ inr y')
                  → p ＝ ap inr (inr-lc p)
inr-lc-is-section refl = refl

\end{code}

Formulation of propositional extensionality:

\begin{code}

propext : ∀ 𝓤 → 𝓤 ⁺ ̇
propext 𝓤 = {P Q : 𝓤 ̇ } → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ＝ Q

PropExt : 𝓤ω
PropExt = ∀ 𝓤 → propext 𝓤

Prop-Ext : 𝓤ω
Prop-Ext = ∀ {𝓤} → propext 𝓤

\end{code}

The following says that, in particular, for any proposition P, we have
that P + ¬ P is a proposition, or that the decidability of a
proposition is a proposition:

\begin{code}

sum-of-contradictory-props : {P : 𝓤 ̇ } {Q : 𝓥 ̇ }
                           → is-prop P
                           → is-prop Q
                           → (P → Q → 𝟘 {𝓦})
                           → is-prop (P + Q)
sum-of-contradictory-props {𝓤} {𝓥} {𝓦} {P} {Q} i j f = γ
 where
  γ : (x y : P + Q) → x ＝ y
  γ (inl p) (inl p') = ap inl (i p p')
  γ (inl p) (inr q)  = 𝟘-elim {𝓤 ⊔ 𝓥} {𝓦} (f p q)
  γ (inr q) (inl p)  = 𝟘-elim (f p q)
  γ (inr q) (inr q') = ap inr (j q q')

sum-of-contradictory-props' : {P : 𝓤 ̇ } {Q : 𝓥 ̇ }
                            → (is-prop P × is-prop Q × (P → Q → 𝟘 {𝓦}))
                            → is-prop (P + Q)
sum-of-contradictory-props' (i , j , f) = sum-of-contradictory-props i j f

sum-of-contradictory-props'-converse : {P : 𝓤 ̇ } {Q : 𝓥 ̇ }
                                     → is-prop (P + Q)
                                     → (is-prop P × is-prop Q × (P → Q → 𝟘 {𝓦}))
sum-of-contradictory-props'-converse k =
 (λ p p' → inl-lc (k (inl p) (inl p'))) ,
 (λ q q' → inr-lc (k (inr q) (inr q'))) ,
 (λ p q → 𝟘-elim (+disjoint (k (inl p) (inr q))))

\end{code}

Without assuming excluded middle, we have that there are no truth
values other than 𝟘 and 𝟙:

\begin{code}

no-props-other-than-𝟘-or-𝟙 : propext 𝓤 → ¬ (Σ P ꞉ 𝓤 ̇ , is-prop P × (P ≠ 𝟘) × (P ≠ 𝟙))
no-props-other-than-𝟘-or-𝟙 pe (P , i , f , g) = 𝟘-elim (φ u)
 where
  u : ¬ P
  u p = g l
   where
    l : P ＝ 𝟙
    l = pe i 𝟙-is-prop unique-to-𝟙 (λ _ → p)

  φ : ¬¬ P
  φ u = f l
   where
    l : P ＝ 𝟘
    l = pe i 𝟘-is-prop (λ p → 𝟘-elim (u p)) 𝟘-elim

\end{code}

Notice how we used 𝟘-elim above to coerce a hypothetical value in 𝟘
{𝓤₀}, arising from negation, to a value in 𝟘 {𝓤}. Otherwise "u" would
have sufficed in place of "λ p → 𝟘-elim (u p)". The same technique is
used in the following construction.

\begin{code}

𝟘-is-not-𝟙 : 𝟘 {𝓤} ≠ 𝟙 {𝓤}
𝟘-is-not-𝟙 p = 𝟘-elim (Idtofun (p ⁻¹) ⋆)

\end{code}

Unique existence.

\begin{code}

∃! : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
∃! A = is-singleton (Σ A)

existsUnique : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
existsUnique X A = ∃! A

syntax existsUnique X (λ x → b) = ∃! x ꞉ X , b

witness-uniqueness : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                   → (∃! x ꞉ X , A x)
                   → (x y : X) → A x → A y → x ＝ y
witness-uniqueness A e x y a b = ap pr₁ (singletons-are-props e (x , a) (y , b))

infixr -1 existsUnique

∃!-intro : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X) (a : A x)
         → ((σ : Σ A) → (x , a) ＝ σ)
         → ∃! A
∃!-intro x a o = (x , a) , o

∃!-witness : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ∃! A → X
∃!-witness ((x , a) , o) = x

∃!-is-witness : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                (u : ∃! A)
              → A (∃!-witness u)
∃!-is-witness ((x , a) , o) = a

description : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ∃! A → Σ A
description (σ , o) = σ

∃!-uniqueness' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                 (u : ∃! A)
               → (σ : Σ A)
               → description u ＝ σ
∃!-uniqueness' ((x , a) , o) = o

∃!-uniqueness : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                (u : ∃! A)
              → (x : X)
                (a : A x)
              → description u ＝ (x , a)
∃!-uniqueness u x a = ∃!-uniqueness' u (x , a)

∃!-uniqueness'' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                  (u : ∃! A)
                → (σ ω : Σ A)
                → σ ＝ ω
∃!-uniqueness'' u σ ω = ∃!-uniqueness' u σ ⁻¹ ∙ ∃!-uniqueness' u ω

\end{code}

Added 5 March 2020 by Tom de Jong.

\begin{code}

+-is-prop : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
          → is-prop X
          → is-prop Y
          → (X → ¬ Y)
          → is-prop (X + Y)
+-is-prop i j f (inl x) (inl x') = ap inl (i x x')
+-is-prop i j f (inl x) (inr y) = 𝟘-induction (f x y)
+-is-prop i j f (inr y) (inl x) = 𝟘-induction (f x y)
+-is-prop i j f (inr y) (inr y') = ap inr (j y y')

+-is-prop' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
           → is-prop X
           → is-prop Y
           → (Y → ¬ X)
           → is-prop (X + Y)
+-is-prop' {𝓤} {𝓥} {X} {Y} i j f = +-is-prop i j (λ y x → f x y)

\end{code}

Added 16th June 2020 by Martin Escardo. (Should have added this ages
ago to avoid boiler-plate code.)

\begin{code}

×₃-is-prop : {𝓥₀ 𝓥₁ 𝓥₂ : Universe}
             {X₀ : 𝓥₀ ̇ } {X₁ : 𝓥₁ ̇ } {X₂ : 𝓥₂ ̇ }
           → is-prop X₀ → is-prop X₁ → is-prop X₂ → is-prop (X₀ × X₁ × X₂)
×₃-is-prop i₀ i₁ i₂ = ×-is-prop i₀ (×-is-prop i₁ i₂)

×₄-is-prop : {𝓥₀ 𝓥₁ 𝓥₂ 𝓥₃ : Universe}
             {X₀ : 𝓥₀ ̇ } {X₁ : 𝓥₁ ̇ } {X₂ : 𝓥₂ ̇ } {X₃ : 𝓥₃ ̇ }
           → is-prop X₀
           → is-prop X₁
           → is-prop X₂
           → is-prop X₃
           → is-prop (X₀ × X₁ × X₂ × X₃)
×₄-is-prop i₀ i₁ i₂ i₃ = ×-is-prop i₀ (×₃-is-prop i₁ i₂ i₃)

×₅-is-prop : {𝓥₀ 𝓥₁ 𝓥₂ 𝓥₃ 𝓥₄ : Universe}
             {X₀ : 𝓥₀ ̇ } {X₁ : 𝓥₁ ̇ } {X₂ : 𝓥₂ ̇ } {X₃ : 𝓥₃ ̇ } {X₄ : 𝓥₄ ̇ }
           → is-prop X₀
           → is-prop X₁
           → is-prop X₂
           → is-prop X₃
           → is-prop X₄
           → is-prop (X₀ × X₁ × X₂ × X₃ × X₄)
×₅-is-prop i₀ i₁ i₂ i₃ i₄ = ×-is-prop i₀ (×₄-is-prop i₁ i₂ i₃ i₄)

×₆-is-prop : {𝓥₀ 𝓥₁ 𝓥₂ 𝓥₃ 𝓥₄ 𝓥₅ : Universe}
             {X₀ : 𝓥₀ ̇ } {X₁ : 𝓥₁ ̇ } {X₂ : 𝓥₂ ̇ } {X₃ : 𝓥₃ ̇ } {X₄ : 𝓥₄ ̇ } {X₅ : 𝓥₅ ̇ }
           → is-prop X₀
           → is-prop X₁
           → is-prop X₂
           → is-prop X₃
           → is-prop X₄
           → is-prop X₅
           → is-prop (X₀ × X₁ × X₂ × X₃ × X₄ × X₅)
×₆-is-prop i₀ i₁ i₂ i₃ i₄ i₅ = ×-is-prop i₀ (×₅-is-prop i₁ i₂ i₃ i₄ i₅)

×₇-is-prop : {𝓥₀ 𝓥₁ 𝓥₂ 𝓥₃ 𝓥₄ 𝓥₅ 𝓥₆ : Universe}
             {X₀ : 𝓥₀ ̇ } {X₁ : 𝓥₁ ̇ } {X₂ : 𝓥₂ ̇ } {X₃ : 𝓥₃ ̇ } {X₄ : 𝓥₄ ̇ } {X₅ : 𝓥₅ ̇ } {X₆ : 𝓥₆ ̇ }
           → is-prop X₀
           → is-prop X₁
           → is-prop X₂
           → is-prop X₃
           → is-prop X₄
           → is-prop X₅
           → is-prop X₆
           → is-prop (X₀ × X₁ × X₂ × X₃ × X₄ × X₅ × X₆)
×₇-is-prop i₀ i₁ i₂ i₃ i₄ i₅ i₆ = ×-is-prop i₀ (×₆-is-prop i₁ i₂ i₃ i₄ i₅ i₆)

×₈-is-prop : {𝓥₀ 𝓥₁ 𝓥₂ 𝓥₃ 𝓥₄ 𝓥₅ 𝓥₆ 𝓥₇ : Universe}
             {X₀ : 𝓥₀ ̇ } {X₁ : 𝓥₁ ̇ } {X₂ : 𝓥₂ ̇ } {X₃ : 𝓥₃ ̇ } {X₄ : 𝓥₄ ̇ } {X₅ : 𝓥₅ ̇ } {X₆ : 𝓥₆ ̇ } {X₇ : 𝓥₇ ̇ }
           → is-prop X₀
           → is-prop X₁
           → is-prop X₂
           → is-prop X₃
           → is-prop X₄
           → is-prop X₅
           → is-prop X₆
           → is-prop X₇ → is-prop (X₀ × X₁ × X₂ × X₃ × X₄ × X₅ × X₆ × X₇)
×₈-is-prop i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ = ×-is-prop i₀ (×₇-is-prop i₁ i₂ i₃ i₄ i₅ i₆ i₇)

\end{code}
