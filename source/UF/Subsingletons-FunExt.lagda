Martin Escardo

In univalent logic, as opposed to Curry-Howard logic, a proposition is
a prop or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

About (sub)singletons using function extensionality.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Subsingletons-FunExt where

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.Hedberg
open import UF.Retracts
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-Properties

Π-is-prop : funext 𝓤 𝓥
          → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
          → ((x : X) → is-prop (A x))
          → is-prop (Π A)
Π-is-prop fe i f g = dfunext fe (λ x → i x (f x) (g x))

Π-is-prop' : funext 𝓤 𝓥
           → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
           → ((x : X) → is-prop (A x))
           → is-prop ({x : X} → A x)
Π-is-prop' fe {X} {A} i = retract-of-prop retr (Π-is-prop fe i)
 where
  retr : retract ({x : X} → A x) of Π A
  retr = (λ f {x} → f x) , (λ g x → g {x}) , (λ x → refl)

Π-is-singleton : funext 𝓤 𝓥
               → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
               → ((x : X) → is-singleton (A x))
               → is-singleton (Π A)
Π-is-singleton fe i = (λ x → pr₁ (i x)) ,
                      (λ f → dfunext fe (λ x → pr₂ (i x) (f x)))

being-prop-is-prop : {X : 𝓤 ̇ }
                   → funext 𝓤 𝓤
                   → is-prop (is-prop X)
being-prop-is-prop {𝓤} {X} fe f g = c₁
 where
  l : is-set X
  l = props-are-sets f

  c : (x y : X) → f x y ＝ g x y
  c x y = l (f x y) (g x y)

  c₀ : (x : X) → f x ＝ g x
  c₀ x = dfunext fe (c x)

  c₁ : f ＝ g
  c₁  = dfunext fe c₀

↔-is-prop : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
          → funext 𝓤 𝓥
          → funext 𝓥 𝓤
          → is-prop X
          → is-prop Y
          → is-prop (X ↔ Y)
↔-is-prop fe fe' X-is-prop Y-is-prop = ×-is-prop
                                       (Π-is-prop fe  (λ _ → Y-is-prop))
                                       (Π-is-prop fe' (λ _ → X-is-prop))

\end{code}

The following means that propositions are h-isolated elements of type
universes:

\begin{code}

identifications-with-props-are-props : propext 𝓤
                                     → funext 𝓤 𝓤
                                     → (P : 𝓤 ̇ )
                                     → is-prop P
                                     → (X : 𝓤 ̇ ) → is-prop (X ＝ P)
identifications-with-props-are-props {𝓤} pe fe P i = γ
 where
  f : (X : 𝓤 ̇ ) → X ＝ P → is-prop X × (X ↔ P)
  f X refl = i , (id , id)

  g : (X : 𝓤 ̇ ) → is-prop X × (X ↔ P) → X ＝ P
  g X (l , φ , γ) = pe l i φ γ

  j : (X : 𝓤 ̇ ) → is-prop (is-prop X × (X ↔ P))
  j X = ×-prop-criterion ( (λ _ → being-prop-is-prop fe)
                         , (λ l → ↔-is-prop fe fe l i))

  k : (X : 𝓤 ̇ ) → wconstant (g X ∘ f X)
  k X p q = ap (g X) (j X (f X p) (f X q))

  γ : (X : 𝓤 ̇ ) → is-prop (X ＝ P)
  γ = local-hedberg' P (λ X → g X ∘ f X , k X)

being-singleton-is-prop : funext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-prop (is-singleton X)
being-singleton-is-prop fe {X} (x , φ) (y , γ) = δ
 where
  isp : is-prop X
  isp = singletons-are-props (y , γ)

  iss : is-set X
  iss = props-are-sets isp

  δ : x , φ ＝ y , γ
  δ = to-Σ-＝ (φ y , dfunext fe λ z → iss {y} {z} _ _)

∃!-is-prop : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
           → funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
           → is-prop (∃! A)
∃!-is-prop fe = being-singleton-is-prop fe

negations-are-props : {X : 𝓤 ̇ } → funext 𝓤 𝓤₀ → is-prop (¬ X)
negations-are-props fe = Π-is-prop fe (λ x → 𝟘-is-prop)

decidability-of-prop-is-prop : funext 𝓤 𝓤₀
                             → {P : 𝓤 ̇ }
                             → is-prop P
                             → is-prop (P + ¬ P)
decidability-of-prop-is-prop fe₀ i = sum-of-contradictory-props
                                      i
                                      (negations-are-props fe₀)
                                      (λ p u → u p)

empty-types-are-props : {X : 𝓤 ̇ } → ¬ X → is-prop X
empty-types-are-props f x = 𝟘-elim (f x)

equal-𝟘-is-empty : {X : 𝓤 ̇ } → X ＝ 𝟘 → ¬ X
equal-𝟘-is-empty e x = 𝟘-elim (transport id e x)

empty-types-are-＝-𝟘 : funext 𝓤 𝓤₀ → propext 𝓤 → {X : 𝓤 ̇ } → ¬ X → X ＝ 𝟘
empty-types-are-＝-𝟘 fe pe f = pe (empty-types-are-props f)
                                𝟘-is-prop
                                (λ x → 𝟘-elim (f x))
                                𝟘-elim

holds-gives-equal-𝟙 : propext 𝓤 → (P : 𝓤 ̇ ) → is-prop P → P → P ＝ 𝟙
holds-gives-equal-𝟙 pe P i p = pe i 𝟙-is-prop unique-to-𝟙 (λ _ → p)

equal-𝟙-gives-holds : (P : 𝓤 ̇ ) → P ＝ 𝟙 → P
equal-𝟙-gives-holds P r = Idtofun (r ⁻¹) ⋆

not-𝟘-is-𝟙 : funext 𝓤 𝓤₀
           → propext 𝓤
           → (¬ 𝟘) ＝ 𝟙
not-𝟘-is-𝟙 fe pe = pe (negations-are-props fe)
                      𝟙-is-prop
                      (λ _ → ⋆)
                      (λ _ z → 𝟘-elim z)

\end{code}

In the above and in the following, 𝟘-elim is used to coerce from 𝟘 {𝓤}
to 𝟘 {𝓤₀} as this is where negations take values in.

Sometimes it is convenient to work with the type of true propositions,
which is a singleton and hence a subsingleton. But we will leave this
type nameless:

\begin{code}

𝟙-is-true-props-center : funext 𝓤 𝓤
                       → propext 𝓤
                       → (σ : Σ P ꞉ 𝓤 ̇ , is-prop P × P) → (𝟙 , 𝟙-is-prop , ⋆) ＝ σ
𝟙-is-true-props-center fe pe = γ
 where
  φ : ∀ P → is-prop (is-prop P × P)
  φ P (i , p) = ×-is-prop (being-prop-is-prop fe) i (i , p)

  γ : ∀ σ → (𝟙 , 𝟙-is-prop , ⋆) ＝ σ
  γ (P , i , p) = to-subtype-＝ φ s
   where
    s : 𝟙 ＝ P
    s = pe 𝟙-is-prop i (λ _ → p) (λ _ → ⋆)

the-true-props-form-a-singleton-type : funext 𝓤 𝓤
                                     → propext 𝓤
                                     → is-singleton (Σ P ꞉ 𝓤 ̇ , is-prop P × P)
the-true-props-form-a-singleton-type fe pe = (𝟙 , 𝟙-is-prop , ⋆) ,
                                             𝟙-is-true-props-center fe pe

the-true-props-form-a-prop : funext 𝓤 𝓤
                           → propext 𝓤
                           → is-prop (Σ P ꞉ 𝓤 ̇ , is-prop P × P)
the-true-props-form-a-prop fe pe =
 singletons-are-props (the-true-props-form-a-singleton-type fe pe)

\end{code}

Added 16th June 2020. (Should have added this ages ago to avoid
boiler-plate code.)

\begin{code}

Π₂-is-prop : Fun-Ext
           → {X : 𝓤 ̇ }
             {Y : X → 𝓥 ̇ }
             {Z : (x : X) → Y x → 𝓦 ̇ }
           → ((x : X) (y : Y x) → is-prop (Z x y))
           → is-prop ((x : X) (y : Y x) → Z x y)
Π₂-is-prop fe i = Π-is-prop fe (λ x → Π-is-prop fe (i x))

Π₃-is-prop : Fun-Ext
           → {X : 𝓤 ̇ }
             {Y : X → 𝓥 ̇ }
             {Z : (x : X) → Y x → 𝓦 ̇ }
             {T : (x : X) (y : Y x) → Z x y → 𝓣 ̇ }
           → ((x : X) (y : Y x) (z : Z x y) → is-prop (T x y z))
           → is-prop ((x : X) (y : Y x) (z : Z x y) → T x y z)
Π₃-is-prop fe i = Π-is-prop fe (λ x → Π₂-is-prop fe (i x))

Π₄-is-prop : Fun-Ext
           → {𝓥₀ 𝓥₁ 𝓥₂ 𝓥₃ : Universe}
             {A : 𝓤 ̇ }
             {B : A → 𝓥₀ ̇ }
             {C : (a : A) → B a → 𝓥₁ ̇ }
             {D : (a : A) (b : B a) → C a b → 𝓥₂ ̇ }
             {E : (a : A) (b : B a) (c : C a b) → D a b c → 𝓥₃ ̇ }
           → ((a : A) (b : B a) (c : C a b) (d : D a b c) → is-prop (E a b c d))
           → is-prop ((a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d)
Π₄-is-prop fe i = Π-is-prop fe (λ x → Π₃-is-prop fe (i x))

Π₅-is-prop : Fun-Ext
           → {𝓥₀ 𝓥₁ 𝓥₂ 𝓥₃ 𝓥₄ : Universe}
             {A : 𝓤 ̇ }
             {B : A → 𝓥₀ ̇ }
             {C : (a : A) → B a → 𝓥₁ ̇ }
             {D : (a : A) (b : B a) → C a b → 𝓥₂ ̇ }
             {E : (a : A) (b : B a) (c : C a b) → D a b c → 𝓥₃ ̇ }
             {F : (a : A) (b : B a) (c : C a b) (d : D a b c) → E a b c d → 𝓥₄ ̇ }
           → ((a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d) → is-prop (F a b c d e))
           → is-prop ((a : A) (b : B a) (c : C a b) (d : D a b c) (e : E a b c d) → F a b c d e)
Π₅-is-prop fe i = Π-is-prop fe (λ x → Π₄-is-prop fe (i x))

Π₂-is-prop' : Fun-Ext
           → {X : 𝓤 ̇ }
             {Y : X → 𝓥 ̇ }
             {Z : (x : X) → Y x → 𝓦 ̇ }
           → ((x : X) (y : Y x) → is-prop (Z x y))
           → is-prop ({x : X} {y : Y x} → Z x y)
Π₂-is-prop' fe i = Π-is-prop' fe (λ x → Π-is-prop' fe (i x))

\end{code}
