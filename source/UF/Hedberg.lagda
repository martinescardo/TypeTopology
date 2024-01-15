Martin Escardo

Based on

 Kraus, N., Escardó, M., Coquand, T., Altenkirch, T.
 Generalizations of Hedberg’s Theorem.
 In: Hasegawa, M. (eds) Typed Lambda Calculi and Applications.
 TLCA 2013. Lecture Notes in Computer Science, vol 7941.
 Springer, Berlin, Heidelberg.
 https://doi.org/10.1007/978-3-642-38946-7_14

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Hedberg where

open import MLTT.Spartan
open import UF.Base
open import UF.Sets
open import UF.Subsingletons

wconstant : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y) → 𝓤 ⊔ 𝓥 ̇
wconstant f = ∀ x y → f x ＝ f y

wconstant-pre-comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                     (f : X → Y) (g : Y → Z)
                   → wconstant f
                   → wconstant (g ∘ f)
wconstant-pre-comp f g c x x' = ap g (c x x')

wconstant-post-comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                      (f : X → Y) (g : Y → Z)
                    → wconstant g
                    → wconstant (g ∘ f)
wconstant-post-comp f g c x x' = c (f x) (f x')

collapsible : 𝓤 ̇ → 𝓤 ̇
collapsible X = Σ f ꞉ (X → X) , wconstant f

Id-collapsible' : {X : 𝓤 ̇ } → X → 𝓤 ̇

Id-collapsible' x = ∀ {y} → collapsible (x ＝ y)

Id-collapsible : 𝓤 ̇ → 𝓤 ̇
Id-collapsible X = {x : X} → Id-collapsible' x

h-isolated-points-are-Id-collapsible : {X : 𝓤 ̇ } {x : X}
                                     → is-h-isolated x
                                     → Id-collapsible' x
h-isolated-points-are-Id-collapsible h = id , h

sets-are-Id-collapsible : {X : 𝓤 ̇ } → is-set X → Id-collapsible X
sets-are-Id-collapsible u = (id , u)

local-hedberg : {X : 𝓤 ̇ } (x : X)
              → ((y : X) → collapsible (x ＝ y))
              → (y : X) → is-prop (x ＝ y)
local-hedberg {𝓤} {X} x pc y p q =
 p                    ＝⟨ c y p ⟩
 f x refl ⁻¹ ∙ f y p  ＝⟨ ap (λ - → (f x refl)⁻¹ ∙ -) (κ y p q) ⟩
 f x refl ⁻¹ ∙ f y q  ＝⟨ (c y q)⁻¹ ⟩
 q                    ∎
 where
  f : (y : X) → x ＝ y → x ＝ y
  f y = pr₁ (pc y)

  κ : (y : X) (p q : x ＝ y) → f y p ＝ f y q
  κ y = pr₂ (pc y)

  c : (y : X) (r : x ＝ y) → r ＝ (f x refl)⁻¹ ∙ f y r
  c _ refl = sym-is-inverse (f x refl)

Id-collapsibles-are-h-isolated : {X : 𝓤 ̇ } (x : X)
                               → Id-collapsible' x
                               → is-h-isolated x
Id-collapsibles-are-h-isolated x pc {y} p q =
 local-hedberg x (λ y → (pr₁ (pc {y})) , (pr₂ (pc {y}))) y p q

Id-collapsibles-are-sets : {X : 𝓤 ̇ } → Id-collapsible X → is-set X
Id-collapsibles-are-sets pc {x} = Id-collapsibles-are-h-isolated x pc

\end{code}

Here is an example. Any type that admits a prop-valued, reflexive and
antisymmetric relation is a set.

\begin{code}

type-with-prop-valued-refl-antisym-rel-is-set : {X : 𝓤 ̇ }
                                              → (_≤_ : X → X → 𝓥 ̇ )
                                              → ((x y : X) → is-prop (x ≤ y))
                                              → ((x : X) → x ≤ x)
                                              → ((x y : X) → x ≤ y → y ≤ x → x ＝ y)
                                              → is-set X
type-with-prop-valued-refl-antisym-rel-is-set
 {𝓤} {𝓥} {X} _≤_ ≤-prop-valued ≤-refl ≤-anti = γ
 where
  α : ∀ {x y} (l l' : x ≤ y) (m m' : y ≤ x) → ≤-anti x y l m ＝ ≤-anti x y l' m'
  α {x} {y} l l' m m' = ap₂ (≤-anti x y)
                            (≤-prop-valued x y l l')
                            (≤-prop-valued y x m m')

  g : ∀ {x y} → x ＝ y → x ≤ y
  g {x} p = transport (x ≤_) p (≤-refl x)

  h : ∀ {x y} → x ＝ y → y ≤ x
  h p = g (p ⁻¹)

  f : ∀ {x y} → x ＝ y → x ＝ y
  f {x} {y} p = ≤-anti x y (g p) (h p)

  κ : ∀ {x y} p q → f {x} {y} p ＝ f {x} {y} q
  κ p q = α (g p) (g q) (h p) (h q)

  γ : is-set X
  γ = Id-collapsibles-are-sets (f , κ)

\end{code}

We also need the following symmetrical version of local Hedberg, which
can be proved by reduction to the above (using the fact that
collapsible types are closed under equivalence), but at this point we
don't have the machinery at our disposal (which is developed in
modules that depend on this one), and hence we prove it directly by
symmetrizing the proof.

\begin{code}

local-hedberg' : {X : 𝓤 ̇ } (x : X)
               → ((y : X) → collapsible (y ＝ x))
               → (y : X) → is-prop (y ＝ x)
local-hedberg' {𝓤} {X} x pc y p q =
  p                     ＝⟨ c y p ⟩
  f y p ∙ (f x refl)⁻¹  ＝⟨  ap (λ - → - ∙ (f x refl)⁻¹) (κ y p q) ⟩
  f y q ∙ (f x refl)⁻¹  ＝⟨ (c y q)⁻¹ ⟩
  q                     ∎
 where
  f : (y : X) → y ＝ x → y ＝ x
  f y = pr₁ (pc y)

  κ : (y : X) (p q : y ＝ x) → f y p ＝ f y q
  κ y = pr₂ (pc y)

  c : (y : X) (r : y ＝ x) → r ＝  (f y r) ∙ (f x refl)⁻¹
  c _ refl = sym-is-inverse' (f x refl)

\end{code}
