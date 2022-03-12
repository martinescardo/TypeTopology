Martin Escardo

In univalent logic, as opposed to Curry-Howard logic, a proposition is
a subsingleton or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF-Subsingletons where

open import SpartanMLTT
open import Unit-Properties

open import Plus-Properties
open import UF-Base

is-prop : 𝓤 ̇ → 𝓤 ̇
is-prop X = (x y : X) → x ≡ y

\end{code}

And of course we could adopt a terminology borrowed from topos logic:

\begin{code}

is-truth-value is-subsingleton : 𝓤 ̇ → 𝓤 ̇
is-truth-value  = is-prop
is-subsingleton = is-prop

\end{code}

\begin{code}

Σ-is-prop : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
          → is-prop X → ((x : X) → is-prop (A x)) → is-prop (Σ A)
Σ-is-prop {𝓤} {𝓥} {X} {A} i j (x , a) (y , b) =
  to-Σ-≡ (i x y , j y (transport A (i x y) a) b)

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
is-central X c = (x : X) → c ≡ x

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
singletons-are-props (c , φ) x y = x ≡⟨ (φ x) ⁻¹ ⟩
                                   c ≡⟨ φ y ⟩
                                   y ∎

prop-criterion' : {X : 𝓤 ̇ } → (X → is-singleton X) → is-prop X
prop-criterion' φ x = singletons-are-props (φ x) x

prop-criterion : {X : 𝓤 ̇ } → (X → is-prop X) → is-prop X
prop-criterion φ x = φ x x

pointed-props-are-singletons : {X : 𝓤 ̇ } → X → is-prop X → is-singleton X
pointed-props-are-singletons x h = x , h x

\end{code}

The two prototypical propositions:

\begin{code}

𝟘-is-prop : is-prop (𝟘 {𝓤})
𝟘-is-prop {𝓤} x y = unique-from-𝟘 {𝓤} {𝓤} x

𝟙-is-prop : is-prop (𝟙 {𝓤})
𝟙-is-prop {𝓤} ⋆ ⋆ = refl {𝓤}

\end{code}

A type is a set if all its identity types are subsingletons. In other
words, sets are types for which equality is a proposition (rather than
data or structure).

\begin{code}

is-h-isolated : {X : 𝓤 ̇ } (x : X) → 𝓤 ̇
is-h-isolated x = ∀ {y} → is-prop (x ≡ y)

is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = {x : X} → is-h-isolated x

hSet : (𝓤 : Universe) → 𝓤 ⁺ ̇
hSet 𝓤 = Σ A ꞉ 𝓤 ̇ , is-set A

underlying-set : hSet 𝓤 → 𝓤 ̇
underlying-set = pr₁

𝟘-is-set : is-set (𝟘 {𝓤})
𝟘-is-set {𝓤} {x} = 𝟘-elim x

refl-is-set : (X : 𝓤 ̇ )
            → ((x : X) (p : x ≡ x) → p ≡ refl)
            → is-set X
refl-is-set X r {x} {.x} p refl = r x p

\end{code}

We now consider some machinery for dealing with the above notions,
using weakly, or wildly, constant maps:

\begin{code}

wconstant : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y) → 𝓤 ⊔ 𝓥 ̇
wconstant f = ∀ x y → f x ≡ f y

wconstant-pre-comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y) (g : Y → Z)
                   → wconstant f → wconstant (g ∘ f)
wconstant-pre-comp f g c x x' = ap g (c x x')

wconstant-post-comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y) (g : Y → Z)
                    → wconstant g → wconstant (g ∘ f)
wconstant-post-comp f g c x x' = c (f x) (f x')

collapsible : 𝓤 ̇ → 𝓤 ̇
collapsible X = Σ f ꞉ (X → X) , wconstant f

Id-collapsible' : {X : 𝓤 ̇ } → X → 𝓤 ̇
Id-collapsible' x = ∀ {y} → collapsible (x ≡ y)

Id-collapsible : 𝓤 ̇ → 𝓤 ̇
Id-collapsible X = {x : X} → Id-collapsible' x

h-isolated-points-are-Id-collapsible : {X : 𝓤 ̇ } {x : X} → is-h-isolated x → Id-collapsible' x
h-isolated-points-are-Id-collapsible h = id , h

sets-are-Id-collapsible : {X : 𝓤 ̇ } → is-set X → Id-collapsible X
sets-are-Id-collapsible u = (id , u)

local-hedberg : {X : 𝓤 ̇ } (x : X)
              → ((y : X) → collapsible (x ≡ y))
              → (y : X) → is-prop (x ≡ y)
local-hedberg {𝓤} {X} x pc y p q =
 p                    ≡⟨ c y p ⟩
 f x refl ⁻¹ ∙ f y p  ≡⟨ ap (λ - → (f x refl)⁻¹ ∙ -) (κ y p q) ⟩
 f x refl ⁻¹ ∙ f y q  ≡⟨ (c y q)⁻¹ ⟩
 q                    ∎
 where
  f : (y : X) → x ≡ y → x ≡ y
  f y = pr₁ (pc y)
  κ : (y : X) (p q : x ≡ y) → f y p ≡ f y q
  κ y = pr₂ (pc y)
  c : (y : X) (r : x ≡ y) → r ≡ (f x refl)⁻¹ ∙ f y r
  c _ refl = sym-is-inverse (f x refl)

Id-collapsibles-are-h-isolated : {X : 𝓤 ̇ } (x : X) → Id-collapsible' x → is-h-isolated x
Id-collapsibles-are-h-isolated x pc {y} p q = local-hedberg x (λ y → (pr₁ (pc {y})) , (pr₂ (pc {y}))) y p q

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
                                              → ((x y : X) → x ≤ y → y ≤ x → x ≡ y)
                                              → is-set X
type-with-prop-valued-refl-antisym-rel-is-set {𝓤} {𝓥} {X} _≤_ ≤-prop-valued ≤-refl ≤-anti = γ
 where
  α : ∀ {x y} (l l' : x ≤ y) (m m' : y ≤ x) → ≤-anti x y l m ≡ ≤-anti x y l' m'
  α {x} {y} l l' m m' = ap₂ (≤-anti x y)
                            (≤-prop-valued x y l l')
                            (≤-prop-valued y x m m')

  g : ∀ {x y} → x ≡ y → x ≤ y
  g {x} p = transport (x ≤_) p (≤-refl x)

  h : ∀ {x y} → x ≡ y → y ≤ x
  h p = g (p ⁻¹)

  f : ∀ {x y} → x ≡ y → x ≡ y
  f {x} {y} p = ≤-anti x y (g p) (h p)

  κ : ∀ {x y} p q → f {x} {y} p ≡ f {x} {y} q
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
               → ((y : X) → collapsible (y ≡ x))
               → (y : X) → is-prop (y ≡ x)
local-hedberg' {𝓤} {X} x pc y p q =
  p                     ≡⟨ c y p ⟩
  f y p ∙ (f x refl)⁻¹  ≡⟨  ap (λ - → - ∙ (f x refl)⁻¹) (κ y p q) ⟩
  f y q ∙ (f x refl)⁻¹  ≡⟨ (c y q)⁻¹ ⟩
  q                     ∎
 where
  f : (y : X) → y ≡ x → y ≡ x
  f y = pr₁ (pc y)
  κ : (y : X) (p q : y ≡ x) → f y p ≡ f y q
  κ y = pr₂ (pc y)
  c : (y : X) (r : y ≡ x) → r ≡  (f y r) ∙ (f x refl)⁻¹
  c _ refl = sym-is-inverse' (f x refl)

props-are-Id-collapsible : {X : 𝓤 ̇ } → is-prop X → Id-collapsible X
props-are-Id-collapsible h {x} {y} = (λ p → h x y) , (λ p q → refl)

props-are-sets : {X : 𝓤 ̇ } → is-prop X → is-set X
props-are-sets h = Id-collapsibles-are-sets (props-are-Id-collapsible h)

𝟘-is-collapsible : collapsible (𝟘 {𝓤})
𝟘-is-collapsible {𝓤} = id , (λ x y → 𝟘-elim y)

pointed-types-are-collapsible : {X : 𝓤 ̇ } → X → collapsible X
pointed-types-are-collapsible x = (λ y → x) , (λ y y' → refl)

\end{code}

Under Curry-Howard, the function type X → 𝟘 is understood as the
negation of X when X is viewed as a proposition. But when X is
understood as a mathematical object, inhabiting the type X → 𝟘 amounts
to showing that X is empty. (In fact, assuming univalence, defined
below, the type X → 𝟘 is equivalent to the type X ≡ 𝟘
(written (X → 𝟘) ≃ (X ≡ 𝟘)).)

\begin{code}

empty-types-are-collapsible : {X : 𝓤 ̇ } → is-empty X → collapsible X
empty-types-are-collapsible u = (id , (λ x x' → unique-from-𝟘 (u x)))

𝟘-is-collapsible' : collapsible 𝟘
𝟘-is-collapsible' = empty-types-are-collapsible id

singleton-type : {X : 𝓤 ̇ } (x : X) → 𝓤 ̇
singleton-type x = Σ y ꞉ type-of x , x ≡ y

singleton-center : {X : 𝓤 ̇ } (x : X) → singleton-type x
singleton-center x = (x , refl)

singleton-types-are-singletons'' : {X : 𝓤 ̇ } {x x' : X} (r : x ≡ x') → singleton-center x ≡ (x' , r)
singleton-types-are-singletons'' {𝓤} {X} = J A (λ x → refl)
 where
  A : (x x' : X) → x ≡ x' → 𝓤 ̇
  A x x' r = singleton-center x ≡[ Σ x' ꞉ X , x ≡ x' ] (x' , r)

singleton-types-are-singletons : {X : 𝓤 ̇ } (x₀ : X) → is-singleton (singleton-type x₀)
singleton-types-are-singletons x₀ = singleton-center x₀ , (λ t → singleton-types-are-singletons'' (pr₂ t))

singleton-types-are-singletons' : {X : 𝓤 ̇ } {x : X} → is-central (singleton-type x) (x , refl)
singleton-types-are-singletons' {𝓤} {X} (y , refl) = refl

singleton-types-are-props : {X : 𝓤 ̇ } (x : X) → is-prop (singleton-type x)
singleton-types-are-props x = singletons-are-props (singleton-types-are-singletons x)

singleton-type' : {X : 𝓤 ̇ } → X → 𝓤 ̇
singleton-type' x = Σ y ꞉ type-of x , y ≡ x

singleton'-center : {X : 𝓤 ̇ } (x : X) → singleton-type' x
singleton'-center x = (x , refl)

×-prop-criterion-necessity : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                           → is-prop (X × Y) → (Y → is-prop X) × (X → is-prop Y)
×-prop-criterion-necessity i = (λ y x x' → ap pr₁ (i (x , y) (x' , y ))) ,
                               (λ x y y' → ap pr₂ (i (x , y) (x  , y')))

×-prop-criterion : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → (Y → is-prop X) × (X → is-prop Y) → is-prop (X × Y)
×-prop-criterion (i , j) (x , y) (x' , y') = to-Σ-≡ (i y x x' , j x _ _)

×-𝟘-is-prop : {X : 𝓤 ̇ } → is-prop (X × 𝟘 {𝓥})
×-𝟘-is-prop (x , z) _ = 𝟘-elim z

𝟘-×-is-prop : {X : 𝓤 ̇ } → is-prop (𝟘 {𝓥} × X)
𝟘-×-is-prop (z , x) _ = 𝟘-elim z

×-is-prop : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
          → is-prop X → is-prop Y → is-prop (X × Y)
×-is-prop i j = ×-prop-criterion ((λ _ → i) , (λ _ → j))

to-subtype-≡ : {X : 𝓦 ̇ } {A : X → 𝓥 ̇ }
               {x y : X} {a : A x} {b : A y}
             → ((x : X) → is-prop (A x))
             → x ≡ y
             → (x , a) ≡ (y , b)
to-subtype-≡ {𝓤} {𝓥} {X} {A} {x} {y} {a} {b} s p = to-Σ-≡ (p , s y (transport A p a) b)

subtype-of-prop-is-prop : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
                          → left-cancellable m → is-prop Y → is-prop X
subtype-of-prop-is-prop {𝓤} {𝓥} {X} m lc i x x' = lc (i (m x) (m x'))

subtypes-of-sets-are-sets : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
                          → left-cancellable m → is-set Y → is-set X
subtypes-of-sets-are-sets {𝓤} {𝓥} {X} m i h = Id-collapsibles-are-sets (f , g)
 where
  f : {x x' : X} → x ≡ x' → x ≡ x'
  f r = i (ap m r)
  g : {x x' : X} (r s : x ≡ x') → f r ≡ f s
  g r s = ap i (h (ap m r) (ap m s))

pr₁-lc : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → ({x : X} → is-prop (Y x))
       → left-cancellable (pr₁ {𝓤} {𝓥} {X} {Y})
pr₁-lc f p = to-Σ-≡ (p , (f _ _))

subsets-of-sets-are-sets : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
                         → is-set X
                         → ({x : X} → is-prop (Y x))
                         → is-set (Σ x ꞉ X , Y x)
subsets-of-sets-are-sets X Y h p = subtypes-of-sets-are-sets pr₁ (pr₁-lc p) h

inl-lc-is-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x x' : X} → (p : inl {𝓤} {𝓥} {X} {Y} x ≡ inl x') → p ≡ ap inl (inl-lc p)
inl-lc-is-section refl = refl

inr-lc-is-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {y y' : Y} → (p : inr {𝓤} {𝓥} {X} {Y} y ≡ inr y') → p ≡ ap inr (inr-lc p)
inr-lc-is-section refl = refl

+-is-set : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → is-set X → is-set Y → is-set (X + Y)
+-is-set X Y i j {inl x} {inl x'} p q = inl-lc-is-section p ∙ r ∙ (inl-lc-is-section q)⁻¹
 where
  r : ap inl (inl-lc p) ≡ ap inl (inl-lc q)
  r = ap (ap inl) (i (inl-lc p) (inl-lc q))
+-is-set X Y i j {inl x} {inr y} p q = 𝟘-elim (+disjoint  p)
+-is-set X Y i j {inr y} {inl x} p q = 𝟘-elim (+disjoint' p)
+-is-set X Y i j {inr y} {inr y'} p q = inr-lc-is-section p ∙ r ∙ (inr-lc-is-section q)⁻¹
 where
  r : ap inr (inr-lc p) ≡ ap inr (inr-lc q)
  r = ap (ap inr) (j (inr-lc p) (inr-lc q))

×-is-set : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → is-set X → is-set Y → is-set (X × Y)
×-is-set i j {(x , y)} {(x' , y')} p q =
 p            ≡⟨ tofrom-×-≡ p ⟩
 to-×-≡ p₀ p₁ ≡⟨ ap₂ (λ -₀ -₁ → to-×-≡ -₀ -₁) (i p₀ q₀) (j p₁ q₁) ⟩
 to-×-≡ q₀ q₁ ≡⟨ (tofrom-×-≡ q)⁻¹ ⟩
 q            ∎ where
  p₀ : x ≡ x'
  p₀ = pr₁ (from-×-≡' p)
  p₁ : y ≡ y'
  p₁ = pr₂ (from-×-≡' p)
  q₀ : x ≡ x'
  q₀ = pr₁ (from-×-≡' q)
  q₁ : y ≡ y'
  q₁ = pr₂ (from-×-≡' q)

\end{code}

Formulation of the K axiom for a universe U.

\begin{code}

K-axiom : ∀ 𝓤 → 𝓤 ⁺ ̇
K-axiom 𝓤 = (X : 𝓤 ̇ ) → is-set X

\end{code}

Formulation of propositional extensionality:

\begin{code}

propext : ∀ 𝓤 → 𝓤 ⁺ ̇
propext 𝓤 = {P Q : 𝓤 ̇ } → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ≡ Q

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
                           → is-prop P → is-prop Q → (P → Q → 𝟘 {𝓦}) → is-prop (P + Q)
sum-of-contradictory-props {𝓤} {𝓥} {𝓦} {P} {Q} i j f = γ
 where
  γ : (x y : P + Q) → x ≡ y
  γ (inl p) (inl p') = ap inl (i p p')
  γ (inl p) (inr q)  = 𝟘-elim {𝓤 ⊔ 𝓥} {𝓦} (f p q)
  γ (inr q) (inl p)  = 𝟘-elim (f p q)
  γ (inr q) (inr q') = ap inr (j q q')

\end{code}

Without assuming excluded middle, we have that there are no truth
values other than 𝟘 and 𝟙:

\begin{code}

no-props-other-than-𝟘-or-𝟙 : propext 𝓤 → ¬ (Σ P ꞉ 𝓤 ̇ , is-prop P × (P ≢ 𝟘) × (P ≢ 𝟙))
no-props-other-than-𝟘-or-𝟙 pe (P , i , f , g) = 𝟘-elim (φ u)
 where
   u : ¬ P
   u p = g l
     where
       l : P ≡ 𝟙
       l = pe i 𝟙-is-prop unique-to-𝟙 (λ _ → p)
   φ : ¬¬ P
   φ u = f l
     where
       l : P ≡ 𝟘
       l = pe i 𝟘-is-prop (λ p → 𝟘-elim (u p)) 𝟘-elim

\end{code}

Notice how we used 𝟘-elim above to coerce a hypothetical value in 𝟘
{𝓤₀}, arising from negation, to a value in 𝟘 {𝓤}. Otherwise "u" would
have sufficed in place of "λ p → 𝟘-elim (u p)". The same technique is
used in the following construction.

\begin{code}

𝟘-is-not-𝟙 : 𝟘 {𝓤} ≢ 𝟙 {𝓤}
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
                   → (x y : X) → A x → A y → x ≡ y
witness-uniqueness A e x y a b = ap pr₁ (singletons-are-props e (x , a) (y , b))

infixr -1 existsUnique

∃!-intro : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X) (a : A x) → ((σ : Σ A) → (x , a) ≡ σ) → ∃! A
∃!-intro x a o = (x , a) , o

∃!-witness : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ∃! A → X
∃!-witness ((x , a) , o) = x

∃!-is-witness : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (u : ∃! A) → A (∃!-witness u)
∃!-is-witness ((x , a) , o) = a

description : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ∃! A → Σ A
description (σ , o) = σ

∃!-uniqueness' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (u : ∃! A) → (σ : Σ A) → description u ≡ σ
∃!-uniqueness' ((x , a) , o) = o

∃!-uniqueness : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (u : ∃! A) → (x : X) (a : A x) → description u ≡ (x , a)
∃!-uniqueness u x a = ∃!-uniqueness' u (x , a)

∃!-uniqueness'' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (u : ∃! A) → (σ ω : Σ A) → σ ≡ ω
∃!-uniqueness'' u σ ω = ∃!-uniqueness' u σ ⁻¹ ∙ ∃!-uniqueness' u ω

\end{code}

Added 5 March 2020 by Tom de Jong.

\begin{code}

+-is-prop : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
          → is-prop X → is-prop Y
          → (X → ¬ Y)
          → is-prop (X + Y)
+-is-prop i j f (inl x) (inl x') = ap inl (i x x')
+-is-prop i j f (inl x) (inr y) = 𝟘-induction (f x y)
+-is-prop i j f (inr y) (inl x) = 𝟘-induction (f x y)
+-is-prop i j f (inr y) (inr y') = ap inr (j y y')

+-is-prop' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
           → is-prop X → is-prop Y
           → (Y → ¬ X)
           → is-prop (X + Y)
+-is-prop' {𝓤} {𝓥} {X} {Y} i j f = +-is-prop i j (λ y x → f x y)

\end{code}

Added 16th June 2020 by Martin Escardo. (Should have added this ages ago to avoid boiler-plate code.)

\begin{code}

×₃-is-prop : {𝓥₀ 𝓥₁ 𝓥₂ : Universe}
             {X₀ : 𝓥₀ ̇ } {X₁ : 𝓥₁ ̇ } {X₂ : 𝓥₂ ̇ }
           → is-prop X₀ → is-prop X₁ → is-prop X₂ → is-prop (X₀ × X₁ × X₂)
×₃-is-prop i₀ i₁ i₂ = ×-is-prop i₀ (×-is-prop i₁ i₂)

×₄-is-prop : {𝓥₀ 𝓥₁ 𝓥₂ 𝓥₃ : Universe}
             {X₀ : 𝓥₀ ̇ } {X₁ : 𝓥₁ ̇ } {X₂ : 𝓥₂ ̇ } {X₃ : 𝓥₃ ̇ }
           → is-prop X₀ → is-prop X₁ → is-prop X₂ → is-prop X₃ → is-prop (X₀ × X₁ × X₂ × X₃)
×₄-is-prop i₀ i₁ i₂ i₃ = ×-is-prop i₀ (×₃-is-prop i₁ i₂ i₃)

×₅-is-prop : {𝓥₀ 𝓥₁ 𝓥₂ 𝓥₃ 𝓥₄ : Universe}
             {X₀ : 𝓥₀ ̇ } {X₁ : 𝓥₁ ̇ } {X₂ : 𝓥₂ ̇ } {X₃ : 𝓥₃ ̇ } {X₄ : 𝓥₄ ̇ }
           → is-prop X₀ → is-prop X₁ → is-prop X₂ → is-prop X₃ → is-prop X₄ → is-prop (X₀ × X₁ × X₂ × X₃ × X₄)
×₅-is-prop i₀ i₁ i₂ i₃ i₄ = ×-is-prop i₀ (×₄-is-prop i₁ i₂ i₃ i₄)

×₆-is-prop : {𝓥₀ 𝓥₁ 𝓥₂ 𝓥₃ 𝓥₄ 𝓥₅ : Universe}
             {X₀ : 𝓥₀ ̇ } {X₁ : 𝓥₁ ̇ } {X₂ : 𝓥₂ ̇ } {X₃ : 𝓥₃ ̇ } {X₄ : 𝓥₄ ̇ } {X₅ : 𝓥₅ ̇ }
           → is-prop X₀ → is-prop X₁ → is-prop X₂ → is-prop X₃ → is-prop X₄ → is-prop X₅ → is-prop (X₀ × X₁ × X₂ × X₃ × X₄ × X₅)
×₆-is-prop i₀ i₁ i₂ i₃ i₄ i₅ = ×-is-prop i₀ (×₅-is-prop i₁ i₂ i₃ i₄ i₅)

×₇-is-prop : {𝓥₀ 𝓥₁ 𝓥₂ 𝓥₃ 𝓥₄ 𝓥₅ 𝓥₆ : Universe}
             {X₀ : 𝓥₀ ̇ } {X₁ : 𝓥₁ ̇ } {X₂ : 𝓥₂ ̇ } {X₃ : 𝓥₃ ̇ } {X₄ : 𝓥₄ ̇ } {X₅ : 𝓥₅ ̇ } {X₆ : 𝓥₆ ̇ }
           → is-prop X₀ → is-prop X₁ → is-prop X₂ → is-prop X₃ → is-prop X₄ → is-prop X₅ → is-prop X₆ → is-prop (X₀ × X₁ × X₂ × X₃ × X₄ × X₅ × X₆)
×₇-is-prop i₀ i₁ i₂ i₃ i₄ i₅ i₆ = ×-is-prop i₀ (×₆-is-prop i₁ i₂ i₃ i₄ i₅ i₆)

×₈-is-prop : {𝓥₀ 𝓥₁ 𝓥₂ 𝓥₃ 𝓥₄ 𝓥₅ 𝓥₆ 𝓥₇ : Universe}
             {X₀ : 𝓥₀ ̇ } {X₁ : 𝓥₁ ̇ } {X₂ : 𝓥₂ ̇ } {X₃ : 𝓥₃ ̇ } {X₄ : 𝓥₄ ̇ } {X₅ : 𝓥₅ ̇ } {X₆ : 𝓥₆ ̇ } {X₇ : 𝓥₇ ̇ }
           → is-prop X₀ → is-prop X₁ → is-prop X₂ → is-prop X₃ → is-prop X₄ → is-prop X₅ → is-prop X₆ → is-prop X₇ → is-prop (X₀ × X₁ × X₂ × X₃ × X₄ × X₅ × X₆ × X₇)
×₈-is-prop i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ = ×-is-prop i₀ (×₇-is-prop i₁ i₂ i₃ i₄ i₅ i₆ i₇)
\end{code}

The type of truth values.

\begin{code}

Ω : ∀ 𝓤 → 𝓤 ⁺ ̇
Ω 𝓤 = Σ P ꞉ 𝓤 ̇ , is-prop P

Ω₀ = Ω 𝓤₀

_holds : Ω 𝓤 → 𝓤 ̇
(P , i) holds = P


holds-is-prop : (p : Ω 𝓤) → is-prop (p holds)
holds-is-prop (P , i) = i

⊥Ω ⊤Ω : Ω 𝓤
⊥Ω = 𝟘 , 𝟘-is-prop   -- false
⊤Ω = 𝟙 , 𝟙-is-prop   -- true

\end{code}
