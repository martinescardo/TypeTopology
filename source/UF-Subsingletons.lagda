In univalent logic, as opposed to Curry-Howard logic, a proposition is
a subsingleton or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Subsingletons where

open import SpartanMLTT
open import UF-Base

\end{code}


\begin{code}

is-subsingleton : ∀ {U} → U ̇ → U ̇
is-subsingleton X = (x y : X) → x ≡ y

Ω : ∀ {U} → U ′ ̇
Ω {U} = Σ \(P : U ̇) → is-subsingleton P 

\end{code}

I prefer the above terminology, but I will stick to the following (at
least for the moment).

\begin{code}

is-prop : ∀ {U} → U ̇ → U ̇
is-prop = is-subsingleton

_holds : ∀ {U} → Ω → U ̇
_holds = pr₁

holds-is-prop : ∀ {U} → (p : Ω {U}) → is-prop (p holds)
holds-is-prop = pr₂

\end{code}

And of course we could adopt a terminology borrowed from topos logic:

\begin{code}

is-truth-value : ∀ {U} → U ̇ → U ̇
is-truth-value = is-subsingleton

\end{code}

\begin{code}

is-prop-closed-under-Σ : ∀ {U V} {X : U ̇} {A : X → V ̇} 
                      → is-prop X → ((x : X) → is-prop(A x)) → is-prop(Σ A)
is-prop-closed-under-Σ {U} {V} {X} {A} isx isa (x , a) (y , b) = 
                      to-Σ-≡ x y a b (isx x y) (isa y (transport A (isx x y) a) b)

\end{code}

Next we define singleton (or contractible types). The terminology
"contractible" is due to Voevodsky. I currently prefer the terminology
"singleton type", because it makes more sense when we consider
univalent type theory as interesting on its own right independently of
its homotopical (originally motivating) models. Also it emphasizes
that we don't required homotopy theory as a prerequisite to understand
univalent type theory.

\begin{code}

is-the-only-element : ∀ {U} {X : U ̇} → X → U ̇
is-the-only-element c = ∀ x → c ≡ x

is-singleton : ∀ {U} → U ̇ → U ̇
is-singleton X = Σ \(c : X) → is-the-only-element c

\end{code}

For compatibility with the homotopical terminology:

\begin{code}

is-center-of-contraction : ∀ {U} {X : U ̇} → X → U ̇
is-center-of-contraction = is-the-only-element

is-contr : ∀ {U} → U ̇ → U ̇
is-contr = is-singleton

𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = * , (λ x → (𝟙-all-* x)⁻¹)

is-singleton-is-prop : ∀ {U} {X : U ̇} → is-singleton X → is-prop X
is-singleton-is-prop {U} {X} (c , φ) x y = x ≡⟨ (φ x) ⁻¹ ⟩ c ≡⟨ φ y ⟩ y ∎

iis-singleton-is-prop : ∀ {U} {X : U ̇} → (X → is-singleton X) → is-prop X
iis-singleton-is-prop {U} {X} φ x = is-singleton-is-prop (φ x) x

iis-prop-is-prop : ∀ {U} {X : U ̇} → (X → is-prop X) → is-prop X
iis-prop-is-prop {U} {X} φ x y = φ x x y

inhabited-proposition-is-singleton : ∀ {U} {X : U ̇} → X → is-prop X → is-singleton X 
inhabited-proposition-is-singleton x h = x , h x

\end{code}

The two prototypical propositions:

\begin{code}

𝟘-is-prop : is-prop 𝟘
𝟘-is-prop x y = unique-from-𝟘 x

𝟙-is-prop : is-prop 𝟙
𝟙-is-prop * * = refl

⊥ ⊤ : Ω
⊥ = 𝟘 , 𝟘-is-prop   -- false
⊤ = 𝟙 , 𝟙-is-prop   -- true

\end{code}

A type is a set if all its identity types are subsingletons. In other
words, sets are types for which equality is a proposition (rather than
data or structure).

\begin{code}

is-set : ∀ {U} → U ̇ → U ̇
is-set X = {x y : X} → is-prop (x ≡ y)

\end{code}

We now consider some machinery for dealing with the above notions:

\begin{code}

constant : ∀ {U V} {X : U ̇} {Y : V ̇} → (f : X → Y) → U ⊔ V ̇
constant f = ∀ x y → f x ≡ f y

collapsible : ∀ {U} → U ̇ → U ̇
collapsible X = Σ \(f : X → X) → constant f

identification-collapsible : ∀ {U} → U ̇ → U ̇
identification-collapsible X = {x y : X} → collapsible(x ≡ y)

set-is-identification-collapsible : ∀ {U} → {X : U ̇} → is-set X → identification-collapsible X
set-is-identification-collapsible u = (id , u)

local-hedberg : ∀ {U} {X : U ̇} (x : X) 
      → ((y : X) → collapsible (x ≡ y)) 
      → (y : X) → is-prop (x ≡ y)
local-hedberg {U} {X} x pc y p q = claim₂
 where
  f : (y : X) → x ≡ y → x ≡ y
  f y = pr₁ (pc y)
  g : (y : X) (p q : x ≡ y) → f y p ≡ f y q
  g y = pr₂ (pc y)
  claim₀ : (y : X) (r : x ≡ y) → r ≡ (f x refl)⁻¹ ∙ f y r
  claim₀ _ refl = sym-is-inverse (f x refl)
  claim₁ : (f x refl)⁻¹ ∙ f y p ≡ (f x refl)⁻¹ ∙ f y q
  claim₁ = ap (λ h → (f x refl)⁻¹ ∙ h) (g y p q)
  claim₂ : p ≡ q
  claim₂ = (claim₀ y p) ∙ claim₁ ∙ (claim₀ y q)⁻¹ 

identification-collapsible-is-set : ∀ {U} {X : U ̇} → identification-collapsible X → is-set X
identification-collapsible-is-set {X} pc {x} {y} p q = local-hedberg x (λ y → (pr₁(pc {x} {y})) , (pr₂(pc {x} {y}))) y p q

\end{code}

We also need the following symmetrical version of local Hedberg, which
can be proved by reduction to the above (using the fact that
collapsible types are closed under equivalence), but at this point we
don't have the machinery at this disposal (which is developed in
modules that depend on this one), and hence we prove it directly by
symmetrizing the proof.

\begin{code}

local-hedberg' : ∀ {U} {X : U ̇} (x : X) 
      → ((y : X) → collapsible (y ≡ x)) 
      → (y : X) → is-prop (y ≡ x)
local-hedberg' {U} {X} x pc y p q = claim₂
 where
  f : (y : X) → y ≡ x → y ≡ x
  f y = pr₁ (pc y)
  g : (y : X) (p q : y ≡ x) → f y p ≡ f y q
  g y = pr₂ (pc y)
  claim₀ : (y : X) (r : y ≡ x) → r ≡  (f y r) ∙ (f x refl)⁻¹
  claim₀ _ refl = sym-is-inverse' (f x refl)
  claim₁ : f y p ∙ (f x refl)⁻¹  ≡ f y q ∙ (f x refl)⁻¹
  claim₁ = ap (λ h → h ∙ (f x refl)⁻¹) (g y p q)
  claim₂ : p ≡ q
  claim₂ = (claim₀ y p) ∙ claim₁ ∙ (claim₀ y q)⁻¹

prop-is-identification-collapsible : ∀ {U} {X : U ̇} → is-prop X → identification-collapsible X
prop-is-identification-collapsible h {x} {y} = ((λ p → h x y) , (λ p q → refl))

prop-is-set : ∀ {U} {X : U ̇} → is-prop X → is-set X
prop-is-set h = identification-collapsible-is-set(prop-is-identification-collapsible h)

𝟘-is-collapsible : collapsible 𝟘
𝟘-is-collapsible = (λ x → x) , (λ x → λ ())

inhabited-is-collapsible : ∀ {U} {X : U ̇} → X → collapsible X
inhabited-is-collapsible x = ((λ y → x) , λ y y' → refl)

\end{code}

Under Curry-Howard, the function type X → 𝟘 is understood as the
negation of X when X is viewed as a proposition. But when X is
understood as a mathematical object, inhabiting the type X → 𝟘 amounts
to showing that X is empty. (In fact, assuming univalence, defined
below, the type X → 𝟘 is equivalent to the type X ≡ 𝟘
(written (X → 𝟘) ≃ (X ≡ 𝟘)).)

\begin{code}

is-empty : ∀ {U} → U ̇ → U ̇
is-empty X = X → 𝟘

is-empty-is-collapsible : ∀ {U} {X : U ̇} → is-empty X → collapsible X
is-empty-is-collapsible u = (id , (λ x x' → unique-from-𝟘(u x)))

𝟘-is-collapsible-as-a-particular-case : collapsible 𝟘
𝟘-is-collapsible-as-a-particular-case = is-empty-is-collapsible id

identifications-from : ∀ {U} {X : U ̇} (x : X) → U ̇
identifications-from x = Σ \y → x ≡ y

trivial-loop : ∀ {U} {X : U ̇} (x : X) → identifications-from x
trivial-loop x = (x , refl)

identification-from-trivial-loop : ∀ {U} {X : U ̇} {x x' : X} (r : x ≡ x') → trivial-loop x ≡ (x' , r)
identification-from-trivial-loop {U} {X} = J A (λ x → refl)
 where 
  A : (x x' : X) → x ≡ x' → U ̇
  A x x' r = _≡_ {_} {Σ \(x' : X) → x ≡ x'} (trivial-loop x) (x' , r) 

identifications-from-is-singleton : ∀ {U} {X : U ̇} (x₀ : X) → is-singleton(identifications-from x₀)
identifications-from-is-singleton x₀ = trivial-loop x₀ , (λ t → identification-from-trivial-loop (pr₂ t))

identifications-from-is-prop : ∀ {U} {X : U ̇} (x : X) → is-prop(identifications-from x)
identifications-from-is-prop x = is-singleton-is-prop (identifications-from-is-singleton x)

singleton-types-are-singletons : ∀ {U} {X : U ̇} {x : X}
                        → is-the-only-element {U} {identifications-from x} (x , refl)
singleton-types-are-singletons {U} {X} (y , refl) = refl

identifications-from-singleton : ∀ {U} {X : U ̇} (x : X) → is-singleton(identifications-from x)
identifications-from-singleton x = ((x , refl) , singleton-types-are-singletons)

identifications-to : ∀ {U} {X : U ̇} → X → U ̇
identifications-to x = Σ \y → y ≡ x

×-prop-criterion-necessity : ∀ {U} {X Y : U ̇} → is-prop(X × Y) → (Y → is-prop X) × (X → is-prop Y)
×-prop-criterion-necessity isp = (λ y x x' → ap pr₁ (isp (x , y) (x' , y ))) ,
                                 (λ x y y' → ap pr₂ (isp (x , y) (x  , y')))

×-prop-criterion : ∀ {U} {X Y : U ̇} → (Y → is-prop X) × (X → is-prop Y) → is-prop(X × Y)
×-prop-criterion (i , j) (x , y) (x' , y') = to-Σ-≡'' (i y x x' , j x _ _)

props-closed-× : ∀ {U} {X Y : U ̇} → is-prop X → is-prop Y → is-prop(X × Y)
props-closed-× i j = ×-prop-criterion ((λ _ → i) , (λ _ → j))

subtype-of-set-is-set : ∀ {U V} {X : U ̇} {Y : V ̇} (m : X → Y)
                     → left-cancellable m → is-set Y → is-set X
subtype-of-set-is-set {U} {V} {X} m i h = identification-collapsible-is-set (f , g)
 where
  f : {x x' : X} → x ≡ x' → x ≡ x'
  f r = i (ap m r)
  g : {x x' : X} (r s : x ≡ x') → f r ≡ f s
  g r s = ap i (h (ap m r) (ap m s))

pr₁-lc : ∀ {U V} {X : U ̇} {Y : X → V ̇} → ({x : X} → is-prop(Y x)) → left-cancellable (pr₁ {U} {V} {X} {Y})
pr₁-lc f p = to-Σ-≡'' (p , (f _ _))

subset-of-set-is-set : ∀ {U V} (X : U ̇) (Y : X → V ̇) 
                    → is-set X → ({x : X} → is-prop(Y x)) → is-set(Σ \(x : X) → Y x)
subset-of-set-is-set X Y h p = subtype-of-set-is-set pr₁ (pr₁-lc p) h

\end{code}

Formulation of the K axiom for a universe U.

\begin{code}

K : ∀ U → U ′ ̇
K U = (X : U ̇) → is-set X

\end{code}

Formulation of propositional extensionality:

\begin{code}

propext : ∀ U → U ′ ̇ 
propext U = {P Q : U ̇} → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ≡ Q

\end{code}

The following says that, in particular, for any proposition P, we have
that P + ¬ P is a proposition, or that the decidability of a
proposition is a proposition:

\begin{code}

sum-of-contradictory-props : ∀ {U V} {P : U ̇} {Q : V ̇}
                           → is-prop P → is-prop Q → (P → Q → 𝟘) → is-prop(P + Q)
sum-of-contradictory-props {U} {V} {P} {Q} isp isq f = go
  where
   go : (x y : P + Q) → x ≡ y
   go (inl p) (inl p') = ap inl (isp p p')
   go (inl p) (inr q)  = 𝟘-elim (f p q)
   go (inr q) (inl p)  = 𝟘-elim (f p q)
   go (inr q) (inr q') = ap inr (isq q q')

\end{code}
