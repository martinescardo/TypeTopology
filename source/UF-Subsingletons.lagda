In univalent logic, as opposed to Curry-Howard logic, a proposition is
a subsingleton or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Subsingletons where

open import UF-Base

\end{code}


\begin{code}

isSubsingleton : ∀ {U} → U ̇ → U ̇
isSubsingleton X = (x y : X) → x ≡ y

Ω : ∀ {U} → U ′ ̇
Ω {U} = Σ \(P : U ̇) → isSubsingleton P 

\end{code}

I prefer the above terminology, but I will stick to the following (at
least for the moment).

\begin{code}

isProp : ∀ {U} → U ̇ → U ̇
isProp = isSubsingleton

Prop : ∀ {U} → U ′ ̇
Prop = Ω

_holds : ∀ {U} → Prop → U ̇
_holds = pr₁

holdsIsProp : ∀ {U} → (p : Prop {U}) → isProp (p holds)
holdsIsProp = pr₂

\end{code}

And of course we could adopt a terminology borrowed from topos logic:

\begin{code}

isTruthValue : ∀ {U} → U ̇ → U ̇
isTruthValue = isSubsingleton

\end{code}

\begin{code}

isProp-closed-under-Σ : ∀ {U V} {X : U ̇} {A : X → V ̇} 
                      → isProp X → ((x : X) → isProp(A x)) → isProp(Σ A)
isProp-closed-under-Σ {U} {V} {X} {A} isx isa (x , a) (y , b) = 
                      to-Σ-≡ x y a b (isx x y) (isa y (transport A (isx x y) a) b)

\end{code}

Next we define contractible types. The terminology is due to
Voevodsky. I currently prefer the terminology "singleton type",
because it makes more sense when we consider univalent type theory as
interesting on its own right independently of its homotopical
(originally motivating) models.

\begin{code}

is-the-only-element : ∀ {U} {X : U ̇} → X → U ̇
is-the-only-element c = ∀ x → c ≡ x

isSingleton : ∀ {U} → U ̇ → U ̇
isSingleton X = Σ \(c : X) → is-the-only-element c

\end{code}

For compatibility with the homotopical terminology:

\begin{code}

is-center-of-contraction : ∀ {U} {X : U ̇} → X → U ̇
is-center-of-contraction = is-the-only-element

isContr : ∀ {U} → U ̇ → U ̇
isContr = isSingleton

isSingleton-isProp : ∀ {U} {X : U ̇} → isSingleton X → isProp X
isSingleton-isProp {U} {X} (c , φ) x y = x ≡⟨ (φ x) ⁻¹ ⟩ c ≡⟨ φ y ⟩ y ∎

iisSingleton-isProp : ∀ {U} {X : U ̇} → (X → isSingleton X) → isProp X
iisSingleton-isProp {U} {X} φ x = isSingleton-isProp (φ x) x

iisProp-isProp : ∀ {U} {X : U ̇} → (X → isProp X) → isProp X
iisProp-isProp {U} {X} φ x y = φ x x y

inhabited-proposition-isSingleton : ∀ {U} {X : U ̇} → X → isProp X → isSingleton X 
inhabited-proposition-isSingleton x h = x , h x

\end{code}

The two prototypical propositions:

\begin{code}

𝟘-isProp : isProp 𝟘
𝟘-isProp x y = unique-from-𝟘 x

𝟙-isProp : isProp 𝟙
𝟙-isProp * * = refl

⊥ ⊤ : Prop
⊥ = 𝟘 , 𝟘-isProp   -- false
⊤ = 𝟙 , 𝟙-isProp   -- true

\end{code}

A type is a set if all its identity types are subsingletons. In other
words, sets are types for which equality is a proposition (rather than
data or structure).

\begin{code}

isSet : ∀ {U} → U ̇ → U ̇
isSet X = {x y : X} → isProp(x ≡ y)

\end{code}

We now consider some machinery for dealing with the above notions:

\begin{code}

constant : ∀ {U V} {X : U ̇} {Y : V ̇} → (f : X → Y) → U ⊔ V ̇
constant f = ∀ x y → f x ≡ f y

collapsible : ∀ {U} → U ̇ → U ̇
collapsible X = Σ \(f : X → X) → constant f

path-collapsible : ∀ {U} → U ̇ → U ̇
path-collapsible X = {x y : X} → collapsible(x ≡ y)

set-is-path-collapsible : ∀ {U} → {X : U ̇} → isSet X → path-collapsible X
set-is-path-collapsible u = (id , u)

path-collapsible-isSet : ∀ {U} {X : U ̇} → path-collapsible X → isSet X
path-collapsible-isSet pc p q = claim₂
 where
  f : ∀ {x y} → x ≡ y → x ≡ y
  f = pr₁ pc
  g : ∀ {x y} (p q : x ≡ y) → f p ≡ f q
  g = pr₂ pc
  claim₀ : ∀ {x y} (r : x ≡ y) → r ≡ (f refl) ⁻¹ ∙ f r
  claim₀ = J (λ x y r → r ≡ (f refl) ⁻¹ ∙ f r) (λ x → sym-is-inverse(f refl))
  claim₁ : (f refl) ⁻¹ ∙ f p ≡ (f refl) ⁻¹ ∙ f q
  claim₁ = ap (λ h → (f refl) ⁻¹ ∙ h) (g p q)
  claim₂ : p ≡ q
  claim₂ = claim₀ p ∙ claim₁ ∙ (claim₀ q)⁻¹

prop-is-path-collapsible : ∀ {U} {X : U ̇} → isProp X → path-collapsible X
prop-is-path-collapsible h {x} {y} = ((λ p → h x y) , (λ p q → refl))

prop-isSet : ∀ {U} {X : U ̇} → isProp X → isSet X
prop-isSet h = path-collapsible-isSet(prop-is-path-collapsible h)

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

isEmpty : ∀ {U} → U ̇ → U ̇
isEmpty X = X → 𝟘

isEmpty-is-collapsible : ∀ {U} {X : U ̇} → isEmpty X → collapsible X
isEmpty-is-collapsible u = (id , (λ x x' → unique-from-𝟘(u x)))

𝟘-is-collapsible-as-a-particular-case : collapsible 𝟘
𝟘-is-collapsible-as-a-particular-case = isEmpty-is-collapsible id

\end{code}

For the moment we will use homotopical terminology for the following
(but, for example, "paths-from x" could be written "singletonType x"
as in https://arxiv.org/pdf/1803.02294).

\begin{code}

paths-from : ∀ {U} {X : U ̇} (x : X) → U ̇
paths-from x = Σ \y → x ≡ y

end-point : ∀ {U} {X : U ̇} {x : X} → paths-from x → X
end-point = pr₁ 

trivial-loop : ∀ {U} {X : U ̇} (x : X) → paths-from x
trivial-loop x = (x , refl)

path-from-trivial-loop : ∀ {U} {X : U ̇} {x x' : X} (r : x ≡ x') → trivial-loop x ≡ (x' , r)
path-from-trivial-loop {U} {X} = J A (λ x → refl)
 where 
  A : (x x' : X) → x ≡ x' → U ̇
  A x x' r = _≡_ {_} {Σ \(x' : X) → x ≡ x'} (trivial-loop x) (x' , r) 

paths-from-isSingleton : ∀ {U} {X : U ̇} (x₀ : X) → isSingleton(paths-from x₀)
paths-from-isSingleton x₀ = trivial-loop x₀ , (λ t → path-from-trivial-loop (pr₂ t))

paths-from-isProp : ∀ {U} {X : U ̇} (x : X) → isProp(paths-from x)
paths-from-isProp x = isSingleton-isProp (paths-from-isSingleton x)

singleton-types-are-singletons : ∀ {U} {X : U ̇} {x : X}
                        → is-the-only-element {U} {paths-from x} (x , refl)
singleton-types-are-singletons {U} {X} (y , refl) = refl

paths-from-contractible : ∀ {U} {X : U ̇} (x : X) → isSingleton(paths-from x)
paths-from-contractible x = ((x , refl) , singleton-types-are-singletons)

paths-to : ∀ {U} {X : U ̇} → X → U ̇
paths-to x = Σ \y → y ≡ x

×-prop-criterion-necessity : ∀ {U} {X Y : U ̇} → isProp(X × Y) → (Y → isProp X) × (X → isProp Y)
×-prop-criterion-necessity isp = (λ y x x' → ap pr₁ (isp (x , y) (x' , y ))) ,
                                 (λ x y y' → ap pr₂ (isp (x , y) (x  , y')))

×-prop-criterion : ∀ {U} {X Y : U ̇} → (Y → isProp X) × (X → isProp Y) → isProp(X × Y)
×-prop-criterion (i , j) (x , y) (x' , y') = to-Σ-≡'' (i y x x' , j x _ _)

props-closed-× : ∀ {U} {X Y : U ̇} → isProp X → isProp Y → isProp(X × Y)
props-closed-× i j = ×-prop-criterion ((λ _ → i) , (λ _ → j))

subtype-of-set-isSet : ∀ {U V} {X : U ̇} {Y : V ̇} (m : X → Y)
                     → left-cancellable m → isSet Y → isSet X
subtype-of-set-isSet {U} {V} {X} m i h = path-collapsible-isSet (f , g)
 where
  f : {x x' : X} → x ≡ x' → x ≡ x'
  f r = i (ap m r)
  g : {x x' : X} (r s : x ≡ x') → f r ≡ f s
  g r s = ap i (h (ap m r) (ap m s))

pr₁-lc : ∀ {U V} {X : U ̇} {Y : X → V ̇} → ({x : X} → isProp(Y x)) → left-cancellable (pr₁ {U} {V} {X} {Y})
pr₁-lc f p = to-Σ-≡'' (p , (f _ _))

subset-of-set-isSet : ∀ {U V} (X : U ̇) (Y : X → V ̇) 
                    → isSet X → ({x : X} → isProp(Y x)) → isSet(Σ \(x : X) → Y x)
subset-of-set-isSet X Y h p = subtype-of-set-isSet pr₁ (pr₁-lc p) h

\end{code}

Formulation of the K axiom for a universe U.

\begin{code}

K : ∀ U → U ′ ̇
K U = (X : U ̇) → isSet X

\end{code}

\begin{code}

propExt : ∀ U → U ′ ̇ 
propExt U = {P Q : U ̇} → isProp P → isProp Q → (P → Q) → (Q → P) → P ≡ Q

\end{code}
