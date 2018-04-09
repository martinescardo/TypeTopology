Martin Escardo, 2011, 2012, 2013, 2014, 2015, 2016, 2017, 2018.

This is a(n incomplete) univalent foundations library (in Agda
notation), with some things developed using the Yoneda-lemma view of
the identity type, as put forward in
http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html, for the sake of
experimentation.

This file has been merged from various different files in different
developments and needs to be organized. We also need to remove
some repetitions that arise from this merging.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF where

\end{code}

The following imported module defines a minimal Martin-Löf type theory
for univalent mathematics. Some things there are repeated here, and
should be removed from there (TODO).

\begin{code}

open import SpartanMLTT public

\end{code}

In univalent logic, as opposed to Curry-Howard logic, a proposition is
a subsingleton or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

\begin{code}

isProp : ∀ {U} → U ̇ → U ̇
isProp X = (x y : X) → x ≡ y

\end{code}

I prefer the following terminology, but I will stick to the above (at
least for the moment).

\begin{code}

isSubsingleton : ∀ {U} → U ̇ → U ̇
isSubsingleton = isProp

\end{code}

And of course we could adopt a terminology borrowed from topos logic:

\begin{code}

isTruthValue : ∀ {U} → U ̇ → U ̇
isTruthValue = isProp

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

\end{code}

We now consider "natural transformations" and the Yoneda-machinery for
them as discussed in http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html

\begin{code}

_⇒_ : ∀ {U V W} {X : U ̇} → (X → V ̇) → (X → W ̇) → (X → V ⊔ W ̇)
A ⇒ B = λ x → A x → B x

Nat : ∀ {U V W} {X : U ̇} → (X → V ̇) → (X → W ̇) → U ⊔ V ⊔ W ̇
Nat A B = Π(A ⇒ B)

\end{code}

Point-point-wise equality of natural transformations:

\begin{code}

_≈_ : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} → Nat (Id x) A → Nat (Id x) A → U ⊔ V ̇
η ≈ θ = ∀ y → η y ∼ θ y

\end{code}

The Yoneda element induced by a natural transformation:

\begin{code}

yoneda-elem : ∀ {U V} {X : U ̇} {x : X} (A : X → V ̇)
           → Nat (Id x) A → A x
yoneda-elem {U} {V} {X} {x} A η = η x (idp x)

\end{code}

We use capital Yoneda for the same constructions with the definition
of "Nat" expanded, beginning here:

\begin{code}

Yoneda-elem : ∀ {U V} {X : U ̇} {x : X} (A : X → V ̇)
           → ((y : X) → x ≡ y → A y) → A x
Yoneda-elem = yoneda-elem

\end{code}

The natural transformation induced by an element:

\begin{code}

yoneda-nat : ∀ {U V} {X : U ̇} {x : X} (A : X → V ̇)
           → A x → Nat (Id x) A 
yoneda-nat A a y p = transport A p a

Yoneda-nat : ∀ {U V} {X : U ̇} {x : X} (A : X → V ̇)
           → A x → (y : X) → x ≡ y → A y
Yoneda-nat = yoneda-nat

\end{code}

The Yoneda Lemma says that every natural transformation is induced by
its Yoneda element:

\begin{code}

yoneda-lemma : ∀ {U V} {X : U ̇} {x : X} (A : X → V ̇) (η : Nat (Id x) A)
            → yoneda-nat A (yoneda-elem A η) ≈ η 
yoneda-lemma {U} {V} {X} {.x} A η x refl = idp (yoneda-elem A η)

Yoneda-lemma : ∀ {U V} {X : U ̇} {x : X} (A : X → V ̇) (η : (y : X) → x ≡ y → A y) (y : X) (p : x ≡ y)
             → transport A p (η x (idp x)) ≡ η y p
Yoneda-lemma = yoneda-lemma

\end{code}

The word "computation" here arises from a tradition in MLTT and should
not be taken too seriously:

\begin{code}

yoneda-computation : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} (a : A x) 
                   → yoneda-elem A (yoneda-nat A a) ≡ a
yoneda-computation = idp 

Yoneda-computation : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} (a : A x) 
                   → transport A (idp x) a ≡ a
Yoneda-computation {U} {V} {X} {x} {A} = yoneda-computation {U} {V} {X} {x} {A}

\end{code}

Two natural transformations with the same Yoneda elements are
(point-point-wise) equal:

\begin{code}

yoneda-elem-lc : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} (η θ : Nat (Id x) A)             
              → yoneda-elem A η ≡ yoneda-elem A θ → η ≈ θ
yoneda-elem-lc {U} {V} {X} {x} {A} η θ q y p =
  η y p                              ≡⟨ (yoneda-lemma A η y p)⁻¹ ⟩
  yoneda-nat A (yoneda-elem A η) y p ≡⟨ ap (λ e → yoneda-nat A e y p) q ⟩
  yoneda-nat A (yoneda-elem A θ) y p ≡⟨ yoneda-lemma A θ y p ⟩
  θ y p ∎

Yoneda-elem-lc : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} (η θ : (y : X) → x ≡ y → A y)             
              → η x (idp x) ≡ θ x (idp x) → (y : X) (p : x ≡ y) → η y p ≡ θ y p
Yoneda-elem-lc = yoneda-elem-lc

\end{code}

Some special cases of interest, which probably speak for themselves:

\begin{code}

yoneda-nat' : ∀ {U} {X : U ̇} (x {y} : X) → Id x y → Nat (Id y) (Id x)
yoneda-nat' x = yoneda-nat (Id x)

Yoneda-nat' : ∀ {U} {X : U ̇} (x {y} : X) → x ≡ y → (z : X) → y ≡ z → x ≡ z
Yoneda-nat' = yoneda-nat'

yoneda-elem' : ∀ {U} {X : U ̇} (x {y} : X) → Nat (Id y) (Id x) → Id x y
yoneda-elem' x = yoneda-elem (Id x)

Yoneda-elem' : ∀ {U} {X : U ̇} (x {y} : X) → ((z : X) → y ≡ z → x ≡ z) → x ≡ y
Yoneda-elem' = yoneda-elem'

yoneda-lemma' : ∀ {U} {X : U ̇} (x {y} : X) (η : Nat (Id y) (Id x)) (z : X) (p : y ≡ z)
              → (yoneda-elem' x η) ∙ p ≡ η z p
yoneda-lemma' x = yoneda-lemma (Id x)

Yoneda-lemma' : ∀ {U} {X : U ̇} (x {y} : X) (η : (z : X) → y ≡ z → x ≡ z) (z : X) (p : y ≡ z)
              → η y (idp y) ∙ p ≡ η z p
Yoneda-lemma' = yoneda-lemma'

yoneda-lemma'' : ∀ {U} {X : U ̇} (x {y} : X) (η : Nat (Id y) (Id x)) (z : X) (p : y ≡ z)
              → yoneda-nat' x (yoneda-elem' x η) z p ≡ η z p
yoneda-lemma'' x = yoneda-lemma (Id x)

hedberg-lemma : ∀ {U} {X : U ̇} (x : X) (η : Nat (Id x) (Id x)) (y : X) (p : x ≡ y)
              → (yoneda-elem' x η) ∙ p ≡ η y p
hedberg-lemma x η y p = yoneda-lemma' x η y p

Hedberg-lemma : ∀ {U} {X : U ̇} (x : X) (η : (y : X) → x ≡ y → x ≡ y) (y : X) (p : x ≡ y)
              → η x (idp x) ∙ p ≡ η y p
Hedberg-lemma = hedberg-lemma

yoneda-const : ∀ {U V} {X : U ̇} {B : V ̇} {x : X} (η : Nat (Id x) (λ _ → B)) (y : X) (p : x ≡ y)
             → yoneda-elem (λ _ → B) η ≡ η y p 
yoneda-const η = yoneda-elem-lc (λ y p → yoneda-elem _ η) η (idp (yoneda-elem _ η))

Yoneda-const : ∀ {U V} {X : U ̇} {B : V ̇} {x : X} (η : (y : X) → x ≡ y → B) (y : X) (p : x ≡ y)
             → η x (idp x) ≡ η y p 
Yoneda-const = yoneda-const

\end{code}

The following is traditionally proved by induction on the identity
type (as articulated by Jbased or J in the module SpartanMLTT), but
here we use the Yoneda machinery instead:

\begin{code}

singleton-types-are-singletons : ∀ {U} {X : U ̇} {x : X}
                        → is-the-only-element (x , idp x)
singleton-types-are-singletons {U} {X} {x} (y , p) = yoneda-const η y p
 where
  η : (y : X) → x ≡ y → paths-from x
  η y p = (y , p)

\end{code}

What the following says is that the Yoneda machinery could have been
taken as primitive, as an alternative to Jbased or J, in the sense
that the latter can be recovered from the former.

\begin{code}

Jbased'' : ∀ {U V} {X : U ̇} (x : X) (A : paths-from x → V ̇)
         → A (x , idp x) → Π A
Jbased'' x A b w = yoneda-nat A b w (singleton-types-are-singletons w)

Jbased' : ∀ {U V} {X : U ̇} (x : X) (B : (y : X) → x ≡ y → V ̇)
        → B x (idp x) → (y : X) (p : x ≡ y) → B y p
Jbased' x B b y p = Jbased'' x (uncurry B) b (y , p)

\end{code}

And now some uses of Yoneda to prove things that traditionally are
proved using J(based).

\begin{code}


idp-left-neutral : ∀ {U} {X : U ̇} {x y : X} {p : x ≡ y} → idp x ∙ p ≡ p
idp-left-neutral {U} {X} {x} {y} {p} = yoneda-lemma (Id x) (λ y p → p) y p

idp-right-neutral : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → p ≡ p ∙ (idp y) 
idp-right-neutral = idp

⁻¹-involutive : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → (p ⁻¹)⁻¹ ≡ p
⁻¹-involutive {U} {X} {x} {y} = yoneda-elem-lc (λ x p → (p ⁻¹)⁻¹) (λ x p → p) (idp(idp x)) y

⁻¹-contravariant : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) {z : X} (q : y ≡ z)
                → q ⁻¹ ∙ p ⁻¹ ≡ (p ∙ q)⁻¹
⁻¹-contravariant {U} {X} {x} {y} p {z} = yoneda-elem-lc (λ z q → q ⁻¹ ∙ p ⁻¹)
                                                       (λ z q → (p ∙ q) ⁻¹)
                                                       idp-left-neutral
                                                       z
\end{code}

Associativity also follows from the Yoneda Lemma, again with the same
proof method. Notice that we prove that two functions (in a context)
are equal without using function extensionality:

\begin{code}

ext-assoc : ∀ {U} {X : U ̇} {z t : X} (r : z ≡ t)
          → (λ (x y : X) (p : x ≡ y) (q : y ≡ z) → (p ∙ q) ∙ r)
          ≡ (λ (x y : X) (p : x ≡ y) (q : y ≡ z) → p ∙ (q ∙ r))
ext-assoc {U} {X} {z} {t} = yoneda-elem-lc (λ z r x y p q → p ∙ q ∙ r)
                                           (λ z r x y p q → p ∙ (q ∙ r))
                                           (idp (λ x y p q → p ∙ q))
                                           t 
\end{code}

Then of course associativity of path composition follows:

\begin{code}

assoc : ∀ {U} {X : U ̇} {x y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
      → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc {U} {X} {x} {y} p q r = ap (λ f → f x y p q) (ext-assoc r) 

left-inverse : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → p ⁻¹ ∙ p ≡ idp y
left-inverse {U} {X} {x} {y} = yoneda-elem-lc (λ x p → p ⁻¹ ∙ p) (λ x p → idp x) (idp(idp x)) y

right-inverse : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → idp x ≡ p ∙ p ⁻¹
right-inverse {U} {X} {x} {y} = yoneda-const (λ x p → p ∙ p ⁻¹) y

cancel-left : ∀ {U} {X : U ̇} {x y z : X} {p : x ≡ y} {q r : y ≡ z}
            → p ∙ q ≡ p ∙ r → q ≡ r
cancel-left {U} {X} {x} {y} {z} {p} {q} {r} s = 
       q              ≡⟨ idp-left-neutral ⁻¹ ⟩
       idp y ∙ q      ≡⟨ ap (λ t → t ∙ q) ((left-inverse p)⁻¹) ⟩
       (p ⁻¹ ∙ p) ∙ q ≡⟨ assoc (p ⁻¹) p q ⟩
       p ⁻¹ ∙ (p ∙ q) ≡⟨ ap (λ t → p ⁻¹ ∙ t) s ⟩
       p ⁻¹ ∙ (p ∙ r) ≡⟨ (assoc (p ⁻¹) p r)⁻¹ ⟩
       (p ⁻¹ ∙ p) ∙ r ≡⟨ ap (λ t → t ∙ r) (left-inverse p) ⟩
       idp y ∙ r      ≡⟨ idp-left-neutral ⟩
       r ∎

from-Σ-Id : ∀ {U V} {X : U ̇} (A : X → V ̇) {σ τ : Σ A}
          → σ ≡ τ
          → Σ \(p : pr₁ σ ≡ pr₁ τ) → yoneda-nat A (pr₂ σ) (pr₁ τ) p ≡ pr₂ τ
from-Σ-Id {U} {V} {X} A {x , a} {τ} = yoneda-nat B (idp x , idp a) τ
 where
   B : (τ : Σ A) → U ⊔ V ̇
   B τ = Σ \(p : x ≡ pr₁ τ) → yoneda-nat A a (pr₁ τ) p ≡ pr₂ τ

to-Σ-Id : ∀ {U V} {X : U ̇} (A : X → V ̇) {σ τ : Σ A}
          → (Σ \(p : pr₁ σ ≡ pr₁ τ) → yoneda-nat A (pr₂ σ) (pr₁ τ) p ≡ pr₂ τ)
          → σ ≡ τ
to-Σ-Id {U} {V} {X} A {x , a} {y , b} (p , q) = r
 where
  η : (y : X) → x ≡ y → Σ A
  η y p = (y , yoneda-nat A a y p)
  yc : (x , a) ≡ (y , yoneda-nat A a y p)
  yc = yoneda-const η y p
  r : (x , a) ≡ (y , b)
  r = yoneda-nat (λ b → (x , a) ≡ (y , b)) yc b q

\end{code}

Next we observe that "only elements" as defined above are universal
elements as in category theory.

\begin{code}

is-universal-element : ∀ {U V} {X : U ̇} {A : X → V ̇} → Σ A → U ⊔ V ̇
is-universal-element {U} {V} {X} {A} (x , a) = ∀ y (b : A y) → Σ \(p : x ≡ y) → yoneda-nat A a y p ≡ b

ue-is-cc : ∀ {U V} {X : U ̇} {A : X → V ̇}
          (σ : Σ A) → is-universal-element σ → is-the-only-element σ
ue-is-cc {U} {V} {X} {A} (x , a) u (y , b) = to-Σ-Id A ((u y) b)

cc-is-ue : ∀ {U V} {X : U ̇} (A : X → V ̇) 
          (σ : Σ A) → is-the-only-element σ → is-universal-element σ
cc-is-ue A (x , a) φ y b = from-Σ-Id A {x , a} {y , b} (φ(y , b))
 
\end{code}

But to study this we need to pause to define and study equivalences,
which first requires defining retractions (and hence sections). We
take Joyal's version of the notion of equivalence as the primary one.

\begin{code}

_isSectionOf_ : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → (Y → X) → U ̇
s isSectionOf r = r ∘ s ∼ id

hasSection : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
hasSection r = Σ \s → s isSectionOf r

hasRetraction : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
hasRetraction s = Σ \r → s isSectionOf r

retract_of_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
retract Y of X = Σ \(r : X → Y) → hasSection r

isEquiv : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
isEquiv f = hasSection f × hasRetraction f 

_≃_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
X ≃ Y = Σ \(f : X → Y) → isEquiv f

ideq : ∀ {U} (X : U ̇) → X ≃ X
ideq X = id , ((id , idp) , (id , idp))

≃-trans : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇} → X ≃ Y → Y ≃ Z → X ≃ Z
≃-trans {U} {V} {W} {X} {Y} {Z} (f , (g , fg) , (h , hf)) (f' , (g' , fg') , (h' , hf'))  =
  f' ∘ f , (g ∘ g' , fg'') , (h ∘ h' , hf'')
 where
    fg'' : (z : Z) → f' (f (g (g' z))) ≡ z
    fg'' z =  ap f' (fg (g' z)) ∙ fg' z
    hf'' : (x : X) → h(h'(f'(f x))) ≡ x
    hf'' x = ap h (hf' (f x)) ∙ hf x

_≃⟨_⟩_ : ∀ {U V W} (X : U ̇) {Y : V ̇} {Z : W ̇} → X ≃ Y → Y ≃ Z → X ≃ Z
_ ≃⟨ d ⟩ e = ≃-trans d e

_■ : ∀ {U} (X : U ̇) → X ≃ X
_■ = ideq

Eq : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
Eq = _≃_

qinv : {U V : Universe} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
qinv f = Σ \g → (g ∘ f ∼ id) × (f ∘ g ∼ id)

inverse : {U V : Universe} {X : U ̇} {Y : V ̇} (f : X → Y) → isEquiv f → qinv f
inverse {U} {V} {X} {Y} f ((s , fs) , (r , rf)) = s , (sf , fs)
 where
  sf : (x : X) → s(f x) ≡ x
  sf x = s(f x)       ≡⟨ (rf (s (f x)))⁻¹ ⟩
         r(f(s(f x))) ≡⟨ ap r (fs (f x)) ⟩
         r(f x)       ≡⟨ rf x ⟩
         x            ∎

qinv-equiv : {U V : Universe} {X : U ̇} {Y : V ̇} (f : X → Y) → qinv f → isEquiv f
qinv-equiv f (g , (gf , fg)) = (g , fg) , (g , gf)

≃-sym : ∀ {U V} {X : U ̇} {Y : V ̇}  → X ≃ Y → Y ≃ X 
≃-sym {U} {V} {X} {Y} (f , e) = (g , d)
 where
  g : Y → X
  g = pr₁(inverse f e)
  q : qinv g
  q = f , pr₂(pr₂(inverse f e)) , pr₁(pr₂(inverse f e))
  d : isEquiv g
  d = qinv-equiv g q

equiv-retract-l : ∀ {U V} {X : U ̇} {Y : V ̇} → X ≃ Y → retract X of Y 
equiv-retract-l (f , (g , fg) , (h , hf)) = h , f , hf

equiv-retract-r : ∀ {U V} {X : U ̇} {Y : V ̇} → X ≃ Y → retract Y of X
equiv-retract-r (f , (g , fg) , (h , hf)) = f , g , fg

\end{code}

Left-cancellable maps.

\begin{code}

left-cancellable : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
left-cancellable f = ∀ {x x'} → f x ≡ f x' → x ≡ x'

left-cancellable' : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
left-cancellable' f = ∀ x x' → f x ≡ f x' → x ≡ x'

lcmtpip : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → left-cancellable f → isProp Y → isProp X
lcmtpip f lc i x x' = lc (i (f x) (f x'))

section-lc : ∀ {U V} {X : U ̇} {A : V ̇} (s : X → A) → hasRetraction s → left-cancellable s
section-lc {U} {V} {X} {Y} s (r , rs) {x} {y} p = (rs x)⁻¹ ∙ ap r p ∙ rs y

isEquiv-lc : ∀ {U} {X Y : U ̇} (f : X → Y) → isEquiv f → left-cancellable f
isEquiv-lc f (_ , hasr) = section-lc f hasr 

lcccomp : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇} (f : X → Y) (g : Y → Z)
        → left-cancellable f → left-cancellable g → left-cancellable (g ∘ f)
lcccomp f g lcf lcg = lcf ∘ lcg

\end{code}

Formulation of function extensionality.

\begin{code}

FunExt : ∀ U V → U ′ ⊔ V ′ ̇
FunExt U V = {X : U ̇} {A : X → V ̇} (f g : Π A) → isEquiv (happly f g)

≃-funext : ∀ U V → FunExt U V → {X : U ̇} {A : X → V ̇} (f g : Π A)
         → (f ≡ g) ≃ ((x : X) → f x ≡ g x)
≃-funext U V fe f g = happly f g , fe f g

funext : ∀ {U V} (fe : FunExt U V) {X : U ̇} {A : X → V ̇} {f g : Π A} 
       → ((x : X) → f x ≡ g x) → f ≡ g
funext fe {X} {A} {f} {g} = pr₁(pr₁(fe f g))

happly-funext : ∀ {U V} {X : U ̇} {A : X → V ̇}
                (fe : FunExt U V) (f g : Π A) (h : f ∼ g)
              → happly f g (funext fe h) ≡ h
happly-funext fe f g = pr₂(pr₁(fe f g))

funext-lc : ∀ {U V} {X : U ̇} {A : X → V ̇} (fe : FunExt U V) 
         → (f g : Π A) → left-cancellable (funext fe {X} {A} {f} {g})
funext-lc fe f g = section-lc (funext fe) (happly f g , happly-funext fe f g)

happly-lc : ∀ {U V} {X : U ̇} {A : X → V ̇} (fe : FunExt U V) (f g : Π A) 
         → left-cancellable(happly f g)
happly-lc fe f g = section-lc (happly f g) ((pr₂ (fe f g)))

\end{code}

Equivalence of transports.

\begin{code}

transport-isEquiv : ∀ {U V} {X : U ̇} {A : X → V ̇} {x y : X} (p : x ≡ y) → isEquiv (transport A p)
transport-isEquiv refl =  pr₂ (ideq _)

back-transport-isEquiv : ∀ {U V} {X : U ̇} {A : X → V ̇} {x y : X} (p : x ≡ y) → isEquiv (back-transport A p)
back-transport-isEquiv p = transport-isEquiv (p ⁻¹)

\end{code}

Formulation of univalence.

\begin{code}

idtoeq : ∀ {U} (X : U ̇) → Nat (Id X) (Eq X)
idtoeq X = yoneda-nat (Eq X) (ideq X)

idtoeq-bis : ∀ {U} (X Y : U ̇) → X ≡ Y → X ≃ Y
idtoeq-bis = idtoeq

isUnivalent : ∀ U → U ′ ̇
isUnivalent U = (X Y : U ̇) → isEquiv(idtoeq X Y)

eqtofun : ∀ {U V} (X : U ̇) → Nat (Eq X) (λ (Y : V ̇) → X → Y)
eqtofun X Y (f , _) = f

eqtofun-bis : ∀ {U V} (X : U ̇) (Y : V ̇) → X ≃ Y → X → Y
eqtofun-bis = eqtofun

idtofun : ∀ {U} (X : U ̇) → Nat (Id X) (λ Y → X → Y)
idtofun X Y p = eqtofun X Y (idtoeq X Y p)

idtofun-bis : ∀ {U} (X Y : U ̇) → X ≡ Y → X → Y
idtofun-bis = idtofun 

eqtoid : ∀ {U} → isUnivalent U → (X Y : U ̇) → X ≃ Y → X ≡ Y 
eqtoid ua X Y = pr₁(pr₁(ua X Y))

idtoeq-eqtoid : ∀ {U} (ua : isUnivalent U)
              → (X Y : U ̇) (e : X ≃ Y) → idtoeq X Y (eqtoid ua X Y e) ≡ e
idtoeq-eqtoid ua X Y = pr₂(pr₁(ua X Y))

eqtoid' : ∀ {U} → isUnivalent U → (X Y : U ̇) → X ≃ Y → X ≡ Y 
eqtoid' ua X Y = pr₁(pr₂(ua X Y))

eqtoid-idtoeq : ∀ {U} (ua : isUnivalent U)
              → (X Y : U ̇) (p : X ≡ Y) →  eqtoid' ua X Y (idtoeq X Y p) ≡ p
eqtoid-idtoeq ua X Y = pr₂(pr₂(ua X Y))

idtoeq' : ∀ {U} (X Y : U ̇) → X ≡ Y → X ≃ Y
idtoeq' X Y p = (pathtofun p , transport-isEquiv p)

idtoEqs-agree : ∀ {U} (X Y : U ̇) → idtoeq' X Y ∼ idtoeq X Y
idtoEqs-agree X X refl = refl

idtoeq'-eqtoid : ∀ {U} (ua : isUnivalent U)
               → (X Y : U ̇) → idtoeq' X Y ∘ eqtoid ua X Y ∼ id
idtoeq'-eqtoid ua X Y e = idtoEqs-agree X Y (eqtoid ua X Y e) ∙ idtoeq-eqtoid ua X Y e


idtofun' : ∀ {U} (X : U ̇) → Nat (Id X) (λ Y → X → Y)
idtofun' X = yoneda-nat (λ Y → X → Y) id

idtofun-agree : ∀ {U} (X : U ̇) → idtofun X ≈ idtofun' X
idtofun-agree X = yoneda-elem-lc (idtofun X) (idtofun' X) (idp id)

idtofun-isEquiv : ∀ {U} (X Y : U ̇) (p : X ≡ Y) → isEquiv(idtofun X Y p)
idtofun-isEquiv X Y p = pr₂(idtoeq X Y p)

isUnivalent-≃ : ∀ {U} → isUnivalent U → (X Y : U ̇) → (X ≡ Y) ≃ (X ≃ Y)
isUnivalent-≃ ua X Y = idtoeq X Y , ua X Y

back-transport-is-pre-comp' : ∀ {U} (ua : isUnivalent U)
                           → {X X' Y : U ̇} (e : X ≃ X') (g : X' → Y)
                           → back-transport (λ Z → Z → Y) (eqtoid ua X X' e) g ≡ g ∘ pr₁ e 
back-transport-is-pre-comp' ua {X} {X'} e g = back-transport-is-pre-comp (eqtoid ua X X' e) g ∙ q
 where
  q : g ∘ pathtofun (eqtoid ua X X' e) ≡ g ∘ (pr₁ e)
  q = ap (λ h → g ∘ h) (ap pr₁ (idtoeq'-eqtoid ua X X' e))

equiv-closed-under-∼ : ∀ {U V} {X : U ̇} {Y : V ̇} (f g : X → Y) → isEquiv f →  g ∼ f  → isEquiv g
equiv-closed-under-∼ {U} {V} {X} {Y} f g ((s , fs) , (r , rf)) peq = ((s , gs) , (r , rg))
 where
  gs : (y : Y) → g(s y) ≡ y
  gs y = g (s y) ≡⟨ peq (s y) ⟩ f (s y) ≡⟨ fs y ⟩ y ∎
  rg : (x : X) → r(g x) ≡ x
  rg x = r (g x) ≡⟨ ap r (peq x) ⟩ r (f x) ≡⟨ rf x ⟩ x ∎

equiv-closed-under-∼' : ∀ {U V} {X : U ̇} {Y : V ̇} {f g : X → Y} → isEquiv f → f ∼ g → isEquiv g
equiv-closed-under-∼' ise h = equiv-closed-under-∼ _ _ ise (λ x → (h x)⁻¹)

preComp-isEquiv : ∀ {U} (ua : isUnivalent U)
                → {X Y Z : U ̇} (f : X → Y) → isEquiv f → isEquiv (λ (g : Y → Z) → g ∘ f)
preComp-isEquiv ua {X} {Y} f ise = equiv-closed-under-∼' (back-transport-isEquiv (eqtoid ua X Y (f , ise)))
                                                          (back-transport-is-pre-comp' ua (f , ise))

\end{code}

Induction on equivalences is available in univalent universes: to
prove that all equivalences satisfy some property, it is enough to
show that the identity equivalences satisfy it.

\begin{code}

identity-data : ∀ {U} (X : U ̇) (i : X → X → U ̇) (r : (x : X) → i x x) → ∀ {V} → U ⊔ V ′ ̇
identity-data {U} X i r {V} =
 Σ \(j : (x : X) (A : (y : X) → i x y → V ̇)
    → A x (r x) → (y : X) (p : i x y) → A y p)
   → (x : X) (A : (y : X) → i x y → V ̇)
    → (b : A x (r x))
    → j x A b x (r x) ≡ b 

JEq : ∀ {U} → isUnivalent U
    → ∀ {V} (X : U ̇) (A : (Y : U ̇) → X ≃ Y → V ̇)
    → A X (ideq X) → (Y : U ̇) (e : X ≃ Y) → A Y e
JEq {U} ua {V} X A b Y e = transport (A Y) (idtoeq-eqtoid ua X Y e) g
 where
  A' : (Y : U ̇) → X ≡ Y → V ̇
  A' Y p = A Y (idtoeq X Y p)
  b' : A' X refl
  b' = b
  f' : (Y : U ̇) (p : X ≡ Y) → A' Y p
  f' = Jbased X A' b'
  g : A Y (idtoeq X Y (eqtoid ua X Y e))
  g = f' Y (eqtoid ua X Y e)

{- TODO:
JEq-comp : ∀ {U} (ua : isUnivalent U)
    → ∀ {V} (X : U ̇) (A : (Y : U ̇) → X ≃ Y → V ̇)
    → (b : A X (ideq X))
    → JEq ua X A b X (ideq X) ≡ b
JEq-comp ua X A b = ?
-}

\end{code}




Conversely, if the induction principle for equivalences with its
computation rule holds, then univalence follows:

\begin{code}

JEq-converse : ∀ {U}
             → (jeq : ∀ {V} (X : U ̇) (A : (Y : U ̇) → X ≃ Y → V ̇)
                → A X (ideq X) → (Y : U ̇) (e : X ≃ Y) → A Y e)
             → (∀ {V} (X : U ̇) (A : (Y : U ̇) → X ≃ Y → V ̇)
                → (b : A X (ideq X)) → jeq X A b X (ideq X) ≡ b)
             → isUnivalent U
JEq-converse {U} jeq jeq-comp X = g
 where
  φ : (Y : U ̇) → X ≃ Y → X ≡ Y
  φ = jeq X (λ Y p → X ≡ Y) (idp X)
  φc : φ X (ideq X) ≡ idp X
  φc = jeq-comp X (λ Y p → X ≡ Y) (idp X)
  idtoeqφ : (Y : U ̇) (e : X ≃ Y) → idtoeq X Y (φ Y e) ≡ e
  idtoeqφ = jeq X (λ Y e → idtoeq X Y (φ Y e) ≡ e) (ap (idtoeq X X) φc)
  φidtoeq : (Y : U ̇) (p : X ≡ Y) → φ Y (idtoeq X Y p) ≡ p
  φidtoeq X refl = φc
  g : (Y : U ̇) → isEquiv(idtoeq X Y)
  g Y =  (φ Y , idtoeqφ Y) , (φ Y , φidtoeq Y)
  
\end{code}

The following says that if the pair (x,a) is a universal element, then
the natural transformation it induces (namely yoneda-nat {U} {X} {x} a)
has a section and a retraction (which can be taken to be the same
function), and hence is an equivalence. Here having a section or
retraction is data not property:

\begin{code}

universality-section : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                     → is-universal-element (x , a) → (y : X) → hasSection(yoneda-nat A a y) 
universality-section {U} {V} {X} {A} x a u y = s y , φ y
 where
  s : (y : X) → A y → x ≡ y
  s y b = pr₁ (u y b) 
  φ : (y : X) (b : A y) → yoneda-nat A a y (s y b) ≡ b 
  φ y b = pr₂ (u y b)

\end{code}

Actually, it suffices to just give the section, as shown next
(https://github.com/HoTT/book/issues/718#issuecomment-65378867):

\begin{code}

idemp-is-id : ∀ {U} {X : U ̇} {x : X} (η : (y : X) → x ≡ y → x ≡ y) (y : X) (p : x ≡ y)
           → η y (η y p) ≡ η y p → η y p ≡ p
idemp-is-id {U} {X} {x} η y p idemp = cancel-left (
        η x (idp x) ∙ η y p ≡⟨ Hedberg-lemma x η y (η y p) ⟩
        η y (η y p)         ≡⟨ idemp ⟩
        η y p               ≡⟨ (Hedberg-lemma x η y p)⁻¹ ⟩
        η x (idp x) ∙ p     ∎ )

natural-section-isEquiv : ∀ {U V} {X : U ̇} {A : X → V ̇}
                           (x : X) (r : Nat (Id x) A)
                        → ((y : X) → hasSection(r y)) 
                        → ((y : X) → isEquiv(r y))
natural-section-isEquiv {U} {V} {X} {A} x r hass = λ y → (hass y , hasr y)
 where
  s : (y : X) → A y → x ≡ y
  s y = pr₁ (hass y)
  rs : {y : X} (a : A y) → r y (s y a) ≡ a
  rs {y} = pr₂ (hass y)
  η : (y : X) → x ≡ y → x ≡ y
  η y p = s y (r y p)
  idemp : (y : X) (p : x ≡ y) → η y (η y p) ≡ η y p
  idemp y p = ap (s y) (rs (r y p))
  η-is-id : (y : X) (p : x ≡ y) → η y p ≡ p
  η-is-id y p = idemp-is-id η y p (idemp y p)
  hasr : (y : X) → hasRetraction(r y)
  hasr y = s y , η-is-id y

\end{code}

We are interested in this corollary:

\begin{code}

universality-equiv : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                   → is-universal-element (x , a)
                   → (y : X) → isEquiv(yoneda-nat A a y)
universality-equiv {U} {V} {X} {A} x a u = natural-section-isEquiv x (yoneda-nat A a)
                                                                     (universality-section x a u)
\end{code}

The converse is trivial:

\begin{code}

section-universality : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                     → ((y : X) → hasSection(yoneda-nat A a y))
                     → is-universal-element (x , a)
section-universality x a φ y b = pr₁(φ y) b , pr₂(φ y) b

equiv-universality : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                   → ((y : X) → isEquiv(yoneda-nat A a y))
                   → is-universal-element (x , a)
equiv-universality x a φ = section-universality x a (λ y → pr₁ (φ y))

\end{code}

Next we show that a presheaf A is representable iff Σ A is contractible.

\begin{code}

_≊_ : ∀ {U V W} {X : U ̇} → (X → V ̇) → (X → W ̇) → U ⊔ V ⊔ W ̇
A ≊ B = Σ \(η : Nat A B) → ∀ x → isEquiv(η x)

isRepresentable : ∀ {U V} {X : U ̇} → (X → V ̇) → U ⊔ V ̇
isRepresentable A = Σ \x → Id x ≊ A

contr-is-repr : ∀ {U V} {X : U ̇} {A : X → V ̇} → isSingleton (Σ A) → isRepresentable A 
contr-is-repr {U} {V} {X} {A} ((x , a) , cc) = g
 where
  g : Σ \(x : X) → Id x ≊ A
  g = x , (yoneda-nat A a , universality-equiv x a (cc-is-ue A (x , a) cc))

is-repr→isEquiv-yoneda : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (η : Nat (Id x) A) (y : X) 
                        → isEquiv (η y) → isEquiv (yoneda-nat A (yoneda-elem A η) y)
is-repr→isEquiv-yoneda {U} {V} {X} {A} x η y ise =
  equiv-closed-under-∼ (η y) (yoneda-nat A (yoneda-elem A η) y) ise (yoneda-lemma A η y)

repr-is-contr : ∀ {U V} {X : U ̇} {A : X → V ̇} → isRepresentable A → isSingleton (Σ A)
repr-is-contr {U} {V} {X} {A} (x , (η , φ)) = g
 where
  σ : Σ A
  σ = x , yoneda-elem A η
  is-ue-σ : is-universal-element σ
  is-ue-σ = equiv-universality x (yoneda-elem A η) (λ y → is-repr→isEquiv-yoneda x η y (φ y))
  g : Σ \(σ : Σ A) → is-the-only-element σ
  g = σ , ue-is-cc σ is-ue-σ

\end{code}

An immediate consequence is the following characterization of
univalence:

\begin{code}

univalence-via-contractibility : ∀ {U} → isUnivalent U ⇔ ((X : U ̇) → isSingleton (Σ \(Y : U ̇) → X ≃ Y))
univalence-via-contractibility {U} = (f , g)
 where
  f : isUnivalent U → (X : U ̇) → isSingleton (Σ (Eq X))
  f ua X = repr-is-contr (X , (idtoeq X , ua X))

  g : ((X : U ̇) → isSingleton (Σ (Eq X))) → isUnivalent U
  g φ X = universality-equiv X (ideq X) (cc-is-ue (Eq X) (X , ideq X) (isSingleton-isProp (φ X) (X , ideq X)))

\end{code}

The fact that this is the case was announced on 5th August
2014 with the techniques of the HoTT Book
(https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ)),
and the proof given here via Yoneda was announced on 12th May 2015
(http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html).

\begin{code}

paths-from-contractible : ∀ {U} {X : U ̇} (x : X) → isSingleton(paths-from x)
paths-from-contractible x = ((x , idp x) , singleton-types-are-singletons)

paths-to : ∀ {U} {X : U ̇} → X → U ̇
paths-to x = Σ \y → y ≡ x

rc-is-c : ∀ {U} {X Y : U ̇} (r : X → Y) → hasSection r → isSingleton X → isSingleton Y
rc-is-c {U} {X} {Y} r (s , rs) (x , i) = r x , λ y → r x ≡⟨ ap r (i (s y)) ⟩ r (s y) ≡⟨ rs y ⟩ y ∎

pt-pf-equiv : ∀ {U} {X : U ̇} (x : X) → Σ \(f : paths-from x → paths-to x) → isEquiv f
pt-pf-equiv {U} {X} x = f , ((g , fg) , (g , gf))
 where
  f : paths-from x → paths-to x
  f (y , p) = y , (p ⁻¹) 
  g : paths-to x → paths-from x
  g (y , p) = y , (p ⁻¹) 
  fg : f ∘ g ∼ id
  fg (y , p) = ap (λ p → y , p) (⁻¹-involutive p)
  gf : g ∘ f ∼ id
  gf (y , p) = ap (λ p → y , p) (⁻¹-involutive p)
  
paths-to-contractible : ∀ {U} {X : U ̇} (x : X) → isSingleton(paths-to x)
paths-to-contractible x = rc-is-c (pr₁(pt-pf-equiv x))
                                  (pr₁(pr₂((pt-pf-equiv x))))
                                  (paths-from-contractible x)

paths-to-isProp : ∀ {U} {X : U ̇} (x : X) → isProp(paths-to x)
paths-to-isProp x = isSingleton-isProp (paths-to-contractible x)

pbucp' : ∀ {U} (X Y : U ̇) → isProp(X × Y) → (Y → isProp X) × (X → isProp Y)
pbucp' {U} X Y isp =  (λ y x x' → ap pr₁ (isp (x , y) (x' , y))) ,
                      (λ x y y' → ap pr₂ (isp (x , y) (x , y')))

pcubp' : ∀ {U} (X Y : U ̇) → (Y → isProp X) × (X → isProp Y) → isProp(X × Y)
pcubp' X Y (i , j) (x , y) (x' , y') = to-Σ-Id _ (i y x x' , j x _ _)

pcubp : ∀ {U} (X Y : U ̇) → isProp X → isProp Y → isProp(X × Y)
pcubp X Y i j = pcubp' X Y ((λ _ → i) , (λ _ → j))

fiber : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → Y → U ⊔ V ̇
fiber f y = Σ \x → f x ≡ y

isVoevodskyEquiv : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
isVoevodskyEquiv f = ∀ y → isSingleton (fiber f y)

isVoevodskyEquiv-isEquiv : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → isVoevodskyEquiv f → isEquiv f
isVoevodskyEquiv-isEquiv {U} {V} {X} {Y} f φ = (g , fg) , (g , gf)
 where
  φ' : (y : Y) → Σ \(c : Σ \(x : X) → f x ≡ y) → (σ : Σ \(x : X) → f x ≡ y) → c ≡ σ
  φ' = φ
  c : (y : Y) → Σ \(x : X) → f x ≡ y
  c y = pr₁(φ y)
  d : (y : Y) → (σ : Σ \(x : X) → f x ≡ y) → c y ≡ σ
  d y = pr₂(φ y)
  g : Y → X
  g y = pr₁(c y)
  fg : (y : Y) → f (g y) ≡ y
  fg y = pr₂(c y)
  e : (x : X) → g(f x) , fg (f x) ≡ x , refl
  e x = d (f x) (x , refl)
  gf : (x : X) → g (f x) ≡ x
  gf x = ap pr₁ (e x)

\end{code}

The following has a proof from function extensionality (see e.g. HoTT
Book), but it has a more direct proof from univalence:

\begin{code}

isEquiv-isVoevodskyEquiv : ∀ {U} → isUnivalent U → {X Y : U ̇} (f : X → Y)
                         → isEquiv f → isVoevodskyEquiv f
isEquiv-isVoevodskyEquiv {U} ua {X} {Y} f ise = g Y (f , ise)
 where
  A : (Y : U ̇) → X ≃ Y → U ̇
  A Y (f , ise) = isVoevodskyEquiv f
  b : A X (ideq X)
  b = paths-to-contractible
  g :  (Y : U ̇) (e : X ≃ Y) → A Y e
  g = JEq ua X A b

\end{code}

\begin{code}

isEmbedding : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
isEmbedding f = ∀ y → isProp(fiber f y)

embedding-lc : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → isEmbedding f → left-cancellable f
embedding-lc f e {x} {x'} p = ap pr₁ (e (f x) (x , refl) (x' , (p ⁻¹)))

id-isEmbedding : ∀ {U} {X : U ̇} → isEmbedding (id {U} {X})
id-isEmbedding = paths-to-isProp

isEmbedding' : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
isEmbedding' f = ∀ x x' → isEquiv (ap f {x} {x'})

fiber' : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → Y → U ⊔ V ̇
fiber' f y = Σ \x → y ≡ f x

fiber-lemma : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) (y : Y) → fiber f y ≃ fiber' f y
fiber-lemma f y = g , (h , gh) , (h , hg)
 where
  g : fiber f y → fiber' f y
  g (x , p) = x , (p ⁻¹)
  h : fiber' f y → fiber f y
  h (x , p) = x , (p ⁻¹)
  hg : ∀ σ → h(g σ) ≡ σ
  hg (x , refl) = refl
  gh : ∀ τ → g(h τ) ≡ τ
  gh (x , refl) = refl
  
embedding-embedding' : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → isEmbedding f → isEmbedding' f
embedding-embedding' {U} {V} {X} {Y} f ise = g
 where
  b : (x : X) → isSingleton(fiber f (f x))
  b x = (x , idp (f x)) , ise (f x) (x , idp (f x))
  c : (x : X) → isSingleton(fiber' f (f x))
  c x = rc-is-c (pr₁ (fiber-lemma f (f x))) (pr₁(pr₂(fiber-lemma f (f x)))) (b x)
  g : (x x' : X) → isEquiv(ap f {x} {x'})
  g x = universality-equiv x refl (cc-is-ue (λ x' → f x ≡ f x') (pr₁(c x)) (pr₂(c x))) 

embedding'-embedding : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) → isEmbedding' f → isEmbedding f
embedding'-embedding {U} {V} {X} {Y} f ise = g
 where
  e : (x x' : X) → is-the-only-element (x , idp (f x))
  e x x' = ue-is-cc (x , idp (f x)) (equiv-universality x (idp (f x)) (ise x))
  h : (x : X) → isProp (fiber' f (f x))
  h x σ τ = σ ≡⟨ (e x (pr₁ σ) σ)⁻¹ ⟩ (x , idp (f x)) ≡⟨ e x (pr₁ τ) τ ⟩ τ ∎  
  g' : (y : Y) → isProp (fiber' f y)
  g' y (x , p) = transport (λ y → isProp (Σ \(x' : X) → y ≡ f x')) (p ⁻¹) (h x) (x , p)
  g : (y : Y) → isProp (fiber f y)
  g y = lcmtpip (pr₁ (fiber-lemma f y)) (section-lc _ (pr₂ (pr₂ (fiber-lemma f y)))) (g' y)

\end{code}

We next consider sums and products of families of left-cancellable
maps, which again give left-cancellable maps.

\begin{code}

NatΣ : ∀ {U V W} {X : U ̇} {A : X → V ̇} {B : X → W ̇} → Nat A B → Σ A → Σ B
NatΣ ζ (x , a) = (x , ζ x a)

NatΣ-lc : ∀ {U V W} (X : U ̇) (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
        → ((x : X) → left-cancellable(ζ x)) → left-cancellable(NatΣ ζ)
NatΣ-lc X A B ζ ζ-lc {(x , a)} {(y , b)} pq = g
  where
    p : x ≡ y
    p = pr₁ (from-Σ-Id B pq)
    η : Nat (Id x) B
    η = yoneda-nat B (ζ x a)
    q : η y p ≡ ζ y b
    q = pr₂ (from-Σ-Id B pq)
    θ : Nat (Id x) A
    θ = yoneda-nat A a
    η' : Nat (Id x) B
    η' y p = ζ y (θ y p)
    r : η' ≈ η
    r = yoneda-elem-lc η' η (idp (ζ x a)) 
    r' : ζ y (θ y p) ≡ η y p
    r' = r y p
    s : ζ y (θ y p) ≡ ζ y b
    s = r' ∙ q
    t : θ y p ≡ b
    t = ζ-lc y s
    g : x , a ≡ y , b
    g = to-Σ-Id A (p , t)

NatΠ : ∀ {U V W} {X : U ̇} {A : X → V ̇} {B : X → W ̇} → Nat A B → Π A → Π B
NatΠ f g x = f x (g x) -- (S combinator from combinatory logic!)

NatΠ-lc : ∀ {U V W} {X : U ̇} {A : X → V ̇} {B : X → W ̇} (f : Nat A B)
    → ((x : X) → left-cancellable(f x))
    → {g g' : Π A} → NatΠ f g ≡ NatΠ f g' → g ∼ g'
NatΠ-lc f flc {g} {g'} p x = flc x (q x)
 where
   q : ∀ x → f x (g x) ≡ f x (g' x)
   q = happly (NatΠ f g) (NatΠ f g') p

isProp-isProp : ∀ {U} {X : U ̇} → FunExt U U → isProp(isProp X)
isProp-isProp {U} {X} fe f g = claim₁
 where
  lemma : isSet X
  lemma = prop-isSet f
  claim : (x y : X) → f x y ≡ g x y
  claim x y = lemma (f x y) (g x y)
  claim₀ : (x : X) → f x ≡ g x 
  claim₀ x = funext fe (claim x) 
  claim₁ : f ≡ g
  claim₁  = funext fe claim₀

isProp-isSingleton : ∀ {U} {X : U ̇} → FunExt U U → isProp(isSingleton X)
isProp-isSingleton {U} {X} fe (x , φ) (y , γ) = to-Σ-Id _ (φ y , funext fe λ z → iss {y} {z} _ _)
 where
  isp : isProp X
  isp = isSingleton-isProp (y , γ)
  iss : isSet X
  iss = prop-isSet isp

subtype-of-set-isSet : ∀ {U V} {X : U ̇} {Y : V ̇} (m : X → Y)
                     → left-cancellable m → isSet Y → isSet X
subtype-of-set-isSet {U} {V} {X} m i h = path-collapsible-isSet (f , g)
 where
  f : {x x' : X} → x ≡ x' → x ≡ x'
  f r = i (ap m r)
  g : {x x' : X} (r s : x ≡ x') → f r ≡ f s
  g r s = ap i (h (ap m r) (ap m s))

\end{code}

\begin{code}

ip-ie-idtofun : ∀ {U} (fe : FunExt U U) (X Y : U ̇) (p : X ≡ Y) → isProp(isEquiv(idtofun X Y p))
ip-ie-idtofun {U} fe X = Jbased X B go
 where
   B : (Y : U ̇) → X ≡ Y → U ̇
   B Y p = isProp(isEquiv(idtofun X Y p))
   A = Σ \(f : X → X) → f ≡ id
   a : isProp A
   a = isSingleton-isProp (paths-to-contractible id)
   A' = Σ \(f : X → X) → f ∼ id
   η : (f : X → X) → f ∼ id → f ≡ id
   η f = funext fe
   η-lc : (f : X → X) → left-cancellable(η f)
   η-lc f = funext-lc fe f id
   h : A' → A
   h = NatΣ η
   h-lc : left-cancellable h
   h-lc = NatΣ-lc (X → X) (λ f → f ∼ id) (λ f → f ≡ id) η η-lc
   b : isProp A'
   b = lcmtpip h h-lc a
   go : isProp(A' × A')
   go = pcubp A' A' b b

jip : ∀ {U} → isUnivalent U → FunExt U U → {X Y : U ̇} 
   → (f : X → Y) → isProp(isEquiv f) 
jip {U} ua fe {X} {Y} f ije = h ije
  where
    e : X ≃ Y
    e = (f , ije)
    p : X ≡ Y
    p = eqtoid ua X Y e
    f' : X → Y
    f' = idtofun X Y p
    h' : isProp(isEquiv f')
    h' = ip-ie-idtofun fe X Y p
    ije' : isEquiv f'
    ije' = idtofun-isEquiv X Y p
    e' : X ≃ Y
    e' = f' , ije'
    q : e' ≡ e
    q = idtoeq-eqtoid ua X Y e
    q₁ : f' ≡ f
    q₁ = ap pr₁ q
    h : isProp(isEquiv f)
    h = yoneda-nat (λ f → isProp(isEquiv f)) h' f q₁

\end{code}

If the codomain of a left-cancellable function is a proposition, so is
its domain. 

\begin{code}

isUnivalent-idtoeq-lc : ∀ {U} → isUnivalent U → (X Y : U ̇) → left-cancellable(idtoeq X Y)
isUnivalent-idtoeq-lc ua X Y = section-lc (idtoeq X Y) (pr₂ (ua X Y))

\end{code}

Formulation of the K axiom for a universe U.

\begin{code}

K : ∀ U → U ′ ̇
K U = (X : U ̇) → isSet X

\end{code}

What we proved above using univalence also follows from K:

\begin{code}

K-idtofun-lc : ∀ {U} → K (U ′) 
            → {X : U ̇} (x y : X) (A : X → U ̇) → left-cancellable(idtofun (Id x y) (A y))
K-idtofun-lc {U} k {X} x y A {p} {q} r = k (Set U) p q

s-lc-e : ∀ {U V} → {X : U ̇} {Y : V ̇} (f : X → Y) → left-cancellable f → isSet Y → isEmbedding f
s-lc-e {U} {V} {X} {Y} f f-lc iss y (x , p) (x' , p') = to-Σ-Id (λ x → f x ≡ y) (r , q)
 where
   r : x ≡ x'
   r = f-lc (p ∙ (p' ⁻¹))
   q : yoneda-nat (λ x → f x ≡ y) p x' r ≡ p'
   q = iss (yoneda-nat (λ x → f x ≡ y) p x' r) p'

K-lc-e : ∀ {U V} → {X : U ̇} {Y : V ̇} (f : X → Y) → left-cancellable f → K V → isEmbedding f
K-lc-e {U} {V} {X} {Y} f f-lc k = s-lc-e f f-lc (k Y)

\end{code}

The map eqtofun is left-cancellable assuming univalence (and function
extensionality, which is a consequence of univalence, but we don't
bother):

\begin{code}

eqtofun-lc : ∀ {U} → isUnivalent U → FunExt U U 
           → (X Y : U ̇) → left-cancellable(eqtofun X Y)
eqtofun-lc ua fe X Y {f , jef} {g , jeg} p = go
 where
  q : yoneda-nat isEquiv jef g p ≡ jeg
  q = jip ua fe g (yoneda-nat isEquiv jef g p) jeg
  go : f , jef ≡ g , jeg
  go = to-Σ-Id isEquiv (p , q)
  
\end{code}

The map idtofun is left-cancellable assuming univalence (and funext):

\begin{code}

isUnivalent-idtofun-lc : ∀ {U} → isUnivalent U → FunExt U U → (X Y : U ̇) 
                       → left-cancellable(idtofun X Y)
isUnivalent-idtofun-lc  ua fe X Y = 
   lcccomp (idtoeq X Y) (eqtofun X Y) (isUnivalent-idtoeq-lc ua X Y) (eqtofun-lc ua fe X Y)

\end{code}

More generally:

\begin{code}

pr₁-embedding : ∀ {U V} {X : U ̇} {Y : X → V ̇}
              → ((x : X) → isProp(Y x))
              → isEmbedding (pr₁ {U} {V} {X} {Y})
pr₁-embedding f x ((.x , y') , refl) ((.x , y'') , refl) = g
 where
  g : (x , y') , refl ≡ (x , y'') , refl
  g = ap (λ y → (x , y) , refl) (f x y' y'')

pr₁-lc : ∀ {U V} {X : U ̇} {Y : X → V ̇} → ({x : X} → isProp(Y x)) → left-cancellable pr₁
pr₁-lc f {u} {v} r = embedding-lc pr₁ (pr₁-embedding (λ x → f {x})) r

pr₁-embedding-converse : ∀ {U V} {X : U ̇} {Y : X → V ̇}
                       → isEmbedding (pr₁ {U} {V} {X} {Y})
                       → ((x : X) → isProp(Y x))
pr₁-embedding-converse {U} {V} {X} {Y} ie x = go
  where
    e : Σ Y → X
    e = pr₁ {U} {V} {X} {Y}
    isp : isProp(fiber e x)
    isp = ie x
    s : Y x → fiber e x
    s y = (x , y) , refl
    r : fiber e x → Y x
    r ((.x , y) , refl) = y
    rs : (y : Y x) → r(s y) ≡ y
    rs y = refl
    go : isProp(Y x)
    go = lcmtpip s (section-lc s (r , rs)) isp

subset-of-set-isSet : ∀ {U V} (X : U ̇) (Y : X → V ̇) 
                    → isSet X → ({x : X} → isProp(Y x)) → isSet(Σ \(x : X) → Y x)
subset-of-set-isSet X Y h p = subtype-of-set-isSet pr₁ (pr₁-lc p) h

isSet-exponential-ideal : ∀ {U V} → FunExt U V → {X : U ̇} {A : X → V ̇} 
                        → ((x : X) → isSet(A x)) → isSet(Π A) 
isSet-exponential-ideal {U} {V} fe {X} {A} isa {f} {g} = b
 where
  a : isProp (f ∼ g)
  a p q = funext fe λ x → isa x (p x) (q x)
  b : isProp(f ≡ g)
  b = lcmtpip (happly f g) (section-lc (happly f g) (pr₂ (fe f g))) a

isProp-closed-under-Σ : ∀ {U V} {X : U ̇} {A : X → V ̇} 
                    → isProp X → ((x : X) → isProp(A x)) → isProp(Σ A)
isProp-closed-under-Σ {U} {V} {X} {A} isx isa (x , a) (y , b) = 
                    Σ-≡ x y a b (isx x y) (isa y (transport A (isx x y) a) b)

isProp-exponential-ideal : ∀ {U V} → FunExt U V → {X : U ̇} {A : X → V ̇} 
                        → ((x : X) → isProp(A x)) → isProp(Π A) 
isProp-exponential-ideal {U} {V} fe {X} {A} isa f g = funext fe (λ x → isa x (f x) (g x))

\end{code}

The following code is used to make Agda work with the constructions we
have given. We make the implicit arguments explicit in the definition
of isSet.

\begin{code}

isSet' : ∀ {U} → U ̇ → U ̇
isSet' X = (x y : X) → isProp(x ≡ y)

isSet'-isSet : ∀ {U} {X : U ̇} → isSet' X → isSet X
isSet'-isSet s {x} {y} = s x y

isSet-isSet' : ∀ {U} {X : U ̇} → isSet X → isSet' X
isSet-isSet' s x y = s {x} {y}

isProp-isSet' : ∀ {U} {X : U ̇} → FunExt U U → isProp (isSet' X)
isProp-isSet' fe = isProp-exponential-ideal fe
                    (λ x → isProp-exponential-ideal fe
                              (λ y → isProp-isProp fe))
propExt : ∀ U → U ′ ̇ 
propExt U = {P Q : U ̇} → isProp P → isProp Q → (P → Q) → (Q → P) → P ≡ Q

Prop : ∀ {U} → U ′ ̇
Prop {U} = Σ \(P : U ̇) → isProp P 

_holds : ∀ {U} → Prop → U ̇
_holds = pr₁

holdsIsProp : ∀ {U} → (p : Prop {U}) → isProp (p holds)
holdsIsProp = pr₂

PropExt : ∀ {U} → FunExt U U → propExt U → {p q : Prop {U}}
        → (p holds → q holds) → (q holds → p holds) → p ≡ q
PropExt {U} fe pe {p} {q} f g =
        to-Σ-Id isProp ((pe (holdsIsProp p) (holdsIsProp q) f g) , isProp-isProp fe _ _)

Prop-isSet : ∀ {U} → FunExt U U → propExt U → isSet (Prop {U})
Prop-isSet {U} fe pe = path-collapsible-isSet pc
 where
  A : (p q : Prop) → U ̇
  A p q = (p holds → q holds) × (q holds → p holds) 
  A-isProp : (p q : Prop) → isProp(A p q)
  A-isProp p q = isProp-closed-under-Σ (isProp-exponential-ideal fe (λ _ → holdsIsProp q)) 
                                       (λ _ → isProp-exponential-ideal fe (λ _ → holdsIsProp p)) 
  g : (p q : Prop) → p ≡ q → A p q
  g p q e = (b , c)
   where
    a : p holds ≡ q holds
    a = ap _holds e
    b : p holds → q holds
    b = transport (λ X → X) a
    c : q holds → p holds
    c = transport (λ X → X) (a ⁻¹)
  h  : (p q : Prop) → A p q → p ≡ q 
  h p q (u , v) = PropExt fe pe u v
  f  : (p q : Prop) → p ≡ q → p ≡ q
  f p q e = h p q (g p q e)
  constant-f : (p q : Prop) (d e : p ≡ q) → f p q d ≡ f p q e 
  constant-f p q d e = ap (h p q) (A-isProp p q (g p q d) (g p q e))
  pc : {p q : Prop} → Σ \(f : p ≡ q → p ≡ q) → constant f
  pc {p} {q} = (f p q , constant-f p q)

neg-isProp : ∀ {U} {X : U ̇} → FunExt U U₀ → isProp(¬ X)
neg-isProp fe u v = funext fe (λ x → 𝟘-elim (u x)) 

disjoint-images : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : W ̇} → (X → A) → (Y → A) → U ⊔ V ⊔ W ̇
disjoint-images f g = ∀ x y → f x ≢ g y

disjoint-cases-embedding : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : W ̇} (f : X → A) (g : Y → A)
                         → isEmbedding f → isEmbedding g → disjoint-images f g
                         → isEmbedding (cases f g)
disjoint-cases-embedding {U} {V} {W} {X} {Y} {A} f g ef eg d = go
  where
   go : (a : A) (σ τ : Σ \(z : X + Y) → cases f g z ≡ a) → σ ≡ τ
   go a (inl x , p) (inl x' , p') = r
     where
       q : x , p ≡ x' , p'
       q = ef a (x , p) (x' , p')
       h : fiber f a → fiber (cases f g) a
       h (x , p) = inl x , p
       r : inl x , p ≡ inl x' , p'
       r = ap h q
   go a (inl x , p) (inr y  , q) = 𝟘-elim (d x y (p ∙ q ⁻¹))
   go a (inr y , q) (inl x  , p) = 𝟘-elim (d x y (p ∙ q ⁻¹))
   go a (inr y , q) (inr y' , q') = r
     where
       p : y , q ≡ y' , q'
       p = eg a (y , q) (y' , q')
       h : fiber g a → fiber (cases f g) a
       h (y , q) = inr y , q
       r : inr y , q ≡ inr y' , q'
       r = ap h p

\end{code}

To use propositional truncation, one needs to assume an element of
PropTrunc, which is a postulated type with no postulated element. This
is use to keep track of which modules or functions depend on
propositional truncation.

\begin{code}

postulate PropTrunc : U₀ ̇

module PropositionalTruncation (pt : PropTrunc) where

 postulate
   ∥_∥ : ∀ {U} → U ̇ → U ̇
   ptisp : ∀ {U} {X : U ̇} → isProp ∥ X ∥
   ∣_∣ : ∀ {U} {X : U ̇} → X → ∥ X ∥
   ptrec : ∀ {U V} {X : U ̇} {Y : V ̇} → isProp Y → (X → Y) → ∥ X ∥ → Y

 isSingleton'-isProp : ∀ {U} {X : U ̇} → FunExt U U → isProp(isProp X × ∥ X ∥)
 isSingleton'-isProp fe = isProp-closed-under-Σ (isProp-isProp fe) (λ _ → ptisp)

 c-es₁ : ∀ {U} {X : U ̇} → isSingleton X ⇔ isProp X × ∥ X ∥
 c-es₁ {U} {X} = f , g
  where
   f : isSingleton X → isProp X × ∥ X ∥ 
   f (x , φ) = isSingleton-isProp (x , φ) , ∣ x ∣
   
   g : isProp X × ∥ X ∥ → isSingleton X
   g (i , s) = ptrec i id s , i (ptrec i id s)
   
 ptfunct : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → ∥ X ∥ → ∥ Y ∥
 ptfunct f = ptrec ptisp (λ x → ∣ f x ∣)

 ∃ : ∀ {U V} {X : U ̇} → (Y : X → V ̇) → U ⊔ V ̇
 ∃ Y = ∥ Σ Y ∥

 _∨_ : ∀ {U} {V} → U ̇ → V ̇ → U ⊔ V ̇
 P ∨ Q = ∥ P + Q ∥

 left-fails-then-right-holds : ∀ {U} {V} {P : U ̇} {Q : V ̇} → isProp Q → P ∨ Q → ¬ P → Q
 left-fails-then-right-holds i d u = ptrec i (λ d → Left-fails-then-right-holds d u) d

 right-fails-then-left-holds : ∀ {U} {V} {P : U ̇} {Q : V ̇} → isProp P → P ∨ Q → ¬ Q → P
 right-fails-then-left-holds i d u = ptrec i (λ d → Right-fails-then-left-holds d u) d

 pt-gdn : ∀ {U} {X : U ̇} → ∥ X ∥ → ∀ {V} (P : V ̇) → isProp P → (X → P) → P
 pt-gdn {U} {X} s {V} P isp u = ptrec isp u s

 gdn-pt : ∀ {U} {X : U ̇} → (∀ {V} (P : V ̇) → isProp P → (X → P) → P) → ∥ X ∥ 
 gdn-pt {U} {X} φ = φ ∥ X ∥ ptisp ∣_∣

 pt-dn : ∀ {U} {X : U ̇} → ∥ X ∥ → ¬¬ X
 pt-dn s = pt-gdn s 𝟘 𝟘-isProp

 binary-choice : ∀ {U V} {X : U ̇} {Y : V ̇} → ∥ X ∥ → ∥ Y ∥ → ∥ X × Y ∥
 binary-choice s t = ptrec ptisp (λ x → ptrec ptisp (λ y → ∣ x , y ∣) t) s
 
 infixr 0 _∨_
 infix 0 ∥_∥

\end{code}

Or we can work with propositional truncation as an assumption, but the
drawback is that we can only eliminate in the same universe we
truncate, at least if we don't want to pass the target universe as an
extra parameter in everything. So we are not using this anymore.

\begin{code}

propositional-truncations-exist : ∀ U V → U ′ ⊔ V ′ ̇
propositional-truncations-exist U V = (X : U ̇) → Σ \(X' : U ̇) → isProp X' × (X → X')
                                        × ((P : V ̇) → isProp P → (X → P) → X' → P)

propositional-truncations-exist' : ∀ U → U ′ ̇
propositional-truncations-exist' U = propositional-truncations-exist U U

module PropositionalTruncation' (pt : ∀ U → propositional-truncations-exist' U) where

 ∥_∥ : ∀ {U} → U ̇ → U ̇
 ∥ X ∥ = pr₁ (pt (universeOf X) X)

 ptisp : ∀ {U} {X : U ̇} → isProp(∥ X ∥)
 ptisp {U} {X} = pr₁(pr₂(pt (universeOf X) X))

 ∣_∣ : ∀ {U} {X : U ̇} → X → ∥ X ∥
 ∣ x ∣ = pr₁(pr₂(pr₂(pt (universeOf(typeOf x)) (typeOf x)))) x

 ptrec : ∀ {U} {X Y : U ̇} → isProp Y → (X → Y) → ∥ X ∥ → Y
 ptrec {U} {X} {Y} isp f = pr₂(pr₂(pr₂(pt (universeOf X) X))) Y isp f

 ptfunct : ∀ {U} {X Y : U ̇} → (X → Y) → ∥ X ∥ → ∥ Y ∥
 ptfunct f = ptrec ptisp (λ x → ∣ f x ∣)

 ∃ : ∀ {U V} {X : U ̇} → (Y : X → V ̇) → U ⊔ V ̇
 ∃ Y = ∥ Σ Y ∥

 _∨_ : ∀ {U} {V} → U ̇ → V ̇ → U ⊔ V ̇
 P ∨ Q = ∥ P + Q ∥

 infixr 0 _∨_
 infix 0 ∥_∥

\end{code}

A main application of propositional truncations is to be able to
define images and surjections:

\begin{code}

module ImageAndSurjection (pt : PropTrunc) where

 open PropositionalTruncation (pt)

 image : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
 image f = Σ \y → ∃ \x → f x ≡ y

 restriction : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
            → image f → Y
 restriction f (y , _) = y

 restriction-embedding : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                      → isEmbedding(restriction f)
 restriction-embedding f = pr₁-embedding (λ y → ptisp)


 corestriction : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
             → X → image f
 corestriction f x = f x , ∣ x , refl ∣

\end{code}

TODO: a map is an embedding iff its corestriction is an equivalence.

\begin{code}

 isSurjection : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
 isSurjection f = ∀ y → ∃ \x → f x ≡ y

 c-es  :  ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) 
          → isVoevodskyEquiv f ⇔ isEmbedding f × isSurjection f
 c-es f = g , h
  where
   g : isVoevodskyEquiv f → isEmbedding f × isSurjection f 
   g i = (λ y → pr₁(pr₁ c-es₁ (i y))) , (λ y → pr₂(pr₁ c-es₁ (i y)))
   
   h : isEmbedding f × isSurjection f → isVoevodskyEquiv f
   h (e , s) = λ y → pr₂ c-es₁ (e y , s y)

 corestriction-surjection : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                         → isSurjection (corestriction f)
 corestriction-surjection f (y , s) = ptfunct g s
  where
   g : (Σ \x → f x ≡ y) → Σ \x → corestriction f x ≡ y , s
   g (x , p) = x , to-Σ-Id (λ y → ∥ Σ (λ x → f x ≡ y) ∥) (p , (ptisp _ _))

 pt-is-surjection : ∀ {U} {X : U ̇} → isSurjection(λ(x : X) → ∣ x ∣)
 pt-is-surjection t = ptrec ptisp (λ x → ∣ x , ptisp (∣ x ∣) t ∣) t

\end{code}

Surjections can be characterized as follows, modulo size:

\begin{code}

 imageInduction : ∀ {W U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ⊔ W ′ ̇
 imageInduction {W} {U} {V} {X} {Y} f =
                (P : Y → W ̇) → ((y : Y) → isProp(P y)) → ((x : X) → P(f x)) → (y : Y) → P y

 surjection-induction : ∀ {W U V} {X : U ̇} {Y : V ̇} (f : X → Y) 
                      → isSurjection f → imageInduction {W} f 
 surjection-induction f is P isp a y = ptrec (isp y)
                                             (λ σ → transport P (pr₂ σ) (a (pr₁ σ)))
                                             (is y)                

 image-surjection-converse : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) 
                           → imageInduction f → isSurjection f 
 image-surjection-converse f is' = is' (λ y → ∥ Σ (λ x → f x ≡ y) ∥)
                                       (λ y → ptisp)
                                       (λ x → ∣ x , refl ∣)

 image-induction : ∀ {W U V} {X : U ̇} {Y : V ̇}
                 (f : X → Y) (P : image f → W ̇)
               → (∀ y' → isProp(P y'))
               → (∀ x → P(corestriction f x))
               → ∀ y' → P y'
 image-induction f = surjection-induction (corestriction f)
                                          (corestriction-surjection f)

 retraction-surjection : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) 
                       → hasSection f → isSurjection f 
 retraction-surjection {U} {V} {X} f φ y = ∣ pr₁ φ y , pr₂ φ y ∣

\end{code}

We definitely need to make the notation more uniform!

Excluded middle (EM) is not provable or disprovable. However, we do
have that there is no truth value other than false (⊥) or true (⊤),
which we refer to as the density of the decidable truth values.

\begin{code}

sum-of-contradictory-props : ∀ {U V} {P : U ̇} {Q : V ̇}
                           → isProp P → isProp Q → (P → Q → 𝟘) → isProp(P + Q)
sum-of-contradictory-props {U} {V} {P} {Q} isp isq f = go
  where
   go : (x y : P + Q) → x ≡ y
   go (inl p) (inl p') = ap inl (isp p p')
   go (inl p) (inr q)  = 𝟘-elim (f p q)
   go (inr q) (inl p)  = 𝟘-elim (f p q)
   go (inr q) (inr q') = ap inr (isq q q')

decidable-isProp : ∀ {U} {P : U ̇} → FunExt U U₀ → isProp P → isProp(P + ¬ P)
decidable-isProp fe₀ isp = sum-of-contradictory-props
                             isp
                             (isProp-exponential-ideal fe₀ λ _ → 𝟘-isProp)
                             (λ p u → u p)

EM : ∀ U → U ′ ̇
EM U = (P : U ̇) → isProp P → P + ¬ P

WEM : ∀ U → U ′ ̇
WEM U = (P : U ̇) → isProp P → ¬ P + ¬¬ P

DNE : ∀ U → U ′ ̇
DNE U = (P : U ̇) → isProp P → ¬¬ P → P

EM-DNE : ∀ {U} → EM U → DNE U
EM-DNE em P isp φ = cases (λ p → p) (λ u → 𝟘-elim (φ u)) (em P isp)

DNE-EM : ∀ {U} → FunExt U U₀ → DNE U → EM U
DNE-EM fe dne P isp = dne (P + ¬ P)
                          (decidable-isProp fe isp)
                          (λ u → u (inr (λ p → u (inl p))))

module _ (pt : PropTrunc) where

 open PropositionalTruncation pt

 double-negation-is-truncation-gives-DNE : ∀ {U} → ((X : U ̇) → ¬¬ X → ∥ X ∥) → DNE U
 double-negation-is-truncation-gives-DNE {U} f P isp u = ptrec isp id (f P u)
 
fem-proptrunc : ∀ {U} → FunExt U U₀ → EM U → propositional-truncations-exist U U
fem-proptrunc fe em X = ¬¬ X ,
                    (isProp-exponential-ideal fe (λ _ → 𝟘-isProp) ,
                     (λ x u → u x) ,
                     λ P isp u φ → EM-DNE em P isp (¬¬-functor u φ))

no-props-other-than-𝟘-or-𝟙 : propExt U₀ → ¬ Σ \(P : U₀ ̇) → isProp P × (P ≢ 𝟘) × (P ≢ 𝟙)  
no-props-other-than-𝟘-or-𝟙 pe (P , (isp , f , g)) = φ u
 where
   u : ¬ P
   u p = g l
     where
       l : P ≡ 𝟙
       l = pe isp 𝟙-isProp unique-to-𝟙 (λ _ → p)
   φ : ¬¬ P
   φ u = f l
     where
       l : P ≡ 𝟘
       l = pe isp 𝟘-isProp u 𝟘-elim

⊥ ⊤ : Prop
⊥ = 𝟘 , 𝟘-isProp   -- false
⊤ = 𝟙 , 𝟙-isProp   -- true

𝟘-is-not-𝟙 : 𝟘 ≢ 𝟙
𝟘-is-not-𝟙 p = idtofun 𝟙 𝟘 (p ⁻¹) *

⊥≠⊤ : ⊥ ≢ ⊤
⊥≠⊤ p = 𝟘-is-not-𝟙 (ap pr₁ p)

no-truth-values-other-than-⊥-or-⊤ : FunExt U₀ U₀ → propExt U₀
                                   → ¬ Σ \(p : Prop) → (p ≢ ⊥) × (p ≢ ⊤)  
no-truth-values-other-than-⊥-or-⊤ fe pe ((P , isp) , (f , g)) = φ u
 where
   u : ¬ P
   u p = g l
     where
       l : (P , isp) ≡ ⊤
       l = PropExt fe pe unique-to-𝟙 (λ _ → p)
   φ : ¬¬ P
   φ u = f l
     where
       l : (P , isp) ≡ ⊥
       l = PropExt fe pe u unique-from-𝟘

open import Two

⊥-⊤-density : FunExt U₀ U₀ → propExt U₀ → (f : Prop → 𝟚)
            → f ⊥ ≡ ₁ → f ⊤ ≡ ₁ → (p : Prop) → f p ≡ ₁
⊥-⊤-density fe pe f r s p = Lemma[b≢₀→b≡₁] a
 where
    a : f p ≢ ₀
    a t = no-truth-values-other-than-⊥-or-⊤ fe pe (p , (b , c))
      where
        b : p ≢ ⊥
        b u = zero-is-not-one (t ⁻¹ ∙ ap f u ∙ r)
        c : p ≢ ⊤
        c u = zero-is-not-one (t ⁻¹ ∙ ap f u ∙ s)

𝟚inProp : 𝟚 → Prop
𝟚inProp ₀ = ⊥
𝟚inProp ₁ = ⊤

𝟚inProp-embedding : FunExt U₀ U₀ → propExt U₀ → isEmbedding 𝟚inProp
𝟚inProp-embedding fe pe (P , isp) (₀ , p) (₀ , q) = Σ-≡ ₀ ₀ p q refl (Prop-isSet fe pe p q)
𝟚inProp-embedding fe pe (P , isp) (₀ , p) (₁ , q) = 𝟘-elim (⊥≠⊤ (p ∙ q ⁻¹))
𝟚inProp-embedding fe pe (P , isp) (₁ , p) (₀ , q) = 𝟘-elim (⊥≠⊤ (q ∙ p ⁻¹))
𝟚inProp-embedding fe pe (P , isp) (₁ , p) (₁ , q) = Σ-≡ ₁ ₁ p q refl (Prop-isSet fe pe p q)

\end{code}

More about retracts.

\begin{code}

rid : ∀ {U} {X : U ̇} → retract X of X
rid = id , (id , λ x → refl)

rexp : ∀ {U V W T} {X : U ̇} {Y : V ̇} {X' : W ̇} {Y' : T ̇} → FunExt U T
    → retract X of X' → retract Y' of Y → retract (X → Y') of (X' → Y)
rexp {U} {V} {W} {T} {X} {Y} {X'} {Y'} fe (rx , (sx , rsx)) (ry , (sy , rsy)) = (r , (s , rs))
 where
  r : (X' → Y) → X → Y'
  r f x = ry (f (sx x))
  s : (X → Y') → X' → Y
  s f' x' = sy (f' (rx x'))
  rs' : (f' : X → Y') (x : X) → ry (sy (f' (rx (sx x)))) ≡ f' x
  rs' f' x = rsy (f' (rx (sx x))) ∙ ap f' (rsx x)
  rs : (f' : X → Y') → r (s f') ≡ f'
  rs f' = funext fe (rs' f')

rpe : ∀ {U V W} {X : U ̇} {Y : V ̇} {Y' : W ̇} → FunExt U W
    → retract Y' of Y → retract (X → Y') of (X → Y)
rpe fe = rexp fe rid

crpe : ∀ {U V W} {X : U ̇} {Y : V ̇} {X' : W ̇} → FunExt U V
    → retract X of X' → retract (X → Y) of (X' → Y)
crpe fe rx = rexp fe rx rid

pdrc : ∀ {U V} {X : U ̇} {Y : V ̇} → X → retract Y of (X → Y)
pdrc x = ((λ f → f x) , ((λ y x → y) , λ y → refl))

retraction : ∀ {U V} {X : U ̇} {Y : V ̇} → (f : X → Y) → U ⊔ V ̇
retraction f = ∀ y → Σ \x → f x ≡ y

retract_Of_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
retract Y Of X = Σ \(f : X → Y) → retraction f

retract-of-retract-Of : ∀ {U V} {X : U ̇} {Y : V ̇} → retract Y of X → retract Y Of X
retract-of-retract-Of {U} {V} {X} {Y} (f , φ)= (f , hass)
 where
  hass : (y : Y) → Σ \(x : X) → f x ≡ y
  hass y = pr₁ φ y , pr₂ φ y

retract-Of-retract-of : ∀ {U V} {X : U ̇} {Y : V ̇} → retract Y Of X → retract Y of X
retract-Of-retract-of {U} {V} {X} {Y} (f , hass) = (f , φ)
 where
  φ : Σ \(s : Y → X) → f ∘ s ∼ id
  φ = (λ y → pr₁ (hass y)) , λ y → pr₂ (hass y)

retracts-compose : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇}
                 → retract Y of X → retract Z of Y → retract Z of X
retracts-compose (r , (s , rs)) (r' , (s' , rs')) = r' ∘ r ,
                                                    (s ∘ s' , λ z → ap r' (rs (s' z)) ∙ rs' z)
retracts-of-closed-under-exponentials : ∀ {U V W} {X : U ̇} {Y : V ̇} {B : W ̇} → FunExt W W
                                      → X → retract B of X → retract B of Y → retract B of (X → Y)
retracts-of-closed-under-exponentials {U} {V} {W} {X} {Y} {B} fe x rbx rby = rbxy
 where
  rbbxy : retract (B → B) of (X → Y)
  rbbxy = rexp fe rbx rby
  rbxy : retract B of (X → Y)
  rbxy = retracts-compose rbbxy (pdrc (pr₁ rbx x))

\end{code}

Associativities and precedences.

\begin{code}

infix  0 _≃_
infix  1 _■
infixr 0 _≃⟨_⟩_

\end{code}
