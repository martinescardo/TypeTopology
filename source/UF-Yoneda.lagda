\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Yoneda where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Retracts
open import UF-Equiv
open import UF-FunExt
open import UF-Equiv-FunExt

\end{code}

We now consider "natural transformations" Nat A B (defined elsewhere)
and the Yoneda-machinery for them as discussed in
http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html

The Yoneda element induced by a natural transformation:

\begin{code}

yoneda-elem : ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇)
           → Nat (Id x) A → A x
yoneda-elem x A η = η x refl

\end{code}

We use capital Yoneda for the same constructions with the definition
of "Nat" expanded, beginning here:

\begin{code}

Yoneda-elem : ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇)
           → ((y : X) → x ≡ y → A y) → A x
Yoneda-elem = yoneda-elem

\end{code}

The natural transformation induced by an element:

\begin{code}

yoneda-nat : ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇)
           → A x → Nat (Id x) A
yoneda-nat x A a y p = transport A p a

Yoneda-nat : ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇)
           → A x → (y : X) → x ≡ y → A y
Yoneda-nat = yoneda-nat

\end{code}

Notice that this is the based recursion principle for the identity type.

The Yoneda Lemma says that every natural transformation is induced by
its Yoneda element:

\begin{code}

yoneda-lemma : ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇) (η : Nat (Id x) A)
             → yoneda-nat x A (yoneda-elem x A η) ≈ η
yoneda-lemma x A η _ refl = refl

Yoneda-lemma : ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇)
                 (η : (y : X) → x ≡ y → A y) (y : X) (p : x ≡ y)
             → transport A p (η x refl) ≡ η y p
Yoneda-lemma = yoneda-lemma

\end{code}

From another point of view, the Yoneda Lemma says that every natural
transformation η is recursively defined.

\begin{code}

yoneda-lemma' : (∀ U V → funext U V)
              → ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇) (η : Nat (Id x) A)
              → yoneda-nat x A (yoneda-elem x A η) ≡ η
yoneda-lemma' fe {U} {V} x A η = dfunext (fe U (U ⊔ V)) (λ y → dfunext (fe U V) (λ p → yoneda-lemma x A η y p))

\end{code}

The word "computation" here arises from a tradition in MLTT and should
not be taken too seriously:

\begin{code}

Yoneda-computation : ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇) (a : A x)
                   → transport A refl a ≡ a
Yoneda-computation x A a = refl

yoneda-computation : ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇) (a : A x)
                  → yoneda-elem x A (yoneda-nat x A a) ≡ a
yoneda-computation x A = Yoneda-computation x A

yoneda-elem-is-equiv : (∀ U V → funext U V) → ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇)
                   → is-equiv (yoneda-elem x A)
yoneda-elem-is-equiv fe {U} {V} {X} x A = (yoneda-nat x A , yoneda-computation x A) ,
                                         (yoneda-nat x A , yoneda-lemma' fe x A)

yoneda-nat-is-equiv : (∀ U V → funext U V) → ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇)
                   → is-equiv (yoneda-nat x A)
yoneda-nat-is-equiv fe {U} {V} {X} x A = (yoneda-elem x A , yoneda-lemma' fe x A) ,
                                        (yoneda-elem x A , yoneda-computation x A)

yoneda-equivalence : (∀ U V → funext U V) → ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇)
                   → A x ≃ Nat (Id x) A
yoneda-equivalence fe x A = yoneda-nat x A , yoneda-nat-is-equiv fe x A

Yoneda-equivalence : (∀ U V → funext U V) → ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇)
                   → A x ≃ (∀ y → x ≡ y → A y)
Yoneda-equivalence = yoneda-equivalence

\end{code}

Next we observe that "only elements" as defined above are universal
elements as in category theory.

\begin{code}

is-universal-element : ∀ {U V} {X : U ̇} {A : X → V ̇} → Σ A → U ⊔ V ̇
is-universal-element {U} {V} {X} {A} (x , a) = ∀ y (b : A y) → Σ \(p : x ≡ y) → yoneda-nat x A a y p ≡ b

universal-element-is-the-only-element : ∀ {U V} {X : U ̇} {A : X → V ̇} (σ : Σ A)
                                      → is-universal-element σ
                                      → is-the-only-element σ
universal-element-is-the-only-element {U} {V} {X} {A} (x , a) u (y , b) = to-Σ-≡ ((u y) b)

unique-element-is-universal-element : ∀ {U V} {X : U ̇} (A : X → V ̇) (σ : Σ A)
                                    → is-the-only-element σ
                                    → is-universal-element σ
unique-element-is-universal-element A (x , a) φ y b = from-Σ-≡'' (φ(y , b))

\end{code}

The following says that if the pair (x,a) is a universal element, then
the natural transformation it induces (namely yoneda-nat x a)
has a section and a retraction (which can be taken to be the same
function), and hence is an equivalence. Here having a section or
retraction is data not property in general, but it is in some cases
considered below.

\begin{code}

universality-section : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                     → is-universal-element (x , a)
                     → (y : X) → has-section (yoneda-nat x A a y)
universality-section {U} {V} {X} {A} x a u y = s y , φ y
 where
  s : (y : X) → A y → x ≡ y
  s y b = pr₁ (u y b)
  φ : (y : X) (b : A y) → yoneda-nat x A a y (s y b) ≡ b
  φ y b = pr₂ (u y b)

section-universality : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                     → ((y : X) → has-section(yoneda-nat x A a y))
                     → is-universal-element (x , a)
section-universality x a φ y b = pr₁(φ y) b , pr₂(φ y) b

\end{code}

NB. Notice that Yoneda-nat gives two different natural
transformations, depending on the number of arguments it takes, namely
the natural transformation (x : X) → A x → Nat (Id x) A and the
natural transformation Nat (Id x) → A (or (y : X) → x ≡ y → A y) if
two additional arguments x and a are given.

Then the Yoneda Theorem (proved below) says that any η : Nat (Id x) A)
is a natural equivalence iff Σ A is a singleton. This, in turn, is
equivalent to η being a natural retraction, and we start with it:

\begin{code}

Yoneda-section-forth : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (η : Nat (Id x) A)
                     → is-singleton (Σ A)
                     → (y : X) → has-section (η y)
Yoneda-section-forth {U} {V} {X} {A} x η iss y = g
 where
  u : is-universal-element (x , yoneda-elem x A η)
  u = unique-element-is-universal-element A (x , yoneda-elem x A η) (is-singleton-is-prop iss (x , yoneda-elem x A η))
  h : yoneda-nat x A (yoneda-elem x A η) y ∼ η y
  h = yoneda-lemma x A η y
  g : has-section (η y)
  g = has-section-closed-under-∼' (universality-section x (yoneda-elem x A η) u y) h

Yoneda-section-back : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (η : Nat (Id x) A)
                   → ((y : X) → has-section (η y))
                   → is-singleton (Σ A)
Yoneda-section-back {U} {V} {X} {A} x η φ = c
 where
  h : ∀ y → yoneda-nat x A (yoneda-elem x A η) y ∼ η y
  h = yoneda-lemma x A η
  g : ∀ y → has-section (yoneda-nat x A (yoneda-elem x A η) y)
  g y = has-section-closed-under-∼ (η y) (yoneda-nat x A (yoneda-elem x A η) y) (φ y) (h y)
  u : is-universal-element (x , yoneda-elem x A η)
  u = section-universality x (yoneda-elem x A η) g
  c : is-singleton (Σ A)
  c = (x , yoneda-elem x A η) , (universal-element-is-the-only-element (x , yoneda-elem x A η) u)

Yoneda-section : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (η : Nat (Id x) A)
               → is-singleton (Σ A) ⇔ ((y : X) → has-section (η y))
Yoneda-section x η = Yoneda-section-forth x η , Yoneda-section-back x η

\end{code}

Here is a direct application (24th April 2018).

\begin{code}

equiv-adj : ∀ {U V : Universe} {X : U ̇} {Y : V ̇} (f : X → Y) (g : Y → X)
              (η : (x : X) (y : Y) → f x ≡ y → g y ≡ x)
          → ((x : X) (y : Y) → has-section (η x y)) ⇔ is-vv-equiv g
equiv-adj f g η = (λ isv x → Yoneda-section-back (f x) (η x) (isv x)) ,
                  (λ φ x → Yoneda-section-forth (f x) (η x) (φ x))

\end{code}

This motivates the following definition.

\begin{code}

has-adj : ∀ {U V} {X : U ̇} {Y : V ̇} → (Y → X) → U ⊔ V ̇
has-adj g = Σ \(f : cod g → dom g) → Σ \(η : ∀ x y → f x ≡ y → g y ≡ x) → ∀ x y → has-section(η x y)

is-vv-equiv-has-adj : ∀ {U V} {X : U ̇} {Y : V ̇} (g : Y → X)
                       → is-vv-equiv g
                       → has-adj g
is-vv-equiv-has-adj {U} {V} {X} {Y} g isv = f , η , hass
 where
  f : X → Y
  f = pr₁ (pr₁ (is-vv-equiv-is-equiv g isv))
  gf : (x : X) → g (f x) ≡ x
  gf = pr₂ (pr₁ (is-vv-equiv-is-equiv g isv))
  η : (x : X) (y : Y) → f x ≡ y → g y ≡ x
  η x y p = transport (λ - → g - ≡ x) p (gf x )
  hass : (x : X) (y : Y) → has-section (η x y)
  hass x = Yoneda-section-forth (f x) (η x) (isv x)

has-adj-is-vv-equiv : ∀ {U V : Universe} {X : U ̇} {Y : V ̇} (g : Y → X)
                       → has-adj g
                       → is-vv-equiv g
has-adj-is-vv-equiv g (f , η , hass) x = Yoneda-section-back (f x) (η x) (hass x)

\end{code}

A natural transformation of the above kind is an equivalence iff it has a section,
as shown in https://github.com/HoTT/book/issues/718#issuecomment-65378867:

\begin{code}

Hedberg-lemma : ∀ {U} {X : U ̇} (x : X) (η : (y : X) → x ≡ y → x ≡ y) (y : X) (p : x ≡ y)
              → η x refl ∙ p ≡ η y p
Hedberg-lemma x η = yoneda-lemma x (Id x) η

idemp-is-id : ∀ {U} {X : U ̇} {x : X} (e : (y : X) → x ≡ y → x ≡ y) (y : X) (p : x ≡ y)
           → e y (e y p) ≡ e y p
           → e y p ≡ p
idemp-is-id {U} {X} {x} e y p idemp = cancel-left (
        e x refl ∙ e y p ≡⟨ Hedberg-lemma x e y (e y p) ⟩
        e y (e y p)      ≡⟨ idemp ⟩
        e y p            ≡⟨ (Hedberg-lemma x e y p)⁻¹ ⟩
        e x refl ∙ p     ∎ )

nat-retraction-is-section : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (η : Nat (Id x) A)
                          → ((y : X) → has-section(η y))
                          → ((y : X) → has-retraction(η y))
nat-retraction-is-section {U} {V} {X} {A} x η hass = hasr
 where
  s : (y : X) → A y → x ≡ y
  s y = pr₁ (hass y)
  ηs : {y : X} (a : A y) → η y (s y a) ≡ a
  ηs {y} = pr₂ (hass y)
  e : (y : X) → x ≡ y → x ≡ y
  e y p = s y (η y p)
  idemp : (y : X) (p : x ≡ y) → e y (e y p) ≡ e y p
  idemp y p = ap (s y) (ηs (η y p))
  e-is-id : (y : X) (p : x ≡ y) → e y p ≡ p
  e-is-id y p = idemp-is-id e y p (idemp y p)
  hasr : (y : X) → has-retraction(η y)
  hasr y = s y , e-is-id y

\end{code}

The above use of the word "is" is justified by the following:

\begin{code}

nat-retraction-is-section-uniquely : (∀ U V → funext U V) → ∀ {U V} {X : U ̇} {A : X → V ̇}
                                     (x : X) (η : Nat (Id x) A)
                                   → ((y : X) → has-section(η y))
                                   → ((y : X) → is-singleton(has-retraction(η y)))
nat-retraction-is-section-uniquely fe x η hass y = inhabited-proposition-is-singleton
                                                      (nat-retraction-is-section x η hass y)
                                                      (hass-is-prop-hasr fe (η y) (hass y))

nat-has-section-is-prop : (∀ U V → funext U V) → ∀ {U V} {X : U ̇} {A : X → V ̇}
                        (x : X) (η : Nat (Id x) A)
                      → is-prop ((y : X) → has-section (η y))
nat-has-section-is-prop fe {U} {V} {X} x η φ = Π-is-prop (fe U (U ⊔ V)) γ φ
  where
   γ : (y : X) → is-prop (has-section (η y))
   γ y = hasr-is-prop-hass fe (η y) (nat-retraction-is-section x η φ y)

nat-retraction-is-equiv : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (η : Nat (Id x) A)
                      → ((y : X) → has-section(η y))
                      → ((y : X) → is-equiv(η y))
nat-retraction-is-equiv x η hass y = (hass y , nat-retraction-is-section x η hass y)

\end{code}

We are interested in the following corollaries:

\begin{code}

universality-equiv : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                   → is-universal-element (x , a)
                   → (y : X) → is-equiv(yoneda-nat x A a y)
universality-equiv {U} {V} {X} {A} x a u = nat-retraction-is-equiv x (yoneda-nat x A a)
                                                                    (universality-section x a u)

equiv-universality : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                   → ((y : X) → is-equiv(yoneda-nat x A a y))
                   → is-universal-element (x , a)
equiv-universality x a φ = section-universality x a (λ y → pr₁ (φ y))

Yoneda-Theorem-forth : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (η : Nat (Id x) A)
                    → is-singleton (Σ A)
                    → (y : X) → is-equiv (η y)
Yoneda-Theorem-forth x η iss = nat-retraction-is-equiv x η (Yoneda-section-forth x η iss)

Yoneda-Theorem-back : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (η : Nat (Id x) A)
                   → ((y : X) → is-equiv (η y))
                   → is-singleton (Σ A)
Yoneda-Theorem-back x η φ = Yoneda-section-back x η (λ y → pr₁(φ y))

\end{code}

Next we conclude that a presheaf A is representable iff Σ A is a
singleton.

\begin{code}

_≊_ : ∀ {U V W} {X : U ̇} → (X → V ̇) → (X → W ̇) → U ⊔ V ⊔ W ̇
A ≊ B = Σ \(η : Nat A B) → ∀ x → is-equiv(η x)

isRepresentable : ∀ {U V} {X : U ̇} → (X → V ̇) → U ⊔ V ̇
isRepresentable A = Σ \x → Id x ≊ A

singleton-representable : ∀ {U V} {X : U ̇} {A : X → V ̇}
                        → is-singleton (Σ A)
                        → isRepresentable A
singleton-representable {U} {V} {X} {A} ((x , a) , cc) = x ,
                                                         yoneda-nat x A a ,
                                                         Yoneda-Theorem-forth x (yoneda-nat x A a) ((x , a) , cc)

representable-singleton : ∀ {U V} {X : U ̇} {A : X → V ̇}
                        → isRepresentable A
                        → is-singleton (Σ A)
representable-singleton {U} {V} {X} {A} (x , (η , φ)) = Yoneda-Theorem-back x η φ

\end{code}

We also have the following corollaries:

\begin{code}

is-vv-equiv-has-adj' : ∀ {U V : Universe} {X : U ̇} {Y : V ̇} (g : Y → X)
                     → is-vv-equiv g
                     → Σ \(f : X → Y) → (x : X) (y : Y) → (f x ≡ y) ≃ (g y ≡ x)
is-vv-equiv-has-adj' {U} {V} {X} {Y} g φ = (pr₁ γ) ,
                                               λ x y → (pr₁ (pr₂ γ) x y) ,
                                                       (nat-retraction-is-equiv (pr₁ γ x) (pr₁ (pr₂ γ) x) (pr₂ (pr₂ γ) x) y)
 where
  γ : has-adj g
  γ = is-vv-equiv-has-adj g φ

has-adj-is-vv-equiv' : ∀ {U V : Universe} {X : U ̇} {Y : V ̇} (g : Y → X)
                     → (Σ \(f : X → Y) → (x : X) (y : Y) → (f x ≡ y) ≃ (g y ≡ x))
                     → is-vv-equiv g
has-adj-is-vv-equiv' g (f , ψ) = has-adj-is-vv-equiv g (f , (λ x y → pr₁(ψ x y)) , (λ x y → pr₁(pr₂(ψ x y))))

\end{code}

Here is an application of the Yoneda machinery to a well-known result
by Voevodsky. If products preserve contractibility, then function
extensionality holds (happly is an equivalence).

\begin{code}

funext-via-singletons : ∀ {U V}
                      → ((X : U ̇) (Y : X → V ̇) → ((x : X) → is-singleton (Y x))
                                                 → is-singleton (Π Y))
                      → funext U V
funext-via-singletons {U} {V} φ {X} {Y} f = γ
 where
  c : is-singleton (Π \(x : X) → Σ \(y : Y x) → f x ≡ y)
  c = φ X (λ x → Σ \(y : Y x) → f x ≡ y) (λ x → identifications-from-singleton (f x))
  A : Π Y → U ⊔ V ̇
  A g = (x : X) → f x ≡ g x
  r : (Π \(x : X) → Σ \(y : Y x) → f x ≡ y) → Σ A
  r = TT-choice
  r-has-section : has-section r
  r-has-section = TT-choice-has-section
  d : is-singleton (Σ A)
  d = retract-of-singleton (r , r-has-section) c
  η : Nat (Id f) A
  η = happly' f
  γ : (g : Π Y) → is-equiv (happly' f g)
  γ = Yoneda-Theorem-forth f η d

\end{code}

We also have the following characterization of univalence from the
Yoneda machinery.

The fact that this is the case was announced on 5th August
2014 with the techniques of the HoTT Book
(https://groups.google.com/forum/#!msg/homotopytypetheory/HfCB_b-PNEU/Ibb48LvUMeUJ)),
and the proof given here via Yoneda was announced on 12th May 2015
(http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html).

\begin{code}

open import UF-Univalence

univalence-via-singletons :
  ∀ {U} → is-univalent U   ⇔   ((X : U ̇) → is-singleton (Σ \(Y : U ̇) → X ≃ Y))
univalence-via-singletons {U} = (f , g)
 where
  f : is-univalent U → (X : U ̇) → is-singleton (Σ (Eq X))
  f ua X = representable-singleton (X , (idtoeq X , ua X))

  g : ((X : U ̇) → is-singleton (Σ (Eq X))) → is-univalent U
  g φ X = universality-equiv X (ideq X)
                                (unique-element-is-universal-element
                                       (Eq X)
                                       (X , ideq X)
                                       (is-singleton-is-prop (φ X) (X , ideq X)))

\end{code}

Notice that is-singleton can be replaced by is-prop in the formulation
of this logical equivalence (exercise).


Appendix.

Two natural transformations with the same Yoneda elements are
(point-point-wise) equal. This can be proved using J (or equivalently
pattern matching), but we use the opportunity to illustrate how to use
the Yoneda Lemma.

\begin{code}

yoneda-elem-lc : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇}
                   (η θ : Nat (Id x) A)
               → yoneda-elem x A η ≡ yoneda-elem x A θ → η ≈ θ
yoneda-elem-lc {U} {V} {X} {x} {A} η θ q y p =
  η y p                                ≡⟨ (yoneda-lemma x A η y p)⁻¹ ⟩
  yoneda-nat x A (yoneda-elem x A η) y p ≡⟨ ap (λ - → yoneda-nat x A - y p) q ⟩
  yoneda-nat x A (yoneda-elem x A θ) y p ≡⟨ yoneda-lemma x A θ y p ⟩
  θ y p ∎

Yoneda-elem-lc : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} (η θ : (y : X) → x ≡ y → A y)
              → η x refl ≡ θ x refl → (y : X) (p : x ≡ y) → η y p ≡ θ y p
Yoneda-elem-lc = yoneda-elem-lc

\end{code}

Some special cases of interest, which probably speak for themselves:

\begin{code}

yoneda-nat-Id : ∀ {U} {X : U ̇} (x {y} : X) → Id x y → Nat (Id y) (Id x)
yoneda-nat-Id x {y} = yoneda-nat y (Id x)

Yoneda-nat-Id : ∀ {U} {X : U ̇} (x {y} : X) → x ≡ y → (z : X) → y ≡ z → x ≡ z
Yoneda-nat-Id = yoneda-nat-Id

Id-charac : (∀ U V → funext U V)
       → ∀ {U} {X : U ̇} (x {y} : X) → (x ≡ y) ≃ Nat (Id y) (Id x)
Id-charac fe {U} {X} x {y} = yoneda-equivalence fe y (Id x)

yoneda-nat-Eq : ∀ {U} (X {Y} : U ̇) → Eq X Y → Nat (Id Y) (Eq X)
yoneda-nat-Eq X {Y} = yoneda-nat Y (Eq X)

yoneda-elem-Id : ∀ {U} {X : U ̇} (x {y} : X) → Nat (Id y) (Id x) → Id x y
yoneda-elem-Id x {y} = yoneda-elem y (Id x)

Yoneda-elem-Id : ∀ {U} {X : U ̇} (x {y} : X) → ((z : X) → y ≡ z → x ≡ z) → x ≡ y
Yoneda-elem-Id = yoneda-elem-Id

yoneda-lemma-Id : ∀ {U} {X : U ̇} (x {y} : X) (η : Nat (Id y) (Id x)) (z : X) (p : y ≡ z)
                → (yoneda-elem-Id x η) ∙ p ≡ η z p
yoneda-lemma-Id x {y} = yoneda-lemma y (Id x)

Yoneda-lemma-Id : ∀ {U} {X : U ̇} (x {y} : X) (η : (z : X) → y ≡ z → x ≡ z) (z : X) (p : y ≡ z)
                → η y refl ∙ p ≡ η z p
Yoneda-lemma-Id = yoneda-lemma-Id

yoneda-const : ∀ {U V} {X : U ̇} {B : V ̇} {x : X} (η : Nat (Id x) (λ _ → B)) (y : X) (p : x ≡ y)
             → yoneda-elem x (λ _ → B) η ≡ η y p
yoneda-const η = yoneda-elem-lc (λ y p → yoneda-elem _ _ η) η refl

Yoneda-const : ∀ {U V} {X : U ̇} {B : V ̇} {x : X} (η : (y : X) → x ≡ y → B) (y : X) (p : x ≡ y)
             → η x refl ≡ η y p
Yoneda-const = yoneda-const

\end{code}

The following is traditionally proved by induction on the identity
type (as articulated by Jbased or J in the module SpartanMLTT), but
here we use the Yoneda machinery instead, again for the sake of
illustration.

\begin{code}

singleton-types-are-singletons-bis : ∀ {U} {X : U ̇} (x : X)
                                  → is-the-only-element (x , refl)
singleton-types-are-singletons-bis {U} {X} x (y , p) = yoneda-const η y p
 where
  η : (y : X) → x ≡ y → identifications-from x
  η y p = (y , p)

\end{code}

What the following says is that the Yoneda machinery could have been
taken as primitive, as an alternative to Jbased or J, in the sense
that the latter can be recovered from the former.

\begin{code}

Jbased'' : ∀ {U V} {X : U ̇} (x : X) (A : identifications-from x → V ̇)
         → A (x , refl) → Π A
Jbased'' x A a w = yoneda-nat (x , refl) A a w (singleton-types-are-singletons w)

Jbased' : ∀ {U V} {X : U ̇} (x : X) (B : (y : X) → x ≡ y → V ̇)
        → B x refl → (y : X) → Π (B y)
Jbased' x B b y p = Jbased'' x (uncurry B) b (y , p)

\end{code}

And now some more uses of Yoneda to prove things that traditionally
are proved using J(based), again for the sake of illustration:

\begin{code}

refl-left-neutral-bis : ∀ {U} {X : U ̇} {x y : X} {p : x ≡ y} → refl ∙ p ≡ p
refl-left-neutral-bis {U} {X} {x} {y} {p} = yoneda-lemma x (Id x) (λ y p → p) y p

⁻¹-involutive-bis : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → (p ⁻¹)⁻¹ ≡ p
⁻¹-involutive-bis {U} {X} {x} {y} = yoneda-elem-lc (λ x p → (p ⁻¹)⁻¹) (λ x p → p) refl y

⁻¹-contravariant-bis : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) {z : X} (q : y ≡ z)
                → q ⁻¹ ∙ p ⁻¹ ≡ (p ∙ q)⁻¹
⁻¹-contravariant-bis {U} {X} {x} {y} p {z} = yoneda-elem-lc (λ z q → q ⁻¹ ∙ p ⁻¹)
                                                       (λ z q → (p ∙ q) ⁻¹)
                                                       refl-left-neutral-bis
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
                                           refl
                                           t
\end{code}

Then of course associativity of path composition follows:

\begin{code}

assoc-bis : ∀ {U} {X : U ̇} {x y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
          → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc-bis {U} {X} {x} {y} p q r = ap (λ - → - x y p q) (ext-assoc r)

left-inverse-bis : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → p ⁻¹ ∙ p ≡ refl
left-inverse-bis {U} {X} {x} {y} = yoneda-elem-lc (λ x p → p ⁻¹ ∙ p) (λ x p → refl) refl y

right-inverse-bis : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → refl ≡ p ∙ p ⁻¹
right-inverse-bis {U} {X} {x} {y} = yoneda-const (λ x p → p ∙ p ⁻¹) y

from-Σ-Id : ∀ {U V} {X : U ̇} {A : X → V ̇} {σ τ : Σ A}
          → σ ≡ τ
          → Σ \(p : pr₁ σ ≡ pr₁ τ) → yoneda-nat (σ .pr₁) A (pr₂ σ) (pr₁ τ) p ≡ pr₂ τ
from-Σ-Id {U} {V} {X} {A} {x , a} {τ} = yoneda-nat (x , yoneda-nat x A a x refl) B (refl , refl) τ
 where
   B : (τ : Σ A) → U ⊔ V ̇
   B τ = Σ \(p : x ≡ pr₁ τ) → yoneda-nat x A a (pr₁ τ) p ≡ pr₂ τ

to-Σ-Id : ∀ {U V} {X : U ̇} {A : X → V ̇} {σ τ : Σ A}
          → (Σ \(p : pr₁ σ ≡ pr₁ τ) → yoneda-nat (pr₁ σ) A (pr₂ σ) (pr₁ τ) p ≡ pr₂ τ)
          → σ ≡ τ
to-Σ-Id {U} {V} {X} {A} {x , a} {y , b} (p , q) = r
 where
  η : (y : X) → x ≡ y → Σ A
  η y p = (y , yoneda-nat x A a y p)
  yc : (x , a) ≡ (y , yoneda-nat x A a y p)
  yc = yoneda-const η y p
  r : (x , a) ≡ (y , b)
  r = yoneda-nat (yoneda-nat x A a y p) (λ b → (x , a) ≡ (y , b)) yc b q

from-Σ-Id' : ∀ {U V} {X : U ̇} {A : X → V ̇} {σ τ : Σ A}
           → σ ≡ τ
           → Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ
from-Σ-Id' = from-Σ-Id

to-Σ-Id' : ∀ {U V} {X : U ̇} {A : X → V ̇} {σ τ : Σ A}
         → (Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
         → σ ≡ τ
to-Σ-Id' = to-Σ-Id

NatΣ-lc : ∀ {U V W} (X : U ̇) (A : X → V ̇) (B : X → W ̇) (ζ : Nat A B)
        → ((x : X) → left-cancellable(ζ x)) → left-cancellable(NatΣ ζ)
NatΣ-lc X A B ζ ζ-lc {(x , a)} {(y , b)} pq = g
  where
    p : x ≡ y
    p = pr₁ (from-Σ-Id pq)
    η : Nat (Id x) B
    η = yoneda-nat x B (ζ x a)
    q : η y p ≡ ζ y b
    q = pr₂ (from-Σ-Id pq)
    θ : Nat (Id x) A
    θ = yoneda-nat x A a
    η' : Nat (Id x) B
    η' y p = ζ y (θ y p)
    r : η' ≈ η
    r = yoneda-elem-lc η' η refl
    r' : ζ y (θ y p) ≡ η y p
    r' = r y p
    s : ζ y (θ y p) ≡ ζ y b
    s = r' ∙ q
    t : θ y p ≡ b
    t = ζ-lc y s
    g : x , a ≡ y , b
    g = to-Σ-Id (p , t)

yoneda-equivalence-Σ : (∀ U V → funext U V) → ∀ {U V} {X : U ̇} (A : X → V ̇)
                     → Σ A ≃ Σ \(x : X) → Nat (Id x) A
yoneda-equivalence-Σ fe A = NatΣ-equiv' A (λ x → Nat (Id x) A) (λ x → yoneda-equivalence fe x A)

nats-are-uniquely-transports : (∀ U V → funext U V) → ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇) (η : Nat (Id x) A)
                            → is-singleton (Σ \(a : A x) → (λ y p → transport A p a) ≡ η)
nats-are-uniquely-transports fe x A = is-equiv-is-vv-equiv (yoneda-nat x A) (yoneda-nat-is-equiv fe x A)

adj-obs : (∀ U V → funext U V) → ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) (g : Y → X) (x : X)
          (η : (y : Y) → f x ≡ y → g y ≡ x)
        → is-singleton (Σ \(q : g (f x) ≡ x) → (λ y p → transport (λ - → g - ≡ x) p q) ≡ η)
adj-obs fe f g x = nats-are-uniquely-transports fe (f x) (λ y → g y ≡ x)

\end{code}

We need this elsewhere:

\begin{code}

idtoeq-bis : ∀ {U} (X : U ̇) → Nat (Id X) (Eq X)
idtoeq-bis X = yoneda-nat X (Eq X) (ideq X)

Idtofun' : ∀ {U} (X : U ̇) → Nat (Id X) (λ Y → X → Y)
Idtofun' X = yoneda-nat X (λ Y → X → Y) id

idtofun-agree' : ∀ {U} (X : U ̇) → idtofun X ≈ Idtofun' X
idtofun-agree' X = yoneda-elem-lc (idtofun X) (Idtofun' X) refl

\end{code}
