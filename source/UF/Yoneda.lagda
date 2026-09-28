Martin Escardo, before 2018.

A better version is in MGS.Yoneda, but currently we are using this one.

We consider "natural transformations" Nat A B (defined elsewhere) and
the Yoneda-machinery for them as discussed in
http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html (2015).

See also

[1] Egbert Rijke, Introduction to Homotopy Type Theory, 2022.
    https://doi.org/10.48550/arXiv.2212.11082

[2] Egbert Rijke, Introduction to Homotopy Type Theory, 2012. Master Thesis.
    https://hottheory.files.wordpress.com/2012/08/hott2.pdf (Section 2.8).

[3] Egbert Rijke, A type-theoretical Yoneda Lemma, 2012.
    http://homotopytypetheory.org/2012/05/02/a-type-theoretical-yoneda-lemma/

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Yoneda where

open import MLTT.Spartan
open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

The Yoneda element induced by a natural transformation:

\begin{code}

yoneda-elem : {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
            → Nat (Id x) A → A x
yoneda-elem x A η = η x refl

\end{code}

We use capital Yoneda for the same constructions with the definition
of "Nat" expanded, beginning here:

\begin{code}

Yoneda-elem : {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
            → ((y : X) → x ＝ y → A y) → A x
Yoneda-elem = yoneda-elem

\end{code}

The natural transformation induced by an element:

\begin{code}

yoneda-nat : {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
           → A x → Nat (Id x) A
yoneda-nat x A a y p = transport A p a

Yoneda-nat : {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
           → A x → (y : X) → x ＝ y → A y
Yoneda-nat = yoneda-nat

\end{code}

Notice that this is the based recursion principle for the identity type.

The Yoneda Lemma says that every natural transformation is induced by
its Yoneda element:

\begin{code}

private
 _≈_ : {X : 𝓤 ̇ } {x : X} {A : X → 𝓥 ̇ } → Nat (Id x) A → Nat (Id x) A → 𝓤 ⊔ 𝓥 ̇
 η ≈ θ = ∀ y → η y ∼ θ y

yoneda-lemma : {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ ) (η : Nat (Id x) A)
             → yoneda-nat x A (yoneda-elem x A η) ≈ η
yoneda-lemma x A η y refl = refl

Yoneda-lemma : {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
               (η : (y : X) → x ＝ y → A y) (y : X) (p : x ＝ y)
             → transport A p (η x refl) ＝ η y p
Yoneda-lemma = yoneda-lemma

\end{code}

From another point of view, the Yoneda Lemma says that every natural
transformation η is recursively defined.

\begin{code}

yoneda-lemma' : FunExt
              → {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ ) (η : Nat (Id x) A)
              → yoneda-nat x A (yoneda-elem x A η) ＝ η
yoneda-lemma' {𝓤} {𝓥} fe x A η = dfunext (fe 𝓤 (𝓤 ⊔ 𝓥))
                                   (λ y → dfunext (fe 𝓤 𝓥)
                                            (λ p → yoneda-lemma x A η y p))

\end{code}

The word "computation" here arises from a tradition in MLTT and should
not be taken too seriously:

\begin{code}

Yoneda-computation : {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ ) (a : A x)
                   → transport A refl a ＝ a
Yoneda-computation x A a = refl

yoneda-computation : {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ ) (a : A x)
                   → yoneda-elem x A (yoneda-nat x A a) ＝ a
yoneda-computation x A = Yoneda-computation x A

yoneda-elem-is-equiv : FunExt
                     → {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
                     → is-equiv (yoneda-elem x A)
yoneda-elem-is-equiv fe x A = qinvs-are-equivs
                               (yoneda-elem x A)
                               (yoneda-nat x A ,
                                yoneda-lemma' fe x A ,
                                yoneda-computation x A)

yoneda-nat-is-equiv : FunExt
                    → {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
                    → is-equiv (yoneda-nat x A)
yoneda-nat-is-equiv fe {X} x A = qinvs-are-equivs
                                  (yoneda-nat x A)
                                  (yoneda-elem x A ,
                                   yoneda-computation x A ,
                                   yoneda-lemma' fe x A)

yoneda-equivalence : FunExt
                   → {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
                   → A x ≃ Nat (Id x) A
yoneda-equivalence fe x A = yoneda-nat x A , yoneda-nat-is-equiv fe x A

Yoneda-equivalence : FunExt
                   → {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
                   → A x ≃ (∀ y → x ＝ y → A y)
Yoneda-equivalence = yoneda-equivalence

\end{code}

Next we observe that centers of contraction are universal elements in
the sense of category theory.

\begin{code}

is-universal-element-of : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → Σ A → 𝓤 ⊔ 𝓥 ̇
is-universal-element-of {𝓤} {𝓥} {X} A (x , a) =
 (y : X) (b : A y) → Σ p ꞉ x ＝ y , yoneda-nat x A a y p ＝ b

universal-element-is-central : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (σ : Σ A)
                             → is-universal-element-of A σ
                             → is-central (Σ A) σ
universal-element-is-central (x , a) u (y , b) = to-Σ-＝ (u y b)

central-point-is-universal : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (σ : Σ A)
                           → is-central (Σ A) σ
                           → is-universal-element-of A σ
central-point-is-universal A (x , a) φ y b = from-Σ-＝ (φ(y , b))

\end{code}

The following says that if the pair (x , a) is a universal element,
then the natural transformation it induces (namely yoneda-nat x a) has
a section and a retraction (which can be taken to be the same
function), and hence is an equivalence. Here having a section or
retraction is data not property in general, but it is in some cases
considered below.

\begin{code}

universality-section : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X) (a : A x)
                     → is-universal-element-of A (x , a)
                     → (y : X) → has-section (yoneda-nat x A a y)
universality-section {𝓤} {𝓥} {X} {A} x a u y = s y , φ y
 where
  s : (y : X) → A y → x ＝ y
  s y b = pr₁ (u y b)

  φ : (y : X) (b : A y) → yoneda-nat x A a y (s y b) ＝ b
  φ y b = pr₂ (u y b)

section-universality : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X) (a : A x)
                     → ((y : X) → has-section(yoneda-nat x A a y))
                     → is-universal-element-of A (x , a)
section-universality x a φ y b = pr₁(φ y) b , pr₂(φ y) b

\end{code}

NB. Notice that Yoneda-nat gives two different natural
transformations, depending on the number of arguments it takes, namely
the natural transformation (x : X) → A x → Nat (Id x) A and the
natural transformation Nat (Id x) → A (or (y : X) → x ＝ y → A y) if
two additional arguments x and a are given.

Then the Yoneda Theorem (proved below) says that any η : Nat (Id x) A)
is a natural equivalence iff Σ A is a singleton. This, in turn, is
equivalent to η being a natural retraction, and we start with it:

\begin{code}

Yoneda-section-forth : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                       (x : X) (η : Nat (Id x) A)
                     → ∃! A
                     → (y : X) → has-section (η y)
Yoneda-section-forth {𝓤} {𝓥} {X} {A} x η i y = g
 where
  u : is-universal-element-of A (x , yoneda-elem x A η)
  u = central-point-is-universal A
        (x , yoneda-elem x A η)
        (singletons-are-props i (x , yoneda-elem x A η))

  h : yoneda-nat x A (yoneda-elem x A η) y ∼ η y
  h = yoneda-lemma x A η y

  g : has-section (η y)
  g = has-section-closed-under-∼'
       (universality-section x (yoneda-elem x A η) u y)
       h

Yoneda-section-back : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X) (η : Nat (Id x) A)
                    → ((y : X) → has-section (η y))
                    → ∃! A
Yoneda-section-back {𝓤} {𝓥} {X} {A} x η φ = c
 where
  h : ∀ y → yoneda-nat x A (yoneda-elem x A η) y ∼ η y
  h = yoneda-lemma x A η

  g : ∀ y → has-section (yoneda-nat x A (yoneda-elem x A η) y)
  g y = has-section-closed-under-∼
         (η y)
         (yoneda-nat x A (yoneda-elem x A η) y)
         (φ y)
         (h y)

  u : is-universal-element-of A (x , yoneda-elem x A η)
  u = section-universality x (yoneda-elem x A η) g

  c : ∃! A
  c = (x , yoneda-elem x A η) ,
      universal-element-is-central (x , yoneda-elem x A η) u

Yoneda-section : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X) (η : Nat (Id x) A)
               → ∃! A ↔ ((y : X) → has-section (η y))
Yoneda-section x η = Yoneda-section-forth x η , Yoneda-section-back x η

\end{code}

Here is a direct application (24th April 2018).

\begin{code}

equiv-adj : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            (f : X → Y)
            (g : Y → X)
            (η : (x : X) (y : Y) → f x ＝ y → g y ＝ x)
          → ((x : X) (y : Y) → has-section (η x y)) ↔ is-vv-equiv g
equiv-adj f g η = (λ i x → Yoneda-section-back (f x) (η x) (i x)) ,
                  (λ φ x → Yoneda-section-forth (f x) (η x) (φ x))

\end{code}

This motivates the following definition.

\begin{code}

has-adj : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (Y → X) → 𝓤 ⊔ 𝓥 ̇
has-adj g = Σ f ꞉ (codomain g → domain g)
          , Σ η ꞉ (∀ x y → f x ＝ y → g y ＝ x)
          , (∀ x y → has-section(η x y))

is-vv-equiv-has-adj : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (g : Y → X)
                    → is-vv-equiv g
                    → has-adj g
is-vv-equiv-has-adj {𝓤} {𝓥} {X} {Y} g isv = f , η , hass
 where
  f : X → Y
  f = pr₁ (pr₁ (vv-equivs-are-equivs g isv))

  gf : (x : X) → g (f x) ＝ x
  gf = pr₂ (pr₁ (vv-equivs-are-equivs g isv))

  η : (x : X) (y : Y) → f x ＝ y → g y ＝ x
  η x y p = transport (λ - → g - ＝ x) p (gf x)

  hass : (x : X) (y : Y) → has-section (η x y)
  hass x = Yoneda-section-forth (f x) (η x) (isv x)

has-adj-is-vv-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (g : Y → X)
                    → has-adj g
                    → is-vv-equiv g
has-adj-is-vv-equiv g (f , η , hass) x =
 Yoneda-section-back (f x) (η x) (hass x)

\end{code}

A natural transformation of the above kind is an equivalence iff it
has a section, as shown in
https://github.com/HoTT/book/issues/718#issuecomment-65378867:

\begin{code}

Hedberg-lemma : {X : 𝓤 ̇ }
                (x : X)
                (η : (y : X) → x ＝ y → x ＝ y)
                (y : X)
                (p : x ＝ y)
              → η x refl ∙ p ＝ η y p
Hedberg-lemma x = yoneda-lemma x (Id x)

idemp-is-id : {X : 𝓤 ̇ }
              {x : X}
              (e : (y : X) → x ＝ y → x ＝ y)
              (y : X)
              (p : x ＝ y)
            → e y (e y p) ＝ e y p
            → e y p ＝ p
idemp-is-id {𝓤} {X} {x} e y p idemp = cancel-left (
        e x refl ∙ e y p ＝⟨ Hedberg-lemma x e y (e y p) ⟩
        e y (e y p)      ＝⟨ idemp ⟩
        e y p            ＝⟨ (Hedberg-lemma x e y p)⁻¹ ⟩
        e x refl ∙ p     ∎)

nat-retraction-is-section : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                            (x : X) (η : Nat (Id x) A)
                          → ((y : X) → has-section(η y))
                          → ((y : X) → is-section(η y))
nat-retraction-is-section {𝓤} {𝓥} {X} {A} x η hs = hr
 where
  s : (y : X) → A y → x ＝ y
  s y = pr₁ (hs y)

  ηs : {y : X} (a : A y) → η y (s y a) ＝ a
  ηs {y} = pr₂ (hs y)

  e : (y : X) → x ＝ y → x ＝ y
  e y p = s y (η y p)

  idemp : (y : X) (p : x ＝ y) → e y (e y p) ＝ e y p
  idemp y p = ap (s y) (ηs (η y p))

  i : (y : X) (p : x ＝ y) → e y p ＝ p
  i y p = idemp-is-id e y p (idemp y p)

  hr : (y : X) → is-section(η y)
  hr y = s y , i y

\end{code}

The above use of the word "is" is justified by the following:

\begin{code}

nat-retraction-is-section-uniquely : FunExt
                                   → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                                     (x : X) (η : Nat (Id x) A)
                                   → ((y : X) → has-section (η y))
                                   → ((y : X) → is-singleton (is-section(η y)))
nat-retraction-is-section-uniquely fe x η hs y =
 pointed-props-are-singletons
  (nat-retraction-is-section x η hs y)
  (sections-have-at-most-one-retraction fe (η y) (hs y))

nat-having-section-is-prop : FunExt
                           → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                             (x : X) (η : Nat (Id x) A)
                           → is-prop ((y : X) → has-section (η y))
nat-having-section-is-prop {𝓤} {𝓥} fe {X} x η φ = Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥)) γ φ
  where
   γ : (y : X) → is-prop (has-section (η y))
   γ y = retractions-have-at-most-one-section fe (η y)
          (nat-retraction-is-section x η φ y)

nats-with-sections-are-equivs
 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X) (η : Nat (Id x) A)
 → ((y : X) → has-section(η y))
 → is-fiberwise-equiv η
nats-with-sections-are-equivs x η hs y = hs y ,
                                         nat-retraction-is-section x η hs y

\end{code}

We are interested in the following corollaries:

\begin{code}

universality-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                     (x : X) (a : A x)
                   → is-universal-element-of A (x , a)
                   → is-fiberwise-equiv (yoneda-nat x A a)
universality-equiv {𝓤} {𝓥} {X} {A} x a u = nats-with-sections-are-equivs x
                                             (yoneda-nat x A a)
                                             (universality-section x a u)

equiv-universality : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                     (x : X) (a : A x)
                   → is-fiberwise-equiv (yoneda-nat x A a)
                   → is-universal-element-of A (x , a)
equiv-universality x a φ = section-universality x a (λ y → pr₁ (φ y))

Yoneda-Theorem-forth : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                       (x : X) (η : Nat (Id x) A)
                     → ∃! A
                     → is-fiberwise-equiv η
Yoneda-Theorem-forth x η i = nats-with-sections-are-equivs x η
                              (Yoneda-section-forth x η i)

\end{code}

Here is another proof, from the MGS'2019 lecture notes
(https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes):

\begin{code}

Yoneda-Theorem-forth' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                        (x : X) (η : Nat (Id x) A)
                      → ∃! A
                      → is-fiberwise-equiv η
Yoneda-Theorem-forth' {𝓤} {𝓥} {X} A x η u = γ
 where
  g : singleton-type x → Σ A
  g = NatΣ η

  e : is-equiv g
  e = maps-of-singletons-are-equivs g (singleton-types-are-singletons x) u

  γ : is-fiberwise-equiv η
  γ = NatΣ-equiv-gives-fiberwise-equiv η e

\end{code}

Here is an application:

\begin{code}

fiberwise-equiv-criterion : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                            (x : X)
                          → ((y : X) → A y ◁ (x ＝ y))
                          → (τ : Nat (Id x) A) → is-fiberwise-equiv τ
fiberwise-equiv-criterion A x ρ τ = Yoneda-Theorem-forth x τ
                                     (Yoneda-section-back x
                                       (λ x → retraction (ρ x))
                                       (λ x → retraction-has-section (ρ x)))

fiberwise-equiv-criterion' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                             (x : X)
                           → ((y : X) → (x ＝ y) ≃ A y)
                           → (τ : Nat (Id x) A) → is-fiberwise-equiv τ
fiberwise-equiv-criterion' A x e = fiberwise-equiv-criterion A x
                                    (λ y → ≃-gives-▷ (e y))

\end{code}

This says that if there is any fiberwise equivalence whatsoever (or
even just a fiberwise retraction), then any natural transformation is
a fiberwise equivalence.

\begin{code}

Yoneda-Theorem-back : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                      (x : X) (η : Nat (Id x) A)
                    → is-fiberwise-equiv η
                    → ∃! A
Yoneda-Theorem-back x η φ = Yoneda-section-back x η (λ y → pr₁(φ y))

\end{code}

Egbert Rijke, in his book [1], refers to Yoneda-Theorem-forth and
Yoneda-Theorem-back as "the fundamental theorem of identity types".
See also his master thesis [2] and his blog post [3].

Next we conclude that a presheaf A is representable iff Σ A is a
singleton.

\begin{code}

_≊_ : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → (X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
A ≊ B = Σ η ꞉ Nat A B , is-fiberwise-equiv η

is-representable : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-representable A = Σ x ꞉ domain A , Id x ≊ A

singleton-representable : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                        → ∃! A
                        → is-representable A
singleton-representable {𝓤} {𝓥} {X} {A} ((x , a) , cc) =
  x ,
  yoneda-nat x A a ,
  Yoneda-Theorem-forth x (yoneda-nat x A a) ((x , a) , cc)

representable-singleton : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                        → is-representable A
                        → ∃! A
representable-singleton (x , (η , φ)) = Yoneda-Theorem-back x η φ

\end{code}

We also have the following corollaries:

\begin{code}

is-vv-equiv-has-adj'
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (g : Y → X)
 → is-vv-equiv g
 → Σ f ꞉ (X → Y) , ((x : X) (y : Y) → (f x ＝ y) ≃ (g y ＝ x))
is-vv-equiv-has-adj' g φ = pr₁ γ ,
                           λ x y → pr₁ (pr₂ γ) x y ,
                                   nats-with-sections-are-equivs
                                     (pr₁ γ x) (pr₁ (pr₂ γ) x) (pr₂ (pr₂ γ) x) y
 where
  γ : has-adj g
  γ = is-vv-equiv-has-adj g φ

has-adj-is-vv-equiv'
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (g : Y → X)
 → (Σ f ꞉ (X → Y) , ((x : X) (y : Y) → (f x ＝ y) ≃ (g y ＝ x)))
 → is-vv-equiv g
has-adj-is-vv-equiv' g (f , ψ) =
 has-adj-is-vv-equiv g (f , (λ x y → pr₁ (ψ x y)) , (λ x y → pr₁ (pr₂(ψ x y))))

\end{code}

Here is an application of the Yoneda machinery to a well-known result
by Voevodsky. If products preserve contractibility, then function
extensionality holds (happly is an equivalence).

\begin{code}

funext-via-singletons
 : ((X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
       → ((x : X) → is-singleton (Y x)) → is-singleton (Π Y))
 → funext 𝓤 𝓥
funext-via-singletons {𝓤} {𝓥} φ {X} {Y} f = γ
 where
  c : is-singleton (Π x ꞉ X , Σ y ꞉ Y x , f x ＝ y)
  c = φ X
        (λ x → Σ y ꞉ Y x , f x ＝ y)
        (λ x → singleton-types-are-singletons (f x))

  A : Π Y → 𝓤 ⊔ 𝓥 ̇
  A g = (x : X) → f x ＝ g x

  r : (Π x ꞉ X , Σ y ꞉ Y x , f x ＝ y) → Σ A
  r = ΠΣ-distr

  r-has-section : has-section r
  r-has-section = equivs-have-sections ⌜ ΠΣ-distr-≃ ⌝ ⌜ ΠΣ-distr-≃ ⌝-is-equiv

  d : ∃! A
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

open import UF.Univalence

univalence-via-singletons→ : is-univalent 𝓤 → (X : 𝓤 ̇ ) → ∃! Y ꞉ 𝓤 ̇ , X ≃ Y
univalence-via-singletons→ ua X = representable-singleton (X , (idtoeq X , ua X))

univalence-via-singletons← : ((X : 𝓤 ̇ ) → ∃! Y ꞉ 𝓤 ̇ , X ≃ Y) → is-univalent 𝓤
univalence-via-singletons← φ X = universality-equiv X (≃-refl X)
                                  (central-point-is-universal
                                    (X ≃_)
                                    (X , ≃-refl X)
                                    (singletons-are-props (φ X) (X , ≃-refl X)))

univalence-via-singletons : is-univalent 𝓤 ↔ ((X : 𝓤 ̇ ) → ∃! Y ꞉ 𝓤 ̇ , X ≃ Y)
univalence-via-singletons = univalence-via-singletons→ ,
                            univalence-via-singletons←

\end{code}

Notice that is-singleton can be replaced by is-prop in the formulation
of this logical equivalence (exercise).

Appendix.

Two natural transformations with the same Yoneda elements are
(point-point-wise) equal. This can be proved using J (or equivalently
pattern matching), but we use the opportunity to illustrate how to use
the Yoneda Lemma.

\begin{code}

yoneda-elem-lc : {X : 𝓤 ̇ } {x : X} {A : X → 𝓥 ̇ }
                 (η θ : Nat (Id x) A)
               → yoneda-elem x A η ＝ yoneda-elem x A θ → η ≈ θ
yoneda-elem-lc {𝓤} {𝓥} {X} {x} {A} η θ q y p =
  η y p                                  ＝⟨ (yoneda-lemma x A η y p)⁻¹ ⟩
  yoneda-nat x A (yoneda-elem x A η) y p ＝⟨ ap (λ - → yoneda-nat x A - y p) q ⟩
  yoneda-nat x A (yoneda-elem x A θ) y p ＝⟨ yoneda-lemma x A θ y p ⟩
  θ y p                                  ∎

Yoneda-elem-lc : {X : 𝓤 ̇ } {x : X} {A : X → 𝓥 ̇ }
                 (η θ : (y : X) → x ＝ y → A y)
               → η x refl ＝ θ x refl
               → (y : X) (p : x ＝ y)
               → η y p ＝ θ y p
Yoneda-elem-lc = yoneda-elem-lc

\end{code}

Some special cases of interest, which probably speak for themselves:

\begin{code}

yoneda-nat-Id : {X : 𝓤 ̇ }
                (x {y} : X)
              → Id x y
              → Nat (Id y) (Id x)
yoneda-nat-Id x {y} = yoneda-nat y (Id x)

Yoneda-nat-Id : {X : 𝓤 ̇ }
                (x {y} : X)
              → x ＝ y
              → (z : X) → y ＝ z → x ＝ z
Yoneda-nat-Id = yoneda-nat-Id

Id-charac : FunExt
          → {X : 𝓤 ̇ }
            (x {y} : X)
          → (x ＝ y) ≃ Nat (Id y) (Id x)
Id-charac fe {X} x {y} = yoneda-equivalence fe y (Id x)

yoneda-nat-Eq : (X {Y} : 𝓤 ̇ )
              → X ≃ Y
              → Nat (Y ＝_) (X ≃_)
yoneda-nat-Eq X {Y} = yoneda-nat Y (X ≃_)

yoneda-elem-Id : {X : 𝓤 ̇ }
                 (x {y} : X)
               → Nat (Id y) (Id x)
               → Id x y
yoneda-elem-Id x {y} = yoneda-elem y (Id x)

Yoneda-elem-Id : {X : 𝓤 ̇ }
                 (x {y} : X)
               → ((z : X) → y ＝ z → x ＝ z)
               → x ＝ y
Yoneda-elem-Id = yoneda-elem-Id

yoneda-lemma-Id : {X : 𝓤 ̇ } (x {y} : X)
                  (η : Nat (Id y) (Id x))
                  (z : X)
                  (p : y ＝ z)
                → yoneda-elem-Id x η ∙ p ＝ η z p
yoneda-lemma-Id x {y} = yoneda-lemma y (Id x)

Yoneda-lemma-Id : {X : 𝓤 ̇ }
                  (x {y} : X)
                  (η : (z : X) → y ＝ z → x ＝ z)
                  (z : X)
                  (p : y ＝ z)
                → η y refl ∙ p ＝ η z p
Yoneda-lemma-Id = yoneda-lemma-Id

yoneda-const : {X : 𝓤 ̇ } {B : 𝓥 ̇ }
               {x : X}
               (η : Nat (Id x) (λ _ → B))
               (y : X)
               (p : x ＝ y)
             → yoneda-elem x (λ _ → B) η ＝ η y p
yoneda-const η = yoneda-elem-lc (λ y p → yoneda-elem _ _ η) η refl

Yoneda-const : {X : 𝓤 ̇ } {B : 𝓥 ̇ }
               {x : X} (η : (y : X) → x ＝ y → B)
               (y : X)
               (p : x ＝ y)
             → η x refl ＝ η y p
Yoneda-const = yoneda-const

\end{code}

The following is traditionally proved by induction on the identity
type (as articulated by Jbased or J), but here we use the Yoneda
machinery instead, again for the sake of illustration.

\begin{code}

singleton-types-are-singletons-bis : {X : 𝓤 ̇ } (x : X)
                                   → is-central (singleton-type x) (x , refl)
singleton-types-are-singletons-bis {𝓤} {X} x (y , p) = yoneda-const η y p
 where
  η : (y : X) → x ＝ y → singleton-type x
  η y p = (y , p)

\end{code}

What the following says is that the Yoneda machinery could have been
taken as primitive, as an alternative to Jbased or J, in the sense
that the latter can be recovered from the former.

\begin{code}

private

 Jbased'' : {X : 𝓤 ̇ } (x : X) (A : singleton-type x → 𝓥 ̇ )
          → A (x , refl) → Π A
 Jbased'' x A a w =
  yoneda-nat (x , refl) A a w (singleton-types-are-singletons' w)

 Jbased' : {X : 𝓤 ̇ } (x : X) (B : (y : X) → x ＝ y → 𝓥 ̇ )
         → B x refl → (y : X) → Π (B y)
 Jbased' x B b y p = Jbased'' x (uncurry B) b (y , p)

\end{code}

And now some more uses of Yoneda to prove things that traditionally
are proved using J(based), again for the sake of illustration:

\begin{code}

refl-left-neutral-bis : {X : 𝓤 ̇ }
                        {x y : X}
                        {p : x ＝ y}
                      → refl ∙ p ＝ p
refl-left-neutral-bis {𝓤} {X} {x} {y} {p} =
 yoneda-lemma x (Id x) (λ y → id) y p

⁻¹-involutive-bis : {X : 𝓤 ̇ }
                    {x y : X}
                    (p : x ＝ y)
                  → (p ⁻¹)⁻¹ ＝ p
⁻¹-involutive-bis {𝓤} {X} {x} {y} =
 yoneda-elem-lc (λ x p → (p ⁻¹)⁻¹) (λ x p → p) refl y

⁻¹-contravariant-bis : {X : 𝓤 ̇ }
                       {x y : X}
                       (p : x ＝ y)
                       {z : X}
                       (q : y ＝ z)
                     → q ⁻¹ ∙ p ⁻¹ ＝ (p ∙ q)⁻¹
⁻¹-contravariant-bis {𝓤} {X} {x} {y} p {z} =
 yoneda-elem-lc (λ z q → q ⁻¹ ∙ p ⁻¹)
  (λ z q → (p ∙ q) ⁻¹)
  refl-left-neutral-bis
  z

\end{code}

Associativity also follows from the Yoneda Lemma, again with the same
proof method. Notice that we prove that two functions (in a context)
are equal without using function extensionality:

\begin{code}

ext-assoc : {X : 𝓤 ̇ } {z t : X} (r : z ＝ t)
          → (λ (x y : X) (p : x ＝ y) (q : y ＝ z) → (p ∙ q) ∙ r)
          ＝ (λ (x y : X) (p : x ＝ y) (q : y ＝ z) → p ∙ (q ∙ r))
ext-assoc {𝓤} {X} {z} {t} =
 yoneda-elem-lc {𝓤} {𝓤} {X} {z}
  {λ - → (x y : X) (p : x ＝ y) (q : y ＝ z) → x ＝ - }
  (λ z r x y p q → p ∙ q ∙ r)
  (λ z r x y p q → p ∙ (q ∙ r))
  refl
  t

\end{code}

Then of course associativity of path composition follows:

\begin{code}

assoc-bis : {X : 𝓤 ̇ }
            {x y z t : X}
            (p : x ＝ y)
            (q : y ＝ z)
            (r : z ＝ t)
          → (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
assoc-bis {𝓤} {X} {x} {y} p q r = ap (λ - → - x y p q) (ext-assoc r)

left-inverse-bis : {X : 𝓤 ̇ }
                   {x y : X}
                   (p : x ＝ y)
                 → p ⁻¹ ∙ p ＝ refl
left-inverse-bis {𝓤} {X} {x} {y} =
 yoneda-elem-lc (λ x p → p ⁻¹ ∙ p) (λ x p → refl) refl y

right-inverse-bis : {X : 𝓤 ̇ }
                    {x y : X}
                    (p : x ＝ y)
                  → refl ＝ p ∙ p ⁻¹
right-inverse-bis {𝓤} {X} {x} {y} =
 yoneda-const (λ x p → p ∙ p ⁻¹) y

from-Σ-Id : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
            {(x , a) (y , b) : Σ A}
          → (x , a) ＝ (y , b)
          → Σ p ꞉ x ＝ y , yoneda-nat x A a y p ＝ b
from-Σ-Id {𝓤} {𝓥} {X} {A} {x , a} {τ} =
 yoneda-nat (x , yoneda-nat x A a x refl) B (refl , refl) τ
  where
    B : (τ : Σ A) → 𝓤 ⊔ 𝓥 ̇
    B (y , b) = Σ p ꞉ x ＝ y , yoneda-nat x A a y p ＝ b

to-Σ-Id : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
          {(x , a) (y , b) : Σ A}
        → (Σ p ꞉ x ＝ y , yoneda-nat x A a y p ＝ b)
        → (x , a) ＝ (y , b)
to-Σ-Id {𝓤} {𝓥} {X} {A} {x , a} {y , b} (p , q) = r
 where
  η : (y : X) → x ＝ y → Σ A
  η y p = (y , yoneda-nat x A a y p)

  yc : (x , a) ＝ (y , yoneda-nat x A a y p)
  yc = yoneda-const η y p

  r : (x , a) ＝ (y , b)
  r = yoneda-nat (yoneda-nat x A a y p) (λ b → (x , a) ＝ (y , b)) yc b q

from-Σ-Id' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
             {(x , a) (y , b) : Σ A}
           → (x , a) ＝ (y , b)
           → Σ p ꞉ x ＝ y , transport A p a ＝ b
from-Σ-Id' = from-Σ-Id

to-Σ-Id' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
             {(x , a) (y , b) : Σ A}
           → Σ p ꞉ x ＝ y , transport A p a ＝ b
           → (x , a) ＝ (y , b)
to-Σ-Id' = to-Σ-Id

NatΣ-lc' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
           (ζ : Nat A B)
         → ((x : X) → left-cancellable(ζ x))
         → left-cancellable(NatΣ ζ)
NatΣ-lc' {𝓤} {𝓥} {𝓦} {X} {A} {B} ζ ζ-lc {(x , a)} {(y , b)} pq = g
  where
    p : x ＝ y
    p = pr₁ (from-Σ-Id pq)

    η : Nat (Id x) B
    η = yoneda-nat x B (ζ x a)

    q : η y p ＝ ζ y b
    q = pr₂ (from-Σ-Id pq)

    θ : Nat (Id x) A
    θ = yoneda-nat x A a

    η' : Nat (Id x) B
    η' y p = ζ y (θ y p)

    r : η' ≈ η
    r = yoneda-elem-lc η' η refl

    r' : ζ y (θ y p) ＝ η y p
    r' = r y p

    s : ζ y (θ y p) ＝ ζ y b
    s = r' ∙ q

    t : θ y p ＝ b
    t = ζ-lc y s

    g : x , a ＝ y , b
    g = to-Σ-Id (p , t)

yoneda-equivalence-Σ : FunExt
                     → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                     → Σ A ≃ (Σ x ꞉ X , Nat (Id x) A)
yoneda-equivalence-Σ fe A = Σ-cong (λ x → yoneda-equivalence fe x A)


nats-are-uniquely-transports : FunExt
                             → {X : 𝓤 ̇ }
                               (x : X)
                               (A : X → 𝓥 ̇ )
                               (η : Nat (Id x) A)
                             → ∃! a ꞉ A x , (λ y p → transport A p a) ＝ η
nats-are-uniquely-transports fe x A = equivs-are-vv-equivs
                                       (yoneda-nat x A)
                                       (yoneda-nat-is-equiv fe x A)

adj-obs : FunExt
        → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
          (f : X → Y)
          (g : Y → X)
          (x : X)
          (η : (y : Y) → f x ＝ y → g y ＝ x)
        → ∃! q ꞉ g (f x) ＝ x , (λ y p → transport (λ - → g - ＝ x) p q) ＝ η
adj-obs fe f g x = nats-are-uniquely-transports fe (f x) (λ y → g y ＝ x)

\end{code}

We need this elsewhere:

\begin{code}

idtoeq-bis : (X : 𝓤 ̇ ) → Nat (X ＝_) (X ≃_)
idtoeq-bis X = yoneda-nat X (X ≃_) (≃-refl X)

Idtofun' : (X : 𝓤 ̇ ) → Nat (Id X) (λ Y → X → Y)
Idtofun' X = yoneda-nat X (λ Y → X → Y) id

idtofun-agree' : (X : 𝓤 ̇ ) → idtofun X ≈ Idtofun' X
idtofun-agree' X = yoneda-elem-lc (idtofun X) (Idtofun' X) refl

\end{code}
