\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Yoneda where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Equiv

\end{code}

We now consider "natural transformations" (defined in Base) and the
Yoneda-machinery for them as discussed in
http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html

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

singleton-types-are-singletons-bis : ∀ {U} {X : U ̇} {x : X}
                                  → is-the-only-element (x , idp x)
singleton-types-are-singletons-bis {U} {X} {x} (y , p) = yoneda-const η y p
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

idp-left-neutral-bis : ∀ {U} {X : U ̇} {x y : X} {p : x ≡ y} → idp x ∙ p ≡ p
idp-left-neutral-bis {U} {X} {x} {y} {p} = yoneda-lemma (Id x) (λ y p → p) y p

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

assoc-bis : ∀ {U} {X : U ̇} {x y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
      → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc-bis {U} {X} {x} {y} p q r = ap (λ f → f x y p q) (ext-assoc r) 

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

from-Σ-Id' : ∀ {U V} {X : U ̇} (A : X → V ̇) {σ τ : Σ A}
           → σ ≡ τ
           → Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ
from-Σ-Id' = from-Σ-Id

to-Σ-Id' : ∀ {U V} {X : U ̇} (A : X → V ̇) {σ τ : Σ A}
         → (Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
         → σ ≡ τ
to-Σ-Id' = to-Σ-Id

\end{code}

Next we observe that "only elements" as defined above are universal
elements as in category theory.

\begin{code}

is-universal-element : ∀ {U V} {X : U ̇} {A : X → V ̇} → Σ A → U ⊔ V ̇
is-universal-element {U} {V} {X} {A} (x , a) = ∀ y (b : A y) → Σ \(p : x ≡ y) → yoneda-nat A a y p ≡ b

universal-element-is-the-only-element : ∀ {U V} {X : U ̇} {A : X → V ̇} (σ : Σ A)
                                      → is-universal-element σ → is-the-only-element σ
universal-element-is-the-only-element {U} {V} {X} {A} (x , a) u (y , b) = to-Σ-Id A ((u y) b)

unique-element-is-universal-element : ∀ {U V} {X : U ̇} (A : X → V ̇) (σ : Σ A)
                                    → is-the-only-element σ → is-universal-element σ
unique-element-is-universal-element A (x , a) φ y b = from-Σ-Id A {x , a} {y , b} (φ(y , b))
 
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

natural-retraction-has-section : ∀ {U V} {X : U ̇} {A : X → V ̇}
                           (x : X) (r : Nat (Id x) A)
                        → ((y : X) → hasSection(r y)) 
                        → ((y : X) → hasRetraction(r y))
natural-retraction-has-section {U} {V} {X} {A} x r hass = hasr
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

natural-retraction-isEquiv : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (r : Nat (Id x) A)
                           → ((y : X) → hasSection(r y)) 
                           → ((y : X) → isEquiv(r y))
natural-retraction-isEquiv {U} {V} {X} {A} x r hass y = (hass y ,
                                                         natural-retraction-has-section x r hass y)

\end{code}

We are interested in this corollary:

\begin{code}

universality-equiv : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                   → is-universal-element (x , a)
                   → (y : X) → isEquiv(yoneda-nat A a y)
universality-equiv {U} {V} {X} {A} x a u = natural-retraction-isEquiv x (yoneda-nat A a)
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
  g = x , (yoneda-nat A a , universality-equiv x a (unique-element-is-universal-element A (x , a) cc))

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
  g = σ , universal-element-is-the-only-element σ is-ue-σ

\end{code}

\begin{code}

idtoeq-bis : ∀ {U} (X : U ̇) → Nat (Id X) (Eq X)
idtoeq-bis X = yoneda-nat (Eq X) (ideq X)

\end{code}

