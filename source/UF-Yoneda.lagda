\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Yoneda where

open import SpartanMLTT
-- open import UF-Base -- We redo the base via Yoneda! (Without name clashes.)
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Retracts
open import UF-Equiv
open import UF-FunExt
open import UF-Equiv-FunExt

\end{code}

We now consider "natural transformations" (defined in Base) and the
Yoneda-machinery for them as discussed in
http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html

The Yoneda element induced by a natural transformation:

\begin{code}

yoneda-elem : ∀ {U V} {X : U ̇} {x : X} (A : X → V ̇)
           → Nat (Id x) A → A x
yoneda-elem {U} {V} {X} {x} A η = η x refl

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

Notice that this is the based recursion principle for the identity type.

The Yoneda Lemma says that every natural transformation is induced by
its Yoneda element:

\begin{code}

yoneda-lemma : ∀ {U V} {X : U ̇} {x : X} (A : X → V ̇) (η : Nat (Id x) A)
            → yoneda-nat A (yoneda-elem A η) ≈ η 
yoneda-lemma A η x refl = refl

Yoneda-lemma : ∀ {U V} {X : U ̇} {x : X} (A : X → V ̇) (η : (y : X) → x ≡ y → A y) (y : X) (p : x ≡ y)
             → transport A p (η x refl) ≡ η y p
Yoneda-lemma = yoneda-lemma

\end{code}

From another point of view, the Yoneda lemma says that very natural
transformation η is recursively defined.

The word "computation" here arises from a tradition in MLTT and should
not be taken too seriously:

\begin{code}

yoneda-computation : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} (a : A x) 
                   → yoneda-elem A (yoneda-nat A a) ≡ a
yoneda-computation a = refl

Yoneda-computation : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} (a : A x) 
                   → transport A refl a ≡ a
Yoneda-computation {U} {V} {X} {x} {A} = yoneda-computation {U} {V} {X} {x} {A}

yoneda-nat-isEquiv : (∀ U V → FunExt U V) → ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇)
                   → isEquiv (yoneda-nat A)
yoneda-nat-isEquiv fe {U} {V} {X} x A =
   (yoneda-elem A , λ η → funext (fe U (U ⊔ V)) (λ y → funext (fe U V) (λ p → yoneda-lemma A η y p))) ,
   (yoneda-elem A , yoneda-computation {U} {V} {X} {x} {A})

yoneda-equivalence : (∀ U V → FunExt U V) → ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇)
                   → A x ≃ Nat (Id x) A  
yoneda-equivalence fe x A = yoneda-nat A , yoneda-nat-isEquiv fe x A

nats-are-uniquely-transports : (∀ U V → FunExt U V) → ∀ {U V} {X : U ̇} (x : X) (A : X → V ̇) (η : Nat (Id x) A)
                            → isSingleton (Σ \(a : A x) → (λ y p → transport A p a) ≡ η)
nats-are-uniquely-transports fe x A = isEquiv-isVoevodskyEquiv (yoneda-nat A) (yoneda-nat-isEquiv fe x A) 
\end{code}

Two natural transformations with the same Yoneda elements are
(point-point-wise) equal. This can be proved using J (or equivalently
pattern matching), but we use the opportunity to illustrate how to use
the Yoneda Lemma.

\begin{code}

yoneda-elem-lc : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} (η θ : Nat (Id x) A)             
              → yoneda-elem A η ≡ yoneda-elem A θ → η ≈ θ
yoneda-elem-lc {U} {V} {X} {x} {A} η θ q y p =
  η y p                              ≡⟨ (yoneda-lemma A η y p)⁻¹ ⟩
  yoneda-nat A (yoneda-elem A η) y p ≡⟨ ap (λ e → yoneda-nat A e y p) q ⟩
  yoneda-nat A (yoneda-elem A θ) y p ≡⟨ yoneda-lemma A θ y p ⟩
  θ y p ∎

Yoneda-elem-lc : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} (η θ : (y : X) → x ≡ y → A y)             
              → η x refl ≡ θ x refl → (y : X) (p : x ≡ y) → η y p ≡ θ y p
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
              → η y refl ∙ p ≡ η z p
Yoneda-lemma' = yoneda-lemma'

yoneda-lemma'' : ∀ {U} {X : U ̇} (x {y} : X) (η : Nat (Id y) (Id x)) (z : X) (p : y ≡ z)
              → yoneda-nat' x (yoneda-elem' x η) z p ≡ η z p
yoneda-lemma'' x = yoneda-lemma (Id x)

hedberg-lemma : ∀ {U} {X : U ̇} (x : X) (η : Nat (Id x) (Id x)) (y : X) (p : x ≡ y)
              → (yoneda-elem' x η) ∙ p ≡ η y p
hedberg-lemma x η y p = yoneda-lemma' x η y p

Hedberg-lemma : ∀ {U} {X : U ̇} (x : X) (η : (y : X) → x ≡ y → x ≡ y) (y : X) (p : x ≡ y)
              → η x refl ∙ p ≡ η y p
Hedberg-lemma = hedberg-lemma

yoneda-const : ∀ {U V} {X : U ̇} {B : V ̇} {x : X} (η : Nat (Id x) (λ _ → B)) (y : X) (p : x ≡ y)
             → yoneda-elem (λ _ → B) η ≡ η y p 
yoneda-const η = yoneda-elem-lc (λ y p → yoneda-elem _ η) η refl

Yoneda-const : ∀ {U V} {X : U ̇} {B : V ̇} {x : X} (η : (y : X) → x ≡ y → B) (y : X) (p : x ≡ y)
             → η x refl ≡ η y p 
Yoneda-const = yoneda-const

\end{code}

The following is traditionally proved by induction on the identity
type (as articulated by Jbased or J in the module SpartanMLTT), but
here we use the Yoneda machinery instead, again for the sake of
illustration.

\begin{code}

singleton-types-are-singletons-bis : ∀ {U} {X : U ̇} {x : X}
                                  → is-the-only-element (x , refl)
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
         → A (x , refl) → Π A
Jbased'' x A b w = yoneda-nat A b w (singleton-types-are-singletons w)

Jbased' : ∀ {U V} {X : U ̇} (x : X) (B : (y : X) → x ≡ y → V ̇)
        → B x refl → (y : X) (p : x ≡ y) → B y p
Jbased' x B b y p = Jbased'' x (uncurry B) b (y , p)

\end{code}

And now some more uses of Yoneda to prove things that traditionally
are proved using J(based), again for the sake of illustration:

\begin{code}

refl-left-neutral-bis : ∀ {U} {X : U ̇} {x y : X} {p : x ≡ y} → refl ∙ p ≡ p
refl-left-neutral-bis {U} {X} {x} {y} {p} = yoneda-lemma (Id x) (λ y p → p) y p

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
assoc-bis {U} {X} {x} {y} p q r = ap (λ f → f x y p q) (ext-assoc r) 

left-inverse : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → p ⁻¹ ∙ p ≡ refl
left-inverse {U} {X} {x} {y} = yoneda-elem-lc (λ x p → p ⁻¹ ∙ p) (λ x p → refl) refl y

right-inverse : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → refl ≡ p ∙ p ⁻¹
right-inverse {U} {X} {x} {y} = yoneda-const (λ x p → p ∙ p ⁻¹) y

cancel-left : ∀ {U} {X : U ̇} {x y z : X} {p : x ≡ y} {q r : y ≡ z}
            → p ∙ q ≡ p ∙ r → q ≡ r
cancel-left {U} {X} {x} {y} {z} {p} {q} {r} s = 
       q              ≡⟨ refl-left-neutral-bis ⁻¹ ⟩
       refl ∙ q       ≡⟨ ap (λ t → t ∙ q) ((left-inverse p)⁻¹) ⟩
       (p ⁻¹ ∙ p) ∙ q ≡⟨ assoc-bis (p ⁻¹) p q ⟩
       p ⁻¹ ∙ (p ∙ q) ≡⟨ ap (λ t → p ⁻¹ ∙ t) s ⟩
       p ⁻¹ ∙ (p ∙ r) ≡⟨ (assoc-bis (p ⁻¹) p r)⁻¹ ⟩
       (p ⁻¹ ∙ p) ∙ r ≡⟨ ap (λ t → t ∙ r) (left-inverse p) ⟩
       refl ∙ r       ≡⟨ refl-left-neutral-bis ⟩
       r ∎

from-Σ-Id : ∀ {U V} {X : U ̇} {A : X → V ̇} {σ τ : Σ A}
          → σ ≡ τ
          → Σ \(p : pr₁ σ ≡ pr₁ τ) → yoneda-nat A (pr₂ σ) (pr₁ τ) p ≡ pr₂ τ
from-Σ-Id {U} {V} {X} {A} {x , a} {τ} = yoneda-nat B (refl , refl) τ
 where
   B : (τ : Σ A) → U ⊔ V ̇
   B τ = Σ \(p : x ≡ pr₁ τ) → yoneda-nat A a (pr₁ τ) p ≡ pr₂ τ

to-Σ-Id : ∀ {U V} {X : U ̇} {A : X → V ̇} {σ τ : Σ A}
          → (Σ \(p : pr₁ σ ≡ pr₁ τ) → yoneda-nat A (pr₂ σ) (pr₁ τ) p ≡ pr₂ τ)
          → σ ≡ τ
to-Σ-Id {U} {V} {X} {A} {x , a} {y , b} (p , q) = r
 where
  η : (y : X) → x ≡ y → Σ A
  η y p = (y , yoneda-nat A a y p)
  yc : (x , a) ≡ (y , yoneda-nat A a y p)
  yc = yoneda-const η y p
  r : (x , a) ≡ (y , b)
  r = yoneda-nat (λ b → (x , a) ≡ (y , b)) yc b q

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
    η = yoneda-nat B (ζ x a)
    q : η y p ≡ ζ y b
    q = pr₂ (from-Σ-Id pq)
    θ : Nat (Id x) A
    θ = yoneda-nat A a
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

\end{code}

Next we observe that "only elements" as defined above are universal
elements as in category theory.

\begin{code}

is-universal-element : ∀ {U V} {X : U ̇} {A : X → V ̇} → Σ A → U ⊔ V ̇
is-universal-element {U} {V} {X} {A} (x , a) = ∀ y (b : A y) → Σ \(p : x ≡ y) → yoneda-nat A a y p ≡ b

universal-element-is-the-only-element : ∀ {U V} {X : U ̇} {A : X → V ̇} (σ : Σ A)
                                      → is-universal-element σ → is-the-only-element σ
universal-element-is-the-only-element {U} {V} {X} {A} (x , a) u (y , b) = to-Σ-Id ((u y) b)

unique-element-is-universal-element : ∀ {U V} {X : U ̇} (A : X → V ̇) (σ : Σ A)
                                    → is-the-only-element σ → is-universal-element σ
unique-element-is-universal-element A (x , a) φ y b = from-Σ-Id (φ(y , b))
 
\end{code}

The following says that if the pair (x,a) is a universal element, then
the natural transformation it induces (namely yoneda-nat {U} {X} {x}
a) has a section and a retraction (which can be taken to be the same
function), and hence is an equivalence. Here having a section or
retraction is data not property in general, but it is in some cases
considered below.

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

The converse is trivial:

\begin{code}

section-universality : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                     → ((y : X) → hasSection(yoneda-nat A a y))
                     → is-universal-element (x , a)
section-universality x a φ y b = pr₁(φ y) b , pr₂(φ y) b

\end{code}

Then the Yoneda Theorem (proved below) says that any η : Nat (Id x) A)
is a natural equivalence iff Σ A is a singleton. This, in turn, is
equivalent to η being a natural retraction, and we start with it:

\begin{code}

Yoneda-section-forth : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (η : Nat (Id x) A)
                     → isSingleton (Σ A) → (y : X) → hasSection (η y)
Yoneda-section-forth {U} {V} {X} {A} x η iss y = g
 where
  u : is-universal-element (x , yoneda-elem A η)
  u = unique-element-is-universal-element A (x , yoneda-elem A η) (isSingleton-isProp iss (x , yoneda-elem A η))
  h : yoneda-nat A (yoneda-elem A η) y ∼ η y
  h = yoneda-lemma A η y
  g : hasSection (η y)
  g = hasSection-closed-under-∼' (universality-section x (yoneda-elem A η) u y) h

Yoneda-section-back : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (η : Nat (Id x) A)
                   → ((y : X) → hasSection (η y)) → isSingleton (Σ A)
Yoneda-section-back {U} {V} {X} {A} x η φ = c
 where
  h : ∀ y → yoneda-nat A (yoneda-elem A η) y ∼ η y
  h = yoneda-lemma A η
  g : ∀ y → hasSection (yoneda-nat A (yoneda-elem A η) y)
  g y = hasSection-closed-under-∼ (η y) (yoneda-nat A (yoneda-elem A η) y) (φ y) (h y)
  u : is-universal-element (x , yoneda-elem A η)
  u = section-universality x (yoneda-elem A η) g 
  c : isSingleton (Σ A)
  c = (x , yoneda-elem A η) , (universal-element-is-the-only-element (x , yoneda-elem A η) u)
  
Yoneda-section : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (η : Nat (Id x) A)
               → isSingleton (Σ A) ⇔ ((y : X) → hasSection (η y))
Yoneda-section x η = Yoneda-section-forth x η , Yoneda-section-back x η              

\end{code}

Here is a direct application (24th April 2018).

\begin{code}

equiv-adj : ∀ {U V : Universe} {X : U ̇} {Y : V ̇} (f : X → Y) (g : Y → X)
              (η : (x : X) (y : Y) → f x ≡ y → g y ≡ x)
          → ((x : X) (y : Y) → hasSection (η x y)) ⇔ isVoevodskyEquiv g 
equiv-adj f g η = (λ isv x → Yoneda-section-back (f x) (η x) (isv x)) , 
                  (λ φ x → Yoneda-section-forth (f x) (η x) (φ x))

\end{code}

This motivates the following definition.

\begin{code}

hasAdj : ∀ {U V} {X : U ̇} {Y : V ̇} → (Y → X) → U ⊔ V ̇
hasAdj g = Σ \(f : cod g → dom g) → Σ \(η : ∀ x y → f x ≡ y → g y ≡ x) → ∀ x y → hasSection(η x y)

adj-obs : (∀ U V → FunExt U V) → ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) (g : Y → X) (x : X)
          (η : (y : Y) → f x ≡ y → g y ≡ x)
        → isSingleton (Σ \(q : g (f x) ≡ x) → (λ (y : Y) (p : f x ≡ y) → transport (λ y → g y ≡ x) p q) ≡ η)
adj-obs fe f g x = nats-are-uniquely-transports fe (f x) (λ y → g y ≡ x)

isVoevodskyEquiv-hasAdj : ∀ {U V} {X : U ̇} {Y : V ̇} (g : Y → X)
                       → isVoevodskyEquiv g → hasAdj g
isVoevodskyEquiv-hasAdj {U} {V} {X} {Y} g isv = f , η , hass
 where
  f : X → Y
  f = pr₁ (pr₁ (isVoevodskyEquiv-isEquiv g isv))
  gf : (x : X) → g (f x) ≡ x
  gf = pr₂ (pr₁ (isVoevodskyEquiv-isEquiv g isv))
  η : (x : X) (y : Y) → f x ≡ y → g y ≡ x
  η x y p = transport (λ y → g y ≡ x) p (gf x )
  hass : (x : X) (y : Y) → hasSection (η x y)
  hass x = Yoneda-section-forth (f x) (η x) (isv x)

hasAdj-isVoevodskyEquiv : ∀ {U V : Universe} {X : U ̇} {Y : V ̇} (g : Y → X)
                        → hasAdj g → isVoevodskyEquiv g
hasAdj-isVoevodskyEquiv g (f , η , hass) x = Yoneda-section-back (f x) (η x) (hass x)
  
\end{code}

A natural transformation of the above kind is an equivalence iff it has a section,
as shown in https://github.com/HoTT/book/issues/718#issuecomment-65378867:

\begin{code}

idemp-is-id : ∀ {U} {X : U ̇} {x : X} (e : (y : X) → x ≡ y → x ≡ y) (y : X) (p : x ≡ y)
           → e y (e y p) ≡ e y p → e y p ≡ p
idemp-is-id {U} {X} {x} e y p idemp = cancel-left (
        e x refl ∙ e y p ≡⟨ Hedberg-lemma x e y (e y p) ⟩
        e y (e y p)      ≡⟨ idemp ⟩
        e y p            ≡⟨ (Hedberg-lemma x e y p)⁻¹ ⟩
        e x refl ∙ p     ∎ )

nat-retraction-is-section : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (η : Nat (Id x) A)
                          → ((y : X) → hasSection(η y)) 
                          → ((y : X) → hasRetraction(η y))
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
  hasr : (y : X) → hasRetraction(η y)
  hasr y = s y , e-is-id y

\end{code}

The above use of the word "is" is justified by the following:

\begin{code}

nat-retraction-is-section-uniquely : (∀ U V → FunExt U V) → ∀ {U V} {X : U ̇} {A : X → V ̇}
                                     (x : X) (η : Nat (Id x) A)
                                   → ((y : X) → hasSection(η y)) 
                                   → ((y : X) → isSingleton(hasRetraction(η y)))
nat-retraction-is-section-uniquely fe x η hass y = inhabited-proposition-isSingleton
                                                      (nat-retraction-is-section x η hass y)
                                                      (hass-isprop-hasr fe (η y) (hass y))

nat-hasSection-isProp : (∀ U V → FunExt U V) → ∀ {U V} {X : U ̇} {A : X → V ̇}
                        (x : X) (η : Nat (Id x) A)
                      → isProp ((y : X) → hasSection (η y)) 
nat-hasSection-isProp fe {U} {V} {X} {A} x η φ = isProp-exponential-ideal (fe U (U ⊔ V)) γ φ
  where
   γ : (y : X) → isProp (hasSection (η y))
   γ y = hasr-isprop-hass fe (η y) (nat-retraction-is-section x η φ y)

nat-retraction-isEquiv : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (f : Nat (Id x) A)
                      → ((y : X) → hasSection(f y)) 
                      → ((y : X) → isEquiv(f y))
nat-retraction-isEquiv {U} {V} {X} {A} x f hass y = (hass y , nat-retraction-is-section x f hass y)

\end{code}

We are interested in the following corollaries:

\begin{code}

universality-equiv : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                   → is-universal-element (x , a)
                   → (y : X) → isEquiv(yoneda-nat A a y)
universality-equiv {U} {V} {X} {A} x a u = nat-retraction-isEquiv x (yoneda-nat A a)
                                                                    (universality-section x a u)
  
equiv-universality : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (a : A x)
                   → ((y : X) → isEquiv(yoneda-nat A a y))
                   → is-universal-element (x , a)
equiv-universality x a φ = section-universality x a (λ y → pr₁ (φ y))

Yoneda-Theorem-forth : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (η : Nat (Id x) A)
                    → isSingleton (Σ A) → (y : X) → isEquiv (η y)
Yoneda-Theorem-forth x η iss = nat-retraction-isEquiv x η (Yoneda-section-forth x η iss)

Yoneda-Theorem-back : ∀ {U V} {X : U ̇} {A : X → V ̇} (x : X) (η : Nat (Id x) A)
                   → ((y : X) → isEquiv (η y)) → isSingleton (Σ A)
Yoneda-Theorem-back x η φ = Yoneda-section-back x η (λ y → pr₁(φ y))

\end{code}

Next we conclude that a presheaf A is representable iff Σ A is a
singleton.

\begin{code}

_≊_ : ∀ {U V W} {X : U ̇} → (X → V ̇) → (X → W ̇) → U ⊔ V ⊔ W ̇
A ≊ B = Σ \(η : Nat A B) → ∀ x → isEquiv(η x)

isRepresentable : ∀ {U V} {X : U ̇} → (X → V ̇) → U ⊔ V ̇
isRepresentable A = Σ \x → Id x ≊ A

singleton-representable : ∀ {U V} {X : U ̇} {A : X → V ̇} → isSingleton (Σ A) → isRepresentable A 
singleton-representable {U} {V} {X} {A} ((x , a) , cc) = x ,
                                                         yoneda-nat A a ,
                                                         Yoneda-Theorem-forth x (yoneda-nat A a) ((x , a) , cc)

representable-singleton : ∀ {U V} {X : U ̇} {A : X → V ̇} → isRepresentable A → isSingleton (Σ A)
representable-singleton {U} {V} {X} {A} (x , (η , φ)) = Yoneda-Theorem-back x η φ

\end{code}

We also have the following corollaries:

\begin{code}

isVoevodskyEquiv-hasAdj' : ∀ {U V : Universe} {X : U ̇} {Y : V ̇} (g : Y → X)
                        → isVoevodskyEquiv g → Σ \(f : X → Y) → (x : X) (y : Y) → (f x ≡ y) ≃ (g y ≡ x)
isVoevodskyEquiv-hasAdj' {U} {V} {X} {Y} g φ = (pr₁ γ) ,
                                               λ x y → (pr₁ (pr₂ γ) x y) ,
                                                       (nat-retraction-isEquiv (pr₁ γ x) (pr₁ (pr₂ γ) x) (pr₂ (pr₂ γ) x) y)
 where
  γ : hasAdj g
  γ = isVoevodskyEquiv-hasAdj g φ
  
hasAdj-isVoevodskyEquiv' : ∀ {U V : Universe} {X : U ̇} {Y : V ̇} (g : Y → X)
                        → (Σ \(f : X → Y) → (x : X) (y : Y) → (f x ≡ y) ≃ (g y ≡ x)) → isVoevodskyEquiv g
hasAdj-isVoevodskyEquiv' g (f , ψ) = hasAdj-isVoevodskyEquiv g (f , (λ x y → pr₁(ψ x y)) , (λ x y → pr₁(pr₂(ψ x y))))

\end{code}

We need this elsewhere:

\begin{code}

idtoeq-bis : ∀ {U} (X : U ̇) → Nat (Id X) (Eq X)
idtoeq-bis X = yoneda-nat (Eq X) (ideq X)

idtofun' : ∀ {U} (X : U ̇) → Nat (Id X) (λ Y → X → Y)
idtofun' X = yoneda-nat (λ Y → X → Y) id

idtofun-agree : ∀ {U} (X : U ̇) → idtofun X ≈ idtofun' X
idtofun-agree X = yoneda-elem-lc (idtofun X) (idtofun' X) refl

\end{code}
