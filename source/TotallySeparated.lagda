Martin Escardo 2011, 2017, 2018.

We define and study totally separated types (which could also have
been called 𝟚-separated types). Most of the material in this file is
from January 2018.

The terminology "totally separated" comes from topology, where it
means that the clopens separate the points. Here the maps into 𝟚
separate the points, formulated in a positive way.

Any type has a totally separated reflection, assuming function
extensionality and propositional truncations.

All the simple types (those obtained from 𝟚 and ℕ by iterating
function spaces) are totally separated (see the module
SimpleTypes). This is because the totally separated types form an
exponential ideal. Moreover, Π Y is totally separated for any family
Y:X→U provided Y x is totally separated for all x:X. This assumes
function extensionality.

In particular, the Cantor and Baire types 𝟚^ℕ and ℕ^ℕ are totally
separated (like in topology).

Closure under Σ fails in general. However, we have closure under _×_,
and ℕ∞ (defined with Σ) is totally separated (proved in the module
GenericConvergentSequence).

A counter-example to closure under Σ (from 2012) is in the file
http://www.cs.bham.ac.uk/~mhe/agda-new/FailureOfTotalSeparatedness.html

This is the "compactification" of ℕ with two points at infinity:

   Σ \(u : ℕ∞) → u ≡ ∞ → 𝟚.

If there is a 𝟚-valued function separating the two points at infinity,
then WLPO holds. (The totally separated reflection of this type should
be ℕ∞ if ¬WLPO holds.)

(In the context of topology, I learned this example from the late
Klaus Keimel (but the rendering in type theory is mine), where it is a
T₁, non-T₂, and non totally separated space which is zero dimensional
(has a base of clopen sets), and where the intersection of two compact
subsets need not be compact. The failure of the Hausdorff property is
with the two points an infinity, which can't be separated by disjoint
open neighbourhoods.)

The total separatedness of the reals (of any kind) should also give a
taboo. All non-sets fail (without the need of taboos) to be totally
separated, because totally separated spaces are sets.

Total separatedness is also characterized as the tightness of a
certain apartness relation that can be defined in any type.

We also show how to construct the tight reflection of any type
equipped with an apartness relation, given by a universal strongly
extensional map into a tight apartness type. Any type with a tight
apartness relation is a set, and so this reflection is always a set.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module TotallySeparated where

open import SpartanMLTT

open import Two-Properties
open import DiscreteAndSeparated hiding (tight)
open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Equiv
open import UF-LeftCancellable
open import UF-Embeddings
open import UF-FunExt
open import UF-PropTrunc
open import UF-ImageAndSurjection

\end{code}

An equality defined by a Leibniz principle with 𝟚-valued functions:

\begin{code}

_≡₂_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
x ≡₂ y = (p : _ → 𝟚) → p x ≡ p y

\end{code}

(In topological models, maps into 𝟚 classify clopens, and so total
separatedness amounts to "the clopens separate the points" in the
sense that any two points with the same clopen neighbourhoods are
equal. This notion in topology is called total separatedness.)

\begin{code}

is-totally-separated : 𝓤 ̇ → 𝓤 ̇
is-totally-separated X = {x y : X} → x ≡₂ y → x ≡ y

\end{code}

Synonym:

\begin{code}

𝟚-separated : 𝓤 ̇ → 𝓤 ̇
𝟚-separated = is-totally-separated

\end{code}

Excluded middle implies that all sets are discrete and hence totally
separated:

\begin{code}

discrete-totally-separated : {X : 𝓤 ̇} → is-discrete X → is-totally-separated X
discrete-totally-separated {𝓤} {X} d {x} {y} α = g
 where
  open import DecidableAndDetachable
  p : X → 𝟚
  p = pr₁ (characteristic-function (d x))

  φ : (y : X) → (p y ≡ ₀ → x ≡ y) × (p y ≡ ₁ → ¬ (x ≡ y))
  φ = pr₂ (characteristic-function (d x))

  b : p x ≡ ₀
  b = different-from-₁-equal-₀ (λ s → pr₂ (φ x) s refl)

  a : p y ≡ ₀
  a = (α p)⁻¹ ∙ b

  g : x ≡ y
  g = pr₁ (φ y) a

\end{code}

The converse fails: by the results below, e.g. (ℕ → 𝟚) is totally
separated, but its discreteness amounts to WLPO.

\begin{code}

retract-totally-separated : {X : 𝓤 ̇} {Y : 𝓥 ̇}
                          → retract Y of X → is-totally-separated X → is-totally-separated Y
retract-totally-separated (r , (s , rs)) ts {y} {y'} α = section-lc s (r , rs) h
 where
  h : s y ≡ s y'
  h = ts (λ p → α (p ∘ s))

\end{code}

Recall that a type is called separated if the doubly negated equality
of any two element implies their equality, and that such a type is a
set.

\begin{code}

totally-separated-types-are-separated : (X : 𝓤 ̇ ) → is-totally-separated X → is-separated X
totally-separated-types-are-separated X ts = g
 where
  g : (x y : X) → ¬¬(x ≡ y) → x ≡ y
  g x y φ  = ts h
   where
    a : (p : X → 𝟚) → ¬¬(p x ≡ p y)
    a p = ¬¬-functor (ap p {x} {y}) φ

    h : (p : X → 𝟚) → p x ≡ p y
    h p = 𝟚-is-separated (p x) (p y) (a p)

open import UF-Miscelanea

totally-separated-types-are-sets : funext 𝓤 𝓤₀ → (X : 𝓤 ̇ ) → is-totally-separated X → is-set X
totally-separated-types-are-sets fe X t = separated-types-are-sets fe (totally-separated-types-are-separated X t)

\end{code}

The converse fails: the type of propositions is a set, but its total
separatedness implies excluded middle. In fact, its separatedness
already implies excluded middle (exercise).

The need to define f and g in the following proof arises because the
function is-prop-is-exponential ideal requires a dependent function
with explicit arguments, but total separatedness is defined with
implicit arguments. The essence of the proof is that of p in the where
clause.

\begin{code}

total-separatedness-is-a-prop : funext 𝓤 𝓤 → funext 𝓤 𝓤₀
                              → (X : 𝓤 ̇ ) → is-prop(is-totally-separated X)
total-separatedness-is-a-prop {𝓤} fe fe₀ X = γ
 where
  T : 𝓤 ̇
  T = (x y : X) → x ≡₂ y → x ≡ y
  f : T → is-totally-separated X
  f t {x} {y} φ = t x y φ
  g : is-totally-separated X → T
  g t x y φ = t {x} {y} φ
  p : is-prop T
  p t = Π-is-prop fe
           (λ x → Π-is-prop fe
                    (λ y → Π-is-prop fe
                              (λ p → totally-separated-types-are-sets fe₀ X (f t))))
        t

  γ : is-prop (is-totally-separated X)
  γ = subtype-of-prop-is-a-prop g (λ {t} {u} (q : g t ≡ g u) → ap f q) p
\end{code}

Old proof which by-passes the step via separatedness:

\begin{code}

totally-separated-types-are-sets' : funext 𝓤 𝓤₀ → (X : 𝓤 ̇ ) → is-totally-separated X → is-set X
totally-separated-types-are-sets' fe X t = Id-collapsibles-are-sets h
 where
  f : {x y : X} → x ≡ y → x ≡ y
  f r = t(λ p → ap p r)

  b : {x y : X} (φ γ : (p : X → 𝟚) → p x ≡ p y) → φ ≡ γ
  b φ γ = dfunext fe (λ p → discrete-types-are-sets 𝟚-is-discrete (φ p) (γ p))

  c : {x y : X} (r s : x ≡ y) → (λ p → ap p r) ≡ (λ p → ap p s)
  c r s = b(λ p → ap p r) (λ p → ap p s)

  g : {x y : X} → constant(f {x} {y})
  g r s = ap t (c r s)

  h : Id-collapsible X
  h {x} {y} = f , g

\end{code}

As discussed above, we don't have general closure under Σ, but we have
the following particular cases:

\begin{code}

×-totally-separated : (X : 𝓤 ̇ ) (Y : 𝓥 ̇)
                    → is-totally-separated X
                    → is-totally-separated Y
                    → is-totally-separated (X × Y)
×-totally-separated X Y t u {a , b} {x , y} φ =
   to-×-≡ (t (λ (p : X → 𝟚) → φ (λ (z : X × Y) → p (pr₁ z))))
          (u (λ (q : Y → 𝟚) → φ (λ (z : X × Y) → q (pr₂ z))))

Σ-is-totally-separated : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇)
                       → is-discrete X
                       → ((x : X) → is-totally-separated (Y x))
                       → is-totally-separated (Σ Y)
Σ-is-totally-separated X Y d t {a , b} {x , y} φ = to-Σ-≡ (r , s)
 where
  r : a ≡ x
  r = discrete-totally-separated d (λ p → φ (λ z → p (pr₁ z)))
  s₂ : transport Y r b ≡₂ y
  s₂ q = g
   where
    f : {u : X} → (u ≡ x) + ¬(u ≡ x) → Y u → 𝟚
    f (inl m) v = q (transport Y m v)
    f (inr _) v = ₀ --<-- What we choose here is irrelevant.
    p : Σ Y → 𝟚
    p (u , v) = f (d u x) v
    i : p (a , b) ≡ q (transport Y r b)
    i = ap (λ - → f - b) (discrete-inl d a x r)
    j : p (a , b) ≡ p (x , y)
    j = φ p
    k : p (x , y) ≡ q (transport Y refl y)
    k = ap (λ - → f - y) (discrete-inl d x x refl)
    g : q (transport Y r b) ≡ q y
    g = i ⁻¹ ∙ j ∙ k
  s : transport Y r b ≡ y
  s = t x s₂

\end{code}

Maybe this can be further generalized by replacing the discreteness of X
with the assumption that

  (x : X) (q : Y x → 𝟚) → Σ \(p : Σ Y → 𝟚) → (y : Y x) → q y ≡ p (x , y).

Then the previous few functions would be a particular case of this.


The following can also be considered as a special case of Σ (indexed by the type 𝟚):

\begin{code}

+-totally-separated : (X : 𝓤 ̇ ) (Y : 𝓥 ̇)
                    → is-totally-separated X
                    → is-totally-separated Y
                    → is-totally-separated (X + Y)
+-totally-separated X Y t u {inl x} {inl x'} φ =
    ap inl (t (λ p → φ (cases p (λ (_ : Y) → ₀))))
+-totally-separated X Y t u {inl x} {inr y} φ =
    𝟘-elim (zero-is-not-one (φ (cases (λ _ → ₀) (λ _ → ₁))))
+-totally-separated X Y t u {inr y} {inl x} φ =
    𝟘-elim (zero-is-not-one (φ (cases (λ _ → ₁) (λ _ → ₀))))
+-totally-separated X Y t u {inr y} {inr y'} φ =
    ap inr (u (λ p → φ (cases (λ (_ : X) → ₀) p)))

\end{code}

\begin{code}

𝟚-is-totally-separated : is-totally-separated 𝟚
𝟚-is-totally-separated e = e id

Π-is-totally-separated : funext 𝓤 𝓥 → {X : 𝓤 ̇} {Y : X → 𝓥 ̇}
                   → ((x : X) → is-totally-separated(Y x)) → is-totally-separated(Π Y)
Π-is-totally-separated fe {X} {Y} t {f} {g} e = dfunext fe h
 where
   P : (x : X) (p : Y x → 𝟚) → Π Y → 𝟚
   P x p f = p(f x)

   h : (x : X) → f x ≡ g x
   h x = t x (λ p → e(P x p))

Cantor-is-totally-separated : funext 𝓤₀ 𝓤₀ → is-totally-separated (ℕ → 𝟚)
Cantor-is-totally-separated fe = Π-is-totally-separated fe (λ n → 𝟚-is-totally-separated)

\end{code}

Closure under /-extensions (see the module InjectiveTypes). Notice
that j doesn't need to be an embedding (which which case the extension
is merely a Kan extension rather than a proper extension).

\begin{code}

module _ (fe : FunExt)  where

 open import InjectiveTypes fe

 /-is-totally-separated : {X : 𝓤 ̇} {A : 𝓥 ̇}
                          (j : X → A)
                          (Y : X → 𝓦 ̇ )
                        → ((x : X) → is-totally-separated (Y x))
                        → (a : A) → is-totally-separated ((Y / j) a)
 /-is-totally-separated {𝓤} {𝓥} {𝓦} j Y t a = Π-is-totally-separated (fe (𝓤 ⊔ 𝓥) 𝓦)
                                                 (λ (σ : fiber j a) → t (pr₁ σ))

\end{code}

We now characterize the totally separated types X as those such that
the map eval {X} is an embedding, in order to construct totally
separated reflections.

\begin{code}

eval : {X : 𝓤 ̇} → X → ((X → 𝟚) → 𝟚)
eval x = λ p → p x

tsieeval : {X : 𝓤 ̇} → funext 𝓤 𝓤₀ → is-totally-separated X → is-embedding(eval {𝓤} {X})
tsieeval {𝓤} {X} fe ts φ (x , p) (y , q) = to-Σ-≡ (t , r)
  where
   s : eval x ≡ eval y
   s = p ∙ q ⁻¹

   t : x ≡ y
   t = ts (happly s)

   r : transport (λ - → eval - ≡ φ) t p ≡ q
   r = totally-separated-types-are-sets fe
         ((X → 𝟚) → 𝟚) (Π-is-totally-separated fe (λ p → 𝟚-is-totally-separated)) _ q

ieevalts : {X : 𝓤 ̇} → funext 𝓤 𝓤₀ → is-embedding(eval {𝓤} {X}) → is-totally-separated X
ieevalts {𝓤} {X} fe i {x} {y} e = ap pr₁ q
  where
   φ : (X → 𝟚) → 𝟚
   φ = eval x

   h : is-prop (fiber eval  φ)
   h = i φ

   g : eval y ≡ φ
   g = dfunext fe (λ p → (e p)⁻¹)

   q : x , refl ≡ y , g
   q = h (x , refl) (y , g)

\end{code}

 Now, if a type is not (necessarily) totally separated, we can
 consider the image of the map eval {X}, and this gives the totally
 separated reflection, with the corestriction of eval {X} to its image
 as its reflector.

\begin{code}

module TotallySeparatedReflection
         (fe : FunExt)
         (pt : propositional-truncations-exist)
 where

 open PropositionalTruncation pt
 open ImageAndSurjection pt

\end{code}

We construct the reflection as the image of the evaluation map.

\begin{code}

 𝕋 : 𝓤 ̇ → 𝓤 ̇
 𝕋 {𝓤} X = image (eval {𝓤} {X})

 tts : {X : 𝓤 ̇} → is-totally-separated(𝕋 X)
 tts {𝓤} {X} {φ , s} {γ , t} = g
  where
   f : (e : (q : 𝕋 X → 𝟚) → q (φ , s) ≡ q (γ , t)) (p : X → 𝟚) → φ p ≡ γ p
   f e p = e (λ (x' : 𝕋 X) → pr₁ x' p)

   g : (e : (q : 𝕋 X → 𝟚) → q (φ , s) ≡ q (γ , t)) → (φ , s) ≡ (γ , t)
   g e = to-Σ-≡ (dfunext (fe 𝓤 𝓤₀) (f e), ∥∥-is-a-prop _ t)

\end{code}

Then the reflector is the corestriction of the evaluation map. The
induction principle for surjections gives an induction principle for
the reflector.

\begin{code}


 η : {X : 𝓤 ̇} → X → 𝕋 X
 η {X} = corestriction (eval {X})

 η-surjection : {X : 𝓤 ̇} → is-surjection(η {𝓤} {X})
 η-surjection = corestriction-surjection eval

 η-induction :  {X : 𝓤 ̇} (P : 𝕋 X → 𝓦 ̇ )
             → ((x' : 𝕋 X) → is-prop(P x'))
             → ((x : X) → P(η x))
             → (x' : 𝕋 X) → P x'
 η-induction = surjection-induction η η-surjection

\end{code}

Perhaps we could have used more induction in the following proof
rather than direct proofs (as in the proof of tight reflection below).

\begin{code}

 totally-separated-reflection : {X : 𝓤 ̇} {A : 𝓥 ̇} → is-totally-separated A
                              → (f : X → A) → ∃! \(f' : 𝕋 X → A) → f' ∘ η ≡ f
 totally-separated-reflection {𝓤} {𝓥} {X} {A} ts f = go
  where
   iss : is-set A
   iss = totally-separated-types-are-sets (fe 𝓥 𝓤₀) A ts

   ie : (γ : (A → 𝟚) → 𝟚) → is-prop (Σ \(a : A) → eval a ≡ γ)
   ie = tsieeval (fe 𝓥 𝓤₀) ts

   h : (φ : (X → 𝟚) → 𝟚) → (∃ \(x : X) → eval x ≡ φ) → Σ \(a : A) → eval a ≡ (λ q → φ(q ∘ f))
   h φ = ∥∥-rec (ie γ) u
    where
     γ : (A → 𝟚) → 𝟚
     γ q = φ (q ∘ f)

     u : (Σ \(x : X) → (λ p → p x) ≡ φ) → Σ \(a : A) → eval a ≡ γ
     u (x , r) = f x , dfunext (fe 𝓥 𝓤₀) (λ q → happly r (q ∘ f))

   h' : (x' : 𝕋 X) → Σ \(a : A) → eval a ≡ (λ q → pr₁ x' (q ∘ f))
   h' (φ , s) = h φ s

   f' : 𝕋 X → A
   f' (φ , s) = pr₁ (h φ s)

   b : (x' : 𝕋 X) (q : A → 𝟚) → q(f' x') ≡ pr₁ x' (q ∘ f)
   b (φ , s) = happly (pr₂ (h φ s))

   r : f' ∘ η ≡ f
   r = dfunext (fe 𝓤 𝓥) (λ x → ts (b (η x)))

   c : (σ : Σ \(f'' : 𝕋 X → A) → f'' ∘ η ≡ f) → (f' , r) ≡ σ
   c (f'' , s) = to-Σ-≡ (t , v)
    where
     w : ∀ x → f'(η x) ≡ f''(η x)
     w = happly (r ∙ s ⁻¹)

     t : f' ≡ f''
     t = dfunext (fe 𝓤 𝓥) (η-induction _ (λ _ → iss) w)

     u : f'' ∘ η ≡ f
     u = transport (λ - → - ∘ η ≡ f) t r

     v : u ≡ s
     v = Π-is-set (fe 𝓤 𝓥) (λ _ → iss) u s

   go : ∃! \(f' : 𝕋 X → A) → f' ∘ η ≡ f
   go = (f' , r) , c

\end{code}

We package the above as follows for convenient use elsewhere
(including the module 2CompactTypes).

\begin{code}

 totally-separated-reflection' : {X : 𝓤 ̇} {A : 𝓥 ̇} → is-totally-separated A
                              → is-equiv (λ (f' : 𝕋 X → A) → f' ∘ η)
 totally-separated-reflection' ts = vv-equivs-are-equivs _ (totally-separated-reflection ts)

 totally-separated-reflection'' : {X : 𝓤 ̇} {A : 𝓥 ̇} → is-totally-separated A
                               → (𝕋 X → A) ≃ (X → A)
 totally-separated-reflection'' ts = (λ f' → f' ∘ η) , totally-separated-reflection' ts

\end{code}

In particular, because 𝟚 is totally separated, 𝕋 X and X have the same
boolean predicates (which we exploit in the module 2CompactTypes).

The notion of total separatedness (or 𝟚-separatedness) is analogous to
the T₀-separation axiom (which says that any two points with the same
open neighbourhoods are equal).

\begin{code}

𝟚-sober : 𝓦 ̇ → 𝓤 ⁺ ⊔ 𝓦 ̇
𝟚-sober {𝓦} {𝓤} A = 𝟚-separated A × ((X : 𝓤 ̇ ) (e : A → X) → is-equiv(dual 𝟚 e) → is-equiv e)

\end{code}

TODO: example of 𝟚-separated type that fails to be 𝟚-sober, 𝟚-sober
reflection.

TODO: most of what we said doesn't depend on the type 𝟚, and total
separatedness can be generalized to S-separatedness for an arbitrary
type S, where 𝟚-separatedness is total separatedness. Then, for
example, Prop-separated is equivalent to is-set, all types in U are U
separated, Set-separatedness (where Set is the type of sets) should be
equivalent to is-1-groupoid, etc.

An interesting case is when S is (the total space of) a dominance,
generalizing the case S=Prop. Because the partial elements are defined
in terms of maps into S, the S-lifting of a type X should coincide
with the S-separated reflection of the lifting of X, and hence, in
this context, it makes sense to restrict our attention to S-separated
types.

Another useful thing is that in any type X we can define an apartness
relation x♯y by ∃(p:X→𝟚), p(x)‌≠p(y), which is tight iff X is totally
separated, where tightness means ¬(x♯y)→x=y. Part of the following
should be moved to another module about apartness, but I keep it here
for the moment.

26 January 2018.

\begin{code}

module Apartness (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 is-prop-valued is-irreflexive is-symmetric is-cotransitive is-tight is-apartness
     : {X : 𝓤 ̇} → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇

 is-prop-valued  _♯_ = ∀ x y → is-prop(x ♯ y)
 is-irreflexive  _♯_ = ∀ x → ¬(x ♯ x)
 is-symmetric    _♯_ = ∀ x y → x ♯ y → y ♯ x
 is-cotransitive _♯_ = ∀ x y z → x ♯ y → x ♯ z ∨ y ♯ z
 is-tight        _♯_ = ∀ x y → ¬(x ♯ y) → x ≡ y
 is-apartness    _♯_ = is-prop-valued _♯_ × is-irreflexive _♯_ × is-symmetric _♯_ × is-cotransitive _♯_

\end{code}

We now show that a type is totally separated iff a particular
apartness relation _♯₂ is tight:

\begin{code}

 _♯₂_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
 x ♯₂ y = ∃ \(p : _ → 𝟚) → p x ≢ p y

 ♯₂-is-apartness : {X : 𝓤 ̇} → is-apartness (_♯₂_ {𝓤} {X})
 ♯₂-is-apartness {𝓤} {X} = a , b , c , d
  where
   a : is-prop-valued _♯₂_
   a x y = ∥∥-is-a-prop

   b : is-irreflexive _♯₂_
   b x = ∥∥-rec 𝟘-is-prop g
    where
     g : ¬ Σ \(p : X → 𝟚) → p x ≢ p x
     g (p , u) = u refl

   c : is-symmetric _♯₂_
   c x y = ∥∥-functor g
    where
     g : (Σ \(p : X → 𝟚) → p x ≢ p y) → Σ \(p : X → 𝟚) → p y ≢ p x
     g (p , u) = p , ≢-sym u

   d : is-cotransitive _♯₂_
   d x y z = ∥∥-functor g
    where
     g : (Σ \(p : X → 𝟚) → p x ≢ p y) → (x ♯₂ z) + (y ♯₂ z)
     g (p , u) = h (discrete-is-cotransitive 𝟚-is-discrete {p x} {p y} {p z} u)
      where
       h : (p x ≢ p z) + (p z ≢ p y) → (x ♯₂ z) + (y ♯₂ z)
       h (inl u) = inl ∣ p , u ∣
       h (inr v) = inr ∣ p , ≢-sym v ∣

 ♯₂-is-tight-ts : {X : 𝓤 ̇} → is-tight (_♯₂_ {𝓤} {X}) → is-totally-separated X
 ♯₂-is-tight-ts {𝓤} {X} t {x} {y} α = t x y (∥∥-rec 𝟘-is-prop h)
  where
   h : ¬ Σ \(p : X → 𝟚) → p x ≢ p y
   h (p , u) = u (α p)

 ts-♯₂-is-tight : {X : 𝓤 ̇} → is-totally-separated X → is-tight (_♯₂_ {𝓤} {X})
 ts-♯₂-is-tight {𝓤} {X} ts x y na = ts α
  where
   h : ¬ Σ \(p : X → 𝟚) → p x ≢ p y
   h (p , u) = na ∣ p , u ∣

   α : (p : X → 𝟚) → p x ≡ p y
   α p = 𝟚-is-separated (p x) (p y) (λ u → h (p , u))

\end{code}

 12 Feb 2018. This was prompted by the discussion
 https://nforum.ncatlab.org/discussion/8282/points-of-the-localic-quotient-with-respect-to-an-apartness-relation/

 But is clearly related to the above characterization of total
 separatedness.

\begin{code}

 is-reflexive is-transitive is-equivalence-rel
     : {X : 𝓤 ̇} → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇

 is-reflexive       _≈_ = ∀ x → x ≈ x
 is-transitive      _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z
 is-equivalence-rel _≈_ = is-prop-valued _≈_ × is-reflexive _≈_ × is-symmetric _≈_ × is-transitive _≈_

\end{code}

 The following is the standard equivalence relation induced by an
 apartness relation. The tightness axiom defined above says that this
 equivalence relation is equality.

\begin{code}

 neg-apart-is-equiv : {X : 𝓤 ̇} → funext 𝓤 𝓤₀
                    → (_♯_ : X → X → 𝓤 ̇ ) → is-apartness _♯_ → is-equivalence-rel (λ x y → ¬(x ♯ y))
 neg-apart-is-equiv {𝓤} {X} fe _♯_ (♯p , ♯i , ♯s , ♯c) = p , ♯i , s , t
  where
   p : (x y : X) → is-prop (¬ (x ♯ y))
   p x y = negations-are-props fe

   s : (x y : X) → ¬ (x ♯ y) → ¬ (y ♯ x)
   s x y u a = u (♯s y x a)

   t : (x y z : X) → ¬ (x ♯ y) → ¬ (y ♯ z) → ¬ (x ♯ z)
   t x y z u v a = v (♯s z y (left-fails-then-right-holds (♯p z y) b u))
    where
     b : (x ♯ y) ∨ (z ♯ y)
     b = ♯c x z y a

 \end{code}

 The following positive formulation of ¬(x ♯ y), which says that two
 elements have the same elements apart from them iff they are not
 apart, gives another way to see that it is an equivalence relation:

 \begin{code}

 not-apart-have-same-apart : {X : 𝓤 ̇} (x y : X) (_♯_ : X → X → 𝓥 ̇ ) → is-apartness _♯_
                          → ¬(x ♯ y) → ((z : X) → x ♯ z ⇔ y ♯ z)
 not-apart-have-same-apart {𝓤} {𝓥} {X} x y _♯_ (p , i , s , c) = g
  where
   g : ¬ (x ♯ y) → (z : X) → x ♯ z ⇔ y ♯ z
   g n z = g₁ , g₂
    where
     g₁ : x ♯ z → y ♯ z
     g₁ a = s z y (left-fails-then-right-holds (p z y) b n)
      where
       b : (x ♯ y) ∨ (z ♯ y)
       b = c x z y a

     n' : ¬(y ♯ x)
     n' a = n (s y x a)

     g₂ : y ♯ z → x ♯ z
     g₂ a = s z x (left-fails-then-right-holds (p z x) b n')
      where
       b : (y ♯ x) ∨ (z ♯ x)
       b = c y z x a

 have-same-apart-are-not-apart : {X : 𝓤 ̇} (x y : X) (_♯_ : X → X → 𝓥 ̇ ) → is-apartness _♯_
                               → ((z : X) → x ♯ z ⇔ y ♯ z) → ¬(x ♯ y)
 have-same-apart-are-not-apart {𝓤} {𝓥} {X} x y _♯_ (p , i , s , c) = f
  where
   f : ((z : X) → x ♯ z ⇔ y ♯ z) → ¬ (x ♯ y)
   f φ a = i y (pr₁(φ y) a)

\end{code}

 Not-not equal elements are not apart, and hence, in the presence of
 tightness, they are equal. It follows that tight apartness types are
 sets.

\begin{code}

 not-not-equal-not-apart : {X : 𝓤 ̇} (x y : X) (_♯_ : X → X → 𝓥 ̇ )
                         → is-apartness _♯_ → ¬¬(x ≡ y) → ¬(x ♯ y)
 not-not-equal-not-apart x y _♯_ (_ , i , _ , _) = contrapositive f
  where
   f : x ♯ y → ¬(x ≡ y)
   f a p = i y (transport (λ - → - ♯ y) p a)

 tight-is-separated : {X : 𝓤 ̇} → (_♯_ : X → X → 𝓥 ̇ )
                 → is-apartness _♯_ → is-tight _♯_ → is-separated X
 tight-is-separated _♯_ a t = f
  where
   f : ∀ x y → ¬¬(x ≡ y) → x ≡ y
   f x y φ = t x y (not-not-equal-not-apart x y _♯_ a φ)

 tight-is-set : {X : 𝓤 ̇} → funext 𝓤 𝓤₀
           → (_♯_ : X → X → 𝓥 ̇ ) → is-apartness _♯_ → is-tight _♯_ → is-set X
 tight-is-set fe _♯_ a t = separated-types-are-sets fe (tight-is-separated _♯_ a t)

\end{code}

 The above use the apartness and tightness data, but their existence is
 enough, because being a separated type and being a set are
 propositions.

\begin{code}

 tight-separated' : {X : 𝓤 ̇} → funext 𝓤 𝓤 → funext 𝓤 𝓤₀
                 → (∃ \(_♯_ : X → X → 𝓤 ̇ ) → is-apartness _♯_ × is-tight _♯_) → is-separated X
 tight-separated' {𝓤} {X} fe fe₀ = ∥∥-rec (is-prop-separated fe fe₀) f
   where
    f : (Σ \(_♯_ : X → X → 𝓤 ̇ ) → is-apartness _♯_ × is-tight _♯_) → is-separated X
    f (_♯_ , a , t) = tight-is-separated _♯_ a t

 tight-is-set' : {X : 𝓤 ̇} → funext 𝓤 𝓤 → funext 𝓤 𝓤₀
           → (∃ \(_♯_ : X → X → 𝓤 ̇ ) → is-apartness _♯_ × is-tight _♯_) → is-set X
 tight-is-set' {𝓤} {X} fe fe₀ = ∥∥-rec (being-set-is-a-prop fe) f
   where
    f : (Σ \(_♯_ : X → X → 𝓤 ̇ ) → is-apartness _♯_ × is-tight _♯_) → is-set X
    f (_♯_ , a , t) = tight-is-set fe₀ _♯_ a t

\end{code}

 A map is called strongly extensional if it reflects apartness.

\begin{code}

 strongly-extensional : ∀ {𝓣} {X : 𝓤 ̇} {Y : 𝓥 ̇}
                      → (X → X → 𝓦 ̇ ) → (Y → Y → 𝓣 ̇) → (X → Y) → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
 strongly-extensional _♯_ _♯'_ f = ∀ {x x'} → f x ♯' f x' → x ♯ x'

 preserves : ∀ {𝓣} {X : 𝓤 ̇} {Y : 𝓥 ̇}
          → (X → X → 𝓦 ̇ ) → (Y → Y → 𝓣 ̇) → (X → Y) → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
 preserves R S f = ∀ {x x'} → R x x' → S (f x) (f x')

 module TightReflection
          (fe : FunExt)
          (pe : propext 𝓥)
          (X : 𝓤 ̇ )
          (_♯_ : X → X → 𝓥 ̇ )
          (♯p : is-prop-valued _♯_)
          (♯i : is-irreflexive _♯_)
          (♯s : is-symmetric _♯_)
          (♯c : is-cotransitive _♯_)
   where

\end{code}

  We now name the standard is-equivalence relation induced by _♯_.

\begin{code}

  _~_ : X → X → 𝓥 ̇
  x ~ y = ¬(x ♯ y)

\end{code}

  For certain purposes we need the apartness axioms packed in to a
  single axiom.

\begin{code}

  ♯a : is-apartness _♯_
  ♯a = (♯p , ♯i , ♯s , ♯c)

\end{code}

  Initially we tried to work with the function apart : X → (X → 𝓥 ̇ )
  defined by apart = _♯_. However, at some point in the development
  below it was difficult to proceed, when we need that the identity
  type apart x = apart y is a proposition. This should be the case
  because _♯_ is is-prop-valued. The most convenient way to achieve this
  is to restrict the codomain of apart from V to Ω, so that the
  codomain of apart is a set.

\begin{code}

  apart : X → (X → Ω 𝓥)
  apart x y = x ♯ y , ♯p x y

\end{code}

  The following is an immediate consequence of the fact that two
  equivalent elements have the same apartness class, using functional
  and propositional extensionality.

\begin{code}

  apart-lemma : (x y : X) → x ~ y → apart x ≡ apart y
  apart-lemma x y na = dfunext (fe 𝓤 (𝓥 ⁺)) h
   where
    f : (z : X) → x ♯ z ⇔ y ♯ z
    f = not-apart-have-same-apart x y _♯_ ♯a na

    g : (z : X) → x ♯ z ≡ y ♯ z
    g z = pe (♯p x z) (♯p y z) (pr₁ (f z)) (pr₂ (f z))

    h : (z : X) → apart x z ≡ apart y z
    h z = to-Σ-≡ (g z , being-a-prop-is-a-prop (fe 𝓥 𝓥) _ _)

\end{code}

  We now construct the tight reflection of (X,♯) to get (X',♯')
  together with a universal strongly extensional map from X into
  tight apartness types. We take X' to be the image of the apart map.

\begin{code}

  open ImageAndSurjection pt

  X' : 𝓤 ⊔ 𝓥 ⁺ ̇
  X' = image apart

\end{code}

The type X may or may not be a set, but its tight reflection is
necessarily a set, and we can see this before we define a tight
apartness on it.

\begin{code}

  X'-is-set : is-set X'
  X'-is-set = subsets-of-sets-are-sets (X → Ω 𝓥) _ (powersets-are-sets (fe 𝓤 (𝓥 ⁺)) (fe 𝓥 𝓥) pe) ∥∥-is-a-prop

  η : X → X'
  η = corestriction apart

\end{code}

  The following induction principle is our main tool. Its uses look
  convoluted at times by the need to show that the property one is
  doing induction over is is-prop-valued. Typically this involves the use
  of the fact the propositions form an exponential ideal, and, more
  generally, are closed under products.

\begin{code}

  η-surjection : is-surjection η
  η-surjection = corestriction-surjection apart

  η-induction : (P : X' → 𝓦 ̇ )
             → ((x' : X') → is-prop(P x'))
             → ((x : X) → P(η x))
             → (x' : X') → P x'
  η-induction = surjection-induction η η-surjection

\end{code}

  The apartness relation _♯'_ on X' is defined as follows.

\begin{code}

  _♯'_ : X' → X' → 𝓤 ⊔ 𝓥 ⁺ ̇
  (u , _) ♯' (v , _) = ∃ \(x : X) → Σ \(y : X) → (x ♯ y) × (apart x ≡ u) × (apart y ≡ v)

\end{code}

  Then η preserves and reflects apartness.

\begin{code}

  η-preserves-apartness : preserves _♯_ _♯'_ η
  η-preserves-apartness {x} {y} a = ∣ x , y , a , refl , refl ∣

  η-strongly-extensional : strongly-extensional _♯_ _♯'_ η
  η-strongly-extensional {x} {y} = ∥∥-rec (♯p x y) g
   where
    g : (Σ \(x' : X) → Σ \(y' : X) → (x' ♯ y') × (apart x' ≡ apart x) × (apart y' ≡ apart y))
      → x ♯ y
    g (x' , y' , a , p , q) = ♯s _ _ (j (♯s _ _ (i a)))
     where
      i : x' ♯ y' → x ♯ y'
      i = idtofun _ _ (ap pr₁ (happly p y'))

      j : y' ♯ x → y ♯ x
      j = idtofun _ _ (ap pr₁ (happly q x))

\end{code}

  Of course, we must check that _♯'_ is indeed an apartness
  relation. We do this by η-induction. These proofs by induction need
  routine proofs that some things are propositions. We include the
  following abbreviation `fuv` to avoid some long lines in such
  proofs.

\begin{code}

  fuv : funext (𝓤 ⊔ 𝓥 ⁺) (𝓤 ⊔ 𝓥 ⁺)
  fuv = fe (𝓤 ⊔ 𝓥 ⁺) (𝓤 ⊔ 𝓥 ⁺)

  ♯'p : is-prop-valued _♯'_
  ♯'p _ _ = ∥∥-is-a-prop

  ♯'i : is-irreflexive _♯'_
  ♯'i = by-induction
   where
    induction-step : ∀ x → ¬(η x ♯' η x)
    induction-step x a = ♯i x (η-strongly-extensional a)

    by-induction : _
    by-induction = η-induction (λ x' → ¬ (x' ♯' x'))
                      (λ _ → Π-is-prop (fe (𝓤 ⊔ 𝓥 ⁺) 𝓤₀) (λ _ → 𝟘-is-prop))
                      induction-step

  ♯'s : is-symmetric _♯'_
  ♯'s = by-nested-induction
   where
    induction-step : ∀ x y → η x ♯' η y → η y ♯' η x
    induction-step x y a = η-preserves-apartness(♯s x y (η-strongly-extensional a))

    by-nested-induction : _
    by-nested-induction =
      η-induction (λ x' → ∀ y' → x' ♯' y' → y' ♯' x')
       (λ x' → Π-is-prop fuv
                (λ y' → Π-is-prop fuv (λ _ → ♯'p y' x')))
       (λ x → η-induction (λ y' → η x ♯' y' → y' ♯' η x)
                (λ y' → Π-is-prop fuv (λ _ → ♯'p y' (η x)))
                (induction-step x))

  ♯'c : is-cotransitive _♯'_
  ♯'c = by-nested-induction
   where
    induction-step : ∀ x y z → η x ♯' η y → η x ♯' η z ∨ η y ♯' η z
    induction-step x y z a = ∥∥-functor c b
     where
      a' : x ♯ y
      a' = η-strongly-extensional a

      b : x ♯ z ∨ y ♯ z
      b = ♯c x y z a'

      c : (x ♯ z) + (y ♯ z) → (η x ♯' η z) + (η y ♯' η z)
      c (inl e) = inl (η-preserves-apartness e)
      c (inr f) = inr (η-preserves-apartness f)

    by-nested-induction : _
    by-nested-induction =
      η-induction (λ x' → ∀ y' z' → x' ♯' y' → (x' ♯' z') ∨ (y' ♯' z'))
       (λ _ → Π-is-prop fuv
                (λ _ → Π-is-prop fuv
                         (λ _ → Π-is-prop fuv (λ _ → ∥∥-is-a-prop))))
       (λ x → η-induction (λ y' → ∀ z' → η x ♯' y' → (η x ♯' z') ∨ (y' ♯' z'))
                (λ _ → Π-is-prop fuv
                         (λ _ → Π-is-prop fuv (λ _ → ∥∥-is-a-prop)))
                (λ y → η-induction (λ z' → η x ♯' η y → (η x ♯' z') ∨ (η y ♯' z'))
                         (λ _ → Π-is-prop fuv (λ _ → ∥∥-is-a-prop))
                         (induction-step x y)))

  ♯'a : is-apartness _♯'_
  ♯'a = (♯'p , ♯'i , ♯'s , ♯'c)

\end{code}

  The tightness of _♯'_ cannot by proved by induction by reduction to
  properties of _♯_, as above, because _♯_ is not (necessarily)
  tight. We need to work with the definitions of X' and _♯'_ directly.

\begin{code}

  ♯'t : is-tight _♯'_
  ♯'t (u , e) (v , f) n = ∥∥-rec X'-is-set (λ σ → ∥∥-rec X'-is-set (h σ) f) e
   where
    h : (Σ \(x : X) → apart x ≡ u) → (Σ \(y : X) → apart y ≡ v) → (u , e) ≡ (v , f)
    h (x , p) (y , q) = to-Σ-≡ (t , ∥∥-is-a-prop _ _)
     where
      remark : (∃ \(x : X) → Σ \(y : X) → (x ♯ y) × (apart x ≡ u) × (apart y ≡ v)) → 𝟘
      remark = n

      r : x ♯ y → 𝟘
      r a = n ∣ x , y , a , p , q ∣

      s : apart x ≡ apart y
      s = apart-lemma x y r

      t : u ≡ v
      t = p ⁻¹ ∙ s ∙ q

\end{code}

  The tightness of _♯'_ gives that η maps equivalent elements to equal
  elements, and its irreflexity gives that elements with the same η
  image are equivalent.

\begin{code}

  η-equiv-equal : {x y : X} → x ~ y → η x ≡ η y
  η-equiv-equal = ♯'t _ _ ∘ contrapositive η-strongly-extensional

  η-equal-equiv : {x y : X} → η x ≡ η y → x ~ y
  η-equal-equiv {x} {y} p a = ♯'i (η y) (transport (λ - → - ♯' η y) p (η-preserves-apartness a))

\end{code}

  We now show that the above data provide the tight reflection, or
  universal strongly extensional map from X to tight apartness types,
  where unique existence is expressed by by saying that a Σ type is a
  singleton, as usual in univalent mathematics and homotopy type
  theory. Notice the use of η-induction to avoid dealing directly with
  the details of the constructions performed above.

\begin{code}

  tight-reflection : ∀ {𝓣} (A : 𝓦 ̇ ) (_♯ᴬ_ : A → A → 𝓣 ̇)
                   → is-apartness _♯ᴬ_
                   → is-tight _♯ᴬ_
                   → (f : X → A)
                   → strongly-extensional _♯_ _♯ᴬ_ f
                   → ∃! \(f' : X' → A) → f' ∘ η ≡ f
  tight-reflection {𝓦} {𝓣} A  _♯ᴬ_  ♯ᴬa  ♯ᴬt  f  se = ic
   where
    iss : is-set A
    iss = tight-is-set (fe 𝓦 𝓤₀) _♯ᴬ_ ♯ᴬa ♯ᴬt

    i : {x y : X} → x ~ y → f x ≡ f y
    i = ♯ᴬt _ _ ∘ contrapositive se

    φ : (x' : X') → is-prop (Σ \a → ∃ \x → (η x ≡ x') × (f x ≡ a))
    φ = η-induction _ γ induction-step
      where
       induction-step : (y : X) → is-prop (Σ \a → ∃ \x → (η x ≡ η y) × (f x ≡ a))
       induction-step x (a , d) (b , e) = to-Σ-≡ (p , ∥∥-is-a-prop _ _)
        where
         h : (Σ \x' → (η x' ≡ η x) × (f x' ≡ a))
           → (Σ \y' → (η y' ≡ η x) × (f y' ≡ b))
           → a ≡ b
         h (x' , r , s) (y' , t , u) = s ⁻¹ ∙ i (η-equal-equiv (r ∙ t ⁻¹)) ∙ u

         p : a ≡ b
         p = ∥∥-rec iss (λ σ → ∥∥-rec iss (h σ) e) d

       γ : (x' : X') → is-prop (is-prop (Σ \a → ∃ \x → (η x ≡ x') × (f x ≡ a)))
       γ x' = being-a-prop-is-a-prop (fe (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦) (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦))

    k : (x' : X') → Σ \(a : A) → ∃ \(x : X) → (η x ≡ x') × (f x ≡ a)
    k = η-induction _ φ induction-step
     where
      induction-step : (y : X) → Σ \a → ∃ \x → (η x ≡ η y) × (f x ≡ a)
      induction-step x = f x , ∣ x , refl , refl ∣

    f' : X' → A
    f' x' = pr₁(k x')

    r : f' ∘ η ≡ f
    r = dfunext (fe 𝓤 𝓦) h
     where
      g : (y : X) → ∃ \x → (η x ≡ η y) × (f x ≡ f' (η y))
      g y = pr₂(k(η y))

      j : (y : X) → (Σ \x → (η x ≡ η y) × (f x ≡ f' (η y))) → f'(η y) ≡ f y
      j y (x , p , q) = q ⁻¹ ∙ i (η-equal-equiv p)

      h : (y : X) → f'(η y) ≡ f y
      h y = ∥∥-rec iss (j y) (g y)

    c : (σ : Σ \(f'' : X' → A) → f'' ∘ η ≡ f) → (f' , r) ≡ σ
    c (f'' , s) = to-Σ-≡ (t , v)
     where
      w : ∀ x → f'(η x) ≡ f''(η x)
      w = happly (r ∙ s ⁻¹)

      t : f' ≡ f''
      t = dfunext (fe (𝓤 ⊔ 𝓥 ⁺) 𝓦) (η-induction _ (λ _ → iss) w)

      u : f'' ∘ η ≡ f
      u = transport (λ - → - ∘ η ≡ f) t r

      v : u ≡ s
      v = Π-is-set (fe 𝓤 𝓦) (λ _ → iss) u s

    ic : ∃! \(f' : X' → A) → f' ∘ η ≡ f
    ic = (f' , r) , c

\end{code}

  The following is an immediate consequence of the tight reflection,
  by the usual categorical argument, using the fact that the identity
  map is strongly extensional (with the identity function as the
  proof). Notice that our construction of the reflection produces a
  result in a universe higher than those where the starting data are,
  to avoid impredicativity (aka propositional resizing). Nevertheless,
  the usual categorical argument is applicable.

  A direct proof that doesn't rely on the tight reflection is equally
  short in this case, and is also included.

  What the following construction says is that if _♯_ is tight, then
  any element of X is uniquely determined by the set of elements apart
  from it.

\begin{code}

  tight-η-equiv-abstract-nonsense : is-tight _♯_ → X ≃ X'
  tight-η-equiv-abstract-nonsense ♯t = η , (θ , happly p₄) , (θ , happly p₀)
   where
    u : ∃! \(θ : X' → X) → θ ∘ η ≡ id
    u = tight-reflection X _♯_ ♯a ♯t id id

    v : ∃! \(ζ : X' → X') → ζ ∘ η ≡ η
    v = tight-reflection X' _♯'_ ♯'a ♯'t η η-strongly-extensional

    θ : X' → X
    θ = pr₁(pr₁ u)

    ζ : X' → X'
    ζ = pr₁(pr₁ v)

    φ : (ζ' : X' → X') → ζ' ∘ η ≡ η → ζ ≡ ζ'
    φ ζ' p = ap pr₁ (pr₂ v (ζ' , p))

    p₀ : θ ∘ η ≡ id
    p₀ = pr₂(pr₁ u)

    p₁ : η ∘ θ ∘ η ≡ η
    p₁ = ap (_∘_ η) p₀

    p₂ : ζ ≡ η ∘ θ
    p₂ = φ (η ∘ θ) p₁

    p₃ : ζ ≡ id
    p₃ = φ id refl

    p₄ : η ∘ θ ≡ id
    p₄ = p₂ ⁻¹ ∙ p₃

  tight-η-equiv-direct : is-tight _♯_ → X ≃ X'
  tight-η-equiv-direct t = (η , vv-equivs-are-equivs η cm)
   where
    lc : left-cancellable η
    lc {x} {y} p = i h
     where
      i : ¬ (η x ♯' η y) → x ≡ y
      i = t x y ∘ contrapositive (η-preserves-apartness {x} {y})

      h : ¬(η x ♯' η y)
      h a = ♯'i (η y) (transport (λ - → - ♯' η y) p a)

    e : is-embedding η
    e =  lc-maps-into-sets-are-embeddings η lc X'-is-set

    cm : is-vv-equiv η
    cm = pr₂ (c-es η) (e , η-surjection)

\end{code}

TODO.

* The tight reflection has the universal property of the quotient by
  _~_. Conversely, the quotient by _~_ gives the tight reflection.

* The tight reflection of ♯₂ has the universal property of the totally
  separated reflection.
