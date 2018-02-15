Martin Escardo 2011, 2017, 2018.

We define and study totally separated types. Most of the material in
this file is from January 2018.

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

Closure under Σ fails in general. However, ℕ∞ (defined with Σ) is
totally separated (proved in the module GenericConvergentSequence).

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

open import UF
open import Two
open import DiscreteAndSeparated hiding (tight)

totally-separated : ∀ {U} → U ̇ → U ̇
totally-separated X = {x y : X} → ((p : X → 𝟚) → p x ≡ p y) → x ≡ y

\end{code}

Excluded middle implies that all sets are discrete and hence totally
separated:

\begin{code}

discrete-totally-separated : ∀ {U} {X : U ̇} → discrete X → totally-separated X
discrete-totally-separated {U} {X} d {x} {y} α = g
 where
  open import DecidableAndDetachable
  p : X → 𝟚
  p = pr₁ (characteristic-function (d x))
  
  φ : (y : X) → (p y ≡ ₀ → x ≡ y) × (p y ≡ ₁ → ¬ (x ≡ y))
  φ = pr₂ (characteristic-function (d x))
  
  b : p x ≡ ₀
  b = Lemma[b≢₁→b≡₀] (λ s → pr₂ (φ x) s refl)
  
  a : p y ≡ ₀
  a = (α p)⁻¹ ∙ b
  
  g : x ≡ y
  g = pr₁ (φ y) a

\end{code}

The converse fails: by the results below, e.g. (ℕ → 𝟚) is totally
separated, but its discreteness amounts to WLPO.

\begin{code}

retract-totally-separated : ∀ {U V} {X : U ̇} {Y : V ̇}
                         → retract Y of X → totally-separated X → totally-separated Y
retract-totally-separated (r , (s , rs)) ts {y} {y'} α = section-lc s (r , rs) h
 where
  h : s y ≡ s y'
  h = ts (λ p → α (p ∘ s))

\end{code}

Recall that a type is called separated if the doubly negated equality
of any two element implies their equality, and that such a type is a
set.

\begin{code}

totally-separated-is-separated : ∀ {U} (X : U ̇) → totally-separated X → separated X
totally-separated-is-separated X ts = g
 where
  g : (x y : X) → ¬¬(x ≡ y) → x ≡ y
  g x y φ  = ts h
   where
    a : (p : X → 𝟚) → ¬¬(p x ≡ p y)
    a p = ¬¬-functor (ap p {x} {y}) φ
    
    h : (p : X → 𝟚) → p x ≡ p y
    h p = 𝟚-separated (p x) (p y) (a p)

open import UF2

totally-separated-is-set : ∀ {U} → FunExt U U₀ → (X : U ̇) → totally-separated X → isSet X
totally-separated-is-set fe X t = separated-is-set fe (totally-separated-is-separated X t)

\end{code}

The converse fails: the type of propositions is a set, but its total
separatedness implies excluded middle. In fact, its separatedness
already implies excluded middle (exercise).

Old proof which by-passes the step via separatedness:

\begin{code}

totally-separated-is-set' : ∀ {U} → FunExt U U₀ → (X : U ̇) → totally-separated X → isSet X
totally-separated-is-set' fe X t = path-collapsible-is-set h
 where
  f : {x y : X} → x ≡ y → x ≡ y
  f r = t(λ p → ap p r)
  
  b : {x y : X} (φ γ : (p : X → 𝟚) → p x ≡ p y) → φ ≡ γ
  b φ γ = funext fe (λ p → discrete-is-set 𝟚-discrete (φ p) (γ p))
  
  c : {x y : X} (r s : x ≡ y) → (λ p → ap p r) ≡ (λ p → ap p s)
  c r s = b(λ p → ap p r) (λ p → ap p s)
  
  g : {x y : X} → constant(f {x} {y})
  g r s = ap t (c r s)
  
  h : path-collapsible X
  h {x} {y} = f , g

\end{code}

We now characterize the totally separated types X as those such that
the map eval {X} is an embedding, in order to construct totally
separated reflections.

\begin{code}

𝟚-totally-separated : totally-separated 𝟚
𝟚-totally-separated e = e id

totally-separated-ideal : ∀ {U V} → FunExt U V → {X : U ̇} {Y : X → V ̇}
                       → ((x : X) → totally-separated(Y x)) → totally-separated(Π Y)
totally-separated-ideal fe {X} {Y} t {f} {g} e = funext fe h
 where
   P : (x : X) (p : Y x → 𝟚) → Π Y → 𝟚
   P x p f = p(f x)
   
   h : (x : X) → f x ≡ g x
   h x = t x (λ p → e(P x p))

eval : ∀ {U} {X : U ̇} → X → ((X → 𝟚) → 𝟚)
eval x = λ p → p x

tsieeval : ∀ {U} {X : U ̇} → FunExt U U₀ → totally-separated X → isEmbedding(eval {U} {X})
tsieeval {U} {X} fe ts φ (x , p) (y , q) = to-Σ-Id _ (t , r)
  where
   s : eval x ≡ eval y
   s = p ∙ q ⁻¹
   
   t : x ≡ y
   t = ts (λ p → ap (λ φ → φ p) s)
   
   r : transport (λ x → eval x ≡ φ) t p ≡ q
   r = totally-separated-is-set fe
         ((X → 𝟚) → 𝟚) (totally-separated-ideal fe (λ p → 𝟚-totally-separated)) _ q

ieevalts : ∀ {U} {X : U ̇} → FunExt U U₀ → isEmbedding(eval {U} {X}) → totally-separated X
ieevalts {U} {X} fe i {x} {y} e = ap pr₁ q
  where
   φ : (X → 𝟚) → 𝟚
   φ = eval x
   
   h : isProp (fiber eval  φ)
   h = i φ
   
   g : eval y ≡ φ
   g = funext fe (λ p → (e p)⁻¹)
   
   q : x , refl ≡ y , g
   q = h (x , refl) (y , g)

\end{code}

 Now, if a type is not (necessarily) totally separated, we can
 consider the image of the map eval {X}, and this gives the totally
 separated reflection, with the corestriction of eval {X} to its image
 as its reflector.

\begin{code}

module TotallySeparatedReflection
         {U  : Universe}
         (fe : ∀ U V → FunExt U V)
         (pt : PropTrunc)
 where

 open PropositionalTruncation pt
 open ImageAndSurjection pt

\end{code}

We construct the reflection as the image of the evaluation map.

\begin{code}

 T : U ̇ → U ̇
 T X = image (eval {U} {X})
 
 tts : {X : U ̇} → totally-separated(T X)
 tts {X} {φ , s} {γ , t} = g
  where
   f : (e : (q : T X → 𝟚) → q (φ , s) ≡ q (γ , t)) (p : X → 𝟚) → φ p ≡ γ p
   f e p = e (λ (x' : T X) → pr₁ x' p)

   g : (e : (q : T X → 𝟚) → q (φ , s) ≡ q (γ , t)) → (φ , s) ≡ (γ , t)
   g e = to-Σ-Id _ (funext (fe U U₀) (f e), ptisp _ t)

\end{code}

Then the reflector is the corestriction of the evaluation map. The
induction principle for surjections gives an induction principle for
the reflector.

\begin{code}


 η : {X : U ̇} → X → T X
 η {X} = corestriction (eval {U} {X})

 η-surjection : {X : U ̇} → isSurjection(η {X})
 η-surjection = corestriction-surjection eval

 η-induction : ∀ {W} {X : U ̇} (P : T X → W ̇)
             → ((x' : T X) → isProp(P x'))
             → ((x : X) → P(η x))
             → (x' : T X) → P x'
 η-induction = surjection-induction η η-surjection

\end{code}

Perhaps we could have used more induction in the following proof
rather than direct proofs (as in the proof of tight reflection below).

\begin{code}

 totally-separated-reflection : ∀ {V} {X : U ̇} {A : V ̇} → totally-separated A 
                              → (f : X → A) → isContr (Σ \(f' : T X → A) → f' ∘ η ≡ f)
 totally-separated-reflection {V} {X} {A} ts f = go
  where
   iss : isSet A
   iss = totally-separated-is-set (fe V U₀) A ts
   
   ie : (γ : (A → 𝟚) → 𝟚) → isProp (Σ \(a : A) → eval a ≡ γ)
   ie = tsieeval (fe V U₀) ts
   
   h : (φ : (X → 𝟚) → 𝟚) → (∃ \(x : X) → eval x ≡ φ) → Σ \(a : A) → eval a ≡ (λ q → φ(q ∘ f))
   h φ = ptrec (ie γ) u
    where
     γ : (A → 𝟚) → 𝟚
     γ q = φ (q ∘ f)
     
     u : (Σ \(x : X) → (λ p → p x) ≡ φ) → Σ \(a : A) → eval a ≡ γ
     u (x , r) = f x , funext (fe V U₀) (λ q → ap (λ φ → φ (q ∘ f)) r)
     
   h' : (x' : T X) → Σ \(a : A) → eval a ≡ (λ q → pr₁ x' (q ∘ f))
   h' (φ , s) = h φ s
   
   f' : T X → A
   f' (φ , s) = pr₁ (h φ s)
   
   b : (x' : T X) (q : A → 𝟚) → q(f' x') ≡ pr₁ x' (q ∘ f)
   b (φ , s) q = ap (λ γ → γ q) (pr₂ (h φ s))
   
   r : f' ∘ η ≡ f
   r = funext (fe U V) (λ x → ts (b (η x)))
   
   c : (σ : Σ \(f'' : T X → A) → f'' ∘ η ≡ f) → (f' , r) ≡ σ
   c (f'' , s) = to-Σ-Id _ (t , v)
    where
     w : ∀ x → f'(η x) ≡ f''(η x)
     w x = ap (λ f → f x) (r ∙ s ⁻¹)
     
     t : f' ≡ f''
     t = funext (fe U V) (η-induction _ (λ _ → iss) w)
     
     u : f'' ∘ η ≡ f
     u = transport (λ g → g ∘ η ≡ f) t r
     
     v : u ≡ s
     v = isSet-exponential-ideal (fe U V) (λ _ → iss) u s

   go : isContr (Σ \(f' : T X → A) → f' ∘ η ≡ f)
   go = (f' , r) , c

\end{code}

We package the above as follows for convenient use elsewhere
(including the module 2CompactTypes).

\begin{code}

 totally-separated-reflection' : ∀ {V} {X : U ̇} {A : V ̇} → totally-separated A 
                              → is-equiv (λ (f' : T X → A) → f' ∘ η)
 totally-separated-reflection' ts = isContrMap-is-equiv _ (totally-separated-reflection ts)

 totally-separated-reflection'' : ∀ {V} {X : U ̇} {A : V ̇} → totally-separated A 
                               → (T X → A) ≃ (X → A)
 totally-separated-reflection'' ts = (λ f' → f' ∘ η) , totally-separated-reflection' ts

\end{code}

In particular, because 𝟚 is totally separated, T X and X have the same
boolean predicates (which we exploit in the module 2CompactTypes).


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

module Apartness (pt : PropTrunc) where

 open PropositionalTruncation (pt)

 prop-valued irreflexive symmetric cotransitive tight apartness
     : ∀ {U V} {X : U ̇} → (X → X → V ̇) → U ⊔ V ̇
 
 prop-valued  _♯_ = ∀ x y → isProp(x ♯ y)
 irreflexive  _♯_ = ∀ x → ¬(x ♯ x)
 symmetric    _♯_ = ∀ x y → x ♯ y → y ♯ x
 cotransitive _♯_ = ∀ x y z → x ♯ y → x ♯ z ∨ y ♯ z
 tight        _♯_ = ∀ x y → ¬(x ♯ y) → x ≡ y
 apartness    _♯_ = prop-valued _♯_ × irreflexive _♯_ × symmetric _♯_ × cotransitive _♯_

\end{code}

We now show that a type is totally separated iff a particular
apartness relation _♯₂ is tight:

\begin{code}

 _♯₂_ : ∀ {U} {X : U ̇} → X → X → U ̇
 x ♯₂ y = ∃ \(p : _ → 𝟚) → p x ≢ p y

 ♯₂-is-apartness : ∀ {U} {X : U ̇} → apartness (_♯₂_ {U} {X})
 ♯₂-is-apartness {U} {X} = a , b , c , d
  where
   a : prop-valued _♯₂_
   a x y = ptisp

   b : irreflexive _♯₂_
   b x = ptrec 𝟘-isProp g
    where
     g : ¬ Σ \(p : X → 𝟚) → p x ≢ p x
     g (p , u) = u refl
     
   c : symmetric _♯₂_
   c x y = ptfunct g
    where
     g : (Σ \(p : X → 𝟚) → p x ≢ p y) → Σ \(p : _ → 𝟚) → p y ≢ p x
     g (p , u) = p , ≢-sym u
   
   d : cotransitive _♯₂_
   d x y z = ptfunct g
    where
     g : (Σ \(p : X → 𝟚) → p x ≢ p y) → (x ♯₂ z) + (y ♯₂ z)
     g (p , u) = h (discrete-is-cotransitive 𝟚-discrete {p x} {p y} {p z} u)
      where
       h : (p x ≢ p z) + (p z ≢ p y) → (x ♯₂ z) + (y ♯₂ z)
       h (inl u) = inl ∣ p , u ∣
       h (inr v) = inr ∣ p , ≢-sym v ∣

 ♯₂-tight-ts : ∀ {U} {X : U ̇} → tight (_♯₂_ {U} {X}) → totally-separated X
 ♯₂-tight-ts {U} {X} t {x} {y} α = t x y (ptrec 𝟘-isProp h)
  where
   h : ¬ Σ \(p : X → 𝟚) → p x ≢ p y
   h (p , u) = u (α p)

 ts-♯₂-tight : ∀ {U} {X : U ̇} → totally-separated X → tight (_♯₂_ {U} {X})
 ts-♯₂-tight {U} {X} ts x y na = ts α
  where
   h : ¬ Σ \(p : X → 𝟚) → p x ≢ p y
   h (p , u) = na ∣ p , u ∣

   α : (p : X → 𝟚) → p x ≡ p y
   α p = 𝟚-separated (p x) (p y) (λ u → h (p , u))

\end{code}

 12 Feb 2018. This was prompted by the discussion
 https://nforum.ncatlab.org/discussion/8282/points-of-the-localic-quotient-with-respect-to-an-apartness-relation/

 But is clearly related to the above characterization of total
 separatedness.

\begin{code}

 reflexive transitive equivalence
     : ∀ {U V} {X : U ̇} → (X → X → V ̇) → U ⊔ V ̇
 
 reflexive   _≈_ = ∀ x → x ≈ x
 transitive  _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z
 equivalence _≈_ = prop-valued _≈_ × reflexive _≈_ × symmetric _≈_ × transitive _≈_

\end{code}

 The following is the standard equivalence relation induced by an
 apartness relation. The tightness axiom defined above says that this
 equivalence relation is equality.

\begin{code}

 neg-apart-is-equiv : ∀ {U} {X : U ̇} → FunExt U U₀
                    → (_♯_ : X → X → U ̇) → apartness _♯_ → equivalence (λ x y → ¬(x ♯ y))
 neg-apart-is-equiv {U} {X} fe _♯_ (♯p , ♯i , ♯s , ♯c) = p , ♯i , s , t
  where
   p : (x y : X) → isProp (¬ (x ♯ y))
   p x y = neg-isProp fe
   
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

 not-apart-have-same-apart : ∀ {U V} {X : U ̇} (x y : X) (_♯_ : X → X → V ̇) → apartness _♯_
                          → ¬(x ♯ y) → ((z : X) → x ♯ z ⇔ y ♯ z) 
 not-apart-have-same-apart {U} {V} {X} x y _♯_ (p , i , s , c) = g
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

 have-same-apart-are-not-apart : ∀ {U V} {X : U ̇} (x y : X) (_♯_ : X → X → V ̇) → apartness _♯_
                               → ((z : X) → x ♯ z ⇔ y ♯ z) → ¬(x ♯ y)
 have-same-apart-are-not-apart {U} {V} {X} x y _♯_ (p , i , s , c) = f
  where
   f : ((z : X) → x ♯ z ⇔ y ♯ z) → ¬ (x ♯ y)
   f φ a = i y (pr₁(φ y) a)

\end{code}

 Not-not equal elements are not apart, and hence, in the presence of
 tightness, they are equal. It follows that tight apartness types are
 sets.

\begin{code}

 not-not-equal-not-apart : ∀ {U V} {X : U ̇} (x y : X) (_♯_ : X → X → V ̇)
                         → apartness _♯_ → ¬¬(x ≡ y) → ¬(x ♯ y)
 not-not-equal-not-apart x y _♯_ (_ , i , _ , _) = contrapositive f
  where
   f : x ♯ y → ¬(x ≡ y)
   f a p = i y (transport (λ x → x ♯ y) p a)

 tight-separated : ∀ {U V} {X : U ̇} → (_♯_ : X → X → V ̇)
                 → apartness _♯_ → tight _♯_ → separated X
 tight-separated _♯_ a t = f
  where
   f : ∀ x y → ¬¬(x ≡ y) → x ≡ y
   f x y φ = t x y (not-not-equal-not-apart x y _♯_ a φ)

 tight-set : ∀ {U V} {X : U ̇} → FunExt U U₀
           → (_♯_ : X → X → V ̇) → apartness _♯_ → tight _♯_ → isSet X
 tight-set fe _♯_ a t = separated-is-set fe (tight-separated _♯_ a t)

\end{code}

 The above use the apartness and tightness data, but their existence is
 enough, because being a separated type and being a set are
 propositions.

\begin{code}

 tight-separated' : ∀ {U} {X : U ̇} → FunExt U U → FunExt U U₀
                 → (∃ \(_♯_ : X → X → U ̇) → apartness _♯_ × tight _♯_) → separated X
 tight-separated' {U} {X} fe fe₀ = ptrec (isProp-separated fe fe₀) f
   where
    f : (Σ \(_♯_ : X → X → U ̇) → apartness _♯_ × tight _♯_) → separated X
    f (_♯_ , a , t) = tight-separated _♯_ a t

 tight-set' : ∀ {U} {X : U ̇} → FunExt U U → FunExt U U₀
           → (∃ \(_♯_ : X → X → U ̇) → apartness _♯_ × tight _♯_) → isSet' X
 tight-set' {U} {X} fe fe₀ = ptrec (isProp-isSet' fe) f
   where
    f : (Σ \(_♯_ : X → X → U ̇) → apartness _♯_ × tight _♯_) → isSet' X
    f (_♯_ , a , t) = isSet-isSet' (tight-set fe₀ _♯_ a t)

\end{code}

 A map is called strongly extensional if it reflects apartness.

\begin{code}

 strongly-extensional : ∀ {U V W T} {X : U ̇} {Y : V ̇}
                              → (X → X → W ̇) → (Y → Y → T ̇) → (X → Y) → U ⊔ W ⊔ T ̇
 strongly-extensional _♯_ _♯'_ f = ∀ {x x'} → f x ♯' f x' → x ♯ x'
 

 preserves : ∀ {U V W T} {X : U ̇} {Y : V ̇}
          → (X → X → W ̇) → (Y → Y → T ̇) → (X → Y) → U ⊔ W ⊔ T ̇
 preserves R S f = ∀ {x x'} → R x x' → S (f x) (f x')

 module TightReflection
          {U V : Universe}
          (fe : ∀ U V → FunExt U V)
          (pe : propExt V)
          (X : U ̇)
          (_♯_ : X → X → V ̇)
          (♯p : prop-valued _♯_)
          (♯i : irreflexive _♯_)
          (♯s : symmetric _♯_)
          (♯c : cotransitive _♯_)
   where

\end{code}

  We now name the standard equivalence relation induced by _♯_.

\begin{code}

  _~_ : X → X → V ̇
  x ~ y = ¬(x ♯ y)

\end{code}

  For certain purposes we need the apartness axioms packed in to a
  single axiom.

\begin{code}

  ♯a : apartness _♯_
  ♯a = (♯p , ♯i , ♯s , ♯c)

\end{code}

  We choose our object Ω of truth-values (aka propositions) at
  universe V, as is the universe our apartness relations takes values
  in.

\begin{code}

  Ω : V ′ ̇
  Ω = Prop {V}

\end{code}

  The following two facts plays a crucial role.

\begin{code}

  Ω-isSet : isSet Ω
  Ω-isSet = Prop-isSet (fe V V) pe

  powerset-isSet : ∀ {W} {A : W ̇} → isSet(A → Ω)
  powerset-isSet {W} = isSet-exponential-ideal (fe W (V ′)) (λ x → Ω-isSet)

\end{code}

  Initially we tried to work with the function apart : X → (X → V ̇)
  defined by apart = _♯_. However, at some point in the development
  below it was difficult to proceed, when we need that the identity
  type apart x = apart y is a proposition. This should be the case
  because _♯_ is prop-valued. The most convenient way to achieve this
  is to restrict the codomain of apart from V to Ω.

\begin{code}

  apart : X → (X → Ω)
  apart x y = x ♯ y , ♯p x y

\end{code}

  The following is an immediate consequence of the fact that two
  equivalent elements have the same apartness class, using functional
  and propositional extensionality.

\begin{code}

  apart-lemma : (x y : X) → x ~ y → apart x ≡ apart y
  apart-lemma x y na = funext (fe U (V ′)) h
   where
    f : (z : X) → x ♯ z ⇔ y ♯ z
    f = not-apart-have-same-apart x y _♯_ ♯a na
     
    g : (z : X) → x ♯ z ≡ y ♯ z
    g z = pe (♯p x z) (♯p y z) (pr₁ (f z)) (pr₂ (f z))

    h : (z : X) → apart x z ≡ apart y z
    h z = to-Σ-Id isProp (g z , isProp-isProp (fe V V) _ _)

\end{code}

  We now construct the tight reflection of (X,♯) to get (X',♯')
  together with a universal strongly extensional map from X into
  tight apartness types. We take X' to be the image of the apart map.

\begin{code}

  open ImageAndSurjection pt
   
  X' : U ⊔ V ′ ̇
  X' = image apart

  X'-isSet : isSet X'
  X'-isSet = subset-of-set-is-set (X → Ω) _ powerset-isSet ptisp

  η : X → X'
  η = corestriction apart

\end{code}

  The following induction principle is our main tool. Its uses look
  convoluted at times by the need to show that the property one is
  doing induction over is prop-valued. Typically this involves the use
  of the fact the propositions form an exponential ideal, and, more
  generally, are closed under products.

\begin{code}

  η-surjection : isSurjection η
  η-surjection = corestriction-surjection apart

  η-induction : ∀ {W} (P : X' → W ̇)
             → ((x' : X') → isProp(P x'))
             → ((x : X) → P(η x))
             → (x' : X') → P x'
  η-induction = surjection-induction η η-surjection

\end{code}

  The apartness relation _♯'_ on X' is defined as follows.

\begin{code}

  _♯'_ : X' → X' → U ⊔ V ′ ̇
  (u , _) ♯' (v , _) = ∃ \(x : X) → Σ \(y : X) → (x ♯ y) × (apart x ≡ u) × (apart y ≡ v)

\end{code}

  Then η preserves and reflects apartness.

\begin{code}

  η-preserves-apartness : preserves _♯_ _♯'_ η
  η-preserves-apartness {x} {y} a = ∣ x , y , a , refl , refl ∣

  η-strongly-extensional : strongly-extensional _♯_ _♯'_ η
  η-strongly-extensional {x} {y} = ptrec (♯p x y) g
   where
    g : (Σ \(x' : X) → Σ \(y' : X) → (x' ♯ y') × (apart x' ≡ apart x) × (apart y' ≡ apart y))
      → x ♯ y
    g (x' , y' , a , p , q) = ♯s _ _ (j (♯s _ _ (i a)))
     where
      i : x' ♯ y' → x ♯ y'
      i = idtofun _ _ (ap pr₁ (happly _ _ p y'))
       
      j : y' ♯ x → y ♯ x
      j = idtofun _ _ (ap pr₁ (happly _ _ q x))

\end{code}

  Of course, we must check that _♯'_ is indeed an apartness
  relation. We do this by η-induction. These proofs by induction need
  routine proofs that some things are propositions. We include the
  following abbreviation `fuv` to avoid some long lines in such
  proofs.

\begin{code}

  fuv : FunExt (U ⊔ V ′) (U ⊔ V ′)
  fuv = fe (U ⊔ V ′) (U ⊔ V ′)

  ♯'p : prop-valued _♯'_
  ♯'p _ _ = ptisp

  ♯'i : irreflexive _♯'_
  ♯'i = by-induction
   where
    induction-step : ∀ x → ¬(η x ♯' η x)
    induction-step x a = ♯i x (η-strongly-extensional a)
     
    by-induction : _
    by-induction = η-induction (λ x' → ¬ (x' ♯' x'))
                      (λ _ → isProp-exponential-ideal (fe (U ⊔ V ′) U₀) (λ _ → 𝟘-isProp))
                      induction-step

  ♯'s : symmetric _♯'_
  ♯'s = by-nested-induction
   where
    induction-step : ∀ x y → η x ♯' η y → η y ♯' η x
    induction-step x y a = η-preserves-apartness(♯s x y (η-strongly-extensional a))
     
    by-nested-induction : _
    by-nested-induction =
      η-induction (λ x' → ∀ y' → x' ♯' y' → y' ♯' x')
       (λ x' → isProp-exponential-ideal fuv
                (λ y' → isProp-exponential-ideal fuv (λ _ → ♯'p y' x')))
       (λ x → η-induction (λ y' → η x ♯' y' → y' ♯' η x)
                (λ y' → isProp-exponential-ideal fuv (λ _ → ♯'p y' (η x)))
                (induction-step x))
   
  ♯'c : cotransitive _♯'_
  ♯'c = by-nested-induction
   where
    induction-step : ∀ x y z → η x ♯' η y → η x ♯' η z ∨ η y ♯' η z
    induction-step x y z a = ptfunct c b
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
       (λ _ → isProp-exponential-ideal fuv
                (λ _ → isProp-exponential-ideal fuv
                         (λ _ → isProp-exponential-ideal fuv (λ _ → ptisp))))
       (λ x → η-induction (λ y' → ∀ z' → η x ♯' y' → (η x ♯' z') ∨ (y' ♯' z'))
                (λ _ → isProp-exponential-ideal fuv
                         (λ _ → isProp-exponential-ideal fuv (λ _ → ptisp)))
                (λ y → η-induction (λ z' → η x ♯' η y → (η x ♯' z') ∨ (η y ♯' z'))
                         (λ _ → isProp-exponential-ideal fuv (λ _ → ptisp))
                         (induction-step x y)))

  ♯'a : apartness _♯'_
  ♯'a = (♯'p , ♯'i , ♯'s , ♯'c)

\end{code}

  The tightness of _♯'_ cannot by proved by induction by reduction to
  properties of _♯_, as above, because _♯_ is not (necessarily)
  tight. We need to work with the definitions of X' and _♯'_ directly.

\begin{code}

  ♯'t : tight _♯'_
  ♯'t (u , e) (v , f) n = ptrec X'-isSet (λ σ → ptrec X'-isSet (h σ) f) e
   where
    h : (Σ \(x : X) → apart x ≡ u) → (Σ \(y : X) → apart y ≡ v) → (u , e) ≡ (v , f)
    h (x , p) (y , q) = to-Σ-Id _ (t , ptisp _ _)
     where
      remark : ∥(Σ \(x : X) → Σ \(y : X) → (x ♯ y) × (apart x ≡ u) × (apart y ≡ v))∥ → 𝟘
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
  η-equal-equiv {x} {y} p a = ♯'i (η y) (transport (λ z → z ♯' η y) p (η-preserves-apartness a))

\end{code}

  We now show that the above data provide the tight reflection, or
  universal strongly extensional map from X to tight apartness types,
  where unique existence is expressed by the contractibility of a Σ
  type, as usual in univalent mathematics and homotopy type
  theory. Notice the use of η-induction to avoid dealing directly with
  the details of the constructions performed above.

\begin{code}

  tight-reflection : ∀ {W T} (A : W ̇) (_♯ᴬ_ : A → A → T ̇)
                   → apartness _♯ᴬ_
                   → tight _♯ᴬ_
                   → (f : X → A)
                   → strongly-extensional _♯_ _♯ᴬ_ f
                   → isContr (Σ \(f' : X' → A) → f' ∘ η ≡ f)
  tight-reflection {W} {T} A  _♯ᴬ_  ♯ᴬa  ♯ᴬt  f  se = ic
   where
    iss : isSet A
    iss = tight-set (fe W U₀) _♯ᴬ_ ♯ᴬa ♯ᴬt
     
    i : {x y : X} → x ~ y → f x ≡ f y
    i = ♯ᴬt _ _ ∘ contrapositive se
     
    φ : (x' : X') → isProp (Σ \a → ∃ \x → (η x ≡ x') × (f x ≡ a))
    φ = η-induction _ γ induction-step
      where
       induction-step : (y : X) → isProp (Σ \a → ∃ \x → (η x ≡ η y) × (f x ≡ a))
       induction-step x (a , d) (b , e) = to-Σ-Id _ (p , ptisp _ _)
        where
         h :  (Σ \x' → (η x' ≡ η x) × (f x' ≡ a))
           → (Σ \y' → (η y' ≡ η x) × (f y' ≡ b))
           → a ≡ b
         h (x' , r , s) (y' , t , u) = s ⁻¹ ∙ i (η-equal-equiv (r ∙ t ⁻¹)) ∙ u
          
         p : a ≡ b
         p = ptrec iss (λ σ → ptrec iss (h σ) e) d

       γ : (x' : X') → isProp (isProp (Σ \a → ∃ \x → (η x ≡ x') × (f x ≡ a)))
       γ x' = isProp-isProp (fe (U ⊔ (V ′) ⊔ W) (U ⊔ (V ′) ⊔ W))

    k : (x' : X') → Σ \(a : A) → ∃ \(x : X) → (η x ≡ x') × (f x ≡ a)
    k = η-induction _ φ induction-step
     where
      induction-step : (y : X) → Σ \a → ∃ \x → (η x ≡ η y) × (f x ≡ a)
      induction-step x = f x , ∣ x , refl , refl ∣

    f' : X' → A
    f' x' = pr₁(k x')

    r : f' ∘ η ≡ f
    r = funext (fe U W) h
     where
      g : (y : X) → ∃ \x → (η x ≡ η y) × (f x ≡ f' (η y))
      g y = pr₂(k(η y))

      j : (y : X) → (Σ \x → (η x ≡ η y) × (f x ≡ f' (η y))) → f'(η y) ≡ f y
      j y (x , p , q) = q ⁻¹ ∙ i (η-equal-equiv p)
         
      h : (y : X) → f'(η y) ≡ f y
      h y = ptrec iss (j y) (g y)

    c : (σ : Σ \(f'' : X' → A) → f'' ∘ η ≡ f) → (f' , r) ≡ σ
    c (f'' , s) = to-Σ-Id _ (t , v)
     where
      w : ∀ x → f'(η x) ≡ f''(η x)
      w x = ap (λ f → f x) (r ∙ s ⁻¹)

      t : f' ≡ f''
      t = funext (fe (U ⊔ V ′) W) (η-induction _ (λ _ → iss) w)

      u : f'' ∘ η ≡ f
      u = transport (λ g → g ∘ η ≡ f) t r

      v : u ≡ s
      v = isSet-exponential-ideal (fe U W) (λ _ → iss) u s
                     
    ic : isContr (Σ \(f' : X' → A) → f' ∘ η ≡ f)
    ic = (f' , r) , c

\end{code}

  The following is a consequence of the reflection, but we offer a
  direct proof.

\begin{code}

  tight-η-equiv : tight _♯_ → X ≃ X'
  tight-η-equiv t = (η , isContrMap-is-equiv η cm)
   where
    lc : left-cancellable η
    lc {x} {y} p = i h
     where
      i : ¬ (η x ♯' η y) → x ≡ y
      i = t x y ∘ contrapositive (η-preserves-apartness {x} {y})
     
      h : ¬(η x ♯' η y)
      h a = ♯'i (η y) (transport (λ z → z ♯' η y) p a)

    e : isEmbedding η
    e = s-lc-e η lc X'-isSet

    cm : isContrMap η
    cm = pr₂ (c-es η) (e , η-surjection)

\end{code}

TODO. 

* The tight reflection has the universal property of the quotient by
  _~_. Conversely, the quotient by _~_ gives the tight reflection.

* The tight reflection of ♯₂ has the universal property of the totally
  separated reflection.
