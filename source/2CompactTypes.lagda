Martin Escardo, January 2018

We consider 𝟚-Compact types, various closure properties for them, and
their interaction with discreteness, total separatedess and function
types.

(More generally, we can consider S-compact types where S is a
dominance (such as the Rosolini dominance, which is one manifestation
of the Sierpinski space), but we don't do this here.)

Because 𝟚-Compact types are defined in terms of maps into 𝟚, a type is
𝟚-compact iff its totally separated reflection is 𝟚-compact, since
𝟚-compactness is a proposition. We also discuss the 𝟚-compactness of
propositions.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF

module 2CompactTypes (fe : ∀ U V → FunExt U V)
                     (pt : PropTrunc)
                     where
                     
open PropositionalTruncation (pt)
open import Two
open import DecidableAndDetachable

\end{code}

The following is our primary notion of compactness here, which is
implied by omniscience and hence by searchability.  However,
compactness is property of a type whereas omniscience and
searchability (as we have defined them in the modules OmniscientTypes
and SearchableTypes) are structure on the type.

\begin{code}

𝟚-Compact : ∀ {U} → U ̇ → U ̇
𝟚-Compact X = (p : X → 𝟚) → decidable (∃ \(x : X) → p x ≡ ₀)

𝟚-Compact-isProp : ∀ {U} {X : U ̇} → isProp (𝟚-Compact X)
𝟚-Compact-isProp {U} = isProp-exponential-ideal (fe U U)
                         (λ _ → decidable-isProp (fe U U₀) ptisp)
\end{code}

The following technical lemmas are often useful in our investigation
of compactness.

\begin{code}

not-exists₀-implies-forall₁ : ∀ {U} {X : U ̇} (p : X → 𝟚)
                            → ¬ (∃ \(x : X) → p x ≡ ₀) → (Π \(x : X) → p x ≡ ₁)
not-exists₀-implies-forall₁ p u x = Lemma[b≢₀→b≡₁] (not-exists-implies-forall-not (u ∘ ∣_∣) x)

forall₁-implies-not-exists₀ : ∀ {U} {X : U ̇} (p : X → 𝟚)
                            → (Π \(x : X) → p x ≡ ₁) → ¬ ∃ \(x : X) → p x ≡ ₀
forall₁-implies-not-exists₀ p α = ptrec 𝟘-isProp h
 where
  h : (Σ \x → p x ≡ ₀) → 𝟘
  h (x , r) = zero-is-not-one (r ⁻¹ ∙ α x)

\end{code}

We also consider a weakening of the notion of compactness, which is
frequently enough to get our desired conclusions from the assumption
of compactness. Notice that the original notion is written with
capital C whereas its weakining is written with lower case c. The
relation of (strong) compactness with weak compactness is the same as
that of LPO with WLPO.

\begin{code}

𝟚-compact : ∀ {U} → U ̇ → U ̇
𝟚-compact X = (p : X → 𝟚) → decidable ((x : X) → p x ≡ ₁)

open import UF2

𝟚-compact-isProp : ∀ {U} {X : U ̇} → isProp (𝟚-compact X)
𝟚-compact-isProp {U} = isProp-exponential-ideal (fe U U)
                         (λ _ → decidable-isProp (fe U U₀)
                                  (isProp-exponential-ideal (fe U U₀) λ _ → 𝟚-is-set))

\end{code}

We do indeed get a stronger notion:

\begin{code}

𝟚-Cc : ∀ {U} {X : U ̇} → 𝟚-Compact X → 𝟚-compact X
𝟚-Cc {U} {X} c p = f (c p)
 where
  f : decidable (∃ \(x : X) → p x ≡ ₀) → decidable (Π \(x : X) → p x ≡ ₁)
  f (inl s) = inr (λ α → ptrec 𝟘-isProp (g α) s)
   where
    g : ((x : X) → p x ≡ ₁) → ¬ Σ \x → p x ≡ ₀
    g α (x , r) = zero-is-not-one (r ⁻¹ ∙ α x)
  f (inr u) = inl (not-exists₀-implies-forall₁ p u)

\end{code}

The weak compactness of X is equivalent to the isolatedness of the
boolean predicate λ x → ₁:

\begin{code}

𝟚-compact' : ∀ {U} → U ̇ → U ̇
𝟚-compact' X = (p : X → 𝟚) → decidable (p ≡ λ x → ₁)

𝟚-c'c : ∀ {U} {X : U ̇} → 𝟚-compact' X → 𝟚-compact X
𝟚-c'c {U} {X} c' p = g (c' p)
 where
  g : decidable (p ≡ λ x → ₁) → decidable ((x : X) → p x ≡ ₁)
  g (inl r) = inl (happly p (λ x → ₁) r)
  g (inr u) = inr (contrapositive (funext (fe U U₀)) u)

𝟚-cc' : ∀ {U} {X : U ̇} → 𝟚-compact X → 𝟚-compact' X
𝟚-cc' {U} {X} c p = g (c p)
 where
  g : decidable ((x : X) → p x ≡ ₁) → decidable (p ≡ λ x → ₁)
  g (inl α) = inl (funext (fe U U₀) α)
  g (inr u) = inr (contrapositive (happly p (λ x → ₁)) u)

\end{code}

In classical topology, the Tychonoff Theorem gives that compact to the
power discrete is compact (where we read the function type X → Y as "Y
to the power X", with Y the base and X the exponent, and call it an
exponential). Here we don't have the Tychonoff Theorem (in the absence
of anti-classical intuitionistic assumptions).

It is less well-known that in classical topology we also have that
discrete to the power compact is discrete. This we do have here,
without the need of any assumption:

\begin{code}

open import DiscreteAndSeparated

cdd : ∀ {U V} {X : U ̇} {Y : V ̇}
   → 𝟚-compact X → discrete Y → discrete(X → Y)
cdd {U} {V} {X} {Y} c d f g = h (c p)
 where
  p : X → 𝟚
  p = pr₁ (co-characteristic-function (λ x → d (f x) (g x)))
  
  r : (x : X) → (p x ≡ ₀ → ¬ (f x ≡ g x)) × (p x ≡ ₁ → f x ≡ g x)
  r = pr₂ (co-characteristic-function λ x → d (f x) (g x))

  φ : ((x : X) → p x ≡ ₁) → f ≡ g
  φ α = (funext (fe U V) (λ x → pr₂ (r x) (α x)))
  
  γ : f ≡ g → (x : X) → p x ≡ ₁ 
  γ t x = Lemma[b≢₀→b≡₁] (λ u → pr₁ (r x) u (happly f g t x))

  h : decidable((x : X) → p x ≡ ₁) → decidable (f ≡ g)
  h (inl α) = inl (φ α)
  h (inr u) = inr (contrapositive γ u)

\end{code}

If an exponential with discrete base is discrete, then its exponent is
compact, provided the base has at least two points.

First, to decide Π(p:X→𝟚), p(x)=1, decide p = λ x → ₁:

\begin{code}

d𝟚c : ∀ {U} {X : U ̇} → discrete(X → 𝟚) → 𝟚-compact X 
d𝟚c d = 𝟚-c'c (λ p → d p (λ x → ₁))

\end{code}

A type X has 𝟚 as a retract iff it can be written as X₀+X₁ with X₀ and
X₁ pointed. A sufficient (but by no means necessary) condition for
this is that there is an isolated point x₀ and a point different from
x₀ (in this case the decomposition is with X₀ ≃ 𝟙).

\begin{code}

dcc : ∀ {U V} {X : U ̇} {Y : V ̇} → retract 𝟚 of Y → discrete(X → Y) → 𝟚-compact X 
dcc {U} re d = d𝟚c (retract-discrete-discrete (rpe (fe U U₀) re) d)

ddc' : ∀ {U V} {X : U ̇} {Y : V ̇} (y₀ y₁ : Y) → y₀ ≢ y₁
    → discrete Y → discrete(X → Y) → 𝟚-compact X 
ddc' y₀ y₁ ne dy = dcc (𝟚-retract-of-discrete ne dy)
  
\end{code}

So, in summary, if Y is a non-trivial discrete type, then X is
𝟚-compact iff (X → Y) is discrete.

Compactness of omniscient sets (and hence of searchable sets, and
hence of ℕ∞):

\begin{code}

open import OmniscientTypes

omniscient-Compact : ∀ {U} {X : U ̇} → omniscient X → 𝟚-Compact X
omniscient-Compact {U} {X} φ p = g (φ p)
 where
  g : ((Σ \(x : X) → p x ≡ ₀) + ((x : X) → p x ≡ ₁)) → decidable (∃ \(x : X) → p x ≡ ₀)
  g (inl (x , r)) = inl ∣ x , r ∣
  g (inr α) = inr (forall₁-implies-not-exists₀ p α)

\end{code}

But notice that the 𝟚-compactness of ℕ is (literally) WLPO.

Compactness of images:

\begin{code}

open ImageAndSurjection (pt)
open import UF2

surjection-𝟚-Compact : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                     → isSurjection f → 𝟚-Compact X → 𝟚-Compact Y
surjection-𝟚-Compact {U} {V} {X} {Y} f su c q = g (c (q ∘ f)) 
 where
  h : (Σ \(x : X) → q(f x) ≡ ₀) → Σ \(y : Y) → q y ≡ ₀
  h (x , r) = (f x , r)
  
  l : (y : Y) → q y ≡ ₀ → (Σ \(x : X) → f x ≡ y) → Σ \(x : X) → q (f x) ≡ ₀
  l y r (x , s) = (x , (ap q s ∙ r))
  
  k : (Σ \(y : Y) → q y ≡ ₀) → ∃ \(x : X) → q (f x) ≡ ₀
  k (y , r) = ptfunct (l y r) (su y)
  
  g : decidable (∃ \(x : X) → q(f x) ≡ ₀) → decidable (∃ \(y : Y) → q y ≡ ₀)
  g (inl s) = inl (ptfunct h s)
  g (inr u) = inr (contrapositive (ptrec ptisp k) u)

image-𝟚-Compact : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
               → 𝟚-Compact X → 𝟚-Compact (image f)
image-𝟚-Compact f = surjection-𝟚-Compact (corestriction f) (corestriction-surjection f)

surjection-𝟚-compact : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                     → isSurjection f → 𝟚-compact X → 𝟚-compact Y
surjection-𝟚-compact {U} {V} {X} {Y} f su c q = g (c (q ∘ f)) 
 where
  g : decidable((x : X) → q (f x) ≡ ₁) → decidable ((x : Y) → q x ≡ ₁)
  g (inl s) = inl (surjection-induction f su (λ y → q y ≡ ₁) (λ _ → 𝟚-is-set) s)
  g (inr u) = inr (contrapositive (λ φ x → φ (f x)) u)

image-𝟚-compact : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
               → 𝟚-compact X → 𝟚-compact (image f)
image-𝟚-compact f = surjection-𝟚-compact (corestriction f) (corestriction-surjection f)

retract-𝟚-compact : ∀ {U V} {X : U ̇} {Y : V ̇}
                  → retract Y of X → 𝟚-compact X → 𝟚-compact Y
retract-𝟚-compact (f , hass) = surjection-𝟚-compact f (retraction-surjection f hass)

i2c2c : ∀ {U V} {X : U ̇} {Y : V ̇}
      → X → 𝟚-compact (X → Y) → 𝟚-compact Y
i2c2c x = retract-𝟚-compact ((λ f → f x) , ((λ y _ → y) , λ y → refl)) 

\end{code}

A main reason to consider the notion of total separatedness is that
the totally separated reflection T X of X has the same supply of
boolean predicates as X, and hence X is compact iff T X is compact, as
we show now.

\begin{code}

open import TotallySeparated

module TCompactness {U : Universe} (X : U ̇) where

 open TotallySeparatedReflection {U} fe pt
 
 extension : (X → 𝟚) → (T X → 𝟚)
 extension p = pr₁ (pr₁ (totally-separated-reflection 𝟚-totally-separated p))

 extension-property : (p : X → 𝟚) (x : X) → extension p (η x) ≡ p x
 extension-property p = happly _ _ (pr₂ (pr₁ (totally-separated-reflection 𝟚-totally-separated p)))

 ct : 𝟚-compact X → 𝟚-compact (T X)
 ct = surjection-𝟚-compact η (η-surjection)

 tc : 𝟚-compact (T X) → 𝟚-compact X
 tc c p = h (c (extension p))
  where
   f : ((x' : T X) → extension p x' ≡ ₁) → ((x : X) → p x ≡ ₁)
   f α x = (extension-property p x) ⁻¹ ∙ α (η x)
   
   g : (α : (x : X) → p x ≡ ₁) → ((x' : T X) → extension p x' ≡ ₁)
   g α = η-induction (λ x' → extension p x' ≡ ₁) (λ _ → 𝟚-is-set) g'
     where
      g' : (x : X) → extension p (η x) ≡ ₁
      g' x = extension-property p x ∙ α x 

   h : decidable ((x' : T X) → extension p x' ≡ ₁) → decidable ((x : X) → p x ≡ ₁)
   h (inl α) = inl (f α)
   h (inr u) = inr (contrapositive g u)

 Ct : 𝟚-Compact X → 𝟚-Compact (T X)
 Ct = surjection-𝟚-Compact η (η-surjection) 

 tC : 𝟚-Compact (T X) → 𝟚-Compact X
 tC c p = h (c (extension p))
  where
   f : (Σ \(x' : T X) → extension p x' ≡ ₀) → ∃ \(x : X) → p x ≡ ₀
   f (x' , r) = ptfunct f' (η-surjection x')
    where
     f' : (Σ \(x : X) → η x ≡ x') → Σ \(x : X) → p x ≡ ₀
     f' (x , s) = x , ((extension-property p x) ⁻¹ ∙ ap (extension p) s ∙ r)

   g : (Σ \(x : X) → p x ≡ ₀) → Σ \(x' : T X) → extension p x' ≡ ₀
   g (x , r) = η x , (extension-property p x ∙ r) 

   h : decidable (∃ \(x' : T X) → extension p x' ≡ ₀) → decidable (∃ \(x : X) → p x ≡ ₀)
   h (inl x) = inl (ptrec ptisp f x)
   h (inr u) = inr (contrapositive (ptfunct g) u)

\end{code}

If X is totally separated, and (X → 𝟚) is compact, then X is
discrete. More generally, if 𝟚 is a retract of Y and (X → Y) is
compact, then X is discrete if it is totally separated. This is a new
result as far as I know. I didn't know it before 12th January 2018.

The following proof works as follows. For any given x,y:X, define
q:(X→𝟚)→𝟚 such that q(p)=1 ⇔ p(x)=p(y), which is possible because 𝟚
has decidable equality (it is discrete). By the 𝟚-compactness of X→𝟚,
the condition (p:X→𝟚)→q(p)=1 is decidable, which amounts to saying
that (p:X→𝟚) → p(x)=p(y) is decidable. But because X is totally
separated, the latter is equivalent to x=y, which shows that X is
discrete.

\begin{code}

tscd : ∀ {U} {X : U ̇} → totally-separated X → 𝟚-compact (X → 𝟚) → discrete X
tscd {U} {X} ts c x y = g (a s)
 where
  q : (X → 𝟚) → 𝟚
  q = pr₁ (co-characteristic-function (λ p → 𝟚-discrete (p x) (p y)))
  
  r : (p : X → 𝟚) → (q p ≡ ₀ → p x ≢ p y) × (q p ≡ ₁ → p x ≡ p y)
  r = pr₂ (co-characteristic-function (λ p → 𝟚-discrete (p x) (p y)))
  
  s : decidable ((p : X → 𝟚) → q p ≡ ₁)
  s = c q
  
  b : (p : X → 𝟚) → p x ≡ p y → q p ≡ ₁
  b p u = Lemma[b≢₀→b≡₁] (λ v → pr₁ (r p) v u)
  
  a : decidable ((p : X → 𝟚) → q p ≡ ₁) → decidable((p : X → 𝟚) → p x ≡ p y)
  a (inl f) = inl (λ p → pr₂ (r p) (f p))
  a (inr φ) = inr h
   where
    h : ¬((p : X → 𝟚) → p x ≡ p y)
    h α = φ (λ p → b p (α p))

  g : decidable ((p : X → 𝟚) → p x ≡ p y) → decidable(x ≡ y)
  g (inl α) = inl (ts α)
  g (inr u) = inr (contrapositive (λ e p → ap p e) u)

\end{code}

We are interested in the following two generalizations, which arise as
corollaries:

\begin{code}

tscd₀ : {X : U₀ ̇} {Y : U₀ ̇} → totally-separated X → retract 𝟚 of Y
     → 𝟚-compact (X → Y) → discrete X
tscd₀ {X} {Y} ts r c = tscd ts (retract-𝟚-compact (rpe (fe U₀ U₀) r) c)

module _ {U : Universe} {X : U ̇} where

 open TotallySeparatedReflection {U} fe pt

 tscd₁ : ∀ {V} {Y : V ̇} → retract 𝟚 of Y
      → 𝟚-compact (X → Y) → discrete (T X)
 tscd₁ {V} {Y} r c = f
  where
   z : retract (X → 𝟚) of (X → Y)
   z = rpe (fe U U₀) r
   
   a : (T X → 𝟚) ≃ (X → 𝟚)
   a = totally-separated-reflection'' 𝟚-totally-separated
   
   b : retract (T X → 𝟚) of (X → 𝟚)
   b = equiv-retract-l a
   
   d : retract (T X → 𝟚) of (X → Y)
   d = retracts-compose z b
   
   e : 𝟚-compact (T X → 𝟚)
   e = retract-𝟚-compact d c
   
   f : discrete (T X)
   f = tscd tts e 

\end{code}

In topological models, 𝟚-compactness is the same as topological
compactess in the presence of total separatedness, at least for some
spaces, including the Kleene-Kreisel spaces, which model the simple
types (see the module SimpleTypes). Hence, for example, the
topological space (ℕ∞→𝟚) is not 𝟚-compact because it is countably
discrete, as it is a theorem of topology that discrete to the power
compact is again discrete, which is compact iff it is finite. This
argument is both classical and external.

But here we have that the type (ℕ∞→𝟚) is "not" 𝟚-compact, internally
and constructively.

\begin{code}

open import DiscreteAndSeparated
open import GenericConvergentSequence
open import WLPO

[ℕ∞→𝟚]-compact-implies-WLPO : 𝟚-compact (ℕ∞ → 𝟚) → WLPO
[ℕ∞→𝟚]-compact-implies-WLPO c = ℕ∞-discrete-WLPO (tscd (ℕ∞-totally-separated (fe U₀ U₀)) c)

\end{code}

Closure of compactness under sums (and hence binary products):

\begin{code}

𝟚-compact-closed-under-Σ : ∀ {U V} {X : U ̇} {Y : X → V ̇}
                         → 𝟚-compact X → ((x : X) → 𝟚-compact (Y x)) → 𝟚-compact (Σ Y)
𝟚-compact-closed-under-Σ {U} {V} {X} {Y} c d p = g e
 where
  f : ∀ x → decidable (∀ y → p (x , y) ≡ ₁)
  f x = d x (λ y → p (x , y))
  
  q : X → 𝟚
  q = pr₁ (co-characteristic-function f)
  
  q₀ : (x : X) → q x ≡ ₀ → ¬ ((y : Y x) → p (x , y) ≡ ₁)
  q₀ x = pr₁(pr₂ (co-characteristic-function f) x)
  
  q₁ : (x : X) → q x ≡ ₁ → (y : Y x) → p (x , y) ≡ ₁
  q₁ x = pr₂(pr₂ (co-characteristic-function f) x)

  e : decidable (∀ x → q x ≡ ₁)
  e = c q

  g : decidable (∀ x → q x ≡ ₁) → decidable(∀ σ → p σ ≡ ₁)
  g (inl α) = inl h
   where
    h : (σ : Σ Y) → p σ ≡ ₁
    h (x , y) = q₁ x (α x) y
  g (inr u) = inr (contrapositive h u)
   where
    h : ((σ : Σ Y) → p σ ≡ ₁) → (x : X) → q x ≡ ₁
    h β x = Lemma[b≢₀→b≡₁] (λ r → q₀ x r (λ y → β (x , y)))

\end{code}

TODO. Consider also capital compactness, and other closure properties.

We now turn to the compactness of propositions. A proposition is
strongly compact iff it is decidable. Regarding the weak compactness
of propositions, we have partial information for the moment.

\begin{code}

module CompactnessOfPropositions where

 ispcd : ∀ {U} (X : U ̇) → isProp X → 𝟚-Compact X → decidable X
 ispcd X isp c = f a
  where
   a : decidable ∥ X × (₀ ≡ ₀) ∥ 
   a = c (λ x → ₀)
   
   f : decidable ∥ X × (₀ ≡ ₀) ∥ → decidable X
   f (inl s) = inl (ptrec isp pr₁ s)
   f (inr u) = inr (λ x → u ∣ x , refl ∣)

 ispdc : ∀ {U} (X : U ̇) → isProp X → decidable X → 𝟚-Compact X
 ispdc X isp d p = g d
  where
   g : decidable X → decidable (∃ \x → p x ≡ ₀)
   g (inl x) = two-equality-cases b c
    where
     b : p x ≡ ₀ → decidable (∃ \x → p x ≡ ₀)
     b r = inl ∣ x , r ∣
     
     c : p x ≡ ₁ → decidable (∃ \x → p x ≡ ₀)
     c r = inr (ptrec (𝟘-isProp) f) 
      where
       f : ¬ Σ \y → p y ≡ ₀
       f (y , q) = zero-is-not-one (transport (λ x → p x ≡ ₀) (isp y x) q ⁻¹ ∙ r)
       
   g (inr u) = inr (ptrec 𝟘-isProp (λ σ → u(pr₁ σ)))

 ispcwd : ∀ {U} (X : U ̇) → isProp X → 𝟚-compact X → decidable(¬ X)
 ispcwd X isp c = f a
  where
   a : decidable (X → ₀ ≡ ₁)
   a = c (λ x → ₀)
   
   f : decidable (X → ₀ ≡ ₁) → decidable (¬ X)
   f (inl u) = inl (zero-is-not-one  ∘ u)
   f (inr φ) = inr λ u → φ (λ x → 𝟘-elim (u x) )

 em2cdn : ∀ {U} (X : U ̇) → isProp X → 𝟚-compact(X + ¬ X) → decidable (¬ X)
 em2cdn X isp c = cases l m a
  where
   p : X + ¬ X → 𝟚
   p (inl x) = ₀
   p (inr u) = ₁
  
   a : decidable ((z : X + ¬ X) → p z ≡ ₁)
   a = c p
  
   l : ((z : X + ¬ X) → p z ≡ ₁) → ¬ X + ¬¬ X
   l α = inl(λ x → 𝟘-elim (zero-is-not-one (α (inl x))))
  
   α : (u : X → 𝟘) (z : X + ¬ X) → p z ≡ ₁
   α u (inl x) = 𝟘-elim (u x)
   α u (inr v) = refl
     
   m : ¬((z : X + ¬ X) → p z ≡ ₁) → ¬ X + ¬¬ X
   m φ = inr(λ u → φ(α u))

\end{code}

TODO: Notice that the map ∣_∣:X→∥X∥ is a surjection, and hence if X is
𝟚-Compact, then ∥X∥, being a searchable proposition, is
decidable. That is, if X is compact then it is decidable whether it is
inhabited.

See also the module SimpleTypes, which uses this module to study
the least collection of types containing ℕ (and sometimes 𝟚) closed
under (non-dependent) function types.

20 Jan 2017

We now consider a truncated version of searchability (see the modules
SearchableTypes and OmniscientTypes).

\begin{code}

𝟚-CompactInhabited : ∀ {U} → U ̇ → U ̇
𝟚-CompactInhabited X = (p : X → 𝟚) → ∃ \(x₀ : X) → p x₀ ≡ ₁ → (x : X) → p x ≡ ₁

𝟚-CompactInhabited-isProp : ∀ {U} {X : U ̇} → isProp (𝟚-CompactInhabited X)
𝟚-CompactInhabited-isProp {U} = isProp-exponential-ideal (fe U U) (λ _ → ptisp)

𝟚-ci-i-and-c : ∀ {U} {X : U ̇} → 𝟚-CompactInhabited X → ∥ X ∥ × 𝟚-Compact X
𝟚-ci-i-and-c {U} {X} c = (ptfunct pr₁ g₁ , λ p → ptrec (decidable-isProp (fe U U₀) ptisp) (g₂ p) (c p))
 where
  g₁ : ∥ Σ (λ x₀ → ₀ ≡ ₁ → (x : X) → ₀ ≡ ₁) ∥
  g₁ = c (λ x → ₀)

  g₂ : (p : X → 𝟚) → (Σ \(x₀ : X) → p x₀ ≡ ₁ → (x : X) → p x ≡ ₁) → decidable (∃ \(x : X) → p x ≡ ₀)
  g₂ p (x₀ , φ) = h (𝟚-discrete (p x₀) ₁)
   where
    h : decidable(p x₀ ≡ ₁) → decidable (∃ \(x : X) → p x ≡ ₀)
    h (inl r) = inr (ptrec 𝟘-isProp f)
     where
      f : ¬ Σ \(x : X) → p x ≡ ₀
      f (x , s) = zero-is-not-one (s ⁻¹ ∙ φ r x)
    h (inr u) = inl ∣ x₀ , (Lemma[b≢₁→b≡₀] u) ∣

𝟚-i-and-c-ci : ∀ {U} {X : U ̇} → ∥ X ∥ × 𝟚-Compact X → 𝟚-CompactInhabited X
𝟚-i-and-c-ci {U} {X} (t , c) p = ptrec ptisp f t
 where
  f : X → ∃ \(x₀ : X) → p x₀ ≡ ₁ → (x : X) → p x ≡ ₁
  f x₀ = g (𝟚-discrete (p x₀) ₀) (c p)
   where
    g : decidable(p x₀ ≡ ₀) → decidable (∃ \(x : X) → p x ≡ ₀) → ∃ \(x₀ : X) → p x₀ ≡ ₁ → (x : X) → p x ≡ ₁
    g (inl r) e = ∣ x₀ , (λ s _ → 𝟘-elim (zero-is-not-one (r ⁻¹ ∙ s))) ∣
    g (inr _) (inl t) = ptfunct h t
     where
      h : (Σ \(x : X) → p x ≡ ₀) → Σ \(x₀ : X) → p x₀ ≡ ₁ → (x : X) → p x ≡ ₁
      h (x , r) = x , λ s _ → 𝟘-elim (zero-is-not-one (r ⁻¹ ∙ s))
    g (inr _) (inr v) = ∣ x₀ , (λ _ → not-exists₀-implies-forall₁ p v) ∣

\end{code}

This characterizes the 𝟚-CompactInhabited types as those that are
𝟚-Compact and inhabited. We can also characterize the 𝟚-Compact types
as those that are 𝟚-CompactInhabited or empty:

\begin{code}

isProp-𝟚-CIorNe : ∀ {U} {X : U ̇} → isProp(𝟚-CompactInhabited X + ¬ X)
isProp-𝟚-CIorNe {U} {X} = sum-of-contradictory-props
                           𝟚-CompactInhabited-isProp (isProp-exponential-ideal (fe U U₀) (λ _ → 𝟘-isProp))
                             (λ c u → ptrec 𝟘-isProp (contrapositive pr₁ u) (c (λ _ → ₀)))

𝟚-CIorNE-C : ∀ {U} {X : U ̇} → 𝟚-CompactInhabited X + ¬ X → 𝟚-Compact X
𝟚-CIorNE-C (inl c)   = pr₂(𝟚-ci-i-and-c c)
𝟚-CIorNE-C (inr u) p = inr (ptrec 𝟘-isProp (λ σ → u (pr₁ σ)))

𝟚-C-CIorNE : ∀ {U} {X : U ̇} → 𝟚-Compact X → 𝟚-CompactInhabited X + ¬ X
𝟚-C-CIorNE {U} {X} c = g
 where
  h : decidable (∃ \(x : X) → ₀ ≡ ₀) → 𝟚-CompactInhabited X + ¬ X
  h (inl t) = inl (𝟚-i-and-c-ci (ptfunct pr₁ t , c))
  h (inr u) = inr (contrapositive (λ x → ∣ x , refl ∣) u)
  
  g : 𝟚-CompactInhabited X + ¬ X
  g = h (c (λ _ → ₀))

\end{code}

Perhaps this characterization of compacteness can make some of the
above proofs a little bit more direct.
