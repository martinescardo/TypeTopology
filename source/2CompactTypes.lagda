Martin Escardo, January 2018

We define and study 𝟚-compact types.

A dominance is a collection of propositions (or subsingletons, or
truth values) that contains 𝟙 and is closed under Σ (see the module
Dominance).

The decidable propositions form a dominance, represented by the
two-point type 𝟚 ≃ 𝟙 + 𝟙 with points ₀ and ₁ (see the module Two). A
point n : 𝟚 represents the decidable truth-value or proposition
n ≡ ₁. The natural order on 𝟚, defined by

  m ≤ n = (m ≡ ₁ → n ≡ ₁) ≃ (n ≡ ₀ → m ≡ ₀),

corresponds to the implication order (P ≤ Q = P → Q) of propositions.

Given a dominance 𝕊 and a type X, we consider the map Κ : 𝕊 → (X → 𝕊)
that sends s:𝕊 to the constant function λ x → s, and we say that

 * X is 𝕊-compact if Κ has a right adjoint A : (X → 𝕊) → 𝕊,
 * X is 𝕊-overt   if K has a left adjoint  E : (X → 𝕊) → 𝕊,

where we endow the function type (X → 𝕊) with the pointwise order. We
also say that

 * X is strongly 𝕊-overt if the composite

           d'        ∃
     (X→𝕊) →  (X→Ω)  →  Ω

   factors through the embedding d : 𝕊 ↪ Ω into the type Ω of truth
   values, where d' p = d ∘ p.

The (normal) overtness of X says that every X-indexed family of
elements of 𝕊 has a least upper bound, and the strong overtness of X
says that this coincides with the least upper bound calculated (by the
existential quantifier ∃) in Ω.

Because the dominance 𝕊=𝟚 is a boolean algebra, we get the odd fact that

 * A is 𝟚-compact iff it is 𝟚-overt.

But strong overtness is a strictly stronger notion, which corresponds
to LPO, whereas compactness and overtness correspond to WLPO. We have
that

 * X is strongly 𝟚-overt if and only if (∃ \(x : X) → p x ≡ ₀) is
   decidable for every p : X → 𝟚.

 * X is 𝟚-compact if and only if (Π \(x : X) → p x ≡ ₁) is decidable
   for every p : X → 𝟚.

We take this as our primary definition of 𝟚-compactness and then
characterize it as the existence of a right adjoint to Κ.  The above
also shows that strong 𝟚-compactness, defined as strong 𝟚-overtness
but replacing ∃ by ∀, coincides with 𝟚-compactness.

We consider various closure properties for 𝟚-compact and strongly
𝟚-overt types, their interaction with discreteness, total separatedess
and function types, and number of characterizations.

Because 𝟚-compact types are defined in terms of maps into 𝟚, a type is
𝟚-compact iff its totally separated reflection is 𝟚-compact, since
𝟚-compactness is a proposition. We also discuss the 𝟚-compactness of
propositions. The same is true for strong 𝟚-overtness.

See also the module SimpleTypes, which uses this module to study
the least collection of types containing ℕ (and sometimes 𝟚) closed
under (non-dependent) function types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import Two
open import UF-FunExt
open import UF-PropTrunc
open import UF-Retracts
open import UF-Retracts-FunExt
open import UF-ImageAndSurjection
open import UF-Equiv

module 2CompactTypes (fe : ∀ U V → funext U V)
                     (pt : PropTrunc)
                     where

open PropositionalTruncation (pt)
open import DecidableAndDetachable

\end{code}

The following is the strong notion of overtness, which is implied by
omniscience and hence by searchability (see below).  However, strong
overtness is property of a type whereas omniscience and searchability
(as we have defined them in the modules OmniscientTypes and
SearchableTypes) are structure on the type.

\begin{code}

strongly-𝟚-overt : ∀ {U} → U ̇ → U ̇
strongly-𝟚-overt X = (p : X → 𝟚) → decidable (∃ \(x : X) → p x ≡ ₀)

strongly-𝟚-overt-is-prop : ∀ {U} {X : U ̇} → is-prop (strongly-𝟚-overt X)
strongly-𝟚-overt-is-prop {U} = Π-is-prop (fe U U)
                                (λ _ → decidable-is-prop (fe U U₀) ptisp)

so-Markov : ∀ {U} {X : U ̇} → strongly-𝟚-overt X → (p : X → 𝟚)
          → ¬¬(∃ \(x : X) → p x ≡ ₀) → ∃ \(x : X) → p x ≡ ₀
so-Markov {U} {X} c p φ = g (c p)
 where
  g : decidable (∃ \(x : X) → p x ≡ ₀) → ∃ \(x : X) → p x ≡ ₀
  g (inl e) = e
  g (inr u) = 𝟘-elim (φ u)

\end{code}

The relation of strong overtness with compactness is the same as that
of LPO with WLPO.

\begin{code}

𝟚-compact : ∀ {U} → U ̇ → U ̇
𝟚-compact X = (p : X → 𝟚) → decidable ((x : X) → p x ≡ ₁)

open import UF-SetExamples

𝟚-compact-is-prop : ∀ {U} {X : U ̇} → is-prop (𝟚-compact X)
𝟚-compact-is-prop {U} = Π-is-prop (fe U U)
                         (λ _ → decidable-is-prop (fe U U₀)
                                  (Π-is-prop (fe U U₀) λ _ → 𝟚-is-set))

\end{code}

The following implication is not to be expected for dominances other than 𝟚:

\begin{code}

𝟚-so-c : ∀ {U} {X : U ̇} → strongly-𝟚-overt X → 𝟚-compact X
𝟚-so-c {U} {X} c p = f (c p)
 where
  f : decidable (∃ \(x : X) → p x ≡ ₀) → decidable (Π \(x : X) → p x ≡ ₁)
  f (inl s) = inr (λ α → ptrec 𝟘-is-prop (g α) s)
   where
    g : ((x : X) → p x ≡ ₁) → ¬ Σ \x → p x ≡ ₀
    g α (x , r) = zero-is-not-one (r ⁻¹ ∙ α x)
  f (inr u) = inl (not-exists₀-implies-forall₁ pt p u)

\end{code}

TODO. Add that finite types are strongly overt and hence compact. For
the moment we do the base case:

\begin{code}

is-empty-strongly-𝟚-overt : ∀ {U} {X : U ̇} → is-empty X → strongly-𝟚-overt X
is-empty-strongly-𝟚-overt u p = inr (ptrec 𝟘-is-prop λ σ → u (pr₁ σ))

empty-𝟚-compact : ∀ {U} {X : U ̇} → is-empty X → 𝟚-compact X
empty-𝟚-compact u p = inl (λ x → 𝟘-elim (u x))

\end{code}

The compactness of X is equivalent to the isolatedness of the boolean
predicate λ x → ₁:

\begin{code}

𝟚-compact' : ∀ {U} → U ̇ → U ̇
𝟚-compact' X = (p : X → 𝟚) → decidable (p ≡ λ x → ₁)

𝟚-compact'-is-prop : ∀ {U} {X : U ̇} → is-prop(𝟚-compact' X)
𝟚-compact'-is-prop {U} = Π-is-prop (fe U U)
                          (λ p → decidable-is-prop (fe U U₀)
                                   (Π-is-set (fe U U₀) (λ x → 𝟚-is-set)))

𝟚-c'c : ∀ {U} {X : U ̇} → 𝟚-compact' X → 𝟚-compact X
𝟚-c'c {U} {X} c' p = g (c' p)
 where
  g : decidable (p ≡ λ x → ₁) → decidable ((x : X) → p x ≡ ₁)
  g (inl r) = inl (happly r)
  g (inr u) = inr (contrapositive (dfunext (fe U U₀)) u)

𝟚-cc' : ∀ {U} {X : U ̇} → 𝟚-compact X → 𝟚-compact' X
𝟚-cc' {U} {X} c p = g (c p)
 where
  g : decidable ((x : X) → p x ≡ ₁) → decidable (p ≡ λ x → ₁)
  g (inl α) = inl (dfunext (fe U U₀) α)
  g (inr u) = inr (contrapositive happly u)

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
  φ α = (dfunext (fe U V) (λ x → pr₂ (r x) (α x)))

  γ : f ≡ g → (x : X) → p x ≡ ₁
  γ t x = Lemma[b≢₀→b≡₁] (λ u → pr₁ (r x) u (happly t x))

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

Strong overtness, and hence compactness, of omniscient sets (and hence
of searchable sets, and hence of ℕ∞, for example):

\begin{code}

open import OmniscientTypes

omniscient-Compact : ∀ {U} {X : U ̇} → omniscient X → strongly-𝟚-overt X
omniscient-Compact {U} {X} φ p = g (φ p)
 where
  g : ((Σ \(x : X) → p x ≡ ₀) + ((x : X) → p x ≡ ₁)) → decidable (∃ \(x : X) → p x ≡ ₀)
  g (inl (x , r)) = inl ∣ x , r ∣
  g (inr α) = inr (forall₁-implies-not-exists₀ pt p α)

\end{code}

But notice that the 𝟚-compactness of ℕ is (literally) WLPO.

Compactness of images:

\begin{code}

open ImageAndSurjection (pt)
open import UF-SetExamples

surjection-strongly-𝟚-overt : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                            → is-surjection f → strongly-𝟚-overt X → strongly-𝟚-overt Y
surjection-strongly-𝟚-overt {U} {V} {X} {Y} f su c q = g (c (q ∘ f))
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

image-strongly-𝟚-overt : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                       → strongly-𝟚-overt X → strongly-𝟚-overt (image f)
image-strongly-𝟚-overt f = surjection-strongly-𝟚-overt (corestriction f) (corestriction-surjection f)

surjection-𝟚-compact : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                     → is-surjection f → 𝟚-compact X → 𝟚-compact Y
surjection-𝟚-compact {U} {V} {X} {Y} f su c q = g (c (q ∘ f))
 where
  g : decidable((x : X) → q (f x) ≡ ₁) → decidable ((x : Y) → q x ≡ ₁)
  g (inl s) = inl (surjection-induction f su (λ y → q y ≡ ₁) (λ _ → 𝟚-is-set) s)
  g (inr u) = inr (contrapositive (λ φ x → φ (f x)) u)

retract-strongly-𝟚-overt : ∀ {U V} {X : U ̇} {Y : V ̇}
                         → retract Y of X → strongly-𝟚-overt X → strongly-𝟚-overt Y
retract-strongly-𝟚-overt (f , hass) = surjection-strongly-𝟚-overt f (retraction-surjection f hass)

retract-strongly-𝟚-overt' : ∀ {U V} {X : U ̇} {Y : V ̇}
                          → ∥ retract Y of X ∥ → strongly-𝟚-overt X → strongly-𝟚-overt Y
retract-strongly-𝟚-overt' t c = ptrec strongly-𝟚-overt-is-prop (λ r → retract-strongly-𝟚-overt r c) t

image-𝟚-compact : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
               → 𝟚-compact X → 𝟚-compact (image f)
image-𝟚-compact f = surjection-𝟚-compact (corestriction f) (corestriction-surjection f)

retract-𝟚-compact : ∀ {U V} {X : U ̇} {Y : V ̇}
                  → retract Y of X → 𝟚-compact X → 𝟚-compact Y
retract-𝟚-compact (f , hass) = surjection-𝟚-compact f (retraction-surjection f hass)

retract-𝟚-compact' : ∀ {U V} {X : U ̇} {Y : V ̇}
                  → ∥ retract Y of X ∥ → 𝟚-compact X → 𝟚-compact Y
retract-𝟚-compact' t c = ptrec 𝟚-compact-is-prop (λ r → retract-𝟚-compact r c) t

i2c2c : ∀ {U V} {X : U ̇} {Y : V ̇}
      → X → 𝟚-compact (X → Y) → 𝟚-compact Y
i2c2c x = retract-𝟚-compact (pdrc x)

\end{code}

A main reason to consider the notion of total separatedness is that
the totally separated reflection T X of X has the same supply of
boolean predicates as X, and hence X is strongly overt (compact) iff
T X is strongly overt (respectively compact), as we show now.

\begin{code}

open import TotallySeparated

module TStronglyOvertnessAndCompactness {U : Universe} (X : U ̇) where

 open TotallySeparatedReflection {U} fe pt

 extension : (X → 𝟚) → (T X → 𝟚)
 extension p = pr₁ (pr₁ (totally-separated-reflection 𝟚-totally-separated p))

 extension-property : (p : X → 𝟚) (x : X) → extension p (η x) ≡ p x
 extension-property p = happly (pr₂ (pr₁ (totally-separated-reflection 𝟚-totally-separated p)))

 sot : strongly-𝟚-overt X → strongly-𝟚-overt (T X)
 sot = surjection-strongly-𝟚-overt η (η-surjection)

 tos : strongly-𝟚-overt (T X) → strongly-𝟚-overt X
 tos c p = h (c (extension p))
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
[ℕ∞→𝟚]-compact-implies-WLPO c = ℕ∞-discrete-gives-WLPO (tscd (ℕ∞-totally-separated (fe U₀ U₀)) c)

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

TODO. Consider also other possible closure properties, and strong
overtness.

We now turn to propositions. A proposition is strongly overt iff it is
decidable. Regarding the compactness of propositions, we have partial
information for the moment.

\begin{code}

isod : ∀ {U} (X : U ̇) → is-prop X → strongly-𝟚-overt X → decidable X
isod X isp c = f a
 where
  a : decidable ∥ X × (₀ ≡ ₀) ∥
  a = c (λ x → ₀)

  f : decidable ∥ X × (₀ ≡ ₀) ∥ → decidable X
  f (inl s) = inl (ptrec isp pr₁ s)
  f (inr u) = inr (λ x → u ∣ x , refl ∣)

isod-corollary : ∀ {U} {X : U ̇} → strongly-𝟚-overt X → decidable ∥ X ∥
isod-corollary {U} {X} c = isod ∥ X ∥ ptisp (surjection-strongly-𝟚-overt ∣_∣ pt-is-surjection c)

isdni : ∀ {U} {X : U ̇} → strongly-𝟚-overt X → ¬¬ X → ∥ X ∥
isdni {U} {X} c φ = g (isod-corollary c)
 where
  g : decidable ∥ X ∥ → ∥ X ∥
  g (inl s) = s
  g (inr u) = 𝟘-elim (φ (λ x → u ∣ x ∣))

idso : ∀ {U} (X : U ̇) → is-prop X → decidable X → strongly-𝟚-overt X
idso X isp d p = g d
 where
  g : decidable X → decidable (∃ \x → p x ≡ ₀)
  g (inl x) = 𝟚-equality-cases b c
   where
    b : p x ≡ ₀ → decidable (∃ \x → p x ≡ ₀)
    b r = inl ∣ x , r ∣

    c : p x ≡ ₁ → decidable (∃ \x → p x ≡ ₀)
    c r = inr (ptrec (𝟘-is-prop) f)
     where
      f : ¬ Σ \y → p y ≡ ₀
      f (y , q) = zero-is-not-one (transport (λ - → p - ≡ ₀) (isp y x) q ⁻¹ ∙ r)

  g (inr u) = inr (ptrec 𝟘-is-prop (λ σ → u(pr₁ σ)))

icdn : ∀ {U} (X : U ̇) → is-prop X → 𝟚-compact X → decidable(¬ X)
icdn X isp c = f a
 where
  a : decidable (X → ₀ ≡ ₁)
  a = c (λ x → ₀)

  f : decidable (X → ₀ ≡ ₁) → decidable (¬ X)
  f (inl u) = inl (zero-is-not-one  ∘ u)
  f (inr φ) = inr λ u → φ (λ x → 𝟘-elim (u x) )

emcdn : ∀ {U} (X : U ̇) → is-prop X → 𝟚-compact(X + ¬ X) → decidable (¬ X)
emcdn X isp c = Cases a l m
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

8th Feb 2018: A pointed detachable subset of any type is a
retract. Hence any detachable (pointed or not) subset of a strongly
overt type is compact. The first construction should probably go to
another module.

\begin{code}

detachable-subset-retract : ∀ {U} {X : U ̇} {A : X → 𝟚}
  → (Σ \(x : X) → A(x) ≡ ₀) → retract (Σ \(x : X) → A(x) ≡ ₀) of X
detachable-subset-retract {U} {X} {A} (x₀ , e₀) = r , pr₁ , rs
 where
  r : X → Σ \(x : X) → A x ≡ ₀
  r x = 𝟚-equality-cases (λ(e : A x ≡ ₀) → (x , e)) (λ(e : A x ≡ ₁) → (x₀ , e₀))

  rs : (σ : Σ \(x : X) → A x ≡ ₀) → r(pr₁ σ) ≡ σ
  rs (x , e) = w
   where
    s : (b : 𝟚) → b ≡ ₀ → 𝟚-equality-cases (λ(_ : b ≡ ₀) → (x , e)) (λ(_ : b ≡ ₁) → (x₀ , e₀)) ≡ (x , e)
    s ₀ refl = refl
    s ₁ ()
    t : 𝟚-equality-cases (λ(_ : A x ≡ ₀) → x , e) (λ (_ : A x ≡ ₁) → x₀ , e₀) ≡ (x , e)
    t = s (A x) e
    u : (λ e' → x , e') ≡ (λ _ → x , e)
    u = dfunext (fe U₀ U) λ e' → ap (λ - → (x , -)) (𝟚-is-set e' e)
    v : r x ≡ 𝟚-equality-cases (λ(_ : A x ≡ ₀) → x , e) (λ (_ : A x ≡ ₁) → x₀ , e₀)
    v = ap (λ - → 𝟚-equality-cases - (λ(_ : A x ≡ ₁) → x₀ , e₀)) u
    w : r x ≡ x , e
    w = v ∙ t

\end{code}

Notice that in the above lemma we need to assume that the detachable
set is pointed. But its use below doesn't, because strong overtness
allows us to decide inhabitedness, and strong overtness is a
proposition.

\begin{code}

detachable-subset-strongly-𝟚-overt : ∀ {U} {X : U ̇} (A : X → 𝟚)
                                   → strongly-𝟚-overt X → strongly-𝟚-overt(Σ \(x : X) → A(x) ≡ ₀)
detachable-subset-strongly-𝟚-overt {U} {X} A c = g (c A)
 where
  g : decidable (∃ \(x : X) → A x ≡ ₀) → strongly-𝟚-overt(Σ \(x : X) → A(x) ≡ ₀)
  g (inl e) = retract-strongly-𝟚-overt' (ptfunct detachable-subset-retract e) c
  g (inr u) = is-empty-strongly-𝟚-overt (contrapositive ∣_∣ u)

\end{code}

For the compact case, the retraction method to prove the last theorem
is not available, but the conclusion holds, with some of the same
ingredients (and with a longer proof (is there a shorter one?)).

\begin{code}

detachable-subset-𝟚-compact : ∀ {U} {X : U ̇} (A : X → 𝟚)
                            → 𝟚-compact X → 𝟚-compact(Σ \(x : X) → A(x) ≡ ₁)
detachable-subset-𝟚-compact {U} {X} A c q = g (c p)
 where
  p₀ : (x : X) → A x ≡ ₀ → 𝟚
  p₀ x e = ₁

  p₁ : (x : X) → A x ≡ ₁ → 𝟚
  p₁ x e = q (x , e)

  p : X → 𝟚
  p x = 𝟚-equality-cases (p₀ x) (p₁ x)

  p-spec₀ : (x : X) → A x ≡ ₀ → p x ≡ ₁
  p-spec₀ x e = s (A x) e (p₁ x)
   where
    s : (b : 𝟚) → b ≡ ₀ → (f₁ : b ≡ ₁ → 𝟚)
      → 𝟚-equality-cases (λ (_ : b ≡ ₀) → ₁) f₁ ≡ ₁
    s ₀ refl = λ f₁ → refl
    s ₁ ()

  p-spec₁ : (x : X) (e : A x ≡ ₁) → p x ≡ q (x , e)
  p-spec₁ x e = u ∙ t
   where
    y : A x ≡ ₁ → 𝟚
    y _ = q (x , e)
    r : p₁ x ≡ y
    r = (dfunext (fe U₀ U₀)) (λ e' → ap (p₁ x) (𝟚-is-set e' e))
    s : (b : 𝟚) → b ≡ ₁
      → 𝟚-equality-cases (λ (_ : b ≡ ₀) → ₁) (λ (_ : b ≡ ₁) → q (x , e)) ≡ q (x , e)
    s ₀ ()
    s ₁ refl = refl
    t : 𝟚-equality-cases (p₀ x) y ≡ q (x , e)
    t = s (A x) e
    u : p x ≡ 𝟚-equality-cases (p₀ x) y
    u = ap (𝟚-equality-cases (p₀ x)) r

  g : decidable ((x : X) → p x ≡ ₁) → decidable ((σ : Σ \(x : X) → A x ≡ ₁) → q σ ≡ ₁)
  g (inl α) = inl h
   where
    h : (σ : Σ \(x : X) → A x ≡ ₁) → q σ ≡ ₁
    h (x , e) = (p-spec₁ x e) ⁻¹ ∙ α x
  g (inr u) = inr(contrapositive h u)
   where
    h : ((σ : Σ \(x : X) → A x ≡ ₁) → q σ ≡ ₁) → (x : X) → p x ≡ ₁
    h β x = 𝟚-equality-cases (p-spec₀ x) (λ e → p-spec₁ x e ∙ β (x , e))

\end{code}

20 Jan 2017

We now consider a truncated version of searchability (see the modules
SearchableTypes and OmniscientTypes).

\begin{code}

inhabited-strongly-𝟚-overt : ∀ {U} → U ̇ → U ̇
inhabited-strongly-𝟚-overt X = (p : X → 𝟚) → ∃ \(x₀ : X) → p x₀ ≡ ₁ → (x : X) → p x ≡ ₁

inhabited-strongly-𝟚-overt-is-prop : ∀ {U} {X : U ̇} → is-prop (inhabited-strongly-𝟚-overt X)
inhabited-strongly-𝟚-overt-is-prop {U} = Π-is-prop (fe U U) (λ _ → ptisp)

\end{code}

Notice that, in view of the above results, inhabitedness can be
replaced by non-emptiness in the following results:

\begin{code}

iso-i-and-c : ∀ {U} {X : U ̇} → inhabited-strongly-𝟚-overt X → ∥ X ∥ × strongly-𝟚-overt X
iso-i-and-c {U} {X} c = (ptfunct pr₁ g₁ , λ p → ptrec (decidable-is-prop (fe U U₀) ptisp) (g₂ p) (c p))
 where
  g₁ : ∥ Σ (λ x₀ → ₀ ≡ ₁ → (x : X) → ₀ ≡ ₁) ∥
  g₁ = c (λ x → ₀)

  g₂ : (p : X → 𝟚) → (Σ \(x₀ : X) → p x₀ ≡ ₁ → (x : X) → p x ≡ ₁) → decidable (∃ \(x : X) → p x ≡ ₀)
  g₂ p (x₀ , φ) = h (𝟚-discrete (p x₀) ₁)
   where
    h : decidable(p x₀ ≡ ₁) → decidable (∃ \(x : X) → p x ≡ ₀)
    h (inl r) = inr (ptrec 𝟘-is-prop f)
     where
      f : ¬ Σ \(x : X) → p x ≡ ₀
      f (x , s) = zero-is-not-one (s ⁻¹ ∙ φ r x)
    h (inr u) = inl ∣ x₀ , (Lemma[b≢₁→b≡₀] u) ∣

i-and-c-iso : ∀ {U} {X : U ̇} → ∥ X ∥ × strongly-𝟚-overt X → inhabited-strongly-𝟚-overt X
i-and-c-iso {U} {X} (t , c) p = ptrec ptisp f t
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
    g (inr _) (inr v) = ∣ x₀ , (λ _ → not-exists₀-implies-forall₁ pt p v) ∣

\end{code}

This characterizes the inhabited-strongly-𝟚-overt types as those that
are strongly-𝟚-overt and inhabited. We can also characterize the
strongly-𝟚-overt types as those that are inhabited-strongly-𝟚-overt or
empty:

\begin{code}

is-prop-isoore : ∀ {U} {X : U ̇} → is-prop(inhabited-strongly-𝟚-overt X + is-empty X)
is-prop-isoore {U} {X} = sum-of-contradictory-props
                           inhabited-strongly-𝟚-overt-is-prop
                             (Π-is-prop (fe U U₀) (λ _ → 𝟘-is-prop))
                                (λ c u → ptrec 𝟘-is-prop (contrapositive pr₁ u) (c (λ _ → ₀)))

isoore-so : ∀ {U} {X : U ̇} → inhabited-strongly-𝟚-overt X + is-empty X → strongly-𝟚-overt X
isoore-so (inl c) = pr₂(iso-i-and-c c)
isoore-so (inr u) = is-empty-strongly-𝟚-overt u

so-isoore : ∀ {U} {X : U ̇} → strongly-𝟚-overt X → inhabited-strongly-𝟚-overt X + is-empty X
so-isoore {U} {X} c = g
 where
  h : decidable (∃ \(x : X) → ₀ ≡ ₀) → inhabited-strongly-𝟚-overt X + is-empty X
  h (inl t) = inl (i-and-c-iso (ptfunct pr₁ t , c))
  h (inr u) = inr (contrapositive (λ x → ∣ x , refl ∣) u)

  g : inhabited-strongly-𝟚-overt X + is-empty X
  g = h (c (λ _ → ₀))

\end{code}

8 Feb 2018: A type X is 𝟚-compact iff every map X → 𝟚 has an infimum:

\begin{code}

_has-inf_ : ∀ {U} {X : U ̇} → (X → 𝟚) → 𝟚 → U ̇
p has-inf n = (∀ x → n ≤₂ p x) × (∀ m → (∀ x → m ≤₂ p x) → m ≤₂ n)

has-inf-is-prop : ∀ {U} {X : U ̇} (p : X → 𝟚) (n : 𝟚) → is-prop(p has-inf n)
has-inf-is-prop {U} {X} p n (f , g) (f' , g') = ×-≡ r s
 where
  r : f ≡ f'
  r = dfunext (fe U U₀) (λ x → dfunext (fe U₀ U₀) (λ r → 𝟚-is-set (f x r) (f' x r)))
  s : g ≡ g'
  s = dfunext (fe U₀ U) (λ n → dfunext (fe U U₀) (λ φ → dfunext (fe U₀ U₀) (λ r → 𝟚-is-set (g n φ r) (g' n φ r))))

at-most-one-inf : ∀ {U} {X : U ̇} (p : X → 𝟚) → is-prop (Σ \(n : 𝟚) → p has-inf n)
at-most-one-inf p (n , f , g) (n' , f' , g') = to-Σ-≡ (≤₂-anti (g' n f) (g n' f') , has-inf-is-prop p n' _ _)

has-infs : ∀ {U} → U ̇ → U ̇
has-infs X = ∀(p : X → 𝟚) → Σ \(n : 𝟚) → p has-inf n

has-infs-is-prop : ∀ {U} {X : U ̇} → is-prop(has-infs X)
has-infs-is-prop {U} {X} = Π-is-prop (fe U U) at-most-one-inf

𝟚-compact-has-infs : ∀ {U} {X : U ̇} → 𝟚-compact X → has-infs X
𝟚-compact-has-infs c p = g (c p)
 where
  g : decidable (∀ x → p x ≡ ₁) → Σ \(n : 𝟚) → p has-inf n
  g (inl α) = ₁ , (λ x _ → α x) , λ m _ → ₁-top
  g (inr u) = ₀ , (λ _ → ₀-bottom) , h
   where
    h : (m : 𝟚) → (∀ x → m ≤₂ p x) → m ≤₂ ₀
    h _ φ r = 𝟘-elim (u α)
     where
      α : ∀ x → p x ≡ ₁
      α x = φ x r

has-infs-𝟚-compact : ∀ {U} {X : U ̇} → has-infs X → 𝟚-compact X
has-infs-𝟚-compact h p = f (h p)
 where
  f : (Σ \(n : 𝟚) → p has-inf n) → decidable (∀ x → p x ≡ ₁)
  f (₀ , _ , h) = inr u
   where
    u : ¬ ∀ x → p x ≡ ₁
    u α = zero-is-not-one (h ₁ (λ x r → α x) refl)
  f (₁ , g , _) = inl α
   where
    α : ∀ x → p x ≡ ₁
    α x = g x refl

\end{code}

TODO. Show equivalence with existence of suprema. Is there a similar
characterization of strong overtness?

Implicit application of type-theoretical choice:

\begin{code}

inf : ∀ {U} {X : U ̇} → 𝟚-compact X → (X → 𝟚) → 𝟚
inf c p = pr₁(𝟚-compact-has-infs c p)

inf-property : ∀ {U} {X : U ̇} → (c : 𝟚-compact X) (p : X → 𝟚) → p has-inf (inf c p)
inf-property c p = pr₂(𝟚-compact-has-infs c p)

inf₁ : ∀ {U} {X : U ̇} (c : 𝟚-compact X) {p : X → 𝟚}
     → inf c p ≡ ₁ → ∀ x → p x ≡ ₁
inf₁ c {p} r x = pr₁(inf-property c p) x r

inf₁-converse : ∀ {U} {X : U ̇} (c : 𝟚-compact X) {p : X → 𝟚}
              → (∀ x → p x ≡ ₁) → inf c p ≡ ₁
inf₁-converse c {p} α = ₁-maximal (h g)
 where
  h : (∀ x → ₁ ≤₂ p x) → ₁ ≤₂ inf c p
  h = pr₂(inf-property c p) ₁
  g : ∀ x → ₁ ≤₂ p x
  g x _ = α x

\end{code}

21 Feb 2018.

It is well known that infima and suprema are characterized as
adjoints. TODO. Link the above development with the following (easy).

In synthetic topology with the dominance 𝟚, a type is called 𝟚-compact
if the map Κ : 𝟚 → (X → 𝟚) has a right adjoint A : (X → 𝟚) → 𝟚, with
respect to the natural ordering of 𝟚 and the pointwise order of the
function type (X → 𝟚), and 𝟚-overt if it has a left-adjoint
E : (X → 𝟚) → 𝟚.

Κ is the usual combinator (written Kappa rather than Kay here):

\begin{code}

Κ : ∀ {U V} {X : U ̇} {Y : V ̇} → Y → (X → Y)
Κ y x = y

\end{code}

The pointwise order on boolean predicates:

\begin{code}

_≤̇_ : ∀ {U} {X : U ̇} → (X → 𝟚) → (X → 𝟚) → U ̇
p ≤̇ q = ∀ x → p x ≤₂ q x

\end{code}

We define adjunctions in the two special cases where one of the sides
is Κ with Y=𝟚, for simplicity, rather than in full generality:

\begin{code}

Κ⊣ : ∀ {U} {X : U ̇} → ((X → 𝟚) → 𝟚) → U ̇
Κ⊣ A = (n : 𝟚) (p : _ → 𝟚) → Κ n ≤̇ p ⇔ n ≤₂ A p

_⊣Κ : ∀ {U} {X : U ̇} → ((X → 𝟚) → 𝟚) → U ̇
E ⊣Κ = (n : 𝟚) (p : _ → 𝟚) → E p ≤₂ n ⇔ p ≤̇ Κ n

\end{code}

TODO: The types Κ⊣ A and E ⊣Κ are propositions, and so are the types
Σ \A → Κ⊣ A (compactness) and Σ \E → E ⊣Κ (overtness).

Right adjoints to Κ are characterized as follows:

\begin{code}

Κ⊣-charac : ∀ {U} {X : U ̇} → (A : (X → 𝟚) → 𝟚)
           → Κ⊣ A ⇔ ((p : X → 𝟚) → A p ≡ ₁ ⇔ p ≡ (λ x → ₁))
Κ⊣-charac {U} {X} A = f , g
 where
  f : Κ⊣ A → (p : X → 𝟚) → A p ≡ ₁ ⇔ p ≡ (λ x → ₁)
  f φ p = f₀ , f₁
   where
    f₀ : A p ≡ ₁ → p ≡ (λ x → ₁)
    f₀ r = dfunext (fe U U₀) l₃
     where
      l₀ : ₁ ≤₂ A p → Κ ₁ ≤̇ p
      l₀ = pr₂ (φ ₁ p)
      l₁ : Κ ₁ ≤̇ p
      l₁ = l₀ (λ _ → r)
      l₂ : (x : X) → ₁ ≤₂ p x
      l₂ = l₁
      l₃ : (x : X) → p x ≡ ₁
      l₃ x = l₂ x refl

    f₁ : p ≡ (λ x → ₁) → A p ≡ ₁
    f₁ s = l₀ refl
     where
      l₃ : (x : X) → p x ≡ ₁
      l₃ = happly s
      l₂ : (x : X) → ₁ ≤₂ p x
      l₂ x _ = l₃ x
      l₁ : Κ ₁ ≤̇ p
      l₁ = l₂
      l₀ : ₁ ≤₂ A p
      l₀ = pr₁ (φ ₁ p) l₁

  g : ((p : X → 𝟚) → A p ≡ ₁ ⇔ p ≡ (λ x → ₁)) → Κ⊣ A
  g γ n p = (g₀ n refl , g₁ n refl)
   where
    g₀ : ∀ m → m ≡ n → Κ m ≤̇ p → m ≤₂ A p
    g₀ ₀ r l ()
    g₀ ₁ refl l refl = pr₂ (γ p) l₁
     where
      l₀ : (x : X) → p x ≡ ₁
      l₀ x = l x refl
      l₁ : p ≡ (λ x → ₁)
      l₁ = dfunext (fe U U₀) l₀

    g₁ : ∀ m → m ≡ n → m ≤₂ A p → Κ m ≤̇ p
    g₁ ₀ r l x ()
    g₁ ₁ refl l x refl = l₀ x
     where
      l₁ : p ≡ (λ x → ₁)
      l₁ = pr₁ (γ p) (l refl)
      l₀ : (x : X) → p x ≡ ₁
      l₀ = happly l₁

\end{code}

Using this as a lemma, we see that a type is 𝟚-compact in the sense we
defined iff it is compact in the usual sense of synthetic topology for
the dominance 𝟚.

\begin{code}

𝟚-compact-iff-Κ-has-right-adjoint : ∀ {U} {X : U ̇}
                                  → 𝟚-compact X ⇔ (Σ \(A : (X → 𝟚) → 𝟚) → Κ⊣ A)
𝟚-compact-iff-Κ-has-right-adjoint {U} {X} = (f , g)
 where
  f : 𝟚-compact X → Σ \(A : (X → 𝟚) → 𝟚) → Κ⊣ A
  f c = (A , pr₂ (Κ⊣-charac A) l₁)
   where
    c' : (p : X → 𝟚) → decidable (p ≡ (λ x → ₁))
    c' = 𝟚-cc' c
    l₀ : (p : X → 𝟚) → decidable (p ≡ (λ x → ₁)) → Σ \(n : 𝟚) → n ≡ ₁ ⇔ p ≡ (λ x → ₁)
    l₀ p (inl r) = (₁ , ((λ _ → r) , λ _ → refl))
    l₀ p (inr u) = (₀ , ((λ s → 𝟘-elim (zero-is-not-one s)) , λ r → 𝟘-elim (u r)))
    A : (X → 𝟚) → 𝟚
    A p = pr₁(l₀ p (c' p))
    l₁ : (p : X → 𝟚) → A p ≡ ₁ ⇔ p ≡ (λ x → ₁)
    l₁ p = pr₂(l₀ p (c' p))

  g : ((Σ \(A : (X → 𝟚) → 𝟚) → Κ⊣ A)) → 𝟚-compact X
  g (A , φ) = 𝟚-c'c c'
   where
    l₁ : (p : X → 𝟚) → A p ≡ ₁ ⇔ p ≡ (λ x → ₁)
    l₁ = pr₁ (Κ⊣-charac A) φ
    l₀ : (p : X → 𝟚) → decidable(A p ≡ ₁) → decidable (p ≡ (λ x → ₁))
    l₀ p (inl r) = inl (pr₁ (l₁ p) r)
    l₀ p (inr u) = inr (contrapositive (pr₂ (l₁ p)) u)
    c' : (p : X → 𝟚) → decidable (p ≡ (λ x → ₁))
    c' p = l₀ p (𝟚-discrete (A p) ₁)

\end{code}

Next we show that κ has a right adjoint iff it has a left adjoint,
namely its De Morgan dual, which exists because 𝟚 is a boolean algebra
and hence so is the type (X → 𝟚) with the pointwise operations.

\begin{code}

𝟚-DeMorgan-dual : ∀ {U} {X : U ̇} → ((X → 𝟚) → 𝟚) → ((X → 𝟚) → 𝟚)
𝟚-DeMorgan-dual φ = λ p → complement(φ(λ x → complement(p x)))

𝟚-DeMorgan-dual-involutive : ∀ {U} → {X : U ̇} → (φ : (X → 𝟚) → 𝟚)
                           → 𝟚-DeMorgan-dual(𝟚-DeMorgan-dual φ) ≡ φ
𝟚-DeMorgan-dual-involutive {U} φ = dfunext (fe U U₀) h
 where
  f : ∀ p → complement (complement (φ (λ x → complement (complement (p x)))))
          ≡ φ (λ x → complement (complement (p x)))
  f p = complement-involutive (φ (λ x → complement (complement (p x))))

  g : ∀ p → φ (λ x → complement (complement (p x))) ≡ φ p
  g p = ap φ (dfunext (fe U U₀) (λ x → complement-involutive (p x)))

  h : ∀ p → 𝟚-DeMorgan-dual(𝟚-DeMorgan-dual φ) p ≡ φ p
  h p = f p ∙ g p

𝟚-compact-is-𝟚-overt : ∀ {U} {X : U ̇} → (A : (X → 𝟚) → 𝟚)
                      → Κ⊣ A → (𝟚-DeMorgan-dual A) ⊣Κ
𝟚-compact-is-𝟚-overt {U} {X} A = f
 where
  E : (X → 𝟚) → 𝟚
  E = 𝟚-DeMorgan-dual A
  f : Κ⊣ A → E ⊣Κ
  f φ = γ
   where
     γ : (n : 𝟚) (p : X → 𝟚) → (E p ≤₂ n) ⇔ (p ≤̇ Κ n)
     γ n p = (γ₀ , γ₁ )
      where
       γ₀ : E p ≤₂ n → p ≤̇ Κ n
       γ₀ l = m₃
        where
         m₀ : complement n ≤₂ A (λ x → complement (p x))
         m₀ = complement-left l
         m₁ : Κ (complement n) ≤̇ (λ x → complement (p x))
         m₁ = pr₂ (φ (complement n) (λ x → complement (p x))) m₀
         m₂ : (x : X) → complement n ≤₂ complement (p x)
         m₂ = m₁
         m₃ : (x : X) → p x ≤₂ n
         m₃ x = complement-both-left (m₂ x)

       γ₁ : p ≤̇ Κ n → E p ≤₂ n
       γ₁ l = complement-left m₀
        where
         m₃ : (x : X) → p x ≤₂ n
         m₃ = l
         m₂ : (x : X) → complement n ≤₂ complement (p x)
         m₂ x = complement-both-right (m₃ x)
         m₁ : Κ (complement n) ≤̇ (λ x → complement (p x))
         m₁ = m₂
         m₀ : complement n ≤₂ A (λ x → complement (p x))
         m₀ = pr₁ (φ (complement n) (λ x → complement (p x))) m₁

𝟚-overt-is-𝟚-compact : ∀ {U} {X : U ̇} → (E : (X → 𝟚) → 𝟚)
                     → E ⊣Κ → Κ⊣ (𝟚-DeMorgan-dual E)
𝟚-overt-is-𝟚-compact {U} {X} E = g
 where
  A : (X → 𝟚) → 𝟚
  A = 𝟚-DeMorgan-dual E
  g : E ⊣Κ → Κ⊣ A
  g γ = φ
   where
     φ : (n : 𝟚) (p : X → 𝟚) → Κ n ≤̇ p ⇔ n ≤₂ A p
     φ n p = (φ₀ , φ₁ )
      where
       φ₀ : Κ n ≤̇ p → n ≤₂ A p
       φ₀ l = complement-right m₀
        where
         m₃ : (x : X) → n ≤₂ p x
         m₃ = l
         m₂ : (x : X) → complement (p x) ≤₂ complement n
         m₂ x = complement-both-right (m₃ x)
         m₁ : (λ x → complement (p x)) ≤̇ Κ (complement n)
         m₁ = m₂
         m₀ : E (λ x → complement (p x)) ≤₂ complement n
         m₀ = pr₂ (γ (complement n) (λ x → complement (p x))) m₂

       φ₁ : n ≤₂ A p → Κ n ≤̇ p
       φ₁ l = m₃
        where
         m₀ : E (λ x → complement (p x)) ≤₂ complement n
         m₀ = complement-right l
         m₁ : (λ x → complement (p x)) ≤̇ Κ (complement n)
         m₁ = pr₁ (γ (complement n) (λ x → complement (p x))) m₀
         m₂ : (x : X) → complement (p x) ≤₂ complement n
         m₂ = m₁
         m₃ : (x : X) → n ≤₂ p x
         m₃ x = complement-both-left (m₂ x)

\end{code}

We have the following corollaries:

\begin{code}

𝟚-compact-iff-𝟚-overt : ∀ {U} {X : U ̇}
                      → (Σ \(A : (X → 𝟚) → 𝟚) → Κ⊣ A) ⇔ (Σ \(E : (X → 𝟚) → 𝟚) → E ⊣Κ)
𝟚-compact-iff-𝟚-overt {U} {X} = (f , g)
 where
  f : (Σ \(A : (X → 𝟚) → 𝟚) → Κ⊣ A) → (Σ \(E : (X → 𝟚) → 𝟚) → E ⊣Κ)
  f (A , φ) = (𝟚-DeMorgan-dual A , 𝟚-compact-is-𝟚-overt A φ)

  g : (Σ \(E : (X → 𝟚) → 𝟚) → E ⊣Κ) → (Σ \(A : (X → 𝟚) → 𝟚) → Κ⊣ A)
  g (E , γ) = (𝟚-DeMorgan-dual E , 𝟚-overt-is-𝟚-compact E γ)

\end{code}

In this corollary we record explicitly that a type is 𝟚-compact iff it
is 𝟚-overt:

\begin{code}

𝟚-compact-iff-Κ-has-left-adjoint : ∀ {U} {X : U ̇}
                                 → 𝟚-compact X ⇔ (Σ \(E : (X → 𝟚) → 𝟚) → E ⊣Κ)
𝟚-compact-iff-Κ-has-left-adjoint {U} {X} = (f , g)
 where
  f : 𝟚-compact X → (Σ \(E : (X → 𝟚) → 𝟚) → E ⊣Κ)
  f c = pr₁ 𝟚-compact-iff-𝟚-overt (pr₁ 𝟚-compact-iff-Κ-has-right-adjoint c)

  g : (Σ \(E : (X → 𝟚) → 𝟚) → E ⊣Κ) → 𝟚-compact X
  g o = pr₂ 𝟚-compact-iff-Κ-has-right-adjoint (pr₂ 𝟚-compact-iff-𝟚-overt o)

\end{code}

TODO. We get as a corollary that

      E ⊣Κ ⇔ ((p : X → 𝟚) → E p ≡ ₀ ⇔ p ≡ (λ x → ₀)).

TODO. Find the appropriate place in this file to remark that decidable
propositions are closed under 𝟚-compact/overt meets and joins. And
then clopen sets (or 𝟚-open sets, or complemented subsets) are closed
under 𝟚-compact/over unions and intersections.

20 Feb 2018. In classical topology, a space X is compact iff the
projection A × X → A is a closed map for every space A, meaning that
the image of every closed set is closed. In our case, because of the
use of decidable truth-values in the definition of 𝟚-compactness, the
appropriate notion is that of clopen map, that is, a map that sends
clopen sets to clopen sets. As in our setup, clopen sets correspond to
decidable subsets, or sets with 𝟚-valued characteristic functions. In
our case, the clopeness of the projections characterize the notion of
strong overtness, which is stronger than compactness.

There is a certain asymmetry in the following definition, in that the
input decidable predicate (or clopen subtype) is given as a 𝟚-valued
function, whereas instead of saying that the image predicate factors
through the embedding 𝟚 of into the type of truth values, we say that
it has decidable truth-values, which is equivalent. Such an asymmetry
is already present in our formulation of the notion of compactness.

We have defined image with lower case in the module UF. We now need
Images with upper case:

\begin{code}

Image : ∀ {U V W} {X : U ̇} {Y : V ̇}
     → (X → Y) → (X → W ̇) → (Y → U ⊔ V ⊔ W ̇)
Image f A = λ y → ∃ \x → A x × (f x ≡ y)

is-clopen-map : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
is-clopen-map {U} {V} {X} {Y} f = (p : X → 𝟚) (y : Y)
                              → decidable (Image f (λ x → p x ≡ ₀) y)

is-clopen-map-is-prop : ∀ {U V} {X : U ̇} {Y : V ̇} → (∀ U V → funext U V)
                   → (f : X → Y) → is-prop(is-clopen-map f)
is-clopen-map-is-prop {U} {V} fe f = Π-is-prop (fe U (U ⊔ V))
                                      (λ p → Π-is-prop (fe V (U ⊔ V))
                                               (λ y → decidable-is-prop (fe (U ⊔ V) U₀) ptisp))

fst : ∀ {U V} (A : U ̇) (X : V ̇) → A × X → A
fst _ _ = pr₁

strongly-𝟚-overt-clopen-projections : ∀ {U} (X : U ̇)
                                    → strongly-𝟚-overt X
                                    → (∀ {V} (A : V ̇) → is-clopen-map(fst A X))
strongly-𝟚-overt-clopen-projections X c A p a = g (c (λ x → p (a , x)))
 where
  g : decidable (∃ \(x : X) → p (a , x) ≡ ₀)
    → decidable (∃ \(z : A × X) → (p z ≡ ₀) × (pr₁ z ≡ a))
  g (inl e) = inl ((ptfunct h) e)
   where
    h : (Σ \(x : X) → p (a , x) ≡ ₀) → Σ \(z : A × X) → (p z ≡ ₀) × (pr₁ z ≡ a)
    h (x , r) =  (a , x) , (r , refl)
  g (inr u) = inr (contrapositive (ptfunct h) u)
   where
    h : (Σ \(z : A × X) → (p z ≡ ₀) × (pr₁ z ≡ a)) → Σ \(x : X) → p (a , x) ≡ ₀
    h ((a' , x) , (r , s)) = x , transport (λ - → p (- , x) ≡ ₀) s r

clopen-projections-strongly-𝟚-overt : ∀ {U W} (X : U ̇)
                                    → (∀ {V} (A : V ̇) → is-clopen-map(fst A X))
                                    → strongly-𝟚-overt X
clopen-projections-strongly-𝟚-overt {U} {W} X κ p = g (κ 𝟙 (λ z → p(pr₂ z)) *)
 where
  g : decidable (∃ \(z : 𝟙 {W} × X) → (p (pr₂ z) ≡ ₀) × (pr₁ z ≡ *))
    → decidable (∃ \(x : X) → p x ≡ ₀)
  g (inl e) = inl (ptfunct h e)
   where
    h : (Σ \(z : 𝟙 × X) → (p (pr₂ z) ≡ ₀) × (pr₁ z ≡ *)) → Σ \(x : X) → p x ≡ ₀
    h ((* , x) , r , _) = x , r
  g (inr u) = inr(contrapositive (ptfunct h) u)
   where
    h : (Σ \(x : X) → p x ≡ ₀) → Σ \(z : 𝟙 × X) → (p (pr₂ z) ≡ ₀) × (pr₁ z ≡ *)
    h (x , r) = (* , x) , (r , refl)


\end{code}

TODO.

* Consider 𝟚-perfect maps.

* Strong overtness: attainability of minima. Existence of potential
  maxima.

* Relation of 𝟚-compactness with finiteness and discreteness.

* Non-classical cotaboos Every 𝟚-compact subtype of ℕ is finite. Every
  𝟚-compact subtype of a discrete type is finite. What are the
  cotaboos necessary (and sufficient) to prove that the type of
  decidable subsingletons of ℕ∞→ℕ is 𝟚-compact?  Continuity principles
  are enough.

* 𝟚-subspace: e:X→Y such that every clopen X→𝟚 extends to some clopen
  Y→𝟚 (formulated with Σ and ∃). Or to a largest such clopen, or a
  smallest such clopen (right and left adjoints to the restriction map
  (Y→𝟚)→(X→𝟚) that maps v to v ∘ e and could be written e ⁻¹[ v ].  A
  𝟚-subspace-embedding of totally separated types should be a
  (homotopy) embedding, but not conversely (find a counter-example).

* 𝟚-injective types (injectives wrt to 𝟚-subspace-embeddigs). They
  should be the retracts of powers of 𝟚. Try to characterize them
  "intrinsically".

* Relation of 𝟚-subspaces with 𝟚-compact subtypes.

* 𝟚-Hofmann-Mislove theorem: clopen filters of clopens should
  correspond to 𝟚-compact (𝟚-saturated) 𝟚-subspaces. Are cotaboos
  needed for this?

* Which results here depend on the particular dominance 𝟚, and which
  ones generalize to any dominance, or to any "suitable" dominance? In
  particular, it is of interest to generalize this to "Sierpinki like"
  dominances. And what is "Sierpinski like" in precise (internal)
  terms? This should be formulated in terms of cotaboos.
