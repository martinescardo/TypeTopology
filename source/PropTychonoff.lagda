Martin Escardo 29 April 2014.

A prop-indexed product of searchable sets is itself searchable. But
the assumption that a prop-indexed product of omniscient sets is
omniscient gives weak excluded middle (negative propositions are
decidable).

The definition of the searchability of a type A is

    searchable A = (p : A → 𝟚) → Σ \(a₀ : A) → p a₀ ≡ ₁ → (a : A) → p a ≡ ₁

With excluded middle for propositions, the above claim is not
surprising, because

    (𝟘 → Y) = Y^𝟘 ≃ 𝟙 (which is always searchable),
    (𝟙 → Y) = Y^𝟙 ≃ Y (which is searchable if Y is),

and excluded middle for a proposition X amounts to X=𝟘 or X=𝟙, so
that 

    Y^X is searchable if Y is searchable and X is a proposition.
    
The point is that

    (1) We can reach this conclusion without excluded middle.

    (2) This also holds for dependent products:

        Π(x:X).Y x is searchable if X is a proposition and Y x is
        searchable for every x:X.

        (This product is written (x : X) → Y x or Π Y in Agda.)

Our Agda proof below can be written rather concisely by expanding the
definitions. We deliberately don't do that, so that we have a rigorous
informal proof side-by-side with the formal proof. We proceed in a
series of trivial steps, hopefully in the most natural way (although
we had a convoluted path to this supposedly natural way).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} 

open import SpartanMLTT
open import UF-FunExt

module PropTychonoff (fe : ∀ U V → FunExt U V) where

open import UF-Base
open import UF-Subsingletons
open import UF-PropIndexedPiSigma
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-Two-Prop-Density
open import Two
open import SearchableTypes

\end{code}

A crucial lemma is 

    prop-indexed-product : isProp X → (a : X) → Π Y ≅ Y a

This is proved in the module Prop-indexed-product. Although it has a
subtle proof, it should be intuitively clear, as X has at most one
element by hypothesis, and if the element is a:X then the product Π Y
should be isomorphic to its only factor Y a. 

With this observation, the following proof should be self-contained,
if we recall again the definition of searchable set from the module
Searchable:

    searchable A = (p : A → 𝟚) → Σ \(a₀ : A) → p a₀ ≡ ₁ → (a : A) → p a ≡ ₁

Recall also that such an a₀ is called a universal witness for the predicate p.

\begin{code}

prop-tychonoff : ∀ {U V} {X : U ̇} {Y : X → V ̇} → isProp X 
               → ((x : X) → searchable(Y x)) → searchable(Π Y)
prop-tychonoff {U} {V} {X} {Y} hp ε p = φ₀ , φ₀-is-universal-witness 
 where
  -- hp : isProp X
  --  ε : (x : X) → searchable(Y x)
  --  p : Π Y → 𝟚

  hip : (x : X) → Π Y ≃ Y x
  hip = prop-indexed-product (fe U V) hp

  -- The essence of the first part of the proof is this:
  not-useful : X → searchable(Π Y)
  not-useful x = equiv-searchable (≃-sym(hip x)) (ε x)
  -- But this is very crude for our purposes (or so it seems). 
  -- So we instead proceed as follows.

  -- The following is what we get from prop-indexed-product, abstractly:
  f : (x : X) → Π Y → Y x
  f x = pr₁(hip x)

  hrf : (x : X) → Σ \(r : Y x → Π Y) → r ∘ f x ∼ id
  hrf x = pr₂(pr₂(hip x))

  h : (x : X) → Y x → Π Y
  h x = pr₁(hrf x)

  hf : (x : X) (φ : Π Y) → h x (f x φ) ≡ φ
  hf x = pr₂(hrf x)

  -- We define a predicate q x: Y x → 𝟚, for each x:X, from the
  -- predicate p:Π Y→𝟚 via (part of) the above isomorphism:
  q : (x : X) → Y x → 𝟚
  q x y = p(h x y)

  -- We argue that the following is a universal witness for the
  -- searchability of the type Π Y wrt the predicate p:
  φ₀ : Π Y
  φ₀ x = pr₁(ε x (q x))

  -- By hypothesis, it satisfies: 
  φ₀-spec : (x : X) → q x (φ₀ x) ≡ ₁ → (y : Y x) → q x y ≡ ₁
  φ₀-spec x = pr₂(ε x (q x)) 

  -- By expanding the definitions, this amounts to:
  φ₀-spec₀ : (x : X) → p(h x (φ₀ x)) ≡ ₁ → (y : Y x) → p(h x y) ≡ ₁
  φ₀-spec₀ = φ₀-spec

  -- By the definition of f in prop-indexed-product (namely f x φ = φ x):
  φ₀-spec₁ : (x : X) → p(h x (f x φ₀)) ≡ ₁ → (y : Y x) → p(h x y) ≡ ₁
  φ₀-spec₁ = φ₀-spec₀
  -- (So we can't abstract away the definition/proof of
  --  prop-indexed-product.)

  -- In particular, with y = f x φ, we get:
  φ₀-spec₁-particular-case : (x : X) → p(h x (f x φ₀)) ≡ ₁ → (φ : Π Y) → p(h x (f x φ)) ≡ ₁
  φ₀-spec₁-particular-case x r φ = φ₀-spec₁ x r (f x φ)

  -- Using the fact that g x (f x φ) = φ for any x:X, we get:
  φ₀-is-universal-witness-assuming-X : X → p φ₀ ≡ ₁ → (φ : Π Y) → p φ ≡ ₁
  φ₀-is-universal-witness-assuming-X x r φ = 
     ap p ((hf x φ)⁻¹) ∙ φ₀-spec₁-particular-case x (ap p (hf x φ₀) ∙ r) φ
  -- Notice that the point x:X vanishes from the conclusion, and so we
  -- are able to omit it from the hypothesis, which is crucial for
  -- what follows.

  -- We get the same conclusion if X is empty:
  φ₀-is-universal-witness-assuming-X→𝟘 : (X → 𝟘) → p φ₀ ≡ ₁ → (φ : Π Y) → p φ ≡ ₁
  φ₀-is-universal-witness-assuming-X→𝟘 u r φ = ap p claim ∙ r 
   where
    claim : φ ≡ φ₀
    claim = funext (fe U V) (λ x → unique-from-𝟘(u x))

  -- So we would get what we want if we had excluded middle, because
  -- the above shows that both X and X→𝟘 give the desired conclusion
  -- that φ₀ is a universal witness. But excluded middle is not needed.

  -- We shuffle the arguments of φ₀-is-universal-witness-assuming-X:
  claim₀ : p φ₀ ≡ ₁ → (φ : Π Y) → X → p φ ≡ ₁
  claim₀ r φ x = φ₀-is-universal-witness-assuming-X x r φ

  -- We then take the contra-positive of the conclusion X → p φ ≡ ₁,
  -- and use the fact that if a point of the two-point type 𝟚 is ₀,
  -- then it is not ₁:
  Claim₁ : p φ₀ ≡ ₁ → (φ : Π Y) → p φ ≡ ₀ → (X → 𝟘)
  Claim₁ r φ = contrapositive(claim₀ r φ) ∘ Lemma[b≡₀→b≢₁]
  -- This concludes the first part of the argument.

  -- We now shuffle the arguments of φ₀-is-universal-witness-assuming-X→𝟘:
  Claim₂ : p φ₀ ≡ ₁ → (φ : Π Y) → (X → 𝟘) → p φ ≡ ₁
  Claim₂ r φ u = φ₀-is-universal-witness-assuming-X→𝟘 u r φ

  -- Combining the two last claims, we get:
  Claim₃ : p φ₀ ≡ ₁ → (φ : Π Y) → p φ ≡ ₀ → p φ ≡ ₁
  Claim₃ r φ = Claim₂ r φ ∘ Claim₁ r φ

  -- Finally, we do case analysis on the value of p φ:
  φ₀-is-universal-witness : p φ₀ ≡ ₁ → (φ : Π Y) → p φ ≡ ₁
  φ₀-is-universal-witness r φ = two-equality-cases (Claim₃ r φ) id

\end{code}

And we are done. (9 Sep 2015: We can generalize from X being a
subsingleton (a proposition) to X being subfinite (embedded into a
finite type).)

A particular case is the following:

\begin{code}

prop-tychonoff-corollary : ∀ {U V} {X : U ̇} {Y : V ̇} → isProp X 
                        → searchable Y → searchable(X → Y)
prop-tychonoff-corollary hp ε = prop-tychonoff hp (λ x → ε)

\end{code}

This holds even for undecided X (such as X=LPO), or when we have no
idea whether X or (X→𝟘), and hence whether (X→Y) is 1 or Y (or none,
if this is undecided)!

Better (9 Sep 2015):

\begin{code}

prop-tychonoff-corollary' : ∀ {U V } {X : U ̇} {Y : V ̇} → isProp X 
                          → (X → searchable Y) → searchable(X → Y)
prop-tychonoff-corollary' hp ε = prop-tychonoff hp ε

\end{code}

So the type (LPO → ℕ) is searchable! (See the module LPO for a proof.)

The Tychonoff theorem for prop-indexed products of omniscient types
doesn't hold. To see this, first notice that a proposition is
omniscient iff it is decidable. Now, the empty type 𝟘 is omniscient
(but not searchable), and if 𝟘^P, that is, ¬P, where omniscient for a
proposition P, this would imply that ¬P is decidable for every
proposition P, which is weak excluded middle, which is not provable.

\begin{code}

open import OmniscientTypes

omniscient-prop-tychonoff-wem : 
  ((X : U₀ ̇) (Y : X → U₀ ̇) → isProp X → ((x : X) → omniscient(Y x)) → omniscient(Π Y))
  → WEM U₀
omniscient-prop-tychonoff-wem τ P isp = omniscient-decidable (¬ P) ¬P-omniscient
 where
  ¬P-omniscient : omniscient (¬ P)
  ¬P-omniscient = τ P (λ p → 𝟘) isp (λ p → 𝟘-omniscient)
              
\end{code}
