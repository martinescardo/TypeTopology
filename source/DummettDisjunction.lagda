Dummett disjunction in Martin-Lӧf Type Theory

Martín Escardó, 31 March 2016, updated 1st April 2016.
Last updated 6 Sep 2016 with the addition of weak Dummet disjunction.

We consider the behaviour of what we call "Dummett disjunction" in
intuitionistic logic in its MLTT rendering in Agda notation. (A
motivation coming from univalent type theory is discussed at the end.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module DummettDisjunction where

open import SpartanMLTT


_⊞_ : Set → Set → Set
P ⊞ Q = ((P → Q) → Q) × ((Q → P) → P)

inL : (P Q : Set) → P → P ⊞ Q
inL P Q p = (λ u → u p) , (λ _ → p)

inR : (P Q : Set) → Q → P ⊞ Q
inR P Q q = (λ _ → q) , (λ v → v q)

\end{code}

Dummett disjunction _⊞_ weakens intuitionistic disjunction _+_:

\begin{code}

weaker-than-intuitionistic : (P Q : Set) → P + Q → P ⊞ Q
weaker-than-intuitionistic P Q (inl p) = inL P Q p
weaker-than-intuitionistic P Q (inr q) = inR P Q q

\end{code}

and strengthens classical disjunction:

\begin{code}

stronger-than-classical : (P Q : Set) → P ⊞ Q → ¬ (¬ P × ¬ Q)
stronger-than-classical P Q = more-generally 𝟘 𝟘-elim
  where
    more-generally : (R : Set) → (R → P) → P ⊞ Q → ((P → R) × (Q → R)) → R
    more-generally R e (_ , γ) (u , v) = u (γ (λ q → e (v q)))

\end{code}

Dummett's linearity axiom for implication,

\begin{code}

linearity-axiom : Set → Set → Set
linearity-axiom P Q = (P → Q) + (Q → P)

\end{code}

makes Dummett disjunction logically equivalent to _+_:

\begin{code}

equivalent-to-intuitionistic : (P Q : Set) → linearity-axiom P Q → P ⊞ Q → P + Q
equivalent-to-intuitionistic P Q (inl u) (φ , _) = inr (φ u)
equivalent-to-intuitionistic P Q (inr v) (_ , γ) = inl (γ v)

\end{code}

We may wish to reformulate the above as follows:

\begin{code}

LA : Set₁
LA = (P Q : Set) → linearity-axiom P Q

LA-gives-agreement : LA → (P Q : Set) → P ⊞ Q → P + Q
LA-gives-agreement la P Q = equivalent-to-intuitionistic P Q (la P Q)

\end{code}

In other words, in Gödel-Dummett logic, disjunction is definable from
conjunction and implication as _⊞_ (M. Dummett, A propositional
calculus with denumerable matrix, Journal of Symbolic Logic, Vol. 24,
No. 2, pp. 97-106, 1959).

It is also well known, and obvious, that linearity just holds if one
of the propositions is decidable:

\begin{code}

dl : (P Q : Set) → decidable P → linearity-axiom P Q
dl P Q (inl p) = inr (λ _ → p)
dl P Q (inr u) = inl (λ p → 𝟘-elim (u p))

\end{code}

Hence if we assume excluded middle (all propositions are decidable),
Dummett disjunction agrees with (intuitionistic and classical)
disjunction.

More generally, without assuming excluded middle, if one of the
propositions is decidable, then P ⊞ Q and P + Q are equivalent:

\begin{code}

classical-logic-gives-agreement : (P Q : Set) → decidable P → P ⊞ Q → P + Q
classical-logic-gives-agreement P Q dp = equivalent-to-intuitionistic P Q (dl P Q dp)

\end{code}

The linearity axiom just holds, in intuitionistic logic, for all
propositions, if we formulate it with Dummett disjunction rather than
intuitionistic disjunction:

\begin{code}

⊞-linearity : (P Q : Set) → (P → Q) ⊞ (Q → P)
⊞-linearity P Q = (λ φ q → φ (λ _ → q) q) , (λ γ p → γ (λ _ → p) p)

\end{code}

I don't know whether this has already been observed. It must have
been.

Therefore we also get that if Dummett disjunction _⊞_ is equivalent to
_+_ in intuitionistic logic, then the linearity axiom must hold:

\begin{code}

agreement-gives-LA : ((P Q : Set) → P ⊞ Q → P + Q) → LA
agreement-gives-LA f P Q = f (P → Q) (Q → P) (⊞-linearity P Q)

\end{code}

And I don't know either whether this is known. It probably is.

The following is adapted from
http://www.jstor.org/stable/20016490?seq=2#page_scan_tab_contents page
154, replacing disjunction by Dummett disjunction.

Jan von Plato, Skolem's Discovery of Gödel-Dummett Logic.  Studia
Logica: An International Journal for Symbolic Logic Vol. 73, No. 1,
Constructivism in Non-Classical Logics and Computer Science (Feb.,
2003), pp. 153-157

\begin{code}

skolem : (A B C : Set) → (A → B ⊞ C) → (A → B) ⊞ (A → C)
skolem A B C h = (λ f a → pr₁(h a) (λ b → f (λ _ → b) a)) ,
                 (λ g a → pr₂(h a) (λ c → g (λ _ → c) a))

dummett : (A B C : Set) → (A × B → C) → (A → C) ⊞ (B → C)
dummett A B C h = (λ f b → f (λ a → h (a , b)) b) ,
                  (λ g a → g (λ b → h (a , b)) a)

\end{code}

The point is that we don't use the linearity axiom for implication to
prove the above, by weakening disjunction to Dummett disjunction.

Dummett also has weak excluded middle ¬P ∨ ¬¬P in his logic. This
again holds in intuitionistic logic if we replace disjunction by
Dummett disjunction. Because the proof doesn't use efq, as noted by
Dummett, we have, more generally, with 𝟘 generalized to any
proposition Q:

\begin{code}

⊞-wem : (P Q : Set) → (P → Q) ⊞ ((P → Q) → Q)
⊞-wem P Q = (λ f g → f g g) , (λ f p → f (λ g → g p) p)

\end{code}

What about excluded middle? Peirce's Law arises directly.

\begin{code}

Peirce's-Law : Set → Set → Set
Peirce's-Law P Q = ((P → Q) → P) → P

PL₀ : Set₁
PL₀ = (P : Set) → Peirce's-Law P 𝟘

⊞-EM : Set₁
⊞-EM = (P : Set) → P ⊞ ¬ P

⊞-EM-gives-PL₀ : ⊞-EM → PL₀
⊞-EM-gives-PL₀ dem P = more-generally 𝟘 (dem P)
 where
  more-generally : (Q : Set) → P ⊞ (P → Q) → Peirce's-Law P Q
  more-generally Q (_ , γ)= γ

\end{code}

The converse holds, but we don't need it:

\begin{code}

PL₀-gives-⊞-EM : PL₀ → ⊞-EM
PL₀-gives-⊞-EM pl₀ P = more-generally 𝟘 (pl₀ P)
 where
  more-generally : (Q : Set) → Peirce's-Law P Q → P ⊞ (P → Q)
  more-generally Q pl = (λ f p → f p p) , pl

PL : Set₁
PL = (P Q : Set) → Peirce's-Law P Q

PL-gives-PL₀ : PL → PL₀
PL-gives-PL₀ pl P = pl P 𝟘

PL₀-gives-PL : PL₀ → PL
PL₀-gives-PL pl₀ P Q ε = pl₀ P (λ u → ε (λ p → pl₀ Q (λ _ → 𝟘-elim (u p))))

Curry-Howard-EM : Set₁
Curry-Howard-EM = (P : Set) → P + ¬ P

PL-gives-Curry-Howard-EM : PL → Curry-Howard-EM
PL-gives-Curry-Howard-EM pl P = pl (P + ¬ P) P (λ f → inl (pl P 𝟘 (λ g → f (inr g))))

\end{code}

The converse of course holds, but again we don't need it:

\begin{code}

Curry-Howard-EM-gives-PL : Curry-Howard-EM → PL
Curry-Howard-EM-gives-PL em P Q ε = f (em P)
  where
    f : P + ¬ P → P
    f (inl p) = p
    f (inr u) = 𝟘-elim (u (ε (λ p → 𝟘-elim (u p))))

\end{code}

Hence although weak excluded middle formulated with Dummett
disjunction just holds, we have that excluded middle formulated with
Dummett or Curry-Howard disjunction are logically equivalent:

\begin{code}

⊞-EM-gives-Curry-Howard-EM : ⊞-EM → Curry-Howard-EM
⊞-EM-gives-Curry-Howard-EM dem = PL-gives-Curry-Howard-EM (PL₀-gives-PL (⊞-EM-gives-PL₀ dem))

\end{code}

Also, the above shows that Peirce's Law is equivalent to
(P Q : Set) → P ⊞ (P → Q).


I hadn't looked at Gӧdel-Dummett logic before.

I came across this as follows.

In univalent foundations, the -1-truncation of a type X can be defined as

   ∥ X ∥ = (P : U) → is--1-type P → (X → P) → P.

A -1-type (or a prop) is a type whose elements are all equal
in the sense of the identity type.

(If X lives in a universe U then ∥ X ∥ lives in the next universe.)

Then disjunction, of -1-types, is defined by

   P ∨ Q = ∥ P + Q ∥.

One can consider a variation of the definition of -1-truncation that
preserves the universe level, by working with a family of -1-types
P : I → U with I: U:

  J X = (i : I) → (X → P i) → P i.

(Cf. Aczel, "The Russell–Prawitz modality", Mathematical Structures in
Computer Science archive Volume 11 Issue 4, August 2001 Pages 541-554.)

Now, Dummett disjunction arises as

  P ⊞ Q = J(P + Q)

for the choice of I as the two-point type (the booleans) with one
point mapped to P and the other to Q.

I wondered what we got in this case, and the answer was Dummett
disjunction. But notice that you won't find "Dummett disjunction" in
the literature. What Dummett proved was that in his (intermediate)
logic, disjunction P‌‌∨Q agrees with ((P → Q) → Q) ∧ ((Q → P) → P), and
hence is definable from implication and conjunction.

Here, instead, we have considered the behaviour of what we call
Dummett disjunction in intuitionistic logic.

Added 6 Sep 2016. Weak Dummet disjunction.

We can decompose P ⊞ Q as (P ⊕ Q) × (Q ⊕ P) in the obvious way.

Weak Dummet disjunction:

\begin{code}

_⊕_ : Set → Set → Set
P ⊕ Q = (P → Q) → Q

⊕-inL : (P Q : Set) → P → P ⊕ Q
⊕-inL P Q p = λ u → u p

⊕-inR : (P Q : Set) → Q → P ⊕ Q
⊕-inR P Q q = λ _ → q

⊕-weaker-than-intuitionistic : (P Q : Set) → P + Q → P ⊕ Q
⊕-weaker-than-intuitionistic P Q (inl p) = ⊕-inL P Q p
⊕-weaker-than-intuitionistic P Q (inr q) = ⊕-inR P Q q

⊕-stronger-than-classical : (P Q : Set) → P ⊕ Q → ¬ (¬ P × ¬ Q)
⊕-stronger-than-classical P Q = more-generally 𝟘 𝟘-elim
  where
    more-generally : (R : Set) → (R → Q) → P ⊕ Q → ((P → R) × (Q → R)) → R
    more-generally R e γ (u , v) = v (γ (λ p → e (u p)))

-- Right excluded middle just holds for this notion of disjunction:

⊕-em-right : (P : Set) → P ⊕ ¬ P
⊕-em-right P = λ u p → u p p

-- But the lack of commutativity shows here: left ⊕-excluded middle is
-- equivalent to excluded middle.

-- Notice that this doesn't use 𝟘-elim:

⊕-Curry-Howard-EM-left-gives-Curry-Howard-EM : ((P : Set) → ¬ P ⊕ P) → Curry-Howard-EM
⊕-Curry-Howard-EM-left-gives-Curry-Howard-EM e P = e (P + ¬ P) (λ φ → inr (λ p → φ (inl p)))

-- Notice also that ¬ P ⊕ P is (¬ P → P) → P, which is a particular
-- case of Peirce's Law with an empty type.

Curry-Howard-EM-gives-⊕-Curry-Howard-EM-left : Curry-Howard-EM → (P : Set) → ¬ P ⊕ P
Curry-Howard-EM-gives-⊕-Curry-Howard-EM-left em P = more-generally P (em P)
 where
  more-generally : (P : Set) → decidable P → ¬ P ⊕ P
  more-generally P (inl p) = λ φ → p
  more-generally P (inr u) = λ φ → φ u

-- Notice, however, that we do have weak excluded middle for our
-- asymetric notion of disjunction, on both sides, but we already know
-- the right case:

⊕-wem-left : (P : Set) → ¬ (¬ P) ⊕ ¬ P
⊕-wem-left P = λ φ p → φ (λ u → u p) p

-- Curry-Howard disjunction agrees with weak Dummet disjunction iff
-- excluded middle holds:

agreement-gives-Curry-Howard-EM : ((P Q : Set) → P ⊕ Q → P + Q) → Curry-Howard-EM
agreement-gives-Curry-Howard-EM f P = f P (¬ P) (⊕-em-right P)

Curry-Howard-EM-gives-agreement : Curry-Howard-EM → (P Q : Set) → P ⊕ Q → P + Q
Curry-Howard-EM-gives-agreement em P Q = more-generally P Q (em P)
 where
  more-generally : (P Q : Set) → decidable P → P ⊕ Q → P + Q
  more-generally P Q (inl p) φ = inl p
  more-generally P Q (inr u) φ = inr (φ (λ p → 𝟘-elim (u p)))

-- Interestingly, also the commutativity of ⊕ is equivalent to excluded middle:

⊕-commutative : Set₁
⊕-commutative = (P Q : Set) → P ⊕ Q → Q ⊕ P

⊕-commutative-gives-Curry-Howard-EM : ⊕-commutative → Curry-Howard-EM
⊕-commutative-gives-Curry-Howard-EM c P = c (P + ¬ P) (¬ P) (λ φ p → φ (inl p) p) inr

-- We also have, of course:

equivalent-to-classical : Curry-Howard-EM → (P Q : Set) → ¬ (¬ P × ¬ Q) → P ⊕ Q
equivalent-to-classical em P Q = more-generally P Q (em P) (em Q)
 where
  more-generally : (P Q : Set) → decidable P → decidable Q → ¬ (¬ P × ¬ Q) → P ⊕ Q
  more-generally P Q (inl p) e v w = w p
  more-generally P Q (inr p) (inl q) v w = q
  more-generally P Q (inr p) (inr q) v w = 𝟘-elim (v ((λ p → q (w p)) , q))

-- The Skolem and Dummet properties also hold for our weakened notion
-- of Dummet disjunction:

⊕-skolem : (A B C : Set) → (A → B ⊕ C) → (A → B) ⊕ (A → C)
⊕-skolem A B C h = λ φ a → h a (λ b → φ (λ _ → b) a)

⊕-dummett : (A B C : Set) → (A × B → C) → (A → C) ⊕ (B → C)
⊕-dummett A B C h = λ φ b → φ (λ a → h (a , b)) b

\end{code}

Added April 2016:

We can apply the same idea to the existential quantifier.

Given a family of propositions P : X → Set, we consider

   (i : X) → ((Σ(x:X).P x) → P i) → P i

which is equivalent to

   (i : X) → ((x : X) → P x → P i) → P i

A Dummet existential quantifier:

\begin{code}

D : {X : Set} (P : X → Set) → Set
D P = ∀ i → (∀ x → P x → P i) → P i

\end{code}

If X is empty then D P holds, but ¬ (∀ x → ¬ (P x)) fails because
∀ x → ¬ (P x) holds vacuously.  However D strengthens the classical
existential quantifier for X non-empty:

\begin{code}

D-stronger-than-classical : {X : Set} (P : X → Set) → ¬ (¬ X) → D P → ¬ (∀ x → ¬ (P x))
D-stronger-than-classical P ne d u = ne (λ i → u i (d i (λ x p → 𝟘-elim (u x p))))
 where
  -- More slowly:
  a : ∀ i x → P x → P i
  a i x p = 𝟘-elim (u x p)
  b : ∀ i → P i
  b i = d i (a i)
  c : ∀ i → 𝟘
  c i = u i (b i)
  g : 𝟘
  g = ne c

D-lin : {X : Set} (P : X → Set) → D \i → D \x → P i → P x
D-lin P i _ _ f = f i (λ p → p)

\end{code}
