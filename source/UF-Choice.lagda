Martin Escardo 7 May 2014, 10 Oct 2014, 25 January 2018.

We first look at choice as in the HoTT book a little bit more
abstractly, where for the HoTT book we take T X = ∥ X ∥. It also makes
sense to consider T=¬¬, in connection with the double-negation shift.

Choice in the HoTT book, under the assumption that X is a set and A is
an X-indexed family of sets is

    (Π x ꞉ X , ∥ A x ∥) → ∥Π x ꞉ X , A x∥

(a set-indexed product of inhabited sets is inhabited).

We show that, under the same assumptions, this is equivalent

    ∥(Π x ꞉ X , ∥ A x ∥ → A x)∥.

Notice that, as shown in the HoTT book, the statement

    ∀ (B : 𝓤 ̇ ) → ∥ B ∥ → B

is in contradiction with the univalence axiom (we cannot reveal
secrets in general). However, univalent choice is consistent with the
univalent axiom, and, moreover, gives that

   ∥∀ (B : 𝓤 ̇ ) → ∥ ∥ B ∥ → B ∥

(one can secretly reveal secrets always), which is equivalent to
choice where X is a proposition (see https://arxiv.org/abs/1610.03346).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT

open import UF-Base
open import UF-Subsingletons renaming (⊤Ω to ⊤ ; ⊥Ω to ⊥)
open import UF-Subsingletons-FunExt
open import UF-FunExt
open import UF-PropTrunc
open import UF-ImageAndSurjection
open import UF-LeftCancellable
open import UF-Equiv

module UF-Choice where

module Shift
   (𝓤 : Universe)
   (T : 𝓤 ̇ → 𝓤 ̇ )
   (T-functor : {X Y : 𝓤 ̇ } → (X → Y) → T X → T Y)
 where

\end{code}

The T-shift for a family A : X → 𝓤 ̇ is

    (Π x ꞉ X , T(A x)) →  T(Π x ꞉ X , A x).

We observe that this is equivalent to

    T(Π x ꞉ X , T(A x) → A x)

This generalizes the T-condition that the double negation shift is
equivalent to

   ¬¬ (Π x ꞉ X , A x + ¬ (A x))

or

   ¬¬ (Π x ꞉ X , ¬¬ A x → A x)

\begin{code}

 Shift = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ ) → (Π x ꞉ X , T(A x)) → T(Π x ꞉ X , A x)

 Shift' = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ ) → T(Π x ꞉ X , (T(A x) → A x))

 lemma : Shift → (X : 𝓤 ̇ ) → T(T X → X)
 lemma shift X = shift (T X) (λ _ → X) (λ x → x)

 theorem : Shift → Shift'
 theorem shift X A = shift X (λ x → T(A x) → A x) (λ x → lemma shift (A x))

 theorem' : Shift' → Shift
 theorem' shift' X A φ = T-functor (claim φ) (shift' X A)
  where
   claim : ((x : X) → T (A x)) → ((x : X) → T(A x) → A x) → (x : X) →  A x
   claim φ ψ x = ψ x (φ x)

\end{code}

We now add the above constraints of the HoTT book for choice, but
abstractly, where T may be ∥_∥ and S may be is-set.

\begin{code}

module TChoice
   (𝓤 : Universe)
   (T : 𝓤 ̇ → 𝓤 ̇ )
   (T-functor : {X Y : 𝓤 ̇ } → (X → Y) → T X → T Y)
   (S : 𝓤 ̇ → 𝓤 ̇ )
   (S-exponential-ideal : {X Y : 𝓤 ̇ } → S Y → S(X → Y))
   (T-is-S : {X : 𝓤 ̇ } → S(T X))
 where

 Shift : (X : 𝓤 ̇ ) → (X → 𝓤 ̇ ) → 𝓤 ̇
 Shift X A = ((x : X) → T(A x)) → T(Π x ꞉ X , A x)

 Choice = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ ) → S X → (Π x ꞉ X , S(A x)) → Shift X A

 Choice' = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ ) → S X → (Π x ꞉ X , S(A x)) → T(Π x ꞉ X , (T(A x) → A x))

 lemma : Choice → (X : 𝓤 ̇ ) → S X → T(T X → X)
 lemma choice X s = choice (T X) (λ _ → X) T-is-S  (λ x → s) (λ x → x)

 theorem : Choice → Choice'
 theorem choice X A s t = choice X
                                 (λ x → T (A x) → A x)
                                 s
                                 (λ x → S-exponential-ideal (t x))
                                 (λ x → lemma choice (A x) (t x))

 theorem' : Choice' → Choice
 theorem' choice' X A s t φ = T-functor (λ ψ x → ψ x (φ x)) (choice' X A s t)

\end{code}

January 2018.

Let's formalize the examples discussed above, which give
characterizations choice as in the HoTT book, which we refer to as
Univalent Choice.

\begin{code}

module UnivalentChoice (fe : FunExt)
                       (pt : propositional-truncations-exist)
                       (𝓤 : Universe)
                       where

 open PropositionalTruncation pt

 sei : {X Y : 𝓤 ̇ } → is-set Y → is-set (X → Y)
 sei isy = Π-is-set (fe 𝓤 𝓤) (λ x → isy)

 open TChoice 𝓤 ∥_∥ ∥∥-functor is-set sei (props-are-sets ∥∥-is-prop)

 AC   = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ ) (P : (x : X) → A x → 𝓤 ̇ )
     → is-set X
     → ((x : X) → is-set (A x))
     → ((x : X) (a : A x) → is-prop (P x a))
     → (∀ (x : X) → ∃ a ꞉ A x , P x a) → ∃ f ꞉ Π A , ∀ (x : X) → P x (f x)

 AC'  = (X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ ) → is-set X → ((x : X) → is-set (Y x))
     → (Π x ꞉ X , ∥ Y x ∥) → ∥(Π x ꞉ X , Y x)∥

 AC'' = (X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ ) → is-set X → ((x : X) → is-set (Y x))
     → ∥(Π x ꞉ X , (∥ Y x ∥ → Y x))∥

 ACAC' : AC → AC'
 ACAC' ac X Y isx isy f = h
  where
   -- NB. We use the type x ≡ x rather than the type 𝟙 because 𝟙 is in
   -- the first universe 𝓤₀ and we don't have cumulativity. This works
   -- because X is a set by assumption, so that x ≡ x is a
   -- proposition. Any inhabited type that is a proposition will do,
   -- of course.

   g : ∃ f ꞉ Π Y , ((x : X) → x ≡ x)
   g = ac X Y (λ x a → x ≡ x) isx isy (λ x a → isx) (λ x → ∥∥-functor (λ y → y , refl) (f x))

   h : ∥ Π Y ∥
   h = ∥∥-functor pr₁ g

 AC'AC : AC' → AC
 AC'AC ac' X A P s t isp f = ∥∥-functor ΠΣ-distr g
  where
   g : ∥(Π x ꞉ X , Σ a ꞉ A x , P x a)∥
   g = ac' X
           (λ x → Σ a ꞉ A x , P x a)
           s
           (λ x → subsets-of-sets-are-sets (A x) (P x) (t x) (λ {a} → isp x a))
           f

 AC'AC'' : AC' → AC''
 AC'AC'' = theorem

 AC''AC' : AC'' → AC'
 AC''AC' = theorem'

 secretly-revealing-secrets : AC' → (B : 𝓤 ̇ ) → is-set B → ∥(∥ B ∥ → B)∥
 secretly-revealing-secrets = lemma

\end{code}

Now, assuming excluded middle, choice is equivalent to the double
negation shift.

\begin{code}

open import UF-ExcludedMiddle

module ChoiceUnderEM₀ (𝓤 : Universe)
                      (em : EM 𝓤)
                      (pt : propositional-truncations-exist)
                      (fe : FunExt)
                      where

 open PropositionalTruncation pt
 open UnivalentChoice fe pt 𝓤

 α : {X : 𝓤 ̇ } → ∥ X ∥ → ¬¬ X
 α s u = ∥∥-rec 𝟘-is-prop u s

 β : {X : 𝓤 ̇ } → ¬¬ X → ∥ X ∥
 β {X} φ = cases (λ s → s) (λ u → 𝟘-elim (φ (contrapositive ∣_∣ u))) (em ∥ X ∥ ∥∥-is-prop)

 DNS = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ ) → is-set X → ((x : X) → is-set (A x))
     → (Π x ꞉ X , ¬¬ A x) → ¬¬ (Π x ꞉ X , A x)

 DNA = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ ) → is-set X → ((x : X) → is-set (A x))
     → ¬¬ (Π x ꞉ X , (¬¬ A x → A x))

 Fact : AC' → DNS
 Fact ac X A isx isa f = α (ac X A isx isa (λ x → β (f x)))

 Fact' : DNS → AC'
 Fact' dns X A isx isa g = β (dns X A isx isa (λ x → α (g x)))

 l : {X : 𝓤 ̇ } → is-set (¬¬ X)
 l {X} = props-are-sets (Π-is-prop (fe 𝓤 𝓤₀) (λ _ → 𝟘-is-prop))

 fact : DNS → DNA
 fact = TChoice.theorem 𝓤 ¬¬_ ¬¬-functor is-set sei l

 fact' : DNA → DNS
 fact' = TChoice.theorem' 𝓤 ¬¬_ ¬¬-functor is-set sei l

\end{code}

But choice implies excluded middle. Provided we have quotients. In
fact, the quotient 𝟚/P of 𝟚 by the relation R ₀ ₁ = P, for any given
proposition P, suffices. In that case, we conclude that, assuming
function extensionality, AC is equivalent to EM × DNS.

What if we don't (necessarily) have the quotient 𝟚/P for an arbitrary
proposition P?  We get from AC that all sets have decidable
equality. This is because the quotient 𝟚/(a₀≡a₁), for two points a₀
and a₁ of a set X can be constructed as the image of the map a:𝟚→X
with values a ₀ = a₀ and a ₁ = a₁.

\begin{code}

module AC-renders-all-sets-discrete
                      (𝓤 : Universe)
                      (pt : propositional-truncations-exist)
                      (fe : FunExt)
                      where

 open PropositionalTruncation pt
 open UnivalentChoice fe pt 𝓤 public
 open ImageAndSurjection pt
 open import DiscreteAndSeparated
 open import UF-Miscelanea

 lemma₁ : {X : 𝓤 ̇ } (a : 𝟚 → X)
        → ((x : X) → (∃ i ꞉ 𝟚 , a i ≡ x) → Σ i ꞉ 𝟚 , a i ≡ x)
        → decidable(a ₀ ≡ a ₁)
 lemma₁ a c = claim (𝟚-is-discrete (s(r ₀)) (s(r ₁)))
  where
   r : 𝟚 → image a
   r = corestriction a

   r-splits : (y : image a) → Σ i ꞉ 𝟚 , r i ≡ y
   r-splits (x , t) = f (c x t)
    where
     f : (Σ i ꞉ 𝟚 , a i ≡ x) → Σ i ꞉ 𝟚 , r i ≡ (x , t)
     f (i , p) = i , to-Σ-≡ (p , ∥∥-is-prop _ t)

   s : image a → 𝟚
   s y = pr₁(r-splits y)

   rs : (y : image a) → r(s y) ≡ y
   rs y = pr₂(r-splits y)

   s-lc : left-cancellable s
   s-lc = section-lc s (r , rs)

   a-r : {i j : 𝟚} → a i ≡ a j → r i ≡ r j
   a-r p = to-Σ-≡ (p , ∥∥-is-prop _ _)

   r-a : {i j : 𝟚} → r i ≡ r j → a i ≡ a j
   r-a = ap pr₁

   a-s : {i j : 𝟚} → a i ≡ a j → s(r i) ≡ s(r j)
   a-s p = ap s (a-r p)

   s-a : {i j : 𝟚} → s(r i) ≡ s(r j) → a i ≡ a j
   s-a p = r-a (s-lc p)

   claim : decidable (s(r ₀) ≡ s(r ₁)) → decidable(a ₀ ≡ a ₁)
   claim (inl p) = inl (s-a p)
   claim (inr u) = inr (contrapositive a-s u)

 lemma₂ : {X : 𝓤 ̇ } → is-set X → (a : 𝟚 → X)
        → ∥((x : X) → (∃ i ꞉ 𝟚 , a i ≡ x) → Σ i ꞉ 𝟚 , a i ≡ x)∥
        → decidable(a ₀ ≡ a ₁)
 lemma₂ is a = ∥∥-rec (decidability-of-prop-is-prop (fe 𝓤 𝓤₀) is) (lemma₁ a)

 ac-discrete-sets' : AC → (X : 𝓤 ̇ ) → is-set X → (a : 𝟚 → X) → decidable(a ₀ ≡ a ₁)
 ac-discrete-sets' ac X isx a = lemma₂ isx a (ac'' X A isx isa)
  where
   A : X → 𝓤 ̇
   A x = Σ i ꞉ 𝟚 , a i ≡ x

   isa : (x : X) → is-set (A x)
   isa x = subsets-of-sets-are-sets 𝟚 (λ i → a i ≡ x) 𝟚-is-set isx

   ac'' : AC''
   ac'' = AC'AC'' (ACAC' ac)

 ac-discrete-sets : AC → (X : 𝓤 ̇ ) → is-set X → (a₀ a₁ : X) → decidable(a₀ ≡ a₁)
 ac-discrete-sets ac X isx a₀ a₁ = ac-discrete-sets' ac X isx (𝟚-cases a₀ a₁)

\end{code}

Is there a way to define the quotient 𝟚/P for an arbitrary proposition
P, in the universe 𝓤, using propositional truncation as the only HIT,
and funext, propext? We could allow, more generally, univalence.

If so, then, under these conditions, AC is equivalent to excluded
middle together with the double-negation shift for set-indexed
families of sets.

If we assume choice for 𝓤₁ we get excluded middle at 𝓤₀. This is
because the quotient 𝟚/P, for a proposition P in 𝓤₀, exists in 𝓤₁. In
fact, it is the image of the map 𝟚→Prop that sends ₀ to 𝟙 and ₁ to P,
because (𝟙≡P)≡P.


\begin{code}

module AC-gives-EM
                      {𝓤 : Universe}
                      (pt : propositional-truncations-exist)
                      (pe : propext 𝓤)
                      (fe : FunExt)
                      where

 open  AC-renders-all-sets-discrete (𝓤 ⁺) pt fe

 ac-gives-em : AC → EM 𝓤
 ac-gives-em ac = Ω-discrete-gives-EM (fe 𝓤 𝓤) pe
                   (ac-discrete-sets ac (Ω 𝓤) (Ω-is-set (fe 𝓤 𝓤) pe))
\end{code}


The following is probably not going to be useful for anything here:

\begin{code}

module Observation (𝓤 : Universe)
                   (pt : propositional-truncations-exist)
                   (fe : FunExt)
                   where

 open PropositionalTruncation pt
 open import DiscreteAndSeparated
 open import UF-Miscelanea

 observation : {X : 𝓤 ̇ } (a : 𝟚 → X)
        → ((x : X) → ¬¬ (Σ i ꞉ 𝟚 , a i ≡ x) → Σ i ꞉ 𝟚 , a i ≡ x)
        → decidable(a ₀ ≡ a ₁)
 observation {X} a c = claim (𝟚-is-discrete (s(r ₀)) (s(r ₁)))
  where
   Y = Σ x ꞉ X , ¬¬ (Σ i ꞉ 𝟚 , a i ≡ x)

   r : 𝟚 → Y
   r i = a i , λ u → u (i , refl)

   r-splits : (y : Y) → Σ i ꞉ 𝟚 , r i ≡ y
   r-splits (x , t) = f (c x t)
    where
     f : (Σ i ꞉ 𝟚 , a i ≡ x) → Σ i ꞉ 𝟚 , r i ≡ (x , t)
     f (i , p) = i , (to-Σ-≡ (p , negations-are-props (fe 𝓤 𝓤₀) _ t))

   s : Y → 𝟚
   s y = pr₁(r-splits y)

   rs : (y : Y) → r(s y) ≡ y
   rs y = pr₂(r-splits y)

   s-lc : left-cancellable s
   s-lc = section-lc s (r , rs)

   a-r : {i j : 𝟚} → a i ≡ a j → r i ≡ r j
   a-r p = to-Σ-≡ (p , negations-are-props (fe 𝓤 𝓤₀) _ _)

   r-a : {i j : 𝟚} → r i ≡ r j → a i ≡ a j
   r-a = ap pr₁

   a-s : {i j : 𝟚} → a i ≡ a j → s(r i) ≡ s(r j)
   a-s p = ap s (a-r p)

   s-a : {i j : 𝟚} → s(r i) ≡ s(r j) → a i ≡ a j
   s-a p = r-a (s-lc p)

   claim : decidable (s(r ₀) ≡ s(r ₁)) → decidable(a ₀ ≡ a ₁)
   claim (inl p) = inl (s-a p)
   claim (inr u) = inr (λ p → u (a-s p))

\end{code}
