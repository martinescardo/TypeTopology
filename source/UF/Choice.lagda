Martin Escardo 7 May 2014, 10 Oct 2014, 25 January 2018, 17 December 2022.

We first look at choice as in the HoTT book a little bit more
abstractly, where for the HoTT book we take T X = ∥ X ∥. It also makes
sense to consider T = ¬¬, in connection with the double-negation
shift.

Choice in the HoTT book, under the assumption that X is a set and A is
an X-indexed family of sets is

    (Π x ꞉ X , ∥ A x ∥) → ∥ Π x ꞉ X , A x ∥

(a set-indexed product of inhabited sets is inhabited).

We show that, under the same assumptions, this is equivalent

    ∥ (Π x ꞉ X , ∥ A x ∥ → A x) ∥.

Notice that, as shown in the HoTT book, the statement

    (B : 𝓤 ̇ ) → ∥ B ∥ → B

is in contradiction with the univalence axiom (we cannot reveal
secrets in general). However, univalent choice is consistent with the
univalent axiom, and, moreover, gives that

   ∥(B : 𝓤 ̇ ) → ∥ ∥ B ∥ → B ∥

(one can secretly reveal secrets always), which is equivalent to
choice where X is a proposition (see https://arxiv.org/abs/1610.03346).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.DiscreteAndSeparated
open import UF.Base
open import UF.Equiv
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.Hedberg
open import UF.LeftCancellable
open import UF.Powerset
open import UF.PropTrunc
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties

module UF.Choice where

module Shift
        (T : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇ )
        (T-functor : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → T X → T Y)
       where

\end{code}

The T-shift for a family A : X → 𝓤 ̇ is

    (Π x ꞉ X , T (A x)) →  T (Π x ꞉ X , A x).

We observe that this is equivalent to

    T (Π x ꞉ X , T (A x) → A x)

This generalizes the T-condition that the double negation shift is
equivalent to

   ¬¬ (Π x ꞉ X , A x + ¬ (A x))

or

   ¬¬ (Π x ꞉ X , ¬¬ A x → A x)

\begin{code}

 Shift : {𝓤 𝓥 : Universe} → (𝓤 ⊔ 𝓥)⁺ ̇
 Shift {𝓤} {𝓥} = (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) → (Π x ꞉ X , T (A x)) → T (Π x ꞉ X , A x)

 Shift' : {𝓤 𝓥 : Universe} → (𝓤 ⊔ 𝓥)⁺ ̇
 Shift' {𝓤} {𝓥} = (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) → T (Π x ꞉ X , (T (A x) → A x))

 Shift-gives-Shift' : Shift {𝓤} {𝓤} → Shift' {𝓤} {𝓤}
 Shift-gives-Shift' {𝓤} s X A = s X (λ x → T (A x) → A x) (λ x → F s (A x))
  where
   F : Shift → (X : 𝓤 ̇ ) → T (T X → X)
   F s X = s (T X) (λ _ → X) (λ x → x)

 Shift'-gives-Shift : Shift' {𝓤} {𝓥} → Shift {𝓤} {𝓥}
 Shift'-gives-Shift s' X A φ = T-functor (F φ) (s' X A)
  where
   F : ((x : X) → T (A x)) → ((x : X) → T (A x) → A x) → (x : X) → A x
   F φ ψ x = ψ x (φ x)

\end{code}

We now add the above constraints of the HoTT book for choice, but
abstractly, where T may be ∥_∥ and S may be is-set.

\begin{code}

module TChoice
        (T : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇ )
        (T-functor : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → T X → T Y)
        (S : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇ )
        (S-exponential-ideal : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                             → S Y → S (X → Y))
        (T-is-S : {𝓤 : Universe} {X : 𝓤 ̇ } → S (T X))
       where

 TAC : {𝓤 𝓥 : Universe} → (𝓤 ⊔ 𝓥)⁺ ̇
 TAC {𝓤} {𝓥} = (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
              → S X
              → (Π x ꞉ X , S (A x))
              → ((x : X) → T (A x)) → T (Π x ꞉ X , A x)

 TAC' : {𝓤 𝓥 : Universe} → (𝓤 ⊔ 𝓥)⁺ ̇
 TAC' {𝓤} {𝓥} = (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
               → S X
               → (Π x ꞉ X , S (A x))
               → T (Π x ꞉ X , (T (A x) → A x))

 T-lemma : TAC → (X : 𝓤 ̇ ) → S X → T (T X → X)
 T-lemma tac X s = tac (T X) (λ _ → X) T-is-S  (λ x → s) (λ x → x)

 TAC-gives-TAC' : TAC {𝓤} {𝓤} → TAC' {𝓤} {𝓤}
 TAC-gives-TAC' tac X A s t = tac
                               X
                               (λ x → T (A x) → A x)
                               s
                               (λ x → S-exponential-ideal (t x))
                               (λ x → T-lemma tac (A x) (t x))

 TAC'-gives-TAC : TAC' {𝓤} {𝓥} → TAC {𝓤} {𝓥}
 TAC'-gives-TAC c' X A s t φ = T-functor (λ ψ x → ψ x (φ x)) (c' X A s t)

\end{code}

January 2018.

We now formalize the examples discussed above, which give
characterizations choice as in the HoTT book, which we refer to as
Univalent Choice.

\begin{code}

module Univalent-Choice
        (fe : FunExt)
        (pt : propositional-truncations-exist)
        where

 open PropositionalTruncation pt

 open TChoice
       ∥_∥
       ∥∥-functor
       is-set
       (λ Y-is-set → Π-is-set (fe _ _) (λ _ → Y-is-set))
       (props-are-sets ∥∥-is-prop)

 AC : {𝓤 𝓥 : Universe} → (𝓤 ⊔ 𝓥) ⁺ ̇
 AC {𝓤} {𝓥} = (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (P : (x : X) → A x → 𝓥 ̇ )
             → is-set X
             → ((x : X) → is-set (A x))
             → ((x : X) (a : A x) → is-prop (P x a))
             → ((x : X) → ∃ a ꞉ A x , P x a)
             → ∃ f ꞉ Π A , ((x : X) → P x (f x))

 AC₁ : {𝓤 𝓥 : Universe} → (𝓤 ⊔ 𝓥)⁺ ̇
 AC₁ {𝓤} {𝓥} = (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
              → is-set X
              → ((x : X) → is-set (A x))
              → (Π x ꞉ X , ∥ A x ∥)
              → ∥(Π x ꞉ X , A x)∥

 AC₂ : {𝓤 𝓥 : Universe} → (𝓤 ⊔ 𝓥)⁺ ̇
 AC₂ {𝓤} {𝓥} = (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
              → is-set X
              → ((x : X) → is-set (A x))
              → ∥(Π x ꞉ X , (∥ A x ∥ → A x))∥

 Axiom-of-Choice Axiom-of-Choice₁ Axiom-of-Choice₂ : 𝓤ω
 Axiom-of-Choice  = {𝓤 𝓥 : Universe} → AC  {𝓤} {𝓥}
 Axiom-of-Choice₁ = {𝓤 𝓥 : Universe} → AC₁ {𝓤} {𝓥}
 Axiom-of-Choice₂ = {𝓤 𝓥 : Universe} → AC₂ {𝓤} {𝓥}

 AC-gives-AC₁ : AC {𝓤} {𝓥} → AC₁ {𝓤} {𝓥}
 AC-gives-AC₁ ac X A i j f = h
  where
   g : ∃ f ꞉ Π A , (X → 𝟙)
   g = ac X A (λ x a → 𝟙) i j (λ x a → 𝟙-is-prop) (λ x → ∥∥-functor (λ z → z , ⋆) (f x))

   h : ∥ Π A ∥
   h = ∥∥-functor pr₁ g

 AC₁-gives-AC : AC₁ {𝓤} {𝓥} → AC {𝓤} {𝓥}
 AC₁-gives-AC ac₁ X A P s t i f = ∥∥-functor ΠΣ-distr g
  where
   g : ∥(Π x ꞉ X , Σ a ꞉ A x , P x a)∥
   g = ac₁
        X
        (λ x → Σ a ꞉ A x , P x a)
        s
        (λ x → subsets-of-sets-are-sets (A x) (P x) (t x) (λ {a} → i x a))
        f

 AC₁-gives-AC₂ : AC₁ {𝓤} {𝓤} → AC₂ {𝓤} {𝓤}
 AC₁-gives-AC₂ = TAC-gives-TAC'

 AC₂-gives-AC₁ : AC₂ {𝓤} {𝓥} → AC₁ {𝓤} {𝓥}
 AC₂-gives-AC₁ = TAC'-gives-TAC

 secretly-revealing-secrets : AC₁ → (B : 𝓤 ̇ ) → is-set B → ∥(∥ B ∥ → B)∥
 secretly-revealing-secrets = T-lemma

\end{code}

But choice implies excluded middle. Provided we have quotients. In
fact, the quotient 𝟚/P of 𝟚 by the relation R ₀ ₁ = P, for any given
proposition P, suffices. In that case, we conclude that, assuming
function extensionality, AC is equivalent to EM × DNS.

What if we don't (necessarily) have the quotient 𝟚/P for an arbitrary
proposition P?  We get from AC that all sets have decidable
equality. This is because the quotient 𝟚/(a₀＝a₁), for two points a₀
and a₁ of a set X can be constructed as the image of the map a:𝟚→X
with values a ₀ = a₀ and a ₁ = a₁.

\begin{code}

module ExcludedMiddle
        (pt : propositional-truncations-exist)
        (fe : FunExt)
       where

 open PropositionalTruncation pt
 open Univalent-Choice fe pt
 open import UF.ImageAndSurjection pt

 decidability-lemma : {X : 𝓤 ̇ } (a : 𝟚 → X)
                    → ((x : X) → (∃ i ꞉ 𝟚 , a i ＝ x) → Σ i ꞉ 𝟚 , a i ＝ x)
                    → is-decidable (a ₀ ＝ a ₁)
 decidability-lemma a c = claim (𝟚-is-discrete (s(r ₀)) (s(r ₁)))
  where
   r : 𝟚 → image a
   r = corestriction a

   r-splits : (y : image a) → Σ i ꞉ 𝟚 , r i ＝ y
   r-splits (x , t) = f (c x t)
    where
     f : (Σ i ꞉ 𝟚 , a i ＝ x) → Σ i ꞉ 𝟚 , r i ＝ (x , t)
     f (i , p) = i , to-Σ-＝ (p , ∥∥-is-prop _ t)

   s : image a → 𝟚
   s y = pr₁(r-splits y)

   rs : (y : image a) → r(s y) ＝ y
   rs y = pr₂(r-splits y)

   s-lc : left-cancellable s
   s-lc = section-lc s (r , rs)

   a-r : {i j : 𝟚} → a i ＝ a j → r i ＝ r j
   a-r p = to-Σ-＝ (p , ∥∥-is-prop _ _)

   r-a : {i j : 𝟚} → r i ＝ r j → a i ＝ a j
   r-a = ap pr₁

   a-s : {i j : 𝟚} → a i ＝ a j → s(r i) ＝ s(r j)
   a-s p = ap s (a-r p)

   s-a : {i j : 𝟚} → s(r i) ＝ s(r j) → a i ＝ a j
   s-a p = r-a (s-lc p)

   claim : is-decidable (s(r ₀) ＝ s(r ₁)) → is-decidable (a ₀ ＝ a ₁)
   claim (inl p) = inl (s-a p)
   claim (inr u) = inr (contrapositive a-s u)

 decidability-lemma₂ : {X : 𝓤 ̇ }
                     → is-set X
                     → (a : 𝟚 → X)
                     → ∥((x : X) → (∃ i ꞉ 𝟚 , a i ＝ x) → Σ i ꞉ 𝟚 , a i ＝ x)∥
                     → is-decidable (a ₀ ＝ a ₁)
 decidability-lemma₂ i a =
  ∥∥-rec (decidability-of-prop-is-prop (fe _ _) i) (decidability-lemma a)

 ac-renders-all-sets-discrete' : AC {𝓤} {𝓤}
                               → (X : 𝓤 ̇ )
                               → is-set X
                               → (a : 𝟚 → X) → is-decidable (a ₀ ＝ a ₁)
 ac-renders-all-sets-discrete' {𝓤} ac X i a =
  decidability-lemma₂ i a (ac₂ X A i j)
  where
   A : X → 𝓤 ̇
   A x = Σ i ꞉ 𝟚 , a i ＝ x

   j : (x : X) → is-set (A x)
   j x = subsets-of-sets-are-sets 𝟚 (λ i → a i ＝ x) 𝟚-is-set i

   ac₂ : AC₂ {𝓤} {𝓤}
   ac₂ = AC₁-gives-AC₂ (AC-gives-AC₁ ac)

 ac-renders-all-sets-discrete : AC {𝓤} {𝓤}
                              → (X : 𝓤 ̇ )
                              → is-set X
                              → (a₀ a₁ : X) → is-decidable (a₀ ＝ a₁)
 ac-renders-all-sets-discrete {𝓤} ac X isx a₀ a₁ =
  ac-renders-all-sets-discrete' {𝓤} ac X isx (𝟚-cases a₀ a₁)

 AC-gives-EM : PropExt → AC {𝓤 ⁺} {𝓤 ⁺} → EM 𝓤
 AC-gives-EM {𝓤} pe ac =
  Ω-discrete-gives-EM (fe _ _) (pe _)
   (ac-renders-all-sets-discrete {𝓤 ⁺} ac (Ω 𝓤)
                                 (Ω-is-set (fe 𝓤 𝓤) (pe 𝓤)))

 Choice-gives-Excluded-Middle : PropExt
                              → Axiom-of-Choice
                              → Excluded-Middle
 Choice-gives-Excluded-Middle pe ac {𝓤} = AC-gives-EM {𝓤} pe (ac {𝓤 ⁺})

\end{code}

Is there a way to define the quotient 𝟚/P for an arbitrary
proposition P, in the universe 𝓤, using propositional truncation as
the only HIT, and funext, propext? We could allow, more generally,
univalence.

If so, then, under these conditions, AC is equivalent to excluded
middle together with the double-negation shift for set-indexed
families of sets.

If we assume choice for 𝓤₁ we get excluded middle at 𝓤₀. This is
because the quotient 𝟚/P, for a proposition P in 𝓤₀, exists in 𝓤₁. In
fact, it is the image of the map 𝟚→Prop that sends ₀ to 𝟙 and ₁ to P,
because (𝟙＝P)＝P.

Now, assuming excluded middle, choice is equivalent to the double
negation shift.

\begin{code}

module DNS
        (pt : propositional-truncations-exist)
        (fe : FunExt)
       where

 open PropositionalTruncation pt
 open Univalent-Choice fe pt
 open ExcludedMiddle pt fe

 DNS : {𝓤 𝓥 : Universe} → (𝓤 ⊔ 𝓥)⁺ ̇
 DNS {𝓤} {𝓥} = (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
              → is-set X
              → ((x : X) → is-set (A x))
              → (Π x ꞉ X , ¬¬ A x)
              → ¬¬ (Π x ꞉ X , A x)

 Double-Negation-Shift : 𝓤ω
 Double-Negation-Shift = {𝓤 𝓥 : Universe} → DNS {𝓤} {𝓥}

 private
  α : {X : 𝓤 ̇ } → ∥ X ∥ → ¬¬ X
  α = inhabited-is-nonempty

  β : EM 𝓤 → {X : 𝓤 ̇ } → ¬¬ X → ∥ X ∥
  β = non-empty-is-inhabited pt

  γ : {X : 𝓤 ̇ } → is-set (¬¬ X)
  γ = props-are-sets (negations-are-props (fe _ _))

  δ : {𝓤 𝓥 : Universe} → {X : 𝓤 ̇ } {A : 𝓥 ̇ } → is-set A → is-set (X → A)
  δ {𝓤} {𝓥} A-is-set = Π-is-set (fe _ _) (λ _ → A-is-set)

 EM-and-AC₁-give-DNS : EM 𝓥 → AC₁ {𝓤} {𝓥} → DNS {𝓤} {𝓥}
 EM-and-AC₁-give-DNS em ac X A i j f = α (ac X A i j (λ x → β em (f x)))

 EM-and-DNS-give-AC₁ : EM (𝓤 ⊔ 𝓥) → DNS {𝓤} {𝓥} → AC₁ {𝓤} {𝓥}
 EM-and-DNS-give-AC₁ em dns X A i j g = β em (dns X A i j (λ x → α (g x)))

\end{code}

DNS for prop-valued A, written DNS' below, is equivalent to the double
negation of the (universally quantified) principle of excluded middle.

\begin{code}

 DNS' : {𝓤 𝓥 : Universe} → (𝓤 ⊔ 𝓥)⁺ ̇
 DNS' {𝓤} {𝓥} = (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
               → is-set X
               → ((x : X) → is-prop (A x))
               → (Π x ꞉ X , ¬¬ A x)
               → ¬¬ (Π x ꞉ X , A x)

 DNS-gives-DNS' : DNS {𝓤} {𝓥} → DNS' {𝓤} {𝓥}
 DNS-gives-DNS' dns X A i j = dns X A i (λ x → props-are-sets (j x))

 DNS'-gives-¬¬EM : propext 𝓤 → DNS' {𝓤 ⁺} {𝓤} → ¬¬ EM 𝓤
 DNS'-gives-¬¬EM {𝓤} pe dns' = ¬¬-functor (λ f P i → f (P , i)) I
  where
   A : Ω 𝓤 → 𝓤 ̇
   A (P , i) = P + ¬ P

   j : (p : Ω 𝓤) → is-prop (A p)
   j (P , i) = decidability-of-prop-is-prop (fe _ _) i

   I : ¬¬ (((P , i) : Ω 𝓤) → P + ¬ P)
   I = dns'
        (Ω 𝓤)
        A
        (Ω-is-set (fe _ _) pe)
        (λ (P , i) → decidability-of-prop-is-prop (fe _ _) i)
        (λ _ → fake-¬¬-EM)

 ¬¬EM-gives-DNS' : ¬¬ EM 𝓤 → DNS' {𝓤} {𝓤}
 ¬¬EM-gives-DNS' {𝓤} nnem X A X-is-set A-is-prop-valued f = ¬¬-functor g nnem
  where
   g : EM 𝓤 → (x : X) → A x
   g em x = EM-gives-DNE em (A x) (A-is-prop-valued x) (f x)

\end{code}

In the presence of propositional extensionality, the axiom of choice
is equivalent to the conjunction of the principle of excluded middle
and the double negation shift for set-valued (rather than prop-valued)
predicates:

\begin{code}

 Choice-gives-Double-Negation-Shift : PropExt
                                    → Axiom-of-Choice₁
                                    → Double-Negation-Shift
 Choice-gives-Double-Negation-Shift pe ac {𝓤} {𝓥} = III
  where
   em : Excluded-Middle
   em = AC-gives-EM pe (AC₁-gives-AC ac)


   III : DNS {𝓤} {𝓥}
   III = EM-and-AC₁-give-DNS em ac

 Double-Negation-Shift-gives-Choice : Excluded-Middle
                                    → Double-Negation-Shift
                                    → Axiom-of-Choice₁
 Double-Negation-Shift-gives-Choice em dns {𝓤} {𝓥} =
  EM-and-DNS-give-AC₁ em (dns {𝓤} {𝓥})

\end{code}

And here is an equivalent variant of DNS:

\begin{code}

 DNA : {𝓤 𝓥 : Universe} → 𝓤 ⁺ ̇
 DNA {𝓤} {𝓥} = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ )
              → is-set X
              → ((x : X) → is-set (A x))
              → ¬¬ (Π x ꞉ X , (¬¬ A x → A x))

 open TChoice

 DNS-gives-DNA : DNS {𝓤} {𝓤} → DNA {𝓤} {𝓥}
 DNS-gives-DNA = TAC-gives-TAC' ¬¬_ ¬¬-functor is-set δ γ

 DNA-gives-DNS : DNA {𝓤} {𝓥} → DNS {𝓤} {𝓤}
 DNA-gives-DNS = TAC'-gives-TAC ¬¬_ ¬¬-functor is-set δ γ

\end{code}

Added 17th December 2022:

\begin{code}

module choice-functions
        (pt : propositional-truncations-exist)
        (pe : PropExt)
        (fe : FunExt)
       where

 open PropositionalTruncation pt
 open Univalent-Choice fe pt
 open ExcludedMiddle pt fe
 open UF.Powerset.inhabited-subsets pt

 Choice-Function : 𝓤 ̇ → 𝓤 ⁺ ̇
 Choice-Function X = ∃ ε ꞉ (𝓟⁺ X → X) , ((𝓐 : 𝓟⁺ X) → ε 𝓐 ∈⁺ 𝓐)

 AC₃ : {𝓤 : Universe} → 𝓤 ⁺ ̇
 AC₃ {𝓤} = (X : 𝓤 ̇ ) → is-set X → Choice-Function X

 AC-gives-AC₃ : {𝓤 : Universe} → AC {𝓤 ⁺} {𝓤} → AC₃ {𝓤}
 AC-gives-AC₃ ac X X-is-set =
  ac (𝓟⁺ X)
     (λ (𝓐 : 𝓟⁺ X) → X)
     (λ ((A , i) : 𝓟⁺ X) (x : X) → x ∈ A)
     (𝓟⁺-is-set' (fe _ _) (pe _))
     (λ (_ : 𝓟⁺ X) → X-is-set)
     (λ (A , i) x → ∈-is-prop A x)
     (λ (A , i) → i)

 AC₃-gives-AC₁ : {𝓤 𝓥 : Universe} → AC₃ {𝓤 ⊔ 𝓥} → AC₁ {𝓤} {𝓥}
 AC₃-gives-AC₁ {𝓤} {𝓥} ac₃ X A X-is-set A-is-set-valued = V
  where
   X' : 𝓤 ⊔ 𝓥 ̇
   X' = Σ x ꞉ X , A x

   X'-is-set : is-set X'
   X'-is-set = Σ-is-set X-is-set A-is-set-valued

   I : ∃ ε ꞉ (𝓟⁺ X' → X') , ((𝓐 : 𝓟⁺ X') → ε 𝓐 ∈⁺ 𝓐)
   I = ac₃ X' X'-is-set

   II : (Π x ꞉ X , ∥ A x ∥)
      → (Σ ε ꞉ (𝓟⁺ X' → X') , ((𝓐 : 𝓟⁺ X') → ε 𝓐 ∈⁺ 𝓐))
      → (Π x ꞉ X , A x)
   II g (ε , ϕ) x = IV
    where
     C : 𝓟 X'
     C (x₀ , a₀) = ((x₀ ＝ x) × ∥ A x ∥) , ×-is-prop X-is-set ∥∥-is-prop

     j : is-inhabited C
     j = ∥∥-functor (λ a → (x , a) , (refl , ∣ a ∣)) (g x)

     x' : X'
     x' = ε (C , j)

     x₀ : X
     x₀ = pr₁ x'

     a₀ : A x₀
     a₀ = pr₂ x'

     III : (x₀ ＝ x) × ∥ A x ∥
     III = ϕ (C , j)

     IV : A x
     IV = transport A (pr₁ III) a₀

   V : (Π x ꞉ X , ∥ A x ∥)
     → ∥(Π x ꞉ X , A x)∥
   V g = ∥∥-functor (II g) I

 AC₃-gives-AC : {𝓤 𝓥 : Universe} → AC₃ {𝓤 ⊔ 𝓥} → AC {𝓤} {𝓥}
 AC₃-gives-AC ac₃ = AC₁-gives-AC (AC₃-gives-AC₁ ac₃)

 Axiom-of-Choice₃ : 𝓤ω
 Axiom-of-Choice₃ = {𝓤 : Universe} → AC₃ {𝓤}

 Choice-gives-Choice₃ : Axiom-of-Choice → Axiom-of-Choice₃
 Choice-gives-Choice₃ c {𝓤} = AC-gives-AC₃ {𝓤} (c {𝓤 ⁺} {𝓤})

 Choice₃-gives-Choice : Axiom-of-Choice₃ → Axiom-of-Choice
 Choice₃-gives-Choice c {𝓤} {𝓥} = AC₃-gives-AC {𝓤} {𝓥} (c {𝓤 ⊔ 𝓥})

 Choice-Function⁻ : 𝓤 ̇ → 𝓤 ⁺ ̇
 Choice-Function⁻ X = ∃ ε ꞉ (𝓟 X → X) , ((A : 𝓟 X) → is-inhabited A → ε A ∈ A)

 AC₄ : {𝓤 : Universe} → 𝓤 ⁺ ̇
 AC₄ {𝓤} = (X : 𝓤 ̇ ) → is-set X → ∥ X ∥ → Choice-Function⁻ X

 Axiom-of-Choice₄ : 𝓤ω
 Axiom-of-Choice₄ = {𝓤 : Universe} → AC₄ {𝓤}

 improve-choice-function : EM 𝓤
                         → {X : 𝓤 ̇ }
                         → Choice-Function X
                         → ∥ X ∥
                         → Choice-Function⁻ X
 improve-choice-function em {X} c s = III
  where
   I : (Σ ε⁺ ꞉ (𝓟⁺ X → X) , (((A , i) : 𝓟⁺ X) → (ε⁺ (A , i) ∈ A)))
     → (Σ ε⁺ ꞉ (𝓟⁺ X → X) , ((A : 𝓟 X) (i : is-inhabited A) → ε⁺ (A , i) ∈ A))
   I = NatΣ (λ (ε⁺ : 𝓟⁺ X → X) ε⁺-behaviour A i → ε⁺-behaviour (A , i))

   II : (Σ ε⁺ ꞉ (𝓟⁺ X → X) , ((A : 𝓟 X) (i : is-inhabited A) → ε⁺ (A , i) ∈ A))
      → X
      → (Σ ε ꞉ (𝓟 X → X) , ((A : 𝓟 X) → is-inhabited A → ε A ∈ A))
   II (ε⁺ , f) x = ε , ε-behaviour

    where
     ε' : (A : 𝓟 X) → is-decidable (is-inhabited A) → X
     ε' A (inl i) = ε⁺ (A , i)
     ε' A (inr ν) = x

     d : (A : 𝓟 X) → is-decidable (is-inhabited A)
     d A = em (is-inhabited A) (being-inhabited-is-prop A)

     ε : 𝓟 X → X
     ε A = ε' A (d A)

     ε'-behaviour : (A : 𝓟 X)
                  → is-inhabited A
                  → (δ : is-decidable (is-inhabited A))
                  →  ε' A δ ∈ A
     ε'-behaviour A _ (inl j) = f A j
     ε'-behaviour A i (inr ν) = 𝟘-elim (ν i)

     ε-behaviour : (A : 𝓟 X) → is-inhabited A → ε A ∈ A
     ε-behaviour A i = ε'-behaviour A i (d A)

   III : Choice-Function⁻ X
   III = ∥∥-rec ∃-is-prop (λ x → ∥∥-rec ∃-is-prop (λ σ → ∣ II (I σ) x ∣) c) s

 Choice-gives-Choice₄ : Axiom-of-Choice → Axiom-of-Choice₄
 Choice-gives-Choice₄ ac X X-is-set = improve-choice-function
                                       (AC-gives-EM pe ac)
                                       (AC-gives-AC₃ ac X X-is-set)
\end{code}

End of addition.

The following is probably not going to be useful for anything here,
but it is stronger than the above decidability lemma:

\begin{code}

module Observation
        (fe : FunExt)
        where

 decidability-observation : {X : 𝓤 ̇ } (a : 𝟚 → X)
                          → ((x : X) → ¬¬ (Σ i ꞉ 𝟚 , a i ＝ x) → Σ i ꞉ 𝟚 , a i ＝ x)
                          → is-decidable (a ₀ ＝ a ₁)
 decidability-observation {𝓤} {X} a c = claim (𝟚-is-discrete (s(r ₀)) (s(r ₁)))
  where
   Y = Σ x ꞉ X , ¬¬ (Σ i ꞉ 𝟚 , a i ＝ x)

   r : 𝟚 → Y
   r i = a i , λ u → u (i , refl)

   r-splits : (y : Y) → Σ i ꞉ 𝟚 , r i ＝ y
   r-splits (x , t) = f (c x t)
    where
     f : (Σ i ꞉ 𝟚 , a i ＝ x) → Σ i ꞉ 𝟚 , r i ＝ (x , t)
     f (i , p) = i , to-Σ-＝ (p , negations-are-props (fe 𝓤 𝓤₀) _ t)

   s : Y → 𝟚
   s y = pr₁(r-splits y)

   rs : (y : Y) → r(s y) ＝ y
   rs y = pr₂(r-splits y)

   s-lc : left-cancellable s
   s-lc = section-lc s (r , rs)

   a-r : {i j : 𝟚} → a i ＝ a j → r i ＝ r j
   a-r p = to-Σ-＝ (p , negations-are-props (fe 𝓤 𝓤₀) _ _)

   r-a : {i j : 𝟚} → r i ＝ r j → a i ＝ a j
   r-a = ap pr₁

   a-s : {i j : 𝟚} → a i ＝ a j → s(r i) ＝ s(r j)
   a-s p = ap s (a-r p)

   s-a : {i j : 𝟚} → s(r i) ＝ s(r j) → a i ＝ a j
   s-a p = r-a (s-lc p)

   claim : is-decidable (s(r ₀) ＝ s(r ₁)) → is-decidable (a ₀ ＝ a ₁)
   claim (inl p) = inl (s-a p)
   claim (inr u) = inr (λ p → u (a-s p))

\end{code}

Added Friday 8th September 2023.

The axiom of propositional choice from
https://doi.org/10.23638/LMCS-13(1:15)2017

\begin{code}

module Propositional-Choice
        (pt : propositional-truncations-exist)
        where

 open PropositionalTruncation pt

 PAC : {𝓤 𝓥 : Universe} → (𝓤 ⊔ 𝓥)⁺ ̇
 PAC {𝓤} {𝓥} = (P : 𝓤 ̇ ) (Y : P → 𝓥 ̇ )
              → is-set P
              → (Π p ꞉ P , ∥ Y p ∥)
              → ∥(Π p ꞉ P , Y p)∥

\end{code}

Notice that we don't require that this is a family of sets. Notice
also that excluded middle implies PAC. For more information, see
Theorem 7.7 of the above reference.

TODO. Are these and more facts about this. Some of them can be adapted
from this Agda file: https://www.cs.bham.ac.uk/~mhe/GeneralizedHedberg/html/GeneralizedHedberg.html
