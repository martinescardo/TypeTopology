Martin Escardo, 24th March 2022
with minor improvements and additions June 2024.

This file is a apropos the discussion at the end of the file
Ordinals.InductiveRecursiveCodesInterpretations.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Taboos.P2 (fe : Fun-Ext) where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import MLTT.Spartan
open import MLTT.Two-Properties
open import UF.Base
open import UF.ClassicalLogic
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

The following map plays a central role in the investigations of this
file.

\begin{code}

σ : (X : 𝓤 ̇ ) → 𝟚 → (X → 𝟚)
σ X n = λ _ → n

\end{code}

Abbreviations.

\begin{code}

σ₀ : {X : 𝓤 ̇ } → (X → 𝟚)
σ₀ {𝓤} {X} = σ X ₀

σ₁ : {X : 𝓤 ̇ } → (X → 𝟚)
σ₁ {𝓤} {X} = σ X ₁

\end{code}

Recall that we say that a type X is empty to mean ¬ X, namely X → 𝟘,
and nonempty to mean ¬¬ X.

In general, if the type X is a proposition we will write "¬ X" rather
than the synonym "is-empty X", and "¬¬ X" rather than the synonym
"is-nonempty X". Also, we will pronounce "¬¬ X" as "X is irrefutable"
when X is a proposition.

\begin{code}

emptiness-criterion : (X : 𝓤 ̇ ) → is-empty X ↔ (σ₀ ＝ σ₁)
emptiness-criterion {𝓤} X = (f , g)
 where
  f : ¬ X → σ₀ ＝ σ₁
  f ν = dfunext fe (λ (x : X) → 𝟘-elim (ν x))

  g : σ₀ ＝ σ₁ → ¬ X
  g e x = zero-is-not-one
           (₀    ＝⟨refl⟩
            σ₀ x ＝⟨ happly e x ⟩
            σ₁ x ＝⟨refl⟩
            ₁    ∎)

nonemptiness-criterion : (X : 𝓤 ̇ ) → is-nonempty X ↔ (σ₀ ≠ σ₁)
nonemptiness-criterion {𝓤} X = I (emptiness-criterion X)
 where
  I : type-of (emptiness-criterion X) → ¬¬ X ↔ (σ₀ ≠ σ₁)
  I (f , g) = (λ (ν : ¬¬ X) (e : σ₀ ＝ σ₁) → ν (g e)) ,
              contrapositive f

\end{code}

The main notion studied in this file is the following:

\begin{code}

is-thinly-inhabited : 𝓤 ̇ → 𝓤 ̇
is-thinly-inhabited X = is-equiv (σ X)

being-thinly-inhabited-is-prop : {X : 𝓤 ̇ } → is-prop (is-thinly-inhabited X)
being-thinly-inhabited-is-prop {𝓤} {X} = being-equiv-is-prop fe' (σ X)

\end{code}

The idea of the terminology "thinly" is that there are very few
elements in the type, but at the same time the type is nonempty. As we
shall see, this is actually a notion stronger than nonemptiness. But
this idea works only for types that have enough functions into the
booleans, called totally separated. We show below that if X is totally
separated and thinly inhabited then X is a proposition.

Exercise. A type X is thinly inhabited if and only if there is *any*
equivalence 𝟚 ≃ (X → 𝟚).

For propositions X, the thin inhabitedness of X is equivalent to the
map σ X having a retraction ρ.

                            σ X
                          𝟚  ↪  (X → 𝟚)
                          𝟚  ↞  (X → 𝟚)
                             ρ

In general there can be many maps ρ with ρ ∘ σ X ∼ id, but there is at
most one if X is a proposition. We use the following lemma to prove
this:

\begin{code}

retraction-of-σ-is-section : {P : 𝓤 ̇ }
                           → is-prop P
                           → (ρ : (P → 𝟚) → 𝟚)
                           → ρ ∘ σ P ∼ id
                           → σ P ∘ ρ ∼ id
retraction-of-σ-is-section {𝓤} {P} i ρ h f = IV
 where
  I : (p : P) → ρ f ＝ f p
  I p = ρ f           ＝⟨ ap ρ III ⟩
        ρ (σ P (f p)) ＝⟨ h (f p) ⟩
        f p           ∎
   where
    II : f ∼ σ P (f p)
    II q = f q         ＝⟨ ap f (i q p) ⟩
           f p         ＝⟨refl⟩
           σ P (f p) q ∎

    III : f ＝ σ P (f p)
    III = dfunext fe II

  IV : σ P (ρ f) ＝ f
  IV = dfunext fe I

σ-having-retraction-is-prop : {X : 𝓤 ̇ }
                            → is-prop X
                            → is-prop (has-retraction (σ X))
σ-having-retraction-is-prop {𝓤} {X} i =
 prop-criterion
  (λ (ρ , ρσ) → sections-have-at-most-one-retraction fe' (σ X)
                 (ρ , retraction-of-σ-is-section i ρ ρσ))

retraction-of-σ-gives-thinly-inhabited : {P : 𝓤 ̇ }
                                       → is-prop P
                                       → has-retraction (σ P)
                                       → is-thinly-inhabited P
retraction-of-σ-gives-thinly-inhabited {𝓤} {P} i (ρ , ρσ) =
 qinvs-are-equivs (σ P) (ρ , ρσ , retraction-of-σ-is-section i ρ ρσ)

\end{code}

For the converse we don't need X to be a proposition, of course.

\begin{code}

thinly-inhabited-gives-retraction-of-σ : {X : 𝓤 ̇ }
                                       → is-thinly-inhabited X
                                       → has-retraction (σ X)
thinly-inhabited-gives-retraction-of-σ {𝓤} {X} = equivs-are-sections (σ X)

\end{code}

By construction, every 𝟚-valued function on a thinly inhabited type is
constant.

\begin{code}

constancy : {X : 𝓤 ̇ }
          → is-thinly-inhabited X
          → (f : X → 𝟚)
          → Σ n ꞉ 𝟚 , f ＝ λ _ → n
constancy {𝓤} {X} ti f = ⌜ e ⌝⁻¹ f , ((inverses-are-sections' e f)⁻¹)
 where
  e : 𝟚 ≃ (X → 𝟚)
  e = σ X , ti

\end{code}

Next we want to show that

 P → is-thinly-inhabited P

for any proposition P, and we use the following lemma.

\begin{code}

point-gives-retraction-of-σ : {X : 𝓤 ̇ }
                            → X
                            → has-retraction (σ X)
point-gives-retraction-of-σ {𝓤} {X} x = (γ , γσ)
 where
  γ : (X → 𝟚) → 𝟚
  γ f = f x

  γσ : γ ∘ σ X ∼ id
  γσ n = refl

point-gives-is-thinly-inhabited : {P : 𝓤 ̇ }
                                → is-prop P
                                → P
                                → is-thinly-inhabited P
point-gives-is-thinly-inhabited {𝓤} {P} i p =
 retraction-of-σ-gives-thinly-inhabited i (point-gives-retraction-of-σ p)

\end{code}

Notice, however, that pointed types X other than propositions are not
thinly inhabited in general. An example is the type X := 𝟚, because there
are four maps X → 𝟚 in this case, and we need exactly two to have an
equivalence.

We will see later that the following implication can't be reversed,
even for just propositions, unless weak excluded middle holds, so that
the notion of being thinly inhabited is stronger, in general, than
that of being nonempty.

\begin{code}

thinly-inhabited-gives-nonempty : {X : 𝓤 ̇ }
                                → is-thinly-inhabited X
                                → is-nonempty X
thinly-inhabited-gives-nonempty {𝓤} {X} ti ν = III
 where
  e : 𝟚 ≃ (X → 𝟚)
  e = σ X , ti

  I : ⌜ e ⌝⁻¹ σ₀ ＝ ⌜ e ⌝⁻¹ σ₁
  I = ap (⌜ e ⌝⁻¹) (σ₀ ＝⟨ dfunext fe (λ x → 𝟘-elim (ν x)) ⟩
                    σ₁ ∎)

  II = ₀          ＝⟨ (inverses-are-retractions' e ₀)⁻¹ ⟩
       ⌜ e ⌝⁻¹ σ₀ ＝⟨ I ⟩
       ⌜ e ⌝⁻¹ σ₁ ＝⟨ inverses-are-retractions' e ₁ ⟩
       ₁          ∎

  III : 𝟘
  III = zero-is-not-one II

\end{code}

In some cases the implication

 P → is-thinly-inhabited P

can be reversed:

\begin{code}

thinly-inhabited-emptiness-gives-emptiness
 : {X : 𝓤 ̇ }
 → is-thinly-inhabited (is-empty X)
 → is-empty X
thinly-inhabited-emptiness-gives-emptiness h =
 three-negations-imply-one (thinly-inhabited-gives-nonempty h)

thinly-inhabited-nonemptiness-gives-nonemptiness
 : {X : 𝓤 ̇ }
 → is-thinly-inhabited (is-nonempty X)
 → is-nonempty X
thinly-inhabited-nonemptiness-gives-nonemptiness {𝓤} {X} =
 thinly-inhabited-emptiness-gives-emptiness {𝓤} {is-empty X}

\end{code}

The following is a digression from our main aims. Recall that a type
is called discrete if it has decidable equality.

\begin{code}

X→𝟚-discreteness-criterion : {X : 𝓤 ̇ }
                           → is-empty X + is-thinly-inhabited X
                           → is-discrete (X → 𝟚)
X→𝟚-discreteness-criterion (inl ν) f g = inl (dfunext fe (λ x → 𝟘-elim (ν x)))
X→𝟚-discreteness-criterion (inr h) f g = retract-is-discrete
                                          (≃-gives-▷ (σ _ , h))
                                          𝟚-is-discrete
                                          f g

P→𝟚-discreteness-criterion-necessity : {P : 𝓤 ̇ }
                                     → is-prop P
                                     → is-discrete (P → 𝟚)
                                     → ¬ P + is-thinly-inhabited P
P→𝟚-discreteness-criterion-necessity {𝓤} {P} i δ = ϕ (δ σ₀ σ₁)
 where
  ϕ : is-decidable (σ₀ ＝ σ₁) → ¬ P + is-thinly-inhabited P
  ϕ (inl e) = inl (fact e)
   where
    fact : σ₀ ＝ σ₁ → ¬ P
    fact e p = zero-is-not-one (ap (λ f → f p) e)
  ϕ (inr n) = inr (retraction-of-σ-gives-thinly-inhabited i (γ , γσ))
   where
    h : (f : P → 𝟚) → is-decidable (f ＝ σ₀) → 𝟚
    h f (inl _) = ₀
    h f (inr _) = ₁

    γ : (P → 𝟚) → 𝟚
    γ f = h f (δ f σ₀)

    h₀ : (d : is-decidable (σ₀ ＝ σ₀)) → h σ₀ d ＝ ₀
    h₀ (inl _) = refl
    h₀ (inr d) = 𝟘-elim (d refl)

    h₁ : (d : is-decidable (σ₁ ＝ σ₀)) → h σ₁ d ＝ ₁
    h₁ (inl e) = 𝟘-elim (n (e ⁻¹))
    h₁ (inr _) = refl

    γσ : γ ∘ σ P ∼ id
    γσ ₀ = h₀ (δ σ₀ σ₀)
    γσ ₁ = h₁ (δ σ₁ σ₀)

\end{code}

Added 25th March 2022. If every nonempty proposition is thinly inhabited,
then weak excluded middle holds. We use the following lemma to prove
this. Recall that the principle of weak excluded middle, which is
equivalent to De Morgan's Law, says that for every proposition P,
either ¬ P or ¬¬ P holds.

\begin{code}

thinly-inhabited-wem-lemma : (X : 𝓤 ̇ )
                           → is-thinly-inhabited (X + is-empty X)
                           → is-empty X + is-nonempty X
thinly-inhabited-wem-lemma X ti = II
 where
  Y = X + ¬ X

  f : Y → 𝟚
  f (inl _) = ₀
  f (inr _) = ₁

  n : 𝟚
  n = inverse (σ Y) ti f

  I : (k : 𝟚) → n ＝ k → ¬ X + ¬¬ X
  I ₀ e = inr ϕ
   where
    I₀ = f         ＝⟨ (inverses-are-sections (σ Y) ti f)⁻¹ ⟩
         σ Y n     ＝⟨ ap (σ Y) e ⟩
         (λ _ → ₀) ∎

    ϕ : ¬¬ X
    ϕ u = zero-is-not-one
           (₀         ＝⟨ (ap (λ - → - (inr u)) I₀)⁻¹ ⟩
            f (inr u) ＝⟨refl⟩
            ₁         ∎)

  I ₁ e = inl u
   where
    I₁ = f         ＝⟨ (inverses-are-sections (σ Y) ti f)⁻¹ ⟩
         σ Y n     ＝⟨ ap (σ Y) e ⟩
         (λ _ → ₁) ∎

    u : ¬ X
    u q = zero-is-not-one
           (₀         ＝⟨refl⟩
            f (inl q) ＝⟨ ap (λ - → - (inl q)) I₁ ⟩
            ₁         ∎)

  II : ¬ X + ¬¬ X
  II = I n refl

\end{code}

As promised above, thin inhabitedness is stronger than nonemptiness in
general, because WEM is not provable or disprovable, as it is true in
some models and false in others, and this is the main observation in
this file so far.

\begin{code}

irrefutable-props-are-thinly-inhabited-gives-WEM
 : ((P : 𝓤 ̇ ) → is-prop P → ¬¬ P → is-thinly-inhabited P)
 → typal-WEM 𝓤
irrefutable-props-are-thinly-inhabited-gives-WEM {𝓤} α = I
 where
  module _ (Q : 𝓤 ̇ ) (i : is-prop Q) where
   P = Q + ¬ Q

   ν : ¬¬ P
   ν ϕ = ϕ (inr (λ q → ϕ (inl q)))

   h : is-thinly-inhabited P
   h = α P (decidability-of-prop-is-prop fe i) ν

  I : typal-WEM 𝓤
  I = WEM-gives-typal-WEM fe (λ Q i → thinly-inhabited-wem-lemma Q (h Q i))

\end{code}

Nathanael Rosnik proved the above independently within a few
hours of difference here:
https://gist.github.com/nrosnick/922250ddcc6bd04272199f59443d7510

Conversely, weak excluded middle gives that every irrefutable
proposition is thinly inhabited, which we get from the above
discreteness criterion.

\begin{code}

typal-WEM-gives-X→𝟚-discreteness
 : typal-WEM 𝓤
 → {X : 𝓤 ̇ } → is-discrete (X → 𝟚)
typal-WEM-gives-X→𝟚-discreteness {𝓤} wem {X} f g = I (wem (f ＝ g))
 where
  s : ¬¬ (f ＝ g) → f ＝ g
  s ϕ = dfunext fe
         (Π-is-¬¬-stable
           (λ x → discrete-is-¬¬-separated 𝟚-is-discrete (f x) (g x))
           (¬¬-functor happly ϕ))

  I : ¬ (f ＝ g) + ¬¬ (f ＝ g) → is-decidable (f ＝ g)
  I (inl ν) = inr ν
  I (inr ϕ) = inl (s ϕ)

X→𝟚-discreteness-gives-irrefutable-props-are-thinly-inhabited
 : ((P : 𝓤 ̇ ) → is-prop P → is-discrete (P → 𝟚))
 → (P : 𝓤 ̇ ) → is-prop P → ¬¬ P → is-thinly-inhabited P
X→𝟚-discreteness-gives-irrefutable-props-are-thinly-inhabited δ P i ν =
 Cases (P→𝟚-discreteness-criterion-necessity i (δ P i))
  (λ (u : ¬ P) → 𝟘-elim (ν u))
  id

typal-WEM-gives-irrefutable-props-are-thinly-inhabited
 : typal-WEM 𝓤
 → (P : 𝓤 ̇ ) → is-prop P → ¬¬ P → is-thinly-inhabited P
typal-WEM-gives-irrefutable-props-are-thinly-inhabited wem =
 X→𝟚-discreteness-gives-irrefutable-props-are-thinly-inhabited
  (λ P i → typal-WEM-gives-X→𝟚-discreteness wem)

irrefutable-props-are-thinly-inhabited-iff-WEM
 : ((P : 𝓤 ̇ ) → is-prop P → ¬¬ P → is-thinly-inhabited P)
 ↔ typal-WEM 𝓤
irrefutable-props-are-thinly-inhabited-iff-WEM =
 irrefutable-props-are-thinly-inhabited-gives-WEM ,
 typal-WEM-gives-irrefutable-props-are-thinly-inhabited

\end{code}

And so the discreteness of the type P → 𝟚 for all propositions P is yet
another formulation of weak excluded middle.

\begin{code}

P→𝟚-discreteness-iff-WEM
 : ((P : 𝓤 ̇ ) → is-prop P → is-discrete (P → 𝟚))
 ↔ typal-WEM 𝓤
P→𝟚-discreteness-iff-WEM =
 (irrefutable-props-are-thinly-inhabited-gives-WEM
   ∘ X→𝟚-discreteness-gives-irrefutable-props-are-thinly-inhabited) ,
 (λ wem P i → typal-WEM-gives-X→𝟚-discreteness wem)

\end{code}

End of addition and back to the past.

A minor observation, giving another instance of an implication
is-thinly-inhabited P → P.

\begin{code}

thinly-inhabited-wem-special : (X : 𝓤 ̇ )
                             → is-thinly-inhabited (is-empty X + is-nonempty X)
                             → is-empty X + is-nonempty X
thinly-inhabited-wem-special X h =
 Cases (thinly-inhabited-wem-lemma (¬ X) h)
  inr
  (inl ∘ three-negations-imply-one)

\end{code}

Digression. A monad on propositions (or even a wild monad on all types?).

\begin{code}

module retraction-monad where

 η : {X : 𝓤 ̇ } → X → has-retraction (σ X)
 η x = (λ f → f x) , (λ n → refl)

 _♯ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
    → (X → has-retraction (σ Y))
    → (has-retraction (σ X) → has-retraction (σ Y))
 _♯ {𝓤} {𝓥} {X} {Y} h (ρ , ρσ) = q
  where
   a : X → (Y → 𝟚) → 𝟚
   a x = retraction-of (σ Y) (h x)

   b : (x : X) (n : 𝟚) → a x (σ Y n) ＝ n
   b x = retraction-equation (σ Y) (h x)

   u : (Y → 𝟚) → 𝟚
   u g = ρ (λ x → a x g)

   v : u ∘ σ Y ∼ id
   v n = (u ∘ σ Y) n           ＝⟨refl⟩
         ρ (λ x → a x (σ Y n)) ＝⟨ ap ρ (dfunext fe (λ x → b x n)) ⟩
         ρ (λ _ → n)           ＝⟨refl⟩
         ρ (σ X n)             ＝⟨ ρσ n ⟩
         n                     ∎

   q : has-retraction (σ Y)
   q = u , v

 functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
         → (X → Y)
         → (has-retraction (σ X) → has-retraction (σ Y))
 functor f = (η ∘ f) ♯

 μ : (X : 𝓤 ̇ )
   → has-retraction (σ (has-retraction (σ X)))
   → has-retraction (σ X)
 μ X = id ♯

\end{code}

TODO. It doesn't seem to be possible to give the structure of a monad
to is-thinly-inhabited.

Added 13th June 2024. The homotopy circle S¹ is thinly inhabited
because, as it is a connected 1-type, all functions S¹ → 𝟚 are
constant as 𝟚 is a set. As another example, the type ℝ of Dedekind
reals is a set, but still there may be no function ℝ → 𝟚 other than
the constant functions, because "all functions ℝ → 𝟚 are continuous"
is a consistent axiom. But if a totally separated type (which is
necessarily a set) is thinly inhabited, then it must be a proposition.

Recall that x ＝₂ y is defined to mean that p x = p y for all p : X → 𝟚,
that is, x and y satisfy the same boolean-valued properties. When
x ＝₂ y holds for all x and y in X, we say that X is connected₂. And
recall that, in another extreme, when x ＝₂ y implies x ＝ y for all x
and y, we say that X is totally separated.

\begin{code}

open import TypeTopology.TotallySeparated
open import TypeTopology.DisconnectedTypes

thinly-inhabited-types-are-connected₂ : {X : 𝓤 ̇ }
                                      → is-thinly-inhabited X
                                      → is-connected₂ X
thinly-inhabited-types-are-connected₂ {𝓤} {X} ti x y = I
 where
  e : 𝟚 ≃ (X → 𝟚)
  e = σ X , ti

  I : (p : X → 𝟚) → p x ＝ p y
  I p = p x                 ＝⟨ happly ((inverses-are-sections' e p)⁻¹) x ⟩
        ⌜ e ⌝ (⌜ e ⌝⁻¹ p) x ＝⟨refl⟩
        ⌜ e ⌝⁻¹ p           ＝⟨refl⟩
        ⌜ e ⌝ (⌜ e ⌝⁻¹ p) y ＝⟨ happly (inverses-are-sections' e p) y ⟩
        p y                 ∎

totally-separated-thinly-inhabited-types-are-props : {X : 𝓤 ̇ }
                                                   → is-totally-separated X
                                                   → is-thinly-inhabited X
                                                   → is-prop X
totally-separated-thinly-inhabited-types-are-props ts ti x y = I
 where
  I : x ＝ y
  I = ts (thinly-inhabited-types-are-connected₂ ti x y)

\end{code}

If replace the type 𝟚 by the type Ω of propositions in the notion of
thin inhabitedness, then we can replace the assumption
"is-totally-separated X" by "is-set X" to get the same conclusion
(exercise). And if we replace 𝟚 by some universe 𝓤, no assumption is
needed to conclude that thinly inhabited types are propositions:

\begin{code}

module universe-discussion where

 κ : (X : 𝓤 ̇ ) → 𝓤 ̇ → (X → 𝓤 ̇ )
 κ X Y = λ (_ : X) → Y

 is-thinly-inhabited' : 𝓤 ̇ → 𝓤 ⁺ ̇
 is-thinly-inhabited' X = is-equiv (κ X)

 thinly-inhabited'-types-are-props : {X : 𝓤 ̇ }
                                   → is-thinly-inhabited' X
                                   → is-prop X
 thinly-inhabited'-types-are-props {𝓤} {X} ti x y = III
  where
   e : 𝓤 ̇ ≃ (X → 𝓤 ̇ )
   e = κ X , ti

   I : (p : X → 𝓤 ̇ ) → p x ＝ p y
   I p = p x                 ＝⟨ happly ((inverses-are-sections' e p)⁻¹) x ⟩
         ⌜ e ⌝ (⌜ e ⌝⁻¹ p) x ＝⟨refl⟩
         ⌜ e ⌝⁻¹ p           ＝⟨refl⟩
         ⌜ e ⌝ (⌜ e ⌝⁻¹ p) y ＝⟨ happly (inverses-are-sections' e p) y ⟩
         p y                 ∎

   II : (x ＝ x) ＝ (x ＝ y)
   II = I (x ＝_)

   III : x ＝ y
   III = idtofun' II refl

 η : {X : 𝓤 ̇ } → is-prop X → X → is-thinly-inhabited' X
 η {𝓤} {X} i x₀ = qinvs-are-equivs (κ X) (s , sκ , κs)
  where
   s : (X → 𝓤 ̇ ) → 𝓤 ̇
   s A = A x₀

   sκ : s ∘ κ X ∼ id
   sκ Y = refl

   κs : κ X ∘ s ∼ id
   κs A = dfunext fe (λ x → ap A (i x₀ x))

 thinly-inhabited'-gives-nonempty : {X : 𝓤 ̇ }
                                  → is-thinly-inhabited' X
                                  → is-nonempty X
 thinly-inhabited'-gives-nonempty {𝓤} {X} ti ν = III
  where
   e : 𝓤 ̇ ≃ (X → 𝓤 ̇ )
   e = κ X , ti

   I : ⌜ e ⌝⁻¹  (⌜ e ⌝ 𝟙) ＝ ⌜ e ⌝⁻¹  (⌜ e ⌝ 𝟘)
   I = ap (⌜ e ⌝⁻¹) (⌜ e ⌝ 𝟙 ＝⟨ dfunext fe (λ x → 𝟘-elim (ν x)) ⟩
                     ⌜ e ⌝ 𝟘 ∎)

   II = 𝟙                 ＝⟨ (inverses-are-retractions' e 𝟙)⁻¹ ⟩
        ⌜ e ⌝⁻¹ (⌜ e ⌝ 𝟙) ＝⟨ I ⟩
        ⌜ e ⌝⁻¹ (⌜ e ⌝ 𝟘) ＝⟨ inverses-are-retractions' e 𝟘 ⟩
        𝟘                 ∎

   III : 𝟘 {𝓤₀}
   III = 𝟘-elim (idtofun' II ⋆)

\end{code}

TODO (done below). Derive a constructive taboo from the hypothesis

      (P : 𝓤 ̇ ) → is-prop P → is-thinly-inhabited P → P.

The difficulty, of course, is to come up with a type P which we can
prove to be thinly inhabited but (we can't prove to be pointed and)
whose pointedness would give a constructive taboo.

Added 16th October 2026. We now come back to the original notion of
thin inhabitedness studied in this file, and solve the above TODO. The
taboo is that weak excluded middle implies excluded middle.

\begin{code}

WEM-implies-EM : ∀ 𝓤 → 𝓤 ⁺ ̇
WEM-implies-EM 𝓤 = typal-WEM 𝓤 → EM 𝓤

\end{code}

We choose the typal version, rather than the propositional version,
for technical convenience. But notice that it doesn't make any
mathematical difference, because, as we have shown in
UF.ClassicalLogic, typal WEM is logically equivalent to propositional WEM.

This can be considered as a sort of taboo because weak excluded middle
holds in models in which excluded middle fails, the simplest example
being sheaves over the two-point space with one open point. Weak
excluded middle is De Morgan's law, and the toposes that satisfy it are
studied in

   P.T. Johnstone. Conditions related to de Morgan's law. Applications
   of Sheaves, Lecture Notes in Mathematics, Vol 753, Springer, 1979,
   pp. 479-491. https://doi.org/10.1007/BFb0061829

We first show that thin inhabitedness amounts to Π-compactness
together with nonemptiness. We repeat the definition of Π-compactness,
rather than import it from TypeTopology.WeaklyCompactTypes, because
that module assumes propositional truncations and this one doesn't. One
direction holds for arbitrary types, and for the other we need a
proposition, as in the above case of a retraction of σ.

\begin{code}

is-Π-compact : 𝓤 ̇ → 𝓤 ̇
is-Π-compact X = (p : X → 𝟚) → is-decidable ((x : X) → p x ＝ ₁)

thinly-inhabited-types-are-Π-compact
 : {X : 𝓤 ̇ }
 → is-thinly-inhabited X
 → is-Π-compact X
thinly-inhabited-types-are-Π-compact {𝓤} {X} ti p = I (constancy ti p)
 where
  I : (Σ n ꞉ 𝟚 , p ＝ (λ _ → n)) → is-decidable ((x : X) → p x ＝ ₁)
  I (₀ , e) = inr (λ (α : (x : X) → p x ＝ ₁)
                     → thinly-inhabited-gives-nonempty ti
                        (λ x → zero-is-not-one
                                (₀   ＝⟨ (happly e x)⁻¹ ⟩
                                 p x ＝⟨ α x ⟩
                                 ₁   ∎)))
  I (₁ , e) = inl (happly e)

Π-compact-nonempty-props-are-thinly-inhabited
 : {P : 𝓤 ̇ }
 → is-prop P
 → is-Π-compact P
 → is-nonempty P
 → is-thinly-inhabited P
Π-compact-nonempty-props-are-thinly-inhabited {𝓤} {P} i c ν =
 retraction-of-σ-gives-thinly-inhabited i (ρ , ρσ)
 where
  h : (f : P → 𝟚) → is-decidable ((x : P) → f x ＝ ₁) → 𝟚
  h f (inl _) = ₁
  h f (inr _) = ₀

  ρ : (P → 𝟚) → 𝟚
  ρ f = h f (c f)

  h₀ : (d : is-decidable ((x : P) → σ₀ x ＝ ₁)) → h σ₀ d ＝ ₀
  h₀ (inl α) = 𝟘-elim (ν (λ p → zero-is-not-one (α p)))
  h₀ (inr _) = refl

  h₁ : (d : is-decidable ((x : P) → σ₁ x ＝ ₁)) → h σ₁ d ＝ ₁
  h₁ (inl _) = refl
  h₁ (inr u) = 𝟘-elim (u (λ _ → refl))

  ρσ : ρ ∘ σ P ∼ id
  ρσ ₀ = h₀ (c σ₀)
  ρσ ₁ = h₁ (c σ₁)

thinly-inhabited-iff-Π-compact-and-nonempty
 : {P : 𝓤 ̇ }
 → is-prop P
 → is-thinly-inhabited P
 ↔ (is-Π-compact P × is-nonempty P)
thinly-inhabited-iff-Π-compact-and-nonempty i =
 (λ ti → thinly-inhabited-types-are-Π-compact ti ,
         thinly-inhabited-gives-nonempty ti) ,
 (λ (c , ν) → Π-compact-nonempty-props-are-thinly-inhabited i c ν)

\end{code}

In particular, the principle that all irrefutable propositions are
Π-compact amounts to weak excluded middle.

\begin{code}

irrefutable-props-are-Π-compact-iff-WEM
 : ((P : 𝓤 ̇ ) → is-prop P → ¬¬ P → is-Π-compact P)
 ↔ typal-WEM 𝓤
irrefutable-props-are-Π-compact-iff-WEM =
 (λ c → irrefutable-props-are-thinly-inhabited-gives-WEM
         (λ P i ν → Π-compact-nonempty-props-are-thinly-inhabited
                     i (c P i ν) ν)) ,
 (λ wem P i ν → thinly-inhabited-types-are-Π-compact
                 (typal-WEM-gives-irrefutable-props-are-thinly-inhabited
                   wem P i ν))

\end{code}

We now name the property we want to characterize.

\begin{code}

Thinly-Inhabited-Props-Are-Pointed : ∀ 𝓤 → 𝓤 ⁺ ̇
Thinly-Inhabited-Props-Are-Pointed 𝓤 =
  (P : 𝓤 ̇ )
 → is-prop P
 → is-thinly-inhabited P
 → P

\end{code}

That thinly inhabited propositions are pointed follows from double
negation elimination, because thinly inhabited types are nonempty, and
so the hypothesis is classically true, which means that no
anti-classical taboo can follow from it.

\begin{code}

DNE-gives-thinly-inhabited-props-are-pointed
 : DNE 𝓤
 → Thinly-Inhabited-Props-Are-Pointed 𝓤
DNE-gives-thinly-inhabited-props-are-pointed dne P i ti =
 dne P i (thinly-inhabited-gives-nonempty ti)

\end{code}

By the above characterization of thin inhabitedness, the hypothesis
says precisely that Π-compact propositions are decidable. We name this
property.

\begin{code}

Π-Compact-Props-Are-Decidable : ∀ 𝓤 → 𝓤 ⁺ ̇
Π-Compact-Props-Are-Decidable 𝓤 =
   (P : 𝓤 ̇ )
 → is-prop P
 → is-Π-compact P
 → is-decidable P

thinly-inhabited-props-are-pointed-iff-Π-compact-props-are-decidable
 : Thinly-Inhabited-Props-Are-Pointed 𝓤
 ↔ Π-Compact-Props-Are-Decidable 𝓤
thinly-inhabited-props-are-pointed-iff-Π-compact-props-are-decidable {𝓤} =
 (f , g)
 where
  f : Thinly-Inhabited-Props-Are-Pointed 𝓤
    → Π-Compact-Props-Are-Decidable 𝓤
  f α P i c = I (c σ₀)
   where
    I : is-decidable ((x : P) → σ₀ x ＝ ₁) → is-decidable P
    I (inl β) = inr (λ p → zero-is-not-one (β p))
    I (inr u) = inl (α P i (Π-compact-nonempty-props-are-thinly-inhabited
                            i c ν))
     where
      ν : is-nonempty P
      ν ϕ = u (λ p → 𝟘-elim (ϕ p))

  g : Π-Compact-Props-Are-Decidable 𝓤
    → Thinly-Inhabited-Props-Are-Pointed 𝓤
  g β P i ti = I (β P i (thinly-inhabited-types-are-Π-compact ti))
   where
    I : is-decidable P → P
    I (inl p) = p
    I (inr u) = 𝟘-elim (thinly-inhabited-gives-nonempty ti u)

\end{code}

Equivalently, by the discreteness criterion given above, the
hypothesis says that the discreteness of P → 𝟚 gives the decidability
of P. This reverses the implication from the decidability of P to the
discreteness of P → 𝟚, which is the motivation for this file, and we
come back to this below.

\begin{code}

P→𝟚-Discreteness-Gives-Decidability : ∀ 𝓤 → 𝓤 ⁺ ̇
P→𝟚-Discreteness-Gives-Decidability 𝓤 =
 (P : 𝓤 ̇ ) → is-prop P → is-discrete (P → 𝟚) → is-decidable P

thinly-inhabited-props-are-pointed-iff-P→𝟚-discreteness-gives-decidability
 : Thinly-Inhabited-Props-Are-Pointed 𝓤
 ↔ P→𝟚-Discreteness-Gives-Decidability 𝓤
thinly-inhabited-props-are-pointed-iff-P→𝟚-discreteness-gives-decidability
 {𝓤} = (f , g)
 where
  f : Thinly-Inhabited-Props-Are-Pointed 𝓤
    → P→𝟚-Discreteness-Gives-Decidability 𝓤
  f α P i δ = Cases (P→𝟚-discreteness-criterion-necessity i δ)
               inr
               (λ ti → inl (α P i ti))

  g : P→𝟚-Discreteness-Gives-Decidability 𝓤
    → Thinly-Inhabited-Props-Are-Pointed 𝓤
  g β P i ti = I (β P i (X→𝟚-discreteness-criterion (inr ti)))
   where
    I : is-decidable P → P
    I (inl p) = p
    I (inr u) = 𝟘-elim (thinly-inhabited-gives-nonempty ti u)

\end{code}

And here is the derivation of the taboo. Under weak excluded middle
every irrefutable proposition is thinly inhabited, and so the
hypothesis turns weak excluded middle into double negation elimination,
and hence into excluded middle.

\begin{code}

thinly-inhabited-props-are-pointed-gives-WEM-implies-EM
 : Thinly-Inhabited-Props-Are-Pointed 𝓤
 → WEM-implies-EM 𝓤
thinly-inhabited-props-are-pointed-gives-WEM-implies-EM {𝓤} α wem =
 DNE-gives-EM fe I
 where
  I : DNE 𝓤
  I P i ν = α P i
             (typal-WEM-gives-irrefutable-props-are-thinly-inhabited
               wem P i ν)

\end{code}

And this is all that the hypothesis gives, in the sense that the
hypothesis and weak excluded middle together are equivalent to excluded
middle.

\begin{code}

thinly-inhabited-props-are-pointed-and-WEM-iff-EM
 : (Thinly-Inhabited-Props-Are-Pointed 𝓤 × typal-WEM 𝓤) ↔ EM 𝓤
thinly-inhabited-props-are-pointed-and-WEM-iff-EM {𝓤} = (f , g)
 where
  f : Thinly-Inhabited-Props-Are-Pointed 𝓤 × typal-WEM 𝓤 → EM 𝓤
  f (α , wem) = thinly-inhabited-props-are-pointed-gives-WEM-implies-EM α wem

  g : EM 𝓤 → Thinly-Inhabited-Props-Are-Pointed 𝓤 × typal-WEM 𝓤
  g em = DNE-gives-thinly-inhabited-props-are-pointed (EM-gives-DNE em) ,
         (λ A → em (¬ A) (negations-are-props fe))

\end{code}

And so the hypothesis gives excluded middle if and only if it gives
weak excluded middle.

\begin{code}

thinly-inhabited-props-are-pointed-gives-EM-iff-gives-WEM
 : (Thinly-Inhabited-Props-Are-Pointed 𝓤 → EM 𝓤)
 ↔ (Thinly-Inhabited-Props-Are-Pointed 𝓤 → typal-WEM 𝓤)
thinly-inhabited-props-are-pointed-gives-EM-iff-gives-WEM {𝓤} = (f , g)
 where
  f : (Thinly-Inhabited-Props-Are-Pointed 𝓤 → EM 𝓤)
    → Thinly-Inhabited-Props-Are-Pointed 𝓤 → typal-WEM 𝓤
  f ϕ α A = ϕ α (¬ A) (negations-are-props fe)

  g : (Thinly-Inhabited-Props-Are-Pointed 𝓤 → typal-WEM 𝓤)
    → Thinly-Inhabited-Props-Are-Pointed 𝓤 → EM 𝓤
  g γ α = thinly-inhabited-props-are-pointed-gives-WEM-implies-EM α (γ α)

\end{code}

We haven't managed to derive weak excluded middle from the hypothesis,
and by the above this is the same as deriving excluded middle from it.
As excluded middle gives the hypothesis, either of these would show
that the hypothesis and excluded middle are equivalent.

This also answers the question that motivates this file. Recall from
the discussion at the end of Ordinals.InductiveRecursiveCodesInterpretations
the implications

 (0) if P is decidable then P → 𝟚 is discrete,
 (1) if P → 𝟚 is discrete then ¬ P is decidable,

and the question of whether they can be reversed. Read as principles
about all propositions, the discreteness of P → 𝟚 and the decidability
of ¬ P are both weak excluded middle, as shown above, and the
decidability of P is excluded middle. So (1) can be reversed as a
principle, although not for an individual proposition, because the
proof that P → 𝟚 is discrete under weak excluded middle uses it for
propositions other than P. The reversal of (0) as a principle says that
weak excluded middle implies excluded middle, which is the taboo above,
and for an individual proposition it is the hypothesis itself. So, as a
principle, the discreteness of P → 𝟚 is not strictly between the
decidability of P and that of ¬ P, because it is equivalent to the
decidability of ¬ P, and what is missing for the decidability of P is
the implication from weak excluded middle to excluded middle. We don't
know whether, conversely, this implication gives the hypothesis.

Finally, we discuss the original question, which was to find a type P
that we can prove to be thinly inhabited and whose pointedness gives a
constructive taboo. Anything that follows from the pointedness of such
a P is irrefutable, because thinly inhabited types are nonempty.

\begin{code}

consequences-of-thinly-inhabited-props-are-irrefutable
 : {P : 𝓤 ̇ } {X : 𝓥 ̇ }
 → is-thinly-inhabited P
 → (P → X)
 → ¬¬ X
consequences-of-thinly-inhabited-props-are-irrefutable ti f =
 ¬¬-functor f (thinly-inhabited-gives-nonempty ti)

\end{code}

So such a P can give only irrefutable statements, and in particular no
statement whose negation is consistent. The most it could give is one
that is irrefutable but not provable, and we don't have such a P.
