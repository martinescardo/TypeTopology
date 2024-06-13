Martin Escardo, 24th March 2022
with minor improvements and additions June 2024.

This file is a apropos the discussion at the end of the file
Ordinals.NotationInterpretation2.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Taboos.P2 (fe : Fun-Ext) where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import MLTT.Spartan
open import MLTT.Two
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
           (₀    ＝⟨ refl ⟩
            σ₀ x ＝⟨ happly e x ⟩
            σ₁ x ＝⟨ refl ⟩
            ₁    ∎)

nonemptiness-criterion : (X : 𝓤 ̇ ) → is-nonempty X ↔ (σ₀ ≠ σ₁)
nonemptiness-criterion {𝓤} X = I (emptiness-criterion X)
 where
  I : type-of (emptiness-criterion X) → ¬¬ X ↔ (σ₀ ≠ σ₁)
  I (f , g) = (λ (ν : ¬¬ X) (e : σ₀ ＝ σ₁) → ν (g e)) ,
              contrapositive f

\end{code}

The main notion studied in this file is the following, which we refer
to as "two-inhabitedness". We are mainly interested in this notion
when X is a proposition. (But we prove below that for certain types
called totally separated, if they are two-inhabited then they are
necessarily propositions.)

Another terminology we experimented with for this notion was "thinly
inhabited", but, as suggestive as it may be, there may be other
related notions which equally deserve this alternative
terminology. But the overall idea is that in some sense the type is
inhabited, but we may not be able get hold of any point of the type,
and in some sense there is at most one inhabitant anyway, similarly to
nonempty types

\begin{code}

is-inhabited₂ : 𝓤 ̇ → 𝓤 ̇
is-inhabited₂ X = is-equiv (σ X)

being-inhabited₂-is-prop : {X : 𝓤 ̇ } → is-prop (is-inhabited₂ X)
being-inhabited₂-is-prop {𝓤} {X} = being-equiv-is-prop fe' (σ X)

\end{code}

For a proposition P, we will use the synonym "holds₂ P" for
"is-inhabited₂ P".

\begin{code}

holds₂ : 𝓤 ̇ → 𝓤 ̇
holds₂ = is-inhabited₂

\end{code}

Exercise (easy but tedious, and hence I didn't implement it). A type X
is two-inhabited if and only if there is *any* equivalence 𝟚 ≃ (X → 𝟚).
If this gets added here, it should be added towards the end as an
appendix (but before the main open problem), to avoid unnecessary
distractions.

For propositions X, the two-inhabitedness of X is equivalent to the
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
           f p         ＝⟨ refl ⟩
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

retraction-of-σ-gives-inhabited₂ : {P : 𝓤 ̇ }
                                 → is-prop P
                                 → has-retraction (σ P)
                                 → holds₂ P
retraction-of-σ-gives-inhabited₂ {𝓤} {P} i (ρ , ρσ) =
 qinvs-are-equivs (σ P) (ρ , ρσ , retraction-of-σ-is-section i ρ ρσ)

\end{code}

For the converse we don't need X to be a proposition, of course.

\begin{code}

inhabited₂-gives-retraction-of-σ : {X : 𝓤 ̇ }
                                 → is-inhabited₂ X
                                 → has-retraction (σ X)
inhabited₂-gives-retraction-of-σ {𝓤} {X} = equivs-are-sections (σ X)

\end{code}

Next we want to show that P → holds₂ P for any proposition P,
and we use the following lemma.

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

point-gives-holds₂ : {P : 𝓤 ̇ }
                   → is-prop P
                   → P
                   → holds₂ P
point-gives-holds₂ {𝓤} {P} i p =
 retraction-of-σ-gives-inhabited₂ i (point-gives-retraction-of-σ p)

\end{code}

Notice, however, that pointed types X other than propositions are not
two-inhabited in general. An example is the type X := 𝟚, because there
are four maps X → 𝟚 in this case, and we need exactly two to have an
equivalence.

We will see later that the following implication can't be reversed,
even for just propositions, unless weak excluded middle holds, so that
being two-inhabited is stronger, in general, than being nonempty.

\begin{code}

inhabited₂-gives-nonempty : {X : 𝓤 ̇ }
                          → is-inhabited₂ X
                          → is-nonempty X
inhabited₂-gives-nonempty {𝓤} {X} e ν = zero-is-not-one II
 where
  I : inverse (σ X) e σ₀ ＝ inverse (σ X) e σ₁
  I = ap (inverse (σ X) e) (σ₀ ＝⟨ dfunext fe (λ x → 𝟘-elim (ν x)) ⟩
                            σ₁ ∎)

  II = ₀                       ＝⟨ (inverses-are-retractions (σ X) e ₀)⁻¹ ⟩
       inverse (σ X) e (σ X ₀) ＝⟨ I ⟩
       inverse (σ X) e (σ X ₁) ＝⟨ inverses-are-retractions (σ X) e ₁ ⟩
       ₁                       ∎

\end{code}

In some cases the implication

 X → is-inhabited₂ X

can be reversed:

\begin{code}

inhabited₂-emptiness-gives-emptiness : {X : 𝓤 ̇ }
                                     → is-inhabited₂ (is-empty X)
                                     → is-empty X
inhabited₂-emptiness-gives-emptiness h =
 three-negations-imply-one (inhabited₂-gives-nonempty h)

inhabited₂-nonemptiness-gives-nonemptiness : {X : 𝓤 ̇ }
                                           → is-inhabited₂ (is-nonempty X)
                                           → is-nonempty X
inhabited₂-nonemptiness-gives-nonemptiness {𝓤} {X} =
 inhabited₂-emptiness-gives-emptiness {𝓤} {is-empty X}

\end{code}

The following is a digression from our main aims. Recall that a type
is called discrete if it has decidable equality.

\begin{code}

X→𝟚-discreteness-criterion : {X : 𝓤 ̇ }
                           → is-empty X + is-inhabited₂ X
                           → is-discrete (X → 𝟚)
X→𝟚-discreteness-criterion (inl ν) f g = inl (dfunext fe (λ x → 𝟘-elim (ν x)))
X→𝟚-discreteness-criterion (inr h) f g = retract-is-discrete
                                          (≃-gives-▷ (σ _ , h))
                                          𝟚-is-discrete
                                          f g

P→𝟚-discreteness-criterion-necessity : {P : 𝓤 ̇ }
                                     → is-prop P
                                     → is-discrete (P → 𝟚)
                                     → ¬ P + holds₂ P
P→𝟚-discreteness-criterion-necessity {𝓤} {P} i δ = ϕ (δ σ₀ σ₁)
 where
  ϕ : is-decidable (σ₀ ＝ σ₁) → ¬ P + holds₂ P
  ϕ (inl e) = inl (fact e)
   where
    fact : σ₀ ＝ σ₁ → ¬ P
    fact e p = zero-is-not-one (ap (λ f → f p) e)
  ϕ (inr n) = inr (retraction-of-σ-gives-inhabited₂ i (γ , γσ))
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

Added 25th March 2022. If every nonempty proposition is inhabited₂,
then weak excluded middle holds. We use the following lemma to prove
this. Recall that the principle of weak excluded middle, which is
equivalent to De Morgan's Law, say that for every proposition P,
either ¬ P or ¬¬ P holds.

\begin{code}

inhabited₂-wem-lemma : (X : 𝓤 ̇)
                     → is-inhabited₂ (X + is-empty X)
                     → is-empty X + is-nonempty X
inhabited₂-wem-lemma X h = II
 where
  Y = X + ¬ X

  f : Y → 𝟚
  f (inl _) = ₀
  f (inr _) = ₁

  n : 𝟚
  n = inverse (σ Y) h f

  I : (k : 𝟚) → n ＝ k → ¬ X + is-nonempty X
  I ₀ e = inr ϕ
   where
    I₀ = f         ＝⟨ (inverses-are-sections (σ Y) h f)⁻¹ ⟩
         σ Y n     ＝⟨ ap (σ Y) e ⟩
         (λ _ → ₀) ∎

    ϕ : ¬¬ X
    ϕ u = zero-is-not-one
           (₀         ＝⟨ (ap (λ - → - (inr u)) I₀)⁻¹ ⟩
            f (inr u) ＝⟨ refl ⟩
            ₁         ∎)

  I ₁ e = inl u
   where
    I₁ = f         ＝⟨ (inverses-are-sections (σ Y) h f)⁻¹ ⟩
         σ Y n     ＝⟨ ap (σ Y) e ⟩
         (λ _ → ₁) ∎

    u : ¬ X
    u q = zero-is-not-one
           (₀         ＝⟨ refl ⟩
            f (inl q) ＝⟨ ap (λ - → - (inl q)) I₁ ⟩
            ₁         ∎)

  II : ¬ X + ¬¬ X
  II = I n refl

\end{code}

As promised above, two-inhabitedness is stronger than nonemptiness in
general, because WEM is not provable or disprovable, as it is true in
some models and false in others, and this is the main observation in
this file so far.

\begin{code}

irrefutable-props-hold₂-gives-WEM
 : ((P : 𝓤 ̇ ) → is-prop P → ¬¬ P → holds₂ P)
 → WEM 𝓤
irrefutable-props-hold₂-gives-WEM {𝓤} α Q i =
  inhabited₂-wem-lemma Q h
 where
  P = Q + ¬ Q

  ν : ¬¬ P
  ν ϕ = ϕ (inr (λ q → ϕ (inl q)))

  h : holds₂ P
  h = α P (decidability-of-prop-is-prop fe i) ν

\end{code}

Nathanael Rosnik proved the above independently within a few
hours of difference here:
https://gist.github.com/nrosnick/922250ddcc6bd04272199f59443d7510

A minor observation:

\begin{code}

inhabited₂-wem-special : (X : 𝓤 ̇)
                       → holds₂ (is-empty X + is-nonempty X)
                       → is-empty X + is-nonempty X
inhabited₂-wem-special X h =
 Cases (inhabited₂-wem-lemma (¬ X) h)
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
   v n = (u ∘ σ Y) n           ＝⟨ refl ⟩
         ρ (λ x → a x (σ Y n)) ＝⟨ ap ρ (dfunext fe (λ x → b x n)) ⟩
         ρ (λ _ → n)           ＝⟨ refl ⟩
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
to is-inhabited₂.

Added 13th June 2024. The homotopy circle S¹ is two-inhabited because,
as its a connected 1-type, all functions S¹ → 𝟚 are constant as 𝟚 is a
set. As another example, the type ℝ of Dedekind reals is a set, but
still there may be no function ℝ → 𝟚 other than the constant
functions, because "all functions ℝ → 𝟚 are continuous" is a
consistent axiom. But if a totally separated type (which is
necessarily a set) is two-inhabited, then it must be a proposition.

Recall that x ＝₂ y is defined to mean that p x = p y for all p : X → 𝟚,
that is, x and y satisfy the same boolean-valued properties. When
all x ＝₂ y holds for all x and y in X, we say that X is
connected₂. And recall that, in another extreme, when x ＝₂ y implies
x ＝ y for all x and y, we say that X is totally separated.w

\begin{code}

open import TypeTopology.TotallySeparated
open import TypeTopology.DisconnectedTypes

inhabited₂-types-are-connected₂ : {X : 𝓤 ̇ }
                                → is-inhabited₂ X
                                → is-connected₂ X
inhabited₂-types-are-connected₂ {𝓤} {X} tp x y = I
 where
  e : 𝟚 ≃ (X → 𝟚)
  e = σ X , tp

  I : (p : X → 𝟚) → p x ＝ p y
  I p = p x                 ＝⟨ happly ((inverses-are-sections' e p)⁻¹) x ⟩
        ⌜ e ⌝ (⌜ e ⌝⁻¹ p) x ＝⟨ refl ⟩
        ⌜ e ⌝⁻¹ p           ＝⟨ refl ⟩
        ⌜ e ⌝ (⌜ e ⌝⁻¹ p) y ＝⟨ happly (inverses-are-sections' e p) y ⟩
        p y                 ∎

totally-separated-inhabited₂-types-are-props : {X : 𝓤 ̇ }
                                             → is-totally-separated X
                                             → is-inhabited₂ X
                                             → is-prop X
totally-separated-inhabited₂-types-are-props ts tp x y = I
 where
  I : x ＝ y
  I = ts (inhabited₂-types-are-connected₂ tp x y)

\end{code}

TODO. Derive a constructive taboo from the hypothesis

      (P : 𝓤 ̇ ) → is-prop P → holds₂ P → P.

The difficulty, of course, is to come up with a type P which we can
prove to be two-inhabited but (we can't prove to be pointed and)
whose pointedness would give a constructive taboo.
