Martin Escardo, 24th March 2022 with minor improvements June 2024.

This file is a apropos the discussion at the end of the file
Ordinals.NotationInterpretation2.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module Taboos.P2 (fe : Fun-Ext) where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import MLTT.Two
open import MLTT.Two-Properties

open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.ClassicalLogic
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

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

Recall that we say that a type X is empty to mean ¬ X, that is X → 𝟘,
and nonempty to mean ¬¬ X.

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

The main notion studied in this file is the following.

\begin{code}

is-thinly-populated : 𝓤 ̇ → 𝓤 ̇
is-thinly-populated X = is-equiv (σ X)

being-thinly-populated-is-prop : {X : 𝓤 ̇ } → is-prop (is-thinly-populated X)
being-thinly-populated-is-prop {𝓤} {X} = being-equiv-is-prop fe' (σ X)

\end{code}

For propositions X, this is equivalent to the map σ X having a
retraction ρ.

                            σ X
                          𝟚  ↪  (X → 𝟚)
                          𝟚  ↞  (X → 𝟚)
                             ρ

In general there can be many maps ρ with ρ ∘ σ X ∼ id, but there is at
most one if X is a proposition:

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

retraction-of-σ-gives-thin-populatedness : {P : 𝓤 ̇ }
                                         → is-prop P
                                         → has-retraction (σ P)
                                         → is-thinly-populated P
retraction-of-σ-gives-thin-populatedness {𝓤} {P} i (ρ , ρσ) =
 qinvs-are-equivs (σ P) (ρ , ρσ , retraction-of-σ-is-section i ρ ρσ)

\end{code}

For the converse we don't need X to be a proposition, of course.

\begin{code}

thin-populatedness-gives-retraction-of-σ : {X : 𝓤 ̇ }
                                         → is-thinly-populated X
                                         → has-retraction (σ X)
thin-populatedness-gives-retraction-of-σ {𝓤} {X} = equivs-are-sections (σ X)

point-gives-retraction-of-σ : {X : 𝓤 ̇ }
                            → X
                            → has-retraction (σ X)
point-gives-retraction-of-σ {𝓤} {X} x = (γ , γσ)
 where
  γ : (X → 𝟚) → 𝟚
  γ f = f x

  γσ : γ ∘ σ X ∼ id
  γσ n = refl

\end{code}

Notice, however, that pointed types X other than propositions are not
thinly-populated in general. An example is the type X := 𝟚, because there
are four maps X → 𝟚 in this case, and we need exactly two to have an
equivalence.

\begin{code}

point-gives-thinly-populated : {P : 𝓤 ̇ }
                             → is-prop P
                             → P
                             → is-thinly-populated P
point-gives-thinly-populated {𝓤} {P} i p =
 retraction-of-σ-gives-thin-populatedness i (point-gives-retraction-of-σ p)

\end{code}

We will later see that the following implication can't be reversed
unless weak excluded middle holds, so that being thinly populated is
stronger, in general, than being nonempty.

\begin{code}

thinly-populated-gives-nonempty : {X : 𝓤 ̇ }
                                → is-thinly-populated X
                                → is-nonempty X
thinly-populated-gives-nonempty {𝓤} {X} e ν = zero-is-not-one II
 where
  I : inverse (σ X) e σ₀ ＝ inverse (σ X) e σ₁
  I = ap (inverse (σ X) e) (σ₀ ＝⟨ dfunext fe (λ x → 𝟘-elim (ν x)) ⟩
                            σ₁ ∎)

  II = ₀                       ＝⟨ (inverses-are-retractions (σ X) e ₀)⁻¹ ⟩
       inverse (σ X) e (σ X ₀) ＝⟨ I ⟩
       inverse (σ X) e (σ X ₁) ＝⟨ inverses-are-retractions (σ X) e ₁ ⟩
       ₁                       ∎

\end{code}

In some cases the above implication P → is-thinly-populated P can be
reversed:

\begin{code}

thinly-populated-emptiness-gives-emptiness : {X : 𝓤 ̇ }
                                           → is-thinly-populated (is-empty X)
                                           → is-empty X
thinly-populated-emptiness-gives-emptiness h =
 three-negations-imply-one (thinly-populated-gives-nonempty h)

thinly-populated-nonemptiness-gives-nonemptiness : {X : 𝓤 ̇ }
                                                 → is-thinly-populated (is-nonempty X)
                                                 → is-nonempty X
thinly-populated-nonemptiness-gives-nonemptiness {𝓤} {X} =
 thinly-populated-emptiness-gives-emptiness {𝓤} {is-empty X}

X→𝟚-discreteness-criterion : {X : 𝓤 ̇ }
                           → is-empty X + is-thinly-populated X
                           → is-discrete (X → 𝟚)
X→𝟚-discreteness-criterion (inl ν) f g = inl (dfunext fe (λ x → 𝟘-elim (ν x)))
X→𝟚-discreteness-criterion (inr h) f g = retract-is-discrete
                                          (≃-gives-▷ (σ _ , h))
                                          𝟚-is-discrete
                                          f g

P→𝟚-discreteness-criterion-necessity : {P : 𝓤 ̇ }
                                     → is-prop P
                                     → is-discrete (P → 𝟚)
                                     → ¬ P + is-thinly-populated P
P→𝟚-discreteness-criterion-necessity {𝓤} {P} i δ = ϕ (δ σ₀ σ₁)
 where
  ϕ : is-decidable (σ₀ ＝ σ₁) → ¬ P + is-thinly-populated P
  ϕ (inl e) = inl (fact e)
   where
    fact : σ₀ ＝ σ₁ → ¬ P
    fact e p = zero-is-not-one (ap (λ f → f p) e)
  ϕ (inr n) = inr (retraction-of-σ-gives-thin-populatedness i (γ , γσ))
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

Added 25th March 2022. If every irrefutable proposition is
thinly-populated, then weak excluded middle holds.

\begin{code}

thin-populatedness-wem-lemma : (X : 𝓤 ̇)
                             → is-thinly-populated (X + is-empty X)
                             → is-empty X + is-nonempty X
thin-populatedness-wem-lemma X h = II
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

As promised above, thin population is stronger than nonemptiness in
general:

\begin{code}

nonempty-props-are-thinly-populated-gives-WEM
 : ((P : 𝓤 ̇ ) → is-prop P → is-nonempty P → is-thinly-populated P)
 → WEM 𝓤
nonempty-props-are-thinly-populated-gives-WEM {𝓤} α Q i =
  thin-populatedness-wem-lemma Q h
 where
  P = Q + ¬ Q

  ν : ¬¬ P
  ν ϕ = ϕ (inr (λ q → ϕ (inl q)))

  h : is-thinly-populated P
  h = α P (decidability-of-prop-is-prop fe i) ν

\end{code}

Nathanael Rosnik proved the above independently within a few
hours of difference here:
https://gist.github.com/nrosnick/922250ddcc6bd04272199f59443d7510

A special case of the lemma:

\begin{code}

thin-populatedness-wem-special : (X : 𝓤 ̇)
                               → is-thinly-populated (is-empty X + is-nonempty X)
                               → is-empty X + is-nonempty X
thin-populatedness-wem-special X h =
 Cases (thin-populatedness-wem-lemma (¬ X) h)
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
to is-thinly-inhabited.

Added 13th June 2024. The homotopy circle S¹ is thinly populated
because, being a connected 1-type, all functions S¹ → 𝟚 are constant
as 𝟚 is a set. As another example, the type ℝ of Dedekind reals is a
set, but still there may be no function ℝ → 𝟚 other than the constant
functions, because "all functions ℝ → 𝟚" are continuous is a
consistent axiom. But if a totally separated type (which is
necessarily a set) is thinly populated, then it must be a proposition.

\begin{code}

open import TypeTopology.TotallySeparated

thin-totally-separated-types-are-props : {X : 𝓤 ̇ }
                                       → is-totally-separated X
                                       → is-thinly-populated X
                                       → is-prop X
thin-totally-separated-types-are-props {𝓤} {X} ts tp x y = II
 where
  e : 𝟚 ≃ (X → 𝟚)
  e = σ X , tp

  I : (f : X → 𝟚) → f x ＝ f y
  I f = f x                 ＝⟨ happly ((inverses-are-sections' e f)⁻¹) x ⟩
        ⌜ e ⌝ (⌜ e ⌝⁻¹ f) x ＝⟨ refl ⟩
        ⌜ e ⌝⁻¹ f           ＝⟨ refl ⟩
        ⌜ e ⌝ (⌜ e ⌝⁻¹ f) y ＝⟨ happly (inverses-are-sections' e f) y ⟩
        f y                 ∎

  II : x ＝ y
  II = ts I

\end{code}

TODO. Derive a constructive taboo from the hypothesis

      (P : 𝓤 ̇ ) → is-prop P → is-thinly-populated P → P.
