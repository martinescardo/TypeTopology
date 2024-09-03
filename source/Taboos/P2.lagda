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

thinly-inhabited-wem-lemma : (X : 𝓤 ̇)
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
            f (inr u) ＝⟨ refl ⟩
            ₁         ∎)

  I ₁ e = inl u
   where
    I₁ = f         ＝⟨ (inverses-are-sections (σ Y) ti f)⁻¹ ⟩
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

As promised above, thin inhabitedness is stronger than nonemptiness in
general, because WEM is not provable or disprovable, as it is true in
some models and false in others, and this is the main observation in
this file so far.

\begin{code}

irrefutable-props-are-thinly-inhabited-gives-WEM
 : ((P : 𝓤 ̇ ) → is-prop P → ¬¬ P → is-thinly-inhabited P)
 → WEM 𝓤
irrefutable-props-are-thinly-inhabited-gives-WEM {𝓤} α = I
 where
  module _ (Q : 𝓤 ̇ ) (i : is-prop Q) where
   P = Q + ¬ Q

   ν : ¬¬ P
   ν ϕ = ϕ (inr (λ q → ϕ (inl q)))

   h : is-thinly-inhabited P
   h = α P (decidability-of-prop-is-prop fe i) ν

  I : WEM 𝓤
  I = WEM'-gives-WEM fe (λ Q i → thinly-inhabited-wem-lemma Q (h Q i))

\end{code}

Nathanael Rosnik proved the above independently within a few
hours of difference here:
https://gist.github.com/nrosnick/922250ddcc6bd04272199f59443d7510

A minor observation, giving another instance of an implication
is-thinly-inhabited P → P.

\begin{code}

thinly-inhabited-wem-special : (X : 𝓤 ̇)
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
        ⌜ e ⌝ (⌜ e ⌝⁻¹ p) x ＝⟨ refl ⟩
        ⌜ e ⌝⁻¹ p           ＝⟨ refl ⟩
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
         ⌜ e ⌝ (⌜ e ⌝⁻¹ p) x ＝⟨ refl ⟩
         ⌜ e ⌝⁻¹ p           ＝⟨ refl ⟩
         ⌜ e ⌝ (⌜ e ⌝⁻¹ p) y ＝⟨ happly (inverses-are-sections' e p) y ⟩
         p y                 ∎

   II : (x ＝ x) ＝ (x ＝ y)
   II = I (x ＝_)

   III : x ＝ y
   III = idtofun' II refl

 η : {X : 𝓤 ̇ } → is-prop X → X → is-thinly-inhabited' X
 η {𝓤} {X} i x₀ = qinvs-are-equivs (κ X) (s , sκ , κs)
  where
   s : (X → 𝓤 ̇) → 𝓤 ̇
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

We now come back to the original notion of thin inhabitedness studied
in this file.

TODO. Derive a constructive taboo from the hypothesis

      (P : 𝓤 ̇ ) → is-prop P → is-thinly-inhabited P → P.

The difficulty, of course, is to come up with a type P which we can
prove to be thinly inhabited but (we can't prove to be pointed and)
whose pointedness would give a constructive taboo.
