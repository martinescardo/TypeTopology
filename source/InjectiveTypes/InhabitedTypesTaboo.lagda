Tom de Jong & Martín Escardó, 8 & 10 September 2023.

Formalising a discussion of 7 September.


As explained in InjectiveTypes.CounterExamples:

────────────────────────────────────────────────────────────────────────────────

We already know that if excluded middle holds then all pointed types are
algebraically injective, and that the converse also holds.

So we can't really give an example of any type which is not algebraicxally
injective, other than the empty type. The best we can hope for is to derive a
constructive taboo, rather than a contradiction, from the assumption that a type
of interest would be injective.

Most types one encounters in practice are "not" injective in the above sense. We
can also say "not all types are injective in general", as there are some
∞-toposes which do satisfy excluded middle, as well as some ∞-toposes which
don't, and we intend TypeTopology to apply to all ∞-toposes, except when special
assumptions are made.

────────────────────────────────────────────────────────────────────────────────

Here we consider the type 𝕀  of inhabited types defined by

 𝕀 = Σ X ꞉ 𝓤 ̇ , ∥ X ∥

and show that the following are equivalent:

(1) 𝕀 is injective.
(2) 𝕀 is a retract of 𝓤.
(3) All propositions are projective:
      (P : 𝓤 ̇  ) (Y : P → 𝓤 ̇  ) → is-prop P
                                → ((p : P) → ∥ Y p ∥)
                                → ∥ (p : P) → Y p ∥.
(4) Every type has unspecified split support:
      (X : 𝓤 ̇  ) → ∥ ∥ X ∥ → X ∥.

The equivalence of (3) and (4) was shown in [Theorem 7.7, 1].

As noted in [1], if Y p in statement (3) is a two-element set, then this is
known as the "world's simplest axiom of choice", which fails in some toposes, as
shown in [2].

Also notice that (3) (and thus, (4)) follows from excluded middle.


It is noteworthy that this yields an example of an injective Σ-type whose index
type is "not" injective, as follows: The type of pointed types
  𝓤∙ = Σ X ꞉ 𝓤 ̇ , X
is injective, as proved in InjectiveTypes.MathematicalStructures, and is
(equivalent) to the Σ-type
  Σ I ꞉ 𝕀 , pr₁ 𝕀,
indexed over the "non"-injective type 𝕀.


To illustrate the constructive differences between the propositional truncation
and the double negation, we show ─ in contrast to the above ─ that the type of
non-empty types *is* injective.


References
──────────
[1] Nicolai Kraus, Martín Escardó, Thierry Coquand and Thorsten Altenkirch.
    Notions of Anonymous Existence in Martin-Löf Type Theory.
    Logical Methods in Computer Science 13(1), pp. 1─36, 2017.
    https://doi.org/10.23638/LMCS-13(1:15)2017

[2] M. P. Fourman and A. Ščedrov.
    The “world's simplest axiom of choice” fails.
    Manuscripta Math 38, pp. 325–332, 1982.
    https://doi.org/10.1007/BF01170929

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Univalence
open import UF.PropTrunc

module InjectiveTypes.InhabitedTypesTaboo
        (pt : propositional-truncations-exist)
        (ua : Univalence)
        (𝓤 : Universe)
       where

open PropositionalTruncation pt

open import MLTT.Negation

open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

 pe' : Prop-Ext
 pe' {𝓤} = pe 𝓤

open import InjectiveTypes.Blackboard fe
open import InjectiveTypes.MathematicalStructures ua

\end{code}

We define the type of inhabited of types (in a fixed, but arbitrary universe 𝓤).
For convenience we also write 𝕀 for this type in this file.

\begin{code}

Inhabited : 𝓤 ⁺ ̇
Inhabited = Σ X ꞉ 𝓤 ̇  , ∥ X ∥

private
 𝕀 : 𝓤 ⁺ ̇
 𝕀 = Inhabited

⟨_⟩ : 𝕀 → 𝓤 ̇
⟨_⟩ = pr₁

\end{code}

We define the two (equivalent) choice principles, labelled (3) and (4) at the
top of this file.

\begin{code}

Propositions-Are-Projective : 𝓤 ⁺ ̇
Propositions-Are-Projective = (P : 𝓤 ̇  ) (Y : P → 𝓤 ̇  )
                            → is-prop P
                            → ((p : P) → ∥ Y p ∥)
                            → ∥ ((p : P) → Y p) ∥

Unspecified-Split-Support : 𝓤 ⁺ ̇
Unspecified-Split-Support = (X : 𝓤 ̇  ) → ∥ (∥ X ∥ → X) ∥

\end{code}

We now prove the equivalence of statemements (1)─(4) and summarise the chain of
implications at the end.

\begin{code}

unspecified-split-support-gives-retract : Unspecified-Split-Support
                                        → retract 𝕀 of (𝓤 ̇  )
unspecified-split-support-gives-retract uss = ρ , σ , ρσ
 where
  σ : 𝕀 → 𝓤 ̇
  σ = ⟨_⟩
  ρ  : 𝓤 ̇ → 𝕀
  ρ X = (∥ X ∥ → X) , uss X
  ρσ : ρ ∘ σ ∼ id
  ρσ (X , s) = to-subtype-＝ (λ Y → ∥∥-is-prop)
                             (eqtoid (ua 𝓤) (∥ X ∥ → X) X e)
   where
    e = (∥ X ∥ → X) ≃⟨ I ⟩
        (𝟙{𝓤} → X)    ≃⟨ ≃-sym (𝟙→ fe') ⟩
        X             ■
     where
      I = →cong'' fe' fe' (idtoeq ∥ X ∥ 𝟙 II)
       where
        II : ∥ X ∥ ＝ 𝟙
        II = holds-gives-equal-𝟙 pe' ∥ X ∥ ∥∥-is-prop s

retract-gives-injectivity : retract 𝕀 of (𝓤 ̇ )
                          → ainjective-type 𝕀 𝓤 𝓤
retract-gives-injectivity ret = retract-of-ainjective 𝕀 (𝓤 ̇ ) inj ret
 where
  inj : ainjective-type (𝓤 ̇ ) 𝓤 𝓤
  inj = universes-are-ainjective-Π (ua 𝓤)

flabbiness-gives-projective-propositions : aflabby 𝕀 𝓤
                                         → Propositions-Are-Projective
flabbiness-gives-projective-propositions ϕ P Y P-is-prop Y-inh = I
 where
  f : P → 𝕀
  f p = (Y p , Y-inh p)
  ext : Σ X ꞉ 𝕀 , ((p : P) → X ＝ f p)
  ext = ϕ P P-is-prop f
  X : 𝓤 ̇
  X = pr₁ (pr₁ ext)
  s : ∥ X ∥
  s = pr₂ (pr₁ ext)
  ext-property : (p : P) → (X , s) ＝ (Y p , Y-inh p)
  ext-property = pr₂ ext
  ext-property' : (p : P) → X ＝ Y p
  ext-property' p = ap ⟨_⟩ (ext-property p)

  II : X → (p : P) → Y p
  II x p = idtofun X (Y p) (ext-property' p) x

  I : ∥ ((p : P) → Y p) ∥
  I = ∥∥-functor II s

injectivity-gives-projective-propositions : ainjective-type 𝕀 𝓤 𝓤
                                          → Propositions-Are-Projective
injectivity-gives-projective-propositions inj =
 flabbiness-gives-projective-propositions (ainjective-types-are-aflabby 𝕀 inj)

projective-propositions-gives-unspecified-split-support :
 Propositions-Are-Projective → Unspecified-Split-Support
projective-propositions-gives-unspecified-split-support pap X =
 pap ∥ X ∥ (λ _ → X) ∥∥-is-prop id

\end{code}

For convenience, we provide a summary of the chain of implications:

\begin{code}

summary : (Unspecified-Split-Support → retract 𝕀 of (𝓤 ̇  ))
        × (retract 𝕀 of (𝓤 ̇  ) → ainjective-type 𝕀 𝓤 𝓤)
        × (ainjective-type 𝕀 𝓤 𝓤 → Propositions-Are-Projective)
        × (Propositions-Are-Projective → Unspecified-Split-Support)
summary = unspecified-split-support-gives-retract
        , retract-gives-injectivity
        , injectivity-gives-projective-propositions
        , projective-propositions-gives-unspecified-split-support

\end{code}

Oberve that the concatenation of the first three implications yields an
alternative (w.r.t. [1]), non-direct proof of the following:

\begin{code}

unspecified-split-support-gives-projective-propositions :
 Unspecified-Split-Support → Propositions-Are-Projective
unspecified-split-support-gives-projective-propositions uss =
 injectivity-gives-projective-propositions
  (retract-gives-injectivity
    (unspecified-split-support-gives-retract uss))

\end{code}

Finally, we recall that the type 𝓤∙ of pointed types *is* injective and record
that 𝓤∙ is equivalent to the Σ-type
  Σ I ꞉ 𝕀 , pr₁ 𝕀,
which is indexed over the "non"-injective type 𝕀.

Hence, this gives an example of an injective Σ-type whose indexing type is "not"
injective.

\begin{code}

𝓤∙ : 𝓤 ⁺ ̇
𝓤∙ = Σ X ꞉ 𝓤 ̇  , X

𝓤∙-is-injective : ainjective-type 𝓤∙ 𝓤 𝓤
𝓤∙-is-injective = ainjectivity-of-type-of-pointed-types

𝓤∙-as-Σ-type-over-𝕀 : 𝓤∙ ≃ (Σ I ꞉ 𝕀 , ⟨ I ⟩)
𝓤∙-as-Σ-type-over-𝕀 = 𝓤∙                      ≃⟨ Σ-cong e ⟩
                      (Σ X ꞉ 𝓤 ̇  , ∥ X ∥ × X) ≃⟨ ≃-sym Σ-assoc ⟩
                      (Σ I ꞉ 𝕀 , ⟨ I ⟩)       ■
 where
  e : (X : 𝓤 ̇  ) → X ≃ ∥ X ∥ × X
  e X = qinveq f (g , η , ε)
   where
    f : X → ∥ X ∥ × X
    f x = ∣ x ∣ , x
    g : ∥ X ∥ × X → X
    g = pr₂
    η : g ∘ f ∼ id
    η x = refl
    ε : f ∘ g ∼ id
    ε (s , x) = to-×-＝ (∥∥-is-prop ∣ x ∣ s) refl

\end{code}

In contrast to the fact that the type of inhabited types is "not" injective, the
type of non-empty types *is* injective. Notice how we prove this by establishing
Non-Empty as a retract of the universe without having to take recourse to a
choice principle like we did in the construction
unspecified-split-support-gives-retract.

This also serves to highlight the (constructive) difference(s) between
propositional truncation and double negation.

\begin{code}

Non-Empty : 𝓤 ⁺ ̇
Non-Empty = Σ X ꞉ 𝓤 ̇  , is-nonempty X

Non-Empty-retract : retract Non-Empty of (𝓤 ̇  )
Non-Empty-retract = ρ , σ , ρσ
 where
  ρ : 𝓤 ̇ → Non-Empty
  ρ X = (¬¬ X → X) , p
   where
    p : ¬¬ (¬¬ X → X)
    p = double-negation-of-implication→ q
     where
      q : ¬ (¬¬ (¬¬ X) × ¬ X)
      q (h₁ , h₂) = h₁ (¬¬-intro h₂)
  σ : Non-Empty → 𝓤 ̇
  σ = pr₁
  ρσ : ρ ∘ σ ∼ id
  ρσ (X , X-non-empty) = to-subtype-＝ (λ Y → negations-are-props fe')
                                       (eqtoid (ua 𝓤) (¬¬ X → X) X e)
   where
    e = (¬¬ X → X) ≃⟨ I ⟩
        (𝟙{𝓤} → X) ≃⟨ ≃-sym (𝟙→ fe') ⟩
        X          ■
     where
      I = →cong'' fe' fe' (idtoeq (¬¬ X) 𝟙 II)
       where
        II : ¬¬ X ＝ 𝟙
        II = holds-gives-equal-𝟙 pe' (¬¬ X) (negations-are-props fe') X-non-empty

Non-Empty-is-injective : ainjective-type Non-Empty 𝓤 𝓤
Non-Empty-is-injective =
 retract-of-ainjective Non-Empty (𝓤 ̇  )
                       (universes-are-ainjective-Π (ua 𝓤))
                       Non-Empty-retract

\end{code}
