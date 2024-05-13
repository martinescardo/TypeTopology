Martin Escardo, 5th September 2023

We give a sufficient condition to derive algebraic flabbiness of a
type of the form type Σ x ꞉ X , A x from algebraic flabbiness of the
type X. (And hence (algebraic) injectivity from injectivity.)

This subsumes and improves and generalizes [1]. For further
motivation, the reader should check [1].

Two major improvements here are that

 1. We don't require the canonical map to be an equivalence - we
    merely require it to have a section (*). (So it is easier to apply
    the theorems as there are fewer things to check.)

 2. We don't restrict to a particular flabiness structure, whereas in [1]
    we use the Π-flabbiness structure.

We have rewritten [1] in [2] to exploit this.

[1] InjectiveTypes.MathematicalStructures.
[2] InjectiveTypes.MathematicalStructuresMoreGeneral.

(*) Which should not be confused with requiring that it merely has a
section. In any case, in TypeTopology we never say "merely" to
indicate propositional truncation. The sentence (*) uses "merely" in
its correct colloquial and official sense.

    merely (mîr′lē)
    adverb
     1. And nothing else or more; only.
     2. Purely; unmixedly; absolutely.
     3. Not otherwise than; simply; barely; only.

Given this meaning, I don't recommend using "merely" to indicate
propositional truncation. End of terminological digression (*).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module InjectiveTypes.Sigma
        (fe : FunExt)
       where

private
 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import InjectiveTypes.Blackboard fe
open import MLTT.Spartan
open import UF.Base
open import UF.Retracts
open import UF.Subsingletons
open import UF.SubtypeClassifier

\end{code}

We now introduce some abbreviations.

\begin{code}

extension : {X : 𝓤 ̇}
          → aflabby X 𝓦 → (p : Ω 𝓦) → (p holds → X) → X
extension = aflabby-extension

extends : {X : 𝓤 ̇} (ϕ : aflabby X 𝓦) (p : Ω 𝓦)
          (f : p holds → X) (h : p holds)
        → extension ϕ p f ＝ f h
extends  = aflabby-extension-property

\end{code}

Notice that extends ϕ p f amounts to the following commutative
triangle:

           p holds ---> 𝟙
               \       .
                \     .
              f  \   . extension ϕ p f
                  \ .
                   v
                   X.

We now assume that an algebraically flabbly type X is given. Recall
that algebraic flabbiness is data rather than merely property.

\begin{code}

module _ {X : 𝓤 ̇ }
         (A : X → 𝓥 ̇ )
         (ϕ : aflabby X 𝓦)
       where

\end{code}

We now give a sufficient *compatibility* condition to derive the
aflabbiness of Σ x ꞉ X , A x from that of X.

In order to extend f' as in the diagram below, first notice that it is
of the form ⟨ f , g ⟩ with f as in the previous diagram and
g : (h : p holds) → A (f h).


           p holds ---> 𝟙
               \       .
                \     .
 f' =: ⟨ f , g ⟩ \   .  (x , a)
                  \ .
                   v
               Σ x ꞉ X , A x.

Our compatibility condition says that the map ρ defined below has a
section, so that we can define the extension (x , a) by

 x = extension ϕ p f,
 a = the section of ρ applied to g.

\begin{code}

 ρ : (p : Ω 𝓦) (f : p holds → X)
   → A (extension ϕ p f) → ((h : p holds) → A (f h))
 ρ p f a h = transport A (extends ϕ p f h) a

\end{code}

Our first objective is to prove that Σ x ꞉ X , A x is aflabby if the
following compatibility condition holds. For a motivation for this
compatibility condition, see the file
InjectiveTypes.MathematicalStructures.

\begin{code}

 compatibility-condition : 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺)  ̇
 compatibility-condition = (p : Ω 𝓦)
                           (f : p holds → X)
                         → has-section (ρ p f)

\end{code}

That this compatibility condition is sufficient but not necessary is
illustrated in the file InjectiveTypes.InhabitednessTaboo, with the
type of pointed types (which is injective) shown to be equivalent to a
subtype of the type of inhabited types (which is "not" injective).

One of the main results of this file is that if A satisfies the
compatibility condition, then Σ x ꞉ X , A x is aflabby and hence
ainjective.

\begin{code}

 Σ-is-aflabby : compatibility-condition → aflabby (Σ A) 𝓦
 Σ-is-aflabby ρ-has-section = I
  where
   I : aflabby (Σ A) 𝓦
   I P P-is-prop f' = (extension ϕ p f , a) , II
    where
     p : Ω 𝓦
     p = (P , P-is-prop)

     have-f' : p holds → Σ A
     have-f' = f'

     f : p holds → X
     f = pr₁ ∘ f'

     g : (h : P) → A (f h)
     g = pr₂ ∘ f'

     σ : ((h : p holds) → A (f h)) → A (extension ϕ p f)
     σ = section-of (ρ p f) (ρ-has-section p f)

     η : ρ p f ∘ σ ∼ id
     η = section-equation (ρ p f) (ρ-has-section p f)

     a : A (extension ϕ p f)
     a = σ g

     II : (h : p holds) → (extension ϕ p f , a) ＝ f' h
     II h = extension ϕ p f , a ＝⟨ to-Σ-＝ (extends ϕ p f h , III) ⟩
            f h , g h           ＝⟨ refl ⟩
            f' h                ∎
      where
       III = transport A (extends ϕ p f h) a  ＝⟨ refl ⟩
             ρ p f a h                        ＝⟨ refl ⟩
             ρ p f (σ g) h                    ＝⟨ ap (λ - → - h) (η g) ⟩
             g h                              ∎

 Σ-ainjective : compatibility-condition → ainjective-type (Σ A) 𝓦 𝓦
 Σ-ainjective = aflabby-types-are-ainjective (Σ A) ∘ Σ-is-aflabby

\end{code}

If the type family A is a predicate, i.e. a family of propositions,
then the compatibility condition simplifies to just having a map in
the reverse direction of ρ p f with the requirement that it's a
section following automatically.

\begin{code}

 simplified-compatibility-condition : 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
 simplified-compatibility-condition =
    (p : Ω 𝓦)
    (f : p holds → X)
  → ((h : p holds) → A (f h)) → A (extension ϕ p f)

 compatibility-condition-gives-simplified-compatibility-condition :
    compatibility-condition
  → simplified-compatibility-condition
 compatibility-condition-gives-simplified-compatibility-condition c p f =
  section-of (ρ p f) (c p f)

 simplified-compatibility-condition-gives-compatibility-condition :
    ((x : X) → is-prop (A x))
  → simplified-compatibility-condition
  → compatibility-condition
 simplified-compatibility-condition-gives-compatibility-condition
  A-is-prop-valued c p f = I , II
   where
    I : ((h : p holds) → A (f h)) → A (extension ϕ p f)
    I = c p f
    II : ρ p f ∘ c p f ∼ id
    II g = dfunext fe'
                   (λ h → A-is-prop-valued (f h) ((ρ p f ∘ c p f) g h) (g h))

 subtype-is-aflabby : ((x : X) → is-prop (A x))
                    → simplified-compatibility-condition
                    → aflabby (Σ A) 𝓦
 subtype-is-aflabby A-is-prop-valued c =
  Σ-is-aflabby
   (simplified-compatibility-condition-gives-compatibility-condition A-is-prop-valued c)

\end{code}

Sometimes we want to prove that Σ x : X , A₁ x × A₂ x is
aflabby/ainjective when we already know that A₁ and A₂ satisfy the
compatibility conditions, and the following lemma can be used for that
purpose.

\begin{code}

compatibility-condition-×
 : {𝓤 𝓥₁ 𝓥₂ 𝓦 : Universe}
   {X : 𝓤 ̇ }
   (ϕ : aflabby X 𝓦)
   {A₁ : X → 𝓥₁ ̇ } {A₂ : X → 𝓥₂ ̇ }
 → compatibility-condition A₁ ϕ
 → compatibility-condition A₂ ϕ
 → compatibility-condition (λ x → A₁ x × A₂ x) ϕ
compatibility-condition-× {𝓤} {𝓥₁} {𝓥₂} {𝓦} {X} ϕ {A₁} {A₂}
                          ρ₁-has-section ρ₂-has-section = γ
 where
  A : X → 𝓥₁ ⊔ 𝓥₂ ̇
  A x = A₁ x × A₂ x

  module _ (p : Ω 𝓦)
           (f : p holds → X)
         where

   σ₁ : ((h : p holds) → A₁ (f h)) → A₁ (extension ϕ p f)
   σ₁ = section-of (ρ A₁ ϕ p f) (ρ₁-has-section p f)

   σ₂ : ((h : p holds) → A₂ (f h)) → A₂ (extension ϕ p f)
   σ₂ = section-of (ρ A₂ ϕ p f) (ρ₂-has-section p f)

   σ : ((h : p holds) → A (f h)) → A (extension ϕ p f)
   σ α = σ₁ (λ h → pr₁ (α h)) , σ₂ (λ h → pr₂ (α h))

   ρσ : ρ A ϕ p f ∘ σ ∼ id
   ρσ α = dfunext fe' I
    where
     α₁ = λ h → pr₁ (α h)
     α₂ = λ h → pr₂ (α h)

     I : ρ A ϕ p f (σ α) ∼ α
     I h =
      ρ A ϕ p f (σ α) h                                       ＝⟨ refl ⟩
      transport A (e h) (σ₁ α₁ , σ₂ α₂)                       ＝⟨ II ⟩
      transport A₁ (e h) (σ₁ α₁) , transport A₂ (e h) (σ₂ α₂) ＝⟨ refl ⟩
      ρ A₁ ϕ p f (σ₁ α₁) h , ρ A₂ ϕ p f (σ₂ α₂) h             ＝⟨ III ⟩
      α₁ h , α₂ h                                             ＝⟨ refl ⟩
      α h                                                     ∎
       where
        e : (h : p holds) → extension ϕ p f ＝ f h
        e = extends ϕ p f

        II  = transport-× A₁ A₂ (e h)
        III = ap₂ _,_
                 (ap (λ - → - h)
                     (section-equation (ρ A₁ ϕ p f) (ρ₁-has-section p f) α₁))
                 (ap (λ - → - h)
                     (section-equation (ρ A₂ ϕ p f) (ρ₂-has-section p f) α₂))

   γ : has-section (ρ A ϕ p f)
   γ = (σ , ρσ)

\end{code}

Sometimes we want to show that types of the form

  Σ x ꞉ X , Σ a ꞉ A x , B x a

is aflabby/ainjective, where the family B happens to be proposition valued and
the type Σ x : X , A x is already known to be aflabby/ainjective. (See the
discussion below for the case that B is not necessarily proposition valued.)
This can often be done directly using the simplified compatibility condition if
we consider types of the equivalent form

  Σ σ ꞉ (Σ x : X , A x) , C σ

again with C proposition valued.

\begin{code}

private
 example : {X : 𝓤 ̇ }
           {A : X → 𝓥 ̇ }
           (C : Σ A → 𝓣 ̇ )
         → (ϕ : aflabby (Σ A) 𝓦)
         → ((σ : Σ A) → is-prop (C σ))
         → simplified-compatibility-condition C ϕ
         → aflabby (Σ C) 𝓦
 example = subtype-is-aflabby

\end{code}

One practical example of this situation takes place when the type X is
a universe, the family A is the structure of pointed ∞-magmas, and C
gives the monoid axioms. So we first show that pointed ∞-magmas are
aflabby, then, using the above, we conclude that so is the subtype of
monoids, provided we also show that the monoid axioms satisfy the
simplified compatibility condition.

The following theorem strengthens both the hypothesis and the
conclusion of the above example, by showing that the full
compatibility condition is preserved if B is closed under extension in
a suitable sense. This gives an alternative way of successively
combining simple mathematical structures such as pointed types and
∞-magmas to get monoids, groups, rings, etc., to show that all the
axioms considered satisfy the compatibility condition and hence the
corresponding types of mathematical structures are aflabby, as
exemplified in the module InjectiveTypes.MathematicalStructuresMoreGeneral.

\begin{code}

compatibility-condition-with-axioms
 : {X : 𝓤 ̇ }
   (ϕ : aflabby X 𝓥)
   (A : X → 𝓦 ̇ )
   (ρ-has-section : compatibility-condition A ϕ)
   (B : (x : X ) → A x → 𝓥 ̇ )
   (B-is-prop-valued : (x : X) (a : A x) → is-prop (B x a))
   (B-is-closed-under-extension
     : (p : Ω 𝓥 )
       (f : p holds → X)
     → (α : (h : p holds) → A (f h))
     → ((h : p holds) → B (f h) (α h))
     → B (extension ϕ p f) (section-of (ρ A ϕ p f) (ρ-has-section p f) α))
 → compatibility-condition (λ x → Σ a ꞉ A x , B x a) ϕ
compatibility-condition-with-axioms
 {𝓤} {𝓥} {𝓦} {X}
 ϕ
 A
 ρ-has-section
 B
 B-is-prop-valued
 B-is-closed-under-extension = ρ'-has-section
  where
   A' : X → 𝓥 ⊔ 𝓦 ̇
   A' x = Σ a ꞉ A x , B x a

   module _ (p : Ω 𝓥)
            (f : p holds → X)
          where

    σ : ((h : p holds) → A (f h)) → A (extension ϕ p f)
    σ = section-of (ρ A ϕ p f) (ρ-has-section p f)

    ρ' : A' (extension ϕ p f) → ((h : p holds) → A' (f h))
    ρ' = ρ A' ϕ p f

    τ : (α : (h : p holds) → A' (f h))
      → B (extension ϕ p f) (σ (λ h → pr₁ (α h)))
    τ α = B-is-closed-under-extension p f
           (λ h → pr₁ (α h))
           (λ h → pr₂ (α h))

    σ' : ((h : p holds) → A' (f h)) → A' (extension ϕ p f)
    σ' α = σ (λ h → pr₁ (α h)) , τ α

    ρσ' : ρ' ∘ σ' ∼ id
    ρσ' α = dfunext fe' I
     where
      α₁ = λ h → pr₁ (α h)
      α₂ = λ h → pr₂ (α h)

      I : ρ' (σ' α) ∼ α
      I h =
       ρ' (σ' α) h                     ＝⟨ refl ⟩
       ρ' (σ α₁ , τ α) h               ＝⟨ refl ⟩
       transport A' (e h) (σ α₁ , τ α) ＝⟨ II ⟩
       (transport A (e h) (σ α₁) , τ') ＝⟨ refl ⟩
       (ρ A ϕ p f (σ α₁) h , _)        ＝⟨ III ⟩
       (α₁ h , α₂ h)                   ＝⟨ refl ⟩
       α h                             ∎
        where
         e : (h : p holds) → extension ϕ p f ＝ f h
         e = extends ϕ p f

         τ' : B (f h) (transport A (extends ϕ p f h) (σ α₁))
         τ' = transportd A B (σ α₁) (e h) (τ α)

         II  = transport-Σ A B (f h) (e h) (σ α₁)
         III = to-subtype-＝
                (B-is-prop-valued (f h))
                (ap (λ - → - h)
                    (section-equation (ρ A ϕ p f) (ρ-has-section p f) α₁))

    ρ'-has-section : has-section ρ'
    ρ'-has-section = σ' , ρσ'

\end{code}

Discussion. It is easy to prove (TODO) that

 ΣΣ-is-aflabby
  : {X : 𝓤 ̇ }
    (A : X → ? ̇ ) (B : (x : X) → A x → ? ̇ )
  → (ϕ : aflabby X ?)
  → (hs : ρ-has-section A ϕ)
  → ρ-has-section (λ ((x , a) : Σ A) → B x a) (Σ-is-aflabby A ϕ hs) -- (*)
  → aflabby (Σ x ꞉ X , Σ a ꞉ A x , B x a) ?

where the question marks are universes that Agda should be able to
resolve, or at least give contraints to.

However, the hypothesis (*) will not be very useful in practice, as in
many cases it will be difficult to check. So a good thing to do would
be to formulate and prove an equivalent condition that would be easier
to work with. Or even a weaker condition that is good enough in
practice.
