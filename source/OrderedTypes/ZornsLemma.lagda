Kelton OBrien, 31 May 2024

A proof that the Axiom of Choice implies Zorn's Lemma, as well as
relevant definitions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Ordinals.Equivalence
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Base
open import UF.Choice
open import UF.ClassicalLogic
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.UA-FunExt
open import UF.Univalence
open import UF.UniverseEmbedding

module OrderedTypes.ZornsLemma
 {𝓤 𝓣 : Universe}
 (pt : propositional-truncations-exist)
 (ua : Univalence)
 {X : 𝓤 ̇ }
 (_≪_ : X → X → 𝓣 ̇ )
  where

open PropositionalTruncation pt
open import Ordinals.BuraliForti ua
open import Ordinals.OrdinalOfOrdinals ua
open import UF.ImageAndSurjection pt

fe : FunExt
fe = Univalence-gives-FunExt ua
pe : Prop-Ext
pe = Univalence-gives-Prop-Ext ua
pe' : PropExt
pe' 𝓤 = pe {𝓤}
fe' : Fun-Ext
fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open UF.Choice.ExcludedMiddle pt fe
open UF.Choice.Univalent-Choice fe pt
open UF.Choice.choice-functions pt pe' fe
open UF.Logic.Existential pt
open UF.Logic.Universal fe'
open import OrderedTypes.Poset fe'
open import Ordinals.WellOrderingTaboo fe' pe
open inhabited-subsets pt

open PosetAxioms
open ClassicalWellOrder pt

_⋘_ : X → X → (𝓤 ⊔ 𝓣) ̇
a ⋘ b =  a ≪ b × (a ≠ b)

is-chain : {𝓥 : Universe} → (Y : 𝓟 {𝓥} X ) →  (𝓤 ⊔ 𝓣 ⊔ 𝓥) ̇
is-chain Y = (x y : X) → x ∈ Y → y ∈ Y → (x ≪ y ∨ y ≪ x)

has-maximal-element-strong :  (𝓤 ⊔ 𝓣) ̇
has-maximal-element-strong = Σ x ꞉ X , ((y : X) → x ≪ y → x ＝ y)

has-maximal-element : (𝓤 ⊔ 𝓣) ̇
has-maximal-element = ∃ x ꞉ X , ((y : X) → x ≪ y → x ＝ y)

all-chains-have-upper-bound : {𝓥 : Universe} → (𝓤 ⊔ 𝓣 ⊔ (𝓥 ⁺)) ̇
all-chains-have-upper-bound {𝓥} =
 (Y : 𝓟 {𝓥} X) → (is-chain Y) → Σ x ꞉ X , (∀ y → y ∈ Y → y ≪ x)

\end{code}

The following is a formalization of the standard transfinite-induction-based
proof of Zorn's lemma. The closest informal analog to the proof can be found
here: https://math.stackexchange.com/a/2889205.
The primary differences between this proof and that proof are just ones of
how sets are treated (notice the lack of a particular poset P),
additional detail in things that are glossed over in the formal proof,
(e.g the proof that the chain allfbs is a chain is not given).
The proof idea is the same.

We do a proof by contradiction (which is why we have that double negation),
where we assume that even though all chains have a least upper bound,
the set at hand does not have a maximal element.
These assumptions allow us to construct a function `f' from the ordinals to X,
which is a set, which preserves order, is therefore left-cancellable, and again
in turn an equivalence. `f' being order preserving relies on the fact
that there is no maximal element, as otherwise `f' would (as defined)
map many ordinals to the maximal element.  An equivalence between the
ordinals and a set is impossible, so there must (not-not) be a
maximum.

While this is the core of the proof logic, the final result to be used
elsewhere is found below, and takes in more reasonable inputs.

\begin{code}

choice-function-gives-zorns-lemma
 : Excluded-Middle
 → poset-axioms (_≪_)
 → all-chains-have-upper-bound
 → (Σ ε ꞉ (𝓟 {𝓣 ⊔ 𝓤} X → X) , ((A : 𝓟 X) → is-inhabited A → ε A ∈ A))
 → has-maximal-element

choice-function-gives-zorns-lemma
 lem
 (X-is-set , ≪-prop , ≪-refl , ≪-trans , ≪-antisym )
 chains
 (ε , ε-behaviour) =
  (¬¬Σ→∃ pt dn (λ no-max → absurd no-max))
   where
    dn : {𝓥 : Universe} → DNE 𝓥
    dn {𝓥} = EM-gives-DNE lem

    eq-is-¬¬-stable : {x : X} {y : X} →  ¬¬-stable (x ＝ y)
    eq-is-¬¬-stable {x} {y} ¬¬x=y = dn (x ＝ y) (X-is-set) ¬¬x=y

    ≪-is-¬¬-stable : {x : X} {y : X} → ¬¬-stable (x ≪ y)
    ≪-is-¬¬-stable {x} {y} ¬¬ll = dn (x ≪ y) (≪-prop x y) ¬¬ll

    ⋘-prop : (a : X) → (b : X) → is-prop (a ⋘ b)
    ⋘-prop a b = ×-is-prop (≪-prop a b) (negations-are-props fe')

    ≪-trans-⋘ : (x y z : X) →  x ≪ y → y ⋘ z → x ⋘ z
    ≪-trans-⋘ x y z x≪y (y≪z , y≠z) =
     ≪-trans x y z x≪y y≪z ,
      λ x=z → y≠z ((≪-antisym y z) y≪z (transport (λ q → q ≪ y) x=z x≪y))

    g : (α : Ordinal 𝓤) → ( ⟨ α ⟩ → X) → X
    g α s = ε  ⁅ x ꞉ X ∣ Ɐ a ꞉ ⟨ α ⟩ , (( s a ⋘ x ) , ⋘-prop (s a) x ) ⁆

    f : Ordinal 𝓤 → X
    f = transfinite-recursion-on-OO X g

    A : Ordinal 𝓤 → 𝓟 { (𝓤 ⊔ 𝓣)} X
    A α = ⁅ x ꞉ X ∣ Ɐ a ꞉ ⟨ α ⟩ , (f (α ↓ a) ⋘ x , ⋘-prop (f (α ↓ a)) x ) ⁆

    f-behaviour : (α : Ordinal 𝓤) → f α ＝ ε (A α)
    f-behaviour = transfinite-recursion-on-OO-behaviour X g

    ⊲-is-classical-well-order : is-classical-well-order (_⊲_ {𝓤})
    ⊲-is-classical-well-order =
      inductive-well-order-is-classical _⊲_ lem ⊲-is-well-order

    ⊲-is-trichotomous : {a b : Ordinal 𝓤} → (a ⊲ b) + (a ＝ b) + (b ⊲ a)
    ⊲-is-trichotomous {a} {b} = pr₁ (( pr₁ (pr₂ ⊲-is-classical-well-order)) a b)

    f-preserves-order : ¬ has-maximal-element-strong
                      → (α β : Ordinal 𝓤)
                      → β ⊲ α
                      → f β ⋘ f α
    f-preserves-order no-max = transfinite-induction-on-OO P (v no-max)
     where
      P : Ordinal 𝓤 → (𝓤 ⁺ ⊔ 𝓣) ̇
      P α = ∀ β → β ⊲ α → f β ⋘ f α
      v : ¬ has-maximal-element-strong
        → (α : Ordinal 𝓤)
        → ((a : ⟨ α ⟩) → P (α ↓ a))
        → P α
      v no-max α s β (a , β=α↓a) =
       transport⁻¹ (λ q → f q ⋘ f α) β=α↓a
        (transport⁻¹ (λ q → f (α ↓ a) ⋘ q) (f-behaviour α) (step a))
       where
        allfb : 𝓟  X
        allfb = ⁅ x ꞉ X ∣ Ǝ β' , ((β' ⊲ α ) × (x ＝ (f β'))) ⁆

        untrunc-works : (x y : X)
                      → (Σ β' ꞉ Ordinal 𝓤 , ((β' ⊲ α) × (x ＝ f β')))
                      → (Σ β'' ꞉ Ordinal 𝓤 , ((β'' ⊲ α) × (y ＝ f β'')))
                      → x ≪ y + y ≪ x
        untrunc-works
         x
         y
         (β' , ((b' , β'=α↓b') , x=fβ'))
         (β'' , ((b'' , β''=α↓b'') , y=fβ''))
         = cases less (cases equal more) ⊲-is-trichotomous
         where
          less : β'' ⊲ β' → (x ≪ y + y ≪ x)
          less b''<b' =
           inr (transport⁻¹ (λ q → y ≪ q) x=fβ'
            (transport⁻¹ (λ q → q ≪ f β') y=fβ''
              (pr₁ (transport⁻¹ (λ q → f β'' ⋘ f q) β'=α↓b' ((s b') β''
               (transport (λ q → β'' ⊲ q) β'=α↓b' b''<b'))))))
          equal : β'' ＝ β' → (x ≪ y + y ≪ x)
          equal b''=b' =
           inr (transport (λ q → y ≪ q)
            (transport⁻¹ (λ q → y ＝ q) x=fβ'
             (transport⁻¹ (λ q → q ＝ f β') y=fβ'' (ap f b''=b'))) (≪-refl y))

          more : β' ⊲ β'' → (x ≪ y + y ≪ x)
          more b'<b'' =
            inl (transport⁻¹ (λ q → x ≪ q) y=fβ''
             (transport⁻¹ (λ q → q ≪ f β'') x=fβ'
              (pr₁ (transport⁻¹ (λ q → f β' ⋘ f q) β''=α↓b''
               ((s b'') β' (transport (λ q → β' ⊲ q) β''=α↓b'' b'<b''))))))
        has-max-neg : (x : X) → ¬¬ (Σ y ꞉ X , ¬ (x ≪ y → x ＝ y))
        has-max-neg x =
         not-Π-implies-not-not-Σ (λ z → →-is-¬¬-stable eq-is-¬¬-stable)
          ((not-Σ-implies-Π-not no-max) x)

        allfb-is-chain :  is-chain allfb
        allfb-is-chain x y = ∥∥-functor₂ (untrunc-works x y)

        allfb-has-ub : Σ x ꞉ X , (∀ y → y ∈ allfb → y ≪ x)
        allfb-has-ub = chains allfb allfb-is-chain

        ub : X
        ub = pr₁ allfb-has-ub

        ub-is-ub : ∀ y → y ∈ allfb → y ≪ ub
        ub-is-ub = pr₂ allfb-has-ub

        ub-is-strict'
         : (Σ q ꞉ X , (¬ ( ub ≪ q → ub ＝ q)))
         → Σ z ꞉ X , (∀ y → y ∈ allfb → y ⋘ z)
        ub-is-strict' (q , foo) =  q ,
         λ y yin → ≪-trans-⋘ y ub q (ub-is-ub y yin)
          ((≪-is-¬¬-stable (pr₁ (negation-of-implication foo)))
           , (pr₂ (negation-of-implication foo)))

        ub-is-strict : ∃ z ꞉ X , (∀ y → y ∈ allfb → y ⋘ z)
        ub-is-strict = (∥∥-functor ub-is-strict') (¬¬Σ→∃ pt dn (has-max-neg ub))

        Aα-inhabited' :  Σ x ꞉ X , (∀ y → y ∈ allfb → y ⋘ x)
                         →  Σ x ꞉ X , ((i : ⟨ α ⟩) → f (α ↓ i) ⋘ x)
        Aα-inhabited' (x , ylt) =
         x ,  λ i →  ylt (f (α ↓ i))  ∣  (α ↓ i) ,  ( ( i , refl )) , refl ∣

        Aα-inhabited :  ∃ x ꞉ X , (∀ y → y ∈ allfb → y ⋘ x) → is-inhabited (A α)
        Aα-inhabited =  ∥∥-functor Aα-inhabited'

        step : (a : ⟨ α ⟩) →  (f (α ↓ a) ⋘ ε (A α))
        step a = (ε-behaviour (A α) (Aα-inhabited (ub-is-strict ))) a

    f-is-injective : ¬ has-maximal-element-strong
                   → (a b : Ordinal 𝓤)
                   → a ≠ b → f a ≠ f b
    f-is-injective no-max a b a≠b =
     cases (less a b) (cases (equal a b a≠b) (more a b)) ⊲-is-trichotomous
     where
      less : (a b : Ordinal 𝓤) → a ⊲ b → f a ≠ f b
      less a b a<b = pr₂ (f-preserves-order no-max b a a<b)

      more : (a b : Ordinal 𝓤) → b ⊲ a → f a ≠ f b
      more a b b<a = ≠-sym (pr₂ (f-preserves-order no-max a b b<a))

      equal : (a b : Ordinal 𝓤) → a ≠ b → a ＝ b → f a ≠ f b
      equal a b a≠b a=b = unique-from-𝟘 (a≠b a=b)

    f-is-left-cancellable
     : {a : Ordinal 𝓤}
     → {b : Ordinal 𝓤}
     → ¬ has-maximal-element-strong
     → f a ＝ f b
     → a ＝ b
    f-is-left-cancellable {a} {b} no-max p =
     dn (a ＝ b) (the-type-of-ordinals-is-a-set (ua 𝓤) fe')
                 ((contrapositive (f-is-injective no-max a b)) (¬¬-intro p))

    f-is-embedding : ¬ has-maximal-element-strong → is-embedding f
    f-is-embedding no-max = lc-maps-into-sets-are-embeddings f
                             (f-is-left-cancellable no-max)
                             X-is-set

    X' : 𝓤 ⁺ ̇
    X' = image f

    f' : Ordinal 𝓤 → X'
    f' = corestriction f

    f'-is-equiv : ¬ has-maximal-element-strong → is-equiv f'
    f'-is-equiv no-max = corestriction-of-embedding-is-equivalence f
                          (f-is-embedding no-max)

    B : X → 𝓤 ⁺ ̇
    B x = x ∈image f

    B-is-prop : (x : X) → is-prop (B x)
    B-is-prop x = being-in-the-image-is-prop x f

    ρ : Propositional-Resizing
    ρ = EM-gives-PR lem

    C : X → 𝓤 ̇
    C x = resize ρ (B x) (B-is-prop x)

    τ : Nat C B
    τ x = from-resize ρ (B x) (B-is-prop x)

    τ-is-equiv : (x : X) → is-equiv (τ x)
    τ-is-equiv x = from-resize-is-equiv ρ (B x) (B-is-prop x)

    X'' : 𝓤 ̇
    X'' = Σ x ꞉ X , C x

    e : ¬ has-maximal-element-strong → X'' ≃ Ordinal 𝓤
    e no-max = X''       ≃⟨ NatΣ τ , NatΣ-is-equiv C B τ τ-is-equiv ⟩
        X'        ≃⟨ ≃-sym (f' , f'-is-equiv no-max) ⟩
        Ordinal 𝓤 ■

    the-type-of-ordinals-is-small : ¬ has-maximal-element-strong
                                  → is-small (Ordinal 𝓤)
    the-type-of-ordinals-is-small no-max = X'' , (e no-max)

    absurd : ¬ has-maximal-element-strong → 𝟘
    absurd no-max = the-type-of-ordinals-is-large
                     (the-type-of-ordinals-is-small no-max)

axiom-of-choice-implies-zorns-lemma
 : Axiom-of-Choice
 → poset-axioms (_≪_)
 → all-chains-have-upper-bound
 → has-maximal-element

axiom-of-choice-implies-zorns-lemma ac (X-is-set , axioms-rest) = III
 where
  em : Excluded-Middle
  em = Choice-gives-Excluded-Middle pe' ac

  lifted-cf
   : ∥ Lift (𝓤 ⊔ 𝓣) X ∥
   → ∃ ε ꞉ (𝓟 (Lift (𝓤 ⊔ 𝓣) X) → (Lift (𝓤 ⊔ 𝓣) X))
         , ((A : 𝓟 (Lift (𝓤 ⊔ 𝓣) X)) → is-inhabited A → ε A ∈ A)
  lifted-cf =
   Choice-gives-Choice₄ ac (Lift (𝓤 ⊔ 𝓣) X) (Lift-is-set (𝓤 ⊔ 𝓣) X X-is-set)

  lower-cf
   : Σ ε ꞉ (𝓟 (Lift (𝓤 ⊔ 𝓣) X) → (Lift (𝓤 ⊔ 𝓣) X))
         , ((A : 𝓟 (Lift (𝓤 ⊔ 𝓣) X)) → is-inhabited A → ε A ∈ A)
   →  Σ ε ꞉ (𝓟 X → X) , ((A : 𝓟 X) → is-inhabited A → ε A ∈ A)
  lower-cf (ϵ , f) = (ϵ' , f')
   where
    ϵ' : 𝓟 X → X
    ϵ' S = lower (ϵ (S ∘ lower))
    inhab-trans : {A' : 𝓟 X} → is-inhabited A' → is-inhabited (A' ∘ lower)
    inhab-trans {A'} isA' =
     isA' >>= λ isA'' →
      ∣ lift (𝓤 ⊔ 𝓣) (pr₁ isA'') ,
      transport (λ q → (A' q) holds) (ε-Lift (𝓤 ⊔ 𝓣) (pr₁ isA'')) (pr₂ isA'')∣
    f' : (A' : 𝓟 X) → is-inhabited A' → ϵ' A' ∈ A'
    f' A' A'-inhab = (f (A' ∘ lower) (inhab-trans {A'} A'-inhab))

  choice-function : ∥ X ∥
                  → ∃ ε ꞉ (𝓟 X → X) , ((A : 𝓟 X) → is-inhabited A → ε A ∈ A)
  choice-function isX =  ∥∥-functor
                          lower-cf
                          (lifted-cf (∥∥-functor (lift (𝓤 ⊔ 𝓣)) isX))

  I' : all-chains-have-upper-bound
     → ∃ ε ꞉ (𝓟 X → X) , ((A : 𝓟 X) → is-inhabited A → ε A ∈ A)
     → has-maximal-element
  I' chains = ∥∥-rec
               (∃-is-prop)
               (choice-function-gives-zorns-lemma em
                 (X-is-set , axioms-rest)
                 chains)

  I : all-chains-have-upper-bound → ∥ X ∥ → has-maximal-element
  I chains-have-ub z = I' chains-have-ub (choice-function z)

  empty-has-no-ub : ¬ ∥ X ∥ → ¬ (all-chains-have-upper-bound {𝓥})
  empty-has-no-ub ν  chains =
   ν ∣ pr₁ (chains ∅ λ x y xin yin →  unique-from-𝟘 (ν ∣ x ∣)) ∣

  II : all-chains-have-upper-bound  →  ¬ ∥ X ∥ → has-maximal-element
  II chains-have-ub ν = unique-from-𝟘 ((empty-has-no-ub ν) chains-have-ub)

  III : all-chains-have-upper-bound → has-maximal-element
  III chains-have-ub =
   cases (I chains-have-ub) (II chains-have-ub) (em ∥ X ∥ ∥∥-is-prop)

\end{code}
