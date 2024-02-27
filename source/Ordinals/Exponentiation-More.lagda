Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
13 November 2023.

TEMPORARILY SPLIT UP TO SPEED UP TYPECHECKING

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split --lossy-unification #-}

open import UF.Univalence

module Ordinals.Exponentiation-More
       (ua : Univalence)
       where

open import UF.Base
open import UF.Embeddings hiding (⌊_⌋)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Size
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

open import MLTT.Plus-Properties
open import MLTT.Spartan hiding (cases ; Cases)
open import MLTT.Sigma
-- open import Notation.CanonicalMap
open import Ordinals.Arithmetic fe
open import Ordinals.ArithmeticProperties ua
open import Ordinals.ConvergentSequence ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying

-- our imports
open import MLTT.List
open import Ordinals.Exponentiation ua

open import Ordinals.WellOrderingTaboo

\end{code}


Given an ordinal α and a type family P, subtype of elements satisfying
P inherits an order from α.  This order also inherits wellfoundedness
and transitivity from the order on α, but not necessarily
extensionality constructively (see Ordinals.ShulmanTaboo).

\begin{code}
subtype-order : (α : Ordinal 𝓤) → (P : ⟨ α ⟩ → 𝓥 ̇ ) → Σ x ꞉ ⟨ α ⟩ , P x → Σ x ꞉ ⟨ α ⟩ , P x → 𝓤 ̇
subtype-order α P (x , _) (y , _) = x ≺⟨ α ⟩ y

subtype-order-propositional : (α : Ordinal 𝓤) → (P : ⟨ α ⟩ → 𝓥 ̇ ) → is-prop-valued (subtype-order α P)
subtype-order-propositional α P (x , _) (y , _) = Prop-valuedness α x y

subtype-order-wellfounded : (α : Ordinal 𝓤) → (P : ⟨ α ⟩ → 𝓥 ̇ ) → is-well-founded (subtype-order α P)
subtype-order-wellfounded α P (a , p) = subtype-order-accessible (a , p) (Well-foundedness α a)
 where
  subtype-order-accessible : (z : Σ x ꞉ ⟨ α ⟩ , P x)
                           → is-accessible (underlying-order α) (pr₁ z) → is-accessible (subtype-order α P) z
  subtype-order-accessible (x , p) (acc step) = acc (λ y q → subtype-order-accessible y (step (pr₁ y) q))

subtype-order-transitive : (α : Ordinal 𝓤) → (P : ⟨ α ⟩ → 𝓥 ̇ ) → is-transitive (subtype-order α P)
subtype-order-transitive α P (x , _) (y , _) (z , _) = Transitivity α x y z

\end{code}



\begin{code}

prop-ordinal-＝ : (P Q : 𝓤 ̇ ) → (pp : is-prop P) → (pq : is-prop Q)
                → P ↔ Q → prop-ordinal P pp ＝ prop-ordinal Q pq
prop-ordinal-＝ P Q pp pq (f , g) =
  ⊴-antisym (prop-ordinal P pp) (prop-ordinal Q pq)
            (simulation P Q pp pq f) (simulation Q P pq pp g)
  where
    simulation : (P Q : 𝓤 ̇ ) → (pp : is-prop P) → (pq : is-prop Q) → (P → Q) →
                 prop-ordinal P pp ⊴ prop-ordinal Q pq
    simulation P Q pp pq f = f , (λ x y e → 𝟘-elim e) , (λ x y e → 𝟘-elim e)

module _ (pt : propositional-truncations-exist)
         (sr : Set-Replacement pt)
       where

 open PropositionalTruncation pt

 open import Ordinals.OrdinalOfOrdinalsSuprema ua
 open suprema pt sr

 open import UF.ImageAndSurjection pt

 sup-preserves-prop : {I : 𝓤 ̇ } → (γ : I → 𝓤 ̇ ) → (γ-is-prop : (i : I) → is-prop (γ i))
                    → sup (λ i → prop-ordinal (γ i) (γ-is-prop i)) ＝ prop-ordinal (∃ i ꞉ I , γ i) ∥∥-is-prop
 sup-preserves-prop {𝓤} {I = I} γ γ-is-prop = surjective-simulation-gives-equality pt sr (sup β) α
                                                (pr₁ (sup-is-lower-bound-of-upper-bounds β α f))
                                                (pr₂ (sup-is-lower-bound-of-upper-bounds β α f))
                                                (surjectivity-lemma β α f f-surjective)
   where
     α : Ordinal 𝓤
     α = prop-ordinal (∃ i ꞉ I , γ i) ∥∥-is-prop
     β : I → Ordinal 𝓤
     β i = prop-ordinal (γ i) (γ-is-prop i)
     f : (i : I) → β i ⊴ α
     f i = (λ b → ∣ i , b ∣) , (λ x y e → 𝟘-elim e) , (λ x y e → 𝟘-elim e)
     f-surjective : (y : ⟨ α ⟩) → ∃ i ꞉ I , Σ b ꞉ ⟨ β i ⟩ , pr₁ (f i) b ＝ y
     f-surjective = ∥∥-induction (λ x → ∥∥-is-prop) λ (i , b) → ∣ i , b , refl ∣


 is-continuous : (Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
 is-continuous {𝓤} F = {I : 𝓤 ̇  } → ∥ I ∥ → (γ : I → Ordinal 𝓤) → F (sup γ) ＝ sup (F ∘ γ)

 is-monotone-if-continuous : (F : Ordinal 𝓤 → Ordinal 𝓤)
                           → is-continuous F
                           → is-monotone (OO 𝓤) (OO 𝓤) F
 is-monotone-if-continuous {𝓤} F F-cont α β α-less-than-β = conclusion
  where
   γ : 𝟙{𝓤} + 𝟙{𝓤} → Ordinal 𝓤
   γ (inl _) = α
   γ (inr _) = β
   eq : F (sup γ) ＝ sup (F ∘ γ)
   eq = F-cont ∣ inl ⋆ ∣ γ
   β-is-upper-bound : (i : 𝟙 + 𝟙) → γ i ⊴ β
   β-is-upper-bound (inl _) = ≼-gives-⊴ α β α-less-than-β
   β-is-upper-bound (inr _) = ⊴-refl β
   I : sup γ ＝ β
   I = ⊴-antisym (sup γ) β (sup-is-lower-bound-of-upper-bounds γ β β-is-upper-bound) (sup-is-upper-bound γ (inr ⋆))
   ineq : F α ⊴ sup (F ∘ γ)
   ineq = sup-is-upper-bound (F ∘ γ) (inl ⋆)
   conclusion : F α ≼ F β
   conclusion = ⊴-gives-≼ (F α) (F β) (transport (F α ⊴_) (eq ⁻¹ ∙ ap F I) ineq)

 module _
         (exp : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤)
        where

  full-sup-spec : 𝓤 ⁺ ̇
  full-sup-spec = (α : Ordinal 𝓤) → is-continuous (exp α)

  full-sup-spec' : 𝓤 ⁺ ̇
  full-sup-spec' = (α : Ordinal 𝓤) → (¬(α ＝ 𝟘ₒ) → is-continuous (exp α)) × ((α ＝ 𝟘ₒ) → (β : Ordinal 𝓤) → ¬(β ＝ 𝟘ₒ) → exp α β ＝ 𝟘ₒ)


  full-succ-spec : 𝓤 ⁺ ̇
  full-succ-spec = (α : Ordinal 𝓤) (β : Ordinal 𝓤) → exp α (β +ₒ 𝟙ₒ) ＝ exp α β ×ₒ α

  full-zero-spec : 𝓤 ⁺ ̇
  full-zero-spec = (α : Ordinal 𝓤) → exp α 𝟘ₒ ＝ 𝟙ₒ

  full-spec : 𝓤 ⁺ ̇
  full-spec = full-zero-spec × full-succ-spec × full-sup-spec

  full-spec' : 𝓤 ⁺ ̇
  full-spec' = full-zero-spec × full-succ-spec × full-sup-spec'


  exp-is-monotone-gives-EM : full-zero-spec
                           → full-succ-spec
                           → ((α : Ordinal 𝓤) → is-monotone (OO 𝓤) (OO 𝓤) (exp α))
                           → EM 𝓤
  exp-is-monotone-gives-EM spec₀ specₛ mon P P-is-prop = P-is-decidable
   where
    α : Ordinal 𝓤
    α = prop-ordinal (P + ¬ P) (decidability-of-prop-is-prop fe' P-is-prop)
    ineq : exp α 𝟘ₒ ⊴ exp α 𝟙ₒ
    ineq = ≼-gives-⊴ (exp α 𝟘ₒ) (exp α 𝟙ₒ) (mon α 𝟘ₒ 𝟙ₒ (𝟘ₒ-least 𝟙ₒ))
    eq₁ : exp α 𝟘ₒ ＝ 𝟙ₒ
    eq₁ = spec₀ α
    eq₂ : exp α 𝟙ₒ ＝ α
    eq₂ = exp α 𝟙ₒ ＝⟨ ap (exp α) ((𝟘ₒ-left-neutral 𝟙ₒ) ⁻¹) ⟩
          exp α (𝟘ₒ +ₒ 𝟙ₒ) ＝⟨ specₛ α 𝟘ₒ ⟩
          (exp α 𝟘ₒ ×ₒ α) ＝⟨ ap (_×ₒ α) eq₁ ⟩
          𝟙ₒ ×ₒ α ＝⟨ 𝟙ₒ-left-neutral-×ₒ α ⟩
          α ∎
    ineq' : 𝟙ₒ ⊴ α
    ineq' = transport₂ _⊴_ eq₁ eq₂ ineq
    P-is-decidable : P + ¬ P
    P-is-decidable = pr₁ ineq' ⋆

  exp-is-monotone-gives-EM' : full-zero-spec
                           → full-succ-spec
                           → ((α : Ordinal 𝓤) → ¬ (α ＝ 𝟘ₒ) → is-monotone (OO 𝓤) (OO 𝓤) (exp α))
                           → EM 𝓤
  exp-is-monotone-gives-EM' spec₀ specₛ mon P P-is-prop = P-is-decidable (pr₁ ineq' ⋆ , refl)
   where
    α : Ordinal 𝓤
    α = prop-ordinal P P-is-prop +ₒ 𝟙ₒ
    α-not-zero : ¬ (α ＝ 𝟘ₒ)
    α-not-zero p = 𝟘-elim (≃ₒ-to-fun α 𝟘ₒ (idtoeqₒ α 𝟘ₒ p) (inr ⋆))
    ineq : exp α 𝟘ₒ ⊴ exp α 𝟙ₒ
    ineq = ≼-gives-⊴ (exp α 𝟘ₒ) (exp α 𝟙ₒ) (mon α α-not-zero 𝟘ₒ 𝟙ₒ (𝟘ₒ-least 𝟙ₒ))
    eq₁ : exp α 𝟘ₒ ＝ 𝟙ₒ
    eq₁ = spec₀ α
    eq₂ : exp α 𝟙ₒ ＝ α
    eq₂ = exp α 𝟙ₒ ＝⟨ ap (exp α) ((𝟘ₒ-left-neutral 𝟙ₒ) ⁻¹) ⟩
          exp α (𝟘ₒ +ₒ 𝟙ₒ) ＝⟨ specₛ α 𝟘ₒ ⟩
          (exp α 𝟘ₒ ×ₒ α) ＝⟨ ap (_×ₒ α) eq₁ ⟩
          𝟙ₒ ×ₒ α ＝⟨ 𝟙ₒ-left-neutral-×ₒ α ⟩
          α ∎
    ineq' : 𝟙ₒ ⊴ α
    ineq' = transport₂ _⊴_ eq₁ eq₂ ineq
    P-is-decidable : Σ a ꞉ ⟨ α ⟩ , (pr₁ ineq' ⋆ ＝ a) → P + ¬ P
    P-is-decidable (inl p , _) = inl p
    P-is-decidable (inr ⋆ , r) = inr (λ p → 𝟘-elim (pr₁ (pr₂ (pr₁ (pr₂ ineq') ⋆ (inl p) (transport⁻¹ (λ - → inl p ≺⟨ α ⟩ -) r ⋆ )))))



  exp-full-spec-gives-EM : full-spec → EM 𝓤
  exp-full-spec-gives-EM (spec₀ , specₛ , specₗ) =
   exp-is-monotone-gives-EM spec₀ specₛ
    (λ α → is-monotone-if-continuous (exp α) (specₗ α))

  exp-full-spec'-gives-EM : full-spec' → EM 𝓤
  exp-full-spec'-gives-EM (spec₀ , specₛ , specₗ) =
   exp-is-monotone-gives-EM' spec₀ specₛ
    (λ α α-not-zero → is-monotone-if-continuous (exp α) (pr₁ (specₗ α) α-not-zero))


\end{code}

And conversely...

\begin{code}


 private
  case : (α : Ordinal 𝓤) → 𝓤 ⁺ ̇
  case {𝓤} α = (Σ α' ꞉ Ordinal 𝓤 , α ＝ 𝟙ₒ +ₒ α')

  cases : (α : Ordinal 𝓤) → 𝓤 ⁺ ̇
  cases α = case α + (α ＝ 𝟘ₒ)

  Cases : 𝓤 ⁺ ̇
  Cases {𝓤} = (α : Ordinal 𝓤) → cases α

  open ClassicalWellOrder fe' (Univalence-gives-Prop-Ext ua) pt

  EM-gives-Cases : EM 𝓤 → Cases {𝓤}
  EM-gives-Cases em α = +functor α-inhabited-gives-least underlying-zero-unique α-inhabited-or-zero
   where
    α-inhabited-or-not : ∥ ⟨ α ⟩ ∥ + ¬ ∥ ⟨ α ⟩ ∥
    α-inhabited-or-not = em ∥ ⟨ α ⟩ ∥ ∥∥-is-prop

    α-inhabited-or-zero : ∥ ⟨ α ⟩ ∥ + (⟨ α ⟩ ＝ 𝟘)
    α-inhabited-or-zero = +functor id (λ ni → empty-types-are-＝-𝟘 fe' (Univalence-gives-Prop-Ext ua) (uninhabited-is-empty ni) ) α-inhabited-or-not

    underlying-zero-unique : (⟨ α ⟩ ＝ 𝟘) → α ＝ 𝟘ₒ
    underlying-zero-unique refl = ⊴-antisym α 𝟘ₒ sim sim'
     where
      sim : (𝟘 , _) ⊴ 𝟘ₒ
      sim = (𝟘-elim , (λ x → 𝟘-elim x) , λ x → 𝟘-elim x)
      sim' : 𝟘ₒ ⊴ (𝟘 , _)
      sim' = (𝟘-elim , (λ x → 𝟘-elim x) , λ x → 𝟘-elim x)

    α-inhabited-gives-least : ∥ ⟨ α ⟩ ∥ → case α
    α-inhabited-gives-least inh = α' , eq
     where
       least-element' : Σ a ꞉ ⟨ α ⟩ , 𝟙 × ((y : ⟨ α ⟩) → 𝟙 → ¬ (y ≺⟨ α ⟩ a))
       least-element' = well-order-gives-minimal (underlying-order α) em (is-well-ordered α) (λ _ → 𝟙) (λ _ → 𝟙-is-prop) (∥∥-functor (λ a → (a , ⋆)) inh)

       a₀ : ⟨ α ⟩
       a₀ = pr₁ least-element'

       a₀-least : ((y : ⟨ α ⟩) → ¬ (y ≺⟨ α ⟩ a₀))
       a₀-least y = pr₂ (pr₂ least-element') y ⋆

       ⟨α'⟩ = Σ x ꞉ ⟨ α ⟩ , a₀ ≺⟨ α ⟩ x

       _<'_ : ⟨α'⟩ → ⟨α'⟩ → _
       _<'_ = subtype-order α (λ - → a₀ ≺⟨ α ⟩ -)

       <'-propvalued : is-prop-valued _<'_
       <'-propvalued = subtype-order-propositional α (λ - → a₀ ≺⟨ α ⟩ -)

       <'-wellfounded : is-well-founded _<'_
       <'-wellfounded = subtype-order-wellfounded α (λ - → a₀ ≺⟨ α ⟩ -)

       <-trichotomy  : is-trichotomous-order (underlying-order α)
       <-trichotomy = trichotomy (underlying-order α) fe' em (is-well-ordered α)

       <'-extensional : is-extensional _<'_
       <'-extensional (x , p) (y , q) f g = to-subtype-＝ (λ x → Prop-valuedness α a₀ x)
                                                         (Extensionality α x y
                                                           (λ u p → f' u (<-trichotomy u a₀) p)
                                                           λ u p → g' u (<-trichotomy u a₀) p)
        where
         f' : (u : ⟨ α ⟩) → in-trichotomy (underlying-order α) u a₀ → u ≺⟨ α ⟩ x → u ≺⟨ α ⟩ y
         f' u (inl q) r = 𝟘-elim (a₀-least u q)
         f' u (inr (inl refl)) r = q
         f' u (inr (inr q)) r = f (u , q) r

         g' : (u : ⟨ α ⟩) → in-trichotomy (underlying-order α) u a₀ → u ≺⟨ α ⟩ y → u ≺⟨ α ⟩ x
         g' u (inl q) r = 𝟘-elim (a₀-least u q)
         g' u (inr (inl refl)) r = p
         g' u (inr (inr q)) r = g (u , q) r


       <'-transitive : is-transitive _<'_
       <'-transitive = subtype-order-transitive α (λ - → a₀ ≺⟨ α ⟩ -)

       α' : Ordinal _
       α' = ⟨α'⟩ , _<'_ , <'-propvalued , <'-wellfounded , <'-extensional , <'-transitive

       f' : (x : ⟨ α ⟩) → in-trichotomy (underlying-order α) x a₀ → 𝟙 + ⟨ α' ⟩
       f' x (inl q) = 𝟘-elim (a₀-least x q)
       f' x (inr (inl r)) = inl ⋆
       f' x (inr (inr q)) = inr (x , q)

       f : ⟨ α ⟩ → 𝟙 + ⟨ α' ⟩
       f x = f' x (<-trichotomy x a₀)

       g : 𝟙 + ⟨ α' ⟩ → ⟨ α ⟩
       g (inl ⋆) = a₀
       g (inr (x , q)) = x

       f-equiv : is-order-equiv α (𝟙ₒ +ₒ α') f
       f-equiv = f-order-preserving , (qinvs-are-equivs f (g , η , ϵ)) , g-order-preserving
        where
         f'-order-preserving : (x y : ⟨ α ⟩)
                             → (tx : in-trichotomy (underlying-order α) x a₀)
                             → (ty : in-trichotomy (underlying-order α) y a₀)
                             → x ≺⟨ α ⟩ y → f' x tx ≺⟨ 𝟙ₒ +ₒ α' ⟩ f' y ty
         f'-order-preserving x y (inl q) ty p = 𝟘-elim (a₀-least x q)
         f'-order-preserving x y (inr (inl r)) (inl q) p = 𝟘-elim (a₀-least y q)
         f'-order-preserving .a₀ .a₀ (inr (inl refl)) (inr (inl refl)) p = 𝟘-elim (irrefl α a₀ p)
         f'-order-preserving .a₀ y (inr (inl refl)) (inr (inr q)) p = ⋆
         f'-order-preserving x y (inr (inr q)) (inl q') p = 𝟘-elim (a₀-least y q')
         f'-order-preserving x .a₀ (inr (inr q)) (inr (inl refl)) p = 𝟘-elim (a₀-least x p)
         f'-order-preserving x y (inr (inr q)) (inr (inr q')) p = p

         f-order-preserving : is-order-preserving α (𝟙ₒ +ₒ α') f
         f-order-preserving x y p = f'-order-preserving x y (<-trichotomy x a₀) (<-trichotomy y a₀) p

         g-order-preserving : is-order-preserving (𝟙ₒ +ₒ α') α g
         g-order-preserving (inl ⋆) (inr (x , q)) p = q
         g-order-preserving (inr (x , q)) (inr (y , q')) p = p

         η' : (x : ⟨ α ⟩) → (t : in-trichotomy (underlying-order α) x a₀) → g (f' x t) ＝ x
         η' x (inl q) = 𝟘-elim (a₀-least x q)
         η' x (inr (inl refl)) = refl
         η' x (inr (inr q)) = refl

         η : (x : ⟨ α ⟩) → g (f x) ＝ x
         η x = η' x (<-trichotomy x a₀)

         ϵ' : (y : 𝟙 + ⟨ α' ⟩) → (t : in-trichotomy (underlying-order α) (g y) a₀) → f' (g y) t ＝ y
         ϵ' (inl ⋆) (inl q) = 𝟘-elim (a₀-least a₀ q)
         ϵ' (inl ⋆) (inr (inl r)) = refl
         ϵ' (inl ⋆) (inr (inr q)) = 𝟘-elim (irrefl α a₀ q)
         ϵ' (inr (x , p)) (inl q) = 𝟘-elim (a₀-least x q)
         ϵ' (inr (.a₀ , p)) (inr (inl refl)) = 𝟘-elim (irrefl α a₀ p)
         ϵ' (inr (x , p)) (inr (inr q)) = ap inr (to-subtype-＝  ((λ x → Prop-valuedness α a₀ x)) refl)

         ϵ : (y : 𝟙 + ⟨ α' ⟩) → f (g y) ＝ y
         ϵ y = ϵ' y (<-trichotomy (g y) a₀)

       eq : α ＝ 𝟙ₒ +ₒ α'
       eq = eqtoidₒ (ua _) fe' α (𝟙ₒ +ₒ α') (f , f-equiv)

 Cases-gives-full-spec : Cases → Σ exp ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) , full-spec' exp
 Cases-gives-full-spec {𝓤} cs = exp , exp-spec'
  where
   exp-aux : (α : Ordinal 𝓤)
           → cases α
           → Ordinal 𝓤 → Ordinal 𝓤
   exp-aux α (inl (α' , _)) β = [𝟙+ α' ]^ β
   exp-aux α (inr _) β = prop-ordinal (β ≃ₒ 𝟘ₒ{𝓤}) (≃ₒ-is-prop-valued fe' β 𝟘ₒ)
   exp : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤
   exp α = exp-aux α (cs α)

   spec₀-aux : (α : Ordinal 𝓤) → (cs : cases α) → exp-aux α cs 𝟘ₒ ＝ 𝟙ₒ
   spec₀-aux α (inl (α' , refl)) = exp-0-spec α'
   spec₀-aux α (inr refl) = eq
     where
       eq : prop-ordinal (𝟘ₒ ≃ₒ 𝟘ₒ{𝓤}) (≃ₒ-is-prop-valued fe' 𝟘ₒ 𝟘ₒ) ＝ 𝟙ₒ
       eq = prop-ordinal-＝ (𝟘ₒ ≃ₒ 𝟘ₒ{𝓤}) 𝟙
                            (≃ₒ-is-prop-valued fe' 𝟘ₒ 𝟘ₒ) 𝟙-is-prop
                            ((λ _ → ⋆) , λ _ → (≃ₒ-refl 𝟘ₒ))

   specₛ-aux : (α : Ordinal 𝓤) → (cs : cases α) → (β : Ordinal 𝓤)
             → exp-aux α cs (β +ₒ 𝟙ₒ) ＝ (exp-aux α cs β ×ₒ α)
   specₛ-aux α (inl (α' , refl)) = exp-succ-spec α'
   specₛ-aux α (inr refl) β = eq ∙ ×ₒ-zero-right (prop-ordinal (β ≃ₒ 𝟘ₒ) (≃ₒ-is-prop-valued fe' β 𝟘ₒ)) ⁻¹
     where
       eq : prop-ordinal ((β +ₒ 𝟙ₒ) ≃ₒ 𝟘ₒ{𝓤}) (≃ₒ-is-prop-valued fe' (β +ₒ 𝟙ₒ) 𝟘ₒ) ＝ 𝟘ₒ
       eq = prop-ordinal-＝ ((β +ₒ 𝟙ₒ) ≃ₒ 𝟘ₒ{𝓤}) 𝟘 (≃ₒ-is-prop-valued fe' (β +ₒ 𝟙ₒ) 𝟘ₒ) 𝟘-is-prop (f , 𝟘-elim)
         where
           f : (β +ₒ 𝟙ₒ) ≃ₒ 𝟘ₒ → 𝟘
           f e = ≃ₒ-to-fun (β +ₒ 𝟙ₒ) 𝟘ₒ e (inr ⋆)

   {-
   specₗ-aux : (α : Ordinal 𝓤) → (cs : cases α) → {I : 𝓤 ̇ } → ∥ I ∥ → (γ : I → Ordinal 𝓤)
             → exp-aux α cs (sup γ) ＝ sup (λ i → exp-aux α cs (γ i))
   specₗ-aux α (inl (α' , refl)) i γ = exp-sup-spec pt sr α' i γ ⁻¹
   specₗ-aux α (inr refl) {I} i₀ γ = eq
     where
       f : sup γ ≃ₒ 𝟘ₒ → ∃ i ꞉ I , γ i ≃ₒ 𝟘ₒ
       f x = {!!}
       g : ∃ i ꞉ I , γ i ≃ₒ 𝟘ₒ → sup γ ≃ₒ 𝟘ₒ
       g = ∥∥-rec (≃ₒ-is-prop-valued fe' (sup γ) 𝟘ₒ) {!!}
       eq : prop-ordinal (sup γ ≃ₒ 𝟘ₒ{𝓤}) (≃ₒ-is-prop-valued fe' (sup γ) 𝟘ₒ) ＝ sup (λ i → prop-ordinal (γ i ≃ₒ 𝟘ₒ{𝓤}) (≃ₒ-is-prop-valued fe' (γ i) 𝟘ₒ))
       eq = prop-ordinal-＝ (sup γ ≃ₒ 𝟘ₒ{𝓤}) (∃ i ꞉ I , (γ i ≃ₒ 𝟘ₒ{𝓤})) _ _ (f , g) ∙ sup-preserves-prop (λ i → (γ i ≃ₒ 𝟘ₒ{𝓤})) (λ i → ≃ₒ-is-prop-valued fe' (γ i) 𝟘ₒ) ⁻¹

   exp-spec : full-spec exp
   exp-spec = (λ α → spec₀-aux α (cs α)) , (λ α → specₛ-aux α (cs α)) , (λ α → specₗ-aux α (cs α))
   -}

   specₗ-aux-nonzero : (α : Ordinal 𝓤) → (cs : cases α) → ¬ (α ＝ 𝟘ₒ) → {I : 𝓤 ̇ } → ∥ I ∥ → (γ : I → Ordinal 𝓤)
                     →  exp-aux α cs (sup γ) ＝ sup (λ i → exp-aux α cs (γ i))
   specₗ-aux-nonzero α (inl (α' , refl)) α-not-zero i γ = exp-sup-spec pt sr α' i γ ⁻¹
   specₗ-aux-nonzero α (inr r) α-not-zero = 𝟘-elim (α-not-zero r)

   specₗ-aux-zero : (α : Ordinal 𝓤) → (cs : cases α) → α ＝ 𝟘ₒ → (β : Ordinal 𝓤) → ¬ (β ＝ 𝟘ₒ)
                  → exp-aux α cs β ＝ 𝟘ₒ
   specₗ-aux-zero α (inl (α' , r)) α-zero β β-not-zero = 𝟘-elim (zero-no-element (α-zero ⁻¹ ∙ r) )
     where
       zero-no-element : (𝟘ₒ ＝ (𝟙ₒ +ₒ α')) → 𝟘
       zero-no-element p = Idtofun ((ap ⟨_⟩ p) ⁻¹) (inl ⋆)
   specₗ-aux-zero α (inr refl) α-zero β β-not-zero = prop-ordinal-＝ (β ≃ₒ 𝟘ₒ) 𝟘 (≃ₒ-is-prop-valued fe' β 𝟘ₒ) 𝟘-is-prop ((λ e → 𝟘-elim (β-not-zero (eqtoidₒ (ua _) fe' _ _ e))) , 𝟘-elim)

   exp-spec' : full-spec' exp
   exp-spec' = (λ α → spec₀-aux α (cs α)) , (λ α → specₛ-aux α (cs α)) , (λ α → specₗ-aux-nonzero α (cs α) , specₗ-aux-zero α (cs α))

 EM-gives-full-spec : EM 𝓤 → Σ exp ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) , full-spec' exp
 EM-gives-full-spec em = Cases-gives-full-spec (EM-gives-Cases em)

 full-spec-gives-Cases : Σ exp ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) , full-spec' exp → Cases {𝓤}
 full-spec-gives-Cases {𝓤} (exp , exp-spec) = EM-gives-Cases (exp-full-spec'-gives-EM exp exp-spec)

\end{code}

\begin{code}

 monotone-in-exponent : (α : Ordinal 𝓤)
                      → is-monotone (OO 𝓤) (OO 𝓤) [𝟙+ α ]^_
 monotone-in-exponent α =
  is-monotone-if-continuous ([𝟙+ α ]^_) (λ i γ → (exp-sup-spec pt sr α i γ) ⁻¹)

 trimmed-ordinal' : (α : Ordinal 𝓤) (x₀ : ⟨ α ⟩)
                  → ((x : ⟨ α ⟩) → in-trichotomy (underlying-order α) x₀ x)
                  → Ordinal 𝓤
 trimmed-ordinal' {𝓤} α x₀ τ = α' , _≺'_
                                  , subtype-order-propositional α (λ - → x₀ ≺⟨ α ⟩ -)
                                  , subtype-order-wellfounded α (λ - → x₀ ≺⟨ α ⟩ -)
                                  , ≺'-extensional
                                  , subtype-order-transitive α (λ - → x₀ ≺⟨ α ⟩ -)
  where
   α' : 𝓤 ̇
   α' = Σ x ꞉ ⟨ α ⟩ , x₀ ≺⟨ α ⟩ x
   _≺'_ : α' → α' → 𝓤 ̇
   _≺'_ = subtype-order α (λ - → x₀ ≺⟨ α ⟩ -)
   ≺'-extensional : is-extensional _≺'_
   ≺'-extensional (x , l) (y , k) u v =
    to-subtype-＝ (Prop-valuedness α x₀) (Extensionality α x y (λ z → u' z (τ z)) (λ z → v' z (τ z)))
     where
      u' : (z : ⟨ α ⟩)
         → in-trichotomy (underlying-order α) x₀ z
         → z ≺⟨ α ⟩ x
         → z ≺⟨ α ⟩ y
      u' z (inl x₀-below-z) m = u (z , x₀-below-z) m
      u' z (inr (inl refl)) m = k
      u' z (inr (inr z-below-x₀)) m = Transitivity α z x₀ y z-below-x₀ k
      v' : (z : ⟨ α ⟩)
         → in-trichotomy (underlying-order α) x₀ z
         → z ≺⟨ α ⟩ y
         → z ≺⟨ α ⟩ x
      v' z (inl x₀-below-z) m = v (z , x₀-below-z) m
      v' z (inr (inl refl)) m = l
      v' z (inr (inr z-below-x₀)) m = Transitivity α z x₀ x z-below-x₀ l

 open import UF.DiscreteAndSeparated
 trimmed-ordinal : (α : Ordinal 𝓤) (x₀ : ⟨ α ⟩)
                 → is-isolated x₀
                 → ((x : ⟨ α ⟩) → x ≠ x₀ → x₀ ≺⟨ α ⟩ x)
                 → Ordinal 𝓤
 trimmed-ordinal α x₀ δ x₀-least = trimmed-ordinal' α x₀ (λ x → τ x (δ x))
  where
   τ : (x : ⟨ α ⟩)
     → is-decidable (x₀ ＝ x)
     → in-trichotomy (underlying-order α) x₀ x
   τ x (inl e) = inr (inl e)
   τ x (inr ne) = inl (x₀-least x (≠-sym ne))

 exp-has-least-element : (α β : Ordinal 𝓤) → Σ γ ꞉ Ordinal 𝓤 , [𝟙+ α ]^ β ＝ 𝟙ₒ +ₒ γ
 exp-has-least-element {𝓤} α β = γ , eqtoidₒ (ua _) fe' ([𝟙+ α ]^ β) (𝟙ₒ +ₒ γ) (f , f-equiv)
  where
   γ : Ordinal 𝓤
   γ = trimmed-ordinal' ([𝟙+ α ]^ β) ([] , []-decr) τ
    where
     τ : (x : ⟨ [𝟙+ α ]^ β ⟩)
       → in-trichotomy (underlying-order ([𝟙+ α ]^ β)) ([] , []-decr) x
     τ ([] , δ) = inr (inl (to-exponential-＝ α β refl))
     τ ((x ∷ l) , δ) = inl []-lex

   f : ⟨ [𝟙+ α ]^ β ⟩ → ⟨ 𝟙ₒ +ₒ γ ⟩
   f ([] , δ) = inl ⋆
   f y@((x ∷ xs) , δ) = inr (y , []-lex)

   g : ⟨ 𝟙ₒ +ₒ γ ⟩ → ⟨ [𝟙+ α ]^ β ⟩
   g (inl _) = ([] , []-decr)
   g (inr (y , p)) = y

   f-order-preserving : is-order-preserving ([𝟙+ α ]^ β) (𝟙ₒ +ₒ γ) f
   f-order-preserving ([] , δ) ((x ∷ xs) , ε) p = ⋆
   f-order-preserving ((x ∷ xs) , δ) ((y ∷ ys) , ε) p = p

   g-order-preserving : is-order-preserving (𝟙ₒ +ₒ γ) ([𝟙+ α ]^ β) g
   g-order-preserving (inl ⋆) (inr (((x ∷ xs) , δ) , q)) _ = []-lex
   g-order-preserving (inr (((x ∷ xs) , δ) , q)) (inr (((y ∷ ys) , ε) , q')) p = p

   f-equiv : is-order-equiv ([𝟙+ α ]^ β) (𝟙ₒ +ₒ γ) f
   f-equiv = f-order-preserving , (qinvs-are-equivs f (g , η , ϵ)) , g-order-preserving
    where
     η : (x : ⟨ [𝟙+ α ]^ β ⟩) → g (f x) ＝ x
     η ([] , []-decr) = refl
     η ((x ∷ xs) , δ) = refl

     ϵ : (x : ⟨ 𝟙ₒ +ₒ γ ⟩) → f (g x) ＝ x
     ϵ (inl ⋆) = refl
     ϵ (inr (((x ∷ xs) , δ) , []-lex)) = refl



\end{code}

Wikipedia:
* γ > 1 => γ^(-) is order preserving
* α^(β + γ) = α^β × α^γ              [ exp-+-distributes ]
* α^(β × γ) = (α^β)^γ
