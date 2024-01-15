sTom de Jong, 27 May 2019.
Refactored 29 April 2020.

We show that lifting (cf. Escardó-Knapp) a set gives the free pointed dcpo on
that set.

When we start with a small set, then the lifting yields an algebraic pointed
dcpo as formalized in LiftingSetAlgebraic.lagda.

The construction that freely adds a least element to a dcpo is described in
LiftingDcpo.lagda.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.Lifting.LiftingSet
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓣 : Universe)
        (pe : propext 𝓣)
       where

open import UF.Equiv
open import UF.Hedberg
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

open PropositionalTruncation pt

open import Lifting.Lifting 𝓣 hiding (⊥)
open import Lifting.Miscelanea 𝓣
open import Lifting.Miscelanea-PropExt-FunExt 𝓣 pe fe
open import Lifting.Monad 𝓣

open import DomainTheory.Basics.Dcpo pt fe 𝓣
open import DomainTheory.Basics.Miscelanea pt fe 𝓣
open import DomainTheory.Basics.Pointed pt fe 𝓣

open import OrderedTypes.Poset fe

\end{code}

We start by showing that the lifting of a set is indeed a pointed dcpo.

\begin{code}

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
         (s : is-set X)
       where

 family-value-map : {I : 𝓣 ̇ }
                  → (α : I → 𝓛 X)
                  → (Σ i ꞉ I , is-defined (α i)) → X
 family-value-map α (i , d) = value (α i) d

 directed-family-value-map-is-wconstant : {I : 𝓣 ̇ }
                                        → (α : I → 𝓛 X)
                                        → (δ : is-directed _⊑'_ α )
                                        → wconstant (family-value-map α)
 directed-family-value-map-is-wconstant {I} α δ (i₀ , d₀) (i₁ , d₁) =
  γ (semidirected-if-directed _⊑'_ α δ i₀ i₁)
   where
    f : (Σ i ꞉ I , is-defined (α i)) → X
    f = family-value-map α
    γ : (∃ k ꞉ I , (α i₀ ⊑' α k) × (α i₁ ⊑' α k)) → f (i₀ , d₀) ＝ f (i₁ , d₁)
    γ = ∥∥-rec s g
     where
      g : (Σ k ꞉ I , (α i₀ ⊑' α k)
                   × (α i₁ ⊑' α k)) → f (i₀ , d₀) ＝ f (i₁ , d₁)
      g (k , l , m) =
       f (i₀ , d₀)                             ＝⟨ refl ⟩
       value (α i₀) d₀                         ＝⟨ ＝-of-values-from-＝ (l d₀) ⟩
       value (α k) (＝-to-is-defined (l d₀) d₀) ＝⟨ ＝-of-values-from-＝ ((m d₁) ⁻¹) ⟩
       value (α i₁) d₁                         ＝⟨ refl ⟩
       f (i₁ , d₁)                             ∎

 lifting-sup-value : {I : 𝓣 ̇ }
                   → (α : I → 𝓛 X)
                   → (δ : is-directed _⊑'_ α )
                   → (∃ i ꞉ I , is-defined (α i)) → X
 lifting-sup-value {I} α δ =
  pr₁ (wconstant-map-to-set-factors-through-truncation-of-domain
        s (family-value-map α)
        (directed-family-value-map-is-wconstant α δ))

 lifting-sup : {I : 𝓣 ̇ } → (α : I → 𝓛 X) → (δ : is-directed _⊑'_ α) → 𝓛 X
 lifting-sup {I} α δ =
  (∃ i ꞉ I , is-defined (α i)) , lifting-sup-value α δ , ∥∥-is-prop

 lifting-sup-is-upperbound : {I : 𝓣 ̇ } → (α : I → 𝓛 X)
                             (δ : is-directed _⊑'_ α)
                           → (i : I) → α i ⊑' lifting-sup α δ
 lifting-sup-is-upperbound {I} α δ i = γ
  where
   γ : α i ⊑' lifting-sup α δ
   γ = ⊑-to-⊑' (f , v)
    where
     f : is-defined (α i) → is-defined (lifting-sup α δ)
     f d = ∣ i , d ∣
     v : (d : is-defined (α i)) → value (α i) d ＝ value (lifting-sup α δ) (f d)
     v d = value (α i) d                 ＝⟨ p    ⟩
           lifting-sup-value α δ (f d)   ＝⟨ refl ⟩
           value (lifting-sup α δ) (f d) ∎
      where
       p = (pr₂ (wconstant-map-to-set-factors-through-truncation-of-domain
                  s (family-value-map α)
                  (directed-family-value-map-is-wconstant α δ)))
           (i , d)

 family-defined-somewhere-sup-＝ : {I : 𝓣 ̇ } {α : I → 𝓛 X}
                                → (δ : is-directed _⊑'_ α)
                                → (i : I)
                                → is-defined (α i)
                                → α i ＝ lifting-sup α δ
 family-defined-somewhere-sup-＝ {I} {α} δ i d =
  (lifting-sup-is-upperbound α δ i) d

 lifting-sup-is-lowerbound-of-upperbounds : {I : 𝓣 ̇ }
                                          → {α : I → 𝓛 X}
                                          → (δ : is-directed _⊑'_ α)
                                          → (v : 𝓛 X)
                                          → ((i : I) → α i ⊑' v)
                                          → lifting-sup α δ ⊑' v
 lifting-sup-is-lowerbound-of-upperbounds {I} {α} δ v b = h
  where
   h : lifting-sup α δ ⊑' v
   h d = ∥∥-rec (lifting-of-set-is-set s) g d
    where
     g : (Σ i ꞉ I , is-defined (α i)) → lifting-sup α δ ＝ v
     g (i , dᵢ) = lifting-sup α δ ＝⟨ (family-defined-somewhere-sup-＝ δ i dᵢ) ⁻¹ ⟩
                  α i             ＝⟨ b i dᵢ ⟩
                  v               ∎

 𝓛-DCPO : DCPO {𝓣 ⁺ ⊔ 𝓤} {𝓣 ⁺ ⊔ 𝓤}
 𝓛-DCPO = 𝓛 X , _⊑'_ , pa , c
  where
   pa : PosetAxioms.poset-axioms _⊑'_
   pa = sl , p , r , t , a
    where
     open PosetAxioms {_} {_} {𝓛 X} _⊑'_
     sl : is-set (𝓛 X)
     sl = lifting-of-set-is-set s
     p : is-prop-valued
     p _ _ = ⊑'-prop-valued s
     r : is-reflexive
     r _ = ⊑'-is-reflexive
     a : is-antisymmetric
     a _ _ = ⊑'-is-antisymmetric
     t : is-transitive
     t _ _ _ = ⊑'-is-transitive
   c : (I : 𝓣 ̇ ) (α : I → 𝓛 X) → is-directed _⊑'_ α → has-sup _⊑'_ α
   c I α δ = lifting-sup α δ ,
             lifting-sup-is-upperbound α δ ,
             lifting-sup-is-lowerbound-of-upperbounds δ

 𝓛-DCPO⊥ : DCPO⊥ {𝓣 ⁺ ⊔ 𝓤} {𝓣 ⁺ ⊔ 𝓤}
 𝓛-DCPO⊥ = 𝓛-DCPO , l , (λ _ → unique-from-𝟘)
  where
   l : 𝓛 X
   l = (𝟘 , 𝟘-elim , 𝟘-is-prop)

\end{code}

Now that we have the lifting as a dcpo, we prove that the lifting functor and
Kleisli extension yield continuous maps.

\begin{code}

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
         (s₀ : is-set X)
         {𝓥 : Universe}
         {Y : 𝓥 ̇ }
         (s₁ : is-set Y)
       where

 ♯-is-monotone : (f : X → 𝓛 Y) → is-monotone (𝓛-DCPO s₀) (𝓛-DCPO s₁) (f ♯)
 ♯-is-monotone f l m ineq d = ap (f ♯) (ineq (♯-is-defined f l d))

 ♯-is-continuous : (f : X → 𝓛 Y) → is-continuous (𝓛-DCPO s₀) (𝓛-DCPO s₁) (f ♯)
 ♯-is-continuous f I α δ = u , v
  where
   u : (i : I) → (f ♯) (α i) ⊑⟨ (𝓛-DCPO s₁) ⟩ (f ♯) (∐ (𝓛-DCPO s₀) δ)
   u i = ♯-is-monotone f (α i) (∐ (𝓛-DCPO s₀) δ)
         (∐-is-upperbound (𝓛-DCPO s₀) δ i)
   v : (m : ⟨ 𝓛-DCPO s₁ ⟩)
     → ((i : I) → (f ♯) (α i) ⊑⟨ (𝓛-DCPO s₁) ⟩ m)
     → (f ♯) (∐ (𝓛-DCPO s₀) δ) ⊑⟨ (𝓛-DCPO s₁) ⟩ m
   v m ineqs d =
    ∥∥-rec (lifting-of-set-is-set s₁) g (♯-is-defined f (∐ (𝓛-DCPO s₀) δ) d)
     where
      g : (Σ i ꞉ I , is-defined (α i)) → (f ♯) (∐ (𝓛-DCPO s₀) δ) ＝ m
      g (i , dᵢ) = (f ♯) (∐ (𝓛-DCPO s₀) δ) ＝⟨ h i dᵢ ⟩
                   (f ♯) (α i)             ＝⟨ ineqs i (＝-to-is-defined (h i dᵢ) d) ⟩
                   m                       ∎
       where
        h : (i : I) → is-defined (α i) → (f ♯) (∐ (𝓛-DCPO s₀) δ) ＝ (f ♯) (α i)
        h i d = ap (f ♯) ((family-defined-somewhere-sup-＝ s₀ δ i d) ⁻¹)

 𝓛̇-continuous : (f : X → Y) → is-continuous (𝓛-DCPO s₀) (𝓛-DCPO s₁) (𝓛̇ f)
 𝓛̇-continuous f = transport
                   (is-continuous (𝓛-DCPO s₀) (𝓛-DCPO s₁))
                   (dfunext fe (𝓛̇-♯-∼ f))
                   (♯-is-continuous (η ∘ f))

\end{code}

Finally we show that the lifting of a set gives the free pointed dcpo on that
set. The main technical tool in proving this is the use of subsingleton suprema,
cf. DomainTheory.Basics.Pointed.lagda, and the fact that every partial element
can be expressed as such a supremum.

\begin{code}

module lifting-is-free-pointed-dcpo-on-set
         {X : 𝓤 ̇ }
         (X-is-set : is-set X)
         (𝓓 : DCPO⊥ {𝓥} {𝓦})
         (f : X → ⟪ 𝓓 ⟫)
       where

 𝓛X : DCPO⊥ {𝓣 ⁺ ⊔ 𝓤} {𝓣 ⁺ ⊔ 𝓤}
 𝓛X = 𝓛-DCPO⊥ X-is-set

 f̃ : ⟪ 𝓛X ⟫ → ⟪ 𝓓 ⟫
 f̃ (P , ϕ , P-is-prop) = ∐ˢˢ 𝓓 (f ∘ ϕ) P-is-prop

 f̃-is-strict : is-strict 𝓛X 𝓓 f̃
 f̃-is-strict = strictness-criterion 𝓛X 𝓓 f̃ γ
  where
   γ : f̃ (⊥ 𝓛X) ⊑⟪ 𝓓 ⟫ ⊥ 𝓓
   γ = ∐ˢˢ-is-lowerbound-of-upperbounds 𝓓
        (f ∘ unique-from-𝟘) 𝟘-is-prop (⊥ 𝓓) 𝟘-induction

 f̃-is-continuous : is-continuous (𝓛X ⁻) (𝓓 ⁻) f̃
 f̃-is-continuous I α δ = ub , lb-of-ubs
  where
   s : 𝓛 X
   s = ∐ (𝓛X ⁻) δ
   ρ : (l : 𝓛 X) → is-prop (is-defined l)
   ρ = being-defined-is-prop
   lemma : (i : I) (p : is-defined (α i))
         → value (α i) p ＝ value s ∣ i , p ∣
   lemma i p = ＝-of-values-from-＝
                (family-defined-somewhere-sup-＝ X-is-set δ i p)
   ub : (i : I) → f̃ (α i) ⊑⟪ 𝓓 ⟫ f̃ s
   ub i = ∐ˢˢ-is-lowerbound-of-upperbounds 𝓓 (f ∘ value (α i)) (ρ (α i)) (f̃ s) γ
    where
     γ : (p : is-defined (α i))
       → f (value (α i) p) ⊑⟪ 𝓓 ⟫ f̃ s
     γ p = f (value (α i) p)     ⊑⟪ 𝓓 ⟫[ ⦅1⦆ ]
           f (value s ∣ i , p ∣) ⊑⟪ 𝓓 ⟫[ ⦅2⦆ ]
           f̃ s                   ∎⟪ 𝓓 ⟫
      where
       ⦅1⦆ = ＝-to-⊑ (𝓓 ⁻) (ap f (lemma i p))
       ⦅2⦆ = ∐ˢˢ-is-upperbound 𝓓 (f ∘ value s) (ρ s) ∣ i , p ∣
   lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 ⁻))
                (f̃ s) (f̃ ∘ α)
   lb-of-ubs y y-is-ub = ∐ˢˢ-is-lowerbound-of-upperbounds 𝓓 (f ∘ value s) (ρ s)
                          y γ
    where
     γ : (q : is-defined s)
       → (f (value s q)) ⊑⟪ 𝓓 ⟫ y
     γ q = ∥∥-rec (prop-valuedness (𝓓 ⁻) (f (value s q)) y) r q
      where
       r : (Σ i ꞉ I , is-defined (α i)) → f (value s q) ⊑⟪ 𝓓 ⟫ y
       r (i , p) = f (value s q)                     ⊑⟪ 𝓓 ⟫[ ⦅1⦆       ]
                   f (value s ∣ i , p ∣)             ⊑⟪ 𝓓 ⟫[ ⦅2⦆       ]
                   f (value (α i) p)                 ⊑⟪ 𝓓 ⟫[ ⦅3⦆       ]
                   ∐ˢˢ 𝓓 (f ∘ value (α i)) (ρ (α i)) ⊑⟪ 𝓓 ⟫[ y-is-ub i ]
                   y                                 ∎⟪ 𝓓 ⟫
        where
         ⦅1⦆ = ＝-to-⊑ (𝓓 ⁻) (ap f (value-is-constant s q ∣ i , p ∣))
         ⦅2⦆ = ＝-to-⊒ (𝓓 ⁻) (ap f (lemma i p))
         ⦅3⦆ = ∐ˢˢ-is-upperbound 𝓓 (f ∘ value (α i)) (being-defined-is-prop (α i)) p

 f̃-after-η-is-f : f̃ ∘ η ∼ f
 f̃-after-η-is-f x = antisymmetry (𝓓 ⁻) (f̃ (η x)) (f x) u v
  where
   u : f̃ (η x) ⊑⟪ 𝓓 ⟫ f x
   u = ∐ˢˢ-is-lowerbound-of-upperbounds 𝓓 (f ∘ (λ _ → x)) 𝟙-is-prop
        (f x) (λ _ → reflexivity (𝓓 ⁻) (f x))
   v : f x ⊑⟪ 𝓓 ⟫ f̃ (η x)
   v = ∐ˢˢ-is-upperbound 𝓓 (λ _ → f x) 𝟙-is-prop ⋆

 all-partial-elements-are-subsingleton-sups :
    (l : ⟪ 𝓛X ⟫)
  → l ＝ ∐ˢˢ 𝓛X (η ∘ value l) (being-defined-is-prop l)
 all-partial-elements-are-subsingleton-sups (P , ϕ , ρ) =
  antisymmetry (𝓛X ⁻) (P , ϕ , ρ) (∐ˢˢ 𝓛X (η ∘ ϕ) ρ) u v
   where
    v : ∐ˢˢ 𝓛X (η ∘ ϕ) ρ ⊑' (P , ϕ , ρ)
    v = ∐ˢˢ-is-lowerbound-of-upperbounds 𝓛X (η ∘ ϕ) ρ (P , ϕ , ρ)
         (λ p ⋆ → (is-defined-η-＝ p) ⁻¹)
    u : (P , ϕ , ρ) ⊑' ∐ˢˢ 𝓛X (η ∘ ϕ) ρ
    u p = antisymmetry (𝓛X ⁻) (P , ϕ , ρ) (∐ˢˢ 𝓛X (η ∘ ϕ) ρ)
           u' v
     where
      u' = (P , ϕ , ρ)      ⊑⟪ 𝓛X ⟫[ ＝-to-⊑ (𝓛X ⁻) (is-defined-η-＝ p) ]
           η (ϕ p)          ⊑⟪ 𝓛X ⟫[ ∐ˢˢ-is-upperbound 𝓛X (η ∘ ϕ) ρ p ]
           ∐ˢˢ 𝓛X (η ∘ ϕ) ρ ∎⟪ 𝓛X ⟫

 f̃-is-unique : (g : ⟪ 𝓛X ⟫ → ⟪ 𝓓 ⟫)
             → is-continuous (𝓛X ⁻) (𝓓 ⁻) g
             → is-strict 𝓛X 𝓓 g
             → g ∘ η ＝ f
             → g ∼ f̃
 f̃-is-unique g con str eq (P , ϕ , ρ) = g (P , ϕ , ρ)        ＝⟨ ⦅1⦆  ⟩
                                        g (∐ˢˢ 𝓛X (η ∘ ϕ) ρ) ＝⟨ ⦅2⦆  ⟩
                                        ∐ˢˢ 𝓓 (g ∘ η ∘ ϕ) ρ  ＝⟨ ⦅3⦆  ⟩
                                        ∐ˢˢ 𝓓 (f ∘ ϕ) ρ      ＝⟨ refl ⟩
                                        f̃ (P , ϕ , ρ)        ∎
   where
    ⦅1⦆ = ap g (all-partial-elements-are-subsingleton-sups (P , ϕ , ρ))
    ⦅2⦆ = ∐ˢˢ-＝-if-continuous-and-strict 𝓛X 𝓓 g con str (η ∘ ϕ) ρ
    ⦅3⦆ = ∐ˢˢ-family-＝ 𝓓 ρ (ap (_∘ ϕ) eq)

 𝓛-gives-the-free-pointed-dcpo-on-a-set :
  ∃! h ꞉ (⟪ 𝓛X ⟫ → ⟪ 𝓓 ⟫) , is-continuous (𝓛X ⁻) (𝓓 ⁻) h
                          × is-strict 𝓛X 𝓓 h
                          × (h ∘ η ＝ f)
 𝓛-gives-the-free-pointed-dcpo-on-a-set =
  (f̃ , f̃-is-continuous , f̃-is-strict , (dfunext fe f̃-after-η-is-f)) , γ
   where
    γ : is-central (Σ h ꞉ (⟪ 𝓛X ⟫ → ⟪ 𝓓 ⟫) , is-continuous (𝓛X ⁻) (𝓓 ⁻) h
                                           × is-strict 𝓛X 𝓓 h
                                           × (h ∘ η ＝ f))
         (f̃ , f̃-is-continuous , f̃-is-strict , dfunext fe f̃-after-η-is-f)
    γ (g , cont , str , eq) =
     to-subtype-＝ (λ h → ×₃-is-prop (being-continuous-is-prop (𝓛X ⁻) (𝓓 ⁻) h)
                                    (being-strict-is-prop 𝓛X 𝓓 h)
                                    (equiv-to-prop
                                      (≃-funext fe (h ∘ η) f)
                                      (Π-is-prop fe (λ _ → sethood (𝓓 ⁻)))))
                                    ((dfunext fe (f̃-is-unique g cont str eq)) ⁻¹)

\end{code}

In general, the lifting of a set is only directed complete and does not have all
(small) sups, but if we lift propositions, then we do get all small suprema.

As an application, we use this to prove that 𝓓∞ is algebraic in
DomainTheory.Bilimits.Dinfinity.lagda.

\begin{code}

open import DomainTheory.Basics.SupComplete pt fe 𝓣

module _
        {P : 𝓤 ̇ }
        (P-is-prop : is-prop P)
       where

 private
  𝓛P :  DCPO {𝓣 ⁺ ⊔ 𝓤} {𝓣 ⁺ ⊔ 𝓤}
  𝓛P = 𝓛-DCPO (props-are-sets (P-is-prop))

 lifting-of-prop-is-sup-complete : is-sup-complete 𝓛P
 lifting-of-prop-is-sup-complete = record { ⋁ = sup ; ⋁-is-sup = lemma }
  where
   sup-map : {I : 𝓣 ̇ } (α : I → ⟨ 𝓛P ⟩) → (∃ i ꞉ I , is-defined (α i)) → P
   sup-map α = ∥∥-rec P-is-prop (λ (i , q) → value (α i) q)
   sup : {I : 𝓣 ̇ } (α : I → ⟨ 𝓛P ⟩) → ⟨ 𝓛P ⟩
   sup {I} α = ((∃ i ꞉ I , is-defined (α i)) , sup-map α , ∃-is-prop)
   lemma : {I : 𝓣 ̇ } (α : I → ⟨ 𝓛P ⟩) → is-sup _⊑'_ (sup α) α
   lemma {I} α = (ub , lb-of-ubs)
    where
     ub : (i : I) → α i ⊑' sup α
     ub i = ⊑-to-⊑' (f , g)
      where
       f : is-defined (α i) → ∃ i ꞉ I , is-defined (α i)
       f p = ∣ i , p ∣
       g : value (α i) ∼ (λ q → sup-map α ∣ i , q ∣)
       g q = P-is-prop (value (α i) q) (sup-map α ∣ i , q ∣)
     lb-of-ubs : is-lowerbound-of-upperbounds _⊑'_ (sup α) α
     lb-of-ubs l l-is-ub = ⊑-to-⊑' (f , g)
      where
       f : (∃ i ꞉ I , is-defined (α i)) → is-defined l
       f = ∥∥-rec (being-defined-is-prop l) h
        where
         h : (Σ i ꞉ I , is-defined (α i)) → is-defined l
         h (i , q) = ＝-to-is-defined (l-is-ub i q) q
       g : sup-map α ∼ (λ q → value l (f q))
       g q = P-is-prop (sup-map α q) (value l (f q))

\end{code}
