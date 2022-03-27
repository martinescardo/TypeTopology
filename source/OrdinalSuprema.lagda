Tom de Jong, March 2022

TODO: Describe contents

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-PropTrunc
open import UF-Univalence

module OrdinalSuprema
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import SpartanMLTT

open import UF-Base hiding (_≈_)
open import UF-Equiv
open import UF-FunExt
open import UF-UA-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open import OrdinalNotions hiding (is-prop-valued)
open import OrdinalsType
open import OrdinalOfOrdinals ua


private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

 pe' : Prop-Ext
 pe' {𝓤} = pe 𝓤

open import UF-Quotient pt fe' pe'

module _
        {I : 𝓤 ̇  }
        (α : I → Ordinal 𝓤)
       where

 private
  Σα : 𝓤 ̇
  Σα = Σ i ꞉ I , ⟨ α i ⟩

  _≈_ : Σα → Σα → 𝓤 ̇
  (i , x) ≈ (j , y) = (α i ↓ x) ≃ₒ (α j ↓ y)

  ≈-is-symmetric : symmetric _≈_
  ≈-is-symmetric (i , x) (j , y) = ≃ₒ-sym (α i ↓ x) (α j ↓ y)

  ≈-is-transitive : transitive _≈_
  ≈-is-transitive (i , x) (j , y) (k , z) = ≃ₒ-trans (α i ↓ x) (α j ↓ y) (α k ↓ z)

  ≈-is-reflexive : reflexive _≈_
  ≈-is-reflexive (i , x) = ≃ₒ-refl (α i ↓ x)

  ≈-is-prop-valued : is-prop-valued _≈_
  ≈-is-prop-valued (i , x) (j , y) = ≃ₒ-is-prop-valued (α i ↓ x) (α j ↓ y)

  _≺_ : Σα → Σα → 𝓤 ⁺ ̇
  (i , x) ≺ (j , y) = (α i ↓ x) ⊲ (α j ↓ y)

  ≺-is-prop-valued : is-prop-valued _≺_
  ≺-is-prop-valued (i , x) (j , y) = ⊲-is-prop-valued (α i ↓ x) (α j ↓ y)

  ≺-is-transitive : transitive _≺_
  ≺-is-transitive (i , x) (j , y) (k , z) =
   ⊲-is-transitive (α i ↓ x) (α j ↓ y) (α k ↓ z)

  ≺-is-well-founded : is-well-founded _≺_
  ≺-is-well-founded = transfinite-induction-converse _≺_ goal
   where
    goal : Well-founded _≺_
    goal P IH (i , x) = lemma (α i ↓ x) i x refl
     where
      P̃ : Ordinal 𝓤 → 𝓤 ⁺ ̇
      P̃ β = (i : I) (x : ⟨ α i ⟩) → β ≡ (α i ↓ x) → P (i , x)
      lemma : (β : Ordinal 𝓤) → P̃ β
      lemma = transfinite-induction _⊲_ ⊲-is-well-founded P̃ claim
       where
        claim : (β : Ordinal 𝓤) → ((γ : Ordinal 𝓤) → γ ⊲ β → P̃ γ) → P̃ β
        claim β IH' i x refl = IH (i , x) subclaim
         where
          subclaim : ((j , y) : Σα) → (j , y) ≺ (i , x) → P (j , y)
          subclaim (j , y) (z , e) = IH' ((α i ↓ x) ↓ z) (z , refl) j y (e ⁻¹)

  ≺-is-extensional-up-to-≈ : (p q : Σα)
                           → ((r : Σα) → r ≺ p → r ≺ q)
                           → ((r : Σα) → r ≺ q → r ≺ p)
                           → p ≈ q
  ≺-is-extensional-up-to-≈ (i , x) (j , y) hyp₁ hyp₂ =
   ⌜ UAₒ-≃ (α i ↓ x) (α j ↓ y) ⌝ goal
    where
     goal : (α i ↓ x) ≡ (α j ↓ y)
     goal = ⊲-is-extensional (α i ↓ x) (α j ↓ y) ⦅1⦆ ⦅2⦆
      where
       ⦅1⦆ : (β : Ordinal 𝓤) → β ⊲ (α i ↓ x) → β ⊲ (α j ↓ y)
       ⦅1⦆ β (p , refl) = goal₁
        where
         goal₁ : ((α i ↓ x) ↓ p) ⊲ (α j ↓ y)
         goal₁ = back-transport (_⊲ (α j ↓ y)) claim₂ claim₁
          where
           x' : ⟨ α i ⟩
           x' = pr₁ p
           x'-below-x : x' ≺⟨ α i ⟩ x
           x'-below-x = pr₂ p
           claim₁ : (α i ↓ x') ⊲ (α j ↓ y)
           claim₁ = hyp₁ (i , x') (↓-preserves-order (α i) x' x x'-below-x)
           claim₂ : ((α i ↓ x) ↓ p) ≡ (α i ↓ x')
           claim₂ = iterated-↓ (α i) x x' x'-below-x
       ⦅2⦆ : (β : Ordinal 𝓤) → β ⊲ (α j ↓ y) → β ⊲ (α i ↓ x)
       ⦅2⦆ β (p , refl) = goal₂
        where
         goal₂ : ((α j ↓ y) ↓ p) ⊲ (α i ↓ x)
         goal₂ = back-transport (_⊲ (α i ↓ x)) claim₂ claim₁
          where
           y' : ⟨ α j ⟩
           y' = pr₁ p
           y'-below-y : y' ≺⟨ α j ⟩ y
           y'-below-y = pr₂ p
           claim₁ : (α j ↓ y') ⊲ (α i ↓ x)
           claim₁ = hyp₂ (j , y') (↓-preserves-order (α j) y' y y'-below-y)
           claim₂ : ((α j ↓ y) ↓ p) ≡ (α j ↓ y')
           claim₂ = iterated-↓ (α j) y y' y'-below-y

  ι : (i : I) → ⟨ α i ⟩ → Σα
  ι i x = (i , x)

  ι-is-order-preserving : (i : I) (x y : ⟨ α i ⟩)
                        → x ≺⟨ α i ⟩ y → ι i x ≺ ι i y
  ι-is-order-preserving i x y l = ↓-preserves-order (α i) x y l

  ι-is-initial-segment-up-to-≈ : (i : I) (x : ⟨ α i ⟩) ((j , y) : Σα)
                               → (j , y) ≺ ι i x
                               → Σ x' ꞉ ⟨ α i ⟩ , (x' ≺⟨ α i ⟩ x)
                                                × (ι i x' ≈ (j , y))
  ι-is-initial-segment-up-to-≈ i x (j , y) (p , e) = (x' , l , goal)
   where
    x' : ⟨ α i ⟩
    x' = pr₁ p
    l : x' ≺⟨ α i ⟩ x
    l = pr₂ p
    goal : (α i ↓ x') ≃ₒ (α j ↓ y)
    goal = ⌜ UAₒ-≃ (α i ↓ x') (α j ↓ y) ⌝ (subgoal ⁻¹)
     where
      subgoal : (α j ↓ y) ≡ (α i ↓ x')
      subgoal = (α j ↓ y)       ≡⟨ e ⟩
                ((α i ↓ x) ↓ p) ≡⟨ iterated-↓ (α i) x x' l ⟩
                (α i ↓ x')      ∎


  module lowerbound-of-upperbounds-proof
          (β : Ordinal 𝓤)
          (β-is-upperbound : (i : I) → α i ⊴ β)
         where

   f : (i : I) → ⟨ α i ⟩ → ⟨ β ⟩
   f i x = pr₁ (β-is-upperbound i) x

   f-key-property : (i : I) (x : ⟨ α i ⟩) → α i ↓ x ≡ β ↓ (f i x)
   f-key-property i x =
    pr₂ (⊴-gives-≼ (α i) β (β-is-upperbound i) (α i ↓ x) (x , refl))

   f̃ : Σα → ⟨ β ⟩
   f̃ (i , x) = f i x

   β-is-upperbound-≼ : (i : I) → α i ≼ β
   β-is-upperbound-≼ i = ⊴-gives-≼ (α i) β (β-is-upperbound i)

   f̃-respects-≈ : {p q : Σα} → p ≈ q → f̃ p ≡ f̃ q
   f̃-respects-≈ {(i , x)} {(j , y)} e = ↓-lc β (f̃ (i , x)) (f̃ (j , y)) goal
    where
     goal = (β ↓ f̃ (i , x)) ≡⟨ ⦅1⦆ ⟩
            (α i ↓ x)       ≡⟨ ⦅2⦆ ⟩
            (α j ↓ y)       ≡⟨ ⦅3⦆ ⟩
            (β ↓ f̃ (j , y)) ∎
      where
       ⦅1⦆ = (f-key-property i x) ⁻¹
       ⦅2⦆ = ⌜ UAₒ-≃ (α i ↓ x) (α j ↓ y) ⌝⁻¹ e
       ⦅3⦆ = f-key-property j y

   f̃-is-order-preserving : (p q : Σα) → p ≺ q → f̃ p ≺⟨ β ⟩ f̃ q
   f̃-is-order-preserving (i , x) (j , y) l =
    ↓-reflects-order β (f̃ (i , x)) (f̃ (j , y)) goal
     where
      goal : (β ↓ f̃ (i , x)) ⊲ (β ↓ f̃ (j , y))
      goal = transport₂ _⊲_ (f-key-property i x) (f-key-property j y) l

   f̃-is-initial-segment : (p : Σα) (b : ⟨ β ⟩)
                        → b ≺⟨ β ⟩ f̃ p
                        → Σ q ꞉ Σα , (q ≺ p) × (f̃ q ≡ b)
   f̃-is-initial-segment (i , x) b l = (i , x') , goal₁ , goal₂
    where
     lemma : Σ x' ꞉ ⟨ α i ⟩ , (x' ≺⟨ α i ⟩ x) × (f i x' ≡ b)
     lemma = simulations-are-initial-segments (α i) β
              (f i) (pr₂ (β-is-upperbound i))
              x b l
     x' : ⟨ α i ⟩
     x' = pr₁ lemma
     x'-below-x : x' ≺⟨ α i ⟩ x
     x'-below-x = pr₁ (pr₂ lemma)

     goal₁ : (α i ↓ x') ⊲ (α i ↓ x)
     goal₁ = ↓-preserves-order (α i) x' x x'-below-x
     goal₂ : f̃ (i , x') ≡ b
     goal₂ = pr₂ (pr₂ lemma)

 ≈R : EqRel Σα
 ≈R = _≈_ , ≈-is-prop-valued , ≈-is-reflexive , ≈-is-symmetric , ≈-is-transitive

 α/ : 𝓤 ⁺ ̇
 α/ = Σα / ≈R

 private
  _≺[Ω]_ : Σα → Σα → Ω (𝓤 ⁺)
  p ≺[Ω] q = (p ≺ q , ≺-is-prop-valued p q)

  ≺-congruence : {p q p' q' : Σα} → p ≈ p' → q ≈ q'
               → (p ≺[Ω] q) ≡ (p' ≺[Ω] q')
  ≺-congruence {(i , x)} {(j , y)} {(i' , x')} {(j' , y')} u v =
   Ω-extensionality fe' pe' ⦅1⦆ ⦅2⦆
    where
     ⦅1⦆ : (α i ↓ x) ⊲ (α j ↓ y) → (α i' ↓ x') ⊲ (α j' ↓ y')
     ⦅1⦆ l = transport₂ _⊲_ e₁ e₂ l
      where
       e₁ : (α i ↓ x) ≡ (α i' ↓ x')
       e₁ = ⌜ UAₒ-≃ (α i ↓ x) (α i' ↓ x') ⌝⁻¹ u
       e₂ : (α j ↓ y) ≡ (α j' ↓ y')
       e₂ = ⌜ UAₒ-≃ (α j ↓ y) (α j' ↓ y') ⌝⁻¹ v
     ⦅2⦆ : (α i' ↓ x') ⊲ (α j' ↓ y') → (α i ↓ x) ⊲ (α j ↓ y)
     ⦅2⦆ l = transport₂ _⊲_ e₁ e₂ l
      where
       e₁ : (α i' ↓ x') ≡ (α i ↓ x)
       e₁ = ⌜ UAₒ-≃ (α i' ↓ x') (α i ↓ x) ⌝⁻¹
             (≈-is-symmetric (i , x) (i' , x') u)
       e₂ : (α j' ↓ y') ≡ (α j ↓ y)
       e₂ = ⌜ UAₒ-≃ (α j' ↓ y') (α j ↓ y) ⌝⁻¹
             (≈-is-symmetric (j , y) (j' , y') v)

  _≺/[Ω]_ : α/ → α/ → Ω (𝓤 ⁺)
  _≺/[Ω]_ = extension-rel₂ ≈R (λ x y → x ≺ y , ≺-is-prop-valued x y) ≺-congruence

  [_] : Σα → α/
  [_] = η/ ≈R

 _≺/_ : α/ → α/ → 𝓤 ⁺ ̇
 x ≺/ y = (x ≺/[Ω] y) holds

 ≺/-≡-≺ : {p q : Σα} → [ p ] ≺/ [ q ] ≡ p ≺ q
 ≺/-≡-≺ {p} {q} = ap pr₁ (extension-rel-triangle₂ ≈R _≺[Ω]_ ≺-congruence p q)

 ≺/-to-≺ : {p q : Σα} → [ p ] ≺/ [ q ] → p ≺ q
 ≺/-to-≺ = Idtofun ≺/-≡-≺

 ≺-to-≺/ : {p q : Σα} → p ≺ q → [ p ] ≺/ [ q ]
 ≺-to-≺/ = back-Idtofun ≺/-≡-≺

 ≺/-is-prop-valued : is-prop-valued _≺/_
 ≺/-is-prop-valued x y = holds-is-prop (x ≺/[Ω] y)

 ≺/-is-transitive : transitive _≺/_
 ≺/-is-transitive = /-induction₃ ≈R ρ γ
  where
   ρ : (x y z : α/) → is-prop (x ≺/ y → y ≺/ z → x ≺/ z)
   ρ x y z = Π₂-is-prop fe' (λ _ _ → ≺/-is-prop-valued x z)
   γ : (p q r : Σα) → [ p ] ≺/ [ q ] → [ q ] ≺/ [ r ] → [ p ] ≺/ [ r ]
   γ p q r k l = ≺-to-≺/ (≺-is-transitive p q r (≺/-to-≺ k) (≺/-to-≺ l))

 ≺/-is-extensional : is-extensional _≺/_
 ≺/-is-extensional = /-induction₂ ≈R
                      (λ x y → Π₂-is-prop fe' (λ _ _ → quotient-is-set ≈R))
                      γ
  where
   γ : (p q : Σα)
     → ((z : α/) → z ≺/ [ p ] → z ≺/ [ q ])
     → ((z : α/) → z ≺/ [ q ] → z ≺/ [ p ])
     → [ p ] ≡ [ q ]
   γ p q u v = η/-identifies-related-points ≈R e
    where
     e : p ≈ q
     e = ≺-is-extensional-up-to-≈ p q u' v'
      where
       u' : (r : Σα) → r ≺ p → r ≺ q
       u' r l = ≺/-to-≺ (u [ r ] (≺-to-≺/ l))
       v' : (r : Σα) → r ≺ q → r ≺ p
       v' r l = ≺/-to-≺ (v [ r ] (≺-to-≺/ l))

 ≺/-is-well-founded : is-well-founded _≺/_
 ≺/-is-well-founded = γ
  where
   a : (x : α/) → is-prop (is-accessible _≺/_ x)
   a = accessibility-is-prop _≺/_ fe
   lemma : (p : Σα) → is-accessible _≺/_ [ p ]
   lemma = transfinite-induction _≺_ ≺-is-well-founded
            (λ p → is-accessible _≺/_ [ p ]) ϕ
    where
     ϕ : (p : Σα) → ((q : Σα) → q ≺ p → is-accessible _≺/_ [ q ])
       → is-accessible _≺/_ [ p ]
     ϕ p IH = next [ p ] IH'
      where
       IH' : (y : α/) → y ≺/ [ p ] → is-accessible _≺/_ y
       IH' = /-induction' ≈R (λ q → Π-is-prop fe' (λ _ → a q))
              (λ q l → IH q (≺/-to-≺ l))
   γ : (x : α/) → is-accessible _≺/_ x
   γ = /-induction' ≈R a lemma

 ≺/-is-well-order : is-well-order _≺/_
 ≺/-is-well-order =
  ≺/-is-prop-valued , ≺/-is-well-founded , ≺/-is-extensional , ≺/-is-transitive

 α/-Ord : Ordinal (𝓤 ⁺)
 α/-Ord = α/ , _≺/_ , ≺/-is-well-order

 α/-is-upperbound : (i : I) → α i ⊴ α/-Ord
 α/-is-upperbound i = ([_] ∘ ι i , sim)
  where
   sim : is-simulation (α i) α/-Ord (λ x → [ i , x ])
   sim = simulation-unprime pt (α i) α/-Ord (λ x → [ i , x ])
          (init-seg , order-pres)
    where
     order-pres : is-order-preserving (α i) α/-Ord (λ x → [ i , x ])
     order-pres x y l = ≺-to-≺/ {i , x} {i , y} (ι-is-order-preserving i x y l)
     init-seg : is-initial-segment' pt (α i) α/-Ord (λ x → [ i , x ])
     init-seg x = /-induction' ≈R (λ y → Π-is-prop fe' λ _ → ∃-is-prop) claim
      where
       claim : (p : Σα) → [ p ] ≺/ [ i , x ]
             → ∃ y ꞉ ⟨ α i ⟩ , (y ≺⟨ α i ⟩ x) × ([ i , y ] ≡ [ p ])
       claim p l = ∣ y , k , η/-identifies-related-points ≈R e ∣
        where
         abstract
          lem : Σ y ꞉ ⟨ α i ⟩ , (y ≺⟨ α i ⟩ x) × ((i , y) ≈ p)
          lem = ι-is-initial-segment-up-to-≈ i x p (≺/-to-≺ l)
          y : ⟨ α i ⟩
          y = pr₁ lem
          k : y ≺⟨ α i ⟩ x
          k = pr₁ (pr₂ lem)
          e : (i , y) ≈ p
          e = pr₂ (pr₂ lem)

 α/-is-lowerbound-of-upperbounds : (β : Ordinal 𝓤)
                                 → ((i : I) → α i ⊴ β)
                                 → α/-Ord ⊴ β
 α/-is-lowerbound-of-upperbounds β β-is-ub = f/ , f/-is-simulation
  where
   open lowerbound-of-upperbounds-proof β β-is-ub
   f/ : α/ → ⟨ β ⟩
   f/ = mediating-map/ ≈R (underlying-type-is-set fe β) f̃ f̃-respects-≈
   f/-≡-f̃ : {p : Σα} → f/ [ p ] ≡ f̃ p
   f/-≡-f̃ {p} = universality-triangle/ ≈R (underlying-type-is-set fe β)
                 f̃ f̃-respects-≈ p
   f/-is-order-preserving : is-order-preserving α/-Ord β f/
   f/-is-order-preserving =
    /-induction₂ ≈R prp ρ
     where
      prp : (x y : α/) → is-prop (x ≺/ y → f/ x ≺⟨ β ⟩ f/ y)
      prp x y = Π-is-prop fe' (λ _ → Prop-valuedness β (f/ x) (f/ y))
      ρ : (p q : Σα) → [ p ] ≺/ [ q ] → f/ [ p ] ≺⟨ β ⟩ f/ [ q ]
      ρ p q l = back-transport₂ (λ -₁ -₂ → -₁ ≺⟨ β ⟩ -₂)
                 f/-≡-f̃ f/-≡-f̃
                 (f̃-is-order-preserving p q (≺/-to-≺ l))
   f/-is-simulation : is-simulation α/-Ord β f/
   f/-is-simulation = simulation-unprime pt α/-Ord β f/ σ
    where
     σ : is-simulation' pt α/-Ord β f/
     σ = init-seg , f/-is-order-preserving
      where
       init-seg : is-initial-segment' pt α/-Ord β f/
       init-seg = /-induction' ≈R prp ρ
        where
         prp : (x : α/)
             → is-prop ((y : ⟨ β ⟩) → y ≺⟨ β ⟩ f/ x
                                    → ∃ x' ꞉ α/ , (x' ≺/ x) × (f/ x' ≡ y))
         prp x = Π₂-is-prop fe' (λ _ _ → ∃-is-prop)
         ρ : (p : Σα) (y : ⟨ β ⟩)
           → y ≺⟨ β ⟩ f/ [ p ]
           → ∃ x' ꞉ α/ , (x' ≺/ [ p ]) × (f/ x' ≡ y)
         ρ p y l = ∣ [ q ] , k , e ∣
          where
           abstract
            lem : Σ q ꞉ Σα , (q ≺ p) × (f̃ q ≡ y)
            lem = f̃-is-initial-segment p y
                   (transport (λ - → y ≺⟨ β ⟩ -) f/-≡-f̃ l)
            q : Σα
            q = pr₁ lem
            k : [ q ] ≺/ [ p ]
            k = ≺-to-≺/ {q} {p} (pr₁ (pr₂ lem))
            e : f/ [ q ] ≡ y
            e = f/ [ q ] ≡⟨ f/-≡-f̃ {q}    ⟩
                f̃    q   ≡⟨ pr₂ (pr₂ lem) ⟩
                y        ∎

\end{code}

TODO: Finally, we resize... (Use Small-Set-Quotients from other branch)

\begin{code}

 open import UF-Size
 open import OrdinalsWellOrderTransport fe

 _≺⁻_ : Σα → Σα → 𝓤 ̇
 (i , x) ≺⁻ (j , y) = (α i ↓ x) ⊲⁻ (α j ↓ y)

 ≺-≃-≺⁻ : (p q : Σα) → (p ≺ q) ≃ (p ≺⁻ q)
 ≺-≃-≺⁻ (i , x) (j , y) = ⊲-is-equivalent-to-⊲⁻ (α i ↓ x) (α j ↓ y)

 ≺/-has-small-values : (x y : α/) → is-small (x ≺/ y)
 ≺/-has-small-values =
  /-induction₂ ≈R (λ x y → being-small-is-prop ua (x ≺/ y) 𝓤)
                  (λ p q → p ≺⁻ q , (p ≺⁻ q         ≃⟨ ≃-sym (≺-≃-≺⁻ p q)     ⟩
                                     p ≺ q          ≃⟨ idtoeq _ _ (≺/-≡-≺ ⁻¹) ⟩
                                     [ p ] ≺/ [ q ] ■))

 _≺/⁻_ : α/ → α/ → 𝓤 ̇
 x ≺/⁻ y = pr₁ (≺/-has-small-values x y)

 ≺/-≃-≺/⁻ : {x y : α/} → x ≺/ y ≃ x ≺/⁻ y
 ≺/-≃-≺/⁻ {x} {y} = ≃-sym (pr₂ (≺/-has-small-values x y))

 ≺/-to-≺/⁻ : {x y : α/} → x ≺/ y → x ≺/⁻ y
 ≺/-to-≺/⁻ = ⌜ ≺/-≃-≺/⁻ ⌝

 ≺/⁻-to-≺/ : {x y : α/} → x ≺/⁻ y → x ≺/ y
 ≺/⁻-to-≺/ = ⌜ ≺/-≃-≺/⁻ ⌝⁻¹

 module _ (small-set-quotients : Small-Set-Quotients 𝓤) where

  private
   X : 𝓤 ̇
   X = pr₁ (small-set-quotients ≈R)

   φ : X ≃ α/
   φ = pr₂ (small-set-quotients ≈R)

   resize-ordinal : Σ s ꞉ OrdinalStructure X , (X , s) ≃ₒ α/-Ord
   resize-ordinal = transfer-structure X α/-Ord φ (_≺/⁻_ , (λ x y → ≺/-≃-≺/⁻))

  α/⁻-Ord : Ordinal 𝓤
  α/⁻-Ord = X , pr₁ resize-ordinal

  α/⁻-≃-α/ : α/⁻-Ord ≃ₒ α/-Ord
  α/⁻-≃-α/ = pr₂ resize-ordinal

  α/-≃-α/⁻ : α/-Ord ≃ₒ α/⁻-Ord
  α/-≃-α/⁻ = ≃ₒ-sym α/⁻-Ord α/-Ord α/⁻-≃-α/

  α/⁻-is-upperbound : (i : I) → α i ⊴ α/⁻-Ord
  α/⁻-is-upperbound i = ⊴-trans (α i) α/-Ord α/⁻-Ord
                         (α/-is-upperbound i)
                         (≃ₒ-to-⊴ α/-Ord α/⁻-Ord α/-≃-α/⁻)

  α/⁻-is-lowerbound-of-upperbounds : (β : Ordinal 𝓤)
                                   → ((i : I) → α i ⊴ β)
                                   → α/⁻-Ord ⊴ β
  α/⁻-is-lowerbound-of-upperbounds β β-is-ub =
   ⊴-trans α/⁻-Ord α/-Ord β (≃ₒ-to-⊴ α/⁻-Ord α/-Ord α/⁻-≃-α/)
                            (α/-is-lowerbound-of-upperbounds β β-is-ub)

\end{code}

\begin{code}

module _ (small-set-quotients : Small-Set-Quotients 𝓤) where

  Ordinal-Of-Ordinals-Has-Small-Suprema : 𝓤 ⁺ ̇
  Ordinal-Of-Ordinals-Has-Small-Suprema =
     (I : 𝓤 ̇  ) (α : I → Ordinal 𝓤)
   → Σ β ꞉ Ordinal 𝓤 , ((i : I) → α i ⊴ β)
                     × ((γ : Ordinal 𝓤) → ((i : I) → α i ⊴ γ) → β ⊴ γ)

  Ordinal-Of-Ordinals-Has-Small-Suprema-is-prop :
   is-prop (Ordinal-Of-Ordinals-Has-Small-Suprema)
  Ordinal-Of-Ordinals-Has-Small-Suprema-is-prop =
   Π₂-is-prop fe' h
    where
     h : (I : 𝓤 ̇  ) (α : I → Ordinal 𝓤)
       → is-prop (Σ β ꞉ Ordinal 𝓤 , ((i : I) → α i ⊴ β)
                                  × ((γ : Ordinal 𝓤) → ((i : I) → α i ⊴ γ)
                                                     → β ⊴ γ))
     h I α (β , β-is-ub , β-is-lb) (β' , β'-is-ub , β'-is-lb) =
      to-subtype-≡ (λ β → ×-is-prop
                           (Π-is-prop fe' (λ i → ⊴-is-prop-valued (α i) β))
                           (Π₂-is-prop fe' (λ γ _ → ⊴-is-prop-valued β γ)))
                   (⊴-antisym β β' (β-is-lb β' β'-is-ub) (β'-is-lb β β-is-ub))

  ordinal-of-ordinals-has-small-suprema : Ordinal-Of-Ordinals-Has-Small-Suprema
  ordinal-of-ordinals-has-small-suprema I α =
   (α/⁻-Ord α smq , α/⁻-is-upperbound α smq
                  , α/⁻-is-lowerbound-of-upperbounds α smq)
    where
     smq : Small-Set-Quotients 𝓤
     smq = small-set-quotients

\end{code}

TODO: Formalize Martín's alternative construction of the least upper bound.
