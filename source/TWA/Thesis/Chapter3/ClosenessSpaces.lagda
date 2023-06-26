\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import Notation.Order
open import Naturals.Order
open import TypeTopology.DiscreteAndSeparated
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Quotient
open import UF.Miscelanea
open import MLTT.Two-Properties

open import TWA.Thesis.Chapter2.FiniteDiscrete

module TWA.Thesis.Chapter3.ClosenessSpaces (fe : FunExt) where

-- Definition 3.2.13-16, 21
open import CoNaturals.GenericConvergentSequence
  renaming (ℕ-to-ℕ∞ to _↑
         ; Zero-smallest to zero-minimal
         ; ∞-largest to ∞-maximal)

-- Lemma 3.2.17 [ TODO: Not used anywhere? ]
≤-≼-relationship : (n m : ℕ) → n ≤ m ⇔ (n ↑) ≼ (m ↑)
pr₁ (≤-≼-relationship 0 m) n≤m = zero-minimal (m ↑)
pr₁ (≤-≼-relationship (succ n) (succ m)) n≤m
 = Succ-monotone (n ↑) (m ↑) (pr₁ (≤-≼-relationship n m) n≤m)
pr₂ (≤-≼-relationship 0 m) n≼m = ⋆
pr₂ (≤-≼-relationship (succ n) 0) n≼m
 = Succ-not-≼-Zero (n ↑) n≼m
pr₂ (≤-≼-relationship (succ n) (succ m)) n≼m
 = pr₂ (≤-≼-relationship n m) (Succ-loc (n ↑) (m ↑) n≼m)
 
-- Lemma 3.2.18 [ TODO: Remove from paper ]

-- Lemma 3.2.19
is-decreasing' : (v : ℕ∞) (n : ℕ) → (i : ℕ) → i ≤ n
               → pr₁ v n ＝ ₁ → pr₁ v i ＝ ₁
is-decreasing' v
 = regress (λ z → pr₁ v z ＝ ₁) (λ n → ≤₂-criterion-converse (pr₂ v n))

positive-below-n : (i n : ℕ) → pr₁ (Succ (n ↑)) i ＝ ₁ → i ≤ n 
positive-below-n zero n snᵢ=1 = ⋆
positive-below-n (succ i) (succ n) snᵢ=1 = positive-below-n i n snᵢ=1

≼-left-decidable : (n : ℕ) (v : ℕ∞) → is-decidable ((n ↑) ≼ v)
≼-left-decidable zero v = inl (zero-minimal v)
≼-left-decidable (succ n) v
 = Cases (𝟚-is-discrete (pr₁ v n) ₁)
     (λ  vₙ=1 → inl (λ i snᵢ=1 → is-decreasing' v n i
                                   (positive-below-n i n snᵢ=1) vₙ=1))
     (λ ¬vₙ=1 → inr (λ sn≼v → ¬vₙ=1 (sn≼v n (ℕ-to-ℕ∞-diagonal₁ n))))

-- Definition 3.2.22
open import TWA.Closeness fe hiding (is-ultra; is-closeness)

is-ultra is-closeness : {X : 𝓤 ̇ } → (X → X → ℕ∞) → 𝓤 ̇
is-ultra {𝓤} {X} c
 = (x y z : X) → min (c x y) (c y z) ≼ c x z

is-closeness c
 = indistinguishable-are-equal c
 × self-indistinguishable c
 × is-symmetric c
 × is-ultra c

-- TODO Put in paper
is-pseudocloseness : {X : 𝓤 ̇ } → (X → X → ℕ∞) → 𝓤 ̇ 
is-pseudocloseness c
 = self-indistinguishable c
 × is-symmetric c
 × is-ultra c

is-pseudocloseness-space : (X : 𝓤 ̇ ) → 𝓤 ̇
is-pseudocloseness-space X = Σ c ꞉ (X → X → ℕ∞) , is-pseudocloseness c

PseudoClosenessSpace : (𝓤 : Universe) → 𝓤 ⁺  ̇ 
PseudoClosenessSpace 𝓤
 = Σ X ꞉ 𝓤 ̇ , is-pseudocloseness-space X

⟪_⟫ : PseudoClosenessSpace 𝓤 → 𝓤 ̇ 
⟪ X , _ ⟫ = X

is-closeness-space : (X : 𝓤 ̇ ) → 𝓤 ̇
is-closeness-space X
 = Σ c ꞉ (X → X → ℕ∞)
 , (indistinguishable-are-equal c
 × is-pseudocloseness c)

ClosenessSpace : (𝓤 : Universe) → 𝓤 ⁺  ̇ 
ClosenessSpace 𝓤
 = Σ X ꞉ 𝓤 ̇ , is-closeness-space X

ι : ClosenessSpace 𝓤 → PseudoClosenessSpace 𝓤
ι (X , c , i , p) = X , c , p

⟨_⟩ : ClosenessSpace 𝓤 → 𝓤 ̇
⟨ X , _ ⟩ = X

c⟨_⟩ : (X : ClosenessSpace 𝓤) → ⟨ X ⟩ → ⟨ X ⟩ → ℕ∞
c⟨ (X , c , e , i , s , u) ⟩ = c

e⟨_⟩ : (X : ClosenessSpace 𝓤)
     → indistinguishable-are-equal c⟨ X ⟩
e⟨ (X , c , e , i , s , u) ⟩ = e

i⟨_⟩ : (X : ClosenessSpace 𝓤)
     → self-indistinguishable c⟨ X ⟩
i⟨ (X , c , e , i , s , u) ⟩ = i

s⟨_⟩ : (X : ClosenessSpace 𝓤)
     → is-symmetric c⟨ X ⟩
s⟨ (X , c , e , i , s , u) ⟩ = s

u⟨_⟩ : (X : ClosenessSpace 𝓤)
     → is-ultra c⟨ X ⟩
u⟨ (X , c , e , i , s , u) ⟩ = u

-- Definition 3.2.23 [ Doesn't say in paper that this is an equiv rel ? TODO ]
C' : (X : PseudoClosenessSpace 𝓤) → ℕ → ⟪ X ⟫ → ⟪ X ⟫ → 𝓤₀ ̇   
C' (X , c , _) n x y = (n ↑) ≼ c x y

C'-prop : (X : PseudoClosenessSpace 𝓤) (n : ℕ) → is-prop-valued (C' X n)
C'-prop X n _ _
 = Π-is-prop (fe _ _) (λ _ → Π-is-prop (fe _ _) (λ _ → 𝟚-is-set))

C'-refl : (X : PseudoClosenessSpace 𝓤) (n : ℕ) → reflexive (C' X n)
C'-refl (X , c , e , s , u) n x
 = transport ((n ↑) ≼_) (e x ⁻¹) (∞-maximal (n ↑))

C'-sym : (X : PseudoClosenessSpace 𝓤) (n : ℕ) → symmetric (C' X n) 
C'-sym (X , c , e , s , u) n x y Cxy
 = transport ((n ↑) ≼_) (s x y) Cxy

C'-trans : (X : PseudoClosenessSpace 𝓤) (n : ℕ) → transitive (C' X n)
C'-trans (X , c , e , s , u) n x y z Cxy Cyz m π
 = u x y z m (Lemma[a＝₁→b＝₁→min𝟚ab＝₁] (Cxy m π) (Cyz m π))

C'-decidable : (X : PseudoClosenessSpace 𝓤) (n : ℕ)
             → (x y : ⟪ X ⟫) → is-decidable (C' X n x y)
C'-decidable (X , c , _) n x y = ≼-left-decidable n (c x y)

C : (X : ClosenessSpace 𝓤) → ℕ → ⟨ X ⟩ → ⟨ X ⟩ → 𝓤₀ ̇   
C = C' ∘ ι

C-prop : (X : ClosenessSpace 𝓤) (n : ℕ) → is-prop-valued (C X n)
C-prop = C'-prop ∘ ι

C-refl : (X : ClosenessSpace 𝓤) (n : ℕ) → reflexive (C X n)
C-refl = C'-refl ∘ ι

C-sym : (X : ClosenessSpace 𝓤) (n : ℕ) → symmetric (C X n) 
C-sym = C'-sym ∘ ι

C-trans : (X : ClosenessSpace 𝓤) (n : ℕ) → transitive (C X n)
C-trans = C'-trans ∘ ι

C-decidable : (X : ClosenessSpace 𝓤) (n : ℕ)
            → (x y : ⟨ X ⟩ ) → is-decidable (C X n x y)
C-decidable = C'-decidable ∘ ι

C-is-eq : (X : ClosenessSpace 𝓤) (n : ℕ)
        → is-equiv-relation (C X n)
C-is-eq X n = C-prop X n , C-refl X n , C-sym X n , C-trans X n

C'Ω : (X : PseudoClosenessSpace 𝓤) → ℕ → ⟪ X ⟫ → ⟪ X ⟫ → Ω 𝓤₀   
C'Ω X n x y = C' X n x y , C'-prop X n x y

CΩ : (X : ClosenessSpace 𝓤) → ℕ → ⟨ X ⟩ → ⟨ X ⟩ → Ω 𝓤₀   
CΩ X n x y = C X n x y , C-prop X n x y

C⁼ : (X : ClosenessSpace 𝓤) (n : ℕ) → EqRel ⟨ X ⟩
C⁼ X n = C X n , C-is-eq X n

C-pred : (X : ClosenessSpace 𝓤)
       → (ε : ℕ)
       → (x y : ⟨ X ⟩)
       → C X (succ ε) x y
       → C X ε x y
C-pred X ε x y Csεxy n n⊏ε
 = Csεxy n (⊏-trans n ε (Succ (ε ↑)) n⊏ε (ℕ-to-ℕ∞-diagonal₁ ε))

C-prev : (X : ClosenessSpace 𝓤)
       → (n i : ℕ)
       → i ≤ n
       → (x y : ⟨ X ⟩)
       → C X n x y
       → C X i x y
C-prev X n i i≤n x y Cnxy k k⊏i
 = Cnxy k (<-gives-⊏ k n (<-≤-trans k i n (⊏-gives-< k i k⊏i) i≤n))

identical-implies-closeness-∞ : (X : ClosenessSpace 𝓤)
                              → (x y : ⟨ X ⟩)
                              → x ＝ y
                              → c⟨ X ⟩ x y ＝ ∞
identical-implies-closeness-∞ X x x refl = i⟨ X ⟩ x

closeness-∞-implies-ϵ-close : (X : ClosenessSpace 𝓤)
                            → (x y : ⟨ X ⟩)
                            → c⟨ X ⟩ x y ＝ ∞
                            → (ε : ℕ) → C X ε x y
closeness-∞-implies-ϵ-close X x y cxy＝∞ ε n _
 = ap (λ - → pr₁ - n) cxy＝∞

C-id : (X : ClosenessSpace 𝓤)
     → (n : ℕ)
     → (x y : ⟨ X ⟩)
     → x ＝ y
     → C X n x y
C-id X n x x refl = C-refl X n x

-- Definition 3.2.24 [ not needed ? ]

-- Definition 3.2.25
f-continuous' : (X : PseudoClosenessSpace 𝓤) (Y : PseudoClosenessSpace 𝓥)
              → (f : ⟪ X ⟫ → ⟪ Y ⟫) → 𝓤 ̇  
f-continuous' X Y f
 = (ϵ : ℕ) → (x₁ : ⟪ X ⟫) → Σ δ ꞉ ℕ , ((x₂ : ⟪ X ⟫)
 → C' X δ x₁ x₂ → C' Y ϵ (f x₁) (f x₂))

f-continuous : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
             → (f : ⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇  
f-continuous X Y = f-continuous' (ι X) (ι Y)

-- Definition 3.2.26
f-ucontinuous' : (X : PseudoClosenessSpace 𝓤) (Y : PseudoClosenessSpace 𝓥)
               → (f : ⟪ X ⟫ → ⟪ Y ⟫) → 𝓤 ̇  
f-ucontinuous' X Y f
 = (ϵ : ℕ) → Σ δ ꞉ ℕ , ((x₁ x₂ : ⟪ X ⟫)
 → C' X δ x₁ x₂ → C' Y ϵ (f x₁) (f x₂))

f-ucontinuous : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
              → (f : ⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇  
f-ucontinuous X Y = f-ucontinuous' (ι X) (ι Y)

-- Lemma 3.2.27
ucontinuous-continuous : (X : ClosenessSpace 𝓤)
                       → (Y : ClosenessSpace 𝓥)
                       → (f : ⟨ X ⟩ → ⟨ Y ⟩)
                       → f-ucontinuous X Y f
                       → f-continuous  X Y f
ucontinuous-continuous X Y f ϕ ϵ x₁ = pr₁ (ϕ ϵ)  , pr₂ (ϕ ϵ) x₁

-- Definition 3.2.28
p-ucontinuous'-with-mod : (X : PseudoClosenessSpace 𝓤)
                        → (p : ⟪ X ⟫ → Ω 𝓦) → ℕ → 𝓤 ⊔ 𝓦  ̇
p-ucontinuous'-with-mod X p δ
 = (x₁ x₂ : ⟪ X ⟫) → C' X δ x₁ x₂ → (p x₁ holds → p x₂ holds)

p-ucontinuous' : (X : PseudoClosenessSpace 𝓤)
               → (p : ⟪ X ⟫ → Ω 𝓦) → 𝓤 ⊔ 𝓦  ̇  
p-ucontinuous' X p
 = Σ δ ꞉ ℕ , p-ucontinuous'-with-mod X p δ

p-ucontinuous-with-mod : (X : ClosenessSpace 𝓤)
                       → (p : ⟨ X ⟩ → Ω 𝓦) → ℕ → 𝓤 ⊔ 𝓦  ̇
p-ucontinuous-with-mod X p δ = p-ucontinuous'-with-mod (ι X) p δ

p-ucontinuous : (X : ClosenessSpace 𝓤)
              → (p : ⟨ X ⟩ → Ω 𝓦) → 𝓤 ⊔ 𝓦  ̇  
p-ucontinuous X p 
 = Σ δ ꞉ ℕ , p-ucontinuous-with-mod X p δ
          
-- Examples 3.2.3 [ TODO Finish file ]
-- in Thesis.Chapter3.ClosenessSpaces-Examples fe

-- Definition 3.3.2 [ TODO in paper needs to be a closeness space, not a general type ]
{- First, some things TODO put in Section 2 -}
_is_net-of_ : (X' : 𝓤'  ̇ ) → ℕ → ClosenessSpace 𝓤 → 𝓤 ⊔ 𝓤'  ̇
X' is ϵ net-of X
 = (Σ g ꞉ (  X'  → ⟨ X ⟩)
 , Σ h ꞉ (⟨ X ⟩ →   X' )
 , ((x : ⟨ X ⟩) → C X ϵ x (g (h x))))
 × finite-discrete X'

-- Definition 3.3.3
-- COMMENT: Discuss totally bounded definition (using correct finite)
totally-bounded : ClosenessSpace 𝓤 → (𝓤' : Universe) → 𝓤 ⊔ (𝓤' ⁺)  ̇ 
totally-bounded X 𝓤' = (ϵ : ℕ) → Σ X' ꞉ 𝓤' ̇ , X' is ϵ net-of X

\end{code}
[ TODO: Put the below in a module or remove it from paper entirely ]

open set-quotients-exist sq

semi-searchable : (C : ClosenessSpace {𝓤}) → 𝓤 ⊔ 𝓦 ⁺  ̇ 
semi-searchable {𝓤} {𝓦} (X , ci)
 = (n : ℕ) → searchable {𝓤} {𝓦} (X / cloeq (X , ci) n)

open extending-relations-to-quotient

quotient-uc-predicate : ((X , ci) : ClosenessSpace {𝓤})
                      → (p : X → Ω 𝓦)
                      → ((δ , _) : u-continuous-pred (X , ci) p)
                      → Σ p' ꞉ (X / cloeq (X , ci) δ → Ω 𝓦)
                      , ((x : X)
                      → (p' (η/ (cloeq (X , ci) δ) x)) ＝ (p x))
quotient-uc-predicate (X , c , i) p (δ , ϕ)
 = pr₁ (/-universality (cloeq (X , c , i) δ) (Ω-is-set (fe _ _) (pe _))
     p (λ η → Ω-extensionality (fe _ _) (pe _)
     (pr₁ (ϕ _ _ η)) (pr₂ (ϕ _ _ η))))

quotient-uc-predicate⇔ : ((X , ci) : ClosenessSpace {𝓤})
                       → (p : X → Ω 𝓦)
                       → ((δ , ϕ) : u-continuous-pred (X , ci) p)
                       → ((x : X)
                       → let p' = pr₁ (quotient-uc-predicate (X , ci) p (δ , ϕ)) in
                         (p' (η/ (cloeq (X , ci) δ) x)) holds
                       ⇔ (p x) holds)
quotient-uc-predicate⇔ C p ϕ x
 = transport (_holds) (pr₂ (quotient-uc-predicate C p ϕ) x   )
 , transport (_holds) (pr₂ (quotient-uc-predicate C p ϕ) x ⁻¹)

semi-searchable⇒c-searchable : ((X , ci) : ClosenessSpace {𝓤})
                             → ((n : ℕ) → has-section (η/ (cloeq (X , ci) n)))
                             → semi-searchable {𝓤} {𝓦} (X , ci)
                             →    c-searchable {𝓤} {𝓦} (X , ci)
semi-searchable⇒c-searchable {𝓤} {𝓦} (X , ci) r S p (δ , ϕ)
 = x₀ , λ (x , px) → p'→p x₀
          (transport (λ - → p' - holds)
            γ₀ (γ₀/ (η/ (cloeq (X , ci) δ) x , p→p' x px)))
 where
   X/ = X / cloeq (X , ci) δ
   p' : X/ → Ω 𝓦
   p' = pr₁ (quotient-uc-predicate (X , ci) p (δ , ϕ))
   p'→p : (x : X) → p' (η/ (cloeq (X , ci) δ) x) holds → (p x holds)
   p'→p x = pr₁ (quotient-uc-predicate⇔ (X , ci) p (δ , ϕ) x)
   p→p' : (x : X) → (p x holds) → p' (η/ (cloeq (X , ci) δ) x) holds
   p→p' x = pr₂ (quotient-uc-predicate⇔ (X , ci) p (δ , ϕ) x)
   ζ = S δ p'
   x₀/ : X / cloeq (X , ci) δ
   x₀/ = pr₁ ζ
   γ₀/ : (Σ x ꞉ X/ , p' x holds) → p' x₀/ holds
   γ₀/ = pr₂ ζ
   x₀ : X
   x₀ = pr₁ (r δ) x₀/
   γ₀ : x₀/ ＝ η/ (cloeq (X , ci) δ) x₀
   γ₀ = pr₂ (r δ) x₀/ ⁻¹
   
