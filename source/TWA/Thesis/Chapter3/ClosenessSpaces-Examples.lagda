\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import CoNaturals.GenericConvergentSequence
 renaming (ℕ-to-ℕ∞ to _↑)
open import Notation.Order
open import Naturals.Order
open import Naturals.Properties
open import NotionsOfDecidability.Complemented
open import TypeTopology.DiscreteAndSeparated
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Quotient
open import UF.Miscelanea
open import UF.Embeddings
open import MLTT.Two-Properties
open import Fin.Variation

module TWA.Thesis.Chapter3.ClosenessSpaces-Examples (fe : FunExt) where

open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter2.Vectors
open import TWA.Thesis.Chapter2.FiniteDiscrete
open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Closeness fe hiding (is-ultra; is-closeness)

open import UF.Equiv

-- Move to ClosenessSpaces
𝟙-finite-discrete : finite-discrete (𝟙 {𝓦})
𝟙-finite-discrete = 1 , qinveq g (h , η , μ)
 where
  g : 𝔽 1 → 𝟙
  g _ = ⋆
  h : 𝟙 → 𝔽 1
  h _ = inl ⋆
  η : (λ _ → inl ⋆) ∼ id
  η (inl ⋆) = refl
  η (inr ())
  μ : (λ _ → ⋆) ∼ id
  μ ⋆ = refl 

pointed : 𝓤 ̇ → 𝓤 ̇
pointed X = X

pointed-has-a-0-net : (X : ClosenessSpace 𝓤)
                    → pointed ⟨ X ⟩
                    → Σ X' ꞉ 𝓦 ̇ , (X' is 0 net-of X)
pointed-has-a-0-net X x
 = 𝟙 , ((λ _ → x) , (λ _ → ⋆) , λ _ _ ()) , 𝟙-finite-discrete

open import UF.Equiv
open import Fin.Type
open import Fin.ArithmeticViaEquivalence
open import UF.EquivalenceExamples

-- TODO: Maybe change to use Martin's Fin type
𝔽-≃ : {n : ℕ} → 𝔽 n ≃ Fin n
𝔽-≃ {n} = qinveq g (h , η , μ)
 where
  g : {n : ℕ} → 𝔽 n → Fin n
  g {succ n} (inl ⋆) = 𝟎
  g {succ n} (inr x) = suc (g x)
  h : {n : ℕ} → Fin n → 𝔽 n
  h {succ n} 𝟎       = inl ⋆
  h {succ n} (suc x) = inr (h x)
  η : {n : ℕ} → (λ (x : 𝔽 n) → h (g x)) ∼ (λ x → x)
  η {succ n} (inl ⋆) = refl
  η {succ n} (inr x) = ap inr (η x)
  μ : {n : ℕ} → (λ (x : Fin n) → g (h x)) ∼ (λ x → x)
  μ {succ n} 𝟎       = refl
  μ {succ n} (suc x) = ap suc (μ x)

+-preserves-finite-discrete : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                            → finite-discrete X
                            → finite-discrete Y
                            → finite-discrete (X + Y)
+-preserves-finite-discrete (n , e) (m , f) =
 n +' m , (𝔽-≃
        ● Fin+homo n m
        ● +-cong (≃-sym 𝔽-≃) (≃-sym 𝔽-≃)
        ● +-cong e f)

×-preserves-finite-discrete : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                            → finite-discrete X
                            → finite-discrete Y
                            → finite-discrete (X × Y)
×-preserves-finite-discrete (n , e) (m , f) =
 n ×' m , (𝔽-≃
        ● Fin×homo n m
        ● ×-cong (≃-sym 𝔽-≃) (≃-sym 𝔽-≃)
        ● ×-cong e f)

Vec-finite-discrete : {F : 𝓤 ̇ } (ϵ : ℕ) → finite-discrete F
                    → finite-discrete (Vec F ϵ)
Vec-finite-discrete {𝓤} {F} zero (n , f) = 1 , qinveq g (h , η , μ)
 where
  g : 𝔽 1 → Vec F zero
  g _ = []
  h : Vec F zero → 𝔽 1
  h _ = inl ⋆
  η : (λ x → h (g x)) ∼ (λ x → x)
  η (inl ⋆) = refl
  μ : (λ x → g (h x)) ∼ (λ x → x)
  μ [] = refl
Vec-finite-discrete {𝓤} {F} (succ ϵ) (n , f)
 = n ×' m , (𝔽-≃
          ● Fin×homo n m
          ● ×-cong (≃-sym 𝔽-≃) (≃-sym 𝔽-≃)
          ● ×-cong f (pr₂ IH)
          ● qinveq g (h , η , μ))
 where
  IH : finite-discrete (Vec F ϵ)
  IH = Vec-finite-discrete ϵ (n , f)
  m : ℕ
  m = pr₁ IH
  g : F × Vec F ϵ → Vec F (succ ϵ)
  g (f , vs) = f ∷ vs
  h : Vec F (succ ϵ) → F × Vec F ϵ
  h (f ∷ vs) = f , vs
  η : (λ x → h (g x)) ∼ (λ x → x)
  η (f , vs) = refl
  μ : (λ x → g (h x)) ∼ (λ x → x)
  μ (f ∷ vs) = refl

dep-vec : {n : ℕ} (Y : 𝔽 (succ n) → 𝓤 ̇ ) → 𝓤 ̇
dep-vec {𝓤} {zero} Y = Y (inl ⋆)
dep-vec {𝓤} {succ n} Y = Y (inl ⋆) × dep-vec (Y ∘ inr)




-- Discrete closeness spaces

discrete-clofun'' : {X : 𝓤 ̇ } (x y : X)
                  → is-decidable (x ＝ y)
                  → ℕ∞
discrete-clofun'' x y (inl _) = ∞
discrete-clofun'' x y (inr _) = 0 ↑

discrete-clofun' : {X : 𝓤 ̇ } → is-discrete X → X → X → ℕ∞
discrete-clofun' d x y = discrete-clofun'' x y (d x y)

discrete-clofun''-e : {X : 𝓤 ̇ } (x y : X)
                    → (d : is-decidable (x ＝ y))
                    → discrete-clofun'' x y d ＝ ∞ → x ＝ y
discrete-clofun''-e x y (inl e) cxy＝∞ = e
discrete-clofun''-e x y (inr f) cxy＝∞ 
 = 𝟘-elim (zero-is-not-one (ap (λ - → pr₁ - 0) cxy＝∞))

discrete-clofun''-i : {X : 𝓤 ̇ } (x : X)
                    → (d : is-decidable (x ＝ x))
                    → discrete-clofun'' x x d ＝ ∞
discrete-clofun''-i x (inl _) = refl
discrete-clofun''-i x (inr f) = 𝟘-elim (f refl)

discrete-clofun''-s : {X : 𝓤 ̇ } (x y : X)
                    → (d  : is-decidable (x ＝ y))
                    → (d' : is-decidable (y ＝ x))
                    → discrete-clofun'' x y d
                    ＝ discrete-clofun'' y x d'
discrete-clofun''-s x y (inl _) (inl _) = refl
discrete-clofun''-s x y (inr _) (inr _) = refl
discrete-clofun''-s x y (inl e) (inr f) = 𝟘-elim (f (e ⁻¹))
discrete-clofun''-s x y (inr f) (inl e) = 𝟘-elim (f (e ⁻¹))
                                           
discrete-clofun''-u : {X : 𝓤 ̇ } (x y z : X)
                    → (d   : is-decidable (x ＝ y))
                    → (d'  : is-decidable (y ＝ z))
                    → (d'' : is-decidable (x ＝ z))
                    → min (discrete-clofun'' x y d  )
                          (discrete-clofun'' y z d' )
                         ≼ discrete-clofun'' x z d''
discrete-clofun''-u x y z      _       _  (inl _) _ _
 = refl
discrete-clofun''-u x y z (inl _) (inr _) (inr _) _
 = id
discrete-clofun''-u x y z (inr _)      _  (inr _) _
 = id
discrete-clofun''-u x x x (inl refl) (inl refl) (inr f)
 = 𝟘-elim (f refl)

discrete-clofun'-is-clofun : {X : 𝓤 ̇ } (d : is-discrete X)
                           → is-closeness (discrete-clofun' d)
discrete-clofun'-is-clofun d
 = (λ x y   → discrete-clofun''-e x y (d x y))
 , (λ x     → discrete-clofun''-i x (d x x))
 , (λ x y   → discrete-clofun''-s x y (d x y) (d y x))
 , (λ x y z → discrete-clofun''-u x y z (d x y) (d y z) (d x z))

discrete-clospace : {X : 𝓤 ̇ } (d : is-discrete X)
                  → is-closeness-space X
discrete-clospace d
 = discrete-clofun' d , discrete-clofun'-is-clofun d

D-ClosenessSpace : {X : 𝓤 ̇ } → is-discrete X → ClosenessSpace 𝓤
D-ClosenessSpace {𝓤} {X} d = X , discrete-clospace d

finite-discrete-totally-bounded
 : {X : 𝓤 ̇ } (f : finite-discrete X)
 → pointed X
 → let d = finite-discrete-is-discrete f in
   totally-bounded (D-ClosenessSpace d) 𝓤
finite-discrete-totally-bounded f x 0
 = pointed-has-a-0-net (D-ClosenessSpace d) x
 where d = finite-discrete-is-discrete f
finite-discrete-totally-bounded {𝓤} {X} f x (succ ε)
 = X , (id , id , η) , f
 where
  d = finite-discrete-is-discrete f
  η : (x : X) → C (D-ClosenessSpace d) (succ ε) x x
  η x n _ = ap (λ - → pr₁ - n) (i⟨ D-ClosenessSpace d ⟩ x)

discrete-apart-implies-closeness-0
 : {X : 𝓤 ̇ }
 → (d : is-discrete X)
 → (x y : X)
 → x ≠ y
 → c⟨ D-ClosenessSpace d ⟩ x y ＝ 0 ↑
discrete-apart-implies-closeness-0 d x y f with d x y
... | inl e = 𝟘-elim (f e)
... | inr _ = refl

-- Disjoint union of closeness spaces

+-clofun' : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
          → (⟨ X ⟩ + ⟨ Y ⟩ → ⟨ X ⟩ + ⟨ Y ⟩ → ℕ∞)
+-clofun' X Y (inl x₁) (inl x₂) = c⟨ X ⟩ x₁ x₂
+-clofun' X Y (inr y₁) (inr y₂) = c⟨ Y ⟩ y₁ y₂
+-clofun' X Y (inl x₁) (inr y₂) = 0 ↑
+-clofun' X Y (inr y₁) (inl x₂) = 0 ↑

+-clofun'-e : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → indistinguishable-are-equal (+-clofun' X Y)
+-clofun'-e X Y (inl x₁) (inl x₂) q
 = ap inl (e⟨ X ⟩ x₁ x₂ q)
+-clofun'-e X Y (inr y₁) (inr y₂) q
 = ap inr (e⟨ Y ⟩ y₁ y₂ q)
+-clofun'-e X Y (inl x₁) (inr y₂) f
 = 𝟘-elim (zero-is-not-one (ap (λ - → pr₁ - 0) f))
+-clofun'-e X Y (inr y₁) (inl x₂) f
 = 𝟘-elim (zero-is-not-one (ap (λ - → pr₁ - 0) f))

+-clofun'-i : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → self-indistinguishable (+-clofun' X Y)
+-clofun'-i X Y (inl x) = i⟨ X ⟩ x
+-clofun'-i X Y (inr y) = i⟨ Y ⟩ y

+-clofun'-s : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → is-symmetric (+-clofun' X Y)
+-clofun'-s X Y (inl x₁) (inl x₂) = s⟨ X ⟩ x₁ x₂
+-clofun'-s X Y (inr y₁) (inr y₂) = s⟨ Y ⟩ y₁ y₂
+-clofun'-s X Y (inl x₁) (inr y₂) = refl
+-clofun'-s X Y (inr y₁) (inl x₂) = refl

+-clofun'-u : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → is-ultra (+-clofun' X Y)
+-clofun'-u X Y (inl x₁) (inl x₂) (inl x₃) = u⟨ X ⟩ x₁ x₂ x₃
+-clofun'-u X Y (inr y₁) (inr y₂) (inr y₃) = u⟨ Y ⟩ y₁ y₂ y₃
+-clofun'-u X Y (inl x₁) (inl x₂) (inr y₃) n mina₀＝₁
 = Lemma[min𝟚ab＝₀] (inr refl) ⁻¹ ∙ mina₀＝₁
+-clofun'-u X Y (inr y₁) (inr y₂) (inl x₃) n mina₀＝₁
 = Lemma[min𝟚ab＝₀] (inr refl) ⁻¹ ∙ mina₀＝₁
+-clofun'-u X Y (inl x₁) (inr y₂) _ _ ()
+-clofun'-u X Y (inr y₁) (inl x₂) _ _ ()

+-clofun'-is-clofun : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
                    → is-closeness (+-clofun' X Y)
+-clofun'-is-clofun X Y 
 = +-clofun'-e X Y
 , +-clofun'-i X Y
 , +-clofun'-s X Y
 , +-clofun'-u X Y
 
+-clospace : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
           → is-closeness-space (⟨ X ⟩ + ⟨ Y ⟩)
+-clospace X Y = +-clofun' X Y , +-clofun'-is-clofun X Y

+-ClosenessSpace : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
                 → ClosenessSpace (𝓤 ⊔ 𝓥)
+-ClosenessSpace X Y = (⟨ X ⟩ + ⟨ Y ⟩) , +-clospace X Y

+-preserves-nets : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
                 → (ε : ℕ)
                 → (X' : 𝓤' ̇ ) (Y' : 𝓥' ̇ )
                 → X' is ε net-of X
                 → Y' is ε net-of Y
                 → (X' + Y') is ε net-of (+-ClosenessSpace X Y)
+-preserves-nets X Y ε X' Y'
 ((gx , hx , ηx) , fx) ((gy , hy , ηy) , fy) = (g , h , η) , f
 where
  g :   X'   +   Y'   → ⟨  X ⟩ + ⟨ Y ⟩
  g (inl x') = inl (gx x')
  g (inr y') = inr (gy y')
  h : ⟨ X  ⟩ + ⟨ Y  ⟩ →    X'  +   Y'
  h (inl x ) = inl (hx x)
  h (inr y ) = inr (hy y)
  η : (x : ⟨ X ⟩ + ⟨ Y ⟩) → C (+-ClosenessSpace X Y) ε x (g (h x))
  η (inl x ) = ηx x
  η (inr y ) = ηy y
  f : finite-discrete (X' + Y')
  f = +-preserves-finite-discrete fx fy
                 
+-totally-bounded : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
                  → totally-bounded X 𝓤'
                  → totally-bounded Y 𝓥'
                  → totally-bounded (+-ClosenessSpace X Y) (𝓤' ⊔ 𝓥')
+-totally-bounded X Y tx ty ε
 = (X' + Y') , (+-preserves-nets X Y ε X' Y' X'-is-ε-net Y'-is-ε-net)
 where
  X' = pr₁ (tx ε)
  Y' = pr₁ (ty ε)
  X'-is-ε-net = pr₂ (tx ε)
  Y'-is-ε-net = pr₂ (ty ε)

-- Binary product of closeness spaces

×-clofun' : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
          → (⟨ X ⟩ × ⟨ Y ⟩ → ⟨ X ⟩ × ⟨ Y ⟩ → ℕ∞)
×-clofun' X Y (x₁ , y₁) (x₂ , y₂)
 = min (c⟨ X ⟩ x₁ x₂) (c⟨ Y ⟩ y₁ y₂)

min-∞-l : (u v : ℕ∞) → min u v ＝ ∞ → u ＝ ∞ 
min-∞-l u v min＝∞
 = to-subtype-＝ (being-decreasing-is-prop (fe _ _))
     (dfunext (fe _ _)
       (λ i → Lemma[min𝟚ab＝₁→a＝₁] (ap (λ - → pr₁ - i) min＝∞)))
       
min-∞-r : (u v : ℕ∞) → min u v ＝ ∞ → v ＝ ∞ 
min-∞-r u v min＝∞
 = to-subtype-＝ (being-decreasing-is-prop (fe _ _))
     (dfunext (fe _ _)
       (λ i → Lemma[min𝟚ab＝₁→b＝₁] (ap (λ - → pr₁ - i) min＝∞)))

×-clofun'-e : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → indistinguishable-are-equal (×-clofun' X Y)
×-clofun'-e X Y (x₁ , y₁) (x₂ , y₂) cxy＝∞
 = ap (_, y₁) (e⟨ X ⟩ x₁ x₂ cx＝∞) ∙ ap (x₂ ,_) (e⟨ Y ⟩ y₁ y₂ cy＝∞)
 where
  cx＝∞ : c⟨ X ⟩ x₁ x₂ ＝ ∞
  cx＝∞ = min-∞-l (c⟨ X ⟩ x₁ x₂) (c⟨ Y ⟩ y₁ y₂) cxy＝∞
  cy＝∞ : c⟨ Y ⟩ y₁ y₂ ＝ ∞
  cy＝∞ = min-∞-r (c⟨ X ⟩ x₁ x₂) (c⟨ Y ⟩ y₁ y₂) cxy＝∞

×-clofun'-i : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → self-indistinguishable (×-clofun' X Y)
×-clofun'-i X Y (x , y)
 = ap (λ - → min - (c⟨ Y ⟩ y y)) (i⟨ X ⟩ x)
 ∙ ap (      min ∞             ) (i⟨ Y ⟩ y)

×-clofun'-s : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → is-symmetric (×-clofun' X Y)
×-clofun'-s X Y (x₁ , y₁) (x₂ , y₂)
 = ap (λ - → min - (c⟨ Y ⟩ y₁ y₂)) (s⟨ X ⟩ x₁ x₂)
 ∙ ap (      min (c⟨ X ⟩ x₂ x₁)  ) (s⟨ Y ⟩ y₁ y₂)

min𝟚-abcd : {a b c d : 𝟚} → a ＝ c → b ＝ d → min𝟚 a b ＝ min𝟚 c d
min𝟚-abcd {a} {b} {.a} {.b} refl refl = refl

min𝟚-abcd-ac : (a b c d : 𝟚)
             → min𝟚 (min𝟚 a b) (min𝟚 c d) ＝ ₁
             → min𝟚 a c ＝ ₁
min𝟚-abcd-ac ₁ ₁ ₁ ₁ e = refl

min𝟚-abcd-bd : (a b c d : 𝟚)
             → min𝟚 (min𝟚 a b) (min𝟚 c d) ＝ ₁
             → min𝟚 b d ＝ ₁
min𝟚-abcd-bd ₁ ₁ ₁ ₁ e = refl

minℕ∞-abcdef : (a b c d e f : ℕ∞)
             → min a b ≼ e → min c d ≼ f
             → min (min a c) (min b d) ≼ min e f
minℕ∞-abcdef a b c d e f mab≼e mcd≼f n minabcd＝₁
 = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
     (mab≼e n (min𝟚-abcd-ac
       (pr₁ a n) (pr₁ c n) (pr₁ b n) (pr₁ d n) minabcd＝₁))
     (mcd≼f n (min𝟚-abcd-bd
       (pr₁ a n) (pr₁ c n) (pr₁ b n) (pr₁ d n) minabcd＝₁))

×-clofun'-u : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → is-ultra (×-clofun' X Y)
×-clofun'-u X Y (x₁ , y₁) (x₂ , y₂) (x₃ , y₃)
 = minℕ∞-abcdef
     (c⟨ X ⟩ x₁ x₂) (c⟨ X ⟩ x₂ x₃)
     (c⟨ Y ⟩ y₁ y₂) (c⟨ Y ⟩ y₂ y₃)
     (c⟨ X ⟩ x₁ x₃) (c⟨ Y ⟩ y₁ y₃)
     (u⟨ X ⟩ x₁ x₂ x₃) (u⟨ Y ⟩ y₁ y₂ y₃)

×-clofun'-is-clofun : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
                    → is-closeness (×-clofun' X Y)
×-clofun'-is-clofun X Y 
 = ×-clofun'-e X Y
 , ×-clofun'-i X Y
 , ×-clofun'-s X Y
 , ×-clofun'-u X Y

×-clospace : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
           → is-closeness-space (⟨ X ⟩ × ⟨ Y ⟩)
×-clospace X Y = ×-clofun' X Y , ×-clofun'-is-clofun X Y

×-ClosenessSpace : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
                 → ClosenessSpace (𝓤 ⊔ 𝓥)
×-ClosenessSpace X Y = (⟨ X ⟩ × ⟨ Y ⟩) , (×-clospace X Y)

×-C-left  : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
          → (x₁ x₂ : ⟨ X ⟩) (y₁ y₂ : ⟨ Y ⟩)
          → (ε : ℕ) → C (×-ClosenessSpace X Y) ε (x₁ , y₁) (x₂ , y₂)
          → C X ε x₁ x₂
×-C-left  X Y x₁ x₂ y₁ y₂ ε Cxy n = Lemma[min𝟚ab＝₁→a＝₁] ∘ (Cxy n)

×-C-right : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
          → (x₁ x₂ : ⟨ X ⟩) (y₁ y₂ : ⟨ Y ⟩)
          → (ε : ℕ) → C (×-ClosenessSpace X Y) ε (x₁ , y₁) (x₂ , y₂)
          → C Y ε y₁ y₂
×-C-right X Y x₁ x₂ y₁ y₂ ε Cxy n = Lemma[min𝟚ab＝₁→b＝₁] ∘ (Cxy n)

×-C-combine : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → (x₁ x₂ : ⟨ X ⟩) (y₁ y₂ : ⟨ Y ⟩)
            → (ε : ℕ)
            → C X ε x₁ x₂
            → C Y ε y₁ y₂
            → C (×-ClosenessSpace X Y) ε (x₁ , y₁) (x₂ , y₂)
×-C-combine X Y x₁ x₂ y₁ y₂ ε Cεx₁x₂ Cεy₁y₂ n n⊏ε
 = Lemma[a＝₁→b＝₁→min𝟚ab＝₁] (Cεx₁x₂ n n⊏ε) (Cεy₁y₂ n n⊏ε)

×-preserves-nets : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
                 → (ε : ℕ)
                 → (X' : 𝓤' ̇ ) (Y' : 𝓥' ̇ )
                 → X' is ε net-of X
                 → Y' is ε net-of Y
                 → (X' × Y') is ε net-of (×-ClosenessSpace X Y)
×-preserves-nets X Y ε X' Y'
 ((gx , hx , ηx) , fx) ((gy , hy , ηy) , fy) = (g , h , η) , f
 where
  g :   X'   ×   Y'   → ⟨  X ⟩ × ⟨ Y ⟩
  g (x' , y') = gx x' , gy y'
  h : ⟨ X  ⟩ × ⟨ Y  ⟩ →    X'  ×   Y'
  h (x  , y ) = hx x  , hy y
  η : (x : ⟨ X ⟩ × ⟨ Y ⟩) → C (×-ClosenessSpace X Y) ε x (g (h x))
  η (x  , y )
   = ×-C-combine X Y x (gx (hx x)) y (gy (hy y)) ε (ηx x) (ηy y)
  f : finite-discrete (X' × Y')
  f = ×-preserves-finite-discrete fx fy
                 
×-totally-bounded : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
                  → totally-bounded X 𝓤'
                  → totally-bounded Y 𝓥'
                  → totally-bounded (×-ClosenessSpace X Y) (𝓤' ⊔ 𝓥')
×-totally-bounded X Y tx ty ε
 = (X' × Y') , (×-preserves-nets X Y ε X' Y' X'-is-ε-net Y'-is-ε-net)
 where
  X' = pr₁ (tx ε)
  Y' = pr₁ (ty ε)
  X'-is-ε-net = pr₂ (tx ε)
  Y'-is-ε-net = pr₂ (ty ε)

-- Subtype closeness spaces

↪-clospace : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X ↪ Y)
           → is-closeness-space Y
           → is-closeness-space X
↪-clospace {𝓤} {𝓥} {X} {Y} (f , η) (cy , ey , iy , sy , uy)
 = c , e , i , s , u
 where
  c : X → X → ℕ∞
  c x y = cy (f x) (f y)
  e : indistinguishable-are-equal c
  e x y cxy＝∞
   = ap pr₁ (η (f y) (x , ey (f x) (f y) cxy＝∞) (y , refl))
  i : self-indistinguishable c
  i x = iy (f x)
  s : is-symmetric c
  s x y = sy (f x) (f y)
  u : is-ultra c
  u x y z = uy (f x) (f y) (f z)                  

↪-ClosenessSpace : {X : 𝓤 ̇ } (Y : ClosenessSpace 𝓥)
                 → X ↪ ⟨ Y ⟩
                 → ClosenessSpace 𝓤
↪-ClosenessSpace {𝓤} {𝓥} {X} Y f = X , ↪-clospace f (pr₂ Y)                 

Σ-ClosenessSpace : (X : ClosenessSpace 𝓤)
                 → (P : ⟨ X ⟩ → 𝓥 ̇ )
                 → (p : (x : ⟨ X ⟩) → is-prop (P x))
                 → ClosenessSpace (𝓤 ⊔ 𝓥)
Σ-ClosenessSpace {𝓤} {𝓥} X P p
 = ↪-ClosenessSpace X (pr₁ , (pr₁-is-embedding p))

≃-ClosenessSpace : {X : 𝓤 ̇} (Y : ClosenessSpace 𝓥)
                 → X ≃ ⟨ Y ⟩
                 → ClosenessSpace 𝓤
≃-ClosenessSpace Y e
  = ↪-ClosenessSpace Y (equivs-embedding e)                      

≃-preserves-nets : {X : 𝓤 ̇ } (Y : ClosenessSpace 𝓥)
                 → (e : X ≃ ⟨ Y ⟩)
                 → (ε : ℕ)
                 → (Y' : 𝓥'  ̇ )
                 → Y' is ε net-of Y
                 → Y' is ε net-of (≃-ClosenessSpace Y e)
≃-preserves-nets Y (f , ((g , η) , (h , μ))) ε Y' ((gₙ , hₙ , ηₙ) , fₙ)
 = (g ∘ gₙ , hₙ ∘ f
 , λ x
 → C-trans Y ε (f x) (gₙ (hₙ (f x))) (f (g (gₙ (hₙ (f x))))) (ηₙ (f x))
    (closeness-∞-implies-ϵ-close Y (gₙ (hₙ (f x))) (f (g (gₙ (hₙ (f x)))))
      (identical-implies-closeness-∞ Y _ _ (η (gₙ (hₙ (f x))) ⁻¹)) ε))
 , fₙ

≃-totally-bounded : {X : 𝓤 ̇}
                  → (Y : ClosenessSpace 𝓥)
                  → (e : X ≃ ⟨ Y ⟩)
                  → totally-bounded Y 𝓥'
                  → totally-bounded (≃-ClosenessSpace Y e) 𝓥'
≃-totally-bounded Y e t ε
 = pr₁ (t ε) , ≃-preserves-nets Y e ε (pr₁ (t ε)) (pr₂ (t ε))

-- Discrete sequence closeness spaces

discrete-decidable-seq
 : {X : ℕ → 𝓤 ̇ }
 → ((i : ℕ) → is-discrete (X i))
 → (α β : Π X) → (n : ℕ) → is-decidable ((α ≈ⁿ β) n)
discrete-decidable-seq d α β 0 = inl (λ _ ())
discrete-decidable-seq d α β (succ n)
 = Cases (discrete-decidable-seq d α β n) γ₁ (inr ∘ γ₂)
 where
   γ₁ : (α ≈ⁿ β) n → is-decidable ((α ≈ⁿ β) (succ n))
   γ₁ α∼ⁿβ = Cases (d n (α n) (β n)) (inl ∘ γ₁₁) (inr ∘ γ₁₂)
    where
      γ₁₁ :    α n ＝ β n →     (α ≈ⁿ β) (succ n)
      γ₁₁ e k k<sn = Cases (≤-split (succ k) n k<sn)
                       (λ k<n → α∼ⁿβ k k<n)
                       (λ sk=sn → transport (λ - → α - ＝ β -)
                         (succ-lc sk=sn ⁻¹) e)
      γ₁₂ : ¬ (α n ＝ β n) → ¬ ((α ≈ⁿ β) (succ n))
      γ₁₂ g α∼ˢⁿβ = g (α∼ˢⁿβ n (<-succ n))
   γ₂ : ¬ ((α ≈ⁿ β) n) → ¬ ((α ≈ⁿ β) (succ n))
   γ₂ f = f
        ∘ λ α∼ˢⁿβ k k<n → α∼ˢⁿβ k (<-trans k n (succ n) k<n (<-succ n))

decidable-𝟚 : {X : 𝓤 ̇ } → is-decidable X → 𝟚
decidable-𝟚 (inl _) = ₁
decidable-𝟚 (inr _) = ₀

decidable-𝟚₁ : {X : 𝓤 ̇ } → (d : is-decidable X)
             → X → decidable-𝟚 d ＝ ₁
decidable-𝟚₁ (inl  x) _ = refl
decidable-𝟚₁ (inr ¬x) x = 𝟘-elim (¬x x)

decidable-𝟚₀ : {X : 𝓤 ̇ } → (d : is-decidable X)
             → ¬ X → decidable-𝟚 d ＝ ₀
decidable-𝟚₀ (inl  x) ¬x = 𝟘-elim (¬x x)
decidable-𝟚₀ (inr ¬x)  _ = refl

𝟚-decidable₁ : {X : 𝓤 ̇ } → (d : is-decidable X)
             → decidable-𝟚 d ＝ ₁ → X
𝟚-decidable₁ d e with d
... | inl  x = x
... | inr ¬x = 𝟘-elim (zero-is-not-one e)

𝟚-decidable₀ : {X : 𝓤 ̇ } → (d : is-decidable X)
             → decidable-𝟚 d ＝ ₀ → ¬ X
𝟚-decidable₀ d e with d
... | inl  x = 𝟘-elim (zero-is-not-one (e ⁻¹))
... | inr ¬x = ¬x

decidable-seq-𝟚 : {X : ℕ → 𝓤 ̇ } → is-complemented X → (ℕ → 𝟚)
decidable-seq-𝟚 d n = decidable-𝟚 (d (succ n))

discrete-seq-clofun'
 : {X : ℕ → 𝓤 ̇ } → ((i : ℕ) → is-discrete (X i)) → Π X → Π X → (ℕ → 𝟚)
discrete-seq-clofun' d α β
 = decidable-seq-𝟚 (discrete-decidable-seq d α β)
 
discrete-seq-clofun'-e
 : {X : ℕ → 𝓤 ̇ }
 → (d : (i : ℕ) → is-discrete (X i))
 → (α β : Π X)
 → ((n : ℕ) → discrete-seq-clofun' d α β n ＝ ₁)
 → α ＝ β
discrete-seq-clofun'-e d α β f
 = dfunext (fe _ _)
     (λ n → 𝟚-decidable₁ (discrete-decidable-seq d α β (succ n))
              (f n) n (<-succ n))

discrete-seq-clofun'-i
 : {X : ℕ → 𝓤 ̇ } 
 → (d : (i : ℕ) → is-discrete (X i))
 → (α : Π X)
 → (n : ℕ) → discrete-seq-clofun' d α α n ＝ ₁
discrete-seq-clofun'-i d α n
 = decidable-𝟚₁ (discrete-decidable-seq d α α (succ n)) (λ _ _ → refl)

discrete-seq-clofun'-s
 : {X : ℕ → 𝓤 ̇ }
 → (d : (i : ℕ) → is-discrete (X i))
 → (α β : Π X)
 → (n : ℕ)
 → discrete-seq-clofun' d α β n ＝ discrete-seq-clofun' d β α n
discrete-seq-clofun'-s d α β n
 with discrete-decidable-seq d α β (succ n)
... | inl  α∼ⁿβ
 = decidable-𝟚₁ (discrete-decidable-seq d β α (succ n))
     (λ i i<n → α∼ⁿβ i i<n ⁻¹) ⁻¹
... | inr ¬α∼ⁿβ
 = decidable-𝟚₀ (discrete-decidable-seq d β α (succ n))
     (λ α∼ⁿβ → ¬α∼ⁿβ (λ i i<n → α∼ⁿβ i i<n ⁻¹)) ⁻¹

discrete-seq-clofun'-u
 : {X : ℕ → 𝓤 ̇ }
 → (d : (i : ℕ) → is-discrete (X i))
 → (α β ζ : Π X)
 → (n : ℕ)
 → min𝟚 (discrete-seq-clofun' d α β n)
        (discrete-seq-clofun' d β ζ n) ＝ ₁
 → discrete-seq-clofun' d α ζ n ＝ ₁
discrete-seq-clofun'-u d α β ζ n minₙ=1
 with discrete-decidable-seq d α β (succ n)
    | discrete-decidable-seq d β ζ (succ n)
    | discrete-decidable-seq d α ζ (succ n)
... |        _ |        _ | inl     _ = refl
... | inl α∼ⁿβ | inl β∼ⁿζ | inr ¬α∼ⁿζ
 = 𝟘-elim (¬α∼ⁿζ (λ i i<n → α∼ⁿβ i i<n ∙ β∼ⁿζ i i<n))

discrete-decidable-seq-𝟚-decreasing
 : {X : ℕ → 𝓤 ̇ }
 → (d : (i : ℕ) → is-discrete (X i))
 → (α β : Π X)
 → is-decreasing (discrete-seq-clofun' d α β)
discrete-decidable-seq-𝟚-decreasing d α β n
 with discrete-decidable-seq d α β (succ n)
    | discrete-decidable-seq d α β (succ (succ n))
... | inl     _ |          _ = ₁-top
... | inr ¬α∼ⁿβ | inl  α∼ˢⁿβ
 = ¬α∼ⁿβ (λ i i≤n → α∼ˢⁿβ i (≤-trans i n (succ n)
                      i≤n (≤-succ n)))
... | inr     _ | inr      _ = ⋆

discrete-seq-clofun
 : {X : ℕ → 𝓤 ̇ }
 → ((i : ℕ) → is-discrete (X i))
 → Π X → Π X → ℕ∞
discrete-seq-clofun d α β
 = discrete-seq-clofun' d α β
 , discrete-decidable-seq-𝟚-decreasing d α β

discrete-seq-clofun-e
 : {X : ℕ → 𝓤 ̇ }
 → (d : (i : ℕ) → is-discrete (X i))
 → indistinguishable-are-equal (discrete-seq-clofun d)
discrete-seq-clofun-e d α β cαβ=∞
 = discrete-seq-clofun'-e d α β (λ n → ap (λ - → pr₁ - n) cαβ=∞) 
     
discrete-seq-clofun-i : {X : ℕ → 𝓤 ̇ }
                      → (d : (i : ℕ) → is-discrete (X i))
                      → self-indistinguishable (discrete-seq-clofun d)
discrete-seq-clofun-i d α
 = to-subtype-＝ (being-decreasing-is-prop (fe _ _))
     (dfunext (fe _ _) (discrete-seq-clofun'-i d α))

discrete-seq-clofun-s : {X : ℕ → 𝓤 ̇ }
                      → (d : (i : ℕ) → is-discrete (X i))
                      → is-symmetric (discrete-seq-clofun d)
discrete-seq-clofun-s d α β
 = to-subtype-＝ (being-decreasing-is-prop (fe _ _))
     (dfunext (fe _ _) (discrete-seq-clofun'-s d α β))

discrete-seq-clofun-u : {X : ℕ → 𝓤 ̇ }
                      → (d : (i : ℕ) → is-discrete (X i))
                      → is-ultra (discrete-seq-clofun d)
discrete-seq-clofun-u = discrete-seq-clofun'-u

discrete-seq-clofun-c : {X : ℕ → 𝓤 ̇ }
                      → (d : (i : ℕ) → is-discrete (X i))
                      → is-closeness (discrete-seq-clofun d)
discrete-seq-clofun-c d = discrete-seq-clofun-e d
                        , discrete-seq-clofun-i d
                        , discrete-seq-clofun-s d
                        , discrete-seq-clofun-u d

discrete-seq-clospace : {X : ℕ → 𝓤 ̇ }
                      → ((i : ℕ) → is-discrete (X i))
                      → is-closeness-space (Π X)
discrete-seq-clospace d = discrete-seq-clofun d
                        , discrete-seq-clofun-c d

ΠD-ClosenessSpace : {X : ℕ → 𝓤 ̇ }
                  → (d : (i : ℕ) → is-discrete (X i))
                  → ClosenessSpace 𝓤
ΠD-ClosenessSpace {𝓤} {X} d = Π X , discrete-seq-clospace d

ℕ→D-ClosenessSpace : {X : 𝓤 ̇ }
                   → (d : is-discrete X)
                   → ClosenessSpace 𝓤
ℕ→D-ClosenessSpace {𝓤} {X} d = ΠD-ClosenessSpace (λ _ → d)

Vec-to-Seq : {X : 𝓤 ̇ } {n : ℕ} → X → Vec X n → (ℕ → X)
Vec-to-Seq x₀ [] n = x₀
Vec-to-Seq x₀ (x ∷ xs) 0 = x
Vec-to-Seq x₀ (x ∷ xs) (succ n) = Vec-to-Seq x₀ xs n

Seq-to-Vec : {X : 𝓤 ̇ } (n : ℕ) → (ℕ → X) → Vec X n
Seq-to-Vec 0 α = []
Seq-to-Vec (succ n) α = α 0 ∷ Seq-to-Vec n (α ∘ succ)

Seq-to-Vec-∼ : {X : 𝓤 ̇ }
             → (α : ℕ → X) (x₀ : X)
             → (ϵ : ℕ)
             → (α ∼ⁿ Vec-to-Seq x₀ (Seq-to-Vec ϵ α)) ϵ
Seq-to-Vec-∼ α x₀ (succ ϵ) 0 i<ϵ = refl
Seq-to-Vec-∼ α x₀ (succ ϵ) (succ i) i<ϵ
 = Seq-to-Vec-∼ (α ∘ succ) x₀ ϵ i i<ϵ

ℕ→F-is-totally-bounded : {F : 𝓤 ̇ } → (f : finite-discrete F) → F
                       → totally-bounded
                           (ℕ→D-ClosenessSpace
                             (finite-discrete-is-discrete f)) 𝓤
ℕ→F-is-totally-bounded {𝓤} {F} f x₀ ϵ
 = Vec F ϵ , (Vec-to-Seq x₀ , Seq-to-Vec ϵ , γ) , Vec-finite-discrete ϵ f
 where
  d : is-discrete F
  d = finite-discrete-is-discrete f
  γ : (α : ℕ → F)
    → C (ℕ→D-ClosenessSpace d) ϵ α (Vec-to-Seq x₀ (Seq-to-Vec ϵ α))
  γ α n n⊏ϵ = decidable-𝟚₁ (discrete-decidable-seq _ _ _ _)
                (λ i i<sn → Seq-to-Vec-∼ α x₀ ϵ i
                  (≤-<-trans i n ϵ i<sn (⊏-gives-< n ϵ n⊏ϵ)))
                  
-- Infinitary product of closeness spaces

Π-clofun' : (T : ℕ → ClosenessSpace 𝓤)
          → Π (⟨_⟩ ∘ T) → Π (⟨_⟩ ∘ T) → (ℕ → 𝟚)
Π-clofun' T x y zero = pr₁ (c⟨ T 0 ⟩ (x 0) (y 0)) 0
Π-clofun' T x y (succ n)
 = min𝟚 (pr₁ (c⟨ T 0 ⟩ (x 0) (y 0)) (succ n))
     (Π-clofun' (T ∘ succ) (x ∘ succ) (y ∘ succ) n)

Π-clofun'-d : (T : ℕ → ClosenessSpace 𝓤)
            → (x y : Π (⟨_⟩ ∘ T))
            → is-decreasing (Π-clofun' T x y)
Π-clofun'-d T x y zero
 = ≤₂-trans _ _ _ Lemma[minab≤₂a] (pr₂ (c⟨ T 0 ⟩ (x 0) (y 0)) 0)
Π-clofun'-d T x y (succ n)
 = min𝟚-preserves-≤ (pr₂ (c⟨ T 0 ⟩ (x 0) (y 0)) (succ n))
     (Π-clofun'-d (T ∘ succ) (x ∘ succ) (y ∘ succ) n)

Π-clofun'-all : (T : ℕ → ClosenessSpace 𝓤)
              → (x y : Π (⟨_⟩ ∘ T))
              → Π-clofun' T x y ∼ (λ i → ₁)
              → (n : ℕ) → (pr₁ (c⟨ T n ⟩ (x n) (y n))) ∼ (λ i → ₁)
Π-clofun'-all T x y cxy∼∞ 0 zero = cxy∼∞ 0
Π-clofun'-all T x y cxy∼∞ 0 (succ i)
 = Lemma[min𝟚ab＝₁→a＝₁] (cxy∼∞ (succ i))
Π-clofun'-all T x y cxy∼∞ (succ n)
 = Π-clofun'-all (T ∘ succ) (x ∘ succ) (y ∘ succ)
     (λ i → Lemma[min𝟚ab＝₁→b＝₁] (cxy∼∞ (succ i))) n

Π-clofun'-e : (T : ℕ → ClosenessSpace 𝓤)
            → (x y : Π (⟨_⟩ ∘ T))
            → Π-clofun' T x y ∼ (λ i → ₁) → x ＝ y
Π-clofun'-e T x y f
 = dfunext (fe _ _)
     (λ i → e i (x i) (y i)
       (to-subtype-＝ (being-decreasing-is-prop (fe _ _))
         (dfunext (fe _ _) (Π-clofun'-all T x y f i))))
 where
  e : (n : ℕ) → indistinguishable-are-equal c⟨ T n ⟩
  e n = pr₁ (pr₂ (pr₂ (T n)))

Π-clofun'-i : (T : ℕ → ClosenessSpace 𝓤)
            → (x : Π (⟨_⟩ ∘ T)) → Π-clofun' T x x ∼ (λ i → ₁)
Π-clofun'-i T x 0 = ap (λ - → pr₁ - 0) (i 0 (x 0))
 where
  i : (n : ℕ) → self-indistinguishable c⟨ T n ⟩
  i n = pr₁ (pr₂ (pr₂ (pr₂ (T n))))
Π-clofun'-i T x (succ n)
 = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
     (ap (λ - → pr₁ - (succ n)) (i 0 (x 0)))
     (Π-clofun'-i (T ∘ succ) (x ∘ succ) n)
 where
  i : (n : ℕ) → self-indistinguishable c⟨ T n ⟩
  i n = pr₁ (pr₂ (pr₂ (pr₂ (T n))))

Π-clofun'-s : (T : ℕ → ClosenessSpace 𝓤)
            → (x y : Π (⟨_⟩ ∘ T))
            → Π-clofun' T x y ∼ Π-clofun' T y x
Π-clofun'-s T x y zero
 = ap (λ - → pr₁ - 0) (s 0 (x 0) (y 0))
 where
  s : (n : ℕ) → is-symmetric c⟨ T n ⟩
  s n = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (T n))))) 
Π-clofun'-s T x y (succ n)
 = ap (λ - → min𝟚 - (Π-clofun' (T ∘ succ) (x ∘ succ) (y ∘ succ) n))
     (ap (λ - → pr₁ - (succ n)) (s 0 (x 0) (y 0)))
 ∙ ap (λ - → min𝟚 (pr₁ (c⟨ T 0 ⟩ (y 0) (x 0)) (succ n)) -)
     (Π-clofun'-s (T ∘ succ) (x ∘ succ) (y ∘ succ) n)
 where
  s : (n : ℕ) → is-symmetric c⟨ T n ⟩
  s n = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (T n)))))

Lemma[min𝟚abcd＝₁→min𝟚ac＝₁] : (a b c d : 𝟚)
                            → min𝟚 (min𝟚 a b) (min𝟚 c d) ＝ ₁
                            → min𝟚 a c ＝ ₁
Lemma[min𝟚abcd＝₁→min𝟚ac＝₁] ₁ ₁ ₁ ₁ e = refl
 
Lemma[min𝟚abcd＝₁→min𝟚bd＝₁] : (a b c d : 𝟚)
                            → min𝟚 (min𝟚 a b) (min𝟚 c d) ＝ ₁
                            → min𝟚 b d ＝ ₁
Lemma[min𝟚abcd＝₁→min𝟚bd＝₁] ₁ ₁ ₁ ₁ e = refl

Π-clofun'-u : (T : ℕ → ClosenessSpace 𝓤)
            → (x y z : Π (⟨_⟩ ∘ T))
            → (n : ℕ)
            → min𝟚 (Π-clofun' T x y n) (Π-clofun' T y z n) ＝ ₁
            → Π-clofun' T x z n ＝ ₁
Π-clofun'-u T x y z 0 η
 = u 0 (x 0) (y 0) (z 0) 0 η
 where
  u : (n : ℕ) → is-ultra c⟨ T n ⟩
  u n = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (T n)))))
Π-clofun'-u T x y z (succ n) η
 = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
     (u 0 (x 0) (y 0) (z 0) (succ n)
       (Lemma[min𝟚abcd＝₁→min𝟚ac＝₁]
         (pr₁ (c⟨ T 0 ⟩ (x 0) (y 0)) (succ n))
         (Π-clofun' (T ∘ succ) (x ∘ succ) (y ∘ succ) n)
         (pr₁ (c⟨ T 0 ⟩ (y 0) (z 0)) (succ n))
         (Π-clofun' (T ∘ succ) (y ∘ succ) (z ∘ succ) n)
         η))
     (Π-clofun'-u (T ∘ succ) (x ∘ succ) (y ∘ succ) (z ∘ succ) n
       (Lemma[min𝟚abcd＝₁→min𝟚bd＝₁]
         (pr₁ (c⟨ T 0 ⟩ (x 0) (y 0)) (succ n))
         (Π-clofun' (T ∘ succ) (x ∘ succ) (y ∘ succ) n)
         (pr₁ (c⟨ T 0 ⟩ (y 0) (z 0)) (succ n))
         (Π-clofun' (T ∘ succ) (y ∘ succ) (z ∘ succ) n)
         η))
 where
  u : (n : ℕ) → is-ultra c⟨ T n ⟩
  u n = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (T n)))))

Π-clofun : (T : ℕ → ClosenessSpace 𝓤)
         → Π (⟨_⟩ ∘ T) → Π (⟨_⟩ ∘ T) → ℕ∞
Π-clofun T x y = (Π-clofun' T x y) , (Π-clofun'-d T x y)

Π-clofun-e : (T : ℕ → ClosenessSpace 𝓤)
            → indistinguishable-are-equal (Π-clofun T)
Π-clofun-e T x y f
 = Π-clofun'-e T x y (λ i → ap (λ - → pr₁ - i) f)

Π-clofun-i : (T : ℕ → ClosenessSpace 𝓤)
           → self-indistinguishable (Π-clofun T)
Π-clofun-i T x
 = to-subtype-＝ (being-decreasing-is-prop (fe _ _))
     (dfunext (fe _ _) (Π-clofun'-i T x))

Π-clofun-s : (T : ℕ → ClosenessSpace 𝓤)
           → is-symmetric (Π-clofun T)
Π-clofun-s T x y
 = to-subtype-＝ (being-decreasing-is-prop (fe _ _))
     (dfunext (fe _ _) (Π-clofun'-s T x y))

Π-clofun-u : (T : ℕ → ClosenessSpace 𝓤)
           → is-ultra (Π-clofun T)
Π-clofun-u = Π-clofun'-u

Π-clofun-c : (T : ℕ → ClosenessSpace 𝓤)
           → is-closeness (Π-clofun T)
Π-clofun-c T = Π-clofun-e T , Π-clofun-i T
             , Π-clofun-s T , Π-clofun-u T

Π-clospace : (T : ℕ → ClosenessSpace 𝓤)
          → is-closeness-space (Π (⟨_⟩ ∘ T))
Π-clospace T = Π-clofun T , Π-clofun-c T

Π-ClosenessSpace : (T : ℕ → ClosenessSpace 𝓤)
                 → ClosenessSpace 𝓤
Π-ClosenessSpace T = Π (⟨_⟩ ∘ T) , Π-clospace T

Π-totally-bounded : (T : ℕ → ClosenessSpace 𝓤)
                  → ((n : ℕ) → ⟨ T n ⟩)
                  → ((n : ℕ) → totally-bounded (T n) 𝓦)
                  → totally-bounded (Π-ClosenessSpace T) 𝓦
Π-totally-bounded {𝓤} {𝓦} T p t 0
 = pointed-has-a-0-net (Π-ClosenessSpace T) p
Π-totally-bounded {𝓤} {𝓦} T p t (succ ϵ)
 = (t₀' × IH') , (g , h , η) , f
 where
  c₀ = pr₁ (pr₂ (T 0))
  t₀ = t 0 (succ ϵ)
  t₀' = pr₁ t₀
  t₀'-is-sϵ-net = pr₂ t₀
  g₀' = pr₁ (pr₁ t₀'-is-sϵ-net)
  h₀' = pr₁ (pr₂ (pr₁ t₀'-is-sϵ-net))
  η₀' = pr₂ (pr₂ (pr₁ t₀'-is-sϵ-net))
  IH = Π-totally-bounded (T ∘ succ) (p ∘ succ) (t ∘ succ) ϵ
  IH' = pr₁ IH
  IH'-is-ϵ-net = pr₂ IH
  gₛ' = pr₁ (pr₁ IH'-is-ϵ-net)
  hₛ' = pr₁ (pr₂ (pr₁ IH'-is-ϵ-net))
  ηₛ' = pr₂ (pr₂ (pr₁ IH'-is-ϵ-net))
  g : t₀' × IH' → Π (⟨_⟩ ∘ T)
  g (x' , αₛ') = g₀' x' :: gₛ' αₛ'
  h : Π (⟨_⟩ ∘ T) → t₀' × IH'
  h α = h₀' (α 0) , hₛ' (α ∘ succ)
  η : (x : Π (⟨_⟩ ∘ T)) → C (Π-ClosenessSpace T) (succ ϵ) x (g (h x))
  η α 0 = η₀' (α 0) 0
  η α (succ n) n⊏ϵ
   = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
       (η₀' (α 0) (succ n) n⊏ϵ)
       (ηₛ' (α ∘ succ) n n⊏ϵ)
  f : finite-discrete (t₀' × IH')
  f = ×-preserves-finite-discrete
        (pr₂ t₀'-is-sϵ-net) (pr₂ IH'-is-ϵ-net)

Π-clofuns-id' : {T : ℕ → 𝓤 ̇ }
              → (d : (i : ℕ) → is-discrete (T i))
              → (x y : Π T)
              → discrete-seq-clofun' d x y
              ∼ Π-clofun' (λ n → D-ClosenessSpace (d n)) x y
Π-clofuns-id' d x y 0 with d 0 (x 0) (y 0)
... | inl _ = refl
... | inr _ = refl
Π-clofuns-id' d x y (succ i)
 with discrete-decidable-seq d x y (succ (succ i))
... | inl z
   = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
       (closeness-∞-implies-ϵ-close (D-ClosenessSpace (d 0))
          (x 0) (y 0)
          (identical-implies-closeness-∞ (D-ClosenessSpace (d 0))
            (x 0) (y 0) (z 0 ⋆))
          (succ (succ i)) (succ i)
          (<-gives-⊏ (succ i) (succ (succ i)) (<-succ (succ i))))
       (Π-clofuns-id' (d ∘ succ) (x ∘ succ) (y ∘ succ) i ⁻¹
       ∙ decidable-𝟚₁ (discrete-decidable-seq _ _ _ _) (z ∘ succ))  ⁻¹
... | inr z
 = Cases (d 0 (x 0) (y 0))
     (λ e → Lemma[min𝟚ab＝₀] (inr
              (Π-clofuns-id' (d ∘ succ) (x ∘ succ) (y ∘ succ) i ⁻¹
                ∙ decidable-𝟚₀ (discrete-decidable-seq _ _ _ _)
                    (λ g → z (γ e g)))))
     (λ f → Lemma[min𝟚ab＝₀]
              (inl (ap (λ - → pr₁ - (succ i))
                (discrete-apart-implies-closeness-0
                  (d 0) (x 0) (y 0) f)))) ⁻¹
  where
   γ : x 0 ＝ y 0
     → ((x ∘ succ) ≈ⁿ (y ∘ succ)) (succ i)
     → (x ≈ⁿ y) (succ (succ i))
   γ e g 0 j<ssi = e
   γ e g (succ j) j<ssi = g j j<ssi

Π-clofuns-id
 : {T : ℕ → 𝓤 ̇ }
 → (d : (i : ℕ) → is-discrete (T i))
 → c⟨ ΠD-ClosenessSpace d ⟩
 ＝ c⟨ Π-ClosenessSpace (λ n → D-ClosenessSpace (d n)) ⟩
Π-clofuns-id d
 = dfunext (fe _ _) (λ x → dfunext (fe _ _) (λ y →
     to-subtype-＝ (being-decreasing-is-prop (fe _ _))
       (dfunext (fe _ _) (Π-clofuns-id' d x y))))

-- Some examples:

ℕ→𝟚-ClosenessSpace : ClosenessSpace 𝓤₀
ℕ→𝟚-ClosenessSpace = ℕ→D-ClosenessSpace 𝟚-is-discrete

open import TWA.Thesis.Chapter5.SignedDigit

𝟛ᴺ-ClosenessSpace : ClosenessSpace 𝓤₀
𝟛ᴺ-ClosenessSpace
 = ℕ→D-ClosenessSpace 𝟛-is-discrete

ℕ∞-ClosenessSpace : ClosenessSpace 𝓤₀
ℕ∞-ClosenessSpace
 = Σ-ClosenessSpace ℕ→𝟚-ClosenessSpace is-decreasing
     (being-decreasing-is-prop (fe _ _))
  

-- ℕ∞ is totally bounded. Should be in paper?
Vec-decreasing : {n : ℕ} → Vec 𝟚 n → 𝓤₀ ̇
Vec-decreasing {0} []    = 𝟙
Vec-decreasing {1} [ ₀ ] = 𝟙
Vec-decreasing {1} [ ₁ ] = 𝟙
Vec-decreasing {succ (succ n)} (₀ ∷ (₀ ∷ v))
 = Vec-decreasing (₀ ∷ v)
Vec-decreasing {succ (succ n)} (₀ ∷ (₁ ∷ v))
 = 𝟘
Vec-decreasing {succ (succ n)} (₁ ∷ v)
 = Vec-decreasing v

Vec-decreasing-is-prop : {n : ℕ} → (x : Vec 𝟚 n)
                       → is-prop (Vec-decreasing x)
Vec-decreasing-is-prop {0} []    = 𝟙-is-prop
Vec-decreasing-is-prop {1} [ ₀ ] = 𝟙-is-prop
Vec-decreasing-is-prop {1} [ ₁ ] = 𝟙-is-prop
Vec-decreasing-is-prop {succ (succ n)} (₀ ∷ (₀ ∷ v))
 = Vec-decreasing-is-prop (₀ ∷ v)
Vec-decreasing-is-prop {succ (succ n)} (₀ ∷ (₁ ∷ v))
 = 𝟘-is-prop
Vec-decreasing-is-prop {succ (succ n)} (₁ ∷ v)
 = Vec-decreasing-is-prop v

Vec-comp-decreasing : {n : ℕ} → ((v , _) : Σ (Vec-decreasing {n}))
                    → Vec-decreasing (₁ ∷ v)
Vec-comp-decreasing {zero} ([] , _) = ⋆
Vec-comp-decreasing {succ n} (_ , d) = d

repeat-vec : {X : 𝓤 ̇ } {n : ℕ} → X → Vec X n
repeat-vec {𝓤} {X} {zero} x₀ = []
repeat-vec {𝓤} {X} {succ n} x₀ = x₀ ∷ repeat-vec x₀

repeat-₀-decreasing : (n : ℕ) → Vec-decreasing {n} (repeat-vec ₀)
repeat-₀-decreasing zero = ⋆
repeat-₀-decreasing (succ zero) = ⋆
repeat-₀-decreasing (succ (succ n)) = repeat-₀-decreasing (succ n)

head-₀-only-repeat-₀-decreasing
 : (n : ℕ) → ((v , _) : Σ (Vec-decreasing {n}))
 → Vec-decreasing (₀ ∷ v)
 → repeat-vec ₀ ＝ v
head-₀-only-repeat-₀-decreasing zero ([] , _) _         = refl
head-₀-only-repeat-₀-decreasing (succ zero) ([ ₀ ] , _) _ = refl
head-₀-only-repeat-₀-decreasing (succ (succ n)) ((₀ ∷ (₀ ∷ v)) , d) d'
 = ap (₀ ∷_) (head-₀-only-repeat-₀-decreasing (succ n) (₀ ∷ v , d) d')

Vec-decreasing-finite : (n : ℕ) → finite-discrete (Σ (Vec-decreasing {n}))
Vec-decreasing-finite n = succ n , qinveq (g n) (h n , η n , μ n)
 where
  g : (n : ℕ) → 𝔽 (succ n) → Σ (Vec-decreasing {n})
  g 0     (inl _) = []    , ⋆
  g 1     (inl _) = [ ₀ ] , ⋆
  g 1     (inr _) = [ ₁ ] , ⋆
  g (succ (succ n)) (inl _) = repeat-vec ₀
                            , repeat-₀-decreasing (succ (succ n))
  g (succ (succ n)) (inr x) = (₁ ∷ pr₁ (g (succ n) x))
                            , pr₂ (g (succ n) x)
  h : (n : ℕ) → Σ (Vec-decreasing {n}) → 𝔽 (succ n)
  h 0     ([]    , ⋆) = inl ⋆
  h 1     ([ ₀ ] , ⋆) = inl ⋆
  h 1     ([ ₁ ] , ⋆) = inr (inl ⋆)
  h (succ (succ n)) ((₀ ∷ _) , _) = inl ⋆
  h (succ (succ n)) ((₁ ∷ v) , d) = inr (h (succ n) (v , d))
  η : (n : ℕ) → (x : 𝔽 (succ n)) → h n (g n x) ＝ x
  η 0     (inl ⋆) = refl
  η 1     (inl ⋆) = refl
  η 1     (inr (inl ⋆)) = refl
  η (succ (succ n)) (inl ⋆) = refl
  η (succ (succ n)) (inr x) = ap inr (η (succ n) x)
  μ : (n : ℕ) → (x : Σ (Vec-decreasing {n})) → g n (h n x) ＝ x
  μ 0     ([]    , ⋆) = refl
  μ 1     ([ ₀ ] , ⋆) = refl
  μ 1     ([ ₁ ] , ⋆) = refl
  μ (succ (succ n)) ((₀ ∷ v) , d)
   = to-subtype-＝ Vec-decreasing-is-prop
      (head-₀-only-repeat-₀-decreasing (succ (succ n)) ((₀ ∷ v) , d) d)
  μ (succ (succ n)) ((₁ ∷ v) , d)
   = to-subtype-＝ Vec-decreasing-is-prop
      (ap (₁ ∷_) (ap pr₁ (μ (succ n) (v , d))))

Seq-to-Vec-decreasing' : (n : ℕ) (v : Vec 𝟚 n)
                       → (a b : 𝟚) → ¬ ((a ＝ ₀) × (b ＝ ₁))
                       → Vec-decreasing (b ∷ v)
                       → Vec-decreasing (a ∷ (b ∷ v))
Seq-to-Vec-decreasing' n v ₀ ₀ f g = g
Seq-to-Vec-decreasing' n v ₁ ₀ f g = g
Seq-to-Vec-decreasing' n v ₁ ₁ f g = g
Seq-to-Vec-decreasing' n v ₀ ₁ f g = 𝟘-elim (f (refl , refl))

Seq-to-Vec-decreasing : (n : ℕ) (α : ℕ → 𝟚)
                      → is-decreasing α
                      → Vec-decreasing (Seq-to-Vec n α)
Seq-to-Vec-decreasing zero α d = ⋆
Seq-to-Vec-decreasing (succ zero) α d with α 0
... | ₀ = ⋆
... | ₁ = ⋆
Seq-to-Vec-decreasing (succ (succ n)) α d
 = Seq-to-Vec-decreasing' n (Seq-to-Vec n (α ∘ succ ∘ succ))
     (α 0) (α 1) γ
     (Seq-to-Vec-decreasing (succ n) (α ∘ succ) (d ∘ succ))
 where
  γ : ¬ ((α 0 ＝ ₀) × (α 1 ＝ ₁))
  γ (e₀ , e₁) = u (α 0) (α 1) e₀ e₁ (d 0)
   where
    u : (a b : 𝟚) → a ＝ ₀ → b ＝ ₁ → ¬ (a ≥ b)
    u a b refl refl = id

Vec-to-Seq-decreasing : (n : ℕ) (v : Vec 𝟚 n)
                      → Vec-decreasing v
                      → is-decreasing (Vec-to-Seq ₀ v)
Vec-to-Seq-decreasing 0 [] d _ = ⋆
Vec-to-Seq-decreasing 1 [ ₀ ] d _ = ⋆
Vec-to-Seq-decreasing 1 [ ₁ ] d _ = ⋆
Vec-to-Seq-decreasing (succ (succ n)) (₀ ∷ (₀ ∷ v)) d = γ
 where
  γ : is-decreasing (Vec-to-Seq ₀ (₀ ∷ (₀ ∷ v)))
  γ zero = ⋆
  γ (succ i) = Vec-to-Seq-decreasing (succ n) (₀ ∷ v) d i
Vec-to-Seq-decreasing (succ (succ n)) (₁ ∷ (₀ ∷ v)) d = γ
 where
  γ : is-decreasing (Vec-to-Seq ₀ (₁ ∷ (₀ ∷ v)))
  γ zero = ⋆
  γ (succ i) = Vec-to-Seq-decreasing (succ n) (₀ ∷ v) d i
Vec-to-Seq-decreasing (succ (succ n)) (₁ ∷ (₁ ∷ v)) d = γ
 where
  γ : is-decreasing (Vec-to-Seq ₀ (₁ ∷ (₁ ∷ v)))
  γ zero = ⋆
  γ (succ i) = Vec-to-Seq-decreasing (succ n) (₁ ∷ v) d i
{-
ℕ∞-is-totally-bounded : totally-bounded ℕ∞-ClosenessSpace 𝓤₀
ℕ∞-is-totally-bounded ϵ'
 = (Σ Vec-decreasing , (f ϵ' , γ ϵ')) , Vec-decreasing-finite ϵ'
 where
  f : (n : ℕ) → Σ (Vec-decreasing {n}) → ⟨ ℕ∞-ClosenessSpace ⟩
  f n (v , d) = (Vec-to-Seq ₀ v) , Vec-to-Seq-decreasing n v d

  γ : (ϵ : ℕ) → (α : ℕ∞) → Σ v ꞉ (Σ Vec-decreasing)
    , (C ℕ∞-ClosenessSpace ϵ α (f ϵ v))
  ζ : (α : ℕ∞) (ϵ n : ℕ) → n < ϵ
    → ((λ z → pr₁ α z) ∼ⁿ
       (λ z →
          pr₁
          (f ϵ
           (Seq-to-Vec (pr₁ α) ϵ , Seq-to-Vec-decreasing ϵ (pr₁ α) (pr₂ α)))
          z))
      (succ n)

  γ ϵ α = (Seq-to-Vec (pr₁ α) ϵ
               , Seq-to-Vec-decreasing ϵ (pr₁ α) (pr₂ α))
               , λ n n⊏ϵ → decidable-𝟚₁
                   (discrete-decidable-seq _ _ _ (succ n))
                   (ζ α ϵ n (⊏-gives-< n ϵ n⊏ϵ))
   where
    IH = γ ϵ ((pr₁ α ∘ succ) , (pr₂ α ∘ succ))
  ζ α (succ ϵ) n n<ϵ zero i<n = refl
  ζ α (succ ϵ) (succ n) n<ϵ (succ i) i<n
   = ζ ((pr₁ α ∘ succ) , (pr₂ α ∘ succ)) ϵ n n<ϵ i i<n
-}

-- Finite vectors TODO later - needed for TBR
{-
<-pred : {n : ℕ} (d : ℕ) → succ n < succ d → n < succ d
<-pred {n} d = <-trans n (succ n) (succ d) (<-succ n)

discrete-decidable-vec
 : {m : ℕ} {Y : Fin' (succ m) → 𝓤 ̇ }
 → ({i : Fin' (succ m)} → is-discrete (Y i))
 → (α β : Π Y) → (n : ℕ) → (sn<m : n < succ m)
 → is-decidable ((α ≈ⁿ β) (n , sn<m))
discrete-decidable-vec d α β 0 _ = inl (λ _ ())
discrete-decidable-vec {𝓤} {m} d α β (succ n) sn<m
 = Cases (discrete-decidable-vec d α β n n<m) γ₁ (inr ∘ γ₂)
 where
   n<m = <-pred m sn<m
   n*  = n , n<m
   sn* = succ n , sn<m
   γ₁ : (α ≈ⁿ β) n* → is-decidable ((α ≈ⁿ β) sn*)
   γ₁ α≈ⁿβ = Cases (d (α n*) (β n*)) (inl ∘ γ₁₁) (inr ∘ γ₁₂)
    where
      γ₁₁ : α n* ＝ β n* → (α ≈ⁿ β) sn*
      γ₁₁ e (k , k<sm) k<sn
       = Cases (≤-split (succ k) n k<sn)
           (λ k<n → α≈ⁿβ (k , k<sm) k<n)
           (λ sk＝sn → transport (λ - → α - ＝ β -)
             (to-subtype-＝ (λ i → <-is-prop-valued i (succ m))
               (succ-lc sk＝sn ⁻¹)) e)
      γ₁₂ : ¬ (α n* ＝ β n*) → ¬ ((α ≈ⁿ β) sn*)
      γ₁₂ g α∼ˢⁿβ = g (α∼ˢⁿβ (n , n<m) (<-succ n))
   γ₂ : ¬ ((α ≈ⁿ β) n*) → ¬ ((α ≈ⁿ β) sn*)
   γ₂ f = f
        ∘ λ α≈ˢⁿβ (k , k<sm) k<n
        → α≈ˢⁿβ (k , k<sm) (<-trans k n (succ n) k<n (<-succ n))
-}
\end{code}
