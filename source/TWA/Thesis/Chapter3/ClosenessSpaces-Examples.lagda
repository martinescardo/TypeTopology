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
open import Quotient.Type
open import UF.Miscelanea
open import UF.Embeddings
open import MLTT.Two-Properties

module TWA.Thesis.Chapter3.ClosenessSpaces-Examples (fe : FunExt) where

open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter2.FiniteDiscrete
open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Closeness fe hiding (is-ultra; is-closeness)

c⟨_⟩ : (X : ClosenessSpace 𝓤) → ⟨ X ⟩ → ⟨ X ⟩ → ℕ∞
c⟨ (X , c , _) ⟩ = c

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
 = ap (_, y₁) (ex x₁ x₂ cx＝∞) ∙ ap (x₂ ,_) (ey y₁ y₂ cy＝∞)
 where
  cx＝∞ : c⟨ X ⟩ x₁ x₂ ＝ ∞
  cx＝∞ = min-∞-l (c⟨ X ⟩ x₁ x₂) (c⟨ Y ⟩ y₁ y₂) cxy＝∞
  cy＝∞ : c⟨ Y ⟩ y₁ y₂ ＝ ∞
  cy＝∞ = min-∞-r (c⟨ X ⟩ x₁ x₂) (c⟨ Y ⟩ y₁ y₂) cxy＝∞
  ex : indistinguishable-are-equal c⟨ X ⟩
  ex = pr₁ (pr₂ (pr₂ X))
  ey : indistinguishable-are-equal c⟨ Y ⟩
  ey = pr₁ (pr₂ (pr₂ Y))

×-clofun'-i : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → self-indistinguishable (×-clofun' X Y)
×-clofun'-i X Y (x , y)
 = ap (λ - → min - (c⟨ Y ⟩ y y)) (ex x)
 ∙ ap (      min ∞             ) (ey y)
 where
  ex : self-indistinguishable c⟨ X ⟩
  ex = pr₁ (pr₂ (pr₂ (pr₂ X)))
  ey : self-indistinguishable c⟨ Y ⟩
  ey = pr₁ (pr₂ (pr₂ (pr₂ Y)))



×-clofun'-s : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → is-symmetric (×-clofun' X Y)
×-clofun'-s X Y (x₁ , y₁) (x₂ , y₂)
 = ap (λ - → min - (c⟨ Y ⟩ y₁ y₂)) (sx x₁ x₂)
 ∙ ap (      min (c⟨ X ⟩ x₂ x₁)  ) (sy y₁ y₂)
 where
  sx : is-symmetric c⟨ X ⟩
  sx = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ X))))
  sy : is-symmetric c⟨ Y ⟩
  sy = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ Y))))

min𝟚-abcd : {a b c d : 𝟚} → a ＝ c → b ＝ d → min𝟚 a b ＝ min𝟚 c d
min𝟚-abcd {a} {b} {.a} {.b} refl refl = refl

min𝟚-abcd-ac : (a b c d : 𝟚) → min𝟚 (min𝟚 a b) (min𝟚 c d) ＝ ₁ → min𝟚 a c ＝ ₁
min𝟚-abcd-ac ₁ ₁ ₁ ₁ e = refl

min𝟚-abcd-bd : (a b c d : 𝟚) → min𝟚 (min𝟚 a b) (min𝟚 c d) ＝ ₁ → min𝟚 b d ＝ ₁
min𝟚-abcd-bd ₁ ₁ ₁ ₁ e = refl

minℕ∞-abcdef : (a b c d e f : ℕ∞)
             → min a b ≼ e → min c d ≼ f
             → min (min a c) (min b d) ≼ min e f
minℕ∞-abcdef a b c d e f mab≼e mcd≼f n minabcd＝₁
 = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
     (mab≼e n (min𝟚-abcd-ac (pr₁ a n) (pr₁ c n) (pr₁ b n) (pr₁ d n) minabcd＝₁))
     (mcd≼f n (min𝟚-abcd-bd (pr₁ a n) (pr₁ c n) (pr₁ b n) (pr₁ d n) minabcd＝₁))

×-clofun'-u : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → is-ultra (×-clofun' X Y)
×-clofun'-u X Y (x₁ , y₁) (x₂ , y₂) (x₃ , y₃)
 = minℕ∞-abcdef
     (c⟨ X ⟩ x₁ x₂) (c⟨ X ⟩ x₂ x₃)
     (c⟨ Y ⟩ y₁ y₂) (c⟨ Y ⟩ y₂ y₃)
     (c⟨ X ⟩ x₁ x₃) (c⟨ Y ⟩ y₁ y₃)
     (ux x₁ x₂ x₃) (uy y₁ y₂ y₃)
 where
  ux : is-ultra c⟨ X ⟩
  ux = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ X))))
  uy : is-ultra c⟨ Y ⟩
  uy = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ Y))))

×-clofun : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
         → is-closeness-space (⟨ X ⟩ × ⟨ Y ⟩)
×-clofun X Y
 = ×-clofun' X Y
 , ×-clofun'-e X Y
 , ×-clofun'-i X Y
 , ×-clofun'-s X Y
 , ×-clofun'-u X Y

×-ClosenessSpace : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
                 → ClosenessSpace (𝓤 ⊔ 𝓥)
×-ClosenessSpace X Y = (⟨ X ⟩ × ⟨ Y ⟩) , (×-clofun X Y)

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

discrete-decidable-seq
 : {X : 𝓤 ̇ } → is-discrete X
 → (α β : ℕ → X) → (n : ℕ) → is-decidable ((α ∼ⁿ β) n)
discrete-decidable-seq d α β 0 = inl (λ _ ())
discrete-decidable-seq d α β (succ n)
 = Cases (discrete-decidable-seq d α β n) γ₁ (inr ∘ γ₂)
 where
   γ₁ : (α ∼ⁿ β) n → is-decidable ((α ∼ⁿ β) (succ n))
   γ₁ α∼ⁿβ = Cases (d (α n) (β n)) (inl ∘ γ₁₁) (inr ∘ γ₁₂)
    where
      γ₁₁ :    α n ＝ β n →     (α ∼ⁿ β) (succ n)
      γ₁₁ e k k<sn = Cases (≤-split (succ k) n k<sn)
                       (λ k<n → α∼ⁿβ k k<n)
                       (λ sk=sn → transport (λ - → α - ＝ β -)
                         (succ-lc sk=sn ⁻¹) e)
      γ₁₂ : ¬ (α n ＝ β n) → ¬ ((α ∼ⁿ β) (succ n))
      γ₁₂ g α∼ˢⁿβ = g (α∼ˢⁿβ n (<-succ n))
   γ₂ : ¬ ((α ∼ⁿ β) n) → ¬ ((α ∼ⁿ β) (succ n))
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
 : {X : 𝓤 ̇ } → is-discrete X → (ℕ → X) → (ℕ → X) → (ℕ → 𝟚)
discrete-seq-clofun' d α β
 = decidable-seq-𝟚 (discrete-decidable-seq d α β)

discrete-seq-clofun'-e
 : {X : 𝓤 ̇ } → (d : is-discrete X) → (α β : ℕ → X)
 → ((n : ℕ) → discrete-seq-clofun' d α β n ＝ ₁)
 → α ＝ β
discrete-seq-clofun'-e d α β f
 = dfunext (fe _ _)
     (λ n → 𝟚-decidable₁ (discrete-decidable-seq d α β (succ n))
              (f n) n (<-succ n))

discrete-seq-clofun'-i
 : {X : 𝓤 ̇ } → (d : is-discrete X) → (α : ℕ → X)
 → (n : ℕ) → discrete-seq-clofun' d α α n ＝ ₁
discrete-seq-clofun'-i d α n
 = decidable-𝟚₁ (discrete-decidable-seq d α α (succ n)) (λ _ _ → refl)

discrete-seq-clofun'-s
 : {X : 𝓤 ̇ } → (d : is-discrete X) → (α β : ℕ → X)
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
 : {X : 𝓤 ̇ } → (d : is-discrete X) → (α β ζ : ℕ → X)
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
 : {X : 𝓤 ̇ } → (d : is-discrete X) → (α β : ℕ → X)
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
 : {X : 𝓤 ̇ } → is-discrete X → (ℕ → X) → (ℕ → X) → ℕ∞
discrete-seq-clofun d α β
 = discrete-seq-clofun' d α β
 , discrete-decidable-seq-𝟚-decreasing d α β

discrete-seq-clofun-e
 : {X : 𝓤 ̇ } → (d : is-discrete X)
 → indistinguishable-are-equal (discrete-seq-clofun d)
discrete-seq-clofun-e d α β cαβ=∞
 = discrete-seq-clofun'-e d α β (λ n → ap (λ - → pr₁ - n) cαβ=∞)

discrete-seq-clofun-i : {X : 𝓤 ̇ } → (d : is-discrete X)
                      → self-indistinguishable (discrete-seq-clofun d)
discrete-seq-clofun-i d α
 = to-subtype-＝ (being-decreasing-is-prop (fe _ _))
     (dfunext (fe _ _) (discrete-seq-clofun'-i d α))

discrete-seq-clofun-s : {X : 𝓤 ̇ } → (d : is-discrete X)
                      → is-symmetric (discrete-seq-clofun d)
discrete-seq-clofun-s d α β
 = to-subtype-＝ (being-decreasing-is-prop (fe _ _))
     (dfunext (fe _ _) (discrete-seq-clofun'-s d α β))

discrete-seq-clofun-u : {X : 𝓤 ̇ } → (d : is-discrete X)
                      → is-ultra (discrete-seq-clofun d)
discrete-seq-clofun-u = discrete-seq-clofun'-u

discrete-seq-clofun-c : {X : 𝓤 ̇ } → (d : is-discrete X)
                      → is-closeness (discrete-seq-clofun d)
discrete-seq-clofun-c d = discrete-seq-clofun-e d
                        , discrete-seq-clofun-i d
                        , discrete-seq-clofun-s d
                        , discrete-seq-clofun-u d

ℕ→D-clofun : {X : 𝓤 ̇ } → (d : is-discrete X)
           → is-closeness-space (ℕ → X)
ℕ→D-clofun d = discrete-seq-clofun d
             , discrete-seq-clofun-c d

ℕ→D-ClosenessSpace : {X : 𝓤 ̇ } → (d : is-discrete X)
                   → ClosenessSpace 𝓤
ℕ→D-ClosenessSpace {𝓤} {X} d = (ℕ → X) , ℕ→D-clofun d

Σ-clofun : {X : 𝓤 ̇ } (P : X → 𝓥 ̇ )
         → ((x : X) → is-prop (P x))
         → Σ cx ꞉ (X → X → ℕ∞) , is-closeness cx
         → Σ c ꞉ (Σ P → Σ P → ℕ∞) , is-closeness c
Σ-clofun {𝓤} {𝓥} {X} P p (cx , ex , ix , sx , ux) = c , e , i , s , u
 where
  c : Σ P → Σ P → ℕ∞
  c (x , _) (y , _) = cx x y
  e : indistinguishable-are-equal c
  e (x , _) (y , _) cxy=∞ = to-subtype-＝ p (ex x y cxy=∞)
  i : self-indistinguishable c
  i (x , _) = ix x
  s : is-symmetric c
  s (x , _) (y , _) = sx x y
  u : is-ultra c
  u (x , _) (y , _) (z , _) = ux x y z

Σ-ClosenessSpace : (X : ClosenessSpace 𝓤)
                 → (P : ⟨ X ⟩ → 𝓥 ̇ ) → ((x : ⟨ X ⟩) → is-prop (P x))
                 → ClosenessSpace (𝓤 ⊔ 𝓥)
Σ-ClosenessSpace {𝓤} {𝓥} (X , cx) P p = Σ P  , Σ-clofun P p cx

↪-clofun : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X ↪ Y)
         → Σ cy ꞉ (Y → Y → ℕ∞) , is-closeness cy
         → Σ c  ꞉ (X → X → ℕ∞) , is-closeness c
↪-clofun {𝓤} {𝓥} {X} {Y} (f , η) (cy , ey , iy , sy , uy)
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

ℕ→𝟚-ClosenessSpace : ClosenessSpace 𝓤₀
ℕ→𝟚-ClosenessSpace = ℕ→D-ClosenessSpace 𝟚-is-discrete

open import TWA.Thesis.Chapter5.SignedDigit

𝟛ᴺ-ClosenessSpace : ClosenessSpace 𝓤₀
𝟛ᴺ-ClosenessSpace = ℕ→D-ClosenessSpace 𝟛-is-discrete

ℕ∞-ClosenessSpace : ClosenessSpace 𝓤₀
ℕ∞-ClosenessSpace
 = Σ-ClosenessSpace ℕ→𝟚-ClosenessSpace is-decreasing
     (being-decreasing-is-prop (fe _ _))

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

ΠT-clofun : (T : ℕ → ClosenessSpace 𝓤)
          → is-closeness-space (Π (⟨_⟩ ∘ T))
ΠT-clofun T = Π-clofun T , Π-clofun-c T

Π-ClosenessSpace : (T : ℕ → ClosenessSpace 𝓤)
                 → ClosenessSpace 𝓤
Π-ClosenessSpace T = Π (⟨_⟩ ∘ T) , ΠT-clofun T

open import TWA.Thesis.Chapter2.Vectors

Vec-to-Seq : {X : 𝓤 ̇ } {n : ℕ} → X → Vec X n → (ℕ → X)
Vec-to-Seq x₀ [] n = x₀
Vec-to-Seq x₀ (x ∷ xs) 0 = x
Vec-to-Seq x₀ (x ∷ xs) (succ n) = Vec-to-Seq x₀ xs n

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

-- Should be in paper
ℕ→F-is-totally-bounded : {F : 𝓤 ̇ } → (f : finite-discrete F) → F
                       → totally-bounded
                           (ℕ→D-ClosenessSpace
                             (finite-discrete-is-discrete f)) 𝓤
ℕ→F-is-totally-bounded {𝓤} {F} f x₀ ϵ
 = (Vec F ϵ , Vec-to-Seq x₀ , γ ϵ) , Vec-finite-discrete ϵ f
 where
  d : is-discrete F
  d = finite-discrete-is-discrete f
  γ : (ϵ : ℕ) → (α : ℕ → F) → Σ v ꞉ (Vec F ϵ)
    , (C (ℕ→D-ClosenessSpace d) ϵ α (Vec-to-Seq x₀ v))
  ζ : (α : ℕ → F) (ϵ n : ℕ) → n < succ ϵ
    → (α ∼ⁿ (Vec-to-Seq x₀ (α 0 ∷ pr₁ (γ ϵ (α ∘ succ))))) (succ n)

  γ 0 α = [] , (λ _ ())
  γ (succ ϵ) α
   = (α 0 ∷ pr₁ (γ ϵ (α ∘ succ)))
   , λ n n⊏ϵ → decidable-𝟚₁ (discrete-decidable-seq _ _ _ (succ n))
                 (ζ (λ z → α z) ϵ n (⊏-gives-< n (succ ϵ) n⊏ϵ))

  ζ α ϵ n n<ϵ zero i<n = refl
  ζ α (succ ϵ) (succ n) n<ϵ (succ i) i<n = ζ (α ∘ succ) ϵ n n<ϵ i i<n

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

Seq-to-Vec : {X : 𝓤 ̇ } → (ℕ → X) → (n : ℕ) → Vec X n
Seq-to-Vec α zero = []
Seq-to-Vec α (succ n) = (α 0) ∷ (Seq-to-Vec (α ∘ succ) n)

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
                      → Vec-decreasing (Seq-to-Vec α n)
Seq-to-Vec-decreasing zero α d = ⋆
Seq-to-Vec-decreasing (succ zero) α d with α 0
... | ₀ = ⋆
... | ₁ = ⋆
Seq-to-Vec-decreasing (succ (succ n)) α d
 = Seq-to-Vec-decreasing' n (Seq-to-Vec (α ∘ succ ∘ succ) n)
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

\end{code}
