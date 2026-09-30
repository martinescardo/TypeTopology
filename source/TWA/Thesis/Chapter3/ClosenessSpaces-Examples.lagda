Todd Waugh Ambridge, January 2024

# Examples of closeness spaces

\begin{code}
{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan
open import CoNaturals.Type
 renaming (ℕ-to-ℕ∞ to _↑)
 hiding (max)
open import Notation.Order
open import Naturals.Order
open import NotionsOfDecidability.Complemented
open import UF.DiscreteAndSeparated
open import UF.FunExt
open import UF.Subsingletons
open import UF.Embeddings
open import MLTT.Two-Properties
open import Fin.Type
open import Fin.Bishop
open import Fin.Embeddings
open import UF.Equiv
open import MLTT.SpartanList hiding (⟨_⟩; _∷_)

module TWA.Thesis.Chapter3.ClosenessSpaces-Examples (fe : FunExt) where

open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter2.Vectors
open import TWA.Thesis.Chapter2.Finite
open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Closeness fe hiding (is-ultra; is-closeness)
\end{code}

## Trivial closeness spaces

\begin{code}
𝟘-clospace : is-closeness-space (𝟘 {𝓤})
𝟘-clospace = (λ ()) , ((λ ()) , (λ ()) , ((λ ()) , (λ ())))

𝟙-clospace : is-closeness-space (𝟙 {𝓤})
𝟙-clospace
 = (λ _ _ → ∞)
 , (λ _ _ _     → refl)
 , (λ _         → refl)
 , (λ _ _       → refl)
 , (λ _ _ _ _ _ → refl)
\end{code}

## Discrete closeness spaces

\begin{code}
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
 = 𝟘-elim (zero-is-not-one (ap (λ - → ℕ∞-to-ℕ→𝟚 - 0) cxy＝∞))

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

finite-totally-bounded
 : {X : 𝓤 ̇ } (f : finite-linear-order X) (d : is-discrete X)
 → pointed X
 → totally-bounded (D-ClosenessSpace d) 𝓤
finite-totally-bounded f d x 0
 = pointed-has-a-0-net (D-ClosenessSpace d) x
finite-totally-bounded {𝓤} {X} f d x (succ ε)
 = X , (id , id , η) , f
 where
  η : (x : X) → C (D-ClosenessSpace d) (succ ε) x x
  η x n _ = ap (λ - → ℕ∞-to-ℕ→𝟚 - n) (i⟨ D-ClosenessSpace d ⟩ x)

discrete-apart-implies-closeness-0
 : {X : 𝓤 ̇ }
 → (d : is-discrete X)
 → (x y : X)
 → x ≠ y
 → c⟨ D-ClosenessSpace d ⟩ x y ＝ 0 ↑
discrete-apart-implies-closeness-0 d x y f = γ (d x y)
 where
  γ : (dxy : is-decidable (x ＝ y)) → discrete-clofun'' x y dxy ＝ Zero
  γ (inl e) = 𝟘-elim (f e)
  γ (inr _) = refl

discrete-closeness-succ-implies-equal
 : {X : 𝓤 ̇ }
 → (d : is-discrete X)
 → (x y : X)
 → (n : ℕ)
 → C (D-ClosenessSpace d) (succ n) x y
 → x ＝ y
discrete-closeness-succ-implies-equal d x y n Csnxy
 = γ (d x y) (Csnxy n (<-gives-⊏ n (succ n) (<-succ n)))
 where
  γ : (dxy : is-decidable (x ＝ y))
    → ℕ∞-to-ℕ→𝟚 (discrete-clofun'' x y dxy) n ＝ ₁
    → x ＝ y
  γ (inl e) _ = e
  γ (inr f) cxyₙ=₁ = 𝟘-elim (zero-is-not-one cxyₙ=₁)
\end{code}

## Disjoint union of closeness spaces

\begin{code}
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
 = 𝟘-elim (zero-is-not-one (ap (λ - → ℕ∞-to-ℕ→𝟚 - 0) f))
+-clofun'-e X Y (inr y₁) (inl x₂) f
 = 𝟘-elim (zero-is-not-one (ap (λ - → ℕ∞-to-ℕ→𝟚 - 0) f))

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
  f : finite-linear-order (X' + Y')
  f = +-is-finite fx fy

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

+-C-left  : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
          → (x₁ x₂ : ⟨ X ⟩)
          → (ε : ℕ) → C (+-ClosenessSpace X Y) ε (inl x₁) (inl x₂)
          → C X ε x₁ x₂
+-C-left  X Y x₁ x₂ ε Cxy n = Cxy n
\end{code}

## Binary product of closeness spaces

\begin{code}
×-clofun' : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
          → (⟨ X ⟩ × ⟨ Y ⟩ → ⟨ X ⟩ × ⟨ Y ⟩ → ℕ∞)
×-clofun' X Y (x₁ , y₁) (x₂ , y₂)
 = min (c⟨ X ⟩ x₁ x₂) (c⟨ Y ⟩ y₁ y₂)

min-∞-l : (u v : ℕ∞) → min u v ＝ ∞ → u ＝ ∞
min-∞-l u v min＝∞
 = to-subtype-＝ (being-decreasing-is-prop (fe _ _))
     (dfunext (fe _ _)
       (λ i → Lemma[min𝟚ab＝₁→a＝₁] (ap (λ - → ℕ∞-to-ℕ→𝟚 - i) min＝∞)))

min-∞-r : (u v : ℕ∞) → min u v ＝ ∞ → v ＝ ∞
min-∞-r u v min＝∞
 = to-subtype-＝ (being-decreasing-is-prop (fe _ _))
     (dfunext (fe _ _)
       (λ i → Lemma[min𝟚ab＝₁→b＝₁] (ap (λ - → ℕ∞-to-ℕ→𝟚 - i) min＝∞)))

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
min𝟚-abcd-ac ₀ b c d e = 𝟘-elim (zero-is-not-one e)
min𝟚-abcd-ac ₁ ₀ c d e = 𝟘-elim (zero-is-not-one e)
min𝟚-abcd-ac ₁ ₁ ₀ d e = 𝟘-elim (zero-is-not-one e)
min𝟚-abcd-ac ₁ ₁ ₁ ₀ e = 𝟘-elim (zero-is-not-one e)
min𝟚-abcd-ac ₁ ₁ ₁ ₁ e = refl

min𝟚-abcd-bd : (a b c d : 𝟚)
             → min𝟚 (min𝟚 a b) (min𝟚 c d) ＝ ₁
             → min𝟚 b d ＝ ₁
min𝟚-abcd-bd ₀ b c d e = 𝟘-elim (zero-is-not-one e)
min𝟚-abcd-bd ₁ ₀ c d e = 𝟘-elim (zero-is-not-one e)
min𝟚-abcd-bd ₁ ₁ ₀ d e = 𝟘-elim (zero-is-not-one e)
min𝟚-abcd-bd ₁ ₁ ₁ ₀ e = 𝟘-elim (zero-is-not-one e)
min𝟚-abcd-bd ₁ ₁ ₁ ₁ e = refl

minℕ∞-abcdef : (a b c d e f : ℕ∞)
             → min a b ≼ e → min c d ≼ f
             → min (min a c) (min b d) ≼ min e f
minℕ∞-abcdef a b c d e f mab≼e mcd≼f n minabcd＝₁
 = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
     (mab≼e n (min𝟚-abcd-ac
       (ℕ∞-to-ℕ→𝟚 a n) (ℕ∞-to-ℕ→𝟚 c n) (ℕ∞-to-ℕ→𝟚 b n) (ℕ∞-to-ℕ→𝟚 d n)
       minabcd＝₁))
     (mcd≼f n (min𝟚-abcd-bd
       (ℕ∞-to-ℕ→𝟚 a n) (ℕ∞-to-ℕ→𝟚 c n) (ℕ∞-to-ℕ→𝟚 b n) (ℕ∞-to-ℕ→𝟚 d n)
       minabcd＝₁))

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
  f : finite-linear-order (X' × Y')
  f = ×-is-finite fx fy

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
\end{code}

## Vector closeness spaces

\begin{code}
vec-ClosenessSpace : (n : ℕ) (X : Fin n → ClosenessSpace 𝓤)
                   → ClosenessSpace 𝓤

vec-clospace : (n : ℕ) (X : Fin n → ClosenessSpace 𝓤)
             → is-closeness-space (vec n (⟨_⟩ ∘ X))

vec-ClosenessSpace n X = (vec n (⟨_⟩ ∘ X)) , vec-clospace n X

vec-clospace 0 X = (λ _ _ → ∞) , e , i , s , u
 where
  e : indistinguishable-are-equal (λ _ _ → ∞)
  e ⟨⟩ ⟨⟩ _ = refl
  i : self-indistinguishable (λ _ _ → ∞)
  i ⟨⟩ = refl
  s : is-symmetric (λ _ _ → ∞)
  s ⟨⟩ ⟨⟩ = refl
  u : is-ultra (λ _ _ → ∞)
  u ⟨⟩ ⟨⟩ ⟨⟩ _ _ = refl
vec-clospace (succ n) X
 = ×-clospace (X 𝟎) (vec-ClosenessSpace n (X ∘ suc))

vec-totally-bounded : (n : ℕ) (X : Fin n → ClosenessSpace 𝓤)
                    → ((i : Fin n) → totally-bounded (X i) 𝓥)
                    → totally-bounded (vec-ClosenessSpace n X) 𝓥
vec-totally-bounded 0 X t ϵ = 𝟙 , ((g , h , η) , 𝟙-is-finite)
 where
  g : 𝟙 → vec 0 (⟨_⟩ ∘ X)
  g _ = ⟨⟩
  h : vec 0 (⟨_⟩ ∘ X) → 𝟙
  h _ = ⋆
  η : (x : vec 0 (⟨_⟩ ∘ X)) → C (vec-ClosenessSpace 0 X) ϵ x ⟨⟩
  η ⟨⟩ = C-refl (vec-ClosenessSpace 0 X) ϵ ⟨⟩
vec-totally-bounded (succ n) X t
 = ×-totally-bounded
     (X 𝟎) (vec-ClosenessSpace n (X ∘ suc))
     (t 𝟎) (vec-totally-bounded n (X ∘ suc) (t ∘ suc))

Vec-clospace : (X : ClosenessSpace 𝓤) (n : ℕ)
             → is-closeness-space (Vec ⟨ X ⟩ n)
Vec-clospace X n = vec-clospace n (λ _ → X)

Vec-ClosenessSpace : (X : ClosenessSpace 𝓤) (n : ℕ)
                   → ClosenessSpace 𝓤
Vec-ClosenessSpace X n = Vec ⟨ X ⟩ n , Vec-clospace X n

Vec-totally-bounded : (X : ClosenessSpace 𝓤) (n : ℕ)
                    → totally-bounded X 𝓥
                    → totally-bounded (Vec-ClosenessSpace X n) 𝓥
Vec-totally-bounded X n t = vec-totally-bounded n (λ _ → X) (λ _ → t)
\end{code}

## Least closeness pseudocloseness space

\begin{code}
Least-clofun : (X : 𝓤 ̇ ) (Y : ClosenessSpace 𝓥)
                 → {n : ℕ}
                 → Vec X n
                 → ((X → ⟨ Y ⟩) → (X → ⟨ Y ⟩) → ℕ∞)
Least-clofun X Y {n} v f g
 = pr₁ (Vec-clospace Y n) (vec-map f v) (vec-map g v)

Least-clofun-is-psclofun
 : (X : 𝓤 ̇ ) (Y : ClosenessSpace 𝓥)
 → {n : ℕ}
 → (v : Vec X n)
 → is-pseudocloseness (Least-clofun X Y v)
Least-clofun-is-psclofun X Y {n} v
 = (λ f → pr₁ (pr₂ γ) (vec-map f v))
 , (λ f g → pr₁ (pr₂ (pr₂ γ)) (vec-map f v) (vec-map g v))
 , (λ f g h → pr₂ (pr₂ (pr₂ γ)) (vec-map f v) (vec-map g v) (vec-map h v))
 where
  γ : is-closeness (pr₁ (Vec-clospace Y n))
  γ = pr₂ (Vec-clospace Y n)

Least-PseudoClosenessSpace : (X : 𝓤 ̇ ) (Y : ClosenessSpace 𝓥)
                               → (f : X → ⟨ Y ⟩)
                               → {n : ℕ}
                               → Vec X n
                               → PseudoClosenessSpace (𝓤 ⊔ 𝓥)
Least-PseudoClosenessSpace X Y f v
 = (X → ⟨ Y ⟩)
 , Least-clofun X Y v
 , Least-clofun-is-psclofun X Y v


close-to-close : (X : ClosenessSpace 𝓤)
               → (Y : ClosenessSpace 𝓥)
               → (Z : ClosenessSpace 𝓦)
               → (f : ⟨ X ⟩ → ⟨ Y ⟩ → ⟨ Z ⟩)
               → {n : ℕ} (v : Vec ⟨ Y ⟩ n)
               → ((y : ⟨ Y ⟩) → f-ucontinuous X Z (λ x → f x y))
               → ((g : ⟨ Y ⟩ → ⟨ Z ⟩) → f-ucontinuous' (ι X)
                   (Least-PseudoClosenessSpace ⟨ Y ⟩ Z g v)
                   f)
close-to-close X Y Z f {0} ⟨⟩ _ k ε = 0 , λ _ _ _ _ _ → refl
close-to-close X Y Z f {succ n} v@(y :: ys) ϕʸ g ε = δ , γ
 where
  IH = close-to-close X Y Z f ys ϕʸ g ε
  δ δ₁ δ₂ : ℕ
  δ₁ = pr₁ (ϕʸ y ε)
  δ₂ = pr₁ IH
  δ = max δ₁ δ₂
  γ : (x₁ x₂ : ⟨ X ⟩) → C X δ x₁ x₂
    → C' (Least-PseudoClosenessSpace ⟨ Y ⟩ Z g v) ε (f x₁) (f x₂)
  γ x₁ x₂ Cx₁x₂ n z
   = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
       (pr₂ (ϕʸ y ε) x₁ x₂
         (C-mono X δ δ₁ (max-≤-upper-bound δ₁ δ₂) x₁ x₂ Cx₁x₂) n z)
       (pr₂ IH x₁ x₂
         (C-mono X δ δ₂ (max-≤-upper-bound' δ₂ δ₁) x₁ x₂ Cx₁x₂) n z)
\end{code}

## Subtype closeness spaces

\begin{code}
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

Σ-clospace : {X : 𝓤 ̇ }
           → (P : X → 𝓥 ̇ )
           → (p : (x : X) → is-prop (P x))
           → is-closeness-space X
           → is-closeness-space (Σ P)
Σ-clospace P p i = ↪-clospace (pr₁ , pr₁-is-embedding p) i

Σ-ClosenessSpace : (X : ClosenessSpace 𝓤)
                 → (P : ⟨ X ⟩ → 𝓥 ̇ )
                 → (p : (x : ⟨ X ⟩) → is-prop (P x))
                 → ClosenessSpace (𝓤 ⊔ 𝓥)
Σ-ClosenessSpace {𝓤} {𝓥} X P p
 = Σ P , Σ-clospace P p (pr₂ X)

≃-ClosenessSpace : {X : 𝓤 ̇ } (Y : ClosenessSpace 𝓥)
                 → X ≃ ⟨ Y ⟩
                 → ClosenessSpace 𝓤
≃-ClosenessSpace Y e
  = ↪-ClosenessSpace Y (equivs-embedding e)

≃-preserves-nets : {X : 𝓤 ̇ } (Y : ClosenessSpace 𝓥)
                 → (e : X ≃ ⟨ Y ⟩)
                 → (ε : ℕ)
                 → (Y' : 𝓥' ̇ )
                 → Y' is ε net-of Y
                 → Y' is ε net-of (≃-ClosenessSpace Y e)
≃-preserves-nets Y (f , ((g , η) , (h , μ))) ε Y' ((gₙ , hₙ , ηₙ) , fₙ)
 = (g ∘ gₙ , hₙ ∘ f
 , λ x
 → C-trans Y ε (f x) (gₙ (hₙ (f x))) (f (g (gₙ (hₙ (f x))))) (ηₙ (f x))
    (closeness-∞-implies-ϵ-close Y (gₙ (hₙ (f x))) (f (g (gₙ (hₙ (f x)))))
      (identical-implies-closeness-∞ Y _ _ (η (gₙ (hₙ (f x))) ⁻¹)) ε))
 , fₙ

≃-totally-bounded : {X : 𝓤 ̇ }
                  → (Y : ClosenessSpace 𝓥)
                  → (e : X ≃ ⟨ Y ⟩)
                  → totally-bounded Y 𝓥'
                  → totally-bounded (≃-ClosenessSpace Y e) 𝓥'
≃-totally-bounded Y e t ε
 = pr₁ (t ε) , ≃-preserves-nets Y e ε (pr₁ (t ε)) (pr₂ (t ε))
\end{code}

## Discrete sequence closeness spaces

\begin{code}
decidable-𝟚 : {X : 𝓤 ̇ } → is-decidable X → 𝟚
decidable-𝟚 (inl _) = ₁
decidable-𝟚 (inr _) = ₀

decidable-𝟚₁ : {X : 𝓤 ̇ } (d : is-decidable X)
             → X
             → decidable-𝟚 d ＝ ₁
decidable-𝟚₁ (inl  x) _ = refl
decidable-𝟚₁ (inr ¬x) x = 𝟘-elim (¬x x)

decidable-𝟚₀ : {X : 𝓤 ̇ } (d : is-decidable X)
             → ¬ X
             → decidable-𝟚 d ＝ ₀
decidable-𝟚₀ (inl  x) ¬x = 𝟘-elim (¬x x)
decidable-𝟚₀ (inr ¬x)  _ = refl

𝟚-decidable₁ : {X : 𝓤 ̇ } (d : is-decidable X)
             → decidable-𝟚 d ＝ ₁ → X
𝟚-decidable₁ (inl x)  _ = x
𝟚-decidable₁ (inr ¬x) e = 𝟘-elim (zero-is-not-one e)

𝟚-decidable₀ : {X : 𝓤 ̇ } (d : is-decidable X)
             → decidable-𝟚 d ＝ ₀
             → ¬ X
𝟚-decidable₀ (inl x)  e = 𝟘-elim (one-is-not-zero e)
𝟚-decidable₀ (inr ¬x) _ = ¬x

decidable-seq-𝟚 : {X : ℕ → 𝓤 ̇ } → is-complemented X → (ℕ → 𝟚)
decidable-seq-𝟚 d n = decidable-𝟚 (d (succ n))

discrete-seq-clofun'
 : {X : ℕ → 𝓤 ̇ } → ((i : ℕ) → is-discrete (X i)) → Π X → Π X → (ℕ → 𝟚)
discrete-seq-clofun' d α β
 = decidable-seq-𝟚 (∼ⁿ-decidable d α β)

discrete-seq-clofun'-e
 : {X : ℕ → 𝓤 ̇ }
 → (d : (i : ℕ) → is-discrete (X i))
 → (α β : Π X)
 → ((n : ℕ) → discrete-seq-clofun' d α β n ＝ ₁)
 → α ＝ β
discrete-seq-clofun'-e d α β f
 = dfunext (fe _ _)
     (λ n → 𝟚-decidable₁ (∼ⁿ-decidable d α β (succ n))
              (f n) n (<-succ n))

discrete-seq-clofun'-i
 : {X : ℕ → 𝓤 ̇ }
 → (d : (i : ℕ) → is-discrete (X i))
 → (α : Π X)
 → (n : ℕ) → discrete-seq-clofun' d α α n ＝ ₁
discrete-seq-clofun'-i d α n
 = decidable-𝟚₁ (∼ⁿ-decidable d α α (succ n)) (λ _ _ → refl)

discrete-seq-clofun'-s
 : {X : ℕ → 𝓤 ̇ }
 → (d : (i : ℕ) → is-discrete (X i))
 → (α β : Π X)
 → (n : ℕ)
 → discrete-seq-clofun' d α β n ＝ discrete-seq-clofun' d β α n
discrete-seq-clofun'-s d α β n
 = γ (∼ⁿ-decidable d α β (succ n)) (∼ⁿ-decidable d β α (succ n))
 where
  γ : (dαβ : is-decidable ((α ∼ⁿ β) (succ n)))
    → (dβα : is-decidable ((β ∼ⁿ α) (succ n)))
    → decidable-𝟚 dαβ ＝ decidable-𝟚 dβα
  γ (inl _) (inl _) = refl
  γ (inr _) (inr _) = refl
  γ (inl f) (inr g) = 𝟘-elim (g (∼ⁿ-sym α β (succ n) f))
  γ (inr f) (inl g) = 𝟘-elim (f (∼ⁿ-sym β α (succ n) g))

discrete-seq-clofun'-u
 : {X : ℕ → 𝓤 ̇ }
 → (d : (i : ℕ) → is-discrete (X i))
 → (α β ζ : Π X)
 → (n : ℕ)
 → min𝟚 (discrete-seq-clofun' d α β n)
        (discrete-seq-clofun' d β ζ n) ＝ ₁
 → discrete-seq-clofun' d α ζ n ＝ ₁
discrete-seq-clofun'-u d α β ζ n
 = γ (∼ⁿ-decidable d α β (succ n))
     (∼ⁿ-decidable d β ζ (succ n))
     (∼ⁿ-decidable d α ζ (succ n))
 where
  γ : (dαβ : is-decidable ((α ∼ⁿ β) (succ n)))
    → (dβζ : is-decidable ((β ∼ⁿ ζ) (succ n)))
    → (dαζ : is-decidable ((α ∼ⁿ ζ) (succ n)))
    → min𝟚 (decidable-𝟚 dαβ) (decidable-𝟚 dβζ) ＝ ₁
    → decidable-𝟚 dαζ ＝ ₁
  γ _          _          (inl _) _ = refl
  γ (inl α∼ⁿβ) (inr _)    (inr _)     m = 𝟘-elim (zero-is-not-one m)
  γ (inr _)     dβζ       (inr _)     m = 𝟘-elim (zero-is-not-one m)
  γ (inl α∼ⁿβ) (inl β∼ⁿζ) (inr ¬α∼ⁿζ) m
   = 𝟘-elim (¬α∼ⁿζ (λ i i<n → α∼ⁿβ i i<n ∙ β∼ⁿζ i i<n))

∼ⁿ-decidable-𝟚-decreasing
 : {X : ℕ → 𝓤 ̇ }
 → (d : (i : ℕ) → is-discrete (X i))
 → (α β : Π X)
 → is-decreasing (discrete-seq-clofun' d α β)
∼ⁿ-decidable-𝟚-decreasing d α β n
 = ≤₂-criterion (γ (∼ⁿ-decidable d α β (succ n))
                   (∼ⁿ-decidable d α β (succ (succ n))))
 where
  γ : (dαβₛₙ  : is-decidable ((α ∼ⁿ β) (succ n)))
    → (dαβₛₛₙ : is-decidable ((α ∼ⁿ β) (succ (succ n))))
    → decidable-𝟚 dαβₛₛₙ ＝ ₁
    → decidable-𝟚 dαβₛₙ ＝ ₁
  γ (inl _) (inl _) _ = refl
  γ (inl _) (inr _) _ = refl
  γ (inr _) (inr _) e = 𝟘-elim (zero-is-not-one e)
  γ (inr ¬α∼ˢⁿβ) (inl α∼ˢˢⁿβ) _
   = (𝟘-elim ∘ ¬α∼ˢⁿβ)
       (λ i i<sn → α∼ˢˢⁿβ i
         (<-trans i (succ n) (succ (succ n)) i<sn
           (<-succ (succ n))))

discrete-seq-clofun
 : {X : ℕ → 𝓤 ̇ }
 → ((i : ℕ) → is-discrete (X i))
 → Π X → Π X → ℕ∞
discrete-seq-clofun d α β
 = discrete-seq-clofun' d α β
 , ∼ⁿ-decidable-𝟚-decreasing d α β

discrete-seq-clofun-e
 : {X : ℕ → 𝓤 ̇ }
 → (d : (i : ℕ) → is-discrete (X i))
 → indistinguishable-are-equal (discrete-seq-clofun d)
discrete-seq-clofun-e d α β cαβ=∞
 = discrete-seq-clofun'-e d α β (λ n → ap (λ - → ℕ∞-to-ℕ→𝟚 - n) cαβ=∞)

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

∼ⁿ-to-C' : {X : ℕ → 𝓤 ̇ }
         → (d : (i : ℕ) → is-discrete (X i))
         → (α β : Π X) (n : ℕ)
         → (α ∼ⁿ β) n
         → C (ΠD-ClosenessSpace d) n α β
∼ⁿ-to-C' d α β zero     α∼ⁿβ i i<n = 𝟘-elim (zero-is-not-one i<n)
∼ⁿ-to-C' d α β (succ n) α∼ⁿβ i i<n
 = is-decreasing' (discrete-seq-clofun d α β)
     n i (⊏-gives-< i (succ n) i<n)
     (decidable-𝟚₁ (∼ⁿ-decidable d α β (succ n)) α∼ⁿβ)

C-to-∼ⁿ' : {X : ℕ → 𝓤 ̇ }
         → (d : (i : ℕ) → is-discrete (X i))
         → (α β : Π X) (n : ℕ)
         → C (ΠD-ClosenessSpace d) n α β
         → (α ∼ⁿ β) n
C-to-∼ⁿ' d α β zero     Cαβ i i<n = 𝟘-elim i<n
C-to-∼ⁿ' d α β (succ n) Cαβ i i<n
 = 𝟚-decidable₁ (∼ⁿ-decidable d α β (succ n))
     (Cαβ n (<-gives-⊏ n (succ n) (<-succ n))) i i<n

ℕ→D-ClosenessSpace : {X : 𝓤 ̇ }
                   → (d : is-discrete X)
                   → ClosenessSpace 𝓤
ℕ→D-ClosenessSpace {𝓤} {X} d = ΠD-ClosenessSpace (λ _ → d)

∼ⁿ-to-C : {X : 𝓤 ̇ } → (d : is-discrete X)
        → (α β : (ℕ → X)) (n : ℕ)
        → (α ∼ⁿ β) n
        → C (ℕ→D-ClosenessSpace d) n α β
∼ⁿ-to-C d = ∼ⁿ-to-C' (λ _ → d)

C-to-∼ⁿ : {X : 𝓤 ̇ } → (d : is-discrete X)
        → (α β : (ℕ → X)) (n : ℕ)
        → C (ℕ→D-ClosenessSpace d) n α β
        → (α ∼ⁿ β) n
C-to-∼ⁿ d = C-to-∼ⁿ' (λ _ → d)

ΠF-totally-bounded : {F : ℕ → 𝓤 ̇ }
                   → (d : (i : ℕ) → is-discrete (F i))
                   → (f : (i : ℕ) → finite-linear-order (F i))
                   → Π F
                   → totally-bounded (ΠD-ClosenessSpace d) 𝓤
ΠF-totally-bounded {𝓤} {F} d f α ϵ
 = vec ϵ (F ∘ ⟦_⟧)
 , (Vec-to-Seq ϵ (α ∘ succ ^ ϵ) , Seq-to-Vec ϵ , γ)
 , vec-is-finite ϵ (f ∘ ⟦_⟧)
 where
  γ : (β : ⟨ ΠD-ClosenessSpace d ⟩)
    → C (ΠD-ClosenessSpace d) ϵ β
        (Vec-to-Seq ϵ (α ∘ succ ^ ϵ) (Seq-to-Vec ϵ β))
  γ β n n⊏ϵ = decidable-𝟚₁ (∼ⁿ-decidable d _ _ _)
                (λ i i<sn → Seq-to-Vec-∼ ϵ (α ∘ succ ^ ϵ) β i
                  (≤-<-trans i n ϵ i<sn (⊏-gives-< n ϵ n⊏ϵ)))

ℕ→F-totally-bounded : {F : 𝓤 ̇ }
                    → (d : is-discrete F)
                    → (f : finite-linear-order F) → F
                    → totally-bounded (ℕ→D-ClosenessSpace d) 𝓤
ℕ→F-totally-bounded {𝓤} {F} d f x₀
 = ΠF-totally-bounded (λ _ → d) (λ _ → f) (λ _ → x₀)
\end{code}

## Infinitary product of closeness spaces

\begin{code}
Π-clofun' : (T : ℕ → ClosenessSpace 𝓤)
          → Π (⟨_⟩ ∘ T) → Π (⟨_⟩ ∘ T) → (ℕ → 𝟚)
Π-clofun' T x y zero = ℕ∞-to-ℕ→𝟚 (c⟨ T 0 ⟩ (x 0) (y 0)) 0
Π-clofun' T x y (succ n)
 = min𝟚 (ℕ∞-to-ℕ→𝟚 (c⟨ T 0 ⟩ (x 0) (y 0)) (succ n))
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
              → (n : ℕ)
              → (ℕ∞-to-ℕ→𝟚 (c⟨ T n ⟩ (x n) (y n))) ∼ (λ i → ₁)
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
     (λ i → e⟨ T i ⟩ (x i) (y i)
       (to-subtype-＝ (being-decreasing-is-prop (fe _ _))
         (dfunext (fe _ _) (Π-clofun'-all T x y f i))))

Π-clofun'-i : (T : ℕ → ClosenessSpace 𝓤)
            → (x : Π (⟨_⟩ ∘ T)) → Π-clofun' T x x ∼ (λ i → ₁)
Π-clofun'-i T x 0 = ap (λ - → ℕ∞-to-ℕ→𝟚 - 0) (i⟨ T 0 ⟩ (x 0))
Π-clofun'-i T x (succ n)
 = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
     (ap (λ - → ℕ∞-to-ℕ→𝟚 - (succ n)) (i⟨ T 0 ⟩ (x 0)))
     (Π-clofun'-i (T ∘ succ) (x ∘ succ) n)

Π-clofun'-s : (T : ℕ → ClosenessSpace 𝓤)
            → (x y : Π (⟨_⟩ ∘ T))
            → Π-clofun' T x y ∼ Π-clofun' T y x
Π-clofun'-s T x y zero
 = ap (λ - → ℕ∞-to-ℕ→𝟚 - 0) (s⟨ T 0 ⟩ (x 0) (y 0))
Π-clofun'-s T x y (succ n)
 = ap (λ - → min𝟚 - (Π-clofun' (T ∘ succ) (x ∘ succ) (y ∘ succ) n))
     (ap (λ - → pr₁ - (succ n)) (s⟨ T 0 ⟩ (x 0) (y 0)))
 ∙ ap (λ - → min𝟚 (pr₁ (c⟨ T 0 ⟩ (y 0) (x 0)) (succ n)) -)
     (Π-clofun'-s (T ∘ succ) (x ∘ succ) (y ∘ succ) n)

Lemma[min𝟚abcd＝₁→min𝟚ac＝₁] : (a b c d : 𝟚)
                            → min𝟚 (min𝟚 a b) (min𝟚 c d) ＝ ₁
                            → min𝟚 a c ＝ ₁
Lemma[min𝟚abcd＝₁→min𝟚ac＝₁] ₀ b c d e = 𝟘-elim (zero-is-not-one e)
Lemma[min𝟚abcd＝₁→min𝟚ac＝₁] ₁ ₀ c d e = 𝟘-elim (zero-is-not-one e)
Lemma[min𝟚abcd＝₁→min𝟚ac＝₁] ₁ ₁ ₀ d e = 𝟘-elim (zero-is-not-one e)
Lemma[min𝟚abcd＝₁→min𝟚ac＝₁] ₁ ₁ ₁ ₀ e = 𝟘-elim (zero-is-not-one e)
Lemma[min𝟚abcd＝₁→min𝟚ac＝₁] ₁ ₁ ₁ ₁ e = refl

Lemma[min𝟚abcd＝₁→min𝟚bd＝₁] : (a b c d : 𝟚)
                            → min𝟚 (min𝟚 a b) (min𝟚 c d) ＝ ₁
                            → min𝟚 b d ＝ ₁
Lemma[min𝟚abcd＝₁→min𝟚bd＝₁] ₀ b c d e = 𝟘-elim (zero-is-not-one e)
Lemma[min𝟚abcd＝₁→min𝟚bd＝₁] ₁ ₀ c d e = 𝟘-elim (zero-is-not-one e)
Lemma[min𝟚abcd＝₁→min𝟚bd＝₁] ₁ ₁ ₀ d e = 𝟘-elim (zero-is-not-one e)
Lemma[min𝟚abcd＝₁→min𝟚bd＝₁] ₁ ₁ ₁ ₀ e = 𝟘-elim (zero-is-not-one e)
Lemma[min𝟚abcd＝₁→min𝟚bd＝₁] ₁ ₁ ₁ ₁ e = refl

Π-clofun'-u : (T : ℕ → ClosenessSpace 𝓤)
            → (x y z : Π (⟨_⟩ ∘ T))
            → (n : ℕ)
            → min𝟚 (Π-clofun' T x y n) (Π-clofun' T y z n) ＝ ₁
            → Π-clofun' T x z n ＝ ₁
Π-clofun'-u T x y z 0 η
 = u⟨ T 0 ⟩ (x 0) (y 0) (z 0) 0 η
Π-clofun'-u T x y z (succ n) η
 = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
     (u⟨ T 0 ⟩ (x 0) (y 0) (z 0) (succ n)
       (Lemma[min𝟚abcd＝₁→min𝟚ac＝₁]
         (ℕ∞-to-ℕ→𝟚 (c⟨ T 0 ⟩ (x 0) (y 0)) (succ n))
         (Π-clofun' (T ∘ succ) (x ∘ succ) (y ∘ succ) n)
         (ℕ∞-to-ℕ→𝟚 (c⟨ T 0 ⟩ (y 0) (z 0)) (succ n))
         (Π-clofun' (T ∘ succ) (y ∘ succ) (z ∘ succ) n)
         η))
     (Π-clofun'-u (T ∘ succ) (x ∘ succ) (y ∘ succ) (z ∘ succ) n
       (Lemma[min𝟚abcd＝₁→min𝟚bd＝₁]
         (ℕ∞-to-ℕ→𝟚 (c⟨ T 0 ⟩ (x 0) (y 0)) (succ n))
         (Π-clofun' (T ∘ succ) (x ∘ succ) (y ∘ succ) n)
         (ℕ∞-to-ℕ→𝟚 (c⟨ T 0 ⟩ (y 0) (z 0)) (succ n))
         (Π-clofun' (T ∘ succ) (y ∘ succ) (z ∘ succ) n)
         η))

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
  g (x' , αₛ') = g₀' x' ∷ gₛ' αₛ'
  h : Π (⟨_⟩ ∘ T) → t₀' × IH'
  h α = h₀' (α 0) , hₛ' (α ∘ succ)
  η : (x : Π (⟨_⟩ ∘ T)) → C (Π-ClosenessSpace T) (succ ϵ) x (g (h x))
  η α 0 = η₀' (α 0) 0
  η α (succ n) n⊏ϵ
   = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
       (η₀' (α 0) (succ n) n⊏ϵ)
       (ηₛ' (α ∘ succ) n n⊏ϵ)
  f : finite-linear-order (t₀' × IH')
  f = ×-is-finite (pr₂ t₀'-is-sϵ-net) (pr₂ IH'-is-ϵ-net)

Π-clofuns-id' : {T : ℕ → 𝓤 ̇ }
              → (d : (i : ℕ) → is-discrete (T i))
              → (x y : Π T)
              → discrete-seq-clofun' d x y
              ∼ Π-clofun' (λ n → D-ClosenessSpace (d n)) x y
Π-clofuns-id' d x y 0 = γ (∼ⁿ-decidable d x y 1) (d 0 (x 0) (y 0))
 where
  γ : (dx∼¹y : is-decidable ((x ∼ⁿ y) 1))
    → (dxy₀ : is-decidable (x 0 ＝ y 0))
    → decidable-𝟚 dx∼¹y ＝ pr₁ (discrete-clofun'' (x 0) (y 0) dxy₀) 0
  γ (inl _) (inl _) = refl
  γ (inr _) (inr _) = refl
  γ (inl  x∼¹y) (inr x₀≠y₀) = 𝟘-elim (x₀≠y₀ (x∼¹y 0 ⋆))
  γ (inr ¬x∼¹y) (inl x₀=y₀) = 𝟘-elim (¬x∼¹y γ')
   where
    γ' : (x ∼ⁿ y) 1
    γ' 0        ⋆ = x₀=y₀
    γ' (succ i) l = 𝟘-elim l
Π-clofuns-id' d x y (succ i)
 = γ (∼ⁿ-decidable d x y (succ (succ i))) (d 0 (x 0) (y 0))
 where
  γ' : x 0 ＝ y 0
     → ((x ∘ succ) ∼ⁿ (y ∘ succ)) (succ i)
     → (x ∼ⁿ y) (succ (succ i))
  γ' x₀=y₀ tx∼ˢⁱty 0 _ = x₀=y₀
  γ' x₀=y₀ tx∼ˢⁱty (succ j) = tx∼ˢⁱty j
  γ : (dx∼ˢˢⁱy : is-decidable ((x ∼ⁿ y) (succ (succ i))))
    → (dxy₀ : is-decidable (x 0 ＝ y 0))
    → decidable-𝟚 dx∼ˢˢⁱy
    ＝ min𝟚 (pr₁ (discrete-clofun'' (x 0) (y 0) dxy₀) (succ i))
           (Π-clofun' (λ n → D-ClosenessSpace (d (succ n)))
             (x ∘ succ) (y ∘ succ) i)
  γ (inl  x∼ˢˢⁱy) (inl _)
   = Lemma[a＝₁→b＝₁→min𝟚ab＝₁] refl
       (Π-clofuns-id' (d ∘ succ) (x ∘ succ) (y ∘ succ) i ⁻¹
       ∙ decidable-𝟚₁ (∼ⁿ-decidable (d ∘ succ) _ _ _)
           (x∼ˢˢⁱy ∘ succ))  ⁻¹
  γ (inl  x∼ˢˢⁱy) (inr x₀≠y₀) = 𝟘-elim (x₀≠y₀ (x∼ˢˢⁱy 0 ⋆))
  γ (inr ¬x∼ˢˢⁱy) (inl x₀=y₀)
   = Lemma[min𝟚ab＝₀]
        (inr (Π-clofuns-id' (d ∘ succ) (x ∘ succ) (y ∘ succ) i ⁻¹
             ∙ decidable-𝟚₀ (∼ⁿ-decidable (d ∘ succ) _ _ _)
                 (λ tx∼ˢⁱty → ¬x∼ˢˢⁱy (γ' x₀=y₀ tx∼ˢⁱty)))) ⁻¹
  γ (inr ¬x∼ˢˢⁱy) (inr x₀≠y₀) = refl

Π-clofuns-id
 : {T : ℕ → 𝓤 ̇ }
 → (d : (i : ℕ) → is-discrete (T i))
 → c⟨ ΠD-ClosenessSpace d ⟩
 ＝ c⟨ Π-ClosenessSpace (λ n → D-ClosenessSpace (d n)) ⟩
Π-clofuns-id d
 = dfunext (fe _ _) (λ x → dfunext (fe _ _) (λ y →
     to-subtype-＝ (being-decreasing-is-prop (fe _ _))
       (dfunext (fe _ _) (Π-clofuns-id' d x y))))

Π-C-combine : (T : ℕ → ClosenessSpace 𝓤)
            → (x₁ x₂ : ⟨ T 0 ⟩) (y₁ y₂ : Π (⟨_⟩ ∘ T ∘ succ))
            → (ε : ℕ)
            → C (T 0) (succ ε) x₁ x₂
            → C (Π-ClosenessSpace (T ∘ succ)) ε y₁ y₂
            → C (Π-ClosenessSpace T) (succ ε) (x₁ ∷ y₁) (x₂ ∷ y₂)
Π-C-combine T x₁ x₂ y₁ y₂ ε Cεx₁x₂ Cεy₁y₂ 0
 = Cεx₁x₂ 0
Π-C-combine T x₁ x₂ y₁ y₂ ε Cεx₁x₂ Cεy₁y₂ (succ n) sn⊏ε
 = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
     (Cεx₁x₂ (succ n) sn⊏ε)
     (Cεy₁y₂ n sn⊏ε)

Π-C-eta : (T : ℕ → ClosenessSpace 𝓤)
        → (α : Π (⟨_⟩ ∘ T))
        → (ε : ℕ)
        → C (Π-ClosenessSpace T) ε α (α 0 ∷ (α ∘ succ))
Π-C-eta T α ε 0 = C-refl (T 0) ε (α 0) 0
Π-C-eta T α zero     (succ n) l = 𝟘-elim (zero-is-not-one l)
Π-C-eta T α (succ ε) (succ n)
 = Π-C-combine T (α 0) (α 0) (α ∘ succ) (α ∘ succ) ε
     (C-refl (T 0) (succ ε) (α 0))
     (C-refl (Π-ClosenessSpace (T ∘ succ)) ε (α ∘ succ))
     (succ n)
\end{code}

## Specific examples of closeness spaces

\begin{code}
𝟚ᴺ-ClosenessSpace : ClosenessSpace 𝓤₀
𝟚ᴺ-ClosenessSpace = ℕ→D-ClosenessSpace 𝟚-is-discrete

𝟚ᴺ×𝟚ᴺ-ClosenessSpace : ClosenessSpace 𝓤₀
𝟚ᴺ×𝟚ᴺ-ClosenessSpace
 = ×-ClosenessSpace 𝟚ᴺ-ClosenessSpace 𝟚ᴺ-ClosenessSpace

ℕ∞-ClosenessSpace : ClosenessSpace 𝓤₀
ℕ∞-ClosenessSpace
 = Σ-ClosenessSpace 𝟚ᴺ-ClosenessSpace is-decreasing
     (being-decreasing-is-prop (fe _ _))

open import TWA.Thesis.Chapter5.SignedDigit

𝟛ᴺ-ClosenessSpace : ClosenessSpace 𝓤₀
𝟛ᴺ-ClosenessSpace = ℕ→D-ClosenessSpace 𝟛-is-discrete

𝟛ᴺ×𝟛ᴺ-ClosenessSpace : ClosenessSpace 𝓤₀
𝟛ᴺ×𝟛ᴺ-ClosenessSpace
 = ×-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
\end{code}
