This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.More-Exercise-Solutions where

open import MGS.Classifiers             public
open import MGS.Subsingleton-Truncation public


module ℕ-order-exercise-solution where

  _≤'_ : ℕ → ℕ → 𝓤₀ ̇
  _≤'_ = ℕ-iteration (ℕ → 𝓤₀ ̇ ) (λ y → 𝟙)
          (λ f → ℕ-recursion (𝓤₀ ̇ ) 𝟘 (λ y P → f y))

  open ℕ-order

  ≤-and-≤'-coincide : (x y : ℕ) → (x ≤ y) ＝ (x ≤' y)
  ≤-and-≤'-coincide 0 y = refl _
  ≤-and-≤'-coincide (succ x) 0 = refl _
  ≤-and-≤'-coincide (succ x) (succ y) = ≤-and-≤'-coincide x y

module ℕ-more where

  open Arithmetic renaming (_+_ to _∔_)
  open basic-arithmetic-and-order

  ≤-prop-valued : (x y : ℕ) → is-subsingleton (x ≤ y)
  ≤-prop-valued 0 y               = 𝟙-is-subsingleton
  ≤-prop-valued (succ x) zero     = 𝟘-is-subsingleton
  ≤-prop-valued (succ x) (succ y) = ≤-prop-valued x y

  ≼-prop-valued : (x y : ℕ) → is-subsingleton (x ≼ y)
  ≼-prop-valued x y (z , p) (z' , p') = γ
   where
    q : z ＝ z'
    q = +-lc x z z' (x ∔ z  ＝⟨ p ⟩
                     y      ＝⟨ p' ⁻¹ ⟩
                     x ∔ z' ∎)

    γ : z , p ＝ z' , p'
    γ = to-subtype-＝ (λ z → ℕ-is-set (x ∔ z) y) q

  ≤-charac : propext 𝓤₀ → (x y : ℕ) → (x ≤ y) ＝ (x ≼ y)
  ≤-charac pe x y = pe (≤-prop-valued x y) (≼-prop-valued x y)
                       (≤-gives-≼ x y) (≼-gives-≤ x y)

the-subsingletons-are-the-subtypes-of-a-singleton : (X : 𝓤 ̇ )
                                                  → is-subsingleton X ↔ (X ↪ 𝟙)
the-subsingletons-are-the-subtypes-of-a-singleton X = φ , ψ
 where
  i : is-subsingleton X → is-embedding (!𝟙' X)
  i s ⋆ (x , refl ⋆) (y , refl ⋆) = ap (λ - → - , refl ⋆) (s x y)

  φ : is-subsingleton X → X ↪ 𝟙
  φ s = !𝟙 , i s

  ψ : X ↪ 𝟙 → is-subsingleton X
  ψ (f , e) x y = d
   where
    a : x ＝ y → f x ＝ f y
    a = ap f {x} {y}

    b : is-equiv a
    b = embedding-gives-ap-is-equiv f e x y

    c : f x ＝ f y
    c = 𝟙-is-subsingleton (f x) (f y)

    d : x ＝ y
    d = inverse a b c

the-subsingletons-are-the-subtypes-of-a-singleton' : propext 𝓤 → global-dfunext
                                                   → (X : 𝓤 ̇ )
                                                   → is-subsingleton X ＝ (X ↪ 𝟙)
the-subsingletons-are-the-subtypes-of-a-singleton' pe fe X = γ
 where
  a : is-subsingleton X ↔ (X ↪ 𝟙)
  a = the-subsingletons-are-the-subtypes-of-a-singleton X

  b : is-subsingleton (X ↪ 𝟙)
  b (f , e) (f' , e') = to-subtype-＝
                           (being-embedding-is-subsingleton fe)
                           (fe (λ x → 𝟙-is-subsingleton (f x) (f' x)))

  γ : is-subsingleton X ＝ (X ↪ 𝟙)
  γ = pe (being-subsingleton-is-subsingleton fe) b (pr₁ a) (pr₂ a)

G↑-≃-equation : (ua : is-univalent (𝓤 ⊔ 𝓥))
              → (X : 𝓤 ̇ )
              → (A : (Σ Y ꞉ 𝓤 ⊔ 𝓥 ̇ , X ≃ Y) → 𝓦 ̇ )
              → (a : A (Lift 𝓥 X , ≃-Lift X))
              → G↑-≃ ua X A a (Lift 𝓥 X) (≃-Lift X) ＝ a
G↑-≃-equation {𝓤} {𝓥} {𝓦} ua X A a =
  G↑-≃ ua X A a (Lift 𝓥 X) (≃-Lift X) ＝⟨ refl (transport A p a) ⟩
  transport A p a                     ＝⟨ ap (λ - → transport A - a) q ⟩
  transport A (refl t) a              ＝⟨ refl a ⟩
  a                                   ∎
 where
  t : (Σ Y ꞉ 𝓤 ⊔ 𝓥 ̇ , X ≃ Y)
  t = (Lift 𝓥 X , ≃-Lift X)

  p : t ＝ t
  p = univalence→'' {𝓤} {𝓤 ⊔ 𝓥} ua X t t

  q : p ＝ refl t
  q = subsingletons-are-sets (Σ Y ꞉ 𝓤 ⊔ 𝓥 ̇ , X ≃ Y)
       (univalence→'' {𝓤} {𝓤 ⊔ 𝓥} ua X) t t p (refl t)

H↑-≃-equation : (ua : is-univalent (𝓤 ⊔ 𝓥))
              → (X : 𝓤 ̇ )
              → (A : (Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓦 ̇ )
              → (a : A (Lift 𝓥 X) (≃-Lift X))
              → H↑-≃ ua X A a (Lift 𝓥 X) (≃-Lift X) ＝ a
H↑-≃-equation ua X A = G↑-≃-equation ua X (Σ-induction A)

has-section-charac : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                   → ((y : Y) → Σ x ꞉ X , f x ＝ y) ≃ has-section f
has-section-charac f = ΠΣ-distr-≃

retractions-into : 𝓤 ̇ → 𝓤 ⁺ ̇
retractions-into {𝓤} Y = Σ X ꞉ 𝓤 ̇ , Y ◁ X

pointed-types : (𝓤 : Universe) → 𝓤 ⁺ ̇
pointed-types 𝓤 = Σ X ꞉ 𝓤 ̇ , X

retraction-classifier : Univalence
                      → (Y : 𝓤 ̇ ) → retractions-into Y ≃ (Y → pointed-types 𝓤)
retraction-classifier {𝓤} ua Y =
 retractions-into Y                                              ≃⟨ i ⟩
 (Σ X ꞉ 𝓤 ̇ , Σ f ꞉ (X → Y) , ((y : Y) → Σ x ꞉ X , f x ＝ y))     ≃⟨ id-≃ _ ⟩
 ((𝓤 /[ id ] Y))                                                 ≃⟨ ii ⟩
 (Y → pointed-types 𝓤)                                           ■
 where
  i  = ≃-sym (Σ-cong (λ X → Σ-cong (λ f → ΠΣ-distr-≃)))
  ii = special-map-classifier (ua 𝓤)
        (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))
        id Y

module surjection-classifier
         (pt : subsingleton-truncations-exist)
         (ua : Univalence)
       where

  hfe : global-hfunext
  hfe = univalence-gives-global-hfunext ua

  open basic-truncation-development pt hfe public

  _↠_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
  X ↠ Y = Σ f ꞉ (X → Y), is-surjection f

  surjections-into : 𝓤 ̇ → 𝓤 ⁺ ̇
  surjections-into {𝓤} Y = Σ X ꞉ 𝓤 ̇ , X ↠ Y

  inhabited-types : (𝓤 : Universe) → 𝓤 ⁺ ̇
  inhabited-types 𝓤 = Σ X ꞉ 𝓤 ̇ , ∥ X ∥

  surjection-classifier : Univalence
                        → (Y : 𝓤 ̇ )
                        → surjections-into Y ≃ (Y → inhabited-types 𝓤)
  surjection-classifier {𝓤} ua = special-map-classifier (ua 𝓤)
                                  (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))
                                  ∥_∥

positive-cantors-diagonal : (e : ℕ → (ℕ → ℕ)) → Σ α ꞉ (ℕ → ℕ), ((n : ℕ) → α ≠ e n)

cantors-diagonal : ¬ (Σ e ꞉ (ℕ → (ℕ → ℕ)) , ((α : ℕ → ℕ) → Σ n ꞉ ℕ , α ＝ e n))

𝟚-has-𝟚-automorphisms : dfunext 𝓤₀ 𝓤₀ → (𝟚 ≃ 𝟚) ≃ 𝟚

lifttwo : is-univalent 𝓤₀ → is-univalent 𝓤₁ → (𝟚 ＝ 𝟚) ＝ Lift 𝓤₁ 𝟚

DNE : ∀ 𝓤 → 𝓤 ⁺ ̇
DNE 𝓤 = (P : 𝓤 ̇ ) → is-subsingleton P → ¬¬ P → P

ne : (X : 𝓤 ̇ ) → ¬¬ (X + ¬ X)

DNE-gives-EM : dfunext 𝓤 𝓤₀ → DNE 𝓤 → EM 𝓤

EM-gives-DNE : EM 𝓤 → DNE 𝓤

SN : ∀ 𝓤 → 𝓤 ⁺ ̇
SN 𝓤 = (P : 𝓤 ̇ ) → is-subsingleton P → Σ X ꞉ 𝓤 ̇ , P ↔ ¬ X

SN-gives-DNE : SN 𝓤 → DNE 𝓤

DNE-gives-SN : DNE 𝓤 → SN 𝓤

succ-no-fixed-point : (n : ℕ) → succ n ≠ n
succ-no-fixed-point 0        = positive-not-zero 0
succ-no-fixed-point (succ n) = γ
 where
  IH : succ n ≠ n
  IH = succ-no-fixed-point n

  γ : succ (succ n) ≠ succ n
  γ p = IH (succ-lc p)

positive-cantors-diagonal = sol
 where
  sol : (e : ℕ → (ℕ → ℕ)) → Σ α ꞉ (ℕ → ℕ), ((n : ℕ) → α ≠ e n)
  sol e = (α , φ)
   where
    α : ℕ → ℕ
    α n = succ (e n n)

    φ : (n : ℕ) → α ≠ e n
    φ n p = succ-no-fixed-point (e n n) q
     where
      q = succ (e n n)  ＝⟨ refl (α n) ⟩
          α n           ＝⟨ ap (λ - → - n) p ⟩
          e n n         ∎

cantors-diagonal = sol
 where
  sol : ¬ (Σ e ꞉ (ℕ → (ℕ → ℕ)) , ((α : ℕ → ℕ) → Σ n ꞉ ℕ , α ＝ e n))
  sol (e , γ) = c
   where
    α : ℕ → ℕ
    α = pr₁ (positive-cantors-diagonal e)

    φ : (n : ℕ) → α ≠ e n
    φ = pr₂ (positive-cantors-diagonal e)

    b : Σ n ꞉ ℕ , α ＝ e n
    b = γ α

    c : 𝟘
    c = φ (pr₁ b) (pr₂ b)

𝟚-has-𝟚-automorphisms = sol
 where
  sol : dfunext 𝓤₀ 𝓤₀ → (𝟚 ≃ 𝟚) ≃ 𝟚
  sol fe = invertibility-gives-≃ f (g , η , ε)
   where
    f : (𝟚 ≃ 𝟚) → 𝟚
    f (h , e) = h ₀

    g : 𝟚 → (𝟚 ≃ 𝟚)
    g ₀ = id , id-is-equiv 𝟚
    g ₁ = swap₂ , swap₂-is-equiv

    η : (e : 𝟚 ≃ 𝟚) → g (f e) ＝ e
    η (h , e) = γ (h ₀) (h ₁) (refl (h ₀)) (refl (h ₁))
     where
      γ : (m n : 𝟚) → h ₀ ＝ m → h ₁ ＝ n → g (h ₀) ＝ (h , e)

      γ ₀ ₀ p q = !𝟘 (g (h ₀) ＝ (h , e))
                     (₁-is-not-₀ (equivs-are-lc h e (h ₁ ＝⟨ q ⟩
                                                     ₀   ＝⟨ p ⁻¹ ⟩
                                                     h ₀ ∎)))

      γ ₀ ₁ p q = to-subtype-＝
                     (being-equiv-is-subsingleton fe fe)
                     (fe (𝟚-induction (λ n → pr₁ (g (h ₀)) n ＝ h n)
                               (pr₁ (g (h ₀)) ₀ ＝⟨ ap (λ - → pr₁ (g -) ₀) p ⟩
                                pr₁ (g ₀) ₀     ＝⟨ refl ₀ ⟩
                                ₀               ＝⟨ p ⁻¹ ⟩
                                h ₀             ∎)
                               (pr₁ (g (h ₀)) ₁ ＝⟨ ap (λ - → pr₁ (g -) ₁) p ⟩
                                pr₁ (g ₀) ₁     ＝⟨ refl ₁ ⟩
                                ₁               ＝⟨ q ⁻¹ ⟩
                                h ₁             ∎)))

      γ ₁ ₀ p q = to-subtype-＝
                     (being-equiv-is-subsingleton fe fe)
                     (fe (𝟚-induction (λ n → pr₁ (g (h ₀)) n ＝ h n)
                               (pr₁ (g (h ₀)) ₀ ＝⟨ ap (λ - → pr₁ (g -) ₀) p ⟩
                                pr₁ (g ₁) ₀     ＝⟨ refl ₁ ⟩
                                ₁               ＝⟨ p ⁻¹ ⟩
                                h ₀             ∎)
                               (pr₁ (g (h ₀)) ₁ ＝⟨ ap (λ - → pr₁ (g -) ₁) p ⟩
                                pr₁ (g ₁) ₁     ＝⟨ refl ₀ ⟩
                                ₀               ＝⟨ q ⁻¹ ⟩
                                h ₁             ∎)))

      γ ₁ ₁ p q = !𝟘 (g (h ₀) ＝ (h , e))
                     (₁-is-not-₀ (equivs-are-lc h e (h ₁ ＝⟨ q ⟩
                                                     ₁   ＝⟨ p ⁻¹ ⟩
                                                     h ₀ ∎)))

    ε : (n : 𝟚) → f (g n) ＝ n
    ε ₀ = refl ₀
    ε ₁ = refl ₁

lifttwo = sol
 where
  sol : is-univalent 𝓤₀ → is-univalent 𝓤₁ → (𝟚 ＝ 𝟚) ＝ Lift 𝓤₁ 𝟚
  sol ua₀ ua₁ = Eq→Id ua₁ (𝟚 ＝ 𝟚) (Lift 𝓤₁ 𝟚) e
   where
    e = (𝟚 ＝ 𝟚)   ≃⟨ Id→Eq 𝟚 𝟚 , ua₀ 𝟚 𝟚 ⟩
        (𝟚 ≃ 𝟚)   ≃⟨ 𝟚-has-𝟚-automorphisms (univalence-gives-dfunext ua₀) ⟩
        𝟚         ≃⟨ ≃-sym (Lift-≃ 𝟚) ⟩
        Lift 𝓤₁ 𝟚 ■

hde-is-subsingleton : dfunext 𝓤 𝓤₀
                    → dfunext 𝓤 𝓤
                    → (X : 𝓤 ̇ )
                    → is-subsingleton (has-decidable-equality X)
hde-is-subsingleton fe₀ fe X h h' = c h h'
 where
  a : (x y : X) → is-subsingleton (decidable (x ＝ y))
  a x y = +-is-subsingleton' fe₀ b
   where
    b : is-subsingleton (x ＝ y)
    b = hedberg h x y

  c : is-subsingleton (has-decidable-equality X)
  c = Π-is-subsingleton fe (λ x → Π-is-subsingleton fe (a x))

ne = sol
 where
  sol : (X : 𝓤 ̇ ) → ¬¬ (X + ¬ X)
  sol X = λ (f : ¬ (X + ¬ X)) → f (inr (λ (x : X) → f (inl x)))

DNE-gives-EM = sol
 where
  sol : dfunext 𝓤 𝓤₀ → DNE 𝓤 → EM 𝓤
  sol fe dne P i = dne (P + ¬ P) (+-is-subsingleton' fe i) (ne P)

EM-gives-DNE = sol
 where
  sol : EM 𝓤 → DNE 𝓤
  sol em P i = γ (em P i)
   where
    γ : P + ¬ P → ¬¬ P → P
    γ (inl p) φ = p
    γ (inr n) φ = !𝟘 P (φ n)

SN-gives-DNE = sol
 where
  sol : SN 𝓤 → DNE 𝓤
  sol {𝓤} sn P i = h
   where
    X : 𝓤 ̇
    X = pr₁ (sn P i)

    f : P → ¬ X
    f = pr₁ (pr₂ (sn P i))

    g : ¬ X → P
    g = pr₂ (pr₂ (sn P i))

    f' : ¬¬ P → ¬ (¬¬ X)
    f' = contrapositive (contrapositive f)

    h : ¬¬ P → P
    h = g ∘ tno X ∘ f'

    h' : ¬¬ P → P
    h' φ = g (λ (x : X) → φ (λ (p : P) → f p x))

DNE-gives-SN = sol
 where
  sol : DNE 𝓤 → SN 𝓤
  sol dne P i = ¬ P , dni P , dne P i

\end{code}
