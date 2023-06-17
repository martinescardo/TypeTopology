Martin Escardo, Paulo Oliva, 9-17 June 2023

We relate our game trees to Aczel's W type of CZF sets in various ways.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.PropTrunc
open import UF.Univalence

module Games.Discussion
        (pt  : propositional-truncations-exist)
        (ua : Univalence)
       where

open import Games.TypeTrees
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.PropIndexedPiSigma
open import UF.Subsingletons
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

fe : Fun-Ext
fe = Univalence-gives-Fun-Ext ua


open PropositionalTruncation pt

is-hereditarily-inhabited : 𝕋 → Type
is-hereditarily-inhabited []       = 𝟙
is-hereditarily-inhabited (X ∷ Xf) =
 ∥ X ∥ × ((x : X) → is-hereditarily-inhabited (Xf x))

being-hereditarily-inhabited-is-prop : (Xt : 𝕋)
                                     → is-prop (is-hereditarily-inhabited Xt)
being-hereditarily-inhabited-is-prop []       = 𝟙-is-prop
being-hereditarily-inhabited-is-prop (X ∷ Xf) =
 ×-is-prop
  ∥∥-is-prop
  (Π-is-prop fe (λ x → being-hereditarily-inhabited-is-prop (Xf x)))

is-[]-free : 𝕋 → Type
is-[]-free []       = 𝟘
is-[]-free (X ∷ Xf) = (x : X) → is-[]-free (Xf x)

being-[]-free-is-prop : (t : 𝕋) → is-prop (is-[]-free t)
being-[]-free-is-prop [] = 𝟘-is-prop
being-[]-free-is-prop (X ∷ Xf) = Π-is-prop fe (λ x → being-[]-free-is-prop (Xf x))

[]-free-trees-have-no-paths : (Xt : 𝕋) → is-[]-free Xt → is-empty (Path Xt)
[]-free-trees-have-no-paths []       p ⟨⟩        = p
[]-free-trees-have-no-paths (X ∷ Xf) p (x :: xs) = []-free-trees-have-no-paths (Xf x) (p x) xs

data 𝔸 : Type₁ where
  _∷_ : (X : Type) (Xf : X → 𝔸) → 𝔸

𝔽 = Σ t ꞉ 𝕋 , is-[]-free t

af : 𝔸 ≃ 𝔽
af = qinveq f (g , gf , fg)
 where
  f : 𝔸 → 𝔽
  f (X ∷ Xf) = (X ∷ (pr₁ ∘ f ∘ Xf)) , pr₂ ∘ f ∘ Xf

  g : 𝔽 → 𝔸
  g ((X ∷ Xf) , φ) = X ∷ (λ x → g (Xf x , φ x))

  fg' : (Xt : 𝕋) (φ : is-[]-free Xt) → f (g (Xt , φ)) ＝ (Xt , φ)
  fg' (X ∷ Xf) φ =
   (f ∘ g) ((X ∷ Xf) , φ)    ＝⟨ refl ⟩
   (X ∷ (pr₁ ∘ h)) , pr₂ ∘ h ＝⟨ I ⟩
   (X ∷ Xf) , φ              ∎
    where
     h : X → 𝔽
     h x = f (g (Xf x , φ x))

     IH : (x : X) → h x ＝ (Xf x , φ x)
     IH x = fg' (Xf x) (φ x)

     I = ap (λ - → (X ∷ (pr₁ ∘ -)) , pr₂ ∘ -) (dfunext fe IH)

  fg : f ∘ g ∼ id
  fg (Xt , φ) = fg' Xt φ

  gf : g ∘ f ∼ id
  gf (X ∷ Xf) = ap (X ∷_) (dfunext fe (λ x → gf (Xf x)))

prune : 𝕋 → 𝕋
prune [] = []
prune (X ∷ Xf) = (Σ x ꞉ X , ∥ Path (Xf x) ∥)
               ∷ (λ (x , _) → prune (Xf x))

prune-path : (Xt : 𝕋) → Path Xt ≃ Path (prune Xt)
prune-path Xt = qinveq (f Xt) (g Xt , gf Xt , fg Xt)
 where
  f : (Xt : 𝕋) → Path Xt → Path (prune Xt)
  f []       ⟨⟩        = ⟨⟩
  f (X ∷ Xf) (x :: xs) = (x , ∣ xs ∣) :: f (Xf x) xs

  g : (Xt : 𝕋) → Path (prune Xt) → Path Xt
  g []       ⟨⟩              = ⟨⟩
  g (X ∷ Xf) ((x , p) :: xs) = x :: g (Xf x) xs

  gf : (Xt : 𝕋) → g Xt ∘ f Xt ∼ id
  gf []       ⟨⟩        = refl
  gf (X ∷ Xf) (x :: xs) = ap (x ::_) (gf (Xf x) xs)

  fg : (Xt : 𝕋) → f Xt ∘ g Xt ∼ id
  fg []       ⟨⟩              = refl
  fg (X ∷ Xf) ((x , p) :: xs) =
   (f (X ∷ Xf) ∘ g (X ∷ Xf)) ((x :: p) :: xs)        ＝⟨ refl ⟩
   ((x :: ∣ g (Xf x) xs ∣) :: f (Xf x) (g (Xf x) xs)) ＝⟨ I ⟩
   ((x :: p) :: f (Xf x) (g (Xf x) xs))              ＝⟨ II ⟩
   (x :: p) :: xs                                    ∎
    where
     I = ap (λ - →  ((x :: -) :: f (Xf x) (g (Xf x) xs)))
            (∥∥-is-prop ∣ g (Xf x) xs ∣ p)
     II = ap ((x :: p) ::_)
             (fg (Xf x) xs)

prune-is-hereditarily-inhabited : (Xt : 𝕋)
                                → ∥ Path Xt ∥
                                → is-hereditarily-inhabited (prune Xt)
prune-is-hereditarily-inhabited []       _ = ⋆
prune-is-hereditarily-inhabited (X ∷ Xf) p = γ , ϕ
 where
  γ : ∥(Σ x ꞉ X , ∥ Path (Xf x) ∥)∥
  γ = ∥∥-functor (λ (x :: xs) → x :: ∣ xs ∣) p

  ϕ : ((x , p) : (Σ x ꞉ X , ∥ Path (Xf x) ∥))
    → is-hereditarily-inhabited (prune (Xf x))
  ϕ (x , p) = prune-is-hereditarily-inhabited (Xf x) p

has-at-least-one-[] : 𝕋 → Type
has-at-least-one-[] []       = 𝟙
has-at-least-one-[] (X ∷ Xf) = ∃ x ꞉ X , has-at-least-one-[] (Xf x)

having-at-least-one-[]-is-prop : (t : 𝕋) → is-prop (has-at-least-one-[] t)
having-at-least-one-[]-is-prop []       = 𝟙-is-prop
having-at-least-one-[]-is-prop (X ∷ Xf) = ∃-is-prop

path-gives-at-least-one-[] : (Xt : 𝕋) → ∥ Path Xt ∥ → has-at-least-one-[] Xt
path-gives-at-least-one-[] []       s = ⟨⟩
path-gives-at-least-one-[] (X ∷ Xf) s = γ
 where
  IH : (x : X) → ∥ Path (Xf x) ∥ → has-at-least-one-[] (Xf x)
  IH x = path-gives-at-least-one-[] (Xf x)

  γ : ∃ x ꞉ X , has-at-least-one-[] (Xf x)
  γ = ∥∥-functor (λ (x , xs) → x , IH x ∣ xs ∣) s

at-least-one-[]-gives-path : (Xt : 𝕋) → has-at-least-one-[] Xt → ∥ Path Xt ∥
at-least-one-[]-gives-path []       h = ∣ ⟨⟩ ∣
at-least-one-[]-gives-path (X ∷ Xf) h = γ
 where
  IH : (x : X) → has-at-least-one-[] (Xf x) → ∥ Path (Xf x) ∥
  IH x = at-least-one-[]-gives-path (Xf x)

  γ : ∃ x ꞉ X , Path (Xf x)
  γ = ∥∥-rec ∃-is-prop (λ (x , g) → remove-truncation-inside-∃ ∣ x , IH x g ∣) h

[]ᴬ : 𝔸
[]ᴬ = 𝟘 ∷ 𝟘-elim

to-𝔸-＝ : {X Y : Type}
          (Xf : X → 𝔸) (Yf : Y → 𝔸)
          (p : X ＝ Y)
        → Xf ＝ Yf ∘ idtofun X Y p
        → (X ∷ Xf) ＝[ 𝔸 ] (Y ∷ Yf)
to-𝔸-＝ Xf Xf refl refl = refl

[]ᴬ-＝ : {X : Type} (Xf : X → 𝔸) → is-empty X → []ᴬ ＝ (X ∷ Xf)
[]ᴬ-＝ {X} Xf e =
   []ᴬ        ＝⟨ refl ⟩
   𝟘 ∷ 𝟘-elim ＝⟨ to-𝔸-＝ 𝟘-elim Xf I II ⟩
   (X ∷ Xf)    ∎
   where
    I : 𝟘 ＝ X
    I = eqtoid (ua 𝓤₀) 𝟘 X (≃-sym (empty-≃-𝟘 e))

    II : 𝟘-elim ＝ Xf ∘ idtofun 𝟘 X I
    II = dfunext fe (λ (x : 𝟘) → 𝟘-elim x)

[]-property : (Xt : 𝕋) → is-[]-free Xt → ¬ has-at-least-one-[] Xt
[]-property (X ∷ Xf) f h = ∥∥-rec 𝟘-is-prop (λ (x , g) → IH x (f x) g) h
 where
  IH : (x : X) → is-[]-free (Xf x) → ¬ has-at-least-one-[] (Xf x)
  IH x = []-property (Xf x)

[]-property₂ : (Xt : 𝕋) → is-[]-free Xt → ¬ ∥ Path Xt ∥
[]-property₂ Xt f = contrapositive (path-gives-at-least-one-[] Xt) ([]-property Xt f)

is-hereditarily-decidable : 𝔸 → Type
is-hereditarily-decidable (X ∷ Xf) = (is-decidable ∥ X ∥)
                                   × ((x : X) → is-hereditarily-decidable (Xf x))

being-hereditarily-decidable-is-prop : (a : 𝔸) → is-prop (is-hereditarily-decidable a)
being-hereditarily-decidable-is-prop (X ∷ Xf) =
 ×-is-prop
  (+-is-prop ∥∥-is-prop (negations-are-props fe) ¬¬-intro)
  (Π-is-prop fe (λ x → being-hereditarily-decidable-is-prop (Xf x)))

𝔾 = Σ t ꞉ 𝕋 , is-hereditarily-inhabited t -- Good game trees.
ℍ = Σ a ꞉ 𝔸 , is-hereditarily-decidable a -- An isomorphic copy.

[]ᴬ-is-hd : is-hereditarily-decidable []ᴬ
[]ᴬ-is-hd = inr (∥∥-rec 𝟘-is-prop id) , (λ x → 𝟘-elim x)

[]ᴴ : ℍ
[]ᴴ = []ᴬ , []ᴬ-is-hd

hg : ℍ ≃ 𝔾
hg = qinveq f (g , gf , fg)
 where
  f' : (a : 𝔸) → is-hereditarily-decidable a → 𝔾
  f' (X ∷ Xf) (inl s , k) = (X ∷ (pr₁ ∘ φ)) , s , pr₂ ∘ φ
   where
    φ : X → 𝔾
    φ x = f' (Xf x) (k x)

  f' (X ∷ Xf) (inr _ , _) = [] , ⟨⟩

  f : ℍ → 𝔾
  f = uncurry f'

  g' : (t : 𝕋) → is-hereditarily-inhabited t → ℍ
  g' []       _       = []ᴴ
  g' (X ∷ Xf) (s , k) = (X ∷ (pr₁ ∘ γ)) , inl s , pr₂ ∘ γ
   where
    γ : X → ℍ
    γ x = g' (Xf x) (k x)

  g : 𝔾 → ℍ
  g = uncurry g'

  fg' : (Xt : 𝕋) (i : is-hereditarily-inhabited Xt)
      → f (g (Xt , i)) ＝ (Xt , i)
  fg' []       ⟨⟩      = refl
  fg' (X ∷ Xf) (s , k) =
   f (g ((X ∷ Xf) , (s , k)))    ＝⟨ refl ⟩
   (X ∷ (pr₁ ∘ h)) , s , pr₂ ∘ h ＝⟨ I ⟩
   ((X ∷ Xf) , s , k)            ∎
    where
     h : X → 𝔾
     h x = f (g (Xf x , k x))

     IH : (x : X) → h x ＝ (Xf x , k x)
     IH x = fg' (Xf x) (k x)

     I = ap (λ - → (X ∷ (pr₁ ∘ -)) , s , pr₂ ∘ -)
            (dfunext fe IH)

  fg : f ∘ g ∼ id
  fg (Xt , i) = fg' Xt i

  gf' : (a : 𝔸) (d : is-hereditarily-decidable a)
      → g (f (a , d)) ＝ (a , d)
  gf' (X ∷ Xf) (inl s , k) =
   g (f ((X ∷ Xf) , inl s , k))      ＝⟨ refl ⟩
   (X ∷ (pr₁ ∘ h)) , inl s , pr₂ ∘ h ＝⟨ I ⟩
   (X ∷ Xf) , inl s , k              ∎
   where
    h : X → ℍ
    h x = g (f (Xf x , k x))

    IH : (x : X) → h x ＝ (Xf x , k x)
    IH x = gf' (Xf x) (k x)

    I = ap (λ - → (X ∷ (pr₁ ∘ -)) , inl s , pr₂ ∘ -)
           (dfunext fe IH)

  gf' (X ∷ Xf) (inr n , k) =
   g (f ((X ∷ Xf) , inr n , k)) ＝⟨ refl ⟩
   []ᴬ , []ᴬ-is-hd              ＝⟨ I ⟩
   (X ∷ Xf) , inr n , k         ∎
    where
     I = to-subtype-＝
          being-hereditarily-decidable-is-prop
          ([]ᴬ-＝ Xf (λ x → n ∣ x ∣))

  gf : g ∘ f ∼ id
  gf (Xt , i) = gf' Xt i

𝔸-Path : 𝔸 → Type
𝔸-Path (X ∷ Xf) = is-empty X + (Σ x ꞉ X , 𝔸-Path (Xf x))

ℍ-Path : ℍ → Type
ℍ-Path (a , _) = 𝔸-Path a

𝔾-Path : 𝔾 → Type
𝔾-Path (Xt , _) = Path Xt

hg-path : (h : ℍ) → ℍ-Path h ≃ 𝔾-Path (⌜ hg ⌝ h)
hg-path (a , d) = γ a d
 where
  γ : (a : 𝔸) (i : is-hereditarily-decidable a)
    → 𝔸-Path a ≃ 𝔾-Path (⌜ hg ⌝ (a , i))
  γ (X ∷ Xf) (inl s , k) =
   𝔸-Path (X ∷ Xf)                              ≃⟨ ≃-refl _ ⟩
   is-empty X + (Σ x ꞉ X , 𝔸-Path (Xf x))       ≃⟨ I ⟩
   𝟘 + (Σ x ꞉ X , 𝔸-Path (Xf x))               ≃⟨ 𝟘-lneutral {𝓤₀} {𝓤₀} ⟩
   (Σ x ꞉ X , 𝔸-Path (Xf x))                    ≃⟨ Σ-cong IH ⟩
   (Σ x ꞉ X , Path (pr₁ (⌜ hg ⌝ (Xf x , k x)))) ≃⟨ ≃-refl _ ⟩
   𝔾-Path (⌜ hg ⌝ ((X ∷ Xf) , inl s , k))       ■
   where
    IH : (x : X) → 𝔸-Path (Xf x) ≃ Path (pr₁ (⌜ hg ⌝ (Xf x , k x)))
    IH x = γ (Xf x) (k x)

    I = +-cong
        (empty-≃-𝟘 (λ e → ∥∥-rec 𝟘-is-prop e s))
        (≃-refl _)

  γ (X ∷ Xf) (inr n , i) =
   𝔸-Path (X ∷ Xf)                        ≃⟨ ≃-refl _ ⟩
   is-empty X + (Σ x ꞉ X , 𝔸-Path (Xf x)) ≃⟨ I ⟩
   𝟙 + 𝟘                                  ≃⟨ 𝟘-rneutral' {𝓤₀} {𝓤₀}⟩
   𝟙                                      ≃⟨ ≃-refl _ ⟩
   Path []                                ■
    where
     I = +-cong
          (prop-indexed-product-one fe (λ x → n ∣ x ∣))
          (prop-indexed-sum-zero (λ x → n ∣ x ∣))

gh-path : (g : 𝔾) → 𝔾-Path g ≃ ℍ-Path (⌜ hg ⌝⁻¹ g)
gh-path g = ≃-sym I
 where
  I = ℍ-Path (⌜ hg ⌝⁻¹ g)          ≃⟨ hg-path (⌜ hg ⌝⁻¹ g) ⟩
      𝔾-Path (⌜ hg ⌝ (⌜ hg ⌝⁻¹ g)) ≃⟨ II ⟩
      𝔾-Path g                     ■
        where
         II = idtoeq _ _
               (ap 𝔾-Path
                   (inverses-are-sections ⌜ hg ⌝ ⌜ hg ⌝-is-equiv g))

\end{code}
