Martin Escardo 2012.

Published at https://doi.org/10.1016/j.entcs.2013.09.010 (MFPS XXIX)
with full, selfcontained Agda code.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.MFPSAndVariations.MFPS-XXIX where

open import MLTT.Spartan
open import MLTT.Athenian
open import UF.Base
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Continuity
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.CombinatoryT

\end{code}

The "effectful forcing" dialogue semantics of combinatory System T.

\begin{code}

B-Set⟦_⟧ : type → 𝓤₀ ̇
B-Set⟦ ι ⟧     = B ℕ
B-Set⟦ σ ⇒ τ ⟧ = B-Set⟦ σ ⟧ → B-Set⟦ τ ⟧

Kleisli-extension : {X : 𝓤₀ ̇ } {σ : type} → (X → B-Set⟦ σ ⟧) → B X → B-Set⟦ σ ⟧
Kleisli-extension {X} {ι}     = kleisli-extension
Kleisli-extension {X} {σ ⇒ τ} = λ g d s → Kleisli-extension {X} {τ} (λ x → g x s) d

zero' : B ℕ
zero' = η zero

succ' : B ℕ → B ℕ
succ' = B-functor succ

iter' : {σ : type} → (B-Set⟦ σ ⟧ → B-Set⟦ σ ⟧) → B-Set⟦ σ ⟧ → B ℕ → B-Set⟦ σ ⟧
iter' f x = Kleisli-extension (iter f x)

B⟦_⟧ : {σ : type} → TΩ σ → B-Set⟦ σ ⟧
B⟦ Ω ⟧     = generic
B⟦ Zero ⟧  = zero'
B⟦ Succ ⟧  = succ'
B⟦ Iter ⟧  = iter'
B⟦ K ⟧     = Ķ
B⟦ S ⟧     = Ş
B⟦ t · u ⟧ = B⟦ t ⟧ B⟦ u ⟧

\end{code}

The dialogue tree of a term of type (ι ⇒ ι) ⇒ ι.

\begin{code}

dialogue-tree : T ((ι ⇒ ι) ⇒ ι) → B ℕ
dialogue-tree t = B⟦ embedding t · Ω ⟧

\end{code}

A logical relation used to prove the desired property of the dialogue
tree:

\begin{code}

R : {σ : type} → (Baire → Set⟦ σ ⟧) → B-Set⟦ σ ⟧ → 𝓤₀ ̇
R {ι}     n n' = (α : Baire) → n α ＝ decode α n'
R {σ ⇒ τ} f f' = (x : Baire → Set⟦ σ ⟧)(x' : B-Set⟦ σ ⟧)
               → R {σ} x x'
               → R {τ} (λ α → f α (x α)) (f' x')

R-kleisli-lemma : (σ : type)
                  (g  : ℕ → Baire → Set⟦ σ ⟧)
                  (g' : ℕ → B-Set⟦ σ ⟧)
                → ((k : ℕ) → R (g k) (g' k))
                → (n  : Baire → ℕ)
                  (n' : B ℕ)
                → R n n'
                → R (λ α → g (n α) α) (Kleisli-extension g' n')

R-kleisli-lemma ι g g' rg n n' rn α =
 g (n α) α                          ＝⟨ rg (n α) α ⟩
 decode α (g' (n α))                ＝⟨ ap (λ - → decode α (g' -)) (rn α) ⟩
 decode α (g' (decode α n'))        ＝⟨ decode-kleisli-extension g' n' α ⟩
 decode α (Kleisli-extension g' n') ∎

R-kleisli-lemma (σ ⇒ τ) g g' rg n n' rn
 = λ y y' ry → R-kleisli-lemma
                τ
                (λ k α → g k α (y α))
                (λ k → g' k y')
                (λ k → rg k y y' ry)
                n
                n'
                rn

main-lemma : {σ : type} (t : TΩ σ)
           → R ⟦ t ⟧' B⟦ t ⟧

main-lemma Ω n n' rn α =
 α (n α)               ＝⟨ ap α (rn α) ⟩
 α (decode α n')       ＝⟨ generic-diagram α n' ⟩
 decode α (generic n') ∎

main-lemma Zero = λ α → refl

main-lemma Succ n n' rn α =
 succ (n α)            ＝⟨ ap succ (rn α) ⟩
 succ (decode α n')    ＝⟨ decode-α-is-natural succ n' α ⟩
 dialogue (succ' n') α ∎

main-lemma {(σ ⇒ .σ) ⇒ .σ ⇒ ι ⇒ .σ} Iter = lemma
 where
  lemma : (f  : Baire → Set⟦ σ ⟧ → Set⟦ σ ⟧)
          (f' : B-Set⟦ σ ⟧ → B-Set⟦ σ ⟧)
        → R {σ ⇒ σ} f f'
        → (x : Baire → Set⟦ σ ⟧)
          (x' : B-Set⟦ σ ⟧)
        → R {σ} x x'
        → (n : Baire → ℕ)
          (n' : B ℕ)
        → R {ι} n n'
        → R {σ} (λ α → iter (f α) (x α) (n α)) (Kleisli-extension (iter f' x') n')
  lemma f f' rf x x' rx = R-kleisli-lemma σ g g' rg
    where
     g : ℕ → Baire → Set⟦ σ ⟧
     g k α = iter (f α) (x α) k

     g' : ℕ → B-Set⟦ σ ⟧
     g' k = iter f' x' k

     rg : (k : ℕ) → R (g k) (g' k)
     rg zero     = rx
     rg (succ k) = rf (g k) (g' k) (rg k)

main-lemma K = λ x x' rx y y' ry → rx

main-lemma S = λ f f' rf g g' rg x x' rx
                 → rf x x' rx (λ α → g α (x α)) (g' x') (rg x x' rx)

main-lemma (t · u) = main-lemma t ⟦ u ⟧' B⟦ u ⟧ (main-lemma u)

dialogue-tree-correct : (t : T ((ι ⇒ ι) ⇒ ι)) (α : Baire)
                      → ⟦ t ⟧ α ＝ decode α (dialogue-tree t)
dialogue-tree-correct t α =
    ⟦ t ⟧ α                    ＝⟨ ap (λ g → g α) (preservation t α) ⟩
    ⟦ embedding t ⟧' α α       ＝⟨ main-lemma (embedding t · Ω) α ⟩
    decode α (dialogue-tree t) ∎

eloquence-theorem : (f : Baire → ℕ) → is-T-definable f → eloquent f
eloquence-theorem f (t , r) =
 (dialogue-tree t ,
  (λ α → dialogue (dialogue-tree t) α ＝⟨ (dialogue-tree-correct t α)⁻¹ ⟩
         ⟦ t ⟧ α                      ＝⟨ ap ((λ - → - α)) r ⟩
         f α                          ∎))

eloquence-corollary₀ : (f : Baire → ℕ)
                     → is-T-definable f
                     → is-continuous f
eloquence-corollary₀ f d = eloquent-functions-are-continuous
                            f
                            (eloquence-theorem f d)

eloquence-corollary₁ : (f : Baire → ℕ)
                     → is-T-definable f
                     → is-uniformly-continuous (C-restriction f)
eloquence-corollary₁ f d = eloquent-functions-are-UC
                            (C-restriction f)
                            (restriction-is-eloquent f (eloquence-theorem f d))

\end{code}

This concludes the development. Some examples follow.

\begin{code}

module examples where

 mod-cont : T ((ι ⇒ ι) ⇒ ι) → Baire → List ℕ
 mod-cont t α = pr₁ (eloquence-corollary₀ ⟦ t ⟧ (t , refl) α)

 mod-cont-obs : (t : T ((ι ⇒ ι) ⇒ ι)) (α : Baire)
              → mod-cont t α ＝ pr₁ (dialogue-continuity (dialogue-tree t) α)
 mod-cont-obs t α = refl

 flatten : {X : 𝓤₀ ̇ } → BT X → List X
 flatten [] = []
 flatten (x ∷ t) = x ∷ flatten(t ₀) ++ flatten(t ₁)

 mod-unif : T ((ι ⇒ ι) ⇒ ι) → List ℕ
 mod-unif t = flatten (pr₁ (eloquence-corollary₁ ⟦ t ⟧ (t , refl)))

 I : {σ : type} → T (σ ⇒ σ)
 I {σ} = S · K · (K {σ} {σ})

 I-behaviour : {σ : type}{x : Set⟦ σ ⟧} → ⟦ I ⟧ x ＝ x
 I-behaviour = refl

 numeral : ℕ → T ι
 numeral zero     = Zero
 numeral (succ n) = Succ · (numeral n)

 t₀ : T ((ι ⇒ ι) ⇒ ι)
 t₀ = K · (numeral 17)

 t₀-interpretation : ⟦ t₀ ⟧ ＝ λ α → 17
 t₀-interpretation = refl

 example₀ : mod-cont t₀ (λ i → i) ＝ []
 example₀ = refl

 example₀' : mod-unif t₀ ＝ []
 example₀' = refl

 v : {γ : type} → T (γ ⇒ γ)
 v = I

 infixl 1 _•_

 _•_ : {γ σ τ : type} → T (γ ⇒ σ ⇒ τ) → T (γ ⇒ σ) → T (γ ⇒ τ)
 f • x = S · f · x

 Numeral : ∀ {γ} → ℕ → T (γ ⇒ ι)
 Numeral n = K · (numeral n)

 t₁ : T ((ι ⇒ ι) ⇒ ι)
 t₁ = v • (Numeral 17)

 t₁-interpretation : ⟦ t₁ ⟧ ＝ λ α → α 17
 t₁-interpretation = refl

 example₁ : mod-unif t₁ ＝ 17 ∷ []
 example₁ = refl

 t₂ : T ((ι ⇒ ι) ⇒ ι)
 t₂ = Iter • t₁ • t₁

 t₂-interpretation : ⟦ t₂ ⟧ ＝ λ α → iter α (α 17) (α 17)
 t₂-interpretation = refl

 example₂ : mod-unif t₂ ＝ 17 ∷ 17 ∷ 17 ∷ 0 ∷ 1 ∷ []
 example₂ = refl

 example₂' : mod-cont t₂ (λ i → i)
           ＝ 17 ∷ 17 ∷ 17 ∷ 17 ∷ 17 ∷ 17 ∷ 17 ∷ 17 ∷ 17
             ∷ 17 ∷ 17 ∷ 17 ∷ 17 ∷ 17 ∷ 17 ∷ 17 ∷ 17 ∷ 17 ∷ 17 ∷ []
 example₂' = refl

 Add : T (ι ⇒ ι ⇒ ι)
 Add = Iter · Succ

 infixl 0 _+ᵀ_

 _+ᵀ_ : ∀ {γ} → T (γ ⇒ ι) → T (γ ⇒ ι) → T (γ ⇒ ι)
 x +ᵀ y = K · Add • x • y

 t₃ : T ((ι ⇒ ι) ⇒ ι)
 t₃ = Iter • (v • Numeral 1) • (v • Numeral 2 +ᵀ v • Numeral 3)

 t₃-interpretation : ⟦ t₃ ⟧ ＝ λ α → iter α (α 1) (iter succ (α 2) (α 3))
 t₃-interpretation = refl

 example₃ : mod-cont t₃ succ
          ＝ 3 ∷ 2 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ []
 example₃ = refl

 example₃' : mod-unif t₃
           ＝ 3 ∷ 2 ∷ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 2 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 1 ∷ []
 example₃' = refl

 max : ℕ → ℕ → ℕ
 max 0        y        = y
 max (succ x) 0        = succ x
 max (succ x) (succ y) = succ (max x y)

 Max : List ℕ → ℕ
 Max []      = 0
 Max (x ∷ s) = max x (Max s)

 t₄ : T ((ι ⇒ ι) ⇒ ι)
 t₄ = Iter • ((v • (v • Numeral 2)) +ᵀ (v • Numeral 3)) • t₃

 t₄-interpretation : ⟦ t₄ ⟧
                   ＝ λ α → iter
                             α
                             (iter succ (α (α 2)) (α 3))
                             (iter α (α 1) (iter succ (α 2) (α 3)))
 t₄-interpretation = refl

 example₄ : length (mod-unif t₄) ＝ 215
 example₄ = refl

 example₄' : Max (mod-unif t₄) ＝ 3
 example₄' = refl

 t₅ : T ((ι ⇒ ι) ⇒ ι)
 t₅ = Iter • (v • (v • t₂ +ᵀ t₄)) • (v • Numeral 2)

 t₅-explicitly : t₅ ＝
  (S · (S · Iter · (S · I · (S · (S · (K · (Iter · Succ))
  · (S · I · (S · (S · Iter · (S · I · (K · (numeral 17))))
  · (S · I · (K · (numeral 17)))))) · (S · (S · Iter · (S · (S
  · (K · (Iter · Succ)) · (S · I · (S · I · (K · (numeral 2)))))
  · (S · I · (K · (numeral 3))))) · (S · (S · Iter · (S · I
  · (K · (numeral 1)))) · (S · (S · (K · (Iter · Succ))
  · (S · I · (K · (numeral 2)))) · (S · I · (K
  · (numeral 3))))))))) · (S · I · (K · (numeral 2))))

 t₅-explicitly = refl

 t₅-interpretation : ⟦ t₅ ⟧
                   ＝ λ α → iter
                             α
                             (α (iter
                                  succ
                                  (α (iter α (α 17) (α 17)))
                                  (iter
                                    α
                                    (iter succ (α (α 2)) (α 3))
                                    (iter α (α 1) (iter succ (α 2) (α 3))))))
                             (α 2)
 t₅-interpretation = refl

 example₅ : length (mod-unif t₅) ＝ 15551
 example₅ = refl

 example₅' : Max (mod-unif t₅) ＝ 17
 example₅' = refl

 example₅'' : Max (mod-cont t₅ succ) ＝ 57
 example₅'' = refl

\end{code}
