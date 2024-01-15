Martin Escardo 2012

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.MFPSAndVariations.Dialogue where

open import MLTT.Spartan
open import MLTT.Athenian
open import EffectfulForcing.MFPSAndVariations.Continuity

data D (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (Z : 𝓦 ̇ ) : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇  where
 η : Z → D X Y Z
 β : (Y → D X Y Z) → X → D X Y Z

dialogue : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
         → D X Y Z
         → (X → Y) → Z
dialogue (η z)   α = z
dialogue (β φ x) α = dialogue (φ(α x)) α

eloquent : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → ((X → Y) → Z) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
eloquent f = Σ d ꞉ D _ _ _ , dialogue d ∼ f

B : 𝓤 ̇  → 𝓤 ̇
B = D ℕ ℕ

dialogue-continuity : (d : B ℕ) → is-continuous (dialogue d)
dialogue-continuity (η n) α = ([] , lemma)
 where
  lemma : ∀ α' → α ＝⟪ [] ⟫ α' → n ＝ n
  lemma α' r = refl

dialogue-continuity (β φ i) α = ((i ∷ is) , lemma)
 where
  IH : (i : ℕ) → is-continuous (dialogue (φ (α i)))
  IH i = dialogue-continuity (φ (α i))

  is : List ℕ
  is = pr₁ (IH i α)

  lemma : (α' : Baire)
        → α ＝⟪ i ∷ is ⟫ α'
        → dialogue (φ (α i)) α ＝ dialogue (φ (α' i)) α'
  lemma α' (r ∷ rs) = dialogue (φ (α i)) α  ＝⟨ pr₂ (IH i α) α' rs ⟩
                      dialogue (φ (α i)) α' ＝⟨ ap (λ n → dialogue (φ n) α') r ⟩
                      dialogue (φ (α' i)) α' ∎

eloquent-functions-are-continuous : (f : Baire → ℕ)
                                  → eloquent f
                                  → is-continuous f
eloquent-functions-are-continuous f (d , e) =
 continuity-extensional (dialogue d) f e (dialogue-continuity d)

C : 𝓤 ̇ → 𝓤 ̇
C = D ℕ 𝟚

dialogue-UC : (d : C ℕ) → is-uniformly-continuous (dialogue d)
dialogue-UC (η n)   = ([] , λ α α' n → refl)
dialogue-UC (β φ i) = ((i ∷ s) , lemma)
 where
  IH : (j : 𝟚) → is-uniformly-continuous (dialogue(φ j))
  IH j = dialogue-UC (φ j)

  s : 𝟚 → BT ℕ
  s j = pr₁ (IH j)

  lemma : ∀ α α' → α ＝⟦ i ∷ s ⟧ α' → dialogue (φ (α i)) α ＝ dialogue (φ (α' i)) α'
  lemma α α' (r ∷ l) =
   dialogue (φ (α i)) α   ＝⟨ ap (λ j → dialogue (φ j) α) r ⟩
   dialogue (φ (α' i)) α  ＝⟨ pr₂ (IH (α' i)) α α' (l (α' i)) ⟩
   dialogue (φ (α' i)) α' ∎

eloquent-functions-are-UC : (f : Cantor → ℕ)
                          → eloquent f
                          → is-uniformly-continuous f
eloquent-functions-are-UC f (d , e) =
 UC-extensional (dialogue d) f e (dialogue-UC d)

prune : B ℕ → C ℕ
prune (η n)   = η n
prune (β φ i) = β (λ j → prune (φ (embedding-𝟚-ℕ j))) i

prune-behaviour : (d : B ℕ) (α : Cantor)
                → dialogue (prune d) α ＝ C-restriction (dialogue d) α
prune-behaviour (η n)   α = refl
prune-behaviour (β φ n) α = prune-behaviour (φ (embedding-𝟚-ℕ (α n))) α

restriction-is-eloquent : (f : Baire → ℕ)
                        → eloquent f
                        → eloquent (C-restriction f)
restriction-is-eloquent f (d , c) =
 (prune d ,
  (λ α → dialogue (prune d) α         ＝⟨ prune-behaviour d α ⟩
         C-restriction (dialogue d) α ＝⟨ c (embedding-C-B α) ⟩
         f (embedding-C-B α)          ∎))

\end{code}

B is a monad.

\begin{code}

kleisli-extension : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → B Y) → B X → B Y
kleisli-extension f (η x)   = f x
kleisli-extension f (β φ i) = β (λ j → kleisli-extension f (φ j)) i

B-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → B X → B Y
B-functor f = kleisli-extension (η ∘ f)

decode : {X : 𝓤 ̇ } → Baire → B X → X
decode α d = dialogue d α

decode-α-is-natural : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (g : X → Y) (d : B X) (α : Baire)
                    → g (decode α d) ＝ decode α (B-functor g d)
decode-α-is-natural g (η x)   α = refl
decode-α-is-natural g (β φ i) α = decode-α-is-natural g (φ(α i)) α

decode-kleisli-extension : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → B Y) (d : B X) (α : Baire)
                         → decode α (f (decode α d))
                         ＝ decode α (kleisli-extension f d)
decode-kleisli-extension f (η x)   α = refl
decode-kleisli-extension f (β φ i) α = decode-kleisli-extension f (φ(α i)) α

\end{code}

The generic element.

\begin{code}

generic : B ℕ → B ℕ
generic = kleisli-extension (β η)

generic-diagram : (α : Baire) (d : B ℕ)
                → α (decode α d) ＝ decode α (generic d)
generic-diagram α (η n)   = refl
generic-diagram α (β φ n) = generic-diagram α (φ (α n))

\end{code}
