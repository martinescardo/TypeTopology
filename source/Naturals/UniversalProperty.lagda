Tom de Jong (adapted from Martin's MGS lecture notes)
18 September 2020

We show that the type of natural numbers enjoys the universal property of a
natural numbers object. We generalize
https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#ℕ-is-nno
here from nondependent functions to dependent functions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Naturals.UniversalProperty where


open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.Retracts
open import UF.Subsingletons

ℕ-induction-retract : funext 𝓤₀ 𝓤
                    → (Y : ℕ → 𝓤 ̇ ) (y₀ : Y 0) (g : (n : ℕ) → Y n → Y (succ n))
                    → (Σ h ꞉ (Π Y) , (h 0 ＝ y₀) ×
                                     ((n : ℕ) → h (succ n) ＝ g n (h n)))
                    ◁ (Σ h ꞉ (Π Y) , h ＝ ℕ-induction y₀ g)
ℕ-induction-retract fe Y y₀ g = Σ-retract _ _ γ
 where
  γ : (h : Π Y)
    → (h 0 ＝ y₀) × ((n : ℕ) → h (succ n) ＝ g n (h n))
    ◁ (h ＝ ℕ-induction y₀ g)
  γ h =  (h 0 ＝ y₀) × ((n : ℕ) → h (succ n) ＝ g n (h n)) ◁⟨ i  ⟩
         (h ∼ ℕ-induction y₀ g)                            ◁⟨ ii ⟩
         (h ＝ ℕ-induction y₀ g)                            ◀
   where
    ii = ≃-gives-◁ (≃-sym (≃-funext fe h (ℕ-induction y₀ g)))
    i  = r , s , η
     where
      r : h ∼ ℕ-induction y₀ g
        → (h 0 ＝ y₀) × ((n : ℕ) → h (succ n) ＝ g n (h n))
      r H = H 0 , (λ n → h (succ n)              ＝⟨ H (succ n)          ⟩
                         ℕ-induction y₀ g (succ n) ＝⟨ refl                ⟩
                         g n (ℕ-induction y₀ g n)  ＝⟨ ap (g n) ((H n) ⁻¹) ⟩
                         g n (h n)               ∎)
      s : (h 0 ＝ y₀) × ((n : ℕ) → h (succ n) ＝ g n (h n))
        → h ∼ ℕ-induction y₀ g
      s (p , K) 0 = p
      s (p , K) (succ n) = h (succ n)              ＝⟨ K n                    ⟩
                           g n (h n)               ＝⟨ ap (g n) (s (p , K) n) ⟩
                           g n (ℕ-induction y₀ g n)  ＝⟨ refl                   ⟩
                           ℕ-induction y₀ g (succ n) ∎
      η : r ∘ s ∼ id
      η (p , K) =
       r (s (p , K))                                      ＝⟨refl⟩
       (p , λ n → s (p , K) (succ n)
                  ∙ (refl ∙ ap (g n) ((s (p , K) n) ⁻¹))) ＝⟨ φ    ⟩
       (p , K)                                            ∎
         where
          φ = ap (p ,_) (dfunext fe ψ)
           where
            ψ : (n : ℕ)
              → s (p , K) (succ n) ∙ (refl ∙ ap (g n) (s (p , K) n ⁻¹))
              ＝ K n
            ψ n = s (p , K) (succ n)
                    ∙ (refl ∙ ap (g n) (s (p , K) n ⁻¹))   ＝⟨refl⟩
                  K n ∙ ap (g n) (s (p , K) n)
                    ∙ (refl ∙ ap (g n) ((s (p , K) n) ⁻¹)) ＝⟨ I    ⟩
                  K n ∙ ap (g n) (s (p , K) n)
                    ∙ ap (g n) ((s (p , K) n) ⁻¹)          ＝⟨ II   ⟩
                  K n ∙ (ap (g n) (s (p , K) n)
                    ∙ ap (g n) ((s (p , K) n) ⁻¹))         ＝⟨ III  ⟩
                  K n ∙ (ap (g n) (s (p , K) n)
                    ∙ (ap (g n) (s (p , K) n)) ⁻¹)         ＝⟨ IV   ⟩
                  K n ∙ refl                               ＝⟨refl⟩
                  K n                                      ∎
             where
              I   = ap (K n ∙ ap (g n) (s (p , K) n) ∙_)
                     (refl-left-neutral {_} {_} {_} {_}
                       {ap (g n) ((s (p , K) n) ⁻¹)})
              II  = ∙assoc
                     (K n)
                     (ap (g n) (s (p , K) n))
                     (ap (g n) ((s (p , K) n) ⁻¹))
              III = ap (λ - → K n ∙ (ap (g n) (s (p , K) n) ∙ -))
                     ((ap-sym (g n) (s (p , K) n)) ⁻¹)
              IV  = ap (K n ∙_)
                     ((right-inverse (ap (g n) (s (p , K) n))) ⁻¹)

ℕ-is-nno-dep : funext 𝓤₀ 𝓤
             → (Y : ℕ → 𝓤 ̇ ) (y₀ : Y 0) (g : (n : ℕ) → Y n → Y (succ n))
             → ∃! h ꞉ (Π Y) , ((h 0 ＝ y₀) × ((n : ℕ) → h (succ n) ＝ g n (h n)))
ℕ-is-nno-dep {𝓤} fe Y y₀ g = γ
 where
  γ : is-singleton
       (Σ h ꞉ (Π Y) , (h 0 ＝ y₀) × ((n : ℕ) → h (succ n) ＝ g n (h n)))
  γ = retract-of-singleton (ℕ-induction-retract fe Y y₀ g)
       (singleton-types'-are-singletons (ℕ-induction {𝓤} {Y} y₀ g))


\end{code}
