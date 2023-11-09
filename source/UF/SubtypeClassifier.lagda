Martin Escardo

The type of truth values and its basic notions and properties. More
notions and properties are in UF.SubtypeClassifier-Properties.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.SubtypeClassifier where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

Ω : ∀ 𝓤 → 𝓤 ⁺ ̇
Ω 𝓤 = Σ P ꞉ 𝓤 ̇ , is-prop P

Ω₀ = Ω 𝓤₀

_holds : Ω 𝓤 → 𝓤 ̇
(P , i) holds = P

holds-is-prop : (p : Ω 𝓤) → is-prop (p holds)
holds-is-prop (P , i) = i

to-Ω-＝ : funext 𝓤 𝓤
        → {P Q : 𝓤 ̇ }
          {i : is-prop P} {j : is-prop Q}
        → P ＝ Q
        → (P , i) ＝[ Ω 𝓤 ] (Q , j)
to-Ω-＝ fe = to-subtype-＝ (λ _ → being-prop-is-prop fe)

from-Ω-＝ : {P Q : 𝓤 ̇ }
            {i : is-prop P} {j : is-prop Q}
          → (P , i) ＝[ Ω 𝓤 ] (Q , j)
          → P ＝ Q
from-Ω-＝ = ap _holds

⊥ ⊤ : Ω 𝓤
⊥ = 𝟘 , 𝟘-is-prop   -- false
⊤ = 𝟙 , 𝟙-is-prop   -- true

⊥-doesnt-hold : ¬ (⊥ {𝓤} holds)
⊥-doesnt-hold = 𝟘-elim

⊤-holds : ⊤ {𝓤} holds
⊤-holds = ⋆

⊥-is-not-⊤ : ⊥ {𝓤} ≠ ⊤ {𝓤}
⊥-is-not-⊤ b = 𝟘-elim (𝟘-is-not-𝟙 (ap _holds b))

not : funext 𝓤 𝓤₀ → Ω 𝓤 → Ω 𝓤
not fe (P , i) = (¬ P , negations-are-props fe)

true-gives-equal-⊤ : propext 𝓤
                   → funext 𝓤 𝓤
                   → (P : 𝓤 ̇ ) (i : is-prop P)
                   → P → (P , i) ＝ ⊤
true-gives-equal-⊤ pe fe P i p = to-Σ-＝ (holds-gives-equal-𝟙 pe P i p ,
                                 being-prop-is-prop fe _ _)

holds-gives-equal-⊤ : propext 𝓤 → funext 𝓤 𝓤 → (p : Ω 𝓤) → p holds → p ＝ ⊤
holds-gives-equal-⊤ pe fe (P , i) = true-gives-equal-⊤ pe fe P i

equal-⊤-gives-holds : (p : Ω 𝓤) → p ＝ ⊤ → p holds
equal-⊤-gives-holds .⊤ refl = ⋆

equal-⊥-gives-not-equal-⊤ : (fe : Fun-Ext)
                            (pe : propext 𝓤)
                            (p : Ω 𝓤)
                          → p ＝ ⊥
                          → not fe p ＝ ⊤
equal-⊥-gives-not-equal-⊤ fe pe p r = γ
 where
  s : p holds ＝ 𝟘
  s = ap _holds r

  t : ¬ (p holds) ＝ 𝟙
  t = ap ¬_ s ∙ not-𝟘-is-𝟙 fe pe

  γ : not fe p ＝ ⊤
  γ = to-subtype-＝ (λ _ → being-prop-is-prop fe) t

false-gives-equal-⊥ : propext 𝓤
                    → funext 𝓤 𝓤
                    → (P : 𝓤 ̇ ) (i : is-prop P)
                    → ¬ P → (P , i) ＝ ⊥
false-gives-equal-⊥ pe fe P i f =
 to-Ω-＝ fe (pe i 𝟘-is-prop (λ p → 𝟘-elim (f p)) 𝟘-elim)

fails-gives-equal-⊥ : propext 𝓤 → funext 𝓤 𝓤 → (p : Ω 𝓤) → ¬ (p holds) → p ＝ ⊥
fails-gives-equal-⊥ pe fe (P , i) = false-gives-equal-⊥ pe fe P i

equal-⊥-gives-fails : (p : Ω 𝓤) → p ＝ ⊥ → ¬ (p holds)
equal-⊥-gives-fails .⊥ refl = 𝟘-elim

decidable-truth-values-are-⊥-or-⊤ : propext 𝓤
                                  → funext 𝓤 𝓤
                                  → (P : 𝓤 ̇ ) (i : is-prop P)
                                  → is-decidable P
                                  → ((P , i) ＝ ⊤)
                                  + ((P , i) ＝ ⊥)
decidable-truth-values-are-⊥-or-⊤ pe fe P i (inl p) =
 inl (true-gives-equal-⊤ pe fe P i p)
decidable-truth-values-are-⊥-or-⊤ pe fe P i (inr ν) =
 inr (false-gives-equal-⊥ pe fe P i ν)

decidable-truth-values-are-⊥-or-⊤' : propext 𝓤
                                  → funext 𝓤 𝓤
                                  → (p : Ω 𝓤)
                                  → is-decidable (p holds)
                                  → (p ＝ ⊤)
                                  + (p ＝ ⊥)
decidable-truth-values-are-⊥-or-⊤' pe fe p =
 decidable-truth-values-are-⊥-or-⊤ pe fe (p holds) (holds-is-prop p)

not-equal-⊤-gives-equal-⊥ : (fe : Fun-Ext)
                            (pe : propext 𝓤)
                            (p : Ω 𝓤)
                          → not fe p ＝ ⊤
                          → p ＝ ⊥
not-equal-⊤-gives-equal-⊥ fe pe p r = γ
 where
  f : (not fe p) holds
  f = Idtofun (ap _holds r ⁻¹) ⋆

  t : p holds ＝ 𝟘
  t = empty-types-are-＝-𝟘 fe pe f

  γ : p ＝ ⊥
  γ = to-subtype-＝ (λ _ → being-prop-is-prop fe) t

different-from-⊤-gives-equal-⊥ : (fe : Fun-Ext)
                                 (pe : propext 𝓤)
                                 (p : Ω 𝓤)
                               → p ≠ ⊤
                               → p ＝ ⊥
different-from-⊤-gives-equal-⊥ fe pe p ν = II
 where
  I : ¬ (p holds)
  I = contrapositive (holds-gives-equal-⊤ pe fe p) ν

  II : p ＝ ⊥
  II = false-gives-equal-⊥ pe fe (p holds) (holds-is-prop p) I

equal-⊤-gives-true : (P : 𝓤 ̇ ) (i : is-prop P) → (P , i) ＝ ⊤ → P
equal-⊤-gives-true P hp r = f ⋆
 where
  s : 𝟙 ＝ P
  s = (ap pr₁ r)⁻¹

  f : 𝟙 → P
  f = transport id s

Ω-extensionality : propext 𝓤
                 → funext 𝓤 𝓤
                 → {p q : Ω 𝓤}
                 → (p holds → q holds)
                 → (q holds → p holds)
                 → p ＝ q
Ω-extensionality pe fe {p} {q} f g =
 to-Ω-＝ fe (pe (holds-is-prop p) (holds-is-prop q) f g)

Ω-extensionality' : propext 𝓤
                  → funext 𝓤 𝓤
                  → {p q : Ω 𝓤}
                  → (p holds ≃ q holds)
                  → p ＝ q
Ω-extensionality' pe fe {p} {q} 𝕗 =
 Ω-extensionality pe fe ⌜ 𝕗 ⌝ ⌜ 𝕗 ⌝⁻¹

Ω-ext : propext 𝓤
      → funext 𝓤 𝓤
      → {p q : Ω 𝓤}
      → (p ＝ ⊤ → q ＝ ⊤)
      → (q ＝ ⊤ → p ＝ ⊤)
      → p ＝ q
Ω-ext pe fe {P , i} {Q , j} f g = III
 where
  I : P → Q
  I x = equal-⊤-gives-true Q j (f (true-gives-equal-⊤ pe fe P i x))

  II : Q → P
  II y = equal-⊤-gives-true P i (g (true-gives-equal-⊤ pe fe Q j y))

  III : P , i ＝ Q , j
  III = Ω-extensionality pe fe I II

Ω-ext' : propext 𝓤
       → funext 𝓤 𝓤
       → {p q : Ω 𝓤}
       → (p ＝ ⊤) ≃ (q ＝ ⊤)
       → p ＝ q
Ω-ext' pe fe 𝕗 = Ω-ext pe fe ⌜ 𝕗 ⌝ ⌜ 𝕗 ⌝⁻¹

Ω-discrete-gives-EM : funext 𝓤 𝓤
                    → propext 𝓤
                    → ((p q : Ω 𝓤) → is-decidable (p ＝ q))
                    → (P : 𝓤 ̇ ) → is-prop P → P + ¬ P
Ω-discrete-gives-EM {𝓤} fe pe δ P i = f (δ p q)
 where
  p q : Ω 𝓤
  p = (P , i)
  q = (𝟙 , 𝟙-is-prop)

  f : is-decidable (p ＝ q) → P + ¬ P
  f (inl e) = inl (equal-𝟙-gives-holds P (ap pr₁ e))
  f (inr ν) = inr (λ (x : P) → ν (to-subtype-＝
                                   (λ _ → being-prop-is-prop fe)
                                   (holds-gives-equal-𝟙 pe P i x)))
\end{code}

Without excluded middle, we have that:

\begin{code}

no-truth-values-other-than-⊥-or-⊤ : funext 𝓤 𝓤
                                  → propext 𝓤
                                  → ¬ (Σ p ꞉ Ω 𝓤 , (p ≠ ⊥) × (p ≠ ⊤))
no-truth-values-other-than-⊥-or-⊤ fe pe ((P , i) , (f , g)) = φ u
 where
  u : ¬ P
  u h = g l
    where
     l : (P , i) ＝ ⊤
     l = Ω-extensionality pe fe unique-to-𝟙 (λ _ → h)

  φ : ¬¬ P
  φ u = f l
    where
     l : (P , i) ＝ ⊥
     l = Ω-extensionality pe fe (λ p → 𝟘-elim (u p)) unique-from-𝟘

no-three-distinct-propositions : funext 𝓤 𝓤
                               → propext 𝓤
                               → ¬ has-three-distinct-points (Ω 𝓤)
no-three-distinct-propositions fe pe ((p , q , r) , u , v , w) = XI
 where
  I : p ≠ ⊥
  I a = no-truth-values-other-than-⊥-or-⊤ fe pe (q , II , III)
   where
    II : q ≠ ⊥
    II b = u (a ∙ b ⁻¹)

    III : q ≠ ⊤
    III c = no-truth-values-other-than-⊥-or-⊤ fe pe (r , IV , V)
     where
      IV : r ≠ ⊥
      IV d = w (d ∙ a ⁻¹)

      V : r ≠ ⊤
      V e = v (c ∙ e ⁻¹)

  VI : p ≠ ⊤
  VI a = no-truth-values-other-than-⊥-or-⊤ fe pe (q , VII , X)
   where
    VII : q ≠ ⊥
    VII b = no-truth-values-other-than-⊥-or-⊤ fe pe (r , VIII , IX)
     where
      VIII : r ≠ ⊥
      VIII c = v (b ∙ c ⁻¹)

      IX : r ≠ ⊤
      IX d = w (d ∙ a ⁻¹)

    X : q ≠ ⊤
    X e = u (a ∙ e ⁻¹)

  XI : 𝟘
  XI = no-truth-values-other-than-⊥-or-⊤ fe pe (p , I , VI)

\end{code}

The above function was added 19th March 2021.

The above implies that if Fin n is embedded in Ω 𝓤, then n ≤ 2. That
is, every finite subset of Ω has at most two elements. See the module
Fin.lagda.

Added 3rd September 2023.

\begin{code}

no-three-distinct-propositions' : funext 𝓤 𝓤
                                → propext 𝓤
                                → (p₀ p₁ q : Ω 𝓤) → p₀ ≠ q → p₁ ≠ q → ¬ (p₀ ≠ p₁)
no-three-distinct-propositions' fe pe p₀ p₁ q ν₀ ν₁ ν =
 no-three-distinct-propositions fe pe ((p₀ , q , p₁) , (ν₀ , ≠-sym ν₁ , ≠-sym ν))

\end{code}
