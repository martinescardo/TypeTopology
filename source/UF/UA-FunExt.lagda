Martin Escardo, 9th April 2018

We first give Voevodsky's original proof that univalence implies
non-dependent, naive function extensionality, as presented by Gambino,
Kapulkin and Lumsdaine in
http://www.math.uwo.ca/faculty/kapulkin/notes/ua_implies_fe.pdf.

We then deduce dependent function extensionality applying a second argument by
Voevodsky, developed in UF.FunExt-from-Naive-FunExt, which doesn't depend on
univalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.UA-FunExt where

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt
open import UF.FunExt-Properties
open import UF.LeftCancellable
open import UF.SubtypeClassifier
open import UF.Univalence

naive-univalence-gives-funext : is-univalent 𝓤 → ∀ {𝓥} → naive-funext 𝓥 𝓤
naive-univalence-gives-funext {𝓤} ua {𝓥} {X} {Y} {f₀} {f₁} h = γ
 where
  Δ = Σ y₀ ꞉ Y , Σ y₁ ꞉ Y , y₀ ＝ y₁

  δ : Y → Δ
  δ y = (y , y , refl)

  π₀ π₁ : Δ → Y
  π₀ (y₀ , y₁ , p) = y₀
  π₁ (y₀ , y₁ , p) = y₁

  δ-is-equiv : is-equiv δ
  δ-is-equiv = (π₀ , η) , (π₀ , ε)
   where
    η : (d : Δ) → δ (π₀ d) ＝ d
    η (y₀ , y₁ , refl) = refl
    ε : (y : Y) → π₀ (δ y) ＝ y
    ε y = refl

  πδ : π₀ ∘ δ ＝ π₁ ∘ δ
  πδ = refl

  φ : (Δ → Y) → (Y → Y)
  φ π = π ∘ δ

  φ-is-equiv : is-equiv φ
  φ-is-equiv = pre-comp-is-equiv ua δ δ-is-equiv

  π₀-equals-π₁ : π₀ ＝ π₁
  π₀-equals-π₁ = is-equiv-lc φ φ-is-equiv πδ

  γ : f₀ ＝ f₁
  γ = f₀                              ＝⟨refl⟩
      (λ x → f₀ x)                    ＝⟨refl⟩
      (λ x → π₀ (f₀ x , f₁ x , h x))  ＝⟨ I ⟩
      (λ x → π₁ (f₀ x , f₁ x , h x))  ＝⟨refl⟩
      (λ x → f₁ x)                    ＝⟨refl⟩
      f₁                              ∎
       where
        I = ap (λ π x → π (f₀ x , f₁ x , h x)) π₀-equals-π₁

\end{code}

Added 19th May 2018:

\begin{code}

univalence-gives-funext : is-univalent 𝓤 → funext 𝓤 𝓤
univalence-gives-funext ua = naive-funext-gives-funext
                              (naive-univalence-gives-funext ua)

\end{code}

Added 27 Jun 2018:

\begin{code}

univalence-gives-funext' : ∀ 𝓤 𝓥
                         → is-univalent 𝓤
                         → is-univalent (𝓤 ⊔ 𝓥)
                         → funext 𝓤 𝓥
univalence-gives-funext' 𝓤 𝓥 ua ua' = naive-funext-gives-funext'
                                       (naive-univalence-gives-funext ua')
                                       (naive-univalence-gives-funext ua)

Univalence-gives-FunExt : Univalence → FunExt
Univalence-gives-FunExt ua 𝓤 𝓥 = univalence-gives-funext' 𝓤 𝓥
                                  (ua 𝓤)
                                  (ua (𝓤 ⊔ 𝓥))

Univalence-gives-Fun-Ext : Univalence → Fun-Ext
Univalence-gives-Fun-Ext ua {𝓤} {𝓥} = Univalence-gives-FunExt ua 𝓤 𝓥

funext-from-successive-univalence : ∀ 𝓤
                                  → is-univalent 𝓤
                                  → is-univalent (𝓤 ⁺)
                                  → funext 𝓤 (𝓤 ⁺)
funext-from-successive-univalence 𝓤 = univalence-gives-funext' 𝓤 (𝓤 ⁺)

open import UF.Subsingletons

Ω-ext-from-univalence : is-univalent 𝓤
                      → {p q : Ω 𝓤}
                      → (p holds → q holds)
                      → (q holds → p holds)
                      → p ＝ q
Ω-ext-from-univalence {𝓤} ua {p} {q} = Ω-extensionality
                                        (univalence-gives-propext ua)
                                        (univalence-gives-funext ua)
\end{code}

April 2020. How much function extensionality do we get from
propositional univalence?

\begin{code}

naive-prop-valued-funext : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
naive-prop-valued-funext 𝓤 𝓥 = (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                              → is-prop Y
                              → is-prop (X → Y)

propositional-univalence : (𝓤 : Universe) → 𝓤 ⁺ ̇
propositional-univalence 𝓤 = (P : 𝓤 ̇ )
                           → is-prop P
                           → (Y : 𝓤 ̇ ) → is-equiv (idtoeq P Y)

prop-eqtoid : propositional-univalence 𝓤
            → (P : 𝓤 ̇ )
            → is-prop P
            → (Y : 𝓤 ̇ )
            → P ≃ Y → P ＝ Y
prop-eqtoid pu P i Y = inverse (idtoeq P Y) (pu P i Y)


propositional-≃-induction : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
propositional-≃-induction 𝓤 𝓥 = (P : 𝓤 ̇ )
                              → is-prop P
                              → (A : (Y : 𝓤 ̇ ) → P ≃ Y → 𝓥 ̇ )
                              → A P (≃-refl P) → (Y : 𝓤 ̇ ) (e : P ≃ Y) → A Y e

propositional-JEq : propositional-univalence 𝓤
                  → (𝓥 : Universe)
                  → propositional-≃-induction 𝓤 𝓥
propositional-JEq {𝓤} pu 𝓥 P i A b Y e = γ
 where
  A' : (Y : 𝓤 ̇ ) → P ＝ Y → 𝓥 ̇
  A' Y q = A Y (idtoeq P Y q)

  b' : A' P refl
  b' = b

  f' : (Y : 𝓤 ̇ ) (q : P ＝ Y) → A' Y q
  f' = Jbased P A' b'

  g : A Y (idtoeq P Y (prop-eqtoid pu P i Y e))
  g = f' Y (prop-eqtoid pu P i Y e)

  γ : A Y (id e)
  γ = transport (A Y) (inverses-are-sections (idtoeq P Y) (pu P i Y) e) g

prop-precomp-is-equiv : propositional-univalence 𝓤
                      → (X Y Z : 𝓤 ̇ )
                      → is-prop X
                      → (f : X → Y)
                      → is-equiv f
                      → is-equiv (λ (g : Y → Z) → g ∘ f)
prop-precomp-is-equiv {𝓤} pu X Y Z i f ise =
 propositional-JEq pu 𝓤 X i (λ W e → is-equiv (λ g → g ∘ ⌜ e ⌝))
   (id-is-equiv (X → Z)) Y (f , ise)

prop-precomp-is-equiv' : propositional-univalence 𝓤
                       → (X Y Z : 𝓤 ̇ )
                       → is-prop Y
                       → (f : X → Y)
                       → is-equiv f
                       → is-equiv (λ (g : Y → Z) → g ∘ f)
prop-precomp-is-equiv' {𝓤} pu X Y Z i f ise =
 prop-precomp-is-equiv pu X Y Z j f ise
  where
   j : is-prop X
   j = equiv-to-prop (f , ise) i

propositional-univalence-gives-naive-prop-valued-funext
 : propositional-univalence 𝓤
 → naive-prop-valued-funext 𝓥 𝓤
propositional-univalence-gives-naive-prop-valued-funext
 {𝓤} {𝓥} pu X Y Y-is-prop f₀ f₁ = γ
 where
  Δ : 𝓤 ̇
  Δ = Σ y₀ ꞉ Y , Σ y₁ ꞉ Y , y₀ ＝ y₁

  δ : Y → Δ
  δ y = (y , y , refl)

  π₀ π₁ : Δ → Y
  π₀ (y₀ , y₁ , p) = y₀
  π₁ (y₀ , y₁ , p) = y₁

  δ-is-equiv : is-equiv δ
  δ-is-equiv = (π₀ , η) , (π₀ , ε)
   where
    η : (d : Δ) → δ (π₀ d) ＝ d
    η (y₀ , y₁ , refl) = refl

    ε : (y : Y) → π₀ (δ y) ＝ y
    ε y = refl

  πδ : π₀ ∘ δ ＝ π₁ ∘ δ
  πδ = refl

  φ : (Δ → Y) → (Y → Y)
  φ π = π ∘ δ

  φ-is-equiv : is-equiv φ
  φ-is-equiv = prop-precomp-is-equiv pu Y Δ Y Y-is-prop δ δ-is-equiv

  π₀-equals-π₁ : π₀ ＝ π₁
  π₀-equals-π₁ = equivs-are-lc φ φ-is-equiv πδ

  γ : f₀ ＝ f₁
  γ = f₀                              ＝⟨refl⟩
      (λ x → f₀ x)                    ＝⟨refl⟩
      (λ x → π₀ (f₀ x , f₁ x , h x))  ＝⟨ I ⟩
      (λ x → π₁ (f₀ x , f₁ x , h x))  ＝⟨refl⟩
      (λ x → f₁ x)                    ＝⟨refl⟩
      f₁                              ∎
   where
    h : (x : X) → f₀ x ＝ f₁ x
    h x = Y-is-prop (f₀ x) (f₁ x)

    I = ap (λ π x → π (f₀ x , f₁ x , h x)) π₀-equals-π₁

\end{code}
