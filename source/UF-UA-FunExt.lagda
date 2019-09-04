Martin Escardo, 9th April 2018
Tom de Jong, July 2019 (Added a lemma on composing eqtoids.)

We first give Voevodsky's original proof that univalence implies
non-dependent, naive function extensionality, as presented by Gambino,
Kapulkin and Lumsdaine in
http://www.math.uwo.ca/faculty/kapulkin/notes/ua_implies_fe.pdf.

We then deduce dependent function extensionality applying a second
argument by Voevodsky, developed in another module, which doesn't
depend on univalence.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-UA-FunExt where

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-Univalence
open import UF-LeftCancellable
open import UF-FunExt
open import UF-FunExt-from-Naive-FunExt
open import UF-Equiv-FunExt

naive-funext-from-univalence : is-univalent 𝓤 → ∀ {𝓥} → naive-funext 𝓥 𝓤
naive-funext-from-univalence {𝓤} ua {𝓥} {X} {Y} {f₀} {f₁} h = γ
 where
  Δ = Σ \(y₀ : Y) → Σ \(y₁ : Y) → y₀ ≡ y₁

  δ : Y → Δ
  δ y = (y , y , refl)

  π₀ π₁ : Δ → Y
  π₀ (y₀ , y₁ , p) = y₀
  π₁ (y₀ , y₁ , p) = y₁

  δ-is-equiv : is-equiv δ
  δ-is-equiv = (π₀ , η) , (π₀ , ε)
   where
    η : (d : Δ) → δ (π₀ d) ≡ d
    η (y₀ , y₁ , refl) = refl
    ε : (y : Y) → π₀ (δ y) ≡ y
    ε y = refl

  πδ : π₀ ∘ δ ≡ π₁ ∘ δ
  πδ = refl

  φ : (Δ → Y) → (Y → Y)
  φ π = π ∘ δ

  φ-is-equiv : is-equiv φ
  φ-is-equiv = pre-comp-is-equiv ua δ δ-is-equiv

  π₀-equals-π₁ : π₀ ≡ π₁
  π₀-equals-π₁ = is-equiv-lc φ φ-is-equiv πδ

  γ : f₀ ≡ f₁
  γ = f₀                              ≡⟨ refl ⟩
      (λ x → f₀ x)                    ≡⟨ refl ⟩
      (λ x → π₀ (f₀ x , f₁ x , h x))  ≡⟨ ap (λ π x → π (f₀ x , f₁ x , h x)) π₀-equals-π₁ ⟩
      (λ x → π₁ (f₀ x , f₁ x , h x))  ≡⟨ refl ⟩
      (λ x → f₁ x)                    ≡⟨ refl ⟩
      f₁                              ∎

\end{code}

Added 19th May 2018:

\begin{code}

funext-from-univalence : is-univalent 𝓤 → funext 𝓤 𝓤
funext-from-univalence ua = naive-funext-gives-funext (naive-funext-from-univalence ua)

\end{code}

Added 27 Jun 2018:

\begin{code}

funext-from-univalence' : ∀ 𝓤 𝓥 → is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → funext 𝓤 𝓥
funext-from-univalence' 𝓤 𝓥 ua ua' = naive-funext-gives-funext'
                                       (naive-funext-from-univalence ua')
                                       (naive-funext-from-univalence ua)

FunExt-from-Univalence : Univalence → FunExt
FunExt-from-Univalence ua 𝓤 𝓥 = funext-from-univalence' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

funext-from-successive-univalence : ∀ 𝓤 → is-univalent 𝓤 → is-univalent (𝓤 ⁺) → funext 𝓤 (𝓤 ⁺)
funext-from-successive-univalence 𝓤 = funext-from-univalence' 𝓤 (𝓤 ⁺)

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

Ω-ext-from-univalence : is-univalent 𝓤
                        → {p q : Ω 𝓤} → (p holds → q holds) → (q holds → p holds) → p ≡ q
Ω-ext-from-univalence {𝓤} ua {p} {q} = Ω-ext (funext-from-univalence ua) (propext-from-univalence ua)

\end{code}

Added July 2019. Used in UF-Classifiers.

It is here, because it is quite a general result, but in cannot be in
UF-Univalence or UF-Equiv or UF-Equiv-FunExt, because of cyclic module
dependencies. In particular, we use funext-from-univalence, which is defined
here.

Alternatively, one could add (fe : funext 𝓤 𝓤) as an additional hypothesis and
put this lemma in different module, but this seems awkward as it follows from
univalence of 𝓤, of course.

\begin{code}

eqtoid-comp : (ua : is-univalent 𝓤) {X Y Z : 𝓤 ̇} (f : X ≃ Y) (g : Y ≃ Z)
            → (eqtoid ua X Y f) ∙ (eqtoid ua Y Z g) ≡ eqtoid ua X Z (f ● g)
eqtoid-comp {𝓤} ua {X} {Y} {Z} f =
 JEq ua Y (λ Z g → eqtoid ua X Y f ∙ eqtoid ua Y Z g ≡ eqtoid ua X Z (f ● g)) γ Z
  where
   γ : eqtoid ua X Y f ∙ eqtoid ua Y Y (≃-refl Y) ≡ eqtoid ua X Y (f ● ≃-refl Y)
   γ = eqtoid ua X Y f ∙ eqtoid ua Y Y (≃-refl Y) ≡⟨ ap (λ - → eqtoid ua X Y f ∙ -) (eqtoid-refl ua Y) ⟩
       eqtoid ua X Y f                            ≡⟨ ap (λ - → eqtoid ua X Y -) h ⟩
       eqtoid ua X Y (f ● ≃-refl Y)               ∎
    where
     h : f ≡ f ● ≃-refl Y
     h = to-Σ-≡ (l , being-equiv-is-a-prop'' fe (eqtofun (f ● ≃-refl Y))
                      (transport is-equiv l (eqtofun-is-an-equiv f))
                      (eqtofun-is-an-equiv (f ● ≃-refl Y)))
      where
       fe : funext 𝓤 𝓤
       fe = funext-from-univalence ua
       l : eqtofun f ≡ eqtofun (f ● ≃-refl Y)
       l = dfunext fe (λ x → refl)

\end{code}
