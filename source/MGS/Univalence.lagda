Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Univalence where

open import MGS.Equivalences public

Id→Eq : (X Y : 𝓤 ̇ ) → X ＝ Y → X ≃ Y
Id→Eq X X (refl X) = id-≃ X

is-univalent : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-univalent 𝓤 = (X Y : 𝓤 ̇ ) → is-equiv (Id→Eq X Y)

univalence-≃ : is-univalent 𝓤 → (X Y : 𝓤 ̇ ) → (X ＝ Y) ≃ (X ≃ Y)
univalence-≃ ua X Y = Id→Eq X Y , ua X Y

Eq→Id : is-univalent 𝓤 → (X Y : 𝓤 ̇ ) → X ≃ Y → X ＝ Y
Eq→Id ua X Y = inverse (Id→Eq X Y) (ua X Y)

Id→fun : {X Y : 𝓤 ̇ } → X ＝ Y → X → Y
Id→fun {𝓤} {X} {Y} p = ⌜ Id→Eq X Y p ⌝

Id→funs-agree : {X Y : 𝓤 ̇ } (p : X ＝ Y)
              → Id→fun p ＝ Id→Fun p
Id→funs-agree (refl X) = refl (𝑖𝑑 X)

swap₂ : 𝟚 → 𝟚
swap₂ ₀ = ₁
swap₂ ₁ = ₀

swap₂-involutive : (n : 𝟚) → swap₂ (swap₂ n) ＝ n
swap₂-involutive ₀ = refl ₀
swap₂-involutive ₁ = refl ₁

swap₂-is-equiv : is-equiv swap₂
swap₂-is-equiv = invertibles-are-equivs
                  swap₂
                  (swap₂ , swap₂-involutive , swap₂-involutive)

module example-of-a-nonset (ua : is-univalent 𝓤₀) where

 e₀ e₁ : 𝟚 ≃ 𝟚
 e₀ = id-≃ 𝟚
 e₁ = swap₂ , swap₂-is-equiv

 e₀-is-not-e₁ : e₀ ≠ e₁
 e₀-is-not-e₁ p = ₁-is-not-₀ r
  where
   q : id ＝ swap₂
   q = ap ⌜_⌝ p

   r : ₁ ＝ ₀
   r = ap (λ - → - ₁) q

 p₀ p₁ : 𝟚 ＝ 𝟚
 p₀ = Eq→Id ua 𝟚 𝟚 e₀
 p₁ = Eq→Id ua 𝟚 𝟚 e₁

 p₀-is-not-p₁ : p₀ ≠ p₁
 p₀-is-not-p₁ q = e₀-is-not-e₁ r
  where
   r = e₀            ＝⟨ (inverses-are-sections (Id→Eq 𝟚 𝟚) (ua 𝟚 𝟚) e₀)⁻¹ ⟩
       Id→Eq 𝟚 𝟚 p₀  ＝⟨ ap (Id→Eq 𝟚 𝟚) q ⟩
       Id→Eq 𝟚 𝟚 p₁  ＝⟨ inverses-are-sections (Id→Eq 𝟚 𝟚) (ua 𝟚 𝟚) e₁ ⟩
       e₁            ∎

 𝓤₀-is-not-a-set : ¬ (is-set (𝓤₀ ̇ ))
 𝓤₀-is-not-a-set s = p₀-is-not-p₁ q
  where
   q : p₀ ＝ p₁
   q = s 𝟚 𝟚 p₀ p₁

\end{code}
