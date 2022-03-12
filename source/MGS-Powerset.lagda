Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module MGS-Powerset where

open import MGS-More-FunExt-Consequences public

propext : ∀ 𝓤  → 𝓤 ⁺ ̇
propext 𝓤 = {P Q : 𝓤 ̇ } → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ≡ Q

global-propext : 𝓤ω
global-propext = ∀ {𝓤} → propext 𝓤

univalence-gives-propext : is-univalent 𝓤 → propext 𝓤
univalence-gives-propext ua {P} {Q} i j f g = Eq→Id ua P Q γ
 where
  γ : P ≃ Q
  γ = logically-equivalent-subsingletons-are-equivalent P Q i j (f , g)

Id-from-subsingleton : propext 𝓤 → dfunext 𝓤 𝓤
                     → (P : 𝓤 ̇ )
                     → is-subsingleton P
                     → (X : 𝓤 ̇ ) → is-subsingleton (P ≡ X)

Id-from-subsingleton {𝓤} pe fe P i = Hedberg P (λ X → h X , k X)
 where
  module _ (X : 𝓤 ̇ ) where
   f : P ≡ X → is-subsingleton X × (P ⇔ X)
   f p = transport is-subsingleton p i , Id→fun p , (Id→fun (p ⁻¹))

   g : is-subsingleton X × (P ⇔ X) → P ≡ X
   g (l , φ , ψ) = pe i l φ ψ

   h : P ≡ X → P ≡ X
   h = g ∘ f

   j : is-subsingleton (is-subsingleton X × (P ⇔ X))
   j = ×-is-subsingleton'
        ((λ (_ : P ⇔ X) → being-subsingleton-is-subsingleton fe) ,
         (λ (l : is-subsingleton X) → ×-is-subsingleton
                                       (Π-is-subsingleton fe (λ p → l))
                                       (Π-is-subsingleton fe (λ x → i))))

   k : wconstant h
   k p q = ap g (j (f p) (f q))

subsingleton-univalence : propext 𝓤 → dfunext 𝓤 𝓤
                        → (P : 𝓤 ̇ )
                        → is-subsingleton P
                        → (X : 𝓤 ̇ ) → is-equiv (Id→Eq P X)

subsingleton-univalence pe fe P i X = γ
 where
  l : P ≃ X → is-subsingleton X
  l e = equiv-to-subsingleton (≃-sym e) i

  eqtoid : P ≃ X → P ≡ X
  eqtoid e = pe i (equiv-to-subsingleton (≃-sym e) i)
                  ⌜ e ⌝ ⌜ ≃-sym e ⌝

  m : is-subsingleton (P ≃ X)
  m (f , k) (f' , k') = to-subtype-≡
                          (being-equiv-is-subsingleton fe fe)
                          (fe (λ x → j (f x) (f' x)))
    where
     j : is-subsingleton X
     j = equiv-to-subsingleton (≃-sym (f , k)) i

  ε : (e : P ≃ X) → Id→Eq P X (eqtoid e) ≡ e
  ε e = m (Id→Eq P X (eqtoid e)) e

  η : (q : P ≡ X) → eqtoid (Id→Eq P X q) ≡ q
  η q = Id-from-subsingleton pe fe P i X (eqtoid (Id→Eq P X q)) q

  γ : is-equiv (Id→Eq P X)
  γ = invertibles-are-equivs (Id→Eq P X) (eqtoid , η , ε)

subsingleton-univalence-≃ : propext 𝓤 → dfunext 𝓤 𝓤
                          → (X P : 𝓤 ̇ ) → is-subsingleton P → (P ≡ X) ≃ (P ≃ X)

subsingleton-univalence-≃ pe fe X P i = Id→Eq P X ,
                                        subsingleton-univalence pe fe P i X

Ω : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ω 𝓤 = Σ P ꞉ 𝓤 ̇ , is-subsingleton P

_holds : Ω 𝓤 → 𝓤 ̇
_holds (P , i) = P

holds-is-subsingleton : (p : Ω 𝓤) → is-subsingleton (p holds)
holds-is-subsingleton (P , i) = i

Ω-ext : dfunext 𝓤 𝓤 → propext 𝓤 → {p q : Ω 𝓤}
      → (p holds → q holds) → (q holds → p holds) → p ≡ q

Ω-ext {𝓤} fe pe {p} {q} f g = to-subtype-≡
                                 (λ _ → being-subsingleton-is-subsingleton fe)
                                 (pe (holds-is-subsingleton p) (holds-is-subsingleton q) f g)

Ω-is-set : dfunext 𝓤 𝓤 → propext 𝓤 → is-set (Ω 𝓤)
Ω-is-set {𝓤} fe pe = types-with-wconstant-≡-endomaps-are-sets (Ω 𝓤) c
 where
  A : (p q : Ω 𝓤) → 𝓤 ̇
  A p q = (p holds → q holds) × (q holds → p holds)

  i : (p q : Ω 𝓤) → is-subsingleton (A p q)
  i p q = Σ-is-subsingleton
           (Π-is-subsingleton fe
             (λ _ → holds-is-subsingleton q))
             (λ _ → Π-is-subsingleton fe (λ _ → holds-is-subsingleton p))

  g : (p q : Ω 𝓤) → p ≡ q → A p q
  g p q e = (u , v)
   where
    a : p holds ≡ q holds
    a = ap _holds e

    u : p holds → q holds
    u = Id→fun a

    v : q holds → p holds
    v = Id→fun (a ⁻¹)

  h : (p q : Ω 𝓤) → A p q → p ≡ q
  h p q (u , v) = Ω-ext fe pe u v

  f : (p q : Ω 𝓤) → p ≡ q → p ≡ q
  f p q e = h p q (g p q e)

  k : (p q : Ω 𝓤) (d e : p ≡ q) → f p q d ≡ f p q e
  k p q d e = ap (h p q) (i p q (g p q d) (g p q e))

  c : (p q : Ω 𝓤) → Σ f ꞉ (p ≡ q → p ≡ q), wconstant f
  c p q = (f p q , k p q)

powersets-are-sets : hfunext 𝓤 (𝓥 ⁺) → dfunext 𝓥 𝓥 → propext 𝓥
                   → {X : 𝓤 ̇ } → is-set (X → Ω 𝓥)

powersets-are-sets fe fe' pe = Π-is-set fe (λ x → Ω-is-set fe' pe)

𝓟 : 𝓤 ̇ → 𝓤 ⁺ ̇
𝓟 {𝓤} X = X → Ω 𝓤

powersets-are-sets' : Univalence
                    → {X : 𝓤 ̇ } → is-set (𝓟 X)

powersets-are-sets' {𝓤} ua = powersets-are-sets
                               (univalence-gives-hfunext' (ua 𝓤) (ua (𝓤 ⁺)))
                               (univalence-gives-dfunext (ua 𝓤))
                               (univalence-gives-propext (ua 𝓤))

_∈_ : {X : 𝓤 ̇ } → X → 𝓟 X → 𝓤 ̇
x ∈ A = A x holds

_⊆_ : {X : 𝓤 ̇ } → 𝓟 X → 𝓟 X → 𝓤 ̇
A ⊆ B = ∀ x → x ∈ A → x ∈ B

∈-is-subsingleton : {X : 𝓤 ̇ } (A : 𝓟 X) (x : X) → is-subsingleton (x ∈ A)
∈-is-subsingleton A x = holds-is-subsingleton (A x)

⊆-is-subsingleton : dfunext 𝓤 𝓤
                  → {X : 𝓤 ̇ } (A B : 𝓟 X) → is-subsingleton (A ⊆ B)

⊆-is-subsingleton fe A B = Π-is-subsingleton fe
                            (λ x → Π-is-subsingleton fe
                            (λ _ → ∈-is-subsingleton B x))

⊆-refl : {X : 𝓤 ̇ } (A : 𝓟 X) → A ⊆ A
⊆-refl A x = 𝑖𝑑 (x ∈ A)

⊆-refl-consequence : {X : 𝓤 ̇ } (A B : 𝓟 X)
                   → A ≡ B → (A ⊆ B) × (B ⊆ A)

⊆-refl-consequence {X} A A (refl A) = ⊆-refl A , ⊆-refl A

subset-extensionality : propext 𝓤 → dfunext 𝓤 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                      → {X : 𝓤 ̇ } {A B : 𝓟 X}
                      → A ⊆ B → B ⊆ A → A ≡ B

subset-extensionality pe fe fe' {X} {A} {B} h k = fe' φ
 where
  φ : (x : X) → A x ≡ B x
  φ x = to-subtype-≡
           (λ _ → being-subsingleton-is-subsingleton fe)
           (pe (holds-is-subsingleton (A x)) (holds-is-subsingleton (B x))
               (h x) (k x))

subset-extensionality' : Univalence
                       → {X : 𝓤 ̇ } {A B : 𝓟 X}
                       → A ⊆ B → B ⊆ A → A ≡ B

subset-extensionality' {𝓤} ua = subset-extensionality
                                 (univalence-gives-propext (ua 𝓤))
                                 (univalence-gives-dfunext (ua 𝓤))
                                 (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))
infix  40 _∈_

\end{code}
