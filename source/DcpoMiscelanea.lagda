Tom de Jong, January 2020.

December 2021: Added material on semidirected and subsingleton suprema.

A collection of various useful facts on (pointed) directed complete posets and
Scott continuous maps between them.

The table of contents is roughly:
 * Lemmas for establishing Scott continuity of maps between dcpos.
 * Continuity of basic functions (constant functions, identity, composition).
 * Defining isomorphisms of (pointed) dcpos.
 * Pointed dcpos have semidirected & subsingleton suprema and these are
   preserved by maps that are both strict and continuous.

   The latter is used to be prove (in DcpoLifting.lagda) that the lifting yields
   the free pointed dcpo on a set.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-PropTrunc

module DcpoMiscelanea
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
       where

open PropositionalTruncation pt

open import UF-Subsingletons

open import Dcpo pt fe 𝓥

\end{code}

Some preliminary basic lemmas.

\begin{code}

∐-is-monotone : (𝓓 : DCPO {𝓤} {𝓣}) {I : 𝓥 ̇ } {α β : I → ⟨ 𝓓 ⟩}
                (δ : is-Directed 𝓓 α) (ε : is-Directed 𝓓 β)
              → ((i : I) → α i ⊑⟨ 𝓓 ⟩ β i)
              → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
∐-is-monotone 𝓓 {I} {α} {β} δ ε l = ∐-is-lowerbound-of-upperbounds 𝓓 δ (∐ 𝓓 ε) γ
 where
  γ : (i : I) → α i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
  γ i = α i   ⊑⟨ 𝓓 ⟩[ l i ]
        β i   ⊑⟨ 𝓓 ⟩[ ∐-is-upperbound 𝓓 ε i ]
        ∐ 𝓓 ε ∎⟨ 𝓓 ⟩

∐-family-≡ : (𝓓 : DCPO {𝓤} {𝓣}) {I : 𝓥 ̇ } {α β : I → ⟨ 𝓓 ⟩}
             (p : α ≡ β) (δ : is-Directed 𝓓 α)
           → ∐ 𝓓 {I} {α} δ ≡ ∐ 𝓓 {I} {β} (transport (is-Directed 𝓓) p δ)
∐-family-≡ 𝓓 {I} {α} {α} refl δ = refl

to-continuous-function-≡ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                           {f g : DCPO[ 𝓓 , 𝓔 ]}
                         → [ 𝓓 , 𝓔 ]⟨ f ⟩ ∼ [ 𝓓 , 𝓔 ]⟨ g ⟩
                         → f ≡ g
to-continuous-function-≡ 𝓓 𝓔 h =
 to-subtype-≡ (being-continuous-is-prop 𝓓 𝓔) (dfunext fe h)

≡-to-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩} → x ≡ y → x ⊑⟨ 𝓓 ⟩ y
≡-to-⊑ 𝓓 {x} {x} refl = reflexivity 𝓓 x

∐-independent-of-directedness-witness : (𝓓 : DCPO {𝓤} {𝓣})
                                        {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
                                        (δ ε : is-Directed 𝓓 α)
                                      → ∐ 𝓓 δ ≡ ∐ 𝓓 ε
∐-independent-of-directedness-witness 𝓓 {I} {α} δ ε = ap (∐ 𝓓) p
 where
  p : δ ≡ ε
  p = being-directed-is-prop (underlying-order 𝓓) α δ ε

is-monotone : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
            → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) → 𝓤 ⊔ 𝓣 ⊔ 𝓣' ̇
is-monotone 𝓓 𝓔 f = (x y : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ y → f x ⊑⟨ 𝓔 ⟩ f y

\end{code}

Lemmas for establishing Scott continuity of maps between dcpos.

\begin{code}

image-is-directed : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                    {f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩}
                  → is-monotone 𝓓 𝓔 f
                  → {I : 𝓥 ̇ }
                  → {α : I → ⟨ 𝓓 ⟩}
                  → is-Directed 𝓓 α
                  → is-Directed 𝓔 (f ∘ α)
image-is-directed 𝓓 𝓔 {f} m {I} {α} δ =
 inhabited-if-Directed 𝓓 α δ , γ
  where
   γ : is-semidirected (underlying-order 𝓔) (f ∘ α)
   γ i j = ∥∥-functor (λ (k , u , v) → k , m (α i) (α k) u , m (α j) (α k) v)
                      (semidirected-if-Directed 𝓓 α δ i j)

continuity-criterion : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                       (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
                     → (m : is-monotone 𝓓 𝓔 f)
                     → ((I : 𝓥 ̇ )
                        (α : I → ⟨ 𝓓 ⟩)
                        (δ : is-Directed 𝓓 α)
                     → f (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ ∐ 𝓔 (image-is-directed 𝓓 𝓔 m δ))
                     → is-continuous 𝓓 𝓔 f
continuity-criterion 𝓓 𝓔 f m e I α δ = ub , lb-of-ubs
 where
  ub : (i : I) → f (α i) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 δ)
  ub i = m (α i) (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ i)
  ε : is-Directed 𝓔 (f ∘ α)
  ε = image-is-directed 𝓓 𝓔 m δ
  lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order 𝓔)
              (f (∐ 𝓓 δ)) (f ∘ α)
  lb-of-ubs y u = f (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩[ e I α δ  ]
                  ∐ 𝓔 ε     ⊑⟨ 𝓔 ⟩[ ∐-is-lowerbound-of-upperbounds 𝓔 ε y u ]
                  y         ∎⟨ 𝓔 ⟩

continuity-criterion' : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                        (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
                      → (m : is-monotone 𝓓 𝓔 f)
                      → ((I : 𝓥 ̇ )
                         (α : I → ⟨ 𝓓 ⟩)
                         (δ : is-Directed 𝓓 α)
                      → is-lowerbound-of-upperbounds (underlying-order 𝓔)
                                                     (f (∐ 𝓓 δ)) (f ∘ α))
                      → is-continuous 𝓓 𝓔 f
continuity-criterion' 𝓓 𝓔 f m lb I α δ = ub , lb I α δ
 where
  ub : (i : I) → f (α i) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 δ)
  ub i = m (α i) (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ i)

monotone-if-continuous : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                         (f : DCPO[ 𝓓 , 𝓔 ])
                       → is-monotone 𝓓 𝓔 [ 𝓓 , 𝓔 ]⟨ f ⟩
monotone-if-continuous 𝓓 𝓔 (f , cts) x y l = γ
  where
   α : 𝟙 {𝓥} + 𝟙 {𝓥} → ⟨ 𝓓 ⟩
   α (inl *) = x
   α (inr *) = y
   δ : is-Directed 𝓓 α
   δ = (∣ inl ⋆ ∣ , ε)
    where
     ε : (i j : 𝟙 + 𝟙) → ∃ k ꞉ 𝟙 + 𝟙 , α i ⊑⟨ 𝓓 ⟩ α k × α j ⊑⟨ 𝓓 ⟩ α k
     ε (inl ⋆) (inl ⋆) = ∣ inr ⋆ , l , l ∣
     ε (inl ⋆) (inr ⋆) = ∣ inr ⋆ , l , reflexivity 𝓓 y ∣
     ε (inr ⋆) (inl ⋆) = ∣ inr ⋆ , reflexivity 𝓓 y , l ∣
     ε (inr ⋆) (inr ⋆) = ∣ inr ⋆ , reflexivity 𝓓 y , reflexivity 𝓓 y ∣
   a : y ≡ ∐ 𝓓 δ
   a = antisymmetry 𝓓 y (∐ 𝓓 δ)
           (∐-is-upperbound 𝓓 δ (inr ⋆))
           (∐-is-lowerbound-of-upperbounds 𝓓 δ y h)
    where
     h : (i : 𝟙 + 𝟙) → α i ⊑⟨ 𝓓 ⟩ y
     h (inl ⋆) = l
     h (inr ⋆) = reflexivity 𝓓 y
   b : is-sup (underlying-order 𝓔) (f y) (f ∘ α)
   b = transport (λ - → is-sup (underlying-order 𝓔) - (f ∘ α)) (ap f (a ⁻¹))
       (cts (𝟙 + 𝟙) α δ)
   γ : f x ⊑⟨ 𝓔 ⟩ f y
   γ = sup-is-upperbound (underlying-order 𝓔) b (inl ⋆)

image-is-directed' : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                     (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇} {α : I → ⟨ 𝓓 ⟩}
                   → is-Directed 𝓓 α
                   → is-Directed 𝓔 ([ 𝓓 , 𝓔 ]⟨ f ⟩ ∘ α)
image-is-directed' 𝓓 𝓔 f {I} {α} δ = image-is-directed 𝓓 𝓔 m δ
 where
  m : is-monotone 𝓓 𝓔 [ 𝓓 , 𝓔 ]⟨ f ⟩
  m = monotone-if-continuous 𝓓 𝓔 f

continuous-∐-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                 (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇} {α : I → ⟨ 𝓓 ⟩}
                 (δ : is-Directed 𝓓 α)
               → [ 𝓓 , 𝓔 ]⟨ f ⟩ (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ ∐ 𝓔 (image-is-directed' 𝓓 𝓔 f δ)
continuous-∐-⊑ 𝓓 𝓔 (f , c) {I} {α} δ =
 sup-is-lowerbound-of-upperbounds (underlying-order 𝓔) (c I α δ) (∐ 𝓔 ε) u
  where
   ε : is-Directed 𝓔 (f ∘ α)
   ε = image-is-directed' 𝓓 𝓔 (f , c) δ
   u : is-upperbound (underlying-order 𝓔) (∐ 𝓔 ε) (f ∘ α)
   u = ∐-is-upperbound 𝓔 ε

continuous-∐-⊒ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                 (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇} {α : I → ⟨ 𝓓 ⟩}
                 (δ : is-Directed 𝓓 α)
               → ∐ 𝓔 (image-is-directed' 𝓓 𝓔 f δ) ⊑⟨ 𝓔 ⟩ [ 𝓓 , 𝓔 ]⟨ f ⟩ (∐ 𝓓 δ)
continuous-∐-⊒ 𝓓 𝓔 (f , c) {I} {α} δ =
 ∐-is-lowerbound-of-upperbounds 𝓔 ε (f (∐ 𝓓 δ)) u
  where
   ε : is-Directed 𝓔 (f ∘ α)
   ε = image-is-directed' 𝓓 𝓔 (f , c) δ
   u : (i : I) → f (α i) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 δ)
   u i = sup-is-upperbound (underlying-order 𝓔) (c I α δ) i

continuous-∐-≡ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                 (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇} {α : I → ⟨ 𝓓 ⟩}
                 (δ : is-Directed 𝓓 α)
               → [ 𝓓 , 𝓔 ]⟨ f ⟩ (∐ 𝓓 δ) ≡ ∐ 𝓔 (image-is-directed' 𝓓 𝓔 f δ)
continuous-∐-≡ 𝓓 𝓔 (f , c) {I} {α} δ =
 antisymmetry 𝓔 (f (∐ 𝓓 δ)) (∐ 𝓔 ε) a b
  where
   ε : is-Directed 𝓔 (f ∘ α)
   ε = image-is-directed' 𝓓 𝓔 (f , c) δ
   a : f (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ ∐ 𝓔 ε
   a = continuous-∐-⊑ 𝓓 𝓔 (f , c) δ
   b : ∐ 𝓔 ε ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 δ)
   b = continuous-∐-⊒ 𝓓 𝓔 (f , c) δ

\end{code}

Continuity of basic functions (constant functions, identity, composition).

\begin{code}

constant-functions-are-continuous : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                                    (e : ⟨ 𝓔 ⟩) → is-continuous 𝓓 𝓔 (λ d → e)
constant-functions-are-continuous 𝓓 𝓔 e I α δ = u , v
 where
  u : (i : I) → e ⊑⟨ 𝓔 ⟩ e
  u i = reflexivity 𝓔 e
  v : (y : ⟨ 𝓔 ⟩) → ((i : I) → e ⊑⟨ 𝓔 ⟩ y) → e ⊑⟨ 𝓔 ⟩ y
  v y l  = ∥∥-rec (prop-valuedness 𝓔 e y)
                  (λ (i : I) → l i)
                  (inhabited-if-Directed 𝓓 α δ)

id-is-monotone : (𝓓 : DCPO {𝓤} {𝓣}) → is-monotone 𝓓 𝓓 id
id-is-monotone 𝓓 x y l = l

id-is-continuous : (𝓓 : DCPO {𝓤} {𝓣}) → is-continuous 𝓓 𝓓 id
id-is-continuous 𝓓 = continuity-criterion 𝓓 𝓓 id (id-is-monotone 𝓓) γ
 where
  γ : (I : 𝓥 ̇) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
    → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (image-is-directed 𝓓 𝓓 (λ x y l → l) δ)
  γ I α δ = ≡-to-⊑ 𝓓 (∐-independent-of-directedness-witness 𝓓
             δ (image-is-directed 𝓓 𝓓 (λ x y l → l) δ))

∘-is-continuous : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) (𝓔' : DCPO {𝓦} {𝓦'})
                  (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) (g : ⟨ 𝓔 ⟩ → ⟨ 𝓔' ⟩)
                → is-continuous 𝓓 𝓔 f
                → is-continuous 𝓔 𝓔' g
                → is-continuous 𝓓 𝓔' (g ∘ f)
∘-is-continuous 𝓓 𝓔 𝓔' f g cf cg = continuity-criterion 𝓓 𝓔' (g ∘ f) m ψ
 where
  mf : is-monotone 𝓓 𝓔 f
  mf = monotone-if-continuous 𝓓 𝓔 (f , cf)
  mg : is-monotone 𝓔 𝓔' g
  mg = monotone-if-continuous 𝓔 𝓔' (g , cg)
  m : is-monotone 𝓓 𝓔' (g ∘ f)
  m x y l = mg (f x) (f y) (mf x y l)
  ψ : (I : 𝓥 ̇) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
    → g (f (∐ 𝓓 δ)) ⊑⟨ 𝓔' ⟩ ∐ 𝓔' (image-is-directed 𝓓 𝓔' m δ)
  ψ I α δ = g (f (∐ 𝓓 δ)) ⊑⟨ 𝓔' ⟩[ l₁ ]
            g (∐ 𝓔 εf)    ⊑⟨ 𝓔' ⟩[ l₂ ]
            ∐ 𝓔' εg       ⊑⟨ 𝓔' ⟩[ l₃ ]
            ∐ 𝓔' ε        ∎⟨ 𝓔' ⟩
   where
    ε : is-Directed 𝓔' (g ∘ f ∘ α)
    ε = image-is-directed 𝓓 𝓔' m δ
    εf : is-Directed 𝓔 (f ∘ α)
    εf = image-is-directed' 𝓓 𝓔 (f , cf) δ
    εg : is-Directed 𝓔' (g ∘ f ∘ α)
    εg = image-is-directed' 𝓔 𝓔' (g , cg) εf
    l₁ = mg (f (∐ 𝓓 δ)) (∐ 𝓔 εf) h
     where
      h : f (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ ∐ 𝓔 εf
      h = continuous-∐-⊑ 𝓓 𝓔 (f , cf) δ
    l₂ = continuous-∐-⊑ 𝓔 𝓔' (g , cg) εf
    l₃ = ≡-to-⊑ 𝓔' (∐-independent-of-directedness-witness 𝓔' εg ε)

∘-is-continuous₃ : {𝓦₁ 𝓣₁ 𝓦₂ 𝓣₂ 𝓦₃ 𝓣₃ 𝓦₄ 𝓣₄ : Universe}
                   (𝓓₁ : DCPO {𝓦₁} {𝓣₁}) (𝓓₂ : DCPO {𝓦₂} {𝓣₂})
                   (𝓓₃ : DCPO {𝓦₃} {𝓣₃}) (𝓓₄ : DCPO {𝓦₄} {𝓣₄})
                   (f : ⟨ 𝓓₁ ⟩ → ⟨ 𝓓₂ ⟩) (g : ⟨ 𝓓₂ ⟩ → ⟨ 𝓓₃ ⟩)
                   (h : ⟨ 𝓓₃ ⟩ → ⟨ 𝓓₄ ⟩)
                 → is-continuous 𝓓₁ 𝓓₂ f
                 → is-continuous 𝓓₂ 𝓓₃ g
                 → is-continuous 𝓓₃ 𝓓₄ h
                 → is-continuous 𝓓₁ 𝓓₄ (h ∘ g ∘ f)
∘-is-continuous₃ 𝓓₁ 𝓓₂ 𝓓₃ 𝓓₄ f g h cf cg ch =
 ∘-is-continuous 𝓓₁ 𝓓₂ 𝓓₄ f (h ∘ g) cf
                 (∘-is-continuous 𝓓₂ 𝓓₃ 𝓓₄ g h cg ch)

DCPO-∘ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) (𝓔' : DCPO {𝓦} {𝓦'})
       → DCPO[ 𝓓 , 𝓔 ] → DCPO[ 𝓔 , 𝓔' ] → DCPO[ 𝓓 , 𝓔' ]
DCPO-∘ 𝓓 𝓔 𝓔' (f , cf) (g , cg) = (g ∘ f) , (∘-is-continuous 𝓓 𝓔 𝓔' f g cf cg)

DCPO-∘₃ : {𝓦₁ 𝓣₁ 𝓦₂ 𝓣₂ 𝓦₃ 𝓣₃ 𝓦₄ 𝓣₄ : Universe}
          (𝓓₁ : DCPO {𝓦₁} {𝓣₁}) (𝓓₂ : DCPO {𝓦₂} {𝓣₂})
          (𝓓₃ : DCPO {𝓦₃} {𝓣₃}) (𝓓₄ : DCPO {𝓦₄} {𝓣₄})
          (f : DCPO[ 𝓓₁ , 𝓓₂ ]) (g : DCPO[ 𝓓₂ , 𝓓₃ ]) (h : DCPO[ 𝓓₃ , 𝓓₄ ])
        → DCPO[ 𝓓₁ , 𝓓₄ ]
DCPO-∘₃ 𝓓₁ 𝓓₂ 𝓓₃ 𝓓₄ f g h = DCPO-∘ 𝓓₁ 𝓓₂ 𝓓₄ f (DCPO-∘ 𝓓₂ 𝓓₃ 𝓓₄ g h)

\end{code}

Defining isomorphisms of (pointed) dcpos.

\begin{code}

_≃ᵈᶜᵖᵒ_ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
𝓓 ≃ᵈᶜᵖᵒ 𝓔 = Σ f ꞉ (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) , Σ g ꞉ (⟨ 𝓔 ⟩ → ⟨ 𝓓 ⟩) ,
                ((d : ⟨ 𝓓 ⟩) → g (f d) ≡ d)
              × ((e : ⟨ 𝓔 ⟩) → f (g e) ≡ e)
              × is-continuous 𝓓 𝓔 f
              × is-continuous 𝓔 𝓓 g

_≃ᵈᶜᵖᵒ⊥_ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
𝓓 ≃ᵈᶜᵖᵒ⊥ 𝓔 = Σ f ꞉ (⟨ 𝓓 ⁻ ⟩ → ⟨ 𝓔 ⁻ ⟩) , Σ g ꞉ (⟨ 𝓔 ⁻ ⟩ → ⟨ 𝓓 ⁻ ⟩) ,
                ((d : ⟨ 𝓓 ⁻ ⟩) → g (f d) ≡ d)
               × ((e : ⟨ 𝓔 ⁻ ⟩) → f (g e) ≡ e)
               × is-continuous (𝓓 ⁻) (𝓔 ⁻) f
               × is-continuous (𝓔 ⁻) (𝓓 ⁻) g
               × is-strict 𝓓 𝓔 f
               × is-strict 𝓔 𝓓 g

≃ᵈᶜᵖᵒ-to-≃ᵈᶜᵖᵒ⊥ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
                → (𝓓 ⁻) ≃ᵈᶜᵖᵒ (𝓔 ⁻) → 𝓓 ≃ᵈᶜᵖᵒ⊥ 𝓔
≃ᵈᶜᵖᵒ-to-≃ᵈᶜᵖᵒ⊥ 𝓓 𝓔 (f , g , gf , fg , cf , cg) =
 f , g , gf , fg , cf , cg , sf , sg
  where
   sf : is-strict 𝓓 𝓔 f
   sf = antisymmetry (𝓔 ⁻) (f (⊥ 𝓓)) (⊥ 𝓔) γ (⊥-is-least 𝓔 (f (⊥ 𝓓)))
    where
     γ = f (⊥ 𝓓)     ⊑⟨ 𝓔 ⁻ ⟩[ l₁ ]
         f (g (⊥ 𝓔)) ⊑⟨ 𝓔 ⁻ ⟩[ l₂ ]
         ⊥ 𝓔         ∎⟨ 𝓔 ⁻ ⟩
      where
       l₁ = monotone-if-continuous (𝓓 ⁻) (𝓔 ⁻) (f , cf) (⊥ 𝓓) (g (⊥ 𝓔))
             (⊥-is-least 𝓓 (g (⊥ 𝓔)))
       l₂ = ≡-to-⊑ (𝓔 ⁻) (fg (⊥ 𝓔))
   sg : is-strict 𝓔 𝓓 g
   sg = antisymmetry (𝓓 ⁻) (g (⊥ 𝓔)) (⊥ 𝓓) γ (⊥-is-least 𝓓 (g (⊥ 𝓔)))
    where
     γ = g (⊥ 𝓔)     ⊑⟨ 𝓓 ⁻ ⟩[ l₁ ]
         g (f (⊥ 𝓓)) ⊑⟨ 𝓓 ⁻ ⟩[ l₂ ]
         ⊥ 𝓓         ∎⟨ 𝓓 ⁻ ⟩
      where
       l₁ = monotone-if-continuous (𝓔 ⁻) (𝓓 ⁻) (g , cg) (⊥ 𝓔) (f (⊥ 𝓓))
             (⊥-is-least 𝓔 (f (⊥ 𝓓)))
       l₂ = ≡-to-⊑ (𝓓 ⁻) (gf (⊥ 𝓓))

is-a-non-trivial-pointed-dcpo : (𝓓 : DCPO⊥ {𝓤} {𝓣}) → 𝓤 ̇
is-a-non-trivial-pointed-dcpo 𝓓 = ∃ x ꞉ ⟪ 𝓓 ⟫ , x ≢ ⊥ 𝓓

\end{code}

Pointed dcpos have semidirected & subsingleton suprema and these are preserved
by maps that are both strict and continuous.

This is used to be prove (in DcpoLifting.lagda) that the lifting yields the free
pointed dcpo on a set.

\begin{code}

add-⊥ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫)
      → (𝟙{𝓥} + I) → ⟪ 𝓓 ⟫
add-⊥ 𝓓 α (inl ⋆) = ⊥ 𝓓
add-⊥ 𝓓 α (inr i) = α i

add-⊥-is-directed : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
                  → is-semidirected (underlying-order (𝓓 ⁻)) α
                  → is-Directed (𝓓 ⁻) (add-⊥ 𝓓 α)
add-⊥-is-directed 𝓓 {I} {α} σ = ∣ inl ⋆ ∣ , δ
 where
  δ : is-semidirected (underlying-order (𝓓 ⁻)) (add-⊥ 𝓓 _)
  δ (inl ⋆) a       = ∣ a , ⊥-is-least 𝓓 (add-⊥ 𝓓 α a) ,
                            reflexivity (𝓓 ⁻) (add-⊥ 𝓓 α a) ∣
  δ (inr i) (inl ⋆) = ∣ (inr i) , reflexivity (𝓓 ⁻) (α i)
                                , ⊥-is-least 𝓓 (α i)        ∣
  δ (inr i) (inr j) = ∥∥-functor (λ (k , u , v) → (inr k , u , v)) (σ i j)

adding-⊥-preserves-sup : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ }
                         (α : I → ⟪ 𝓓 ⟫) (x : ⟪ 𝓓 ⟫)
                       → is-sup (underlying-order (𝓓 ⁻)) x α
                       → is-sup (underlying-order (𝓓 ⁻)) x (add-⊥ 𝓓 α)
adding-⊥-preserves-sup 𝓓 {I} α x x-is-sup = x-is-ub , x-is-lb-of-ubs
 where
  x-is-ub : (i : 𝟙 + I) → add-⊥ 𝓓 α i ⊑⟪ 𝓓 ⟫ x
  x-is-ub (inl ⋆) = ⊥-is-least 𝓓 x
  x-is-ub (inr i) = sup-is-upperbound (underlying-order (𝓓 ⁻)) x-is-sup i
  x-is-lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 ⁻))
                    x (add-⊥ 𝓓 α)
  x-is-lb-of-ubs y y-is-ub = sup-is-lowerbound-of-upperbounds
                              (underlying-order (𝓓 ⁻)) x-is-sup y
                              (λ i → y-is-ub (inr i))

adding-⊥-reflects-sup : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ }
                        (α : I → ⟪ 𝓓 ⟫) (x : ⟪ 𝓓 ⟫)
                      → is-sup (underlying-order (𝓓 ⁻)) x (add-⊥ 𝓓 α)
                      → is-sup (underlying-order (𝓓 ⁻)) x α
adding-⊥-reflects-sup 𝓓 {I} α x x-is-sup = x-is-ub , x-is-lb-of-ubs
 where
  x-is-ub : (i : I) → α i ⊑⟪ 𝓓 ⟫ x
  x-is-ub i = sup-is-upperbound (underlying-order (𝓓 ⁻)) x-is-sup (inr i)
  x-is-lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 ⁻)) x α
  x-is-lb-of-ubs y y-is-ub = sup-is-lowerbound-of-upperbounds
                              (underlying-order (𝓓 ⁻)) x-is-sup y
                              h
   where
    h : is-upperbound (underlying-order (𝓓 ⁻)) y (add-⊥ 𝓓 α)
    h (inl ⋆) = ⊥-is-least 𝓓 y
    h (inr i) = y-is-ub i

semidirected-complete-if-pointed : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
                                 → is-semidirected (underlying-order (𝓓 ⁻)) α
                                 → has-sup (underlying-order (𝓓 ⁻)) α
semidirected-complete-if-pointed 𝓓 {I} {α} σ = x , x-is-sup
 where
  δ : is-Directed (𝓓 ⁻) (add-⊥ 𝓓 α)
  δ = add-⊥-is-directed 𝓓 σ
  x : ⟪ 𝓓 ⟫
  x = ∐ (𝓓 ⁻) δ
  x-is-sup : is-sup (underlying-order (𝓓 ⁻)) x α
  x-is-sup = adding-⊥-reflects-sup 𝓓 α x (∐-is-sup (𝓓 ⁻) δ)

∐ˢᵈ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
    → is-semidirected (underlying-order (𝓓 ⁻)) α → ⟪ 𝓓 ⟫
∐ˢᵈ 𝓓 {I} {α} σ = pr₁ (semidirected-complete-if-pointed 𝓓 σ)

∐ˢᵈ-in-terms-of-∐ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
                    (σ : is-semidirected (underlying-order (𝓓 ⁻)) α)
                  → ∐ˢᵈ 𝓓 σ ≡ ∐ (𝓓 ⁻) (add-⊥-is-directed 𝓓 σ)
∐ˢᵈ-in-terms-of-∐ 𝓓 {I} {α} σ = refl

preserves-semidirected-sups-if-continuous-and-strict :
   (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
   (f : ⟪ 𝓓 ⟫ → ⟪ 𝓔 ⟫)
 → is-continuous (𝓓 ⁻) (𝓔 ⁻) f
 → is-strict 𝓓 𝓔 f
 → {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
 → (σ : is-semidirected (underlying-order (𝓓 ⁻)) α)
 → is-sup (underlying-order (𝓔 ⁻)) (f (∐ˢᵈ 𝓓 σ)) (f ∘ α)
preserves-semidirected-sups-if-continuous-and-strict 𝓓 𝓔 f con str {I} {α} σ =
 ub , lb-of-ubs
 where
  δ : is-Directed (𝓓 ⁻) (add-⊥ 𝓓 α)
  δ = add-⊥-is-directed 𝓓 σ
  claim₁ : is-sup (underlying-order (𝓔 ⁻)) (f (∐ (𝓓 ⁻) δ))
            (f ∘ add-⊥ 𝓓 α)
  claim₁ = con (𝟙 + I) (add-⊥ 𝓓 α) (add-⊥-is-directed 𝓓 σ)
  claim₂ : is-sup (underlying-order (𝓔 ⁻)) (f (∐ˢᵈ 𝓓 σ))
            (f ∘ add-⊥ 𝓓 α)
  claim₂ = transport⁻¹
            (λ - → is-sup (underlying-order (𝓔 ⁻)) (f -) (f ∘ (add-⊥ 𝓓 α)))
            (∐ˢᵈ-in-terms-of-∐ 𝓓 σ) claim₁
  ub : (i : I) → f (α i) ⊑⟪ 𝓔 ⟫ f (∐ˢᵈ 𝓓 σ)
  ub i = sup-is-upperbound (underlying-order (𝓔 ⁻)) claim₂ (inr i)
  lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓔 ⁻)) (f (∐ˢᵈ 𝓓 σ))
                (f ∘ α)
  lb-of-ubs y y-is-ub = sup-is-lowerbound-of-upperbounds (underlying-order (𝓔 ⁻))
                         claim₂ y h
   where
    h : is-upperbound (underlying-order (𝓔 ⁻)) y (f ∘ add-⊥ 𝓓 α)
    h (inl ⋆) = f (⊥ 𝓓) ⊑⟪ 𝓔 ⟫[ ≡-to-⊑ (𝓔 ⁻) str ]
                ⊥ 𝓔     ⊑⟪ 𝓔 ⟫[ ⊥-is-least 𝓔 y ]
                y       ∎⟪ 𝓔 ⟫
    h (inr i) = y-is-ub i

subsingleton-indexed-is-semidirected : (𝓓 : DCPO {𝓤} {𝓣})
                                       {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩)
                                     → is-prop I
                                     → is-semidirected (underlying-order 𝓓) α
subsingleton-indexed-is-semidirected 𝓓 α ρ i j = ∣ i , r , r' ∣
  where
   r : α i ⊑⟨ 𝓓 ⟩ α i
   r = reflexivity 𝓓 (α i)
   r' : α j ⊑⟨ 𝓓 ⟩ α i
   r' = transport (λ k → α k ⊑⟨ 𝓓 ⟩ α i) (ρ i j) r

subsingleton-complete-if-pointed : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫)
                                 → is-prop I
                                 → has-sup (underlying-order (𝓓 ⁻)) α
subsingleton-complete-if-pointed 𝓓 α ρ =
 semidirected-complete-if-pointed 𝓓 σ
  where
   σ : is-semidirected (underlying-order (𝓓 ⁻)) α
   σ = subsingleton-indexed-is-semidirected (𝓓 ⁻) α ρ

∐ˢˢ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫)
    → is-prop I → ⟪ 𝓓 ⟫
∐ˢˢ 𝓓 {I} α ρ = pr₁ (subsingleton-complete-if-pointed 𝓓 α ρ)

∐ˢˢ-in-terms-of-∐ˢᵈ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
                      (ρ : is-prop I)
                    → ∐ˢˢ 𝓓 α ρ
                    ≡ ∐ˢᵈ 𝓓
                       (subsingleton-indexed-is-semidirected (𝓓 ⁻) α ρ)
∐ˢˢ-in-terms-of-∐ˢᵈ 𝓓 {I} {α} σ = refl

preserves-subsingleton-sups-if-continuous-and-strict :
   (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
   (f : ⟪ 𝓓 ⟫ → ⟪ 𝓔 ⟫)
 → is-continuous (𝓓 ⁻) (𝓔 ⁻) f
 → is-strict 𝓓 𝓔 f
 → {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫)
 → (ρ : is-prop I)
 → is-sup (underlying-order (𝓔 ⁻)) (f (∐ˢˢ 𝓓 α ρ)) (f ∘ α)
preserves-subsingleton-sups-if-continuous-and-strict 𝓓 𝓔 f con str α ρ =
 preserves-semidirected-sups-if-continuous-and-strict 𝓓 𝓔 f con str
  (subsingleton-indexed-is-semidirected (𝓓 ⁻) α ρ)

∐ˢˢ-is-upperbound : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫)
                    (ρ : is-prop I)
                  → is-upperbound
                     (underlying-order (𝓓 ⁻)) (∐ˢˢ 𝓓 α ρ) α
∐ˢˢ-is-upperbound 𝓓 {I} α ρ i = ∐-is-upperbound (𝓓 ⁻) δ (inr i)
 where
  δ : is-Directed (𝓓 ⁻) (add-⊥ 𝓓 α)
  δ = add-⊥-is-directed 𝓓 (subsingleton-indexed-is-semidirected (𝓓 ⁻) α ρ)

∐ˢˢ-is-lowerbound-of-upperbounds : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫)
                                   (ρ : is-prop I)
                                 → is-lowerbound-of-upperbounds
                                    (underlying-order (𝓓 ⁻)) (∐ˢˢ 𝓓 α ρ) α
∐ˢˢ-is-lowerbound-of-upperbounds 𝓓 {I} α ρ y y-is-ub =
 ∐-is-lowerbound-of-upperbounds (𝓓 ⁻) δ y h
  where
   δ : is-Directed (𝓓 ⁻) (add-⊥ 𝓓 α)
   δ = add-⊥-is-directed 𝓓 (subsingleton-indexed-is-semidirected (𝓓 ⁻) α ρ)
   h : (i : 𝟙 + I) → add-⊥ 𝓓 α i ⊑⟪ 𝓓 ⟫ y
   h (inl ⋆) = ⊥-is-least 𝓓 y
   h (inr i) = y-is-ub i

∐ˢˢ-is-sup : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫) (ρ : is-prop I)
           → is-sup (underlying-order (𝓓 ⁻)) (∐ˢˢ 𝓓 α ρ) α
∐ˢˢ-is-sup 𝓓 α ρ = ∐ˢˢ-is-upperbound 𝓓 α ρ
                 , ∐ˢˢ-is-lowerbound-of-upperbounds 𝓓 α ρ

∐ˢˢ-≡-if-continuous-and-strict : (𝓓 : DCPO⊥ {𝓤} {𝓣}) (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
                                 (f : ⟪ 𝓓 ⟫ → ⟪ 𝓔 ⟫)
                               → is-continuous (𝓓 ⁻) (𝓔 ⁻) f
                               → is-strict 𝓓 𝓔 f
                               → {I : 𝓥 ̇ } (α : I → ⟪ 𝓓 ⟫)
                               → (ρ : is-prop I)
                               → f (∐ˢˢ 𝓓 α ρ) ≡ ∐ˢˢ 𝓔 (f ∘ α) ρ
∐ˢˢ-≡-if-continuous-and-strict 𝓓 𝓔 f con str α ρ =
 sups-are-unique
  (underlying-order (𝓔 ⁻))
  (axioms-of-dcpo (𝓔 ⁻)) (f ∘ α)
  (preserves-subsingleton-sups-if-continuous-and-strict 𝓓 𝓔 f con str α ρ)
  (∐ˢˢ-is-sup 𝓔 (f ∘ α) ρ)

∐ˢˢ-family-≡ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } {α β : I → ⟪ 𝓓 ⟫} (ρ : is-prop I)
             → α ≡ β
             → ∐ˢˢ 𝓓 α ρ ≡ ∐ˢˢ 𝓓 β ρ
∐ˢˢ-family-≡ 𝓓 ρ refl = refl

\end{code}
