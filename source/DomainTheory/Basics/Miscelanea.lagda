Tom de Jong, January 2020.

December 2021: Added material on semidirected and subsingleton suprema.
June 2022: Refactored and moved some material around to/from other files.

A collection of various useful definitions and facts on directed complete posets
and Scott continuous maps between them.

Table of contents
 * Lemmas for establishing Scott continuity of maps between dcpos.
 * Continuity of basic functions (constant functions, identity, composition).
 * Definitions of isomorphisms of dcpos, continuous retracts and
   embedding-projection pairs.
 * Defining local smallness for dcpos and showing it is preserved by continuous
   retracts.
 * Lemmas involving (joins of) cofinal directed families.
 * Reindexing directed families.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.Basics.Miscelanea
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe)
       where

private
 fe' : FunExt
 fe' _ _ = fe

open PropositionalTruncation pt

open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Size hiding (is-small ; is-locally-small)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import DomainTheory.Basics.Dcpo pt fe 𝓥

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

∐-family-＝ : (𝓓 : DCPO {𝓤} {𝓣}) {I : 𝓥 ̇ } {α β : I → ⟨ 𝓓 ⟩}
             (p : α ＝ β) (δ : is-Directed 𝓓 α)
           → ∐ 𝓓 {I} {α} δ ＝ ∐ 𝓓 {I} {β} (transport (is-Directed 𝓓) p δ)
∐-family-＝ 𝓓 {I} {α} {α} refl δ = refl

to-continuous-function-＝ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                           {f g : DCPO[ 𝓓 , 𝓔 ]}
                         → [ 𝓓 , 𝓔 ]⟨ f ⟩ ∼ [ 𝓓 , 𝓔 ]⟨ g ⟩
                         → f ＝ g
to-continuous-function-＝ 𝓓 𝓔 h =
 to-subtype-＝ (being-continuous-is-prop 𝓓 𝓔) (dfunext fe h)

＝-to-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩} → x ＝ y → x ⊑⟨ 𝓓 ⟩ y
＝-to-⊑ 𝓓 {x} {x} refl = reflexivity 𝓓 x

＝-to-⊒ : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩} → y ＝ x → x ⊑⟨ 𝓓 ⟩ y
＝-to-⊒ 𝓓 p = ＝-to-⊑ 𝓓 (p ⁻¹)

∐-independent-of-directedness-witness : (𝓓 : DCPO {𝓤} {𝓣})
                                        {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
                                        (δ ε : is-Directed 𝓓 α)
                                      → ∐ 𝓓 δ ＝ ∐ 𝓓 ε
∐-independent-of-directedness-witness 𝓓 {I} {α} δ ε = ap (∐ 𝓓) p
 where
  p : δ ＝ ε
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
   a : y ＝ ∐ 𝓓 δ
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
                     (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
                   → is-Directed 𝓓 α
                   → is-Directed 𝓔 ([ 𝓓 , 𝓔 ]⟨ f ⟩ ∘ α)
image-is-directed' 𝓓 𝓔 f {I} {α} δ = image-is-directed 𝓓 𝓔 m δ
 where
  m : is-monotone 𝓓 𝓔 [ 𝓓 , 𝓔 ]⟨ f ⟩
  m = monotone-if-continuous 𝓓 𝓔 f

continuous-∐-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                 (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
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
                 (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
                 (δ : is-Directed 𝓓 α)
               → ∐ 𝓔 (image-is-directed' 𝓓 𝓔 f δ) ⊑⟨ 𝓔 ⟩ [ 𝓓 , 𝓔 ]⟨ f ⟩ (∐ 𝓓 δ)
continuous-∐-⊒ 𝓓 𝓔 (f , c) {I} {α} δ =
 ∐-is-lowerbound-of-upperbounds 𝓔 ε (f (∐ 𝓓 δ)) u
  where
   ε : is-Directed 𝓔 (f ∘ α)
   ε = image-is-directed' 𝓓 𝓔 (f , c) δ
   u : (i : I) → f (α i) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 δ)
   u i = sup-is-upperbound (underlying-order 𝓔) (c I α δ) i

continuous-∐-＝ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                 (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
                 (δ : is-Directed 𝓓 α)
               → [ 𝓓 , 𝓔 ]⟨ f ⟩ (∐ 𝓓 δ) ＝ ∐ 𝓔 (image-is-directed' 𝓓 𝓔 f δ)
continuous-∐-＝ 𝓓 𝓔 (f , c) {I} {α} δ =
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
                                    {e : ⟨ 𝓔 ⟩} → is-continuous 𝓓 𝓔 (λ d → e)
constant-functions-are-continuous 𝓓 𝓔 {e} I α δ = u , v
 where
  u : (i : I) → e ⊑⟨ 𝓔 ⟩ e
  u i = reflexivity 𝓔 e
  v : (y : ⟨ 𝓔 ⟩) → ((i : I) → e ⊑⟨ 𝓔 ⟩ y) → e ⊑⟨ 𝓔 ⟩ y
  v y l  = ∥∥-rec (prop-valuedness 𝓔 e y) l (inhabited-if-Directed 𝓓 α δ)

id-is-monotone : (𝓓 : DCPO {𝓤} {𝓣}) → is-monotone 𝓓 𝓓 id
id-is-monotone 𝓓 x y l = l

id-is-continuous : (𝓓 : DCPO {𝓤} {𝓣}) → is-continuous 𝓓 𝓓 id
id-is-continuous 𝓓 = continuity-criterion 𝓓 𝓓 id (id-is-monotone 𝓓) γ
 where
  γ : (I : 𝓥 ̇ )(α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
    → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (image-is-directed 𝓓 𝓓 (λ x y l → l) δ)
  γ I α δ = ＝-to-⊑ 𝓓 (∐-independent-of-directedness-witness 𝓓
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
  ψ : (I : 𝓥 ̇ )(α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
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
    l₃ = ＝-to-⊑ 𝓔' (∐-independent-of-directedness-witness 𝓔' εg ε)

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
                ((d : ⟨ 𝓓 ⟩) → g (f d) ＝ d)
              × ((e : ⟨ 𝓔 ⟩) → f (g e) ＝ e)
              × is-continuous 𝓓 𝓔 f
              × is-continuous 𝓔 𝓓 g

is-deflation : (𝓓 : DCPO {𝓤} {𝓣}) → DCPO[ 𝓓 , 𝓓 ] → 𝓤 ⊔ 𝓣 ̇
is-deflation 𝓓 f = (x : ⟨ 𝓓 ⟩) → [ 𝓓 , 𝓓 ]⟨ f ⟩ x ⊑⟨ 𝓓 ⟩ x

is-continuous-retract : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                      → DCPO[ 𝓓 , 𝓔 ]
                      → DCPO[ 𝓔 , 𝓓 ]
                      → 𝓤 ̇
is-continuous-retract 𝓓 𝓔 (σ , _) (ρ , _) = (x : ⟨ 𝓓 ⟩) → ρ (σ x) ＝ x

record _continuous-retract-of_
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'}) : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇  where
  field
   s : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
   r : ⟨ 𝓔 ⟩ → ⟨ 𝓓 ⟩
   s-section-of-r : r ∘ s ∼ id
   s-is-continuous : is-continuous 𝓓 𝓔 s
   r-is-continuous : is-continuous 𝓔 𝓓 r

  𝕤 : DCPO[ 𝓓 , 𝓔 ]
  𝕤 = s , s-is-continuous

  𝕣 : DCPO[ 𝓔 , 𝓓 ]
  𝕣 = r , r-is-continuous

is-embedding-projection : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                        → DCPO[ 𝓓 , 𝓔 ]
                        → DCPO[ 𝓔 , 𝓓 ]
                        → 𝓤 ⊔ 𝓤' ⊔ 𝓣' ̇
is-embedding-projection 𝓓 𝓔 ε π =
 is-continuous-retract 𝓓 𝓔 ε π × is-deflation 𝓔 (DCPO-∘ 𝓔 𝓓 𝓔 π ε)

record embedding-projection-pair-between
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'}) : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇  where
  field
   e : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
   p : ⟨ 𝓔 ⟩ → ⟨ 𝓓 ⟩
   e-section-of-p : p ∘ e ∼ id
   e-p-deflation : (y : ⟨ 𝓔 ⟩) → e (p y) ⊑⟨ 𝓔 ⟩ y
   e-is-continuous : is-continuous 𝓓 𝓔 e
   p-is-continuous : is-continuous 𝓔 𝓓 p

  𝕖 : DCPO[ 𝓓 , 𝓔 ]
  𝕖 = e , e-is-continuous

  𝕡 : DCPO[ 𝓔 , 𝓓 ]
  𝕡 = p , p-is-continuous


\end{code}

Many examples of dcpos conveniently happen to be locally small.

We present and prove the equivalence of three definitions:
- our main one, is-locally-small, which uses a record so that we have convenient
  helper functions;
- a second one, is-locally-small-Σ, which is like the above but uses a Σ-type
  rather than a record;
- a third one, is-locally-small', which arguably looks more like the familiar
  categorical notion of a locally small category.

To prove their equivalence, we prove a general lemma on small-valued binary
relations.

\begin{code}

is-small : (X : 𝓤 ̇ ) → 𝓥 ⁺ ⊔ 𝓤 ̇
is-small X = X is 𝓥 small

small-binary-relation-equivalence : {X : 𝓤 ̇ } {Y : 𝓦 ̇ } {R : X → Y → 𝓣 ̇ }
                                  → ((x : X) (y : Y) → is-small (R x y))
                                  ≃ (Σ Rₛ ꞉ (X → Y → 𝓥 ̇ ) ,
                                      ((x : X) (y : Y) → Rₛ x y ≃ R x y))
small-binary-relation-equivalence {𝓤} {𝓦} {𝓣} {X} {Y} {R} =
 ((x : X) (y : Y)    → is-small (R x y))                            ≃⟨ I   ⟩
 ((((x , y) : X × Y) → is-small (R x y)))                           ≃⟨ II  ⟩
 (Σ R' ꞉ (X × Y → 𝓥 ̇ ) , (((x , y) : X × Y) → R' (x , y) ≃ R x y)) ≃⟨ III ⟩
 (Σ R' ꞉ (X × Y → 𝓥 ̇ ) , ((x : X) (y : Y) → R' (x , y) ≃ R x y))   ≃⟨ IV  ⟩
 (Σ Rₛ ꞉ (X → Y → 𝓥 ̇ ) , ((x : X) (y : Y) → Rₛ x y ≃ R x y))       ■
  where
   φ : {𝓤 𝓥 𝓦 : Universe}
       {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : (Σ x ꞉ X , Y x) → 𝓦 ̇ }
     → Π Z ≃ (Π x ꞉ X , Π y ꞉ Y x , Z (x , y))
   φ = curry-uncurry fe'
   I   = ≃-sym φ
   II  = ΠΣ-distr-≃
   III = Σ-cong (λ R → φ)
   IV  = Σ-change-of-variable (λ R' → (x : X) (y : Y) → R' x y ≃ R x y)
          ⌜ φ ⌝ (⌜⌝-is-equiv φ)

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 record is-locally-small : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
  field
   _⊑ₛ_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ̇
   ⊑ₛ-≃-⊑ : {x y : ⟨ 𝓓 ⟩} → x ⊑ₛ y ≃ x ⊑⟨ 𝓓 ⟩ y

  ⊑ₛ-to-⊑ : {x y : ⟨ 𝓓 ⟩} → x ⊑ₛ y → x ⊑⟨ 𝓓 ⟩ y
  ⊑ₛ-to-⊑ = ⌜ ⊑ₛ-≃-⊑ ⌝

  ⊑-to-⊑ₛ : {x y : ⟨ 𝓓 ⟩} → x ⊑⟨ 𝓓 ⟩ y → x ⊑ₛ y
  ⊑-to-⊑ₛ = ⌜ ⊑ₛ-≃-⊑ ⌝⁻¹

  ⊑ₛ-is-prop-valued : (x y : ⟨ 𝓓 ⟩) → is-prop (x ⊑ₛ y)
  ⊑ₛ-is-prop-valued x y = equiv-to-prop ⊑ₛ-≃-⊑ (prop-valuedness 𝓓 x y)

  transitivityₛ : (x : ⟨ 𝓓 ⟩) {y z : ⟨ 𝓓 ⟩}
                → x ⊑ₛ y → y ⊑ₛ z → x ⊑ₛ z
  transitivityₛ x {y} {z} u v = ⌜ ⊑ₛ-≃-⊑ ⌝⁻¹
                                 (transitivity 𝓓 x y z
                                               (⌜ ⊑ₛ-≃-⊑ ⌝ u)
                                               (⌜ ⊑ₛ-≃-⊑ ⌝ v))

  syntax transitivityₛ x u v = x ⊑ₛ[ u ] v
  infixr 0 transitivityₛ

  reflexivityₛ : (x : ⟨ 𝓓 ⟩) → x ⊑ₛ x
  reflexivityₛ x = ⌜ ⊑ₛ-≃-⊑ ⌝⁻¹ (reflexivity 𝓓 x)

  syntax reflexivityₛ x = x ∎ₛ
  infix 1 reflexivityₛ

\end{code}

This ends our helper function for the record and we proceed by giving the
alternative definitions of local smallness and proving their equivalence.

\begin{code}

 is-locally-small-Σ : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 is-locally-small-Σ =
   Σ _⊑ₛ_ ꞉ (⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ̇ ) , ((x y : ⟨ 𝓓 ⟩) → (x ⊑ₛ y) ≃ (x ⊑⟨ 𝓓 ⟩ y))

 is-locally-small-record-equivalence : is-locally-small ≃ is-locally-small-Σ
 is-locally-small-record-equivalence = qinveq f (g , (λ _ → refl) , (λ _ → refl))
  where
   f : is-locally-small → is-locally-small-Σ
   f ls = _⊑ₛ_ , (λ x y → ⊑ₛ-≃-⊑)
    where
     open is-locally-small ls
   g : is-locally-small-Σ → is-locally-small
   g ls = record { _⊑ₛ_ = pr₁ ls ; ⊑ₛ-≃-⊑ = (λ {x} {y} → pr₂ ls x y) }

 is-locally-small' : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 is-locally-small' = (x y : ⟨ 𝓓 ⟩) → is-small (x ⊑⟨ 𝓓 ⟩ y)

 local-smallness-equivalent-definitions : is-locally-small ≃ is-locally-small'
 local-smallness-equivalent-definitions =
  is-locally-small-record-equivalence ● ≃-sym (small-binary-relation-equivalence)

 being-locally-small'-is-prop : PropExt → is-prop is-locally-small'
 being-locally-small'-is-prop pe =
  Π₂-is-prop fe (λ x y → prop-being-small-is-prop pe fe'
                          (x ⊑⟨ 𝓓 ⟩ y) (prop-valuedness 𝓓 x y))

 being-locally-small-is-prop : PropExt → is-prop is-locally-small
 being-locally-small-is-prop pe =
  equiv-to-prop local-smallness-equivalent-definitions
                (being-locally-small'-is-prop pe)

\end{code}

Being locally small is preserved by continuous retracts.

\begin{code}

local-smallness-preserved-by-continuous-retract :
   (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
 → 𝓓 continuous-retract-of 𝓔
 → is-locally-small 𝓔
 → is-locally-small 𝓓
local-smallness-preserved-by-continuous-retract 𝓓 𝓔 ρ ls =
 ⌜ local-smallness-equivalent-definitions 𝓓 ⌝⁻¹ γ
  where
   open _continuous-retract-of_ ρ
   open is-locally-small ls
   γ : is-locally-small' 𝓓
   γ x y = (s x ⊑ₛ s y , g)
    where
     g : (s x ⊑ₛ s y) ≃ (x ⊑⟨ 𝓓 ⟩ y)
     g = logically-equivalent-props-are-equivalent
          (equiv-to-prop ⊑ₛ-≃-⊑
            (prop-valuedness 𝓔 (s x) (s y)))
          (prop-valuedness 𝓓 x y)
          ⦅⇒⦆ ⦅⇐⦆
      where
       ⦅⇒⦆ : (s x ⊑ₛ s y) → (x ⊑⟨ 𝓓 ⟩ y)
       ⦅⇒⦆ l = x      ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
              r (s x) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
              r (s y) ⊑⟨ 𝓓 ⟩[ ⦅3⦆ ]
              y       ∎⟨ 𝓓 ⟩
        where
         ⦅1⦆ = ＝-to-⊒ 𝓓 (s-section-of-r x)
         ⦅2⦆ = monotone-if-continuous 𝓔 𝓓 𝕣 (s x) (s y) (⊑ₛ-to-⊑ l)
         ⦅3⦆ = ＝-to-⊑ 𝓓 (s-section-of-r y)
       ⦅⇐⦆ : (x ⊑⟨ 𝓓 ⟩ y) → (s x ⊑ₛ s y)
       ⦅⇐⦆ l = ⊑-to-⊑ₛ (monotone-if-continuous 𝓓 𝓔 𝕤 x y l)

\end{code}

Moving on from local smallness, we present a few useful lemmas on cofinality and
(joins of) directed families.

\begin{code}

semidirected-if-bicofinal : (𝓓 : DCPO {𝓤} {𝓣}) {I J : 𝓦 ̇ }
                            (α : I → ⟨ 𝓓 ⟩) (β : J → ⟨ 𝓓 ⟩)
                          → ((i : I) → ∃ j ꞉ J , α i ⊑⟨ 𝓓 ⟩ β j)
                          → ((j : J) → ∃ i ꞉ I , β j ⊑⟨ 𝓓 ⟩ α i)
                          → is-semidirected (underlying-order 𝓓) α
                          → is-semidirected (underlying-order 𝓓) β
semidirected-if-bicofinal 𝓓 {I} {J} α β α-cofinal-in-β β-cofinal-in-α σ j₁ j₂ =
 ∥∥-rec₂ ∃-is-prop f (β-cofinal-in-α j₁) (β-cofinal-in-α j₂)
  where
   f : (Σ i₁ ꞉ I , β j₁ ⊑⟨ 𝓓 ⟩ α i₁)
     → (Σ i₂ ꞉ I , β j₂ ⊑⟨ 𝓓 ⟩ α i₂)
     → ∃ j ꞉ J , (β j₁ ⊑⟨ 𝓓 ⟩ β j) × (β j₂ ⊑⟨ 𝓓 ⟩ β j)
   f (i₁ , u₁) (i₂ , u₂) = ∥∥-rec ∃-is-prop g (σ i₁ i₂)
    where
     g : (Σ i ꞉ I , (α i₁ ⊑⟨ 𝓓 ⟩ α i) × (α i₂ ⊑⟨ 𝓓 ⟩ α i))
       → (∃ j ꞉ J , (β j₁ ⊑⟨ 𝓓 ⟩ β j) × (β j₂ ⊑⟨ 𝓓 ⟩ β j))
     g (i , v₁ , v₂) = ∥∥-functor h (α-cofinal-in-β i)
      where
       h : (Σ j ꞉ J , α i ⊑⟨ 𝓓 ⟩ β j)
         → (Σ j ꞉ J , (β j₁ ⊑⟨ 𝓓 ⟩ β j) × (β j₂ ⊑⟨ 𝓓 ⟩ β j))
       h (j , w) = (j , (β j₁ ⊑⟨ 𝓓 ⟩[ u₁ ]
                         α i₁ ⊑⟨ 𝓓 ⟩[ v₁ ]
                         α i  ⊑⟨ 𝓓 ⟩[ w ]
                         β j  ∎⟨ 𝓓 ⟩)
                      , (β j₂ ⊑⟨ 𝓓 ⟩[ u₂ ]
                         α i₂ ⊑⟨ 𝓓 ⟩[ v₂ ]
                         α i  ⊑⟨ 𝓓 ⟩[ w ]
                         β j  ∎⟨ 𝓓 ⟩))

directed-if-bicofinal : (𝓓 : DCPO {𝓤} {𝓣}) {I J : 𝓦 ̇ }
                        {α : I → ⟨ 𝓓 ⟩} {β : J → ⟨ 𝓓 ⟩}
                      → ((i : I) → ∃ j ꞉ J , α i ⊑⟨ 𝓓 ⟩ β j)
                      → ((j : J) → ∃ i ꞉ I , β j ⊑⟨ 𝓓 ⟩ α i)
                      → is-Directed 𝓓 α
                      → is-Directed 𝓓 β
directed-if-bicofinal 𝓓 {I} {J} {α} {β} κ₁ κ₂ δ =
 (γ , semidirected-if-bicofinal 𝓓 α β κ₁ κ₂ (semidirected-if-Directed 𝓓 α δ))
  where
   γ : ∥ J ∥
   γ = ∥∥-rec ∥∥-is-prop ϕ (inhabited-if-Directed 𝓓 α δ)
    where
     ϕ : I → ∥ J ∥
     ϕ i = ∥∥-functor pr₁ (κ₁ i)

∐-⊑-if-cofinal : (𝓓 : DCPO {𝓤} {𝓣}) {I J : 𝓥 ̇ }
                 {α : I → ⟨ 𝓓 ⟩} {β : J → ⟨ 𝓓 ⟩}
               → ((i : I) → ∃ j ꞉ J , α i ⊑⟨ 𝓓 ⟩ β j)
               → (δ : is-Directed 𝓓 α)
               → (ε : is-Directed 𝓓 β)
               → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
∐-⊑-if-cofinal 𝓓 {I} {J} {α} {β} α-cofinal-in-β δ ε =
 ∐-is-lowerbound-of-upperbounds 𝓓 δ (∐ 𝓓 ε) γ
  where
   γ : (i : I) → α i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
   γ i = ∥∥-rec (prop-valuedness 𝓓 (α i) (∐ 𝓓 ε)) ϕ (α-cofinal-in-β i)
    where
     ϕ : (Σ j ꞉ J , α i ⊑⟨ 𝓓 ⟩ β j)
       → α i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
     ϕ (j , u) = α i   ⊑⟨ 𝓓 ⟩[ u ]
                 β j   ⊑⟨ 𝓓 ⟩[ ∐-is-upperbound 𝓓 ε j ]
                 ∐ 𝓓 ε ∎⟨ 𝓓 ⟩

∐-＝-if-bicofinal : (𝓓 : DCPO {𝓤} {𝓣}) {I J : 𝓥 ̇ }
                   {α : I → ⟨ 𝓓 ⟩} {β : J → ⟨ 𝓓 ⟩}
                 → ((i : I) → ∃ j ꞉ J , α i ⊑⟨ 𝓓 ⟩ β j)
                 → ((j : J) → ∃ i ꞉ I , β j ⊑⟨ 𝓓 ⟩ α i)
                 → (δ : is-Directed 𝓓 α)
                 → (ε : is-Directed 𝓓 β)
                 → ∐ 𝓓 δ ＝ ∐ 𝓓 ε
∐-＝-if-bicofinal 𝓓 κ₁ κ₂ δ ε =
 antisymmetry 𝓓 (∐ 𝓓 δ) (∐ 𝓓 ε) (∐-⊑-if-cofinal 𝓓 κ₁ δ ε)
                                (∐-⊑-if-cofinal 𝓓 κ₂ ε δ)

\end{code}

Finally, we sometimes wish to reindex a directed family by another equivalent
type. The resulting family is of course directed again and has the same
supremum, which is what we prove here.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {I : 𝓦 ̇ } {J : 𝓦' ̇ }
        (ρ : I ≃ J)
        (α : I → ⟨ 𝓓 ⟩)
       where

 reindexed-family : J → ⟨ 𝓓 ⟩
 reindexed-family = α ∘ ⌜ ρ ⌝⁻¹

 reindexed-family-is-directed : is-Directed 𝓓 α
                              → is-Directed 𝓓 reindexed-family
 reindexed-family-is-directed δ = J-inh , β-semidirected
  where
   J-inh : ∥ J ∥
   J-inh = ∥∥-functor ⌜ ρ ⌝ (inhabited-if-Directed 𝓓 α δ)
   β : J → ⟨ 𝓓 ⟩
   β = reindexed-family
   β-semidirected : is-semidirected (underlying-order 𝓓) β
   β-semidirected j₁ j₂ =
    ∥∥-functor r (semidirected-if-Directed 𝓓 α δ (⌜ ρ ⌝⁻¹ j₁) (⌜ ρ ⌝⁻¹ j₂))
     where
      r : (Σ i ꞉ I , (β j₁ ⊑⟨ 𝓓 ⟩ α i) × (β j₂ ⊑⟨ 𝓓 ⟩ α i))
        → (Σ j ꞉ J , (β j₁ ⊑⟨ 𝓓 ⟩ β j) × (β j₂ ⊑⟨ 𝓓 ⟩ β j))
      r (i , l₁ , l₂) = (⌜ ρ ⌝ i
                        , (β j₁                    ⊑⟨ 𝓓 ⟩[ l₁ ]
                           α i                     ⊑⟨ 𝓓 ⟩[ k ]
                           (α ∘ ⌜ ρ ⌝⁻¹ ∘ ⌜ ρ ⌝) i ∎⟨ 𝓓 ⟩)
                        , (β j₂                    ⊑⟨ 𝓓 ⟩[ l₂ ]
                           α i                     ⊑⟨ 𝓓 ⟩[ k ]
                           (α ∘ ⌜ ρ ⌝⁻¹ ∘ ⌜ ρ ⌝) i ∎⟨ 𝓓 ⟩))
       where
        k = ＝-to-⊒ 𝓓
             (ap α (inverses-are-retractions ⌜ ρ ⌝ (⌜⌝-is-equiv ρ) i))

 reindexed-family-sup : (x : ⟨ 𝓓 ⟩)
                      → is-sup (underlying-order 𝓓) x α
                      → is-sup (underlying-order 𝓓) x (reindexed-family)
 reindexed-family-sup x x-is-sup = ub , lb-of-ubs
  where
   β : J → ⟨ 𝓓 ⟩
   β = reindexed-family
   ub : is-upperbound (underlying-order 𝓓) x β
   ub i = sup-is-upperbound (underlying-order 𝓓) x-is-sup (⌜ ρ ⌝⁻¹ i)
   lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order 𝓓) x β
   lb-of-ubs y y-is-ub = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓)
                          x-is-sup y lemma
    where
     lemma : is-upperbound (underlying-order 𝓓) y α
     lemma i = α i         ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
               β (⌜ ρ ⌝ i) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
               y           ∎⟨ 𝓓 ⟩
      where
       ⦅1⦆ = ＝-to-⊒ 𝓓
             (ap α (inverses-are-retractions ⌜ ρ ⌝ (⌜⌝-is-equiv ρ) i))
       ⦅2⦆ = y-is-ub (⌜ ρ ⌝ i)

\end{code}
