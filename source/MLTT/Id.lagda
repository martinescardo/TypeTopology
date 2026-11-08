Martin Escardo, original date unknown.

Identity type.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Id where

open import MLTT.Universes
open import MLTT.Pi

open import MLTT.Identity-Type renaming (_＝_ to infix 0 _＝_) public

𝓻𝓮𝒻𝓵 : {X : 𝓤 ̇ } (x : X) → x ＝ x
𝓻𝓮𝒻𝓵 x = refl {_} {_} {x}

Id : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
Id = _＝_

Jbased : {X : 𝓤 ̇ } (x : X) (A : (y : X) → x ＝ y → 𝓥 ̇ )
       → A x refl → (y : X) (r : x ＝ y) → A y r
Jbased x A b x refl = b

J : {X : 𝓤 ̇ } (A : (x y : X) → x ＝ y → 𝓥 ̇ )
  → ((x : X) → A x x refl) → {x y : X} (r : x ＝ y) → A x y r
J A f {x} {y} = Jbased x (A x) (f x) y

private

 transport' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
            → x ＝ y → A x → A y
 transport' A {x} {y} p a = Jbased x (λ y p → A y) a y p


transport : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
          → x ＝ y → A x → A y
transport A refl = id

lhs : {X : 𝓤 ̇ } {x y : X} → x ＝ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇ } {x y : X} → x ＝ y → X
rhs {𝓤} {X} {x} {y} p = y

_∙_ : {X : 𝓤 ̇ } {x y z : X} → x ＝ y → y ＝ z → x ＝ z
p ∙ q = transport (lhs p ＝_) q p

_⁻¹ : {X : 𝓤 ̇ } → {x y : X} → x ＝ y → y ＝ x
p ⁻¹ = transport (_＝ lhs p) p refl

ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} → x ＝ x' → f x ＝ f x'
ap f p = transport (λ - → f (lhs p) ＝ f -) p refl

transport⁻¹ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} → x ＝ y → A y → A x
transport⁻¹ B p = transport B (p ⁻¹)

\end{code}

Added 4th Feb 2025. For the above definition, we have the definitional
equality p ∙ refl = p. In order to simplify some computations, we
include a version with refl ∙ q = q definitionally.

\begin{code}

_∙'_ : {X : 𝓤 ̇ } {x y z : X} → x ＝ y → y ＝ z → x ＝ z
refl ∙' q = q

∙-agrees-with-∙' : {X : 𝓤 ̇ } {x y z : X} (p : x ＝ y) (q : y ＝ z)
                 → p ∙' q ＝ p ∙ q
∙-agrees-with-∙' refl refl = refl

\end{code}

End of addition.

\begin{code}

module _ {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } where

 infix  4 _∼_

 _∼_ :  Π A → Π A → 𝓤 ⊔ 𝓥 ̇
 f ∼ g = ∀ x → f x ＝ g x

 ∼-refl : {f : Π A} → f ∼ f
 ∼-refl x = refl

 ∼-trans : {f g h : Π A} → f ∼ g → g ∼ h → f ∼ h
 ∼-trans h k x = h x ∙ k x

 ∼-sym : {f g : Π A} → f ∼ g → g ∼ f
 ∼-sym h x = (h x)⁻¹

 ∼-ap : {E : 𝓦 ̇ } (F : E → Π A) {e e' : E} → e ＝ e' → F e ∼ F e'
 ∼-ap F p x = ap (λ - → F - x) p

∼-ap-∘ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
         {f g : X → Y} (h : Y → Z)
       → f ∼ g → h ∘ f ∼ h ∘ g
∼-ap-∘ h p x = ap h (p x)

\end{code}

Notations to make some proofs more readable:

\begin{code}

by-definition : {X : 𝓤 ̇ } {x : X} → x ＝ x
by-definition = refl

by-construction : {X : 𝓤 ̇ } {x : X} → x ＝ x
by-construction = refl

by-assumption : {X : 𝓤 ̇ } {x : X} → x ＝ x
by-assumption = refl

\end{code}

Standard syntax for equality chain reasoning:

\begin{code}

_＝⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x ＝ y → y ＝ z → x ＝ z
_ ＝⟨ p ⟩ q = p ∙ q

_∎ : {X : 𝓤 ̇ } (x : X) → x ＝ x
_∎ _ = refl


module _ {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } where

 _∼⟨_⟩_ : (f : Π A) {g h : Π A} → f ∼ g → g ∼ h → f ∼ h
 _ ∼⟨ p ⟩ q = ∼-trans p q

 _∼∎ : (f : Π A) → f ∼ f
 _∼∎ _ = ∼-refl

 infix  1 _∼∎
 infixr 0 _∼⟨_⟩_

\end{code}

Added by Carlo Angiuli on November 20, 2025.

Special syntax for definitional steps in equality chain reasoning:

\begin{code}

_＝⟨refl⟩_ : {X : 𝓤 ̇ } (x : X) {y : X} → x ＝ y → x ＝ y
_ ＝⟨refl⟩ p = p

_＝⟨by-definition⟩_ : {X : 𝓤 ̇ } (x : X) {y : X} → x ＝ y → x ＝ y
_＝⟨by-definition⟩_ = _＝⟨refl⟩_

\end{code}

End of addition.

Fixities:

\begin{code}

infix  3  _⁻¹
infix  1 _∎
infixr 0 _＝⟨_⟩_
infixr 0 _＝⟨refl⟩_
infixr 0 _＝⟨by-definition⟩_
infixl 2 _∙_

\end{code}
