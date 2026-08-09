Martin Escardo, May 2020

We now consider σ-frames. A σ-frame is a poset with countable joins
and finite meets such that binary meets distribute over countable
joins. Countable joins are exhausted by finitely indexed joins and
ℕ-indexed joins. But, apart from the empty join, all finite joins can
be expressed as ℕ-indexed joins (of eventually constant sequences) and
hence it is enough to consider the empty join (a bottom element) and
ℕ-indexed joins, which is the approach we take here.

We denote the empty meet (a top element) by ⊤, the binary meet by ∧,
the empty join (a bottom element) by ⊥, and the ℕ-indexed join by
⋁. These are unary, binary and ℕ-ary operations.

TODO. Currently the order is derived from the binary meet. However,
for size reasons, it would be good to add the other as a separate
relation coinciding with the binary meet order, similarly to what we
did with σ-sup-lattices. Perhaps it would be better to define a
σ-frame as a σ-sup-lattice equipped with a binary meet.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module OrderedTypes.sigma-frame (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Equiv hiding (_≅_)
open import UF.SIP
open import UF.SIP-Examples
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Univalence

σ-frame-structure : 𝓤 ̇ → 𝓤 ̇
σ-frame-structure X = X × (X → X → X) × X × ((ℕ → X) → X)

σ-frame-axioms : (X : 𝓤 ̇ ) → σ-frame-structure X → 𝓤 ̇
σ-frame-axioms {𝓤} X (⊤ , _∧_ , ⊥ , ⋁) = I × II × III × IV × V × VI × VII × VIII × IX
 where
  _≤_ : X → X → 𝓤 ̇
  x ≤ y = x ∧ y ＝ x

  I    = is-set X
  II   = (x : X) → x ∧ x ＝ x
  III  = (x y : X) → x ∧ y ＝ y ∧ x
  IV   = (x y z : X) → x ∧ (y ∧ z) ＝ (x ∧ y) ∧ z
  V    = (x : X) → ⊥ ≤ x
  VI   = (x : X) → x ≤ ⊤
  VII  = (x : X) (y : ℕ → X) → x ∧ (⋁ y) ＝ ⋁ (n ↦ (x ∧ y n))
  VIII = (x : ℕ → X) (n : ℕ) → x n ≤ ⋁ x
  IX   = (x : ℕ → X) (u : X) → ((n : ℕ) → x n ≤ u) → ⋁ x ≤ u
\end{code}

Axioms I-IV say that (X , ⊤ , ∧) is a bounded semilattice, axiom VII
says that ⋁ gives least upper bounds w.r.t. the induced partial order,
and axiom VI says that binary meets distribute over countable joins.

\begin{code}

σ-frame-axioms-is-prop : (X : 𝓤 ̇ ) (s : σ-frame-structure X)
                       → is-prop (σ-frame-axioms X s)
σ-frame-axioms-is-prop X (⊤ , _∧_ , ⊥ , ⋁) = prop-criterion δ
 where
  δ : σ-frame-axioms X (⊤ , _∧_ , ⊥ , ⋁) → is-prop (σ-frame-axioms X (⊤ , _∧_ , ⊥ , ⋁))
  δ (i , ii-ix) =
    ×-is-prop (being-set-is-prop fe)
   (×-is-prop (Π-is-prop fe (λ x →  i {x ∧ x} {x}))
   (×-is-prop (Π-is-prop fe (λ x →
               Π-is-prop fe (λ y →  i {x ∧ y} {y ∧ x})))
   (×-is-prop (Π-is-prop fe (λ x →
               Π-is-prop fe (λ y →
               Π-is-prop fe (λ z →  i {x ∧ (y ∧ z)} {(x ∧ y) ∧ z}))))
   (×-is-prop (Π-is-prop fe (λ x →  i {⊥ ∧ x} {⊥}))
   (×-is-prop (Π-is-prop fe (λ x →  i {x ∧ ⊤} {x}))
   (×-is-prop (Π-is-prop fe (λ x →
               Π-is-prop fe (λ y →  i {x ∧ ⋁ y} {⋁ (n ↦ x ∧ y n)})))
   (×-is-prop (Π-is-prop fe (λ x →
               Π-is-prop fe (λ n → i {x n ∧ ⋁ x} {x n})))
              (Π-is-prop fe (λ x →
               Π-is-prop fe (λ u →
               Π-is-prop fe (λ _ →  i {⋁ x ∧ u} {⋁ x})))))))))))

σ-Frame : (𝓤 : Universe) → 𝓤 ⁺ ̇
σ-Frame 𝓤 = Σ A ꞉ 𝓤 ̇ , Σ s ꞉ σ-frame-structure A , σ-frame-axioms A s

⟨_⟩ : σ-Frame 𝓤 → 𝓤 ̇
⟨ A , _ ⟩ = A

is-σ-frame-homomorphism : (𝓐 : σ-Frame 𝓤) (𝓑 : σ-Frame 𝓥)
                        → (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → 𝓤 ⊔ 𝓥 ̇
is-σ-frame-homomorphism  (A , (⊤ , _∧_ , ⊥ , ⋁) , _) (_ , (⊤' , _∧'_ , ⊥' , ⋁') , _) f =
    (f ⊤ ＝ ⊤')
  × ((λ (a b : A) → f (a ∧ b)) ＝ (λ a b → f a ∧' f b))
  × (f ⊥ ＝ ⊥')
  × ((λ (𝕒 : ℕ → A) → f (⋁ 𝕒)) ＝ (λ 𝕒 → ⋁' (n ↦ f (𝕒 n))))

_≅[σ-Frame]_ : σ-Frame 𝓤 → σ-Frame 𝓤 → 𝓤 ̇
𝓐 ≅[σ-Frame] 𝓑 = Σ f ꞉ (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩), is-equiv f × is-σ-frame-homomorphism 𝓐 𝓑 f

characterization-of-σ-Frame-＝ : is-univalent 𝓤
                              → (A B : σ-Frame 𝓤)
                              → (A ＝ B) ≃ (A ≅[σ-Frame] B)
characterization-of-σ-Frame-＝ ua =
  sip.characterization-of-＝ ua
   (sip-with-axioms.add-axioms
      σ-frame-axioms
      σ-frame-axioms-is-prop
     (sip-join.join
       pointed-type.sns-data
     (sip-join.join
       ∞-magma.sns-data
       (sip-join.join
        pointed-type.sns-data
        (∞-bigmagma.sns-data ℕ)))))

\end{code}

We name the projections (we wouldn't need to do this if we had used a
record, but we need Σ for our approach to SIP):

\begin{code}

⊤⟨_⟩ : (𝓐 : σ-Frame 𝓤) → ⟨ 𝓐 ⟩
⊤⟨ A , (⊤ , _∧_ , ⊥ , ⋁) , _ ⟩ = ⊤

meet : (𝓐 : σ-Frame 𝓤) → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩
meet (A , (⊤ , _∧_ , ⊥ , ⋁) , _) = _∧_

syntax meet 𝓐 x y = x ∧⟨ 𝓐 ⟩ y

⊥⟨_⟩ : (𝓐 : σ-Frame 𝓤) → ⟨ 𝓐 ⟩
⊥⟨ A , (⊤ , _∧_ , ⊥ , ⋁) , _ ⟩ = ⊥

⋁⟨_⟩ : (𝓐 : σ-Frame 𝓤) → (ℕ → ⟨ 𝓐 ⟩) → ⟨ 𝓐 ⟩
⋁⟨ A , (⊤ , _∧_ , ⊥ , ⋁) , _ ⟩ = ⋁

⟨_⟩-is-set : (𝓐 : σ-Frame 𝓤) → is-set ⟨ 𝓐 ⟩
⟨ A , _ , (i , ii , iii , iv , v , vi , vii , viii , ix) ⟩-is-set = i

⟨_⟩-idempotency : (𝓐 : σ-Frame 𝓤) (a : ⟨ 𝓐 ⟩)
                → a ∧⟨ 𝓐 ⟩ a ＝ a
⟨ A , _ , (i , ii , iii , iv , v , vi , vii , viii , ix) ⟩-idempotency = ii

⟨_⟩-commutativity : (𝓐 : σ-Frame 𝓤) (a b : ⟨ 𝓐 ⟩)
                  → a ∧⟨ 𝓐 ⟩ b ＝ b ∧⟨ 𝓐 ⟩ a
⟨ A , _ , (i , ii , iii , iv , v , vi , vii , viii , ix) ⟩-commutativity = iii

⟨_⟩-associativity : (𝓐 : σ-Frame 𝓤) (a b c : ⟨ 𝓐 ⟩)
                  → a ∧⟨ 𝓐 ⟩ (b ∧⟨ 𝓐 ⟩ c) ＝ (a ∧⟨ 𝓐 ⟩ b) ∧⟨ 𝓐 ⟩ c
⟨ A , _ , (i , ii , iii , iv , v , vi , vii , viii , ix) ⟩-associativity = iv

order : (𝓐 : σ-Frame 𝓤)
   → ⟨ 𝓐 ⟩ → ⟨ 𝓐 ⟩ → 𝓤 ̇
order 𝓐 a b = a ∧⟨ 𝓐 ⟩ b ＝ a

syntax order 𝓐 x y = x ≤⟨ 𝓐 ⟩ y

⟨_⟩-⊥-minimum : (𝓐 : σ-Frame 𝓤) (a : ⟨ 𝓐 ⟩)
              → ⊥⟨ 𝓐 ⟩ ≤⟨ 𝓐 ⟩ a
⟨ A , _ , (i , ii , iii , iv , v , vi , vii , viii , ix) ⟩-⊥-minimum = v

⟨_⟩-⊤-maximum : (𝓐 : σ-Frame 𝓤) (a : ⟨ 𝓐 ⟩)
              → a ≤⟨ 𝓐 ⟩ ⊤⟨ 𝓐 ⟩
⟨ A , _ , (i , ii , iii , iv , v , vi , vii , viii , ix) ⟩-⊤-maximum = vi

⟨_⟩-distributivity : (𝓐 : σ-Frame 𝓤) (a : ⟨ 𝓐 ⟩) (b : ℕ → ⟨ 𝓐 ⟩)
                   → a ∧⟨ 𝓐 ⟩ (⋁⟨ 𝓐 ⟩ b) ＝ ⋁⟨ 𝓐 ⟩ (n ↦ (a ∧⟨ 𝓐 ⟩ b n))
⟨ A , _ , (i , ii , iii , iv , v , vi , vii , viii , ix) ⟩-distributivity = vii

⟨_⟩-⋁-is-ub : (𝓐 : σ-Frame 𝓤) (a : ℕ → ⟨ 𝓐 ⟩) (n : ℕ)
            → a n ≤⟨ 𝓐 ⟩ ⋁⟨ 𝓐 ⟩ a
⟨ A , _ , (i , ii , iii , iv , v , vi , vii , viii , ix) ⟩-⋁-is-ub = viii

⟨_⟩-⋁-is-lb-of-ubs : (𝓐 : σ-Frame 𝓤) (a : ℕ → ⟨ 𝓐 ⟩) (u : ⟨ 𝓐 ⟩)
                   → ((n : ℕ) → a n ≤⟨ 𝓐 ⟩ u) → ⋁⟨ 𝓐 ⟩ a ≤⟨ 𝓐 ⟩ u
⟨ A , _ , (i , ii , iii , iv , v , vi , vii , viii , ix) ⟩-⋁-is-lb-of-ubs = ix

⟨_⟩-refl : (𝓐 : σ-Frame 𝓤) (a : ⟨ 𝓐 ⟩) → a ≤⟨ 𝓐 ⟩ a
⟨_⟩-refl 𝓐 a = ⟨ 𝓐 ⟩-idempotency a

⟨_⟩-trans : (𝓐 : σ-Frame 𝓤) (a b c : ⟨ 𝓐 ⟩) → a ≤⟨ 𝓐 ⟩ b → b ≤⟨ 𝓐 ⟩ c → a ≤⟨ 𝓐 ⟩ c
⟨_⟩-trans 𝓐 a b c l m = (a ∧⟨ 𝓐 ⟩ c)             ＝⟨ ap (λ - → - ∧⟨ 𝓐 ⟩ c) (l ⁻¹) ⟩
                         ((a ∧⟨ 𝓐 ⟩ b) ∧⟨ 𝓐 ⟩ c) ＝⟨ (⟨ 𝓐 ⟩-associativity a b c)⁻¹ ⟩
                         (a ∧⟨ 𝓐 ⟩ (b ∧⟨ 𝓐 ⟩ c)) ＝⟨ ap (λ - → a ∧⟨ 𝓐 ⟩ -) m ⟩
                         (a ∧⟨ 𝓐 ⟩ b)             ＝⟨ l ⟩
                         a                         ∎

⟨_⟩-antisym : (𝓐 : σ-Frame 𝓤) (a b : ⟨ 𝓐 ⟩) → a ≤⟨ 𝓐 ⟩ b → b ≤⟨ 𝓐 ⟩ a → a ＝ b
⟨_⟩-antisym 𝓐 a b l m = a            ＝⟨ l ⁻¹ ⟩
                        (a ∧⟨ 𝓐 ⟩ b) ＝⟨ ⟨ 𝓐 ⟩-commutativity a b ⟩
                        (b ∧⟨ 𝓐 ⟩ a) ＝⟨ m ⟩
                        b             ∎


being-σ-frame-homomorphism-is-prop : (𝓐 : σ-Frame 𝓤) (𝓑 : σ-Frame 𝓥)
                                   → (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
                                   → is-prop (is-σ-frame-homomorphism 𝓐 𝓑 f)
being-σ-frame-homomorphism-is-prop (_ , _ ,  _) (_ , _ , (i' , _)) f =
  ×-is-prop i'
 (×-is-prop (Π-is-set fe (λ a →
             Π-is-set fe (λ b → i')))
 (×-is-prop i' (Π-is-set fe (λ 𝕒 → i'))))

∘-σ-frame-homomorphism : (𝓐 : σ-Frame 𝓤) (𝓑 : σ-Frame 𝓥) (𝓒 : σ-Frame 𝓦)
                         (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) (g : ⟨ 𝓑 ⟩ → ⟨ 𝓒 ⟩)
                       → is-σ-frame-homomorphism 𝓐 𝓑 f
                       → is-σ-frame-homomorphism 𝓑 𝓒 g
                       → is-σ-frame-homomorphism 𝓐 𝓒 (g ∘ f)
∘-σ-frame-homomorphism 𝓐 𝓑 𝓒 f g (p₀ , q₀ , r₀ , s₀) (p₁ , q₁ , r₁ , s₁) = (p₂ , q₂ , r₂ , s₂)
 where
  p₂ = g (f ⊤⟨ 𝓐 ⟩) ＝⟨ ap g p₀ ⟩
       g ⊤⟨ 𝓑 ⟩     ＝⟨ p₁ ⟩
       ⊤⟨ 𝓒 ⟩       ∎

  q₂ = (λ (a b : ⟨ 𝓐 ⟩) → g (f (a ∧⟨ 𝓐 ⟩ b)))     ＝⟨ dfunext fe (λ a → dfunext fe (λ b → ap (λ - → g (- a b)) q₀)) ⟩
       (λ (a b : ⟨ 𝓐 ⟩) → g (f a ∧⟨ 𝓑 ⟩ f b))     ＝⟨ dfunext fe (λ a → dfunext fe (λ b → ap (λ - → - (f a) (f b)) q₁)) ⟩
       (λ (a b : ⟨ 𝓐 ⟩) → g (f a) ∧⟨ 𝓒 ⟩ g (f b)) ∎

  r₂ = g (f ⊥⟨ 𝓐 ⟩) ＝⟨ ap g r₀ ⟩
       g ⊥⟨ 𝓑 ⟩     ＝⟨ r₁ ⟩
       ⊥⟨ 𝓒 ⟩       ∎

  s₂ = (λ 𝕒 → g (f (⋁⟨ 𝓐 ⟩ 𝕒)))           ＝⟨ dfunext fe (λ 𝕒 → ap (λ - → g (- 𝕒)) s₀) ⟩
       (λ 𝕒 → g (⋁⟨ 𝓑 ⟩ (λ n → f (𝕒 n)))) ＝⟨ dfunext fe (λ 𝕒 → ap (λ - → - (λ n → f (𝕒 n))) s₁) ⟩
       (λ 𝕒 → ⋁⟨ 𝓒 ⟩ (λ n → g (f (𝕒 n)))) ∎

\end{code}

I think I prefer to work with pointwise homomorphisms:

\begin{code}
is-σ-frame-hom : (𝓐 : σ-Frame 𝓤) (𝓑 : σ-Frame 𝓥)
               → (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) → 𝓤 ⊔ 𝓥 ̇
is-σ-frame-hom  (_ , (⊤ , _∧_ , ⊥ , ⋁) , _) (_ , (⊤' , _∧'_ , ⊥' , ⋁') , _) f =
    (f ⊤ ＝ ⊤')
  × (∀ a b → f (a ∧ b) ＝ f a ∧' f b)
  × (f ⊥ ＝ ⊥')
  × (∀ 𝕒 → f (⋁ 𝕒) ＝ ⋁' (n ↦ f (𝕒 n)))

σ-frame-hom-⊤ : (𝓐 : σ-Frame 𝓤) (𝓑 : σ-Frame 𝓥)
              → (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
              → is-σ-frame-hom 𝓐 𝓑 f
              → f ⊤⟨ 𝓐 ⟩ ＝ ⊤⟨ 𝓑 ⟩
σ-frame-hom-⊤ 𝓐 𝓑 f (i , ii , iii , vi) = i

σ-frame-hom-∧ : (𝓐 : σ-Frame 𝓤) (𝓑 : σ-Frame 𝓥)
              → (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
              → is-σ-frame-hom 𝓐 𝓑 f
              → ∀ a b → f (a ∧⟨ 𝓐 ⟩ b) ＝ f a ∧⟨ 𝓑 ⟩ f b
σ-frame-hom-∧ 𝓐 𝓑 f (i , ii , iii , vi) = ii

σ-frame-hom-⊥ : (𝓐 : σ-Frame 𝓤) (𝓑 : σ-Frame 𝓥)
              → (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
              → is-σ-frame-hom 𝓐 𝓑 f
              → f ⊥⟨ 𝓐 ⟩ ＝ ⊥⟨ 𝓑 ⟩
σ-frame-hom-⊥ 𝓐 𝓑 f (i , ii , iii , vi) = iii

σ-frame-hom-⋁ : (𝓐 : σ-Frame 𝓤) (𝓑 : σ-Frame 𝓥)
              → (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
              → is-σ-frame-hom 𝓐 𝓑 f
              → ∀ 𝕒 → f (⋁⟨ 𝓐 ⟩ 𝕒) ＝ ⋁⟨ 𝓑 ⟩ (n ↦ f (𝕒 n))
σ-frame-hom-⋁ 𝓐 𝓑 f (i , ii , iii , vi) = vi

being-σ-frame-hom-is-prop : (𝓐 : σ-Frame 𝓤) (𝓑 : σ-Frame 𝓥)
                          → (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩)
                          → is-prop (is-σ-frame-hom 𝓐 𝓑 f)
being-σ-frame-hom-is-prop (_ , _ ,  _) (_ , _ , (i' , _)) f =

   ×₄-is-prop i' (Π₂-is-prop fe (λ a b → i')) i' (Π-is-prop fe (λ 𝕒 → i'))

id-is-σ-frame-hom : (𝓐 : σ-Frame 𝓤) → is-σ-frame-hom 𝓐 𝓐 id
id-is-σ-frame-hom 𝓐 = refl , (λ a b → refl) , refl , (λ 𝕒 → refl)

∘-σ-frame-hom : (𝓐 : σ-Frame 𝓤) (𝓑 : σ-Frame 𝓥) (𝓒 : σ-Frame 𝓦)
                (f : ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) (g : ⟨ 𝓑 ⟩ → ⟨ 𝓒 ⟩)
              → is-σ-frame-hom 𝓐 𝓑 f
              → is-σ-frame-hom 𝓑 𝓒 g
              → is-σ-frame-hom 𝓐 𝓒 (g ∘ f)
∘-σ-frame-hom 𝓐 𝓑 𝓒 f g (p₀ , q₀ , r₀ , s₀) (p₁ , q₁ , r₁ , s₁) = (p₂ , q₂ , r₂ , s₂)
 where
  p₂ = g (f ⊤⟨ 𝓐 ⟩) ＝⟨ ap g p₀ ⟩
       g ⊤⟨ 𝓑 ⟩     ＝⟨ p₁ ⟩
       ⊤⟨ 𝓒 ⟩       ∎

  q₂ = λ a b → g (f (a ∧⟨ 𝓐 ⟩ b))     ＝⟨ ap g (q₀ a b) ⟩
               g (f a ∧⟨ 𝓑 ⟩ f b)     ＝⟨ q₁ (f a) (f b) ⟩
               g (f a) ∧⟨ 𝓒 ⟩ g (f b) ∎

  r₂ = g (f ⊥⟨ 𝓐 ⟩) ＝⟨ ap g r₀ ⟩
       g ⊥⟨ 𝓑 ⟩     ＝⟨ r₁ ⟩
       ⊥⟨ 𝓒 ⟩       ∎

  s₂ = λ 𝕒 → g (f (⋁⟨ 𝓐 ⟩ 𝕒))           ＝⟨ ap g (s₀ 𝕒) ⟩
             g (⋁⟨ 𝓑 ⟩ (λ n → f (𝕒 n))) ＝⟨ s₁ (λ n → f (𝕒 n)) ⟩
             ⋁⟨ 𝓒 ⟩ (λ n → g (f (𝕒 n))) ∎

import OrderedTypes.sigma-sup-lattice

private σ-SupLat = OrderedTypes.sigma-sup-lattice.σ-SupLat fe

σ-frames-are-σ-suplats : σ-Frame 𝓤 → σ-SupLat 𝓤 𝓤
σ-frames-are-σ-suplats 𝓑  = ⟨ 𝓑 ⟩ ,
                            (⊥⟨ 𝓑 ⟩ , ⋁⟨ 𝓑 ⟩) ,
                            (λ x y → x ∧⟨ 𝓑 ⟩ y ＝ x) ,
                            (λ x y → ⟨ 𝓑 ⟩-is-set) ,
                            (⟨ 𝓑 ⟩-refl) ,
                            ⟨ 𝓑 ⟩-trans ,
                            ⟨ 𝓑 ⟩-antisym ,
                            ⟨ 𝓑 ⟩-⊥-minimum ,
                            ⟨ 𝓑 ⟩-⋁-is-ub ,
                            ⟨ 𝓑 ⟩-⋁-is-lb-of-ubs

open import OrderedTypes.Frame fe

frames-are-sigma-frames : Frame 𝓤 𝓤₀ → σ-Frame 𝓤
frames-are-sigma-frames (X , (⊤ , _∧_ , ⋁) , i , ii , iii , iv , v , vi , vii , viii) =
                        (X , (⊤ , _∧_ , ⋁ unique-from-𝟘 , ⋁ {ℕ}) , i , ii , iii , iv ,
                        (λ x → viii unique-from-𝟘 x (λ (n : 𝟘) → 𝟘-elim n)) ,
                        v , (λ x y → vi x {ℕ} y) , vii {ℕ} , viii {ℕ})

open import UF.PropTrunc

module _ (pe : Prop-Ext)
         (pt  : propositional-truncations-exist)
       where

 Ω-qua-σ-frame : σ-Frame (𝓤 ⁺)
 Ω-qua-σ-frame {𝓤} = frames-are-sigma-frames (Ω-qua-frame pe pt 𝓤₀ 𝓤)

 Ω-qua-σ-suplat : σ-SupLat (𝓤 ⁺) (𝓤 ⁺)
 Ω-qua-σ-suplat {𝓤} = σ-frames-are-σ-suplats (Ω-qua-σ-frame {𝓤})

\end{code}
