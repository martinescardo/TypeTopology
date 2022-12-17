Tom de Jong, ?? ─ ??
In collaboration with Nicolai Kraus, Fredrik Norvall Forsberg and Chuangjie Xu.

TO DO: Update
(1) The recursive nature of 𝕍-to-Ord is convenient because it allows us to prove
    properties by induction. Moreover, the supremum yields an ordinal by
    construction. It is possible to give a more direct presentation of
    𝕍-to-Ord (𝕍-set {A} f) however, that is nonrecursive.

    Namely, we can show that 𝕍-to-Ord (𝕍-set {A} f) ＝ (A/~ , <), where ~
    identifies elements of A that have the same image under f and [a] < [a'] is
    defined as f a ∈ f a'.

    It is straightforward to see that (A/~ , <) is in fact equivalent (but not
    equal for size reasons) to the image of f, which in turn is equivalent to
    the total space (Σ y ꞉ 𝕍 , y ∈ 𝕍-set f), so that the map 𝕍-to-Ord can be
    described (up to equivalence) as x ↦ Σ y ꞉ 𝕍 , y ∈ x.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan

open import UF.PropTrunc
open import UF.Univalence

module Ordinals.CumulativeHierarchy-Addendum
        (pt : propositional-truncations-exist)
        (ua : Univalence)
        (𝓤 : Universe)
       where

open PropositionalTruncation pt

open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Quotient hiding (is-prop-valued)
open import UF.UA-FunExt

private
 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' _ _ = fe

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

open import UF.CumulativeHierarchy pt fe pe
open import Ordinals.CumulativeHierarchy pt ua 𝓤
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type

module _
        (ch : cumulative-hierarchy-exists 𝓤)
       where

 open cumulative-hierarchy-exists ch

 open import UF.CumulativeHierarchy-LocallySmall pt fe pe
 open 𝕍-is-locally-small ch
 open ordinal-of-set-theoretic-ordinals ch

 module total-space-of-𝕍-set
         (x : 𝕍)
         (σ : is-set-theoretic-ordinal x)
        where

  𝕋x : 𝓤 ⁺ ̇
  𝕋x = Σ y ꞉ 𝕍 , y ∈ x

  _∈ₓ_ : 𝕋x → 𝕋x → 𝓤 ⁺ ̇
  u ∈ₓ v = pr₁ u ∈ pr₁ v

  ∈ₓ-is-prop-valued : is-prop-valued _∈ₓ_
  ∈ₓ-is-prop-valued u v = ∈-is-prop-valued

  ∈ₓ-is-transitive : is-transitive _∈ₓ_
  ∈ₓ-is-transitive u v w m n =
   transitive-set-if-set-theoretic-ordinal
    (being-set-theoretic-ordinal-is-hereditary σ (pr₂ w)) (pr₁ v) (pr₁ u) n m

  ∈ₓ-is-extensional : is-extensional _∈ₓ_
  ∈ₓ-is-extensional u v s t =
   to-subtype-＝ (λ _ → ∈-is-prop-valued)
                (∈-extensionality (pr₁ u) (pr₁ v)
                                  s' t')
    where
     s' : pr₁ u ⊆ pr₁ v
     s' y y-in-u = s (y , τ) y-in-u
      where
       τ : y ∈ x
       τ = transitive-set-if-set-theoretic-ordinal σ (pr₁ u) y (pr₂ u) y-in-u
     t' : pr₁ v ⊆ pr₁ u
     t' y y-in-v = t (y , τ) y-in-v
      where
       τ : y ∈ x
       τ = transitive-set-if-set-theoretic-ordinal σ (pr₁ v) y (pr₂ v) y-in-v

  ∈ₓ-is-well-founded : is-well-founded _∈ₓ_
  ∈ₓ-is-well-founded = λ (y , m) → ρ y m
   where
    ρ : (y : 𝕍) (m : y ∈ x) → is-accessible _∈ₓ_ (y , m)
    ρ = transfinite-induction _∈_ ∈-is-well-founded _ h
     where
      h : (y : 𝕍)
        → ((u : 𝕍) → u ∈ y → (m : u ∈ x) → is-accessible _∈ₓ_ (u , m))
        → (m : y ∈ x) → is-accessible _∈ₓ_ (y , m)
      h y IH m = step (λ (u , u-in-x) u-in-y → IH u u-in-y u-in-x)

  𝕋x-ordinal : Ordinal (𝓤 ⁺)
  𝕋x-ordinal = 𝕋x , _∈ₓ_ , ∈ₓ-is-prop-valued , ∈ₓ-is-well-founded
                         , ∈ₓ-is-extensional , ∈ₓ-is-transitive

  𝕋ᵒʳᵈx : 𝓤 ⁺ ̇
  𝕋ᵒʳᵈx = Σ y ꞉ 𝕍ᵒʳᵈ , y ∈ᵒʳᵈ (x , σ)

  -- NB
  𝕋ᵒʳᵈx-≃-𝕋x : 𝕋ᵒʳᵈx ≃ 𝕋x
  𝕋ᵒʳᵈx-≃-𝕋x = qinveq f (g , η , ε)
   where
    f : 𝕋ᵒʳᵈx → 𝕋x
    f ((y , _) , m) = y , m
    g : 𝕋x → 𝕋ᵒʳᵈx
    g (y , m) = (y , (being-set-theoretic-ordinal-is-hereditary σ m)) , m
    ε : f ∘ g ∼ id
    ε (y , m) = to-subtype-＝ (λ _ → ∈-is-prop-valued) refl
    η : g ∘ f ∼ id
    η ((y , τ) , m) =
     to-subtype-＝ (λ _ → ∈-is-prop-valued)
                   (to-subtype-＝ (λ _ → being-set-theoretic-ordinal-is-prop)
                                  refl)

\end{code}

\begin{code}

 module 𝕍-set-carrier-quotient
         (sq : set-quotients-exist)
         {A : 𝓤 ̇ }
         (f : A → 𝕍)
        where

  open set-quotients-exist sq
  open extending-relations-to-quotient fe pe

  _~_ : A → A → 𝓤 ⁺ ̇
  a ~ b = f a ＝ f b

  ~EqRel : EqRel A
  ~EqRel = _~_ , (λ a b → 𝕍-is-large-set)
               , (λ a → refl)
               , (λ a b e → e ⁻¹)
               , (λ a b c e₁ e₂ → e₁ ∙ e₂)

  A/~ : 𝓤 ⁺ ̇
  A/~ = A / ~EqRel

  [_] : A → A/~
  [_] = η/ ~EqRel

  -- TO DO: Use bisimilation relation on 𝕍 instead to have A/~ in 𝓤

  _≺[Ω]_ : A/~ → A/~ → Ω (𝓤 ⁺)
  _≺[Ω]_ = extension-rel₂ ~EqRel (λ a b → f a ∈[Ω] f b) ρ
   where
    ρ : {a b a' b' : A}
      → a ~ a' → b ~ b' → f a ∈[Ω] f b ＝ f a' ∈[Ω] f b'
    ρ {a} {b} {a'} {b'} e e' =
     Ω-extensionality fe pe (transport₂ _∈_ e e')
                            (transport₂ _∈_ (e ⁻¹) (e' ⁻¹))

  _≺_ : A/~ → A/~ → 𝓤 ⁺ ̇
  a ≺ b = (a ≺[Ω] b) holds

  ≺-is-prop-valued : is-prop-valued _≺_
  ≺-is-prop-valued a b = holds-is-prop (a ≺[Ω] b)

  ≺-＝-∈ : {a b : A} → [ a ] ≺ [ b ] ＝ f a ∈ f b
  ≺-＝-∈ {a} {b} = ap (_holds) (extension-rel-triangle₂ ~EqRel _ _ a b)

  ∈-to-≺ : {a b : A} → f a ∈ f b → [ a ] ≺ [ b ]
  ∈-to-≺ = back-Idtofun ≺-＝-∈

  ≺-to-∈ : {a b : A} → [ a ] ≺ [ b ] → f a ∈ f b
  ≺-to-∈ = Idtofun ≺-＝-∈

  ≺-is-transitive : is-set-theoretic-ordinal (𝕍-set f)
                  → is-transitive _≺_
  ≺-is-transitive σ = /-induction₃ fe ~EqRel prop-valued trans
    where
     prop-valued : (x y z : A / ~EqRel) → is-prop (x ≺ y → y ≺ z → x ≺ z)
     prop-valued x y z = Π₂-is-prop fe (λ _ _ → ≺-is-prop-valued x z)
     trans : (a b c : A) → [ a ] ≺ [ b ] → [ b ] ≺ [ c ] → [ a ] ≺ [ c ]
     trans a b c m n = ∈-to-≺ (τ (f a) (≺-to-∈ n) (≺-to-∈ m))
      where
       τ : (v : 𝕍) → f b ∈ f c → v ∈ f b → v ∈ f c
       τ = transitive-set-if-element-of-set-theoretic-ordinal σ
            (to-∈-of-𝕍-set ∣ c , refl ∣) (f b)

  ≺-is-extensional : is-transitive-set (𝕍-set f)
                   → is-extensional _≺_
  ≺-is-extensional τ =
   /-induction₂ fe ~EqRel (λ x y → Π₂-is-prop fe (λ _ _ → /-is-set ~EqRel))
                ext
    where
     ext : (a b : A)
         → ((x : A/~) → x ≺ [ a ] → x ≺ [ b ])
         → ((x : A/~) → x ≺ [ b ] → x ≺ [ a ])
         → [ a ] ＝ [ b ]
     ext a b s t = η/-identifies-related-points ~EqRel e'
      where
       e' : a ~ b
       e' = ∈-extensionality (f a) (f b) s' t'
        where
         lem : (x : 𝕍) (c : A) → x ∈ f c → ∃ d ꞉ A , f d ＝ x
         lem x c m = from-∈-of-𝕍-set (τ (f c) x (to-∈-of-𝕍-set ∣ c , refl ∣) m)
         s' : f a ⊆ f b
         s' x m = ∥∥-rec ∈-is-prop-valued h (lem x a m)
          where
           h : (Σ c ꞉ A , f c ＝ x) → x ∈ f b
           h (c , refl) = ≺-to-∈ (s [ c ] (∈-to-≺ m))
         t' : f b ⊆ f a
         t' x m = ∥∥-rec ∈-is-prop-valued h (lem x b m)
          where
           h : (Σ c ꞉ A , f c ＝ x) → x ∈ f a
           h (c , refl) = ≺-to-∈ (t [ c ] (∈-to-≺ m))

  ≺-is-well-founded : is-well-founded _≺_
  ≺-is-well-founded = /-induction ~EqRel acc-is-prop acc
   where
    acc-is-prop : (x : A/~) → is-prop (is-accessible _≺_ x)
    acc-is-prop = accessibility-is-prop _≺_ fe'
    acc' : (x : 𝕍) → ((a : A) → f a ＝ x → is-accessible _≺_ [ a ])
    acc' = transfinite-induction _∈_ ∈-is-well-founded _ h
     where
      h : (x : 𝕍)
        → ((y : 𝕍) → y ∈ x → (a : A) → f a ＝ y → is-accessible _≺_ [ a ])
        → (a : A) → f a ＝ x → is-accessible _≺_ [ a ]
      h x IH a refl =
       step (/-induction ~EqRel (λ _ → Π-is-prop fe (λ _ → acc-is-prop _)) α)
        where
         α : (b : A) → [ b ] ≺ [ a ] → is-accessible _≺_ [ b ]
         α b m = IH (f b) (≺-to-∈ m) b refl
    acc : (a : A) → is-accessible _≺_ [ a ]
    acc a = acc' (f a) a refl

  module construct-ordinal-as-quotient
          (σ : is-set-theoretic-ordinal (𝕍-set f))
         where

   A/~ᵒʳᵈ : Ordinal (𝓤 ⁺)
   A/~ᵒʳᵈ = A/~ , _≺_
                , ≺-is-prop-valued
                , ≺-is-well-founded
                , ≺-is-extensional (transitive-set-if-set-theoretic-ordinal σ)
                , ≺-is-transitive σ

\end{code}

Now we show that A/~ is equivalent to a type in 𝓤 which then gives us an ordinal
in 𝓤 equivalent to A/~ᵒʳᵈ.

\begin{code}

  _~⁻_ : A → A → 𝓤 ̇
  a ~⁻ b = f a ＝⁻ f b

  ~⁻EqRel : EqRel A
  ~⁻EqRel = _~⁻_ , (λ a b → ＝⁻-is-prop-valued)
                 , (λ a → ＝⁻-is-reflexive)
                 , (λ a b → ＝⁻-is-symmetric)
                 , (λ a b c → ＝⁻-is-transitive)

  A/~⁻ : 𝓤 ̇
  A/~⁻ = A / ~⁻EqRel

  A/~-≃-A/~⁻ : A/~ ≃ A/~⁻
  A/~-≃-A/~⁻ = quotients-equivalent A ~EqRel ~⁻EqRel (＝-to-＝⁻ , ＝⁻-to-＝)

  open import UF.Size -- TO DO: Move imports
  open import Ordinals.WellOrderTransport (λ _ _ → fe)

  private
   ≺-has-small-values : (x y : A/~) → is-small (x ≺ y)
   ≺-has-small-values =
    /-induction₂ fe ~EqRel
                 (λ x y → being-small-is-prop ua (x ≺ y) 𝓤)
                 (λ a b → (f a ∈⁻ f b)
                        , ((f a ∈⁻ f b)    ≃⟨ ∈⁻-≃-∈ ⟩
                           (f a ∈ f b)     ≃⟨ idtoeq _ _ (≺-＝-∈ ⁻¹) ⟩
                           ([ a ] ≺ [ b ]) ■))

   _≺'_ : A/~ → A/~ → 𝓤 ̇
   x ≺' y = pr₁ (≺-has-small-values x y)

   ≺-≃-≺' : {x y : A/~} → x ≺ y ≃ x ≺' y
   ≺-≃-≺' {x} {y} = ≃-sym (pr₂ (≺-has-small-values x y))

  module construct-ordinal-as-quotient₂
          (σ : is-set-theoretic-ordinal (𝕍-set f))
         where

   open construct-ordinal-as-quotient σ

   private
    resize-ordinal : Σ s ꞉ OrdinalStructure A/~⁻ , (A/~⁻ , s) ≃ₒ A/~ᵒʳᵈ
    resize-ordinal = transfer-structure A/~⁻ A/~ᵒʳᵈ (≃-sym A/~-≃-A/~⁻)
                      (_≺'_ , (λ x y → ≺-≃-≺'))

   A/~⁻ᵒʳᵈ : Ordinal 𝓤
   A/~⁻ᵒʳᵈ = A/~⁻ , pr₁ resize-ordinal

   A/~⁻ᵒʳᵈ-≃ₒ-A/~ᵒʳᵈ : A/~⁻ᵒʳᵈ ≃ₒ A/~ᵒʳᵈ
   A/~⁻ᵒʳᵈ-≃ₒ-A/~ᵒʳᵈ = pr₂ resize-ordinal

   A/~ᵒʳᵈ--≃ₒ-A/~⁻ᵒʳᵈ : A/~ᵒʳᵈ ≃ₒ A/~⁻ᵒʳᵈ
   A/~ᵒʳᵈ--≃ₒ-A/~⁻ᵒʳᵈ = ≃ₒ-sym A/~⁻ᵒʳᵈ A/~ᵒʳᵈ A/~⁻ᵒʳᵈ-≃ₒ-A/~ᵒʳᵈ

   [_]⁻ : A → A/~⁻
   [_]⁻ = ⌜ A/~-≃-A/~⁻ ⌝ ∘ [_]

   open import UF.ImageAndSurjection -- TO DO: Move and clean up
   open ImageAndSurjection pt
   []⁻-is-surjection : is-surjection [_]⁻
   []⁻-is-surjection = ∘-is-surjection (image-surjection-converse [_] λ P → /-induction ~EqRel) (equivs-are-surjections (⌜⌝-is-equiv A/~-≃-A/~⁻))

   _≺⁻_ : A/~⁻ → A/~⁻ → 𝓤 ̇
   _≺⁻_ = underlying-order A/~⁻ᵒʳᵈ

   ≺⁻-≃-≺ : {a b : A} → [ a ]⁻ ≺⁻ [ b ]⁻ ≃ [ a ] ≺ [ b ]
   ≺⁻-≃-≺ {a} {b} = logically-equivalent-props-are-equivalent
                      (prop-valuedness _≺⁻_ (is-well-ordered A/~⁻ᵒʳᵈ)
                        [ a ]⁻ [ b ]⁻)
                      (≺-is-prop-valued [ a ] [ b ])
                      (⦅2⦆ [ a ] [ b ])
                      (⦅1⦆ [ a ] [ b ])
    where
     φ⁺ : A/~⁻ᵒʳᵈ ≃ₒ A/~ᵒʳᵈ
     φ⁺ = A/~⁻ᵒʳᵈ-≃ₒ-A/~ᵒʳᵈ
     φ⁻¹ : A/~ → A/~⁻
     φ⁻¹ = ≃ₒ-to-fun⁻¹ _ _ φ⁺
     φ-is-order-equiv : is-order-equiv A/~⁻ᵒʳᵈ A/~ᵒʳᵈ (≃ₒ-to-fun _ _ φ⁺)
     φ-is-order-equiv = ≃ₒ-to-fun-is-order-equiv _ _ φ⁺
     ⦅1⦆ : (x y : A/~) → x ≺ y → φ⁻¹ x ≺⁻ φ⁻¹ y
     ⦅1⦆ = inverses-of-order-equivs-are-order-preserving A/~⁻ᵒʳᵈ A/~ᵒʳᵈ
                                                         φ-is-order-equiv
     ⦅2⦆ : (x y : A/~) → φ⁻¹ x ≺⁻ φ⁻¹ y → x ≺ y
     ⦅2⦆ = inverses-of-order-equivs-are-order-reflecting A/~⁻ᵒʳᵈ A/~ᵒʳᵈ
                                                          φ-is-order-equiv

   ≺⁻-≃-∈ : {a b : A} → [ a ]⁻ ≺⁻ [ b ]⁻ ≃ f a ∈ f b
   ≺⁻-≃-∈ {a} {b} = [ a ]⁻ ≺⁻ [ b ]⁻ ≃⟨ ≺⁻-≃-≺ ⟩
                    ([ a ] ≺ [ b ])  ≃⟨ idtoeq _ _ ≺-＝-∈ ⟩
                    f a ∈ f b        ■

   ≺⁻-to-∈ : {a b : A} → [ a ]⁻ ≺⁻ [ b ]⁻ → f a ∈ f b
   ≺⁻-to-∈ = ⌜ ≺⁻-≃-∈ ⌝

   ∈-to-≺⁻ : {a b : A} → f a ∈ f b → [ a ]⁻ ≺⁻ [ b ]⁻
   ∈-to-≺⁻ = ⌜ ≺⁻-≃-∈ ⌝⁻¹

\end{code}

    We prove that A/~ is the supremum defined above by showing that
      Ord-to-𝕍 (A/~ᵒʳᵈ) ＝ 𝕍-set f.
    This boils down to proving
      (a : A) → f a ＝ Ord-to-𝕍 (A/~ ↓ [ a ]) (module size issues)

\begin{code}

   key-lemma : (a' : A/~⁻) (a : A) → a' ＝ [ a ]⁻ → Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ a ]⁻) ＝ f a
   key-lemma = transfinite-induction _≺⁻_ (Well-foundedness A/~⁻ᵒʳᵈ) _ ind-proof
    where
     ind-proof : (a' : A/~⁻)
               → ((b' : A/~⁻) → b' ≺⁻ a'
                              → (b : A) → b' ＝ [ b ]⁻
                              → Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ b ]⁻) ＝ f b)
               → (a : A) → a' ＝ [ a ]⁻ → Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ a ]⁻) ＝ f a
     ind-proof a' IH a refl = ∈-extensionality _ _ ⦅1⦆ ⦅2⦆
      where
       -- TO DO: Clean
       ⦅1⦆ : Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ a ]⁻) ⊆ f a
       ⦅1⦆ x m = ∥∥-rec ∈-is-prop-valued bzz
           (from-∈-of-𝕍-set (transport (x ∈_) (Ord-to-𝕍-behaviour (A/~⁻ᵒʳᵈ ↓ [ a ]⁻)) m))
        where
         foo : (b : A) → f b ∈ f a → x ＝ Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ b ]⁻) → x ∈ f a
         foo b n e = transport (_∈ f a) ((IH [ b ]⁻ (∈-to-≺⁻ n) b refl) ⁻¹ ∙ e ⁻¹) n
         bzz : Σ (λ a₁ → Ord-to-𝕍 ((A/~⁻ᵒʳᵈ ↓ [ a ]⁻) ↓ a₁) ＝ x) → x ∈ f a
         bzz ((b' , l) , e) = ∥∥-rec ∈-is-prop-valued zzz ([]⁻-is-surjection b')
          where
           zzz : Σ (λ x₁ → [ x₁ ]⁻ ＝ b') → x ∈ f a
           zzz (b , refl) = transport (_∈ f a) ((IH [ b ]⁻ l b refl) ⁻¹ ∙ ((ap Ord-to-𝕍 (iterated-↓ A/~⁻ᵒʳᵈ [ a ]⁻ [ b ]⁻ l)) ⁻¹ ∙ e ) ) (≺⁻-to-∈ l)
       ⦅2⦆ : f a ⊆ Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ a ]⁻)
       ⦅2⦆ x m = ∥∥-rec ∈-is-prop-valued (λ (b , n , e) → baz b n e) m'
        where
         m' : ∃ b ꞉ A , (f b ∈ f a) × (f b ＝ x)
         m' = ∥∥-functor h blah
          where
           blah : ∃ b ꞉ A , f b ＝ x
           blah = from-∈-of-𝕍-set (transitive-set-if-set-theoretic-ordinal σ (f a) x (to-∈-of-𝕍-set ∣ a , refl ∣) m)
           abstract
            h : (Σ b ꞉ A , f b ＝ x)
              → Σ b ꞉ A , (f b ∈ f a) × (f b ＝ x)
            h (b , e) = b , transport⁻¹ (_∈ f a) e m , e
         foo : (b : A) → f b ∈ f a → f b ＝ x → Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ b ]⁻) ＝ f b
         foo b n e = IH [ b ]⁻ (∈-to-≺⁻ n) b refl
         baz : (b : A) → f b ∈ f a → f b ＝ x → x ∈ Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ a ]⁻)
         baz b n e = transport (_∈ Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ a ]⁻)) (IH [ b ]⁻ (∈-to-≺⁻ n) b refl ∙ e)
                               (transport⁻¹ (Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ b ]⁻) ∈_)
                                            (Ord-to-𝕍-behaviour (A/~⁻ᵒʳᵈ ↓ [ a ]⁻))
                                            (to-∈-of-𝕍-set ∣ ([ b ]⁻ , (∈-to-≺⁻ n)) , (ap Ord-to-𝕍 (iterated-↓ A/~⁻ᵒʳᵈ [ a ]⁻ [ b ]⁻ (∈-to-≺⁻ n))) ∣))

   open 𝕍-to-Ord-construction sq
   coincide : 𝕍ᵒʳᵈ-to-Ord (𝕍-set f , σ) ＝ A/~⁻ᵒʳᵈ
   coincide = Ord-to-𝕍-is-left-cancellable (𝕍ᵒʳᵈ-to-Ord (𝕍-set f , σ)) A/~⁻ᵒʳᵈ
               e
    where
     e : Ord-to-𝕍 (𝕍ᵒʳᵈ-to-Ord (𝕍-set f , σ)) ＝ Ord-to-𝕍 A/~⁻ᵒʳᵈ
     e = Ord-to-𝕍 (𝕍ᵒʳᵈ-to-Ord (𝕍-set f , σ)) ＝⟨ ap pr₁ (𝕍ᵒʳᵈ-to-Ord-is-section-of-Ord-to-𝕍ᵒʳᵈ (𝕍-set f , σ)) ⟩
         𝕍-set f ＝⟨ 𝕍-set-ext f _ ⦅2⦆ ⟩
         𝕍-set (λ a' → Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ a')) ＝⟨ (Ord-to-𝕍-behaviour A/~⁻ᵒʳᵈ) ⁻¹ ⟩
         Ord-to-𝕍 A/~⁻ᵒʳᵈ ∎
      where
       ⦅2⦆ : f ≈ (λ a' → Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ a'))
       pr₁ ⦅2⦆ a = ∣ [ a ]⁻ , (key-lemma [ a ]⁻ a refl) ∣
       pr₂ ⦅2⦆ a' = ∥∥-functor h ([]⁻-is-surjection a')
        where
         h : Σ (λ x → [ x ]⁻ ＝ a') → Σ (λ b → f b ＝ Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ a'))
         h (a , refl) = a , ((key-lemma a' a refl) ⁻¹)

 module total-space-of-𝕍-set'
         (sq : set-quotients-exist)
         {A : 𝓤 ̇ }
         (f : A → 𝕍)
         (σ : is-set-theoretic-ordinal (𝕍-set f))
        where

  private
   x = 𝕍-set f

  open total-space-of-𝕍-set x σ
  open 𝕍-set-carrier-quotient sq f
  open construct-ordinal-as-quotient₂ σ
  open construct-ordinal-as-quotient σ

  open import UF.ImageAndSurjection
  open ImageAndSurjection pt
  open import UF.EquivalenceExamples

  open set-quotients-exist sq

  𝕋x-≃-image-f : 𝕋x ≃ image f
  𝕋x-≃-image-f = Σ-cong h
   where
    h : (y : 𝕍) → (y ∈ x) ≃ y ∈image f
    h y = logically-equivalent-props-are-equivalent
           ∈-is-prop-valued
           (being-in-the-image-is-prop y f)
           from-∈-of-𝕍-set
           to-∈-of-𝕍-set

  open import Ordinals.WellOrderTransport (λ _ _ → fe)
  private
   transfer : Σ s ꞉ OrdinalStructure (image f) , (image f , s) ≃ₒ 𝕋x-ordinal
   transfer = transfer-structure (image f) 𝕋x-ordinal (≃-sym 𝕋x-≃-image-f) (_∈ₓ_ , (λ u v → ≃-refl (u ∈ₓ v)))

  image-f-ordinal : Ordinal (𝓤 ⁺)
  image-f-ordinal = image f , pr₁ transfer

  𝕋x-ordinal-≃-image-f-ordinal : 𝕋x-ordinal ≃ₒ image-f-ordinal
  𝕋x-ordinal-≃-image-f-ordinal = ≃ₒ-sym _ _ (pr₂ transfer)

  coincide₂ : 𝕋x-ordinal ＝ A/~ᵒʳᵈ
  coincide₂ = 𝕋x-ordinal      ＝⟨ ⦅1⦆ ⟩
              image-f-ordinal ＝⟨ ⦅2⦆ ⟩
              A/~ᵒʳᵈ          ∎
   where
    ⦅1⦆ = eqtoidₒ _ _ 𝕋x-ordinal-≃-image-f-ordinal
    ⦅2⦆ = eqtoidₒ _ _ (≃ₒ-sym _ _ (ϕ , ϕ-is-order-equiv))
     where
      open set-replacement-construction sq pt f 𝕍-is-locally-small 𝕍-is-large-set hiding ([_])
      ϕ : A/~ → image f
      ϕ = quotient-to-image
      ϕ-behaviour : (a : A) → ϕ [ a ] ＝ corestriction f a
      ϕ-behaviour = universality-triangle/ ~EqRel (image-is-set f 𝕍-is-large-set) (corestriction f) _
      ϕ-is-order-preserving : is-order-preserving A/~ᵒʳᵈ image-f-ordinal ϕ
      ϕ-is-order-preserving =
       /-induction₂ fe ~EqRel
                    (λ a' b' → Π-is-prop fe
                                (λ _ → prop-valuedness (underlying-order image-f-ordinal)
                                                       (is-well-ordered image-f-ordinal)
                                                       (ϕ a') (ϕ b')))
                    test
       where
        test : (a b : A) → [ a ] ≺ [ b ]
             → underlying-order image-f-ordinal (ϕ [ a ]) (ϕ [ b ])
        test a b l = transport₂ (underlying-order image-f-ordinal) ((ϕ-behaviour a) ⁻¹) ((ϕ-behaviour b) ⁻¹) (≺-to-∈ l)
      ϕ-is-order-reflecting : is-order-reflecting A/~ᵒʳᵈ image-f-ordinal ϕ
      ϕ-is-order-reflecting =
       /-induction₂ fe ~EqRel
                    (λ a' b' → Π-is-prop fe λ _ → prop-valuedness _≺_ (is-well-ordered A/~ᵒʳᵈ) a' b')
                    (λ a b l → ∈-to-≺ (transport₂ (underlying-order image-f-ordinal) (ϕ-behaviour a) (ϕ-behaviour b) l))
      ϕ-is-order-equiv : is-order-equiv A/~ᵒʳᵈ image-f-ordinal ϕ
      ϕ-is-order-equiv =
       order-preserving-reflecting-equivs-are-order-equivs _ _
        ϕ (⌜⌝⁻¹-is-equiv image-≃-quotient)
        ϕ-is-order-preserving
        ϕ-is-order-reflecting


 module _
         (sq : set-quotients-exist)
         (x : 𝕍ᵒʳᵈ)
        where

  open 𝕍-to-Ord-construction sq
  open total-space-of-𝕍-set
  open total-space-of-𝕍-set' sq

  finally : 𝕍ᵒʳᵈ-to-Ord x ≃ₒ 𝕋x-ordinal (pr₁ x) (pr₂ x)
  finally = blah (pr₁ x) (pr₂ x)
   where
    blah : (y : 𝕍) (σ : is-set-theoretic-ordinal y)
         → 𝕍ᵒʳᵈ-to-Ord (y , σ) ≃ₒ 𝕋x-ordinal y σ
    blah = 𝕍-prop-simple-induction _ (λ y → Π-is-prop fe (λ σ → ≃ₒ-is-prop-valued (𝕍ᵒʳᵈ-to-Ord (y , σ)) (𝕋x-ordinal y σ))) foofoo
     where
      foofoo : {A : 𝓤 ̇ } (f : A → 𝕍) (σ : is-set-theoretic-ordinal (𝕍-set f))
             → 𝕍ᵒʳᵈ-to-Ord (𝕍-set f , σ) ≃ₒ 𝕋x-ordinal (𝕍-set f) σ
      foofoo {A} f σ = ≃ₒ-trans (𝕍ᵒʳᵈ-to-Ord (𝕍-set f , σ)) A/~⁻ᵒʳᵈ (𝕋x-ordinal (𝕍-set f) σ)
                        (idtoeqₒ _ _ coincide)
                        (≃ₒ-sym _ _ (≃ₒ-trans (𝕋x-ordinal (𝕍-set f) σ) A/~ᵒʳᵈ A/~⁻ᵒʳᵈ
                                              (idtoeqₒ _ _ (coincide₂ f σ))
                                              A/~ᵒʳᵈ--≃ₒ-A/~⁻ᵒʳᵈ))
       where
       open 𝕍-set-carrier-quotient sq f
       open construct-ordinal-as-quotient₂ σ
       open construct-ordinal-as-quotient σ

\end{code}
