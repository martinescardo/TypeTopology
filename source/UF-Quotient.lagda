Tom de Jong, 4 & 5 April 2022.

Assuming set quotients, we
(1) derive propositional truncations in the presence of function extensionality;
(2) prove Set Replacement as defined in UF-Size.lagda.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF-Quotient where

open import SpartanMLTT

open import UF-Base hiding (_≈_)
open import UF-Equiv
open import UF-FunExt
open import UF-ImageAndSurjection
open import UF-PropTrunc
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Size

is-prop-valued is-equiv-relation : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-prop-valued    _≈_ = ∀ x y → is-prop (x ≈ y)
is-equiv-relation _≈_ = is-prop-valued _≈_ × reflexive  _≈_
                      × symmetric      _≈_ × transitive _≈_

EqRel : {𝓤 𝓥 : Universe} → 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
EqRel {𝓤} {𝓥} X = Σ R ꞉ (X → X → 𝓥 ̇ ) , is-equiv-relation R

_≈[_]_ : {X : 𝓤 ̇ } → X → EqRel X → X → 𝓥 ̇
x ≈[ _≈_ , _ ] y = x ≈ y

identifies-related-points : {X : 𝓤 ̇  } (≈ : EqRel {𝓤} {𝓥} X) {Y : 𝓦 ̇  }
                          → (X → Y) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
identifies-related-points (_≈_ , _) f = ∀ {x x'} → x ≈ x' → f x ≡ f x'

record set-quotients-exist : 𝓤ω where
 field
  _/_ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇  ) → EqRel {𝓤} {𝓥} X → 𝓤 ⊔ 𝓥 ̇
  η/ : {𝓤 𝓥 : Universe} {X : 𝓤 ̇  } (≋ : EqRel {𝓤} {𝓥} X) → X → X / ≋
  η/-identifies-related-points : {𝓤 𝓥 : Universe}
                                 {X : 𝓤 ̇  } (≋ : EqRel {𝓤} {𝓥} X)
                               → identifies-related-points ≋ (η/ ≋)
  /-is-set : {𝓤 𝓥 : Universe} {X : 𝓤 ̇  } (≋ : EqRel {𝓤} {𝓥} X) → is-set (X / ≋)
  /-induction : {𝓤 𝓥 : Universe} {X : 𝓤 ̇  } (≋ : EqRel {𝓤} {𝓥} X)
                {𝓦 : Universe} {P : X / ≋ → 𝓦 ̇  }
              → ((x' : X / ≋) → is-prop (P x'))
              → ((x : X) → P (η/ ≋ x)) → (y : X / ≋) → P y
  /-universality : {𝓤 𝓥 : Universe} {X : 𝓤 ̇  } (≋ : EqRel {𝓤} {𝓥} X)
                   {𝓦 : Universe} {Y : 𝓦 ̇  }
                 → is-set Y → (f : X → Y)
                 → identifies-related-points ≋ f
                 → ∃! f̅ ꞉ (X / ≋ → Y) , f̅ ∘ η/ ≋ ∼ f

\end{code}

Paying attention to universe levels, it is important to note that the quotient
of X : 𝓤 by a 𝓥-valued equivalence relation is assumed to live in 𝓤 ⊔ 𝓥. In
particular, the quotient of type in 𝓤 by a 𝓤-valued equivalence relation lives
in 𝓤 again.

The following is boilerplate and duplicates some of the material in
UF-Quotient.lagda, where large set quotients are constructed using propositional
truncations, function extensionality and propositional extensionality.

We need the boilerplate in OrdinalOfOrdinalsSuprema.lagda, where we use set
quotients to construct small suprema of small ordinals.


A quotient is said to be effective if for every x, y : X, we have x ≈ y whenever
η/ x ≡ ‌η/ y. Notice that we did not include effectivity as a requirement in
'set-quotients-exist'. But actually it follows from the other properties, at
least in the presence of function extensionality and propositonal
extensionality, as Martín observed. The proof is as follows:

(1) First construct propositional truncations using assumed set quotients.
(2) Construct another (large) quotient as described in UF-Large-Quotients.lagda.
(3) This large quotient is effective, but has to be isomorphic to the assumed
    set quotient, hence this quotient has to be effective as well.

TODO: Implement this in Agda.

\begin{code}

 module _
         {X : 𝓤 ̇  }
         (≋@(_≈_ , ≈p , ≈r , ≈s , ≈t) : EqRel {𝓤} {𝓥} X)
        where

  module _
          {A : 𝓦 ̇  }
          (A-is-set : is-set A)
         where

   mediating-map/ : (f : X → A)
                  → identifies-related-points ≋ f
                  → X / ≋ → A
   mediating-map/ f p = ∃!-witness (/-universality ≋ A-is-set f p)

   universality-triangle/ : (f : X → A)
                            (p : identifies-related-points ≋ f)
                          → mediating-map/ f p ∘ η/ ≋ ∼ f
   universality-triangle/ f p = ∃!-is-witness (/-universality ≋ A-is-set f p)

\end{code}

We extend unary and binary prop-valued relations to the quotient.

\begin{code}

 module extending-relations-to-quotient (fe : Fun-Ext) (pe : Prop-Ext) where

  module _
          {X : 𝓤 ̇  }
          (≋@(_≈_ , ≈p , ≈r , ≈s , ≈t) : EqRel {𝓤} {𝓥} X)
         where

   module _
           (r : X → Ω 𝓣)
           (p : {x y : X} → x ≈ y → r x ≡ r y)
          where

    extension-rel₁ : X / ≋ → Ω 𝓣
    extension-rel₁ = mediating-map/ ≋ (Ω-is-set fe pe) r p

    extension-rel-triangle₁ : extension-rel₁ ∘ η/ ≋ ∼ r
    extension-rel-triangle₁ = universality-triangle/ ≋ (Ω-is-set fe pe) r p

   module _ (r : X → X → Ω 𝓣)
            (p : {x y x' y' : X} → x ≈ x' → y ≈ y' → r x y ≡ r x' y')
          where

    abstract
     private
      p' : (x : X) {y y' : X} → y ≈ y' → r x y ≡ r x y'
      p' x {y} {y'} = p (≈r x)

      r₁ : X → X / ≋ → Ω 𝓣
      r₁ x = extension-rel₁ (r x) (p' x)

      δ : {x x' : X} → x ≈ x' → (y : X) → r₁ x (η/ ≋ y) ≡ r₁ x' (η/ ≋ y)
      δ {x} {x'} e y =
        r₁ x  (η/ ≋ y)  ≡⟨ extension-rel-triangle₁ (r x) (p (≈r x)) y        ⟩
        r  x     y      ≡⟨ p e (≈r y)                                        ⟩
        r  x'    y      ≡⟨ (extension-rel-triangle₁ (r x') (p (≈r x')) y) ⁻¹ ⟩
        r₁ x' (η/ ≋ y)  ∎

      ρ : (q : X / ≋) {x x' : X} → x ≈ x' → r₁ x q ≡ r₁ x' q
      ρ q {x} {x'} e = /-induction ≋ (λ q → Ω-is-set fe pe) (δ e) q

      r₂ : X / ≋ → X / ≋ → Ω 𝓣
      r₂ = mediating-map/ ≋ (Π-is-set fe (λ _ → Ω-is-set fe pe)) r₁
                            (λ {x} {x'} e → dfunext fe (λ q → ρ q e))

      σ : (x : X) → r₂ (η/ ≋ x) ≡ r₁ x
      σ = universality-triangle/ ≋ (Π-is-set fe (λ _ → Ω-is-set fe pe)) r₁
                                   (λ {x} {x'} e → dfunext fe (λ q → ρ q e))

      τ : (x y : X) → r₂ (η/ ≋ x) (η/ ≋ y) ≡ r x y
      τ x y = r₂ (η/ ≋ x) (η/ ≋ y) ≡⟨ happly (σ x) (η/ ≋ y) ⟩
              r₁ x        (η/ ≋ y) ≡⟨ extension-rel-triangle₁ (r x) (p' x) y ⟩
              r  x            y    ∎

     extension-rel₂ : X / ≋ → X / ≋ → Ω 𝓣
     extension-rel₂ = r₂

     extension-rel-triangle₂ : (x y : X)
                             → extension-rel₂ (η/ ≋ x) (η/ ≋ y) ≡ r x y
     extension-rel-triangle₂ = τ

\end{code}

For proving properties of an extended binary relation, it is useful to have a
binary and ternary versions of quotient induction.

\begin{code}

 module _
         (fe : Fun-Ext)
         {X : 𝓤 ̇  }
         (≋ : EqRel {𝓤 } {𝓥} X)
        where

  /-induction₂ : ∀ {𝓦} {P : X / ≋ → X / ≋ → 𝓦 ̇ }
               → ((x' y' : X / ≋) → is-prop (P x' y'))
               → ((x y : X) → P (η/ ≋ x) (η/ ≋ y))
               → (x' y' : X / ≋) → P x' y'
  /-induction₂ p h =
   /-induction ≋ (λ x' → Π-is-prop fe (p x'))
                 (λ x → /-induction ≋ (p (η/ ≋ x)) (h x))

  /-induction₃ : ∀ {𝓦} → {P : X / ≋ → X / ≋ → X / ≋ → 𝓦 ̇ }
               → ((x' y' z' : X / ≋) → is-prop (P x' y' z'))
               → ((x y z : X) → P (η/ ≋ x) (η/ ≋ y) (η/ ≋ z))
               → (x' y' z' : X / ≋) → P x' y' z'
  /-induction₃ p h =
   /-induction₂ (λ x' y' → Π-is-prop fe (p x' y'))
                (λ x y → /-induction ≋ (p (η/ ≋ x) (η/ ≋ y)) (h x y))


 quotients-equivalent : (X : 𝓤 ̇ ) (R : EqRel {𝓤} {𝓥} X) (R' : EqRel {𝓤} {𝓦} X)
                      → ({x y : X} → x ≈[ R ] y ⇔ x ≈[ R' ] y)
                      → (X / R) ≃ (X / R')
 quotients-equivalent X (_≈_  , ≈p ,  ≈r  , ≈s  , ≈t )
                        (_≈'_ , ≈p' , ≈r' , ≈s' , ≈t') ε = γ
  where
   ≋  = (_≈_  , ≈p ,  ≈r  , ≈s  , ≈t )
   ≋' = (_≈'_ , ≈p' , ≈r' , ≈s' , ≈t')
   i : {x y : X} → x ≈ y → η/ ≋' x ≡ η/ ≋' y
   i e = η/-identifies-related-points ≋' (lr-implication ε e)
   i' : {x y : X} → x ≈' y → η/ ≋ x ≡ η/ ≋ y
   i' e = η/-identifies-related-points ≋ (rl-implication ε e)
   f : X / ≋ → X / ≋'
   f = mediating-map/ ≋ (/-is-set ≋') (η/ ≋') i
   f' : X / ≋' → X / ≋
   f' = mediating-map/ ≋' (/-is-set ≋) (η/ ≋) i'
   a : (x : X) → f (f' (η/ ≋' x)) ≡ η/ ≋' x
   a x = f (f' (η/ ≋' x)) ≡⟨ I ⟩
         f (η/ ≋ x)       ≡⟨ II ⟩
         η/ ≋' x          ∎
    where
     I  = ap f (universality-triangle/ ≋' (/-is-set ≋) (η/ ≋) i' x)
     II = universality-triangle/ ≋ (/-is-set ≋') (η/ ≋') i x
   α : f ∘ f' ∼ id
   α = /-induction ≋' (λ _ → /-is-set ≋') a
   a' : (x : X) → f' (f (η/ ≋ x)) ≡ η/ ≋ x
   a' x = f' (f (η/ ≋ x)) ≡⟨ I ⟩
         f' (η/ ≋' x)     ≡⟨ II ⟩
         η/ ≋ x           ∎
    where
     I  = ap f' (universality-triangle/ ≋ (/-is-set ≋') (η/ ≋') i x)
     II = universality-triangle/ ≋' (/-is-set ≋) (η/ ≋) i' x
   α' : f' ∘ f ∼ id
   α' = /-induction ≋ (λ _ → /-is-set ≋) a'
   γ : (X / ≋) ≃ (X / ≋')
   γ = qinveq f (f' , α' , α)

\end{code}

We now construct propositional truncations using set quotients. Notice that
function extensionality is (only) needed to prove that the quotient is a
proposition.

\begin{code}

 private
  module _ {X : 𝓤 ̇  } where
   _≈_ : X → X → 𝓤₀ ̇
   x ≈ y = 𝟙
   ≋ : EqRel X
   ≋ = _≈_ , (λ x y → 𝟙-is-prop) , (λ x → ⋆) , (λ x y _ → ⋆) , (λ x y z _ _ → ⋆)

  ∥_∥ : 𝓤 ̇  → 𝓤 ̇
  ∥_∥ X = X / ≋

  ∣_∣ : {X : 𝓤 ̇  } → X → ∥ X ∥
  ∣_∣ = η/ ≋

  ∥∥-is-prop : {X : 𝓤 ̇  } → funext 𝓤 𝓤 → is-prop ∥ X ∥
  ∥∥-is-prop {𝓤} {X} fe = /-induction ≋ (λ x' → Π-is-prop fe (λ y' → /-is-set ≋))
                           (λ x → /-induction ≋ (λ y' → /-is-set ≋)
                                  (λ y → η/-identifies-related-points ≋ ⋆))

  ∥∥-rec : {X : 𝓤 ̇  } {P : 𝓥 ̇  } → is-prop P → (X → P) → ∥ X ∥ → P
  ∥∥-rec {𝓤} {𝓥} {X} {P} i f =
   ∃!-witness (/-universality ≋ (props-are-sets i) f
                              (λ {x} {x'}_ → i (f x) (f x')))


 propositional-truncations-from-set-quotients :
  Fun-Ext → propositional-truncations-exist
 propositional-truncations-from-set-quotients fe = record
  { ∥_∥        = ∥_∥
  ; ∥∥-is-prop = ∥∥-is-prop fe
  ; ∣_∣        = ∣_∣
  ; ∥∥-rec     = ∥∥-rec
  }

\end{code}

Finally, we show that Set Replacement is derivable when we have set quotients as
defined above.

Notice how we could replace propositional-truncations-exist assumption by
function extensionality (funext) as we can use funext to construct truncations,
as shown above.

\begin{code}

module _
        (sq : set-quotients-exist)
        (pt : propositional-truncations-exist)
       where
 open set-quotients-exist sq

 open ImageAndSurjection pt
 open PropositionalTruncation pt

 module set-replacement-construction
         {X : 𝓤 ̇  }
         {Y : 𝓦 ̇  }
         (f : X → Y)
         (Y-is-loc-small : Y is-locally 𝓥 small)
         (Y-is-set : is-set Y)
        where

  _≈_ : X → X → 𝓦 ̇
  x ≈ x' = f x ≡ f x'

  ≈-is-prop-valued : is-prop-valued _≈_
  ≈-is-prop-valued x x' = Y-is-set

  ≈-is-reflexive : reflexive _≈_
  ≈-is-reflexive x = refl

  ≈-is-symmetric : symmetric _≈_
  ≈-is-symmetric x x' p = p ⁻¹

  ≈-is-transitive : transitive _≈_
  ≈-is-transitive _ _ _ p q = p ∙ q

  ≈-is-equiv-rel : is-equiv-relation _≈_
  ≈-is-equiv-rel = ≈-is-prop-valued , ≈-is-reflexive  ,
                   ≈-is-symmetric   , ≈-is-transitive

 \end{code}

 Using that Y is locally 𝓥 small, we resize _≈_ to a 𝓥-valued equivalence
 relation.

 \begin{code}

  _≈⁻_ : X → X → 𝓥 ̇
  x ≈⁻ x' = pr₁ (Y-is-loc-small (f x) (f x'))

  ≈⁻-≃-≈ : {x x' : X} → x ≈⁻ x' ≃ x ≈ x'
  ≈⁻-≃-≈ {x} {x'} = pr₂ (Y-is-loc-small (f x) (f x'))

  ≈⁻-is-prop-valued : is-prop-valued _≈⁻_
  ≈⁻-is-prop-valued x x' = equiv-to-prop ≈⁻-≃-≈ (≈-is-prop-valued x x')

  ≈⁻-is-reflexive : reflexive _≈⁻_
  ≈⁻-is-reflexive x = ⌜ ≈⁻-≃-≈ ⌝⁻¹ (≈-is-reflexive x)

  ≈⁻-is-symmetric : symmetric _≈⁻_
  ≈⁻-is-symmetric x x' p = ⌜ ≈⁻-≃-≈ ⌝⁻¹ (≈-is-symmetric x x' (⌜ ≈⁻-≃-≈ ⌝ p))

  ≈⁻-is-transitive : transitive _≈⁻_
  ≈⁻-is-transitive x x' x'' p q =
   ⌜ ≈⁻-≃-≈ ⌝⁻¹ (≈-is-transitive x x' x'' (⌜ ≈⁻-≃-≈ ⌝ p) (⌜ ≈⁻-≃-≈ ⌝ q))

  ≈⁻-is-equiv-rel : is-equiv-relation _≈⁻_
  ≈⁻-is-equiv-rel = ≈⁻-is-prop-valued , ≈⁻-is-reflexive  ,
                    ≈⁻-is-symmetric   , ≈⁻-is-transitive

  ≋ : EqRel X
  ≋ = _≈_ , ≈-is-equiv-rel

  X/≈ : 𝓤 ⊔ 𝓦 ̇
  X/≈ = (X / ≋)

  X/≈⁻ : 𝓤 ⊔ 𝓥 ̇
  X/≈⁻ = (X / (_≈⁻_ , ≈⁻-is-equiv-rel))

  [_] : X → X/≈
  [_] = η/ ≋

  X/≈-≃-X/≈⁻ : X/≈ ≃ X/≈⁻
  X/≈-≃-X/≈⁻ = quotients-equivalent X ≋ (_≈⁻_ , ≈⁻-is-equiv-rel)
                                        (⌜ ≈⁻-≃-≈ ⌝⁻¹ , ⌜ ≈⁻-≃-≈ ⌝)

 \end{code}

 We now proceed to show that X/≈ and image f are equivalent types.

 \begin{code}

  corestriction-respects-≈ : {x x' : X}
                           → x ≈ x'
                           → corestriction f x ≡ corestriction f x'
  corestriction-respects-≈ =
   to-subtype-≡ (λ y → being-in-the-image-is-prop y f)

  quotient-to-image : X/≈ → image f
  quotient-to-image = mediating-map/ ≋ (image-is-set f Y-is-set)
                       (corestriction f) (corestriction-respects-≈)

  image-to-quotient' : (y : image f)
                     → Σ q ꞉ X/≈ , ∃ x ꞉ X , ([ x ] ≡ q) × (f x ≡ pr₁ y)
  image-to-quotient' (y , p) = ∥∥-rec prp r p
   where
    r : (Σ x ꞉ X , f x ≡ y)
      → (Σ q ꞉ X/≈ , ∃ x ꞉ X , ([ x ] ≡ q) × (f x ≡ y))
    r (x , e) = [ x ] , ∣ x , refl , e ∣
    prp : is-prop (Σ q ꞉ X/≈ , ∃ x ꞉ X , ([ x ] ≡ q) × (f x ≡ y))
    prp (q , u) (q' , u') = to-subtype-≡ (λ _ → ∃-is-prop)
                                         (∥∥-rec₂ (/-is-set ≋) γ u u')
     where
      γ : (Σ x  ꞉ X , ([ x  ] ≡ q ) × (f x  ≡ y))
        → (Σ x' ꞉ X , ([ x' ] ≡ q') × (f x' ≡ y))
        → q ≡ q'
      γ (x , refl , e) (x' , refl , refl) = η/-identifies-related-points ≋ e

  image-to-quotient : image f → X/≈
  image-to-quotient y = pr₁ (image-to-quotient' y)

  image-to-quotient-lemma : (x : X)
                          → image-to-quotient (corestriction f x) ≡ [ x ]
  image-to-quotient-lemma x = ∥∥-rec (/-is-set ≋) γ t
   where
    q : X/≈
    q = image-to-quotient (corestriction f x)
    t : ∃ x' ꞉ X , ([ x' ] ≡ q) × (f x' ≡ f x)
    t = pr₂ (image-to-quotient' (corestriction f x))
    γ : (Σ x' ꞉ X , ([ x' ] ≡ q) × (f x' ≡ f x))
      → q ≡ [ x ]
    γ (x' , u , v) =   q    ≡⟨ u ⁻¹ ⟩
                     [ x' ] ≡⟨ η/-identifies-related-points ≋ v ⟩
                     [ x  ] ∎

  image-≃-quotient : image f ≃ X/≈
  image-≃-quotient = qinveq ϕ (ψ , ρ , σ)
   where
    ϕ : image f → X/≈
    ϕ = image-to-quotient
    ψ : X/≈ → image f
    ψ = quotient-to-image
    τ : (x : X) → ψ [ x ] ≡ corestriction f x
    τ = universality-triangle/ ≋ (image-is-set f Y-is-set)
                               (corestriction f)
                               corestriction-respects-≈
    σ : ϕ ∘ ψ ∼ id
    σ = /-induction ≋ (λ x' → /-is-set ≋) γ
     where
      γ : (x : X) → ϕ (ψ [ x ]) ≡ [ x ]
      γ x = ϕ (ψ [ x ])            ≡⟨ ap ϕ (τ x)                ⟩
            ϕ (corestriction f x ) ≡⟨ image-to-quotient-lemma x ⟩
            [ x ]                  ∎
    ρ : ψ ∘ ϕ ∼ id
    ρ (y , p) = ∥∥-rec (image-is-set f Y-is-set) γ p
     where
      γ : (Σ x ꞉ X , f x ≡ y) → ψ (ϕ (y , p)) ≡ (y , p)
      γ (x , refl) = ψ (ϕ (f x , p))           ≡⟨ ⦅1⦆ ⟩
                     ψ (ϕ (corestriction f x)) ≡⟨ ⦅2⦆ ⟩
                     ψ [ x ]                   ≡⟨ ⦅3⦆ ⟩
                     corestriction f x         ≡⟨ ⦅4⦆ ⟩
                     (f x , p)                 ∎
       where
        ⦅4⦆ = to-subtype-≡ (λ y → being-in-the-image-is-prop y f) refl
        ⦅1⦆ = ap (ψ ∘ ϕ) (⦅4⦆ ⁻¹)
        ⦅2⦆ = ap ψ (image-to-quotient-lemma x)
        ⦅3⦆ = τ x

 set-replacement-from-set-quotients : Set-Replacement pt
 set-replacement-from-set-quotients
  {𝓦} {𝓣} {𝓤} {𝓥} {X} {Y} f X-is-small Y-is-loc-small Y-is-set = X/≈⁻ , ≃-sym e
  where
   X' : 𝓤 ̇
   X' = pr₁ X-is-small
   φ : X' ≃ X
   φ = pr₂ X-is-small
   f' : X' → Y
   f' = f ∘ ⌜ φ ⌝
   open set-replacement-construction f' Y-is-loc-small Y-is-set
   open import UF-EquivalenceExamples
   e = image f  ≃⟨ Σ-cong (λ y → ∥∥-cong pt (h y)) ⟩
       image f' ≃⟨ image-≃-quotient ⟩
       X/≈      ≃⟨ X/≈-≃-X/≈⁻       ⟩
       X/≈⁻     ■
    where
     h : (y : Y) → (Σ x ꞉ X , f x ≡ y) ≃ (Σ x' ꞉ X' , f' x' ≡ y)
     h y = ≃-sym (Σ-change-of-variable (λ x → f x ≡ y) ⌜ φ ⌝ (⌜⌝-is-equiv φ))

\end{code}
