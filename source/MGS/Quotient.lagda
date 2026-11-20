This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Quotient where

open import MGS.Unique-Existence        public
open import MGS.Subsingleton-Truncation public

is-subsingleton-valued
 reflexive
 symmetric
 transitive
 is-equivalence-relation :

 {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇

is-subsingleton-valued  _≈_ = ∀ x y → is-subsingleton (x ≈ y)
reflexive               _≈_ = ∀ x → x ≈ x
symmetric               _≈_ = ∀ x y → x ≈ y → y ≈ x
transitive              _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

is-equivalence-relation _≈_ = is-subsingleton-valued _≈_
                            × reflexive _≈_
                            × symmetric _≈_
                            × transitive _≈_

module quotient
       {𝓤 𝓥 : Universe}
       (pt  : subsingleton-truncations-exist)
       (hfe : global-hfunext)
       (pe  : propext 𝓥)
       (X   : 𝓤 ̇ )
       (_≈_ : X → X → 𝓥 ̇ )
       (≈p  : is-subsingleton-valued _≈_)
       (≈r  : reflexive _≈_)
       (≈s  : symmetric _≈_)
       (≈t  : transitive _≈_)
      where

 open basic-truncation-development pt hfe

 equiv-rel : X → (X → Ω 𝓥)
 equiv-rel x y = (x ≈ y) , ≈p x y

 X/≈ : 𝓥 ⁺ ⊔ 𝓤 ̇
 X/≈ = image equiv-rel

 X/≈-is-set : is-set X/≈
 X/≈-is-set = subsets-of-sets-are-sets (X → Ω 𝓥) _
               (powersets-are-sets (dfunext-gives-hfunext hunapply) hunapply pe)
               (λ _ → ∃-is-subsingleton)

 η : X → X/≈
 η = corestriction equiv-rel

 η-surjection : is-surjection η
 η-surjection = corestriction-is-surjection equiv-rel

 η-induction : (P : X/≈ → 𝓦 ̇ )
             → ((x' : X/≈) → is-subsingleton (P x'))
             → ((x : X) → P (η x))
             → (x' : X/≈) → P x'

 η-induction = surjection-induction η η-surjection

 η-equiv-equal : {x y : X} → x ≈ y → η x ＝ η y
 η-equiv-equal {x} {y} e =
  to-subtype-＝
    (λ _ → ∃-is-subsingleton)
    (hunapply (λ z → to-subtype-＝
                        (λ _ → being-subsingleton-is-subsingleton hunapply)
                        (pe (≈p x z) (≈p y z) (≈t y x z (≈s x y e)) (≈t x y z e))))

 η-equal-equiv : {x y : X} → η x ＝ η y → x ≈ y
 η-equal-equiv {x} {y} p = equiv-rel-reflect (ap pr₁ p)
  where
   equiv-rel-reflect : equiv-rel x ＝ equiv-rel y → x ≈ y
   equiv-rel-reflect q = b (≈r y)
    where
     a : (y ≈ y) ＝ (x ≈ y)
     a = ap (λ - → pr₁(- y)) (q ⁻¹)

     b : y ≈ y → x ≈ y
     b = Id→fun a

 universal-property : (A : 𝓦 ̇ )
                    → is-set A
                    → (f : X → A)
                    → ({x x' : X} → x ≈ x' → f x ＝ f x')
                    → ∃! f' ꞉ (X/≈ → A), f' ∘ η ＝ f

 universal-property {𝓦} A i f τ = e
  where
   G : X/≈ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ̇
   G x' = Σ a ꞉ A , ∃ x ꞉ X , (η x ＝ x') × (f x ＝ a)

   φ : (x' : X/≈) → is-subsingleton (G x')
   φ = η-induction _ γ induction-step
    where
     induction-step : (y : X) → is-subsingleton (G (η y))
     induction-step x (a , d) (b , e) = to-subtype-＝ (λ _ → ∃-is-subsingleton) p
      where
       h : (Σ x' ꞉ X , (η x' ＝ η x) × (f x' ＝ a))
         → (Σ y' ꞉ X , (η y' ＝ η x) × (f y' ＝ b))
         → a ＝ b
       h (x' , r , s) (y' , t , u) = a    ＝⟨ s ⁻¹ ⟩
                                     f x' ＝⟨ τ (η-equal-equiv (r ∙ t ⁻¹)) ⟩
                                     f y' ＝⟨ u ⟩
                                     b    ∎

       p : a ＝ b
       p = ∥∥-recursion (i a b) (λ σ → ∥∥-recursion (i a b) (h σ) e) d

     γ : (x' : X/≈) → is-subsingleton (is-subsingleton (G x'))
     γ x' = being-subsingleton-is-subsingleton hunapply

   k : (x' : X/≈) → G x'
   k = η-induction _ φ induction-step
    where
     induction-step : (y : X) → G (η y)
     induction-step x = f x , ∣ x , refl (η x) , refl (f x) ∣

   f' : X/≈ → A
   f' x' = pr₁ (k x')

   r : f' ∘ η ＝ f
   r = hunapply h
    where
     g : (y : X) → ∃ x ꞉ X , (η x ＝ η y) × (f x ＝ f' (η y))
     g y = pr₂ (k (η y))

     j : (y : X) → (Σ x ꞉ X , (η x ＝ η y) × (f x ＝ f' (η y))) → f'(η y) ＝ f y
     j y (x , p , q) = f' (η y) ＝⟨ q ⁻¹ ⟩
                       f x      ＝⟨ τ (η-equal-equiv p) ⟩
                       f y      ∎

     h : (y : X) → f'(η y) ＝ f y
     h y = ∥∥-recursion (i (f' (η y)) (f y)) (j y) (g y)

   c : (σ : Σ f'' ꞉ (X/≈ → A), f'' ∘ η ＝ f) → (f' , r) ＝ σ
   c (f'' , s) = to-subtype-＝ (λ g → Π-is-set hfe (λ _ → i) (g ∘ η) f) t
    where
     w : ∀ x → f'(η x) ＝ f''(η x)
     w = happly (f' ∘ η) (f'' ∘ η) (r ∙ s ⁻¹)

     t : f' ＝ f''
     t = hunapply (η-induction _ (λ x' → i (f' x') (f'' x')) w)

   e : ∃! f' ꞉ (X/≈ → A), f' ∘ η ＝ f
   e = (f' , r) , c

\end{code}
