Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.Unique-Existence where

open import MGS.Subsingleton-Theorems public

∃! : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
∃! A = is-singleton (Σ A)

-∃! : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-∃! X Y = ∃! Y

syntax -∃! A (λ x → b) = ∃! x ꞉ A , b

∃!-is-subsingleton : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                   → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                   → is-subsingleton (∃! A)

∃!-is-subsingleton A fe = being-singleton-is-subsingleton fe

unique-existence-gives-weak-unique-existence : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )

  → (∃! x ꞉ X , A x)
  → (Σ x ꞉ X , A x) × ((x y : X) → A x → A y → x ＝ y)

unique-existence-gives-weak-unique-existence A s = center (Σ A) s , u
 where
  u : ∀ x y → A x → A y → x ＝ y
  u x y a b = ap pr₁ (singletons-are-subsingletons (Σ A) s (x , a) (y , b))

weak-unique-existence-gives-unique-existence-sometimes : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) →

    ((x : X) → is-subsingleton (A x))

  → ((Σ x ꞉ X , A x) × ((x y : X) → A x → A y → x ＝ y))
  → (∃! x ꞉ X , A x)

weak-unique-existence-gives-unique-existence-sometimes A i ((x , a) , u) = (x , a) , φ
 where
  φ : (σ : Σ A) → x , a ＝ σ
  φ (y , b) = to-subtype-＝ i (u x y a b)

ℕ-is-nno : hfunext 𝓤₀ 𝓤
         → (Y : 𝓤 ̇ ) (y₀ : Y) (g : Y → Y)
         → ∃! h ꞉ (ℕ → Y), (h 0 ＝ y₀) × (h ∘ succ ＝ g ∘ h)

ℕ-is-nno {𝓤} hfe Y y₀ g = γ
 where

  fe : dfunext 𝓤₀ 𝓤
  fe = hfunext-gives-dfunext hfe

  lemma₀ : (h : ℕ → Y) → ((h 0 ＝ y₀) × (h ∘ succ ∼ g ∘ h)) ◁ (h ∼ ℕ-iteration Y y₀ g)
  lemma₀ h = r , s , η
   where
    s : (h 0 ＝ y₀) × (h ∘ succ ∼ g ∘ h) → h ∼ ℕ-iteration Y y₀ g
    s (p , K) 0 = p
    s (p , K) (succ n) = h (succ n)                  ＝⟨ K n ⟩
                         g (h n)                     ＝⟨ ap g (s (p , K) n) ⟩
                         g (ℕ-iteration Y y₀ g n)    ＝⟨ refl _ ⟩
                         ℕ-iteration Y y₀ g (succ n) ∎

    r : codomain s → domain s
    r H = H 0 , (λ n → h (succ n)                  ＝⟨ H (succ n) ⟩
                       ℕ-iteration Y y₀ g (succ n) ＝⟨ refl _ ⟩
                       g (ℕ-iteration Y y₀ g n)    ＝⟨ ap g ((H n)⁻¹) ⟩
                       g (h n )                    ∎)

    remark : ∀ n H → pr₂ (r H) n ＝ H (succ n) ∙ (refl _ ∙ ap g ((H n)⁻¹))
    remark n H = refl _

    η : (z : (h 0 ＝ y₀) × (h ∘ succ ∼ g ∘ h)) → r (s z) ＝ z
    η (p , K) = q
     where
      v = λ (n : ℕ) →
       s (p , K) (succ n) ∙ (refl _ ∙ ap g ((s (p , K) n)⁻¹))                  ＝⟨ refl _ ⟩
       K n ∙  ap g (s (p , K) n) ∙ (refl _ ∙ ap g ((s (p , K) n)⁻¹))           ＝⟨ i   n ⟩
       K n ∙  ap g (s (p , K) n) ∙  ap g ((s (p , K) n) ⁻¹)                    ＝⟨ ii  n ⟩
       K n ∙ (ap g (s (p , K) n) ∙  ap g ((s (p , K) n) ⁻¹))                   ＝⟨ iii n ⟩
       K n ∙ (ap g (s (p , K) n) ∙ (ap g  (s (p , K) n))⁻¹)                    ＝⟨ iv  n ⟩
       K n ∙ refl _                                                            ＝⟨ refl _ ⟩
       K n                                                                     ∎
        where
         i   = λ (n : ℕ) → ap (K n ∙ ap g (s (p , K) n) ∙_)
                           (refl-left {_} {_} {_} {_} {ap g ((s (p , K) n)⁻¹)})
         ii  = λ (n : ℕ) → ∙assoc (K n) (ap g (s (p , K) n)) (ap g ((s (p , K) n)⁻¹))
         iii = λ (n : ℕ) → ap (λ - → K n ∙ (ap g (s (p , K) n) ∙ -)) (ap⁻¹ g (s (p , K) n) ⁻¹)
         iv  = λ (n : ℕ) → ap (K n ∙_) (⁻¹-right∙ (ap g (s (p , K) n)))

      q = r (s (p , K))                                                      ＝⟨ refl _ ⟩
          p , (λ n → s (p , K) (succ n) ∙ (refl _ ∙ ap g ((s (p , K) n)⁻¹))) ＝⟨ vi ⟩
          p , K                                                              ∎
       where
         vi = ap (p ,_) (fe v)

  lemma₁ = λ h → (h 0 ＝ y₀) × (h ∘ succ ＝ g ∘ h) ◁⟨ i h ⟩
                 (h 0 ＝ y₀) × (h ∘ succ ∼ g ∘ h) ◁⟨ lemma₀ h ⟩
                 (h ∼ ℕ-iteration Y y₀ g)        ◁⟨ ii h ⟩
                 (h ＝ ℕ-iteration Y y₀ g)        ◀
   where
    i  = λ (h : ℕ → Y) → Σ-retract (λ _ → ≃-gives-◁ (happly (h ∘ succ) (g ∘ h) , hfe _ _))
    ii = λ (h : ℕ → Y) → ≃-gives-▷ (happly h (ℕ-iteration Y y₀ g) , hfe _ _)

  lemma₂ : (Σ h ꞉ (ℕ → Y), (h 0 ＝ y₀) × (h ∘ succ ＝ g ∘ h))
         ◁ (Σ h ꞉ (ℕ → Y), h ＝ ℕ-iteration Y y₀ g)

  lemma₂ = Σ-retract lemma₁

  γ : is-singleton (Σ h ꞉ (ℕ → Y), (h 0 ＝ y₀) × (h ∘ succ ＝ g ∘ h))
  γ = retract-of-singleton lemma₂
                           (singleton-types-are-singletons (ℕ → Y) (ℕ-iteration Y y₀ g))

module finite-types (hfe : hfunext 𝓤₀ 𝓤₁) where

 fin :  ∃! Fin ꞉ (ℕ → 𝓤₀ ̇ )
               , (Fin 0 ＝ 𝟘)
               × (Fin ∘ succ ＝ λ n → Fin n + 𝟙)

 fin = ℕ-is-nno hfe (𝓤₀ ̇ ) 𝟘 (_+ 𝟙)

 Fin : ℕ → 𝓤₀ ̇
 Fin = pr₁ (center _ fin)

 Fin-equation₀ : Fin 0 ＝ 𝟘
 Fin-equation₀ = refl _

 Fin-equation-succ : Fin ∘ succ ＝ λ n → Fin n + 𝟙
 Fin-equation-succ = refl _

 Fin-equation-succ' : (n : ℕ) → Fin (succ n) ＝ Fin n + 𝟙
 Fin-equation-succ' n = refl _

 Fin-equation₁ : Fin 1 ＝ 𝟘 + 𝟙
 Fin-equation₁ = refl _

 Fin-equation₂ : Fin 2 ＝ (𝟘 + 𝟙) + 𝟙
 Fin-equation₂ = refl _

 Fin-equation₃ : Fin 3 ＝ ((𝟘 + 𝟙) + 𝟙) + 𝟙
 Fin-equation₃ = refl _

infixr -1 -∃!

\end{code}
