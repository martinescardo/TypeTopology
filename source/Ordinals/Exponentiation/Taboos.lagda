Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu
December 2024 (with results potentially going back to November 2023)

Taboos involving ordinal exponentation.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.Taboos
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

-- curiosity : (P : 𝓤 ̇ ) → (pp : is-prop P) → exp {𝓤} 𝟚ₒ (prop-ordinal P pp) ＝ 𝟙ₒ +ₒ prop-ordinal P pp
-- curiosity {𝓤} P pp = transport⁻¹ (λ - → - ＝ 𝟙ₒ +ₒ (prop-ordinal P pp))
--                                  (^ₒ-behaviour 𝟚ₒ (prop-ordinal P pp) ∙ ap sup (dfunext fe' eq))
--                                  (⊴-antisym (sup F) (𝟙ₒ +ₒ prop-ordinal P pp)
--                                             (sup-is-lower-bound-of-upper-bounds F _ upper-bound)
--                                             (g , g-is-simulation))
--  where
--   F : 𝟙 + P → Ordinal 𝓤
--   F (inl _) = 𝟙ₒ
--   F (inr p) = 𝟚ₒ

--   eq : (i : 𝟙 + P) → (cases (λ _ → 𝟙ₒ) (λ b → exp 𝟚ₒ (prop-ordinal P pp ↓ b) ×ₒ 𝟚ₒ)) i ＝ F i
--   eq (inl _) = refl
--   eq (inr p) = exp 𝟚ₒ (prop-ordinal P pp ↓ p) ×ₒ 𝟚ₒ ＝⟨ ap (λ z → exp 𝟚ₒ z ×ₒ 𝟚ₒ) (prop-ordinal-↓ P pp p) ⟩
--                exp 𝟚ₒ 𝟘ₒ ×ₒ 𝟚ₒ                      ＝⟨ ap (_×ₒ 𝟚ₒ) (^ₒ-satisfies-zero-specification 𝟚ₒ) ⟩
--                𝟙ₒ ×ₒ 𝟚ₒ                             ＝⟨ 𝟙ₒ-left-neutral-×ₒ 𝟚ₒ ⟩
--                𝟚ₒ ∎

--   upper-bound : (i : 𝟙 + P) → F i ⊴ (𝟙ₒ +ₒ prop-ordinal P pp)
--   upper-bound (inl _) = (λ _ → inl _) , (λ x → dep-cases (λ _ → 𝟘-elim) (λ p → 𝟘-elim)) , (λ _ _ q → 𝟘-elim q)
--   upper-bound (inr p) = cases inl (λ _ → inr p) , (λ { (inr p') (inl _) _ → (inl _) , (⋆ , refl)
--                                                      ; (inl _) (inr p') q → 𝟘-elim q
--                                                      ; (inr p') (inr p'') q → 𝟘-elim q})
--                                                 , (λ { (inl _) (inr p') q → ⋆
--                                                      ; (inl _) (inl _) q → 𝟘-elim q})

--   f : (i : ⟨ 𝟙ₒ +ₒ prop-ordinal P pp ⟩) → ⟨ F i ⟩
--   f (inl _) = ⋆
--   f (inr p) = inr ⋆

--   g : (i : ⟨ 𝟙ₒ +ₒ prop-ordinal P pp ⟩) → ⟨ sup F ⟩
--   g i = pr₁ (sup-is-upper-bound F i) (f i)

--   g-is-initial-segment : is-initial-segment (𝟙ₒ +ₒ prop-ordinal P pp) (sup F) g
--   g-is-initial-segment (inl _) y q = inl ⋆ , pr₂ (pr₁ (pr₂ (sup-is-upper-bound F (inl _))) ⋆ y q)
--   g-is-initial-segment (inr p) y q with pr₁ (pr₂ (sup-is-upper-bound F (inr p))) (inr ⋆) y q
--   ... | inl _ , _ , refl = inl ⋆ , ⋆ , ↓-lc (sup F)
--                                             (pr₁ (sup-is-upper-bound F (inl ⋆)) ⋆)
--                                             (pr₁ (sup-is-upper-bound F (inr p)) (inl ⋆))
--                                             e
--    where
--     e = (sup F ↓ pr₁ (sup-is-upper-bound F (inl ⋆)) ⋆)
--           ＝⟨ initial-segment-of-sup-at-component F (inl ⋆) ⋆ ⟩
--         (𝟙ₒ ↓ ⋆)
--           ＝⟨ +ₒ-↓-left ⋆ ⟩
--         (𝟚ₒ ↓ inl ⋆)
--           ＝⟨ initial-segment-of-sup-at-component F (inr p) (inl ⋆) ⁻¹ ⟩
--         (sup F ↓ pr₁ (sup-is-upper-bound F (inr p)) (inl ⋆))
--           ∎

--   g-is-order-preserving : is-order-preserving (𝟙ₒ +ₒ prop-ordinal P pp) (sup F) g
--   g-is-order-preserving (inl _) (inr p) _ = ↓-reflects-order (sup F) (g (inl _)) (g (inr p)) q
--    where
--     eq₁ = sup F ↓ pr₁ (sup-is-upper-bound F (inl ⋆)) ⋆
--             ＝⟨ initial-segment-of-sup-at-component F (inl ⋆) ⋆ ⟩
--           𝟙ₒ ↓ ⋆
--             ＝⟨ prop-ordinal-↓ 𝟙 𝟙-is-prop ⋆ ⟩
--           𝟘ₒ
--             ∎
--     eq₂ = sup F ↓ pr₁ (sup-is-upper-bound F (inr p)) (inr ⋆)
--             ＝⟨ initial-segment-of-sup-at-component F (inr p) (inr ⋆) ⟩
--           (𝟚ₒ ↓ inr ⋆)
--             ＝⟨ successor-lemma-right 𝟙ₒ ⟩
--           𝟙ₒ
--             ∎
--     q : (sup F ↓ pr₁ (sup-is-upper-bound F (inl ⋆)) ⋆) ⊲ (sup F ↓ pr₁ (sup-is-upper-bound F (inr p)) (inr ⋆))
--     q = transport₂⁻¹ _⊲_ eq₁ eq₂ (⋆ , (prop-ordinal-↓ 𝟙 𝟙-is-prop ⋆ ⁻¹))
--   g-is-order-preserving (inl _) (inl _) q = 𝟘-elim q

--   g-is-simulation : is-simulation (𝟙ₒ +ₒ prop-ordinal P pp) (sup F) g
--   g-is-simulation = g-is-initial-segment , g-is-order-preserving


-- \end{code}

-- \begin{code}


-- Added 12 November 2024.
-- module _ {𝓤 : Universe}
--  where

--  [_]ₒ : (n : ℕ) → Ordinal 𝓤
--  [ 0 ]ₒ = 𝟘ₒ
--  [ 1 ]ₒ = 𝟙ₒ
--  [ succ n ]ₒ = [ n ]ₒ +ₒ 𝟙ₒ

--  -- TODO: Upstream(?)
--  {-
--  open import Naturals.Addition renaming (_+_ to _+ℕ_)
--  open import Naturals.Multiplication
--  []ₒ-preserves-addition : {n m : ℕ} → [ n ]ₒ +ₒ [ m ]ₒ ＝ [ n +ℕ m ]ₒ
--  []ₒ-preserves-addition {n} {0} = 𝟘ₒ-right-neutral [ n ]ₒ
--  []ₒ-preserves-addition {0} {1} = 𝟘ₒ-left-neutral 𝟙ₒ
--  []ₒ-preserves-addition {succ n} {1} = refl
--  []ₒ-preserves-addition {n} {succ (m'@(succ m))} =
--   ([ n ]ₒ +ₒ ([ m' ]ₒ +ₒ 𝟙ₒ)) ＝⟨ (+ₒ-assoc [ n ]ₒ [ m' ]ₒ 𝟙ₒ) ⁻¹ ⟩
--   (([ n ]ₒ +ₒ [ m' ]ₒ) +ₒ 𝟙ₒ) ＝⟨ ap (_+ₒ 𝟙ₒ) []ₒ-preserves-addition ⟩
--   ([ n +ℕ m' ]ₒ +ₒ 𝟙ₒ)        ∎

--  []ₒ-preserves-multiplication : {n m : ℕ} → [ n ]ₒ ×ₒ [ m ]ₒ ＝ [ n * m ]ₒ
--  []ₒ-preserves-multiplication {n} {0} = ×ₒ-𝟘ₒ-right [ n ]ₒ
--  []ₒ-preserves-multiplication {n} {1} = 𝟙ₒ-right-neutral-×ₒ [ n ]ₒ
--  []ₒ-preserves-multiplication {n} {succ (m'@(succ m))} =
--   [ n ]ₒ ×ₒ ([ m' ]ₒ +ₒ 𝟙ₒ)     ＝⟨ ×ₒ-successor [ n ]ₒ [ m' ]ₒ ⟩
--   ([ n ]ₒ ×ₒ [ m' ]ₒ) +ₒ [ n ]ₒ ＝⟨ ap (_+ₒ [ n ]ₒ) []ₒ-preserves-multiplication ⟩
--   [ n * m' ]ₒ +ₒ [ n ]ₒ         ＝⟨ []ₒ-preserves-addition ⟩
--   [ n * m' +ℕ n ]ₒ              ＝⟨ ap [_]ₒ (addition-commutativity (n * m') n) ⟩
--   [ n +ℕ (n * m') ]ₒ            ＝⟨ refl ⟩
--   [ n * succ m' ]ₒ              ∎
--  -}

-- -- TODO: Upstream and clean
-- holds-gives-equal-𝟙ₒ : {P : 𝓤 ̇ } (i : is-prop P) → P → prop-ordinal P i ＝ 𝟙ₒ
-- holds-gives-equal-𝟙ₒ {𝓤} {P} i p = eqtoidₒ (ua 𝓤) fe' (prop-ordinal P i) 𝟙ₒ (f , order-preserving-reflecting-equivs-are-order-equivs (prop-ordinal P i) 𝟙ₒ f (qinvs-are-equivs f ((λ _ → p) , (i p , 𝟙-is-prop ⋆))) (λ _ _ → 𝟘-elim) λ _ _ → 𝟘-elim)
--  where
--   f : P → 𝟙
--   f _ = ⋆

-- -- TODO: Think about a better name?
-- exp-weakly-monotone-in-base-implies-EM :
--    ((α β γ : Ordinal 𝓤) → 𝟙ₒ{𝓤} ⊴ α → α ⊲ β → (α ^ₒ γ ⊴ β ^ₒ γ))
--  → EM 𝓤
-- exp-weakly-monotone-in-base-implies-EM {𝓤} assumption P P-is-prop = VI (f x) refl
--  where
--   α β γ Pₒ : Ordinal 𝓤
--   α = [ 2 ]ₒ
--   Pₒ = prop-ordinal P P-is-prop
--   β = [ 3 ]ₒ +ₒ Pₒ
--   γ = [ 2 ]ₒ

--   I : α ⊲ β
--   I = (inl (inr ⋆) , ((successor-lemma-right α) ⁻¹ ∙ +ₒ-↓-left (inr ⋆)))

--   α-ineq : 𝟙ₒ ⊴ α
--   α-ineq = ⊲-gives-⊴ 𝟙ₒ α (successor-increasing 𝟙ₒ)

--   β-ineq : 𝟙ₒ ⊴ β
--   β-ineq = ⊴-trans 𝟙ₒ α β α-ineq (⊲-gives-⊴ α β I)

--   II : α ^ₒ γ ⊴ β ^ₒ γ
--   II = assumption α β γ α-ineq I

--   III : α ^ₒ γ ＝ α ×ₒ α
--   III = ^ₒ-𝟚ₒ-is-×ₒ α α-ineq

--   IV : β ^ₒ γ ＝ (β ×ₒ β)
--   IV = ^ₒ-𝟚ₒ-is-×ₒ β β-ineq

--   x : ⟨ α ×ₒ α ⟩
--   x = (inr ⋆ , inr ⋆)

--   𝕗 : (α ×ₒ α) ⊴ (β ×ₒ β)
--   𝕗 = ⊴-trans _ _ _ (≃ₒ-to-⊴ _ _ (idtoeqₒ _ _ (III ⁻¹)))
--                     (⊴-trans _ _ _ II (≃ₒ-to-⊴ _ _ (idtoeqₒ _ _ IV)))

--   f : ⟨ α ×ₒ α ⟩ → ⟨ β ×ₒ β ⟩
--   f = [ α ×ₒ α , β ×ₒ β ]⟨ 𝕗 ⟩

--   pattern ⊥β = inl (inl (inl ⋆))

--   f' : P → ⟨ α ×ₒ α ⟩ → ⟨ β ×ₒ β ⟩
--   f' p (inl ⋆ , inl ⋆) = (⊥β , ⊥β)
--   f' p (inr ⋆ , inl ⋆) = (inl (inl (inr ⋆)) , ⊥β)
--   f' p (inl ⋆ , inr ⋆) = (inl (inr ⋆) , ⊥β)
--   f' p (inr ⋆ , inr ⋆) = (inr p , ⊥β)

--   f'-simulation : (p : P) → is-simulation (α ×ₒ α) (β ×ₒ β) (f' p)
--   f'-simulation p = f'-initial-seg , f'-order-pres
--    where
--     f'-initial-seg : is-initial-segment (α ×ₒ α) (β ×ₒ β) (f' p)
--     f'-initial-seg (inr ⋆ , inl ⋆) (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
--      = (inl ⋆ , inl ⋆) , inr (refl , l) , refl
--     f'-initial-seg (inl ⋆ , inr ⋆) (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
--      = (inl ⋆ , inl ⋆) , inl ⋆ , refl
--     f'-initial-seg (inl ⋆ , inr ⋆) (inl (inl (inr ⋆)) , .⊥β) (inr (refl , l))
--      = (inr ⋆ , inl ⋆) , inl ⋆ , refl
--     f'-initial-seg (inr ⋆ , inr ⋆) (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
--      = (inl ⋆ , inl ⋆) , inl ⋆ , refl
--     f'-initial-seg (inr ⋆ , inr ⋆) (inl (inl (inr ⋆)) , .⊥β) (inr (refl , l))
--      = (inr ⋆ , inl ⋆) , inl ⋆ , refl
--     f'-initial-seg (inr ⋆ , inr ⋆) (inl (inr ⋆) , .⊥β)       (inr (refl , l))
--      = (inl ⋆ , inr ⋆) , inr (refl , l) , refl
--     f'-initial-seg (inl ⋆ , inl ⋆) (inl (inl (inl ⋆)) , .⊥β) (inr (refl , l))
--      = 𝟘-elim l
--     f'-initial-seg (inl ⋆ , inl ⋆) (inl (inl (inr ⋆)) , .⊥β) (inr (refl , l))
--      = 𝟘-elim l
--     f'-initial-seg (inl ⋆ , inl ⋆) (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
--     f'-initial-seg (inl ⋆ , inl ⋆) (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
--     f'-initial-seg (inl ⋆ , inr ⋆) (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
--     f'-initial-seg (inl ⋆ , inr ⋆) (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
--     f'-initial-seg (inr ⋆ , inl ⋆) (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
--     f'-initial-seg (inr ⋆ , inl ⋆) (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l
--     f'-initial-seg (inr ⋆ , inr ⋆) (y , inl (inl (inl ⋆))) (inl l) = 𝟘-elim l
--     f'-initial-seg (inr ⋆ , inr ⋆) (y , inl (inl (inr ⋆))) (inl l) = 𝟘-elim l

--     f'-order-pres : is-order-preserving (α ×ₒ α) (β ×ₒ β) (f' p)
--     f'-order-pres (inl ⋆ , inl ⋆) (inl ⋆ , inr ⋆) (inl l) = inr (refl , l)
--     f'-order-pres (inl ⋆ , inl ⋆) (inr ⋆ , inr ⋆) (inl l) = inr (refl , l)
--     f'-order-pres (inr ⋆ , inl ⋆) (inl ⋆ , inr ⋆) (inl l) = inr (refl , l)
--     f'-order-pres (inr ⋆ , inl ⋆) (inr ⋆ , inr ⋆) (inl l) = inr (refl , l)
--     f'-order-pres (x , inr ⋆) (y , inl ⋆) (inl l) = 𝟘-elim l
--     f'-order-pres (x , inr ⋆) (y , inr ⋆) (inl l) = 𝟘-elim l
--     f'-order-pres (inl ⋆ , inl ⋆) (inr ⋆ , x') (inr (refl , l)) = inr (refl , l)
--     f'-order-pres (inl ⋆ , inr ⋆) (inr ⋆ , x') (inr (refl , l)) = inr (refl , l)
--     f'-order-pres (inr ⋆ , x') (inl ⋆ , x') (inr (refl , l)) = 𝟘-elim l
--     f'-order-pres (inr ⋆ , x') (inr ⋆ , x') (inr (refl , l)) = 𝟘-elim l

--   V : (p : P) → f ∼ f' p
--   V p = at-most-one-simulation (α ×ₒ α) (β ×ₒ β) f (f' p) (pr₂ 𝕗) (f'-simulation p)

--   VI : (y : ⟨ β ×ₒ β ⟩) → f x ＝ y → P + ¬ P
--   VI (inl y , y') r = inr (λ p → +disjoint (ap pr₁ (VII p)))
--    where
--     VII : (p : P) → (inl y , y') ＝ (inr p , ⊥β)
--     VII p = (inl y , y') ＝⟨ r ⁻¹ ⟩
--             f x          ＝⟨ V p x ⟩
--             (inr p , ⊥β) ∎
--   VI (inr p , y') r = inl p

-- exp-monotone-in-base-implies-EM :
--    ((α β γ : Ordinal 𝓤) → 𝟙ₒ{𝓤} ⊴ α → α ⊴ β → (α ^ₒ γ ⊴ β ^ₒ γ))
--  → EM 𝓤
-- exp-monotone-in-base-implies-EM m =
--  exp-weakly-monotone-in-base-implies-EM (λ α β γ l i → m α β γ l (⊲-gives-⊴ α β i))

-- EM-implies-exp-monotone-in-base : EM 𝓤
--  → (α β γ : Ordinal 𝓤) → α ⊴ β → (α ^ₒ γ ⊴ β ^ₒ γ)
-- EM-implies-exp-monotone-in-base {𝓤} em α β γ l =
--  transfinite-induction-on-OO _ I γ
--  where
--   I : (γ : Ordinal 𝓤) → ((c : ⟨ γ ⟩) → (α ^ₒ (γ ↓ c) ⊴ β ^ₒ (γ ↓ c)))
--     → (α ^ₒ γ ⊴ β ^ₒ γ)
--   I γ IH = transport₂⁻¹ _⊴_ (^ₒ-behaviour α γ) (^ₒ-behaviour β γ)
--             (sup-monotone
--              (cases (λ _ → 𝟙ₒ) (λ c → α ^ₒ (γ ↓ c) ×ₒ α))
--              (cases (λ _ → 𝟙ₒ) (λ c → β ^ₒ (γ ↓ c) ×ₒ β))
--              κ)
--    where
--     κ : (i : 𝟙 + ⟨ γ ⟩)
--       → cases (λ _ → 𝟙ₒ) (λ c → α ^ₒ (γ ↓ c) ×ₒ α) i
--       ⊴ cases (λ _ → 𝟙ₒ) (λ c → β ^ₒ (γ ↓ c) ×ₒ β) i
--     κ (inl ⋆) = ⊴-refl 𝟙ₒ
--     κ (inr c) = EM-implies-induced-⊴-on-×ₒ em (α ^ₒ (γ ↓ c)) α
--                                               (β ^ₒ (γ ↓ c)) β
--                                               (IH c) l
