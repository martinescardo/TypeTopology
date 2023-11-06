Brendan Hart 2019-2020

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module PCF.Lambda.Substitution
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import Naturals.Properties
open import PCF.Lambda.AbstractSyntax pt
open import UF.Base
open import UF.Subsingletons

ids : {n : ℕ} {Γ : Context n} {A : type} → Γ ∋ A → PCF Γ A
ids x = v x

exts-cong : {n m : ℕ} {Γ : Context n} {Δ : Context m} {B : type}
          → {f g : ∀ {A} → Γ ∋ A → PCF Δ A}
          → (∀ {A} → f {A = A} ∼ g)
          → (∀ {A} → (exts f {B}) {A = A} ∼ (exts g))
exts-cong eq Z     = refl
exts-cong eq (S x) = ap (rename S) (eq x)

subst-cong : {n m : ℕ} {Γ : Context n} {Δ : Context m} {B : type}
           → (M M' : PCF Γ B)
           → (f g : ∀ {A} → Γ ∋ A → PCF Δ A)
           → M ＝ M'
           → (∀ {A} → f {A = A} ∼ g)
           → subst f M ＝ subst g M'

subst-cong Zero .Zero f g refl eq = refl

subst-cong (Succ M) .(Succ M) f g refl eq = ap Succ
                                             (subst-cong M M f g refl eq)

subst-cong (Pred M) .(Pred M) f g refl eq = ap Pred
                                             (subst-cong M M f g refl eq)

subst-cong (IfZero M M₁ M₂)
          .(IfZero M M₁ M₂) f g refl eq   = ap₃ IfZero
                                             (subst-cong M M f g refl eq)
                                             (subst-cong M₁ M₁ f g refl eq)
                                             (subst-cong M₂ M₂ f g refl eq)

subst-cong (ƛ M) .(ƛ M) f g refl eq = ap ƛ
                                       (subst-cong M M
                                         (exts f)
                                         (exts g)
                                         refl
                                         (exts-cong eq))

subst-cong (M · M₁) .(M · M₁) f g refl eq = ap₂ _·_
                                             (subst-cong M M f g refl eq)
                                             (subst-cong M₁ M₁ f g refl eq)

subst-cong (v x) .(v x) f g refl eq = eq x

subst-cong (Fix M) .(Fix M) f g refl eq = ap Fix
                                           (subst-cong M M f g refl eq)

ext-cong : {n m : ℕ} {Γ : Context n} {Δ : Context m} {B : type}
         → {ρ ρ' : ∀ {A} → Γ ∋ A → Δ ∋ A}
         → (∀ {A} → ρ {A = A} ∼ ρ')
         → (∀ {A} → (ext ρ {B}) {A = A} ∼ ext ρ')
ext-cong eq Z     = refl
ext-cong eq (S x) = ap S (eq x)

compose-ext : {n m k : ℕ}
              {Γ : Context n} {Δ : Context m} {Σ : Context k}
              {B : type}
              (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
              (ρ' : ∀ {A} → Δ ∋ A → Σ ∋ A)
              {A : type}
            → (x : (Γ ’ B) ∋ A) → (ext ρ' ∘ ext ρ) x ＝ ext (ρ' ∘ ρ) x
compose-ext ρ ρ' Z     = refl
compose-ext ρ ρ' (S x) = refl

rename-cong : {n m : ℕ}
              {Γ : Context n} {Δ : Context m}
              {B : type}
              (M M' : PCF Γ B)
              (ρ ρ' : ∀ {A} → Γ ∋ A → Δ ∋ A)
            → M ＝ M'
            → (∀ {A} → ρ {A = A} ∼ ρ')
            → rename ρ M ＝ rename ρ' M'

rename-cong Zero .Zero ρ ρ' refl eq = refl

rename-cong (Succ M) .(Succ M) ρ ρ' refl eq =
 ap Succ
  (rename-cong M M ρ ρ' refl eq)

rename-cong (Pred M) .(Pred M) ρ ρ' refl eq =
 ap Pred
  (rename-cong M M ρ ρ' refl eq)

rename-cong (IfZero M M₁ M₂) .(IfZero M M₁ M₂) ρ ρ' refl eq =
 ap₃ IfZero
  (rename-cong M M ρ ρ' refl eq)
  (rename-cong M₁ M₁ ρ ρ' refl eq)
  (rename-cong M₂ M₂ ρ ρ' refl eq)

rename-cong (ƛ M) .(ƛ M) ρ ρ' refl eq =
 ap ƛ
   (rename-cong M M (ext ρ) (ext ρ') refl (ext-cong eq))

rename-cong (M · M₁) .(M · M₁) ρ ρ' refl eq =
 ap₂ _·_
  (rename-cong M M ρ ρ' refl eq)
  (rename-cong M₁ M₁ ρ ρ' refl eq)

rename-cong (v x) .(v x) ρ ρ' refl eq =
 ap v
   (eq x)

rename-cong (Fix M) .(Fix M) ρ ρ' refl eq =
 ap Fix
   (rename-cong M M ρ ρ' refl eq)

compose-rename : {n m k : ℕ}
                 {Γ : Context n} {Δ : Context m} {Σ : Context k}
                 {B : type}
                 (M : PCF Γ B)
                 (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
                 (ρ' : ∀ {A} → Δ ∋ A → Σ ∋ A)
               → rename ρ' (rename ρ M) ＝ rename (ρ' ∘ ρ) M

compose-rename Zero ρ ρ' = refl

compose-rename (Succ M) ρ ρ' = ap Succ (compose-rename M ρ ρ')

compose-rename (Pred M) ρ ρ' = ap Pred (compose-rename M ρ ρ')

compose-rename (IfZero M M₁ M₂) ρ ρ' = ap₃ IfZero
                                        (compose-rename M ρ ρ')
                                        (compose-rename M₁ ρ ρ')
                                        (compose-rename M₂ ρ ρ')
compose-rename (ƛ M) ρ ρ' = ap ƛ γ
  where
    γ : rename (ext ρ') (rename (ext ρ) M) ＝ rename (ext (ρ' ∘ ρ)) M
    γ = rename (ext ρ') (rename (ext ρ) M) ＝⟨ i ⟩
        rename ((ext ρ') ∘ (ext ρ)) M      ＝⟨ ii ⟩
        rename (ext (λ x → ρ' (ρ x))) M    ∎
     where
      i   = compose-rename M (ext ρ) (ext ρ')
      ii  = rename-cong M M
             (λ {A} x → ext ρ' (ext ρ x))
             (ext (λ {A} x → ρ' (ρ x)))
             refl
             (compose-ext ρ ρ')

compose-rename (M · M₁) ρ ρ' = ap₂ _·_
                                (compose-rename M ρ ρ')
                                (compose-rename M₁ ρ ρ')

compose-rename (v x) ρ ρ' = refl

compose-rename (Fix M) ρ ρ' = ap Fix
                               (compose-rename M ρ ρ')

exts-ids : {n : ℕ} {Γ : Context n} {B A : type}
           (x : (Γ ’ B) ∋ A)
         → exts ids x ＝ ids x
exts-ids Z     = refl
exts-ids (S x) = refl

sub-id : {n : ℕ}
         {Γ : Context n} {B : type}
         (M : PCF Γ B)
       → subst ids M ＝ M
sub-id Zero = refl
sub-id (Succ M) = ap Succ (sub-id M)
sub-id (Pred M) = ap Pred (sub-id M)
sub-id (IfZero M M₁ M₂) = ap₃ IfZero (sub-id M) (sub-id M₁) (sub-id M₂)
sub-id (ƛ M) = ap ƛ γ
  where
    γ : subst (exts ids) M ＝ M
    γ = subst (exts ids) M ＝⟨ subst-cong M M (exts ids) ids refl exts-ids ⟩
        subst ids M        ＝⟨ sub-id M ⟩
        M                  ∎

sub-id (M · M₁) = ap₂ _·_ (sub-id M) (sub-id M₁)
sub-id (v x) = refl
sub-id (Fix M) = ap Fix (sub-id M)

exts-ext-ids :  {n m : ℕ}
                {Γ : Context n} {Δ : Context m}
                {B : type}
                (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
                {A : type}
                (x : (Γ ’ B) ∋ A)
             → (ids ∘ ext ρ) x ＝ exts (ids ∘ ρ) x
exts-ext-ids ρ Z     = refl
exts-ext-ids ρ (S x) = refl

rename-is-a-substitution : {n m : ℕ}
                           {Γ : Context n}
                           {Δ : Context m}
                           {A : type}
                           (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
                           (M : PCF Γ A)
                         → rename ρ M ＝ subst (ids ∘ ρ) M
rename-is-a-substitution ρ Zero = refl
rename-is-a-substitution ρ (Succ M) = ap Succ (rename-is-a-substitution ρ M)
rename-is-a-substitution ρ (Pred M) = ap Pred (rename-is-a-substitution ρ M)
rename-is-a-substitution ρ (IfZero M M₁ M₂) = ap₃ IfZero
                                               (rename-is-a-substitution ρ M)
                                               (rename-is-a-substitution ρ M₁)
                                               (rename-is-a-substitution ρ M₂)
rename-is-a-substitution ρ (ƛ M) = ap ƛ γ
  where
    γ : rename (ext ρ) M ＝ subst (exts (ids ∘ ρ)) M
    γ = rename (ext ρ) M         ＝⟨ i ⟩
        subst (ids ∘ ext ρ) M    ＝⟨ ii ⟩
        subst (exts (ids ∘ ρ)) M ∎
      where
        i = rename-is-a-substitution (ext ρ) M
        ii = subst-cong M M (ids ∘ ext ρ) (exts (ids ∘ ρ)) refl (exts-ext-ids ρ)

rename-is-a-substitution ρ (M · M₁) = ap₂ _·_
                                      (rename-is-a-substitution ρ M)
                                      (rename-is-a-substitution ρ M₁)

rename-is-a-substitution ρ (v x) = refl
rename-is-a-substitution ρ (Fix M) = ap Fix (rename-is-a-substitution ρ M)

_；_ : {n m k : ℕ}
       {Γ : Context n} {Δ : Context m} {Σ : Context k}
      → (∀ {A} → Γ ∋ A → PCF Δ A)
      → (∀ {A} → Δ ∋ A → PCF Σ A)
      → (∀ {A} → Γ ∋ A → PCF Σ A)
_；_ f g x = subst g (f x)

sub-ids-right : {n m : ℕ}
                {Γ : Context n} {Δ : Context m}
                (f : ∀ {A} → Γ ∋ A → PCF Δ A)
                {A : type}
                (x : Γ ∋ A)
              → (f ； ids) x ＝ f x
sub-ids-right f x = sub-id (f x)

ext-comp : {a b c : ℕ}
           {Γ : Context a} {Δ : Context b} {Ψ : Context c}
           (ρ₁ : ∀ {A} → Γ ∋ A → Δ ∋ A)
           (ρ₂ : ∀ {A} → Δ ∋ A → Ψ ∋ A)
           {B A : type}
           (x : (Γ ’ B) ∋ A)
         → (ext ρ₂ ∘ ext ρ₁) x ＝ ext (ρ₂ ∘ ρ₁) x
ext-comp ρ₁ ρ₂ Z     = refl
ext-comp ρ₁ ρ₂ (S x) = refl

exts-ext : {a b c : ℕ}
           {Γ : Context a} {Δ : Context b} {Ψ : Context c}
           (B : type)
           (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
           (σ : ∀ {A} → Δ ∋ A → PCF Ψ A)
           {A : type}
           (x : (Γ ’ B) ∋ A)
          → (exts σ ∘ ext ρ) x ＝ exts (σ ∘ ρ) x
exts-ext B ρ σ  Z    = refl
exts-ext B ρ σ (S x) = refl

rename-comp : {a b c : ℕ}
              {Γ : Context a} {Δ : Context b} {Ψ : Context c}
              {B : type}
              (ρ₁ : ∀ {A} → Γ ∋ A → Δ ∋ A)
              (ρ₂ : ∀ {A} → Δ ∋ A → Ψ ∋ A)
              (t : PCF Γ B)
            → rename ρ₂ (rename ρ₁ t) ＝ rename (ρ₂ ∘ ρ₁) t
rename-comp ρ₁ ρ₂ Zero = refl
rename-comp ρ₁ ρ₂ (Succ t) = ap Succ (rename-comp ρ₁ ρ₂ t)
rename-comp ρ₁ ρ₂ (Pred t) = ap Pred (rename-comp ρ₁ ρ₂ t)
rename-comp ρ₁ ρ₂ (IfZero t t₁ t₂) = ap₃ IfZero
                                      (rename-comp ρ₁ ρ₂ t)
                                      (rename-comp ρ₁ ρ₂ t₁)
                                      (rename-comp ρ₁ ρ₂ t₂)

rename-comp ρ₁ ρ₂ (ƛ {_} {_} {σ} t) = ap ƛ γ
  where
    IH : rename (ext ρ₂) (rename (ext ρ₁) t) ＝ rename (ext ρ₂ ∘ ext ρ₁) t
    IH = rename-comp (ext ρ₁) (ext ρ₂) t

    i : rename (ext ρ₂ ∘ ext ρ₁) t
      ＝ rename (λ {A} → ext (λ {A = A₁} x → ρ₂ (ρ₁ x))) t
    i = rename-cong t t (ext ρ₂ ∘ ext ρ₁) (ext (ρ₂ ∘ ρ₁)) refl (ext-comp ρ₁ ρ₂)

    γ : rename (ext ρ₂) (rename (ext ρ₁) t) ＝ rename (ext (ρ₂ ∘ ρ₁)) t
    γ = IH ∙ i

rename-comp ρ₁ ρ₂ (t · t₁) = ap₂ _·_
                             (rename-comp ρ₁ ρ₂ t)
                             (rename-comp ρ₁ ρ₂ t₁)

rename-comp ρ₁ ρ₂ (v x) = refl
rename-comp ρ₁ ρ₂ (Fix t) = ap Fix (rename-comp ρ₁ ρ₂ t)

subst-rename-comp : {a b c : ℕ}
                    {Γ : Context a} {Δ : Context b} {Ψ : Context c}
                    {A : type}
                    (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
                    (σ : ∀ {A} → Δ ∋ A → PCF Ψ A)
                    (M : PCF Γ A)
                  → subst σ (rename ρ M) ＝ subst (σ ∘ ρ) M
subst-rename-comp ρ σ Zero = refl
subst-rename-comp ρ σ (Succ M) = ap Succ (subst-rename-comp ρ σ M)
subst-rename-comp ρ σ (Pred M) = ap Pred (subst-rename-comp ρ σ M)
subst-rename-comp ρ σ (IfZero M M₁ M₂) = ap₃ IfZero
                                          (subst-rename-comp ρ σ M)
                                          (subst-rename-comp ρ σ M₁)
                                          (subst-rename-comp ρ σ M₂)

subst-rename-comp ρ σ (ƛ {_} {_} {A} M) = ap ƛ γ
  where
    IH : subst (exts σ) (rename (ext ρ) M) ＝ subst (exts σ ∘ ext ρ) M
    IH = subst-rename-comp (ext ρ) (exts σ) M

    δ : subst (exts σ ∘ ext ρ) M ＝ subst (exts (σ ∘ ρ)) M
    δ = subst-cong M M
         (λ {A} → exts σ ∘ ext ρ) (exts (λ {A} → σ ∘ ρ))
         refl
         (exts-ext A ρ σ)

    γ : subst (exts σ) (rename (ext ρ) M) ＝ subst (exts (σ ∘ ρ)) M
    γ = IH ∙ δ

subst-rename-comp ρ σ (M · M₁) = ap₂ _·_
                                  (subst-rename-comp ρ σ M)
                                  (subst-rename-comp ρ σ M₁)

subst-rename-comp ρ σ (v x) = refl
subst-rename-comp ρ σ (Fix M) = ap Fix (subst-rename-comp ρ σ M)

rename-exts : {a b c : ℕ}
              {Γ : Context a} {Δ : Context b} {Ψ : Context c}
              {B : type}
              (σ : ∀ {A} → Γ ∋ A → PCF Δ A)
              (ρ : ∀ {A} → Δ ∋ A → Ψ ∋ A)
              {A : type}
              (x : (Γ ’ B) ∋ A)
            → rename (ext ρ) (exts σ x) ＝ exts (rename ρ ∘ σ) x
rename-exts σ ρ Z     = refl
rename-exts σ ρ (S x) = γ
  where
    γ : rename (ext ρ) (exts σ (S x)) ＝ rename S (rename ρ (σ x))
    γ = rename (ext ρ) (exts σ (S x)) ＝⟨ i ⟩
        rename (S ∘ ρ) (σ x)          ＝⟨ ii ⟩
        rename S (rename ρ (σ x))     ∎
      where
        i  = rename-comp S (ext ρ) (σ x)
        ii = rename-comp ρ S (σ x) ⁻¹

subst-rename-commute : {a b c : ℕ}
                       {Γ : Context a} {Δ : Context b} {Ψ : Context c}
                       {A : type}
                       (σ : ∀ {A} → Γ ∋ A → PCF Δ A)
                       (ρ : ∀ {A} → Δ ∋ A → Ψ ∋ A)
                       (M : PCF Γ A)
                     → rename ρ (subst σ M) ＝ subst (rename ρ ∘ σ) M
subst-rename-commute σ ρ Zero = refl
subst-rename-commute σ ρ (Succ M) = ap Succ
                                     (subst-rename-commute σ ρ M)

subst-rename-commute σ ρ (Pred M) = ap Pred
                                     (subst-rename-commute σ ρ M)

subst-rename-commute σ ρ (IfZero M M₁ M₂) = ap₃ IfZero
                                             (subst-rename-commute σ ρ M)
                                             (subst-rename-commute σ ρ M₁)
                                             (subst-rename-commute σ ρ M₂)
subst-rename-commute σ ρ (ƛ M) = ap ƛ γ
  where
    IH : rename (ext ρ) (subst (exts σ) M) ＝ subst (rename (ext ρ) ∘ exts σ) M
    IH = subst-rename-commute (exts σ) (ext ρ) M

    δ : subst (rename (ext ρ) ∘ exts σ) M
      ＝ subst (exts (rename ρ ∘ σ)) M
    δ = subst-cong M M
         (rename (ext ρ) ∘ exts σ)
         (exts (rename ρ ∘ σ))
         refl
         (rename-exts σ ρ)

    γ : rename (ext ρ) (subst (exts σ) M) ＝ subst (exts (rename ρ ∘ σ)) M
    γ = IH ∙ δ

subst-rename-commute σ ρ (M · M₁) = ap₂ _·_
                                     (subst-rename-commute σ ρ M)
                                     (subst-rename-commute σ ρ M₁)

subst-rename-commute σ ρ (v x) = refl
subst-rename-commute σ ρ (Fix M) = ap Fix (subst-rename-commute σ ρ M)

exts-seq : {n m k : ℕ}
           {Γ : Context n} {Δ : Context m} {Σ : Context k}
           {B : type}
           (f : ∀ {A} → Γ ∋ A → PCF Δ A)
           (g : ∀ {A} → Δ ∋ A → PCF Σ A)
           {A : type}
           (x : (Γ ’ B) ∋ A)
         → (exts f ； exts g) x ＝ exts (f ； g) x
exts-seq f g  Z    = refl
exts-seq f g (S x) = subst (exts g) (rename S (f x)) ＝⟨ i ⟩
                      subst (exts g ∘ S) (f x)       ＝⟨ refl ⟩
                      subst (rename S ∘ g) (f x)     ＝⟨ ii ⟩
                      rename S (subst g (f x))       ∎
  where
    i  = subst-rename-comp S (exts g) (f x)
    ii = subst-rename-commute g S (f x) ⁻¹

sub-sub-lem : {n m k : ℕ}
              {Γ : Context n} {Δ : Context m} {Σ : Context k}
              {B : type}
              (M : PCF Γ B)
              (f : ∀ {A} → Γ ∋ A → PCF Δ A)
              (g : ∀ {A} → Δ ∋ A → PCF Σ A)
             → subst g (subst f M) ＝ subst (f ； g) M
sub-sub-lem Zero f g = refl
sub-sub-lem (Succ M) f g = ap Succ (sub-sub-lem M f g)
sub-sub-lem (Pred M) f g = ap Pred (sub-sub-lem M f g)
sub-sub-lem (IfZero M M₁ M₂) f g = ap₃ IfZero
                                    (sub-sub-lem M f g)
                                    (sub-sub-lem M₁ f g)
                                    (sub-sub-lem M₂ f g)
sub-sub-lem (ƛ M) f g = ap ƛ γ
  where
    IH : subst (exts g) (subst (exts f) M) ＝ subst (exts f ； exts g) M
    IH = sub-sub-lem M (exts f) (exts g)

    δ : subst (exts f ； exts g) M ＝ subst (exts (f ； g)) M
    δ = subst-cong M M (exts f ； exts g) (exts (f ； g)) refl (exts-seq f g)

    γ : subst (exts g) (subst (exts f) M) ＝ subst (exts (f ； g)) M
    γ = IH ∙ δ

sub-sub-lem (M · M₁) f g = ap₂ _·_ (sub-sub-lem M f g) (sub-sub-lem M₁ f g)
sub-sub-lem (v x) f g = refl
sub-sub-lem (Fix M) f g = ap Fix (sub-sub-lem M f g)

cons-cong : {n m : ℕ}
            {Γ : Context n} {Δ : Context m}
            {B : type}
            {M M' : PCF Δ B}
            {f g : ∀ {A} → Γ ∋ A → PCF Δ A}
          → M ＝ M'
          → (∀ {A} → f {A = A} ∼ g )
          → (∀ {A} → (x : (Γ ’ B) ∋ A) → extend-with M f x ＝ extend-with M' g x)
cons-cong refl eq Z     = refl
cons-cong refl eq (S x) = eq x

exts-extend-S : {n m : ℕ}
                {Γ : Context n} {Δ : Context m}
                {B : type}
                (f : ∀ {A} → (x : Γ ∋ A) → PCF Δ A)
                {A : type}
                (x : (Γ ’ B) ∋ A)
              → exts f x ＝ extend-with (v Z) (f ； (ids ∘ S)) x
exts-extend-S f Z     = refl
exts-extend-S f (S x) = rename-is-a-substitution S (f x)

；-cong : {n m k : ℕ}
          {Γ : Context n} {Δ : Context m} {Σ : Context k}
          (f g : ∀ {A} → Γ ∋ A → PCF Δ A)
          (h j : ∀ {A} → Δ ∋ A → PCF Σ A)
         → (∀ {A} → f {A = A} ∼ g)
         → (∀ {A} → h {A = A} ∼ j)
         → {A : type}
           (x : Γ ∋ A)
         → (f ； h) x ＝ (g ； j) x
；-cong f g h j x x₁ x₂ = subst-cong (f x₂) (g x₂) h j (x x₂) x₁

；-assoc : {n m k l : ℕ}
          {Γ : Context n} {Δ : Context m} {Σ : Context k} {ψ : Context l}
          (f : ∀ {A} → Γ ∋ A → PCF Δ A)
          (g : ∀ {A} → Δ ∋ A → PCF Σ A)
          (h : ∀ {A} → Σ ∋ A → PCF ψ A)
          {A : type}
          (x : Γ ∋ A)
        → ((f ； g) ； h) x ＝ (f ； (g ； h)) x

；-assoc f g h x = sub-sub-lem (f x) g h

subst-Z-cons-ids : {n : ℕ}
                   {Γ : Context n}
                   {B : type}
                   (M₁ : PCF Γ B)
                   {A : type}
                   (x : (Γ ’ B) ∋ A)
                 → replace-first B Γ M₁ x ＝ extend-with M₁ ids x
subst-Z-cons-ids M₁ Z     = refl
subst-Z-cons-ids M₁ (S x) = refl

sub-dist : {n m k : ℕ}
           {Γ : Context n} {Δ : Context m} {Σ : Context k}
           {B : type}
           (M : PCF Δ B)
           (f : ∀ {A} → Γ ∋ A → PCF Δ A)
           (g : ∀ {A} → Δ ∋ A → PCF Σ A)
           {A : type}
           (x : (Γ ’ B) ∋ A)
         → (extend-with M f ； g) x ＝ (extend-with (subst g M) (f ； g)) x
sub-dist M f g Z     = refl
sub-dist M f g (S x) = refl

extend-replace-first : {C : type}
                       {n m : ℕ}
                       {Γ : Context n} {Δ : Context m}
                       (M₁ : PCF Δ C)
                       (f : ∀ {A} → Γ ∋ A → PCF Δ A)
                       {B : type}
                       (x : (Γ ’ C) ∋ B)
                     → extend-with M₁ f x ＝ (exts f ； replace-first C Δ M₁) x
extend-replace-first {σ} {n} {m} {Γ} {Δ} M₁ f x = γ ⁻¹
 where
  γ : (exts f ； replace-first σ Δ M₁) x ＝ extend-with M₁ f x
  γ = (exts f ； replace-first σ Δ M₁) x                               ＝⟨ i ⟩
        ((extend-with (v Z) (f ； (ids ∘ S))) ； extend-with M₁ ids) x ＝⟨ ii ⟩
         extend-with (subst (extend-with M₁ ids) (v Z)) ((f ； (ids ∘ S)) ；
         extend-with M₁ ids) x                                         ＝⟨ iii ⟩
         extend-with M₁ (((f ； (ids ∘ S)) ； extend-with M₁ ids)) x   ＝⟨ iv ⟩
         extend-with M₁ (f ； ((ids ∘ S) ； extend-with M₁ ids)) x     ＝⟨ iiiii ⟩
         extend-with M₁ (f ； ids) x                                   ＝⟨ vi ⟩
         extend-with M₁ f x                                            ∎
   where
    i     = ；-cong
             (exts f)
             (extend-with (v Z) (f ； (ids ∘ S)))
             (replace-first σ Δ M₁)
             (extend-with M₁ ids)
             (exts-extend-S f)
             (subst-Z-cons-ids M₁)
             x

    ii    = sub-dist (v Z) (f ； (ids ∘ S)) (extend-with M₁ ids) x
    iii   = cons-cong refl (λ x₁ → refl) x
    iv    = cons-cong refl (；-assoc f (ids ∘ S) (extend-with M₁ v)) x
    iiiii = cons-cong refl (λ x₁ → refl) x
    vi    = cons-cong refl (sub-ids-right f) x

subst-ext : {A B : type}
            {n m : ℕ}
            {Γ : Context n} {Δ : Context m}
            (M : PCF (Γ ’ A) B) (M₁ : PCF Δ A)
            (f : ∀ {A} → Γ ∋ A → PCF Δ A)
          → subst (extend-with M₁ f) M
          ＝ subst (replace-first A Δ M₁) (subst (exts f) M)
subst-ext {σ} {τ} {n} {m} {Γ} {Δ} M M₁ f = ii ∙ i ⁻¹
  where
    i : subst (replace-first σ Δ M₁) (subst (exts f) M)
      ＝ subst (exts f ； (replace-first σ Δ M₁)) M
    i = sub-sub-lem M (exts f) (replace-first σ Δ M₁)

    ii : subst (extend-with M₁ f) M
       ＝ subst (exts f ； replace-first σ Δ M₁) M
    ii = subst-cong M M
          (extend-with M₁ f)
          (exts f ； replace-first σ Δ M₁)
          refl
          (extend-replace-first M₁ f)

\end{code}
