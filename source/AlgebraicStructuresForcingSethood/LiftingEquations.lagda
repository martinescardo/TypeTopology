Jakub Opršal, 27th March – 1st Apr 2026

My goal here is to explain how to lift height 1 equations to the loop space
assuming all the operations are idempotent, i.e., satisfy

  ∀ x , f x ... x = x

A 'height 1 equation' is informally an equation that does not involve
composition. Formally, it is an equation of the form 

  ∀ x , f (x ∘ π) = g (x ∘ σ)

where f : (N → A) → A, g : (N' → A) → A, π : N → M, σ : N' → M. For simplicity,
I will assume N' = M and σ = λ x → x, hence I will only lift identities of the form

  ∀ x, f (x ∘ π) = g x

Originally, I though that I will only work with functions of finite arity, i.e.,
I'd assume that M and N are of the form `Fin m` and `Fin n` for some n m : ℕ,
but the proofs are easier if I work with general types. I will need to assume
function extensionallity for functions with domain M or N, and actually not
more! I believe that `Fin n` is extensional in this sense, but leave the proof
for latter.

Let me start with formulating function extensionality. We will onnly require
that the arity is extensional.

\begin{code}

open import MLTT.Spartan
open import UF.Equiv

module AlgebraicStructuresForcingSethood.LiftingEquations where

happly : {A : Type} {B : A → Type}
       → {f g : (a : A) → B a}
       → f ＝ g
       → (a : A)
       → f a ＝ g a
happly refl a = refl

is-extensional : (A : Type) → (A → Type) → Type
is-extensional A B = (f g : (a : A) → B a) → is-equiv (happly {f = f} {g = g})

\end{code}

The next block deals with conjugation, and will be useful in conjuction with
commuting paths.

\begin{code}

sym : {A : Type} {a b : A} → (a ＝ b) → (b ＝ a)
sym = _⁻¹

refl∙ : {A : Type} {a b : A} (q : a ＝ b) → refl ∙ q ＝ q
refl∙ refl = refl

∙-cancel : {A : Type} {a b c : A} (q : a ＝ b) {p p' : b ＝ c}
         → q ∙ p ＝ q ∙ p'
         → p ＝ p'
∙-cancel refl {p = p} {p' = p'} h = sym (refl∙ p) ∙ h ∙ (refl∙ p')

eq-cong : {A : Type} {a a' b b' : A}
        → (a ＝ a')
        → (b ＝ b')
        → (a ＝ b)
        → (a' ＝ b')
eq-cong refl refl p = p

eq-cong-refl : {A : Type} {a a' : A} (q : a ＝ a')
             → eq-cong q q refl ＝ refl
eq-cong-refl refl = refl

eq-cong-sq : {A : Type} {a a' b b' : A} (h₁ : a ＝ a') (h₂ : b ＝ b') (p : a ＝ b)
          → h₁ ∙ eq-cong h₁ h₂ p ＝ p ∙ h₂
eq-cong-sq refl refl p = (refl∙ p)

\end{code}

Next, we start lifting operations. To make an N-ary function f act on loops as
an N-ary function, we will need that:

1. f is idempotent, i.e., f (λ _ → a) ＝ a;
2. functions with domain N are extensional.

The second point is needed since ap f naturally acts on paths over functions N
→ A, rather than N-tuples of paths.

\begin{code}

const : {A B : Type} (a : A) → B → A
const a = (λ _ → a)

Ω : {A N : Type}
  → (f : (N → A) → A)
  → (idem : (a : A) → f (const a) ＝ a)
  → (dom-is-ext : (B : N → Type) → is-extensional N B)
  → {a : A}
  → (N → a ＝ a)
  → a ＝ a
Ω {A} {N} f idem dom-is-ext {a} p = eq-cong (idem a) (idem a) (ap f p')
  where
   funext = pr₁ (pr₁ (dom-is-ext (λ _ → A) (const a) (const a)))
   p' : const a ＝ const a
   p' = funext p

module lift-equation
       {A : Type}
       (loops-commute : {a : A} (p q : a ＝ a) → p ∙ q ＝ q ∙ p)
       {N M : Type}
       (f : (N → A) → A)
       (idem-f : (a : A) → f (const a) ＝ a)
       (dom-f-is-ext : (B : N → Type) → is-extensional N B)
       (g : (M → A) → A)
       (idem-g : (a : A) → g (const a) ＝ a)
       (dom-g-is-ext : (B : M → Type) → is-extensional M B)
       (π : N → M)
       (eq : (a : M → A) → (f (a ∘ π) ＝ g a))
       where

 Ωf : {a : A} → (p : N → a ＝ a) → a ＝ a
 Ωf = Ω f idem-f dom-f-is-ext

 Ωg : {a : A} → (p : M → a ＝ a) → a ＝ a
 Ωg = Ω g idem-g dom-g-is-ext

 conjugation-triv : {a : A} (g : a ＝ a) (p : a ＝ a)
                  → eq-cong g g p ＝ p
 conjugation-triv g p = ∙-cancel g (eq-cong-sq g g p ∙ loops-commute p g)

 one-eq-cong : {a b c : A} (p : a ＝ a) (q : b ＝ b)
               (h₀ : a ＝ b) (h₁ : a ＝ c) (h₂ : b ＝ c)
             → eq-cong h₀ h₀ p ＝ q
             → eq-cong h₁ h₁ p ＝ eq-cong h₂ h₂ q
 one-eq-cong p q refl h₁ refl eq = conjugation-triv h₁ p ∙ eq

 funext' : {a : A} → (N → a ＝ a) → (const {_} {N} a ＝ const {_} {N} a)
 funext' {a} = pr₁ (pr₁ (dom-f-is-ext (λ _ → A) (const a) (const a)))

 funext : {a : A} → (M → a ＝ a) → (const {_} {M} a ＝ const {_} {M} a)
 funext {a} = pr₁ (pr₁ (dom-g-is-ext (λ _ → A) (const a) (const a)))

 path-minor : {a : A}
            → (p : M → a ＝ a)
            → funext' (p ∘ π) ＝ ap (λ x → x ∘ π) (funext p)
 path-minor {a} p = goal-finally
   where
    happly-funext : happly (funext p) ＝ p
    happly-funext = pr₂ (pr₁ (dom-g-is-ext (λ _ → A) _ _)) p

    happly-funext' : happly (funext' (p ∘ π)) ＝ p ∘ π
    happly-funext' = pr₂ (pr₁ (dom-f-is-ext (λ _ → A) _ _)) (p ∘ π)

    goal : (i : N)
         → happly (funext' (p ∘ π)) i ＝
           happly (ap (λ x → x ∘ π) (funext p)) i
    goal i =
     happly (funext' (p ∘ π)) i               ＝⟨ I ⟩
     (p (π i))                                ＝⟨ II ⟩
     happly (funext p) (π i)                  ＝⟨ III ⟩
     happly (ap (λ x → x ∘ π) (funext p)) i   ∎
      where
       I = ap (λ q → q i) happly-funext'
       II = ap (λ q → q (π i)) (sym happly-funext)
       III = happly-ap (funext p) i
        where
         happly-ap : {g g' : M → A} (q : g ＝ g') (i : N)
                   → happly {f = g} {g = g'} q (π i) ＝
                     happly {f = (g ∘ π)} {g = (g' ∘ π)} (ap (λ x → x ∘ π) q) i
         happly-ap refl i = refl
    
    goal' : happly (funext' (p ∘ π)) ＝ happly (ap (λ x → x ∘ π) (funext p))
    goal' = funext'' goal
     where
      funext'' =  pr₁ (pr₁ (dom-f-is-ext (λ _ → a ＝ a)
                                         (happly (funext' (p ∘ π)))
                                         (happly (ap (λ x → x ∘ π) (funext p)))))
    
    goal-finally : funext' (p ∘ π) ＝ ap (λ x → x ∘ π) (funext p)
    goal-finally = sym I ∙ II ∙ III -- follows since happly is a section
     where
      is-section-happly = pr₂ (dom-f-is-ext (λ _ → A) (const a) (const a))
      I   = pr₂ is-section-happly (funext' (p ∘ π))
      II  = ap (pr₁ is-section-happly) goal'
      III = pr₂ is-section-happly (ap (λ x → x ∘ π) (funext p))

 eq^ : {a a' : M → A}
     → (p : a ＝ a')
     → eq-cong (eq a) (eq a') (ap f (ap (λ x → x ∘ π) p)) ＝ ap g p
 eq^ {a} {a} refl = eq-cong-refl (eq a)

 Ωeq : {a : A} → (p : M → a ＝ a) → Ωf (p ∘ π) ＝ Ωg p
 Ωeq {a} p =
  Ωf (p ∘ π)                                                         ＝⟨ refl ⟩
  eq-cong (idem-f a) (idem-f a) (ap f (funext' (p ∘ π)))             ＝⟨ I ⟩
  eq-cong (idem-f a) (idem-f a) (ap f (ap (λ x → x ∘ π) (funext p))) ＝⟨ II ⟩
  eq-cong (idem-g a) (idem-g a) (ap g (funext p))                    ＝⟨ refl ⟩
  Ωg p ∎
   where
    I = ap (λ x → eq-cong (idem-f a) (idem-f a) (ap f x)) (path-minor p)
    II = one-eq-cong _ _ (eq (const a)) (idem-f a) (idem-g a) (eq^ (funext p))

\end{code}
