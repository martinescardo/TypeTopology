--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

June 2022
--------------------------------------------------------------------------------

This is an addendum to the file Groups. We prove that group axioms are
a proposition. This fact is needed in order to have a meaningful
definition of subgroups. Much of the first part is the same as in
UF.SIP-Examples.


July 2022
--------------------------------------------------------------------------------

This is vestigial. The proof that group-axioms is prop is in Groups.Type

--------------------------------------------------------------------------------


\begin{code}

{-# OPTIONS --safe --without-K #-}

module Groups.Type-Supplement where

open import Groups.Type hiding (group-axioms-is-prop)
open import MLTT.Spartan
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

First prove that monoid axioms are a proposition. Same as in
UF.SIP-Examples.

\begin{code}

monoid-axioms-is-prop : funext 𝓤 𝓤
                      → (X : 𝓤 ̇ )(m : monoid-structure X)
                      → is-prop (monoid-axioms X m)
monoid-axioms-is-prop fe X (_·_ , e) a = γ a
  where
    i : is-set X
    i = pr₁ a

    γ : is-prop (monoid-axioms X (_·_ , e))
    γ = ×-is-prop (being-set-is-prop fe)
        (×-is-prop
        (Π-is-prop fe (λ x → i))
        (×-is-prop
        (Π-is-prop fe (λ x → i))
        (Π-is-prop fe
          (λ x → Π-is-prop fe
            (λ y → Π-is-prop fe
              (λ z → i))))))

\end{code}

Version with the unit as part of the structure rather than part of the
axioms. We prove that the group axiom is a prop following
UF.SIP-Examples.

\begin{code}

group-structure₁ : 𝓤 ̇ → 𝓤 ̇
group-structure₁ X = Σ m ꞉ monoid-structure X , monoid-axioms X m

group-axiom₁ : (X : 𝓤 ̇ )→ monoid-structure X → 𝓤 ̇
group-axiom₁ X (_·_ , e) = (x : X) → Σ x' ꞉ X , (x' · x ＝ e) × (x · x' ＝ e)

group-axiom₁-is-prop : funext 𝓤 𝓤
                     → (X : 𝓤 ̇)
                     → (s : group-structure₁ X)
                     → is-prop (group-axiom₁ X (pr₁ s))
group-axiom₁-is-prop fe X ((_·_ , e) , m) = γ
  where
    i : is-set X
    i = pr₁ m

    j : (x : X) → is-prop (Σ x' ꞉ X , (x' · x ＝ e) × (x · x' ＝ e))
    j x (y , q , _) (z , _ , u) = to-subtype-＝ (λ x' → ×-is-prop i i) p
      where
        p : y ＝ z
        p = inv-lemma X _·_ e m x y z q u

    γ : is-prop (group-axiom₁ X (_·_ , e))
    γ = Π-is-prop fe j

\end{code}


Conversion between the two types of group axioms.

\begin{code}
group-axiom₁→axioms : (X : 𝓤 ̇)
                    → (s : group-structure₁ X)
                    → (γ : group-axiom₁ X (pr₁ s))
                    → group-axioms X (pr₁ (pr₁ s))
group-axiom₁→axioms X ((_·_ , e) , (i , l , r , a)) γ = i , a , (e , (l , (r , γ)))

group-axioms→axiom₁ : (X : 𝓤 ̇)
                    → (_·_ : group-structure X)
                    → (s : group-axioms X _·_)
                    → group-structure₁ X → group-axiom₁ X (monoid-structure-of (X , _·_ , s))
group-axioms→axiom₁ X _·_ (i , a , e , l , r , γ) = λ { _ → γ}

-- just to be clear
group-axioms→axiom₁' : (X : 𝓤 ̇)
                     → (_·_ : group-structure X)
                     → (s : group-axioms X _·_)
                     → group-structure₁ X × group-axiom₁ X (monoid-structure-of (X , _·_ , s))
group-axioms→axiom₁' X _·_ (i , a , e , l , r , γ) = ((_·_ , e) , (i , l , r , a)) , γ

\end{code}


Direct proof that the group axioms (as in Groups) are a
proposition. This ought to be in Groups.lagda.

\begin{code}

group-axioms-is-prop : funext 𝓤 𝓤
                     → (X : 𝓤 ̇)
                     → (_·_ : group-structure X)
                     → is-prop (group-axioms X _·_)
group-axioms-is-prop fe X _·_ s = γ s
  where
    i : is-set X
    i = pr₁ s

    α : is-prop (associative _·_)
    α = Π-is-prop fe
                  (λ x → Π-is-prop fe
                                   (λ y →  Π-is-prop fe
                                                     (λ z → i)))

    β : is-prop ( Σ e ꞉ X , left-neutral e _·_ ×
                            right-neutral e _·_ ×
                            ((x : X) → Σ x' ꞉ X , (x' · x ＝ e) × (x · x' ＝ e)) )
    β (e , l , _ , _) (e' , _ , r , _) = to-subtype-＝ η p
      where
        p : e ＝ e'
        p = e      ＝⟨ (r e) ⁻¹ ⟩
            e · e' ＝⟨ l e' ⟩
            e' ∎

        η : (x : X) → is-prop (left-neutral x _·_ ×
                               right-neutral x _·_ ×
                               ((x₁ : X) → Σ x' ꞉ X , (x' · x₁ ＝ x) × (x₁ · x' ＝ x)))
        η x t = ε t
          where
            ε : is-prop (left-neutral x _·_ ×
                               right-neutral x _·_ ×
                               ((x₁ : X) → Σ x' ꞉ X , (x' · x₁ ＝ x) × (x₁ · x' ＝ x)))
            ε = ×-is-prop (Π-is-prop fe (λ _ → i))
                (×-is-prop (Π-is-prop fe (λ _ → i))
                 (Π-is-prop fe ε'))
                    where
                      ε' : (x₁ : X) → is-prop (Σ x' ꞉ X , (x' · x₁ ＝ x) × (x₁ · x' ＝ x))
                      ε' x₁ (u , v) (u' , v') = to-subtype-＝ (λ x₂ → ×-is-prop i i) q
                        where
                          q : u ＝ u'
                          q = u             ＝⟨ (pr₁ (pr₂ t) u) ⁻¹ ⟩
                              u · x         ＝⟨ ap (λ a → u · a) (pr₂ v') ⁻¹ ⟩
                              u · (x₁ · u') ＝⟨ (pr₁ (pr₂ s) _ _ _) ⁻¹ ⟩
                              (u · x₁) · u' ＝⟨ ap (λ a → a · u') (pr₁ v) ⟩
                              x · u'        ＝⟨ pr₁ t u' ⟩
                              u' ∎

    γ : is-prop (group-axioms X _·_)
    γ = ×-is-prop (being-set-is-prop fe)
        (×-is-prop α β)
\end{code}
