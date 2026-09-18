Martin Escardo, May 2020

We now consider frames. A frame is a poset with all joins
and finite meets such that binary meets distribute over countable
joins.

TODO. Currently the order is derived from the binary meet. However,
for size reasons, it would be good to add the other as a separate
relation coinciding with the binary meet order.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons

module OrderedTypes.Frame (fe : Fun-Ext) where

open import UF.Equiv hiding (_≅_)
open import UF.SIP
open import UF.SIP-Examples
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier hiding (Ω₀)
open import UF.SubtypeClassifier-Properties
open import UF.Univalence

module _ (𝓤 𝓥 : Universe) where

 frame-structure : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
 frame-structure X = X × (X → X → X) × ({N : 𝓥 ̇ } → ((N → X) → X))

 frame-axioms : (X : 𝓤 ̇ ) → frame-structure X → 𝓤 ⊔ (𝓥 ⁺) ̇
 frame-axioms X (⊤ , _∧_ , ⋁) = I × II × III × IV × V × VI × VII × VIII
  where
   _≤_ : X → X → 𝓤 ̇
   x ≤ y = x ∧ y ＝ x

   I    = is-set X
   II   = (x : X) → x ∧ x ＝ x
   III  = (x y : X) → x ∧ y ＝ y ∧ x
   IV   = (x y z : X) → x ∧ (y ∧ z) ＝ (x ∧ y) ∧ z
   V    = (x : X) → x ∧ ⊤ ＝ x
   VI   = (x : X) {N : 𝓥 ̇ } (y : N → X) → x ∧ (⋁ y) ＝ ⋁ (n ↦ (x ∧ y n))
   VII  = {N : 𝓥 ̇ } (x : N → X) (n : N) → x n ≤ ⋁ x
   VIII = {N : 𝓥 ̇ } (x : N → X) (u : X) → ((n : N) → x n ≤ u) → ⋁ x ≤ u
 \end{code}

 Axioms I-IV say that (X , ⊤ , ∧) is a bounded semilattice, axiom VII
 says that ⋁ gives least upper bounds w.r.t. the induced partial order,
 and axiom VI says that binary meets distribute over countable joins.

 \begin{code}

 frame-axioms-is-prop : (X : 𝓤 ̇ ) (s : frame-structure X)
                      → is-prop (frame-axioms X s)
 frame-axioms-is-prop X (⊤ , _∧_ , ⋁) = prop-criterion δ
  where
   δ : frame-axioms X (⊤ , _∧_ , ⋁) → is-prop (frame-axioms X (⊤ , _∧_ , ⋁))
   δ (i , ii-vii) =
     ×₈-is-prop
       (being-set-is-prop fe)
       (Π-is-prop fe (λ x →           i {x ∧ x} {x}))
       (Π₂-is-prop fe (λ x y →        i {x ∧ y} {y ∧ x}))
       (Π₃-is-prop fe (λ x y z →      i {x ∧ (y ∧ z)} {(x ∧ y) ∧ z}))
       (Π-is-prop fe (λ x →           i {x ∧ ⊤} {x}))
       (Π-is-prop fe (λ x →
        implicit-Π-is-prop fe (λ N →
        Π-is-prop fe (λ y →           i {x ∧ ⋁ y} {⋁ (λ n → x ∧ y n)}))))
       (implicit-Π-is-prop fe (λ n
         →  Π₂-is-prop  fe (λ 𝕪 n →   i {𝕪 n ∧ ⋁ 𝕪} {𝕪 n})))
       (implicit-Π-is-prop fe (λ n
         →  Π₃-is-prop  fe (λ 𝕪 u _ → i {⋁ 𝕪 ∧ u} {⋁ 𝕪})))

 Frame : (𝓤 ⊔ 𝓥)⁺ ̇
 Frame = Σ A ꞉ 𝓤 ̇ , Σ s ꞉ frame-structure A , frame-axioms A s

 _≅[Frame]_ : Frame → Frame → 𝓤 ⊔ (𝓥 ⁺) ̇
 (A , (⊤ , _∧_ , ⋁) , _) ≅[Frame] (A' , (⊤' , _∧'_ , ⋁') , _) =

                         Σ f ꞉ (A → A')
                             , is-equiv f
                             × (f ⊤ ＝ ⊤')
                             × ((λ (a b : A) → f (a ∧ b)) ＝ (λ a b → f a ∧' f b))
                             × ((λ {N} (𝕒 : N → A) → f (⋁ 𝕒)) ＝ (λ {N} 𝕒 → ⋁' (n ↦ f (𝕒 n))))

 characterization-of-Frame-＝ : is-univalent 𝓤
                             → (A B : Frame)
                             → (A ＝ B) ≃ (A ≅[Frame] B)
 characterization-of-Frame-＝ ua =
   sip.characterization-of-＝ ua
    (sip-with-axioms.add-axioms
       frame-axioms
       frame-axioms-is-prop
      (sip-join.join
        pointed-type.sns-data
      (sip-join.join
        ∞-magma.sns-data
        ∞-hugemagma.sns-data)))

\end{code}

Example.

\begin{code}

open import UF.PropTrunc

module _ (pe : Prop-Ext)
         (pt  : propositional-truncations-exist)
       where

 open PropositionalTruncation pt

 _∧Ω_ : Ω 𝓤 → Ω 𝓤 → Ω 𝓤
 (P , i) ∧Ω (Q , j) = (P × Q) , ×-is-prop i j

 _≤Ω_ : Ω 𝓤 → Ω 𝓤 → 𝓤 ⁺ ̇
 𝕡 ≤Ω 𝕢 = 𝕡 ∧Ω 𝕢 ＝ 𝕡

 from-≤Ω : {𝕡 𝕢 : Ω 𝓤} → 𝕡 ≤Ω 𝕢 → (𝕡 holds → 𝕢 holds)
 from-≤Ω {𝓤} {P , i} {Q , j} l p = γ
  where
   r : P × Q ＝ P
   r = ap _holds l

   g : P → P × Q
   g = idtofun P (P × Q) (r ⁻¹)

   γ : Q
   γ = pr₂ (g p)

 to-≤Ω : {𝕡 𝕢 : Ω 𝓤} → (𝕡 holds → 𝕢 holds) → 𝕡 ≤Ω 𝕢
 to-≤Ω {𝓤} {P , i} {Q , j} f = γ
  where
   r : P × Q ＝ P
   r = pe (×-is-prop i j) i pr₁ (λ p → (p , f p))

   γ : ((P × Q) , _) ＝ (P , _)
   γ = to-subtype-＝ (λ _ → being-prop-is-prop fe) r

 ⋁Ω : {N : 𝓤 ̇ } → (N → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
 ⋁Ω {𝓤} {𝓥} {N} 𝕡 = (∃ n ꞉ N , (𝕡 n holds)) , ∃-is-prop

 Ω-qua-frame : ∀ 𝓤 𝓥 → Frame ((𝓤 ⊔ 𝓥)⁺) 𝓤
 Ω-qua-frame 𝓤 𝓥 = Ω₀ ,
                   (⊤ , _∧Ω_ , ⋁Ω) ,
                   Ω-is-set fe pe ,
                   ∧-is-idempotent ,
                   ∧-is-commutative ,
                   ∧-is-associative ,
                   ⊤-is-maximum ,
                   ∧-⋁-distributivity ,
                   ⋁-is-ub ,
                   ⋁-is-lb-of-ubs
  where
   Ω₀ = Ω (𝓤 ⊔ 𝓥)


   ∧-is-idempotent : (𝕡 : Ω₀) → 𝕡 ∧Ω 𝕡 ＝ 𝕡
   ∧-is-idempotent (P , i) = γ
    where
     r : P × P ＝ P
     r = pe (×-is-prop i i) i pr₁ (λ p → (p , p))

     γ : ((P × P) , _) ＝ (P , _)
     γ = to-subtype-＝ (λ _ → being-prop-is-prop fe) r


   ∧-is-commutative : (𝕡 𝕢 : Ω₀) → 𝕡 ∧Ω 𝕢 ＝ 𝕢 ∧Ω 𝕡
   ∧-is-commutative (P , i) (Q , j) = γ
    where
     r : P × Q ＝ Q × P
     r = pe (×-is-prop i j)
            (×-is-prop j i)
            (λ (p , q) → (q , p))
            (λ (q , p) → (p , q))

     γ : ((P × Q) , _) ＝ ((Q × P) , _)
     γ = to-subtype-＝ (λ _ → being-prop-is-prop fe) r

   ∧-is-associative : (𝕡 𝕢 𝕣 : Ω₀) → 𝕡 ∧Ω (𝕢 ∧Ω 𝕣) ＝ (𝕡 ∧Ω 𝕢) ∧Ω 𝕣
   ∧-is-associative (P , i) (Q , j) (R , k) = γ
    where
     r : P × (Q × R) ＝ (P × Q) × R
     r = pe (×-is-prop i (×-is-prop j k))
            (×-is-prop (×-is-prop i j) k)
            (λ (p , (q , r)) → ((p , q) , r))
            (λ ((p , q) , r) → (p , (q , r)))

     γ : ((P × (Q × R)) , _) ＝ (((P × Q) × R) , _)
     γ = to-subtype-＝ (λ _ → being-prop-is-prop fe) r

   ⊤-is-maximum : (𝕡 : Ω₀) → 𝕡 ≤Ω ⊤
   ⊤-is-maximum (P , i) = γ
    where
     r : P × 𝟙 ＝ P
     r = pe (×-is-prop i 𝟙-is-prop)
            i
            (λ (p , _) → p)
            (λ p → (p , ⋆))

     γ : ((P × 𝟙) , _) ＝ (P , _)
     γ = to-subtype-＝ (λ _ → being-prop-is-prop fe) r

   ∧-⋁-distributivity : (𝕡 : Ω₀) {N : 𝓤 ̇ } (𝕢 : N → Ω₀) → 𝕡 ∧Ω (⋁Ω 𝕢) ＝ ⋁Ω (n ↦ 𝕡 ∧Ω 𝕢 n)
   ∧-⋁-distributivity (P , i) {N} 𝕢 = γ
    where
     Q : N → 𝓤 ⊔ 𝓥 ̇
     Q n = 𝕢 n holds

     j : (n : N) → is-prop (Q n)
     j n = holds-is-prop (𝕢 n)

     α  : P × ∃ Q → ∃ n ꞉ N , P × Q n
     α (p , e) = ∥∥-rec ∃-is-prop (λ (n , q) → ∣ n , p , q ∣) e

     β : (∃ n ꞉ N , P × Q n) → P × ∃ Q
     β e = ∥∥-rec i (λ (n , p , q) → p) e ,
           ∥∥-rec ∃-is-prop (λ (n , p , q) → ∣ n , q ∣) e

     r : P × (∃ n ꞉ N , Q n) ＝ (∃ n ꞉ N , P × Q n)
     r = pe (×-is-prop i ∃-is-prop) ∃-is-prop α β


     γ : ((P × (∃ n ꞉ N , Q n)) , _) ＝ ((∃ n ꞉ N , P × Q n) , _)
     γ = to-subtype-＝ (λ _ → being-prop-is-prop fe) r


   ⋁-is-ub : {N : 𝓤 ̇ } (𝕡 : N → Ω₀) → (n : N) → 𝕡 n ≤Ω ⋁Ω 𝕡
   ⋁-is-ub 𝕡 n = to-≤Ω {_} {𝕡 n} {⋁Ω 𝕡} (λ p → ∣ n , p ∣)

   ⋁-is-lb-of-ubs : {N : 𝓤 ̇ } (𝕡 : N → Ω₀) (𝕦 : Ω₀)
                  → ((n : N) → 𝕡 n ≤Ω 𝕦)
                  → ⋁Ω 𝕡 ≤Ω 𝕦
   ⋁-is-lb-of-ubs {N} 𝕡 𝕦 φ = to-≤Ω {_} {⋁Ω 𝕡} {𝕦} γ
    where
     δ : (Σ n ꞉ N , 𝕡 n holds) → 𝕦 holds
     δ (n , p) = from-≤Ω {_} {𝕡 n} {𝕦} (φ n) p

     γ : (∃ n ꞉ N , 𝕡 n holds) → 𝕦 holds
     γ = ∥∥-rec (holds-is-prop 𝕦) δ


\end{code}
