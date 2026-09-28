--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

July 1, 2021
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K #-}


open import Groups.Type
open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons-Properties

\end{code}

We define the kernel of a group homomorphism $f : A → B$ as the fiber of f
at the unit e⟨ B ⟩

\begin{code}

module Groups.Kernel where

module _ (A : Group 𝓤) (B : Group 𝓥)
         (f : ⟨ A ⟩ → ⟨ B ⟩) (isf : is-hom A B f) where

  kernel : Group (𝓤 ⊔ 𝓥)
  kernel = K , group-structure-k ,
               is-set-k ,
               assoc-k ,
               unit-k ,
               left-neutral-k ,
               (right-neutral-k , λ x → (inv-k x) , (inv-left-k x , inv-right-k x))
    where
      K : 𝓤 ⊔ 𝓥 ̇
      K = fiber f e⟨ B ⟩

      group-structure-k : group-structure K
      pr₁ (group-structure-k (a , p) (a' , p')) = a ·⟨ A ⟩ a'
      pr₂ (group-structure-k (a , p) (a' , p')) = f (a ·⟨ A ⟩ a')    ＝⟨ isf ⟩
                                                  f a ·⟨ B ⟩ f a'    ＝⟨ ap (λ v → v ·⟨ B ⟩ f a') p ⟩
                                                  e⟨ B ⟩ ·⟨ B ⟩ f a'  ＝⟨ unit-left B (f a') ⟩
                                                  f a'              ＝⟨ p' ⟩
                                                  e⟨ B ⟩ ∎

      is-set-k : is-set K
      is-set-k = Σ-is-set (groups-are-sets A) λ a → props-are-sets (groups-are-sets B)


      assoc-k : associative group-structure-k
      assoc-k (a , p) (a₁ , p₁) (a₂ , p₂) = to-Σ-＝ ((assoc A a a₁ a₂) , groups-are-sets B _ _)

      unit-k : K
      pr₁ unit-k = e⟨ A ⟩
      pr₂ unit-k = homs-preserve-unit A B f isf

      left-neutral-k : left-neutral unit-k group-structure-k
      left-neutral-k (a , p) = to-Σ-＝ ((unit-left A a) , (groups-are-sets B _ _))

      right-neutral-k : right-neutral unit-k group-structure-k
      right-neutral-k (a , p) = to-Σ-＝ ((unit-right A a) , (groups-are-sets B _ _))

      inv-k : K → K
      pr₁ (inv-k (a , p)) = inv A a
      pr₂ (inv-k (a , p)) = f (inv A a)                      ＝⟨ homs-preserve-invs A B f isf _ ⟩
                            inv B (f a)                      ＝⟨ ap (inv B) p ⟩
                            inv B (unit B)                   ＝⟨ (unit-right B _ ) ⁻¹ ⟩
                            (inv B (unit B)) ·⟨ B ⟩ (unit B)  ＝⟨ inv-left B _ ⟩
                             unit B ∎

      inv-left-k : (x : K) → group-structure-k (inv-k x) x ＝ unit-k
      inv-left-k (a , p) = to-Σ-＝ ((inv-left A a) , (groups-are-sets B _ _))

      inv-right-k : (x : K) → group-structure-k x (inv-k x) ＝ unit-k
      inv-right-k (a , p) = to-Σ-＝ ((inv-right A a) , (groups-are-sets B _ _))


  -- Canonical map from the kernel
  kernel-map : ⟨ kernel ⟩ → ⟨ A ⟩
  kernel-map = λ { (a , p) → a}

  -- Canonical map is a homomorphism
  kernel-map-is-hom : is-hom kernel A kernel-map
  kernel-map-is-hom = refl

  -- Canonical map is left cancellable
  kernel-map-is-lc : left-cancellable kernel-map
  kernel-map-is-lc {a , p} {a' , p'} u = to-Σ-＝ (u , (groups-are-sets B _ _))

  -- Canonical map is an embedding
  kernel-map-is-embedding : is-embedding kernel-map
  kernel-map-is-embedding = lc-maps-into-sets-are-embeddings kernel-map kernel-map-is-lc (groups-are-sets A)

  -- Kernel is normal
  kernel-is-normal : ⟨ A ⟩ → ⟨ kernel ⟩ → ⟨ kernel ⟩
  pr₁ (kernel-is-normal x (a , p)) = (x ·⟨ A ⟩ a) ·⟨ A ⟩ (inv A x)
  pr₂ (kernel-is-normal x (a , p)) = f ((x ·⟨ A ⟩ a) ·⟨ A ⟩ (inv A x))      ＝⟨ isf ⟩
                                     f (x ·⟨ A ⟩ a) ·⟨ B ⟩ f (inv A x)      ＝⟨ ap (λ v → v ·⟨ B ⟩ f (inv A x)) isf ⟩
                                     (f x ·⟨ B ⟩ f a) ·⟨ B ⟩ f (inv A x)    ＝⟨ i ⟩
                                     (f x ·⟨ B ⟩ e⟨ B ⟩) ·⟨ B ⟩ f (inv A x)  ＝⟨ ii ⟩
                                     f x ·⟨ B ⟩ f (inv A x)                ＝⟨ iii ⟩
                                     f x ·⟨ B ⟩ (inv B (f x))              ＝⟨ inv-right B _ ⟩
                                     e⟨ B ⟩ ∎
                        where
                         i   = ap (λ v → v ·⟨ B ⟩ f (inv A x)) (ap (λ v → f x ·⟨ B ⟩ v) p)
                         ii  = ap (λ v → v ·⟨ B ⟩ f (inv A x)) (unit-right B _)
                         iii = ap (λ v → f x ·⟨ B ⟩ v) (homs-preserve-invs A B f isf _)

\end{code}

The Universal property of the kernel is, as usual, that For any group
homomorphism $u : G → A$ such that $f ∘ u$ is the trivial map there exists a
(unique) homomorphism $G → \Ker(f)$. The map itself does not require
extra axioms

\begin{code}


  kernel-universal-map : (G : Group 𝓦) (u : ⟨ G ⟩ → ⟨ A ⟩) (isu : is-hom G A u)
                       → ((g : ⟨ G ⟩) → f (u g) ＝ e⟨ B ⟩)
                       → ⟨ G ⟩ → ⟨ kernel ⟩
  kernel-universal-map G u isu γ = λ g → (u g) , (γ g)

  kernel-universal-map-is-hom : (G : Group 𝓦) (u : ⟨ G ⟩ → ⟨ A ⟩) (isu : is-hom G A u)
                              → (γ : (g : ⟨ G ⟩) → f (u g) ＝ e⟨ B ⟩)
                              → is-hom G kernel (kernel-universal-map G u isu γ)
  kernel-universal-map-is-hom G u isu γ {x} {y} = to-Σ-＝ (isu , groups-are-sets B _ _)


  {-
     FIXME: to claim universality we must show that v : ⟨ G ⟩ → ⟨ kernel ⟩
            is unique.
            We should also prove it with equality kernel-map ∘ v ＝ u using
            function extensionality
   -}

  kernel-universal : (G : Group 𝓦) (u : ⟨ G ⟩ → ⟨ A ⟩) (isu : is-hom G A u)
                   → ((g : ⟨ G ⟩) → f (u g) ＝ e⟨ B ⟩)
                   → Σ (λ v → kernel-map ∘ v ∼ u)
  kernel-universal G u isu γ = kernel-universal-map G u isu γ , λ g → refl

\end{code}
