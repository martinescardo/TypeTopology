Martin Escardo, July 2026.

Free egroups, in pure MLTT.

For a type A of generators, we construct the free egroup on A and
prove its universal property. Unlike the HoTT/UF construction in
Groups.Free, this needs no function extensionality, propositional
truncation, quotients or univalence. The underlying type of the free
egroup is simply the type FA of words, and its equivalence relation is _∿_,
the symmetric-reflexive-transitive closure of the reduction
relation. There is no quotient because we are working with setoids:
the mediating map into a target egroup is the map h of EGroups.MediatingMap
directly, and its invariance under _∿_ is established from the
Church-Rosser property, with no propositional truncation.

Finally, we phrase the universal property as an adjunction: restriction
along the insertion of generators is a setoid isomorphism between the
setoid of homomorphisms out of the free egroup and the setoid of
functions from the generators into the underlying setoid of the target.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EGroups.FreeOnType where

open import MLTT.Spartan
open import MLTT.List renaming (_∷_ to _•_ ; _++_ to _◦_ ; ++-assoc to ◦-assoc)

open import Groups.Free using (module free-group-construction)
open import EGroups.Setoid
open import EGroups.Type
open import EGroups.MediatingMap

\end{code}

The free egroup on A. The underlying setoid is (FA , _∿_); the operation
is concatenation, with the empty word as unit and finv as inverse. All
the data comes from Groups.Free, imported directly, and is developed in
pure MLTT.

\begin{code}

free-egroup : (A : 𝓤 ̇ ) → EGroup 𝓤 𝓤
free-egroup A =
   (FA , _∿_ , (srt-reflexive _▷_ , srt-symmetric _▷_ , srt-transitive _▷_))
 , _◦_
 , ( ◦-cong-∿
   , (λ s t u → ＝-gives-∿ (◦-assoc s t u))
   , ( []
     , (λ s → srt-reflexive _▷_ s)
     , (λ s → ＝-gives-∿ (([]-right-neutral s)⁻¹))
     , (λ s → finv s , finv-left-∿ s , finv-right-∿ s) ) )
 where
  open free-group-construction A

\end{code}

The universal property. Given a target egroup 𝓖 and a map f : A → ⟨ 𝓖 ⟩,
the extension is the mediating map h of EGroups.MediatingMap, and it is the
unique homomorphism extending f, up to the equivalence relation.

\begin{code}

module free-egroup-universal-property
        {𝓤 : Universe}
        (A : 𝓤 ̇ )
        {𝓥 𝓦 : Universe}
        (𝓖 : EGroup 𝓥 𝓦)
        (f : A → ⟨ 𝓖 ⟩)
       where

 open free-group-construction A
 open E-group-theory 𝓖
 open ≈-reasoning (underlying-relation 𝓖) (E-refl 𝓖) (E-trans 𝓖)
 open free-group-mediating-map A ⟨ 𝓖 ⟩ (underlying-relation 𝓖)
       (E-refl 𝓖) (E-sym 𝓖) (E-trans 𝓖)
       (E-multiplication 𝓖) (E-is-congruence 𝓖) (E-assoc 𝓖)
       (E-unit 𝓖) (E-unit-left 𝓖) (E-unit-right 𝓖)
       (E-inv 𝓖) (E-inv-left 𝓖) (E-inv-right 𝓖)
       f

 private
  _*_    = E-multiplication 𝓖
  *-cong = E-is-congruence 𝓖
  e      = E-unit 𝓖
  invG   = E-inv 𝓖

 free-map : ⟨ free-egroup A ⟩ → ⟨ 𝓖 ⟩
 free-map = h

 free-map-is-hom : is-hom (free-egroup A) 𝓖 free-map
 free-map-is-hom = (λ {x} {y} → h-identifies-∿-related-points)
                 , (λ {x} {y} → h-is-hom x y)

 free-map-triangle : (a : A) → free-map (η a) ≈⟨ 𝓖 ⟩ f a
 free-map-triangle a = E-unit-right 𝓖 (f a)

\end{code}

Uniqueness: any homomorphism g extending f agrees with the extension up
to the equivalence relation. As in Groups.Free, the argument derives
preservation of the unit and inverses from the other assumptions.

\begin{code}

 free-map-is-unique : (g : ⟨ free-egroup A ⟩ → ⟨ 𝓖 ⟩)
                    → is-hom (free-egroup A) 𝓖 g
                    → ((a : A) → g (η a) ≈⟨ 𝓖 ⟩ f a)
                    → (s : ⟨ free-egroup A ⟩) → g s ≈⟨ 𝓖 ⟩ free-map s
 free-map-is-unique g g-hom@(_ , g-mult) g-tri = u
  where
   g-preserves-unit : g [] ≈⟨ 𝓖 ⟩ e
   g-preserves-unit = homs-preserve-unit (free-egroup A) 𝓖 g g-hom

   g-preserves-inv : (w : FA) → g (finv w) ≈⟨ 𝓖 ⟩ invG (g w)
   g-preserves-inv w = homs-preserve-inv (free-egroup A) 𝓖 g g-hom w

   u : (s : FA) → g s ≈⟨ 𝓖 ⟩ free-map s
   u [] = g-preserves-unit
   u ((₀ , a) • s) =
    g (η a ◦ s)   ≈[ g-mult {η a} {s} ]
    g (η a) * g s ≈[ *-cong (g-tri a) (u s) ]
    f a * h s     ≈∎
   u ((₁ , a) • s) =
    g (finv (η a) ◦ s)   ≈[ g-mult {finv (η a)} {s} ]
    g (finv (η a)) * g s ≈[ *-cong lemma (u s) ]
    invG (f a) * h s     ≈∎
     where
      lemma : g (finv (η a)) ≈⟨ 𝓖 ⟩ invG (f a)
      lemma = g (finv (η a))  ≈[ g-preserves-inv (η a) ]
              invG (g (η a))  ≈[ ≈-inv-cong (g (η a)) (f a) (g-tri a) ]
              invG (f a)      ≈∎

 free-map-is-unique₂ : (g₀ g₁ : ⟨ free-egroup A ⟩ → ⟨ 𝓖 ⟩)
                     → is-hom (free-egroup A) 𝓖 g₀
                     → is-hom (free-egroup A) 𝓖 g₁
                     → ((a : A) → g₀ (η a) ≈⟨ 𝓖 ⟩ f a)
                     → ((a : A) → g₁ (η a) ≈⟨ 𝓖 ⟩ f a)
                     → (s : ⟨ free-egroup A ⟩) → g₀ s ≈⟨ 𝓖 ⟩ g₁ s
 free-map-is-unique₂ g₀ g₁ i₀ i₁ t₀ t₁ s =
  E-trans 𝓖 (g₀ s) (free-map s) (g₁ s)
   (free-map-is-unique g₀ i₀ t₀ s)
   (E-sym 𝓖 (g₁ s) (free-map s) (free-map-is-unique g₁ i₁ t₁ s))

\end{code}

The universal property as an adjunction: restriction along η and
extension are mutually inverse setoid maps between the hom-setoid out
of the free egroup and the function setoid into the underlying setoid of
the target.

\begin{code}

free-adjunction : {𝓤 𝓥 𝓦 : Universe} (A : 𝓤 ̇ ) (𝓖 : EGroup 𝓥 𝓦)
                → hom-setoid (free-egroup A) 𝓖
                ≅ˢ function-setoid A (underlying-setoid 𝓖)
free-adjunction {𝓤} {𝓥} {𝓦} A 𝓖 = record
                                     { to        = to
                                     ; from      = from
                                     ; to-resp   = λ {x} {y} → to-resp {x} {y}
                                     ; from-resp = λ {x} {y} → from-resp {x} {y}
                                     ; to-from   = ε
                                     ; from-to   = θ
                                     }
 where
  open free-group-construction A using (η)
  open free-egroup-universal-property A 𝓖

  S : Setoid (𝓤 ⊔ 𝓥 ⊔ 𝓦) (𝓤 ⊔ 𝓦)
  S = hom-setoid (free-egroup A) 𝓖

  T : Setoid (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓦)
  T = function-setoid A (underlying-setoid 𝓖)

  to : ∣ S ∣ → ∣ T ∣
  to (g , _) a = g (η a)

  from : ∣ T ∣ → ∣ S ∣
  from f = free-map f , free-map-is-hom f

  to-resp : is-setoid-map S T to
  to-resp p a = p (η a)

  from-resp : is-setoid-map T S from
  from-resp {f} {f'} p = free-map-is-unique f'
                          (free-map f)
                          (free-map-is-hom f)
                          (λ a → E-trans 𝓖 _ _ _
                                  (free-map-triangle f a)
                                  (p a))

  ε : (f : ∣ T ∣) → to (from f) ≈⟦ T ⟧ f
  ε f a = free-map-triangle f a

  θ : (u : ∣ S ∣) → from (to u) ≈⟦ S ⟧ u
  θ u@(g , g-hom) s = E-sym 𝓖 _ _
                       (free-map-is-unique (to u) g g-hom
                         (λ a → E-refl 𝓖 (g (η a))) s)

\end{code}
