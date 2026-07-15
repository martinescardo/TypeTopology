Martin Escardo, July 2026.

This module defines the mediating map into a target egroup and
proves its basic properties. This paraphrases its construction in
Groups.Free, replacing the identity type by the underlying equivalence
relation, and removing the HoTT/UF assumptions.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

module EGroups.MediatingMap where

open import MLTT.Spartan
open import MLTT.List renaming (_∷_ to _•_ ; _++_ to _◦_ ; ++-assoc to ◦-assoc)

open import Groups.Free using (module free-group-construction)
open import EGroups.Setoid

\end{code}

The mediating map into a target group, given by raw components, whose
laws hold up to _≈_. This is the content of Groups.Free's
free-group-construction-step₃, with _≈_ replacing _＝_.

\begin{code}

module free-group-mediating-map
        {𝓤 : Universe}
        (A : 𝓤 ̇ )
        {𝓥 𝓦 : Universe}
        (G : 𝓥 ̇ )
        (_≈_ : G → G → 𝓦 ̇ )
        (≈r : reflexive  _≈_)
        (≈s : symmetric  _≈_)
        (≈t : transitive _≈_)
        (_*_ : G → G → G)
        (*-cong : is-congruence _≈_ _*_)
        (*-assoc : ≈-associative _≈_ _*_)
        (e : G)
        (ln : ≈-left-neutral  _≈_ e _*_)
        (rn : ≈-right-neutral _≈_ e _*_)
        (invG : G → G)
        (invl : (x : G) → (invG x * x) ≈ e)
        (invr : (x : G) → (x * invG x) ≈ e)
        (f : A → G)
       where

 open free-group-construction A
 open ≈-reasoning _≈_ ≈r ≈t

\end{code}

The mediating map h, exactly as in Groups.Free, by induction on words.

\begin{code}

 h : FA → G
 h []            = e
 h ((₀ , a) • s) = f a * h s
 h ((₁ , a) • s) = invG (f a) * h s

\end{code}

The following are as in Groups.Free, but replacing _＝_ by _≈_.

\begin{code}

 h⁻ : (x : X) → h (x • x ⁻ • []) ≈ e
 h⁻ (₀ , a) = f a * (invG (f a) * e) ≈[ *-cong (≈r (f a)) (rn (invG (f a))) ]
              f a * invG (f a)       ≈[ invr (f a) ]
              e                      ≈∎
 h⁻ (₁ , a) = invG (f a) * (f a * e) ≈[ *-cong (≈r (invG (f a))) (rn (f a)) ]
              invG (f a) * f a       ≈[ invl (f a) ]
              e                      ≈∎

 h-is-hom : (s t : FA) → h (s ◦ t) ≈ (h s * h t)
 h-is-hom [] t = ≈s _ _ (ln (h t))
 h-is-hom ((₀ , a) • s) t =
  f a * h (s ◦ t)   ≈[ *-cong (≈r (f a)) (h-is-hom s t) ]
  f a * (h s * h t) ≈[ ≈s _ _ (*-assoc (f a) (h s) (h t)) ]
  (f a * h s) * h t ≈∎
 h-is-hom ((₁ , a) • s) t =
  invG (f a) * h (s ◦ t)   ≈[ *-cong (≈r (invG (f a))) (h-is-hom s t) ]
  invG (f a) * (h s * h t) ≈[ ≈s _ _ (*-assoc (invG (f a)) (h s) (h t)) ]
  (invG (f a) * h s) * h t ≈∎

\end{code}

The map h respects the reduction relation _▷_, hence its
reflexive-transitive closure _▷⋆_, and therefore, using the
Church-Rosser property, the equivalence relation _∿_.

\begin{code}

 h-identifies-▷-related-points : {s t : FA} → s ▷ t → h s ≈ h t
 h-identifies-▷-related-points {s} {t} (u , v , y , p , q) =
  h s                            ≈[ ＝-to-≈ (ap h p) ]
  h (u ◦ y • y ⁻ • v)            ≈[ h-is-hom u (y • y ⁻ • v) ]
  h u * h (y • y ⁻ • v)          ≈[ *-cong (≈r (h u)) (h-is-hom (y • y ⁻ • []) v) ]
  h u * (h (y • y ⁻ • []) * h v) ≈[ *-cong (≈r (h u)) (*-cong (h⁻ y) (≈r (h v))) ]
  h u * (e * h v)                ≈[ *-cong (≈r (h u)) (ln (h v)) ]
  h u * h v                      ≈[ ≈s _ _ (h-is-hom u v) ]
  h (u ◦ v)                      ≈[ ＝-to-≈ (ap h (q ⁻¹)) ]
  h t                            ≈∎

 h-identifies-▷⋆-related-points : {s t : FA} → s ▷⋆ t → h s ≈ h t
 h-identifies-▷⋆-related-points {s} {t} (n , r) = γ n s t r
  where
   γ : (n : ℕ) (s t : FA) → s ▷[ n ] t → h s ≈ h t
   γ 0        s s refl        = ≈r (h s)
   γ (succ n) s t (z , d , i) = h s ≈[ h-identifies-▷-related-points d ]
                                h z ≈[ γ n z t i ]
                                h t ≈∎

 h-identifies-∿-related-points : {s t : FA} → s ∿ t → h s ≈ h t
 h-identifies-∿-related-points {s} {t} e' =
  γ (from-∿ Theorem[Church-Rosser] s t e')
  where
   γ : (Σ z ꞉ FA , (s ▷⋆ z) × (t ▷⋆ z)) → h s ≈ h t
   γ (z , σ , τ) = h s ≈[ h-identifies-▷⋆-related-points σ ]
                   h z ≈[ ≈s _ _ (h-identifies-▷⋆-related-points τ) ]
                   h t ≈∎

\end{code}
