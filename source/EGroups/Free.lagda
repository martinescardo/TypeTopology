Martin Escardo, July 2026.

The free egroup on a setoid.

Its underlying type is the type FA of words on the generators, and its
equivalence relation is convertibility _∿_. The operation is
concatenation _◦_, and we check that it is a congruence for _∿_, that
the group laws hold up to _∿_, and that the generators are inserted by
η. We then prove that it is free, in the sense that every setoid map
from the generators into an egroup extends along η to a homomorphism,
uniquely up to the equivalence relation of that egroup.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import MLTT.List renaming (_∷_ to _•_ ; _++_ to _◦_ ; ++-assoc to ◦-assoc)
open import Relations.SRTclosure

module EGroups.Free
        {𝓤 : Universe}
        (A : 𝓤 ⁺ ̇ )
        (_≈_ : A → A → 𝓤 ̇ )
        (≈r : reflexive  _≈_)
        (≈s : symmetric  _≈_)
        (≈t : transitive _≈_)
       where

open import EGroups.Reduction A _≈_ ≈r ≈s ≈t
open import EGroups.Setoid
open import EGroups.Type

\end{code}

Identities give convertibilities, and convertibility is a congruence
for cons, a special case of the congruence for concatenation.

\begin{code}

＝-gives-∿ : {s t : FA} → s ＝ t → s ∿ t
＝-gives-∿ {s} refl = srt-reflexive _▷_ s

•-∿ : (x : X) {s t : FA} → s ∿ t → (x • s) ∿ (x • t)
•-∿ x e = ∿-◦-right (x • []) e

\end{code}

We record the two basic cancellations as convertibilities.

\begin{code}

cancel : (x : X) → (x • (x ⁻) • []) ∿ []
cancel x = srt-extension _▷_ (x • (x ⁻) • []) []
            ([] , [] , x , (x ⁻) , refl , refl , ≈[X]-refl (x ⁻))

cancel⁻ : (x : X) (s : FA) → ((x ⁻) • x • s) ∿ s
cancel⁻ x s = srt-extension _▷_ ((x ⁻) • x • s) s
               ([] , s , (x ⁻) , x , refl , refl , to-≈[X] ((inv-invol x) ⁻¹))

\end{code}

The word inverse reverses the word and inverts each letter.

\begin{code}

inv : FA → FA
inv []      = []
inv (x • s) = inv s ◦ ((x ⁻) • [])

inv-left : (x : FA) → (inv x ◦ x) ∿ []
inv-left []      = srt-reflexive _▷_ []
inv-left (a • s) =
 srt-transitive _▷_ (inv (a • s) ◦ (a • s)) (inv s ◦ ((a ⁻) • a • s)) []
  (＝-gives-∿ (◦-assoc (inv s) ((a ⁻) • []) (a • s)))
  (srt-transitive _▷_ (inv s ◦ ((a ⁻) • a • s)) (inv s ◦ s) []
    (∿-◦-right (inv s) (cancel⁻ a s))
    (inv-left s))

inv-right : (x : FA) → (x ◦ inv x) ∿ []
inv-right []      = srt-reflexive _▷_ []
inv-right (a • s) =
 srt-transitive _▷_
  ((a • s) ◦ inv (a • s)) (a • ((s ◦ inv s) ◦ ((a ⁻) • []))) []
  (＝-gives-∿ (ap (a •_) ((◦-assoc s (inv s) ((a ⁻) • [])) ⁻¹)))
  (srt-transitive _▷_ (a • ((s ◦ inv s) ◦ ((a ⁻) • []))) (a • ((a ⁻) • [])) []
    (•-∿ a (∿-◦-left (inv-right s) ((a ⁻) • [])))
    (cancel a))

\end{code}

We assemble the free egroup.

\begin{code}

underlying-setoid-of-free-egroup : Setoid (𝓤 ⁺) (𝓤 ⁺)
underlying-setoid-of-free-egroup = FA
                                 , _∿_
                                 , srt-reflexive  _▷_
                                 , srt-symmetric  _▷_
                                 , srt-transitive _▷_

free-egroup : EGroup (𝓤 ⁺) (𝓤 ⁺)
free-egroup = underlying-setoid-of-free-egroup
            , _◦_
            , (λ {x} {x'} {y} {y'} → ◦-cong-∿ {x} {x'} {y} {y'})
            , (λ x y z → ＝-gives-∿ (◦-assoc x y z))
            , []
            , (λ x → srt-reflexive _▷_ x)
            , (λ x → ＝-gives-∿ (([]-right-neutral x) ⁻¹))
            , (λ x → inv x , inv-left x , inv-right x)

\end{code}

The underlying type of the free egroup is FA, and its insertion of
generators is η : A → FA.

\begin{code}

ηᴳ : A → ⟨ free-egroup ⟩
ηᴳ = η

\end{code}

The universal property. Given an egroup 𝓖 and a setoid map f from the
setoid of generators to the underlying setoid of 𝓖, we extend f to a
homomorphism from the free egroup, and show that the extension is
unique up to the equivalence relation of 𝓖.

The extension h is defined by recursion on words, sending a generator
to its value under f and a formally inverted generator to the inverse
of that value. That f is a setoid map is needed already to see that h
identifies the two sides of a reduction, because we cancel adjacent
letters whose generators are merely ≈-related.

\begin{code}

module free-egroup-universal-property
        {𝓥 𝓦 : Universe}
        (𝓖 : EGroup 𝓥 𝓦)
        (f : A → ⟨ 𝓖 ⟩)
        (f-resp : {a b : A} → a ≈ b → f a ≈⟨ 𝓖 ⟩ f b)
       where

 open egroup-theory 𝓖
 open ≈-reasoning (underlying-relation 𝓖) (erefl 𝓖) (etrans 𝓖)

 private
  _*_    = emultiplication-of 𝓖
  *-cong = econgruence-of 𝓖
  eᴳ     = eunit-of 𝓖
  invᴳ   = einv 𝓖

 h : FA → ⟨ 𝓖 ⟩
 h []            = eᴳ
 h ((₀ , a) • s) = f a * h s
 h ((₁ , a) • s) = invᴳ (f a) * h s

\end{code}

The map h respects the letter-wise relation on words, and it is a
homomorphism from concatenation to the operation of 𝓖.

\begin{code}

 h-respects-≈[FA] : (s t : FA) → s ≈[FA] t → h s ≈⟨ 𝓖 ⟩ h t
 h-respects-≈[FA] [] [] ⋆ = erefl 𝓖 eᴳ
 h-respects-≈[FA] ((₀ , a) • s) ((₀ , b) • t) ((refl , q) , r) =
  *-cong (f-resp q) (h-respects-≈[FA] s t r)
 h-respects-≈[FA] ((₁ , a) • s) ((₁ , b) • t) ((refl , q) , r) =
  *-cong (≈-inv-cong (f a) (f b) (f-resp q)) (h-respects-≈[FA] s t r)

 h-is-hom : (s t : FA) → h (s ◦ t) ≈⟨ 𝓖 ⟩ (h s * h t)
 h-is-hom [] t = esym 𝓖 _ _ (eunit-left 𝓖 (h t))
 h-is-hom ((₀ , a) • s) t =
  f a * h (s ◦ t)   ≈[ *-cong (erefl 𝓖 (f a)) (h-is-hom s t) ]
  f a * (h s * h t) ≈[ esym 𝓖 _ _ (eassoc 𝓖 (f a) (h s) (h t)) ]
  (f a * h s) * h t ≈∎
 h-is-hom ((₁ , a) • s) t =
  invᴳ (f a) * h (s ◦ t)   ≈[ *-cong (erefl 𝓖 (invᴳ (f a))) (h-is-hom s t) ]
  invᴳ (f a) * (h s * h t) ≈[ esym 𝓖 _ _ (eassoc 𝓖 (invᴳ (f a)) (h s) (h t)) ]
  (invᴳ (f a) * h s) * h t ≈∎

\end{code}

A redex is sent to the unit, and hence h identifies the two sides of a
reduction, of a reduction sequence, and finally of a convertibility.
The last step uses the Church-Rosser property modulo _≈_, whose two
reducts are related by _≈[FA]_ rather than by the identity type, which
is why we needed h to respect _≈[FA]_.

\begin{code}

 h-redex : (x y : X) → y ≈[X] (x ⁻) → h (x • y • []) ≈⟨ 𝓖 ⟩ eᴳ
 h-redex (₀ , a) (₁ , b) (refl , q) =
  f a * (invᴳ (f b) * eᴳ) ≈[ I ]
  f a * invᴳ (f b)        ≈[ II ]
  f a * invᴳ (f a)        ≈[ einv-right 𝓖 (f a) ]
  eᴳ                      ≈∎
   where
    I  = *-cong (erefl 𝓖 (f a)) (eunit-right 𝓖 (invᴳ (f b)))
    II = *-cong (erefl 𝓖 (f a)) (≈-inv-cong (f b) (f a) (f-resp q))
 h-redex (₁ , a) (₀ , b) (refl , q) =
  invᴳ (f a) * (f b * eᴳ) ≈[ I ]
  invᴳ (f a) * f b        ≈[ II ]
  invᴳ (f a) * f a        ≈[ einv-left 𝓖 (f a) ]
  eᴳ                      ≈∎
   where
    I  = *-cong (erefl 𝓖 (invᴳ (f a))) (eunit-right 𝓖 (f b))
    II = *-cong (erefl 𝓖 (invᴳ (f a))) (f-resp q)

 h-identifies-▷-related-points : {s t : FA} → s ▷ t → h s ≈⟨ 𝓖 ⟩ h t
 h-identifies-▷-related-points (u , v , x , y , refl , refl , c) =
  h (u ◦ x • y • v)            ≈[ h-is-hom u (x • y • v) ]
  h u * h (x • y • v)          ≈[ I ]
  h u * (h (x • y • []) * h v) ≈[ II ]
  h u * (eᴳ * h v)             ≈[ III ]
  h u * h v                    ≈[ esym 𝓖 _ _ (h-is-hom u v) ]
  h (u ◦ v)                    ≈∎
   where
    I   = *-cong (erefl 𝓖 (h u)) (h-is-hom (x • y • []) v)
    II  = *-cong (erefl 𝓖 (h u)) (*-cong (h-redex x y c) (erefl 𝓖 (h v)))
    III = *-cong (erefl 𝓖 (h u)) (eunit-left 𝓖 (h v))

 h-identifies-▷⋆-related-points : (s t : FA) → s ▷⋆ t → h s ≈⟨ 𝓖 ⟩ h t
 h-identifies-▷⋆-related-points s t (n , i) = γ n s t i
  where
   γ : (n : ℕ) (s t : FA) → iteration _▷_ n s t → h s ≈⟨ 𝓖 ⟩ h t
   γ 0        s s refl        = erefl 𝓖 (h s)
   γ (succ n) s t (z , d , i) =
    etrans 𝓖 (h s) (h z) (h t) (h-identifies-▷-related-points d) (γ n z t i)

 h-identifies-∿-related-points : (s t : FA) → s ∿ t → h s ≈⟨ 𝓖 ⟩ h t
 h-identifies-∿-related-points s t c = γ (Church-Rosser≈ s t c)
  where
   γ : (Σ z₀ ꞉ FA , Σ z₁ ꞉ FA , (s ▷⋆ z₀) × (t ▷⋆ z₁) × (z₀ ≈[FA] z₁))
     → h s ≈⟨ 𝓖 ⟩ h t
   γ (z₀ , z₁ , σ , τ , ez) =
    h s  ≈[ h-identifies-▷⋆-related-points s z₀ σ ]
    h z₀ ≈[ h-respects-≈[FA] z₀ z₁ ez ]
    h z₁ ≈[ esym 𝓖 _ _ (h-identifies-▷⋆-related-points t z₁ τ) ]
    h t  ≈∎

\end{code}

Hence h is a homomorphism from the free egroup which extends f along
the insertion of generators.

\begin{code}

 free-map : ⟨ free-egroup ⟩ → ⟨ 𝓖 ⟩
 free-map = h

 free-map-is-hom : is-hom free-egroup 𝓖 free-map
 free-map-is-hom = (λ {s} {t} → h-identifies-∿-related-points s t)
                 , (λ {s} {t} → h-is-hom s t)

 free-map-triangle : (a : A) → free-map (ηᴳ a) ≈⟨ 𝓖 ⟩ f a
 free-map-triangle a = eunit-right 𝓖 (f a)

\end{code}

Any homomorphism extending f agrees with the extension up to the
equivalence relation of 𝓖. As in Groups.Free, the argument derives
preservation of the unit and of inverses from the other assumptions.

\begin{code}

 free-map-is-unique : (g : ⟨ free-egroup ⟩ → ⟨ 𝓖 ⟩)
                    → is-hom free-egroup 𝓖 g
                    → ((a : A) → g (ηᴳ a) ≈⟨ 𝓖 ⟩ f a)
                    → (s : ⟨ free-egroup ⟩) → g s ≈⟨ 𝓖 ⟩ free-map s
 free-map-is-unique g g-hom@(_ , g-mult) g-tri = u
  where
   u : (s : FA) → g s ≈⟨ 𝓖 ⟩ h s
   u []            = homs-preserve-unit free-egroup 𝓖 g g-hom
   u ((₀ , a) • s) =
    g (ηᴳ a ◦ s)   ≈[ g-mult {ηᴳ a} {s} ]
    g (ηᴳ a) * g s ≈[ *-cong (g-tri a) (u s) ]
    f a * h s      ≈∎
   u ((₁ , a) • s) =
    g (inv (ηᴳ a) ◦ s)   ≈[ g-mult {inv (ηᴳ a)} {s} ]
    g (inv (ηᴳ a)) * g s ≈[ *-cong I (u s) ]
    invᴳ (f a) * h s     ≈∎
     where
      I : g (inv (ηᴳ a)) ≈⟨ 𝓖 ⟩ invᴳ (f a)
      I = g (inv (ηᴳ a))  ≈[ homs-preserve-inv free-egroup 𝓖 g g-hom (ηᴳ a) ]
          invᴳ (g (ηᴳ a)) ≈[ ≈-inv-cong (g (ηᴳ a)) (f a) (g-tri a) ]
          invᴳ (f a)      ≈∎

 free-map-is-unique₂ : (g₀ g₁ : ⟨ free-egroup ⟩ → ⟨ 𝓖 ⟩)
                     → is-hom free-egroup 𝓖 g₀
                     → is-hom free-egroup 𝓖 g₁
                     → ((a : A) → g₀ (ηᴳ a) ≈⟨ 𝓖 ⟩ f a)
                     → ((a : A) → g₁ (ηᴳ a) ≈⟨ 𝓖 ⟩ f a)
                     → (s : ⟨ free-egroup ⟩) → g₀ s ≈⟨ 𝓖 ⟩ g₁ s
 free-map-is-unique₂ g₀ g₁ i₀ i₁ t₀ t₁ s =
  etrans 𝓖 (g₀ s) (free-map s) (g₁ s)
   (free-map-is-unique g₀ i₀ t₀ s)
   (esym 𝓖 (g₁ s) (free-map s) (free-map-is-unique g₁ i₁ t₁ s))

\end{code}
