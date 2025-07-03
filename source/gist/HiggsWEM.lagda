J.A. Carr 2 July 2025

This code fragment is part of the development in UF/HiggsInvolutionTheorem, pending reorganizations of the document



Aut Ω has weak excluded middle: Every automorphism is either equal to
not (in which case full LEM holds) or it's not equal to it, and hence
not not equal to the identity.

Full excluded middle is not provable. Many examples of Grothendieck topoi have non-trivial automorphisms. By Johnstone, automorphisms are in bijection with closed Boolean sublocales of Ω. For example, in the topos of digraphs, one automorphism negates truth-on-edges while leaving vertices unchanged. Any locale with closed points (or rather, any irreducible closed sets) in a space give automorphisms which negate the presence of that point when possible.

On the other hand, Aut Ω is sometimes a singleton. For another sheaf topos example, consider the total order (ℤ, ≤), every inhabited closed sublocale is equivalent to (ℤ, ≤) or (ℕ, ≤). Neither of these are boolean, so there are no boolean closed sublocales of Ω in these topoi.

\begin{code}

 widespread'-has-weak-excluded-middle : (p : Ω) →
   is-widespread' p →
   (⇁ p) holds + (⇁⇁ p) holds
 widespread'-has-weak-excluded-middle p w = II
  where
   weak-lem-is-prop : is-prop ((⇁ p) holds + (⇁⇁ p) holds)
   weak-lem-is-prop =
     (sum-of-contradictory-props
       (holds-is-prop (⇁ p))
       (holds-is-prop (⇁⇁ p))
       (λ np nnp -> nnp np))

   I : ((⇁ p) holds + ((⇁ p) ⇒ p) holds) →
       (⇁ p) holds + (⇁⇁ p) holds
   I (inl p) = inl p
   I (inr nnp) = inr (λ np → np (nnp np))

   II : (⇁ p) holds + (⇁⇁ p) holds
   II = ∥∥-rec weak-lem-is-prop I (w (⇁ p))

 ℍ-has-WEM
   : (x : ℍ)
   → (pr₁ x ＝ ⊥) + (pr₁ x ≠ ⊥)
 ℍ-has-WEM x@(r@(R , j) , r-is-ws) = +functor IV V III
  where
   I : (⇁ r ∨ (⇁ r ⇒ r)) holds
   I = widespread-gives-widespread' r r-is-ws (r ⇒ ⊥)

   II : (⇁ r) holds + (⇁ r ⇒ r) holds → (⇁ r) holds + (⇁⇁ r) holds
   II (inl nr) = inl nr
   II (inr nnr) = inr (λ nr → nr (nnr nr))

   weak-lem-is-prop : is-prop ((⇁ r) holds + (⇁⇁ r) holds)
   weak-lem-is-prop =
     (sum-of-contradictory-props
       (holds-is-prop (⇁ r))
       (holds-is-prop (⇁⇁ r))
       (λ np nnp -> nnp np))

   III : (⇁ r) holds + (⇁⇁ r) holds
   III = ∥∥-rec weak-lem-is-prop II I

   IV : (⇁ r) holds → (r ＝ ⊥)
   IV nr = Ω-extensionality pe fe (λ R → 𝟘-elim (nr R)) 𝟘-elim

   V : (⇁⇁ r) holds → (r ≠ ⊥)
   V nnr refl = 𝟘-elim (nnr 𝟘-elim)

 Aut-Ω-has-WEM
  : (𝕗 : Aut Ω)
  → (𝕗 ≠ 𝕚𝕕) + ¬ (𝕗 ≠ 𝕚𝕕)
 Aut-Ω-has-WEM 𝕗 = V I
  where
    I : (pr₁ (Aut-Ω-to-ℍ 𝕗) ＝ ⊥) + (pr₁ (Aut-Ω-to-ℍ 𝕗) ≠ ⊥)
    I = ℍ-has-WEM (Aut-Ω-to-ℍ 𝕗)

    II : (pr₁ (Aut-Ω-to-ℍ 𝕗) ＝ ⊥) → 𝕗 ≠ 𝕚𝕕
    II fbot refl = ⊥-is-not-⊤ (fbot ⁻¹)

    III : ⌜ 𝕗 ⌝ ⊤ ＝ ⊤ → 𝕗 ＝ 𝕚𝕕
    III = eval-at-⊤-is-lc {𝕗} {𝕚𝕕}

    IV : (pr₁ (Aut-Ω-to-ℍ 𝕗) ≠ ⊥) → (𝕗 ≠ 𝕚𝕕) → 𝟘
    IV 𝕗-not-bot 𝕗-not-id = 𝕗-not-bot
      (different-from-⊤-gives-equal-⊥ fe pe (⌜ 𝕗 ⌝ ⊤)
        (𝕗-not-id ∘ III))

    V : (pr₁ (Aut-Ω-to-ℍ 𝕗) ＝ ⊥) + (pr₁ (Aut-Ω-to-ℍ 𝕗) ≠ ⊥) →
        (𝕗 ≠ 𝕚𝕕) + ¬ (𝕗 ≠ 𝕚𝕕)
    V (inl not-id) = inl (II not-id)
    V (inr not-not-id) = inr (IV not-not-id)

 DNE-gives-double-negation-equality : DNE 𝓤 → (P : Ω) → ⇁⇁ P ＝ P
 DNE-gives-double-negation-equality dne P =
   Ω-extensionality pe fe (dne (P holds) (holds-is-prop P)) (λ p np → np p)

 EM-gives-not-is-automorphism : EM 𝓤 → is-equiv ⇁_
 EM-gives-not-is-automorphism em = ( (⇁_ , I) , (⇁_ , I))
   where
     I : (P : Ω) → ⇁⇁ P ＝ P
     I =
       DNE-gives-double-negation-equality (EM-gives-DNE em)

 Ω-automorphism-not-id-iff-equals-not
  : (𝕗 : Aut Ω)
  → (𝕗 ≠ 𝕚𝕕) ↔ (⌜ 𝕗 ⌝ ＝ ⇁_)
 Ω-automorphism-not-id-iff-equals-not 𝕗@(f , f-is-equiv) = ( FW , BW )
  where
   I : f ⊤ ＝ ⊤ → 𝕗 ＝ 𝕚𝕕
   I = eval-at-⊤-is-lc {𝕗} {𝕚𝕕}

   II : (𝕗 ≠ 𝕚𝕕) → f ⊤ ≠ ⊤
   II ν = contrapositive I ν

   III : (𝕗 ≠ 𝕚𝕕) → f ⊤ ＝ ⊥
   III ν = different-from-⊤-gives-equal-⊥ fe pe (f ⊤) (II ν)

   ⇁' : (𝕗 ≠ 𝕚𝕕) → Aut Ω
   ⇁' ν = (⇁_ , EM-gives-not-is-automorphism (Ω-automorphism-distinct-from-𝕚𝕕-gives-EM (𝕗 , ν)))

   not-true-is-false : (ν : 𝕗 ≠ 𝕚𝕕) → ⊥ ＝ eval-at-⊤ (⇁' ν)
   not-true-is-false ν = Ω-extensionality pe fe
     𝟘-elim (λ f → 𝟘-elim (f ⋆))

   IV : (ν : 𝕗 ≠ 𝕚𝕕) → 𝕗 ＝ (⇁' ν)
   IV ν = (eval-at-⊤-is-lc (III ν ∙ not-true-is-false ν))

   FW : (𝕗 ≠ 𝕚𝕕) → ⌜ 𝕗 ⌝ ＝ ⇁_
   FW ν = ap pr₁ {𝕗} {⇁' ν} (IV ν)

   not-is-not-id : ⇁_ ≠ id
   not-is-not-id e = ⊥-is-not-⊤
     (not-equal-⊤-gives-equal-⊥ fe pe ⊤ (ap (λ f → f ⊤) e) ⁻¹)

   BW : ⌜ 𝕗 ⌝ ＝ ⇁_ → 𝕗 ≠ 𝕚𝕕
   BW f-is-not e = not-is-not-id (f-is-not ⁻¹ ∙ ap pr₁ e)

\end{code}

