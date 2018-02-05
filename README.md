```
   v a r i o u s   n e w   t h e o r e m s   i n  
   c o n s t r u c t i v e    u n i v a l e n t    m a t h e m a t i c s
   w r i t t e n    i n   A g d a
```

This development was started by Martin Escardo in 2010, to github
Monday 5th February 2018. A few files are authored by collaborators,
with names added at the top. If you contribute, please add your name
and date at the place of contribution.


The is an [hmlt](http://www.cs.bham.ac.uk/~mhe/agda-new/index.html)
rendring of the Agda code.

# Spartan MLTT and univalent foundations


At the moment the univalent foundations module [UF](http://www.cs.bham.ac.uk/~mhe/agda-new/UF.html) is a mess and incomplete, but it works. It imports public the module  [SpartanMLTT](http://www.cs.bham.ac.uk/~mhe/agda-new/SpartanMLTT.html), which has portions that should be moved to UF (everything regarding equality, for example), and repetitions
should be avoided, and better naming conventions are needed.


# Omniscient and searchable types

This investigates the notion of [omniscient type](http://www.cs.bham.ac.uk/~mhe/agda-new/OmniscientTypes.html). A type `X` is omniscient
iff
```agda
   Π \(p : X → 𝟚) → (Σ \(x : X) → p x ≡ ₀) + Π \(x : X) → p x ≡ ₁
```
The omniscience of `ℕ` is a [contructive taboo](https://ncatlab.org/nlab/show/taboo), known as [LPO](https://ncatlab.org/nlab/show/principle+of+omniscience), which is an
undecided proposition in our type theory. Nevertheless, we can show
that the function type [`LPO → ℕ` is omniscient](http://www.cs.bham.ac.uk/~mhe/agda-new/LPO.html).
See also [WLPO](http://www.cs.bham.ac.uk/~mhe/agda-new/WLPO.html).

A more interesting example of an omniscient set is `ℕ∞`, known as the [generic convergent sequence](http://www.cs.bham.ac.uk/~mhe/agda-new/GenericConvergentSequence.html), which under
classical logic is equivalent to `ℕ ∪ { ∞ }`.
But it is more direct to [show](http://www.cs.bham.ac.uk/~mhe/agda-new/ConvergentSequenceSearchable.html) that `ℕ∞` is a [searchable type](http://www.cs.bham.ac.uk/~mhe/agda-new/SearchableTypes.html), and get
omniscience as a corollary.

An interesting consequence of the omniscience of `ℕ∞` is that the
[following property](http://www.cs.bham.ac.uk/~mhe/agda-new/ADecidableQuantificationOverTheNaturals.html), an instance of `WLPO`, holds constructively:
```
  Π \(p : ℕ∞ → 𝟚) → (Π \(n : ℕ) → p(under n) ≡ ₁) + ¬(Π \(n : ℕ) → p(under n) ≡ ₁).
```
where
```
  under : ℕ → ℕ∞
```
is the embedding. (The name for the embedding comes from the fact that
in published papers we used an underlined symbol `n` to denote the copy
of `n : ℕ` in `ℕ∞`.)

This is used to show that the [non-continuity of a function ℕ∞ → ℕ is
decidable](http://www.cs.bham.ac.uk/~mhe/agda-new/DecidabilityOfNonContinuity.hmtl).

Another example of searchable set is the type of univalent
propositions (proved in the above module [SearchableTypes](http://www.cs.bham.ac.uk/~mhe/agda-new/SearchableTypes.html)).

Given countably many searchable sets, one can take the disjoint sum
with a limit point at infinity, and this is again a searchable
sets. This construction is called the squashed sum of the countable
family searchable sets. It can be transfinitely iterated to produce
increasingly complex searchable ordinals. The the modules

[SquashedSum](http://www.cs.bham.ac.uk/~mhe/agda-new/SquashedSum.html) defines the sum of a countable family with an added point at infinity.

The module [SearchableOrdinals](http://www.cs.bham.ac.uk/~mhe/agda-new/SearchableOrdinals.html) defines a map from ordinal codes à la Brouwer to types which are searchable.
The module [LexicographicSearch](http://www.cs.bham.ac.uk/~mhe/agda-new/LexicographicSearch.html) show how to find infima of decidable predicates in the lexicographic order.
The module [ConvergentSequenceInfSearchable](http://www.cs.bham.ac.uk/~mhe/agda-new/ConvergentSequenceInfSearchable.html) shows that we can find infima of decidable predicates on `ℕ∞`. 

# Conaturals

The module [CoNaturals](http://www.cs.bham.ac.uk/~mhe/agda-new/CoNaturals.html) characterizes `ℕ∞` as the
final coalgebra of the functor `𝟙 + (-)`, and is followed by an
illustrative example ([CoNaturalsExercise](http://www.cs.bham.ac.uk/~mhe/agda-new/CoNaturalsExercise.html)).

# The topology of the universe

The module [TheTopologyOfTheUniverse](http://www.cs.bham.ac.uk/~mhe/agda-new/TheTopologyOfTheUniverse.html) discusses in what sense `ℕ∞` is the generic
convergent sequence, and proves that the universe `U` of types is
indiscrete, with a certain Rice's Theorem for the universe U as a
corollary in the module [RicesTheoremForTheUniverse](http://www.cs.bham.ac.uk/~mhe/agda-new/RicesTheoremForTheUniverse.html).
The module [BasicDiscontinuityTaboo](http://www.cs.bham.ac.uk/~mhe/agda-new/BasicDiscontinuityTaboo.html)
shows that a basic form of discontinuity is a
taboo, and this is used to formulate and prove Rice's
Theorem.

# Injective types

The module
[InjectiveTypes](http://www.cs.bham.ac.uk/~mhe/agda-new/InjectiveTypes.html)
shows that universes are injective, and more generally that the
injective types are the retracts of exponential powers of universes.
This uses properties of products and sums indexed by univalent
propositions. This uses the module [IdEmbedding]((http://www.cs.bham.ac.uk/~mhe/agda-new/IdEmbedding.html), which shows that the identity type former `Id {X} : X → X → U` is an embedding assuming either Streicher's K axiom (`U` is a set) or the Voevodky's univalence axiom.

And more subtly, it uses that a product of searchable sets indexed by a
univalent proposition is itself searchable: [PropTychonoff](http://www.cs.bham.ac.uk/~mhe/agda-new/PropTychonoff.html).


The following generalizes the squashed sum, with a simple construction
and proof, using the injectivity of the universe and the Prop-Tychonoff theorem:
[ExtendedSumSearchable](http://www.cs.bham.ac.uk/~mhe/agda-new/ExtendedSumSearchable.html).


# 𝟚-compact types, totally separated types, and simple types

The following modules define 𝟚-compactness and study its interaction
with discreteness and total separatedness, with applications to simple
types. We get properties that resemble those of the model of
Kleene-Kreisel continuous functionals of simple types, with some new
results: [TotallySeparated](http://www.cs.bham.ac.uk/~mhe/agda-new/TotallySeparated.html),
[2CompactTypes](http://www.cs.bham.ac.uk/~mhe/agda-new/2CompactTypes.html),
[SimpleTypes](http://www.cs.bham.ac.uk/~mhe/agda-new/SimpleTypes.html),
[FailureOfTotalSeparatedness](http://www.cs.bham.ac.uk/~mhe/agda-new/FailureOfTotalSeparatedness.html).

# More

The following modules contain auxiliary definitions and additional
results and discussion that we choose not to bring here:
* [UF2](http://www.cs.bham.ac.uk/~mhe/agda-new/UF2.html)
* [DecidableAndDetachable](http://www.cs.bham.ac.uk/~mhe/agda-new/DecidableAndDetachable.html) 
* [DiscreteAndSeparated](http://www.cs.bham.ac.uk/~mhe/agda-new/DiscreteAndSeparated.html)
* [ExhaustibleTypes](http://www.cs.bham.ac.uk/~mhe/agda-new/ExhaustibleTypes.html)
* [Naturals](http://www.cs.bham.ac.uk/~mhe/agda-new/Naturals.html)
* [BinaryNaturals](http://www.cs.bham.ac.uk/~mhe/agda-new/BinaryNaturals.html)
* [OrdinalCodes](http://www.cs.bham.ac.uk/~mhe/agda-new/OrdinalCodes.html)
* [Sequence](http://www.cs.bham.ac.uk/~mhe/agda-new/Sequence.html)
* [Two](http://www.cs.bham.ac.uk/~mhe/agda-new/Two.html) 
* [HiggsInvolutionTheorem](http://www.cs.bham.ac.uk/~mhe/agda-new/HiggsInvolutionTheorem.html)
* [DummettDisjunction](http://www.cs.bham.ac.uk/~mhe/agda-new/DummettDisjunction.html)
* [UnivalentChoice](http://www.cs.bham.ac.uk/~mhe/agda-new/UnivalentChoice.html)
* [Dominance](http://www.cs.bham.ac.uk/~mhe/agda-new/Dominance.html)
* [KrausLemma](http://www.cs.bham.ac.uk/~mhe/agda-new/KrausLemma.html)
* [NonCollapsibleFamily](http://www.cs.bham.ac.uk/~mhe/agda-new/NonCollapsibleFamily.html)
* [PropIndexedPiSigma](http://www.cs.bham.ac.uk/~mhe/agda-new/PropIndexedPiSigma.html)

# Rogue modules: countable Tychonoff and omniscience of the Cantor space

The following two rogue modules depart from our main philosophy of
working strictly within a Spartan Martin-Löf type theory with
univalent extensions.  They disable the termination checker, for the
reasons explained in the first module. But to make our point, we also
include runnable experiments in the second module:
[CountableTychonoff](http://www.cs.bham.ac.uk/~mhe/agda-new/CountableTychonoff).html
implements a countable Tychonoff Theorem for searchable sets, and
[CantorSearchable](http://www.cs.bham.ac.uk/~mhe/agda-new/CantorSearchable.html)
uses this to conclude that the Cantor type is searchable.

