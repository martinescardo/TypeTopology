## Ayberk Tosun, 17 September 2023
## Makefile generated from the dependency graph of `index.lagda`.

all: _build/2.6.3/agda/source/index.agdai

_build/2.6.3/agda/source/Agda/Primitive.agdai:
	agda --safe source/MLTT/Universes.lagda

_build/2.6.3/agda/source/MLTT/Universes.agdai: source/MLTT/Universes.lagda _build/2.6.3/agda/source/Agda/Primitive.agdai
	agda --safe source/MLTT/Universes.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Empty-Type.agdai: source/MLTT/Empty-Type.lagda _build/2.6.3/agda/source/MLTT/Universes.agdai
	agda --safe source/MLTT/Empty-Type.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Empty.agdai: source/MLTT/Empty.lagda _build/2.6.3/agda/source/MLTT/Empty-Type.agdai
	agda --safe source/MLTT/Empty.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Pi.agdai: source/MLTT/Pi.lagda _build/2.6.3/agda/source/MLTT/Universes.agdai
	agda --safe source/MLTT/Pi.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Identity-Type.agdai: source/MLTT/Identity-Type.lagda _build/2.6.3/agda/source/MLTT/Universes.agdai
	agda --safe source/MLTT/Identity-Type.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Id.agdai: source/MLTT/Id.lagda _build/2.6.3/agda/source/MLTT/Pi.agdai  _build/2.6.3/agda/source/MLTT/Identity-Type.agdai
	agda --safe source/MLTT/Id.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Sigma-Type.agdai: source/MLTT/Sigma-Type.lagda _build/2.6.3/agda/source/MLTT/Universes.agdai
	agda --safe source/MLTT/Sigma-Type.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Sigma.agdai: source/MLTT/Sigma.lagda _build/2.6.3/agda/source/MLTT/Sigma-Type.agdai
	agda --safe source/MLTT/Sigma.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Plus-Type.agdai: source/MLTT/Plus-Type.lagda _build/2.6.3/agda/source/MLTT/Universes.agdai
	agda --safe source/MLTT/Plus-Type.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Plus.agdai: source/MLTT/Plus.lagda _build/2.6.3/agda/source/MLTT/Plus-Type.agdai
	agda --safe source/MLTT/Plus.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Negation.agdai: source/MLTT/Negation.lagda _build/2.6.3/agda/source/MLTT/Empty.agdai  _build/2.6.3/agda/source/MLTT/Id.agdai  _build/2.6.3/agda/source/MLTT/Sigma.agdai  _build/2.6.3/agda/source/MLTT/Plus.agdai
	agda --safe source/MLTT/Negation.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Unit.agdai: source/MLTT/Unit.lagda _build/2.6.3/agda/source/MLTT/Universes.agdai
	agda --safe source/MLTT/Unit.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Unit-Properties.agdai: source/MLTT/Unit-Properties.lagda _build/2.6.3/agda/source/MLTT/Negation.agdai  _build/2.6.3/agda/source/MLTT/Unit.agdai
	agda --safe source/MLTT/Unit-Properties.lagda
	touch $@

_build/2.6.3/agda/source/Notation/General.agdai: source/Notation/General.lagda _build/2.6.3/agda/source/MLTT/Negation.agdai
	agda --safe source/Notation/General.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Plus-Properties.agdai: source/MLTT/Plus-Properties.lagda _build/2.6.3/agda/source/MLTT/Unit-Properties.agdai  _build/2.6.3/agda/source/Notation/General.agdai
	agda --safe source/MLTT/Plus-Properties.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Two.agdai: source/MLTT/Two.lagda _build/2.6.3/agda/source/MLTT/Universes.agdai
	agda --safe source/MLTT/Two.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Natural-Numbers-Type.agdai: source/MLTT/Natural-Numbers-Type.lagda _build/2.6.3/agda/source/Agda/Primitive.agdai
	agda --safe source/MLTT/Natural-Numbers-Type.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/NaturalNumbers.agdai: source/MLTT/NaturalNumbers.lagda _build/2.6.3/agda/source/MLTT/Natural-Numbers-Type.agdai  _build/2.6.3/agda/source/MLTT/Universes.agdai
	agda --safe source/MLTT/NaturalNumbers.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Spartan.agdai: source/MLTT/Spartan.lagda _build/2.6.3/agda/source/MLTT/Two.agdai  _build/2.6.3/agda/source/MLTT/NaturalNumbers.agdai  _build/2.6.3/agda/source/MLTT/Unit.agdai  _build/2.6.3/agda/source/Notation/General.agdai
	agda --safe source/MLTT/Spartan.lagda
	touch $@

_build/2.6.3/agda/source/UF/Base.agdai: source/UF/Base.lagda _build/2.6.3/agda/source/MLTT/Spartan.agdai
	agda --safe source/UF/Base.lagda
	touch $@

_build/2.6.3/agda/source/UF/Subsingletons.agdai: source/UF/Subsingletons.lagda _build/2.6.3/agda/source/MLTT/Plus-Properties.agdai  _build/2.6.3/agda/source/UF/Base.agdai
	agda --safe source/UF/Subsingletons.lagda
	touch $@

_build/2.6.3/agda/source/UF/Sets.agdai: source/UF/Sets.lagda _build/2.6.3/agda/source/UF/Subsingletons.agdai
	agda --safe source/UF/Sets.lagda
	touch $@

_build/2.6.3/agda/source/UF/Hedberg.agdai: source/UF/Hedberg.lagda _build/2.6.3/agda/source/UF/Sets.agdai
	agda --safe source/UF/Hedberg.lagda
	touch $@

_build/2.6.3/agda/source/UF/Subsingletons-Properties.agdai: source/UF/Subsingletons-Properties.lagda _build/2.6.3/agda/source/UF/Hedberg.agdai
	agda --safe source/UF/Subsingletons-Properties.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/AlternativePlus.agdai: source/MLTT/AlternativePlus.lagda _build/2.6.3/agda/source/MLTT/Two.agdai  _build/2.6.3/agda/source/MLTT/Sigma.agdai
	agda --safe source/MLTT/AlternativePlus.lagda
	touch $@

_build/2.6.3/agda/source/UF/Retracts.agdai: source/UF/Retracts.lagda _build/2.6.3/agda/source/UF/Subsingletons.agdai  _build/2.6.3/agda/source/MLTT/AlternativePlus.agdai
	agda --safe source/UF/Retracts.lagda
	touch $@

_build/2.6.3/agda/source/UF/Equiv.agdai: source/UF/Equiv.lagda _build/2.6.3/agda/source/UF/Retracts.agdai
	agda --safe source/UF/Equiv.lagda
	touch $@

_build/2.6.3/agda/source/UF/LeftCancellable.agdai: source/UF/LeftCancellable.lagda _build/2.6.3/agda/source/UF/Equiv.agdai
	agda --safe source/UF/LeftCancellable.lagda
	touch $@

_build/2.6.3/agda/source/UF/FunExt.agdai: source/UF/FunExt.lagda _build/2.6.3/agda/source/UF/LeftCancellable.agdai
	agda --safe source/UF/FunExt.lagda
	touch $@

_build/2.6.3/agda/source/UF/Subsingletons-FunExt.agdai: source/UF/Subsingletons-FunExt.lagda _build/2.6.3/agda/source/UF/Subsingletons-Properties.agdai  _build/2.6.3/agda/source/UF/FunExt.agdai
	agda --safe source/UF/Subsingletons-FunExt.lagda
	touch $@

_build/2.6.3/agda/source/UF/Sets-Properties.agdai: source/UF/Sets-Properties.lagda _build/2.6.3/agda/source/UF/Subsingletons-FunExt.agdai
	agda --safe source/UF/Sets-Properties.lagda
	touch $@

_build/2.6.3/agda/source/UF/Univalence.agdai: source/UF/Univalence.lagda _build/2.6.3/agda/source/UF/LeftCancellable.agdai
	agda --safe source/UF/Univalence.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Unit-Type.agdai: source/MLTT/Unit-Type.lagda _build/2.6.3/agda/source/MLTT/Universes.agdai
	agda --safe source/MLTT/Unit-Type.lagda
	touch $@

_build/2.6.3/agda/source/MGS/MLTT.agdai: source/MGS/MLTT.lagda _build/2.6.3/agda/source/MLTT/Plus-Type.agdai  _build/2.6.3/agda/source/MLTT/Identity-Type.agdai  _build/2.6.3/agda/source/MLTT/Unit-Type.agdai  _build/2.6.3/agda/source/MLTT/Natural-Numbers-Type.agdai  _build/2.6.3/agda/source/MLTT/Sigma-Type.agdai  _build/2.6.3/agda/source/MLTT/Empty-Type.agdai
	agda --safe source/MGS/MLTT.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Basic-UF.agdai: source/MGS/Basic-UF.lagda _build/2.6.3/agda/source/MGS/MLTT.agdai
	agda --safe source/MGS/Basic-UF.lagda
	touch $@

_build/2.6.3/agda/source/MGS/hlevels.agdai: source/MGS/hlevels.lagda _build/2.6.3/agda/source/MGS/Basic-UF.agdai
	agda --safe source/MGS/hlevels.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Retracts.agdai: source/MGS/Retracts.lagda _build/2.6.3/agda/source/MGS/hlevels.agdai
	agda --safe source/MGS/Retracts.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Equivalences.agdai: source/MGS/Equivalences.lagda _build/2.6.3/agda/source/MGS/Retracts.agdai
	agda --safe source/MGS/Equivalences.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Univalence.agdai: source/MGS/Univalence.lagda _build/2.6.3/agda/source/MGS/Equivalences.agdai
	agda --safe source/MGS/Univalence.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Solved-Exercises.agdai: source/MGS/Solved-Exercises.lagda _build/2.6.3/agda/source/MGS/Equivalences.agdai
	agda --safe source/MGS/Solved-Exercises.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Equivalence-Induction.agdai: source/MGS/Equivalence-Induction.lagda _build/2.6.3/agda/source/MGS/Univalence.agdai  _build/2.6.3/agda/source/MGS/Solved-Exercises.agdai
	agda --safe source/MGS/Equivalence-Induction.lagda
	touch $@

_build/2.6.3/agda/source/MGS/FunExt-from-Univalence.agdai: source/MGS/FunExt-from-Univalence.lagda _build/2.6.3/agda/source/MGS/Equivalence-Induction.agdai
	agda --safe source/MGS/FunExt-from-Univalence.lagda
	touch $@

_build/2.6.3/agda/source/MGS/TypeTopology-Interface.agdai: source/MGS/TypeTopology-Interface.lagda _build/2.6.3/agda/source/UF/Equiv.agdai  _build/2.6.3/agda/source/MGS/FunExt-from-Univalence.agdai
	agda --safe source/MGS/TypeTopology-Interface.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Subsingleton-Theorems.agdai: source/MGS/Subsingleton-Theorems.lagda _build/2.6.3/agda/source/MGS/FunExt-from-Univalence.agdai
	agda --safe source/MGS/Subsingleton-Theorems.lagda
	touch $@

_build/2.6.3/agda/source/MGS/HAE.agdai: source/MGS/HAE.lagda _build/2.6.3/agda/source/MGS/Equivalence-Induction.agdai
	agda --safe source/MGS/HAE.lagda
	touch $@

_build/2.6.3/agda/source/MGS/More-FunExt-Consequences.agdai: source/MGS/More-FunExt-Consequences.lagda _build/2.6.3/agda/source/MGS/Subsingleton-Theorems.agdai  _build/2.6.3/agda/source/MGS/HAE.agdai
	agda --safe source/MGS/More-FunExt-Consequences.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Embeddings.agdai: source/MGS/Embeddings.lagda _build/2.6.3/agda/source/MGS/More-FunExt-Consequences.agdai
	agda --safe source/MGS/Embeddings.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Equivalence-Constructions.agdai: source/MGS/Equivalence-Constructions.lagda _build/2.6.3/agda/source/MGS/More-FunExt-Consequences.agdai
	agda --safe source/MGS/Equivalence-Constructions.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Universe-Lifting.agdai: source/MGS/Universe-Lifting.lagda _build/2.6.3/agda/source/MGS/Embeddings.agdai  _build/2.6.3/agda/source/MGS/Equivalence-Constructions.agdai
	agda --safe source/MGS/Universe-Lifting.lagda
	touch $@

_build/2.6.3/agda/source/UF/Lower-FunExt.agdai: source/UF/Lower-FunExt.lagda _build/2.6.3/agda/source/MGS/TypeTopology-Interface.agdai  _build/2.6.3/agda/source/MGS/Universe-Lifting.agdai  _build/2.6.3/agda/source/UF/FunExt.agdai
	agda --safe source/UF/Lower-FunExt.lagda
	touch $@

_build/2.6.3/agda/source/UF/PropIndexedPiSigma.agdai: source/UF/PropIndexedPiSigma.lagda _build/2.6.3/agda/source/UF/Subsingletons-Properties.agdai  _build/2.6.3/agda/source/UF/FunExt.agdai
	agda --safe source/UF/PropIndexedPiSigma.lagda
	touch $@

_build/2.6.3/agda/source/UF/SubtypeClassifier.agdai: source/UF/SubtypeClassifier.lagda _build/2.6.3/agda/source/UF/Subsingletons-FunExt.agdai
	agda --safe source/UF/SubtypeClassifier.lagda
	touch $@

_build/2.6.3/agda/source/Naturals/Properties.agdai: source/Naturals/Properties.lagda _build/2.6.3/agda/source/MLTT/NaturalNumbers.agdai  _build/2.6.3/agda/source/MLTT/Unit-Properties.agdai
	agda --safe source/Naturals/Properties.lagda
	touch $@

_build/2.6.3/agda/source/Notation/Order.agdai: source/Notation/Order.lagda _build/2.6.3/agda/source/MLTT/Spartan.agdai
	agda --safe source/Notation/Order.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Two-Properties.agdai: source/MLTT/Two-Properties.lagda _build/2.6.3/agda/source/Naturals/Properties.agdai  _build/2.6.3/agda/source/UF/FunExt.agdai  _build/2.6.3/agda/source/Notation/Order.agdai
	agda --safe source/MLTT/Two-Properties.lagda
	touch $@

_build/2.6.3/agda/source/UF/PropTrunc.agdai: source/UF/PropTrunc.lagda _build/2.6.3/agda/source/UF/Subsingletons-FunExt.agdai  _build/2.6.3/agda/source/MLTT/Two-Properties.agdai
	agda --safe source/UF/PropTrunc.lagda
	touch $@

_build/2.6.3/agda/source/UF/EquivalenceExamples.agdai: source/UF/EquivalenceExamples.lagda _build/2.6.3/agda/source/UF/Lower-FunExt.agdai  _build/2.6.3/agda/source/UF/PropIndexedPiSigma.agdai  _build/2.6.3/agda/source/UF/SubtypeClassifier.agdai  _build/2.6.3/agda/source/UF/PropTrunc.agdai
	agda --safe source/UF/EquivalenceExamples.lagda
	touch $@

_build/2.6.3/agda/source/UF/Equiv-FunExt.agdai: source/UF/Equiv-FunExt.lagda _build/2.6.3/agda/source/UF/EquivalenceExamples.agdai
	agda --safe source/UF/Equiv-FunExt.lagda
	touch $@

_build/2.6.3/agda/source/UF/Yoneda.agdai: source/UF/Yoneda.lagda _build/2.6.3/agda/source/UF/Univalence.agdai  _build/2.6.3/agda/source/UF/Equiv-FunExt.agdai
	agda --safe source/UF/Yoneda.lagda
	touch $@

_build/2.6.3/agda/source/UF/FunExt-Properties.agdai: source/UF/FunExt-Properties.lagda _build/2.6.3/agda/source/UF/Yoneda.agdai
	agda --safe source/UF/FunExt-Properties.lagda
	touch $@

_build/2.6.3/agda/source/UF/UA-FunExt.agdai: source/UF/UA-FunExt.lagda _build/2.6.3/agda/source/UF/FunExt-Properties.agdai
	agda --safe source/UF/UA-FunExt.lagda
	touch $@

_build/2.6.3/agda/source/UF/Embeddings.agdai: source/UF/Embeddings.lagda _build/2.6.3/agda/source/UF/Sets-Properties.agdai  _build/2.6.3/agda/source/UF/UA-FunExt.agdai
	agda --safe source/UF/Embeddings.lagda
	touch $@

_build/2.6.3/agda/source/UF/SIP.agdai: source/UF/SIP.lagda _build/2.6.3/agda/source/UF/Embeddings.agdai
	agda --safe source/UF/SIP.lagda
	touch $@

_build/2.6.3/agda/source/BinarySystems/InitialBinarySystem.agdai: source/BinarySystems/InitialBinarySystem.lagda _build/2.6.3/agda/source/UF/SIP.agdai
	agda --safe source/BinarySystems/InitialBinarySystem.lagda
	touch $@

_build/2.6.3/agda/source/NotionsOfDecidability/Decidable.agdai: source/NotionsOfDecidability/Decidable.lagda _build/2.6.3/agda/source/MLTT/Two-Properties.agdai
	agda --safe source/NotionsOfDecidability/Decidable.lagda
	touch $@

_build/2.6.3/agda/source/NotionsOfDecidability/Complemented.agdai: source/NotionsOfDecidability/Complemented.lagda _build/2.6.3/agda/source/NotionsOfDecidability/Decidable.agdai
	agda --safe source/NotionsOfDecidability/Complemented.lagda
	touch $@

_build/2.6.3/agda/source/UF/HedbergApplications.agdai: source/UF/HedbergApplications.lagda _build/2.6.3/agda/source/UF/Subsingletons-FunExt.agdai
	agda --safe source/UF/HedbergApplications.lagda
	touch $@

_build/2.6.3/agda/source/UF/DiscreteAndSeparated.agdai: source/UF/DiscreteAndSeparated.lagda _build/2.6.3/agda/source/NotionsOfDecidability/Complemented.agdai  _build/2.6.3/agda/source/UF/HedbergApplications.agdai  _build/2.6.3/agda/source/UF/Embeddings.agdai
	agda --safe source/UF/DiscreteAndSeparated.lagda
	touch $@

_build/2.6.3/agda/source/BinarySystems/InitialBinarySystem2.agdai: source/BinarySystems/InitialBinarySystem2.lagda _build/2.6.3/agda/source/UF/SIP.agdai  _build/2.6.3/agda/source/UF/DiscreteAndSeparated.agdai
	agda --safe source/BinarySystems/InitialBinarySystem2.lagda
	touch $@

_build/2.6.3/agda/source/BinarySystems/index.agdai: source/BinarySystems/index.lagda _build/2.6.3/agda/source/BinarySystems/InitialBinarySystem.agdai  _build/2.6.3/agda/source/BinarySystems/InitialBinarySystem2.agdai
	agda --safe source/BinarySystems/index.lagda
	touch $@

_build/2.6.3/agda/source/Notation/CanonicalMap.agdai: source/Notation/CanonicalMap.lagda _build/2.6.3/agda/source/MLTT/Spartan.agdai
	agda --safe source/Notation/CanonicalMap.lagda
	touch $@

_build/2.6.3/agda/source/Naturals/Addition.agdai: source/Naturals/Addition.lagda _build/2.6.3/agda/source/Naturals/Properties.agdai  _build/2.6.3/agda/source/MLTT/Spartan.agdai
	agda --safe source/Naturals/Addition.lagda
	touch $@

_build/2.6.3/agda/source/Naturals/Multiplication.agdai: source/Naturals/Multiplication.lagda _build/2.6.3/agda/source/Naturals/Addition.agdai  _build/2.6.3/agda/source/UF/Base.agdai
	agda --safe source/Naturals/Multiplication.lagda
	touch $@

_build/2.6.3/agda/source/Naturals/AbsoluteDifference.agdai: source/Naturals/AbsoluteDifference.lagda _build/2.6.3/agda/source/Naturals/Addition.agdai
	agda --safe source/Naturals/AbsoluteDifference.lagda
	touch $@

_build/2.6.3/agda/source/UF/ImageAndSurjection.agdai: source/UF/ImageAndSurjection.lagda _build/2.6.3/agda/source/UF/Embeddings.agdai
	agda --safe source/UF/ImageAndSurjection.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/Density.agdai: source/TypeTopology/Density.lagda _build/2.6.3/agda/source/UF/DiscreteAndSeparated.agdai
	agda --safe source/TypeTopology/Density.lagda
	touch $@

_build/2.6.3/agda/source/UF/PairFun.agdai: source/UF/PairFun.lagda _build/2.6.3/agda/source/UF/ImageAndSurjection.agdai  _build/2.6.3/agda/source/TypeTopology/Density.agdai
	agda --safe source/UF/PairFun.lagda
	touch $@

_build/2.6.3/agda/source/UF/UniverseEmbedding.agdai: source/UF/UniverseEmbedding.lagda _build/2.6.3/agda/source/UF/PairFun.agdai
	agda --safe source/UF/UniverseEmbedding.lagda
	touch $@

_build/2.6.3/agda/source/UF/ExcludedMiddle.agdai: source/UF/ExcludedMiddle.lagda _build/2.6.3/agda/source/UF/UniverseEmbedding.agdai
	agda --safe source/UF/ExcludedMiddle.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/Notions.agdai: source/Ordinals/Notions.lagda _build/2.6.3/agda/source/UF/ExcludedMiddle.agdai
	agda --safe source/Ordinals/Notions.lagda
	touch $@

_build/2.6.3/agda/source/Naturals/Order.agdai: source/Naturals/Order.lagda _build/2.6.3/agda/source/Naturals/Multiplication.agdai  _build/2.6.3/agda/source/Naturals/AbsoluteDifference.agdai  _build/2.6.3/agda/source/Ordinals/Notions.agdai
	agda --safe source/Naturals/Order.lagda
	touch $@

_build/2.6.3/agda/source/UF/SubtypeClassifier-Properties.agdai: source/UF/SubtypeClassifier-Properties.lagda _build/2.6.3/agda/source/UF/Embeddings.agdai
	agda --safe source/UF/SubtypeClassifier-Properties.lagda
	touch $@

_build/2.6.3/agda/source/UF/IdEmbedding.agdai: source/UF/IdEmbedding.lagda _build/2.6.3/agda/source/UF/SubtypeClassifier-Properties.agdai
	agda --safe source/UF/IdEmbedding.lagda
	touch $@

_build/2.6.3/agda/source/Lifting/Lifting.agdai: source/Lifting/Lifting.lagda _build/2.6.3/agda/source/UF/Subsingletons.agdai
	agda --safe source/Lifting/Lifting.lagda
	touch $@

_build/2.6.3/agda/source/UF/StructureIdentityPrinciple.agdai: source/UF/StructureIdentityPrinciple.lagda _build/2.6.3/agda/source/UF/Sets-Properties.agdai  _build/2.6.3/agda/source/UF/UA-FunExt.agdai
	agda --safe source/UF/StructureIdentityPrinciple.lagda
	touch $@

_build/2.6.3/agda/source/Lifting/IdentityViaSIP.agdai: source/Lifting/IdentityViaSIP.lagda _build/2.6.3/agda/source/Lifting/Lifting.agdai  _build/2.6.3/agda/source/UF/StructureIdentityPrinciple.agdai
	agda --safe source/Lifting/IdentityViaSIP.lagda
	touch $@

_build/2.6.3/agda/source/Lifting/Monad.agdai: source/Lifting/Monad.lagda _build/2.6.3/agda/source/Lifting/IdentityViaSIP.agdai
	agda --safe source/Lifting/Monad.lagda
	touch $@

_build/2.6.3/agda/source/Lifting/Algebras.agdai: source/Lifting/Algebras.lagda _build/2.6.3/agda/source/Lifting/Monad.agdai
	agda --safe source/Lifting/Algebras.lagda
	touch $@

_build/2.6.3/agda/source/Lifting/EmbeddingViaSIP.agdai: source/Lifting/EmbeddingViaSIP.lagda _build/2.6.3/agda/source/Lifting/IdentityViaSIP.agdai  _build/2.6.3/agda/source/UF/Embeddings.agdai
	agda --safe source/Lifting/EmbeddingViaSIP.lagda
	touch $@

_build/2.6.3/agda/source/UF/KrausLemma.agdai: source/UF/KrausLemma.lagda _build/2.6.3/agda/source/UF/PropTrunc.agdai
	agda --safe source/UF/KrausLemma.lagda
	touch $@

_build/2.6.3/agda/source/UF/Section-Embedding.agdai: source/UF/Section-Embedding.lagda _build/2.6.3/agda/source/UF/KrausLemma.agdai  _build/2.6.3/agda/source/UF/Embeddings.agdai
	agda --safe source/UF/Section-Embedding.lagda
	touch $@

_build/2.6.3/agda/source/UF/Size.agdai: source/UF/Size.lagda _build/2.6.3/agda/source/UF/SubtypeClassifier-Properties.agdai  _build/2.6.3/agda/source/UF/ExcludedMiddle.agdai  _build/2.6.3/agda/source/UF/Section-Embedding.agdai
	agda --safe source/UF/Size.lagda
	touch $@

_build/2.6.3/agda/source/Lifting/Size.agdai: source/Lifting/Size.lagda _build/2.6.3/agda/source/UF/Size.agdai  _build/2.6.3/agda/source/Lifting/IdentityViaSIP.agdai
	agda --safe source/Lifting/Size.lagda
	touch $@

_build/2.6.3/agda/source/InjectiveTypes/Blackboard.agdai: source/InjectiveTypes/Blackboard.lagda _build/2.6.3/agda/source/UF/IdEmbedding.agdai  _build/2.6.3/agda/source/Lifting/Algebras.agdai  _build/2.6.3/agda/source/Lifting/EmbeddingViaSIP.agdai  _build/2.6.3/agda/source/Lifting/Size.agdai
	agda --safe source/InjectiveTypes/Blackboard.lagda
	touch $@

_build/2.6.3/agda/source/UF/NotNotStablePropositions.agdai: source/UF/NotNotStablePropositions.lagda _build/2.6.3/agda/source/UF/Size.agdai
	agda --safe source/UF/NotNotStablePropositions.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/TotallySeparated.agdai: source/TypeTopology/TotallySeparated.lagda _build/2.6.3/agda/source/InjectiveTypes/Blackboard.agdai  _build/2.6.3/agda/source/UF/NotNotStablePropositions.agdai
	agda --safe source/TypeTopology/TotallySeparated.lagda
	touch $@

_build/2.6.3/agda/source/CoNaturals/GenericConvergentSequence.agdai: source/CoNaturals/GenericConvergentSequence.lagda _build/2.6.3/agda/source/Notation/CanonicalMap.agdai  _build/2.6.3/agda/source/Naturals/Order.agdai  _build/2.6.3/agda/source/TypeTopology/TotallySeparated.agdai
	agda --safe source/CoNaturals/GenericConvergentSequence.lagda
	touch $@

_build/2.6.3/agda/source/CoNaturals/UniversalProperty.agdai: source/CoNaturals/UniversalProperty.lagda _build/2.6.3/agda/source/CoNaturals/GenericConvergentSequence.agdai
	agda --safe source/CoNaturals/UniversalProperty.lagda
	touch $@

_build/2.6.3/agda/source/CoNaturals/Arithmetic.agdai: source/CoNaturals/Arithmetic.lagda _build/2.6.3/agda/source/CoNaturals/UniversalProperty.agdai
	agda --safe source/CoNaturals/Arithmetic.lagda
	touch $@

_build/2.6.3/agda/source/Naturals/Sequence.agdai: source/Naturals/Sequence.lagda _build/2.6.3/agda/source/Naturals/Addition.agdai  _build/2.6.3/agda/source/UF/FunExt.agdai
	agda --safe source/Naturals/Sequence.lagda
	touch $@

_build/2.6.3/agda/source/TWA/Closeness.agdai: source/TWA/Closeness.lagda _build/2.6.3/agda/source/CoNaturals/Arithmetic.agdai  _build/2.6.3/agda/source/Naturals/Sequence.agdai
	agda --safe source/TWA/Closeness.lagda
	touch $@

_build/2.6.3/agda/source/Taboos/WLPO.agdai: source/Taboos/WLPO.lagda _build/2.6.3/agda/source/TWA/Closeness.agdai
	agda --safe source/Taboos/WLPO.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/CompactTypes.agdai: source/TypeTopology/CompactTypes.lagda _build/2.6.3/agda/source/TypeTopology/TotallySeparated.agdai
	agda --safe source/TypeTopology/CompactTypes.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/DisconnectedTypes.agdai: source/TypeTopology/DisconnectedTypes.lagda _build/2.6.3/agda/source/TypeTopology/TotallySeparated.agdai
	agda --safe source/TypeTopology/DisconnectedTypes.lagda
	touch $@

_build/2.6.3/agda/source/UF/Retracts-FunExt.agdai: source/UF/Retracts-FunExt.lagda _build/2.6.3/agda/source/UF/FunExt.agdai
	agda --safe source/UF/Retracts-FunExt.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/WeaklyCompactTypes.agdai: source/TypeTopology/WeaklyCompactTypes.lagda _build/2.6.3/agda/source/Taboos/WLPO.agdai  _build/2.6.3/agda/source/TypeTopology/CompactTypes.agdai  _build/2.6.3/agda/source/TypeTopology/DisconnectedTypes.agdai  _build/2.6.3/agda/source/UF/Retracts-FunExt.agdai
	agda --safe source/TypeTopology/WeaklyCompactTypes.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/GenericConvergentSequenceCompactness.agdai: source/TypeTopology/GenericConvergentSequenceCompactness.lagda _build/2.6.3/agda/source/TypeTopology/WeaklyCompactTypes.agdai
	agda --safe source/TypeTopology/GenericConvergentSequenceCompactness.lagda
	touch $@

_build/2.6.3/agda/source/UF/Connected.agdai: source/UF/Connected.lagda _build/2.6.3/agda/source/UF/PropTrunc.agdai
	agda --safe source/UF/Connected.lagda
	touch $@

_build/2.6.3/agda/source/CantorSchroederBernstein/CSB.agdai: source/CantorSchroederBernstein/CSB.lagda _build/2.6.3/agda/source/TypeTopology/GenericConvergentSequenceCompactness.agdai  _build/2.6.3/agda/source/UF/Connected.agdai
	agda --safe source/CantorSchroederBernstein/CSB.lagda
	touch $@

_build/2.6.3/agda/source/CantorSchroederBernstein/CSB-TheoryLabLunch.agdai: source/CantorSchroederBernstein/CSB-TheoryLabLunch.lagda _build/2.6.3/agda/source/TypeTopology/GenericConvergentSequenceCompactness.agdai
	agda --safe source/CantorSchroederBernstein/CSB-TheoryLabLunch.lagda
	touch $@

_build/2.6.3/agda/source/CantorSchroederBernstein/index.agdai: source/CantorSchroederBernstein/index.lagda _build/2.6.3/agda/source/CantorSchroederBernstein/CSB-TheoryLabLunch.agdai  _build/2.6.3/agda/source/CantorSchroederBernstein/CSB.agdai
	agda --safe source/CantorSchroederBernstein/index.lagda
	touch $@

_build/2.6.3/agda/source/Categories/Category.agdai: source/Categories/Category.lagda _build/2.6.3/agda/source/UF/Equiv-FunExt.agdai  _build/2.6.3/agda/source/UF/Sets-Properties.agdai
	agda --safe source/Categories/Category.lagda
	touch $@

_build/2.6.3/agda/source/Categories/Functor.agdai: source/Categories/Functor.lagda _build/2.6.3/agda/source/Categories/Category.agdai
	agda --safe source/Categories/Functor.lagda
	touch $@

_build/2.6.3/agda/source/Categories/NaturalTransformation.agdai: source/Categories/NaturalTransformation.lagda _build/2.6.3/agda/source/Categories/Functor.agdai
	agda --safe source/Categories/NaturalTransformation.lagda
	touch $@

_build/2.6.3/agda/source/Categories/Adjunction.agdai: source/Categories/Adjunction.lagda _build/2.6.3/agda/source/Categories/NaturalTransformation.agdai
	agda --safe source/Categories/Adjunction.lagda
	touch $@

_build/2.6.3/agda/source/Categories/index.agdai: source/Categories/index.lagda _build/2.6.3/agda/source/Categories/Adjunction.agdai
	agda --safe source/Categories/index.lagda
	touch $@

_build/2.6.3/agda/source/Circle/Integers.agdai: source/Circle/Integers.lagda _build/2.6.3/agda/source/UF/Base.agdai
	agda --safe source/Circle/Integers.lagda
	touch $@

_build/2.6.3/agda/source/Circle/Integers-Properties.agdai: source/Circle/Integers-Properties.lagda _build/2.6.3/agda/source/Circle/Integers.agdai  _build/2.6.3/agda/source/UF/DiscreteAndSeparated.agdai
	agda --safe source/Circle/Integers-Properties.lagda
	touch $@

_build/2.6.3/agda/source/Circle/Induction.agdai: source/Circle/Induction.lagda _build/2.6.3/agda/source/Circle/Integers-Properties.agdai
	agda --safe source/Circle/Induction.lagda
	touch $@

_build/2.6.3/agda/source/Naturals/UniversalProperty.agdai: source/Naturals/UniversalProperty.lagda _build/2.6.3/agda/source/UF/FunExt.agdai
	agda --safe source/Naturals/UniversalProperty.lagda
	touch $@

_build/2.6.3/agda/source/Circle/Integers-SymmetricInduction.agdai: source/Circle/Integers-SymmetricInduction.lagda _build/2.6.3/agda/source/Naturals/UniversalProperty.agdai  _build/2.6.3/agda/source/Circle/Integers-Properties.agdai
	agda --safe source/Circle/Integers-SymmetricInduction.lagda
	touch $@

_build/2.6.3/agda/source/Circle/Construction.agdai: source/Circle/Construction.lagda _build/2.6.3/agda/source/UF/SIP.agdai  _build/2.6.3/agda/source/Circle/Induction.agdai  _build/2.6.3/agda/source/Circle/Integers-SymmetricInduction.agdai
	agda --safe source/Circle/Construction.lagda
	touch $@

_build/2.6.3/agda/source/Circle/index.agdai: source/Circle/index.lagda _build/2.6.3/agda/source/Circle/Construction.agdai
	agda --safe source/Circle/index.lagda
	touch $@

_build/2.6.3/agda/source/CoNaturals/Exercise.agdai: source/CoNaturals/Exercise.lagda _build/2.6.3/agda/source/CoNaturals/UniversalProperty.agdai  _build/2.6.3/agda/source/Naturals/Sequence.agdai
	agda --safe source/CoNaturals/Exercise.lagda
	touch $@

_build/2.6.3/agda/source/CoNaturals/index.agdai: source/CoNaturals/index.lagda _build/2.6.3/agda/source/CoNaturals/Exercise.agdai  _build/2.6.3/agda/source/CoNaturals/Arithmetic.agdai
	agda --safe source/CoNaturals/index.lagda
	touch $@

_build/2.6.3/agda/source/ContinuityAxiom/Preliminaries.agdai: source/ContinuityAxiom/Preliminaries.lagda _build/2.6.3/agda/source/NotionsOfDecidability/Decidable.agdai
	agda --safe source/ContinuityAxiom/Preliminaries.lagda
	touch $@

_build/2.6.3/agda/source/ContinuityAxiom/ExitingTruncations.agdai: source/ContinuityAxiom/ExitingTruncations.lagda _build/2.6.3/agda/source/Naturals/Order.agdai  _build/2.6.3/agda/source/ContinuityAxiom/Preliminaries.agdai
	agda --safe source/ContinuityAxiom/ExitingTruncations.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Bool.agdai: source/MLTT/Bool.lagda _build/2.6.3/agda/source/MLTT/Spartan.agdai
	agda --safe source/MLTT/Bool.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/List.agdai: source/MLTT/List.lagda _build/2.6.3/agda/source/Naturals/Properties.agdai  _build/2.6.3/agda/source/MLTT/Bool.agdai
	agda --safe source/MLTT/List.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Fin.agdai: source/MLTT/Fin.lagda _build/2.6.3/agda/source/MLTT/List.agdai
	agda --safe source/MLTT/Fin.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Vector.agdai: source/MLTT/Vector.lagda _build/2.6.3/agda/source/MLTT/Fin.agdai
	agda --safe source/MLTT/Vector.lagda
	touch $@

_build/2.6.3/agda/source/ContinuityAxiom/False.agdai: source/ContinuityAxiom/False.lagda _build/2.6.3/agda/source/MLTT/Vector.agdai
	agda --safe source/ContinuityAxiom/False.lagda
	touch $@

_build/2.6.3/agda/source/ContinuityAxiom/FalseWithoutIdentityTypes.agdai: source/ContinuityAxiom/FalseWithoutIdentityTypes.lagda _build/2.6.3/agda/source/MLTT/Empty.agdai  _build/2.6.3/agda/source/MLTT/NaturalNumbers.agdai  _build/2.6.3/agda/source/MLTT/Sigma.agdai  _build/2.6.3/agda/source/MLTT/Unit.agdai
	agda --safe source/ContinuityAxiom/FalseWithoutIdentityTypes.lagda
	touch $@

_build/2.6.3/agda/source/ContinuityAxiom/UniformContinuity.agdai: source/ContinuityAxiom/UniformContinuity.lagda _build/2.6.3/agda/source/ContinuityAxiom/ExitingTruncations.agdai
	agda --safe source/ContinuityAxiom/UniformContinuity.lagda
	touch $@

_build/2.6.3/agda/source/ContinuityAxiom/index.agdai: source/ContinuityAxiom/index.lagda _build/2.6.3/agda/source/ContinuityAxiom/FalseWithoutIdentityTypes.agdai  _build/2.6.3/agda/source/ContinuityAxiom/UniformContinuity.agdai  _build/2.6.3/agda/source/ContinuityAxiom/False.agdai
	agda --safe source/ContinuityAxiom/index.lagda
	touch $@

_build/2.6.3/agda/source/UF/IdentitySystems.agdai: source/UF/IdentitySystems.lagda _build/2.6.3/agda/source/UF/PairFun.agdai
	agda --safe source/UF/IdentitySystems.lagda
	touch $@

_build/2.6.3/agda/source/Coslice/Type.agdai: source/Coslice/Type.lagda _build/2.6.3/agda/source/MLTT/Spartan.agdai
	agda --safe source/Coslice/Type.lagda
	touch $@

_build/2.6.3/agda/source/Coslice/Hom.agdai: source/Coslice/Hom.lagda _build/2.6.3/agda/source/UF/IdentitySystems.agdai  _build/2.6.3/agda/source/Coslice/Type.agdai
	agda --safe source/Coslice/Hom.lagda
	touch $@

_build/2.6.3/agda/source/Coslice/index.agdai: source/Coslice/index.lagda _build/2.6.3/agda/source/Coslice/Hom.agdai
	agda --safe source/Coslice/index.lagda
	touch $@

_build/2.6.3/agda/source/Groups/Type.agdai: source/Groups/Type.lagda _build/2.6.3/agda/source/UF/UniverseEmbedding.agdai
	agda --safe source/Groups/Type.lagda
	touch $@

_build/2.6.3/agda/source/Groups/Kernel.agdai: source/Groups/Kernel.lagda _build/2.6.3/agda/source/Groups/Type.agdai
	agda --safe source/Groups/Kernel.lagda
	touch $@

_build/2.6.3/agda/source/Groups/Triv.agdai: source/Groups/Triv.lagda _build/2.6.3/agda/source/Groups/Type.agdai
	agda --safe source/Groups/Triv.lagda
	touch $@

_build/2.6.3/agda/source/Groups/Image.agdai: source/Groups/Image.lagda _build/2.6.3/agda/source/Groups/Type.agdai
	agda --safe source/Groups/Image.lagda
	touch $@

_build/2.6.3/agda/source/Groups/Homomorphisms.agdai: source/Groups/Homomorphisms.lagda _build/2.6.3/agda/source/Groups/Kernel.agdai  _build/2.6.3/agda/source/Groups/Triv.agdai  _build/2.6.3/agda/source/Groups/Image.agdai
	agda --safe source/Groups/Homomorphisms.lagda
	touch $@

_build/2.6.3/agda/source/Quotient/Type.agdai: source/Quotient/Type.lagda _build/2.6.3/agda/source/UF/SubtypeClassifier-Properties.agdai  _build/2.6.3/agda/source/UF/ImageAndSurjection.agdai
	agda --safe source/Quotient/Type.lagda
	touch $@

_build/2.6.3/agda/source/Groups/Quotient.agdai: source/Groups/Quotient.lagda _build/2.6.3/agda/source/Quotient/Type.agdai  _build/2.6.3/agda/source/Groups/Type.agdai
	agda --safe source/Groups/Quotient.lagda
	touch $@

_build/2.6.3/agda/source/Quotient/GivesPropTrunc.agdai: source/Quotient/GivesPropTrunc.lagda _build/2.6.3/agda/source/Quotient/Type.agdai
	agda --safe source/Quotient/GivesPropTrunc.lagda
	touch $@

_build/2.6.3/agda/source/Quotient/Large.agdai: source/Quotient/Large.lagda _build/2.6.3/agda/source/Quotient/Type.agdai
	agda --safe source/Quotient/Large.lagda
	touch $@

_build/2.6.3/agda/source/Quotient/Effectivity.agdai: source/Quotient/Effectivity.lagda _build/2.6.3/agda/source/Quotient/GivesPropTrunc.agdai  _build/2.6.3/agda/source/Quotient/Large.agdai
	agda --safe source/Quotient/Effectivity.lagda
	touch $@

_build/2.6.3/agda/source/Groups/Cokernel.agdai: source/Groups/Cokernel.lagda _build/2.6.3/agda/source/Groups/Homomorphisms.agdai  _build/2.6.3/agda/source/Groups/Quotient.agdai  _build/2.6.3/agda/source/Quotient/Effectivity.agdai
	agda --safe source/Groups/Cokernel.lagda
	touch $@

_build/2.6.3/agda/source/CrossedModules/CrossedModules.agdai: source/CrossedModules/CrossedModules.lagda _build/2.6.3/agda/source/Groups/Cokernel.agdai
	agda --safe source/CrossedModules/CrossedModules.lagda
	touch $@

_build/2.6.3/agda/source/CrossedModules/index.agdai: source/CrossedModules/index.lagda _build/2.6.3/agda/source/CrossedModules/CrossedModules.agdai
	agda --safe source/CrossedModules/index.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/PropTychonoff.agdai: source/TypeTopology/PropTychonoff.lagda _build/2.6.3/agda/source/TypeTopology/CompactTypes.agdai
	agda --safe source/TypeTopology/PropTychonoff.lagda
	touch $@

_build/2.6.3/agda/source/Taboos/BasicDiscontinuity.agdai: source/Taboos/BasicDiscontinuity.lagda _build/2.6.3/agda/source/Taboos/WLPO.agdai
	agda --safe source/Taboos/BasicDiscontinuity.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/FailureOfTotalSeparatedness.agdai: source/TypeTopology/FailureOfTotalSeparatedness.lagda _build/2.6.3/agda/source/Taboos/BasicDiscontinuity.agdai
	agda --safe source/TypeTopology/FailureOfTotalSeparatedness.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/SigmaDiscreteAndTotallySeparated.agdai: source/TypeTopology/SigmaDiscreteAndTotallySeparated.lagda _build/2.6.3/agda/source/TypeTopology/PropTychonoff.agdai  _build/2.6.3/agda/source/TypeTopology/FailureOfTotalSeparatedness.agdai  _build/2.6.3/agda/source/TypeTopology/GenericConvergentSequenceCompactness.agdai
	agda --safe source/TypeTopology/SigmaDiscreteAndTotallySeparated.lagda
	touch $@

_build/2.6.3/agda/source/Integers/Type.agdai: source/Integers/Type.lagda _build/2.6.3/agda/source/Notation/CanonicalMap.agdai  _build/2.6.3/agda/source/UF/DiscreteAndSeparated.agdai
	agda --safe source/Integers/Type.lagda
	touch $@

_build/2.6.3/agda/source/Integers/Negation.agdai: source/Integers/Negation.lagda _build/2.6.3/agda/source/Integers/Type.agdai
	agda --safe source/Integers/Negation.lagda
	touch $@

_build/2.6.3/agda/source/Integers/Addition.agdai: source/Integers/Addition.lagda _build/2.6.3/agda/source/Integers/Negation.agdai  _build/2.6.3/agda/source/Naturals/Addition.agdai
	agda --safe source/Integers/Addition.lagda
	touch $@

_build/2.6.3/agda/source/Integers/Multiplication.agdai: source/Integers/Multiplication.lagda _build/2.6.3/agda/source/Naturals/Multiplication.agdai  _build/2.6.3/agda/source/Integers/Addition.agdai
	agda --safe source/Integers/Multiplication.lagda
	touch $@

_build/2.6.3/agda/source/Integers/Abs.agdai: source/Integers/Abs.lagda _build/2.6.3/agda/source/Integers/Multiplication.agdai  _build/2.6.3/agda/source/Naturals/AbsoluteDifference.agdai
	agda --safe source/Integers/Abs.lagda
	touch $@

_build/2.6.3/agda/source/Integers/Order.agdai: source/Integers/Order.lagda _build/2.6.3/agda/source/Naturals/Order.agdai  _build/2.6.3/agda/source/Integers/Abs.agdai
	agda --safe source/Integers/Order.lagda
	touch $@

_build/2.6.3/agda/source/Naturals/Division.agdai: source/Naturals/Division.lagda _build/2.6.3/agda/source/Naturals/Order.agdai
	agda --safe source/Naturals/Division.lagda
	touch $@

_build/2.6.3/agda/source/Integers/Division.agdai: source/Integers/Division.lagda _build/2.6.3/agda/source/Integers/Order.agdai  _build/2.6.3/agda/source/Naturals/Division.agdai
	agda --safe source/Integers/Division.lagda
	touch $@

_build/2.6.3/agda/source/Naturals/HCF.agdai: source/Naturals/HCF.lagda _build/2.6.3/agda/source/Naturals/Division.agdai
	agda --safe source/Naturals/HCF.lagda
	touch $@

_build/2.6.3/agda/source/Integers/HCF.agdai: source/Integers/HCF.lagda _build/2.6.3/agda/source/Integers/Division.agdai  _build/2.6.3/agda/source/Naturals/HCF.agdai
	agda --safe source/Integers/HCF.lagda
	touch $@

_build/2.6.3/agda/source/Rationals/Fractions.agdai: source/Rationals/Fractions.lagda _build/2.6.3/agda/source/TypeTopology/SigmaDiscreteAndTotallySeparated.agdai  _build/2.6.3/agda/source/Integers/HCF.agdai
	agda --safe source/Rationals/Fractions.lagda
	touch $@

_build/2.6.3/agda/source/Rationals/Type.agdai: source/Rationals/Type.lagda _build/2.6.3/agda/source/Rationals/Fractions.agdai
	agda --safe source/Rationals/Type.lagda
	touch $@

_build/2.6.3/agda/source/Rationals/FractionsOperations.agdai: source/Rationals/FractionsOperations.lagda _build/2.6.3/agda/source/Rationals/Fractions.agdai
	agda --safe source/Rationals/FractionsOperations.lagda
	touch $@

_build/2.6.3/agda/source/Rationals/Addition.agdai: source/Rationals/Addition.lagda _build/2.6.3/agda/source/Rationals/Type.agdai  _build/2.6.3/agda/source/Rationals/FractionsOperations.agdai
	agda --safe source/Rationals/Addition.lagda
	touch $@

_build/2.6.3/agda/source/Rationals/Multiplication.agdai: source/Rationals/Multiplication.lagda _build/2.6.3/agda/source/Rationals/Addition.agdai
	agda --safe source/Rationals/Multiplication.lagda
	touch $@

_build/2.6.3/agda/source/Rationals/Negation.agdai: source/Rationals/Negation.lagda _build/2.6.3/agda/source/Rationals/Multiplication.agdai
	agda --safe source/Rationals/Negation.lagda
	touch $@

_build/2.6.3/agda/source/Rationals/FractionsOrder.agdai: source/Rationals/FractionsOrder.lagda _build/2.6.3/agda/source/Rationals/FractionsOperations.agdai
	agda --safe source/Rationals/FractionsOrder.lagda
	touch $@

_build/2.6.3/agda/source/Rationals/Order.agdai: source/Rationals/Order.lagda _build/2.6.3/agda/source/Rationals/Negation.agdai  _build/2.6.3/agda/source/Rationals/FractionsOrder.agdai
	agda --safe source/Rationals/Order.lagda
	touch $@

_build/2.6.3/agda/source/Rationals/Abs.agdai: source/Rationals/Abs.lagda _build/2.6.3/agda/source/Rationals/Order.agdai
	agda --safe source/Rationals/Abs.lagda
	touch $@

_build/2.6.3/agda/source/Rationals/Positive.agdai: source/Rationals/Positive.lagda _build/2.6.3/agda/source/Rationals/Abs.agdai
	agda --safe source/Rationals/Positive.lagda
	touch $@

_build/2.6.3/agda/source/MetricSpaces/Type.agdai: source/MetricSpaces/Type.lagda _build/2.6.3/agda/source/Rationals/Positive.agdai
	agda --safe source/MetricSpaces/Type.lagda
	touch $@

_build/2.6.3/agda/source/Rationals/MinMax.agdai: source/Rationals/MinMax.lagda _build/2.6.3/agda/source/Rationals/Order.agdai
	agda --safe source/Rationals/MinMax.lagda
	touch $@

_build/2.6.3/agda/source/MetricSpaces/Rationals.agdai: source/MetricSpaces/Rationals.lagda _build/2.6.3/agda/source/MetricSpaces/Type.agdai  _build/2.6.3/agda/source/Rationals/MinMax.agdai
	agda --safe source/MetricSpaces/Rationals.lagda
	touch $@

_build/2.6.3/agda/source/Rationals/Limits.agdai: source/Rationals/Limits.lagda _build/2.6.3/agda/source/MetricSpaces/Rationals.agdai
	agda --safe source/Rationals/Limits.lagda
	touch $@

_build/2.6.3/agda/source/UF/Powerset.agdai: source/UF/Powerset.lagda _build/2.6.3/agda/source/UF/SubtypeClassifier-Properties.agdai  _build/2.6.3/agda/source/UF/ExcludedMiddle.agdai
	agda --safe source/UF/Powerset.lagda
	touch $@

_build/2.6.3/agda/source/DedekindReals/Type.agdai: source/DedekindReals/Type.lagda _build/2.6.3/agda/source/Rationals/Order.agdai  _build/2.6.3/agda/source/UF/Powerset.agdai
	agda --safe source/DedekindReals/Type.lagda
	touch $@

_build/2.6.3/agda/source/DedekindReals/Properties.agdai: source/DedekindReals/Properties.lagda _build/2.6.3/agda/source/Rationals/Limits.agdai  _build/2.6.3/agda/source/DedekindReals/Type.agdai
	agda --safe source/DedekindReals/Properties.lagda
	touch $@

_build/2.6.3/agda/source/DedekindReals/Order.agdai: source/DedekindReals/Order.lagda _build/2.6.3/agda/source/DedekindReals/Type.agdai
	agda --safe source/DedekindReals/Order.lagda
	touch $@

_build/2.6.3/agda/source/DedekindReals/Addition.agdai: source/DedekindReals/Addition.lagda _build/2.6.3/agda/source/DedekindReals/Properties.agdai  _build/2.6.3/agda/source/DedekindReals/Order.agdai  _build/2.6.3/agda/source/Groups/Type.agdai
	agda --safe source/DedekindReals/Addition.lagda
	touch $@

_build/2.6.3/agda/source/MetricSpaces/DedekindReals.agdai: source/MetricSpaces/DedekindReals.lagda _build/2.6.3/agda/source/DedekindReals/Properties.agdai  _build/2.6.3/agda/source/DedekindReals/Order.agdai
	agda --safe source/MetricSpaces/DedekindReals.lagda
	touch $@

_build/2.6.3/agda/source/DedekindReals/Extension.agdai: source/DedekindReals/Extension.lagda _build/2.6.3/agda/source/MetricSpaces/DedekindReals.agdai
	agda --safe source/DedekindReals/Extension.lagda
	touch $@

_build/2.6.3/agda/source/DedekindReals/Functions.agdai: source/DedekindReals/Functions.lagda _build/2.6.3/agda/source/DedekindReals/Extension.agdai
	agda --safe source/DedekindReals/Functions.lagda
	touch $@

_build/2.6.3/agda/source/DedekindReals/Multiplication.agdai: source/DedekindReals/Multiplication.lagda _build/2.6.3/agda/source/DedekindReals/Type.agdai  _build/2.6.3/agda/source/Rationals/MinMax.agdai
	agda --safe source/DedekindReals/Multiplication.lagda
	touch $@

_build/2.6.3/agda/source/DedekindReals/index.agdai: source/DedekindReals/index.lagda _build/2.6.3/agda/source/DedekindReals/Addition.agdai  _build/2.6.3/agda/source/DedekindReals/Functions.agdai  _build/2.6.3/agda/source/DedekindReals/Multiplication.agdai
	agda --safe source/DedekindReals/index.lagda
	touch $@

_build/2.6.3/agda/source/Posets/Poset.agdai: source/Posets/Poset.lagda _build/2.6.3/agda/source/UF/Sets-Properties.agdai
	agda --safe source/Posets/Poset.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Basics/Dcpo.agdai: source/DomainTheory/Basics/Dcpo.lagda _build/2.6.3/agda/source/Posets/Poset.agdai  _build/2.6.3/agda/source/UF/PropTrunc.agdai
	agda --safe source/DomainTheory/Basics/Dcpo.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Basics/Miscelanea.agdai: source/DomainTheory/Basics/Miscelanea.lagda _build/2.6.3/agda/source/UF/Size.agdai  _build/2.6.3/agda/source/DomainTheory/Basics/Dcpo.agdai
	agda --safe source/DomainTheory/Basics/Miscelanea.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Basics/Pointed.agdai: source/DomainTheory/Basics/Pointed.lagda _build/2.6.3/agda/source/DomainTheory/Basics/Miscelanea.agdai
	agda --safe source/DomainTheory/Basics/Pointed.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Basics/WayBelow.agdai: source/DomainTheory/Basics/WayBelow.lagda _build/2.6.3/agda/source/DomainTheory/Basics/Pointed.agdai
	agda --safe source/DomainTheory/Basics/WayBelow.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Basics/SupComplete.agdai: source/DomainTheory/Basics/SupComplete.lagda _build/2.6.3/agda/source/DomainTheory/Basics/WayBelow.agdai  _build/2.6.3/agda/source/MLTT/List.agdai
	agda --safe source/DomainTheory/Basics/SupComplete.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Basics/Exponential.agdai: source/DomainTheory/Basics/Exponential.lagda _build/2.6.3/agda/source/DomainTheory/Basics/SupComplete.agdai
	agda --safe source/DomainTheory/Basics/Exponential.lagda
	touch $@

_build/2.6.3/agda/source/Posets/PosetReflection.agdai: source/Posets/PosetReflection.lagda _build/2.6.3/agda/source/Quotient/Large.agdai
	agda --safe source/Posets/PosetReflection.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/IndCompletion.agdai: source/DomainTheory/BasesAndContinuity/IndCompletion.lagda _build/2.6.3/agda/source/Posets/PosetReflection.agdai  _build/2.6.3/agda/source/DomainTheory/Basics/WayBelow.agdai
	agda --safe source/DomainTheory/BasesAndContinuity/IndCompletion.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/Continuity.agdai: source/DomainTheory/BasesAndContinuity/Continuity.lagda _build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/IndCompletion.agdai
	agda --safe source/DomainTheory/BasesAndContinuity/Continuity.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/Bases.agdai: source/DomainTheory/BasesAndContinuity/Bases.lagda _build/2.6.3/agda/source/DomainTheory/Basics/Exponential.agdai  _build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/Continuity.agdai
	agda --safe source/DomainTheory/BasesAndContinuity/Bases.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/ContinuityDiscussion.agdai: source/DomainTheory/BasesAndContinuity/ContinuityDiscussion.lagda _build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/Continuity.agdai
	agda --safe source/DomainTheory/BasesAndContinuity/ContinuityDiscussion.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/IdealCompletion/IdealCompletion.agdai: source/DomainTheory/IdealCompletion/IdealCompletion.lagda _build/2.6.3/agda/source/DomainTheory/Basics/Dcpo.agdai  _build/2.6.3/agda/source/UF/Powerset.agdai
	agda --safe source/DomainTheory/IdealCompletion/IdealCompletion.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/IdealCompletion/Properties.agdai: source/DomainTheory/IdealCompletion/Properties.lagda _build/2.6.3/agda/source/DomainTheory/IdealCompletion/IdealCompletion.agdai  _build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/Bases.agdai
	agda --safe source/DomainTheory/IdealCompletion/Properties.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/IdealCompletion/Retracts.agdai: source/DomainTheory/IdealCompletion/Retracts.lagda _build/2.6.3/agda/source/DomainTheory/IdealCompletion/Properties.agdai
	agda --safe source/DomainTheory/IdealCompletion/Retracts.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/StepFunctions.agdai: source/DomainTheory/BasesAndContinuity/StepFunctions.lagda _build/2.6.3/agda/source/DomainTheory/IdealCompletion/Retracts.agdai
	agda --safe source/DomainTheory/BasesAndContinuity/StepFunctions.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Basics/Products.agdai: source/DomainTheory/Basics/Products.lagda _build/2.6.3/agda/source/DomainTheory/Basics/Pointed.agdai
	agda --safe source/DomainTheory/Basics/Products.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Basics/ProductsContinuity.agdai: source/DomainTheory/Basics/ProductsContinuity.lagda _build/2.6.3/agda/source/DomainTheory/Basics/Products.agdai
	agda --safe source/DomainTheory/Basics/ProductsContinuity.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Basics/FunctionComposition.agdai: source/DomainTheory/Basics/FunctionComposition.lagda _build/2.6.3/agda/source/DomainTheory/Basics/Pointed.agdai
	agda --safe source/DomainTheory/Basics/FunctionComposition.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Basics/Curry.agdai: source/DomainTheory/Basics/Curry.lagda _build/2.6.3/agda/source/DomainTheory/Basics/Exponential.agdai  _build/2.6.3/agda/source/DomainTheory/Basics/ProductsContinuity.agdai  _build/2.6.3/agda/source/DomainTheory/Basics/FunctionComposition.agdai
	agda --safe source/DomainTheory/Basics/Curry.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Basics/LeastFixedPoint.agdai: source/DomainTheory/Basics/LeastFixedPoint.lagda _build/2.6.3/agda/source/DomainTheory/Basics/Exponential.agdai  _build/2.6.3/agda/source/Naturals/Order.agdai
	agda --safe source/DomainTheory/Basics/LeastFixedPoint.lagda
	touch $@

_build/2.6.3/agda/source/Lifting/EmbeddingDirectly.agdai: source/Lifting/EmbeddingDirectly.lagda _build/2.6.3/agda/source/Lifting/Lifting.agdai  _build/2.6.3/agda/source/UF/Embeddings.agdai
	agda --safe source/Lifting/EmbeddingDirectly.lagda
	touch $@

_build/2.6.3/agda/source/Lifting/UnivalentPrecategory.agdai: source/Lifting/UnivalentPrecategory.lagda _build/2.6.3/agda/source/Lifting/IdentityViaSIP.agdai  _build/2.6.3/agda/source/Lifting/EmbeddingDirectly.agdai
	agda --safe source/Lifting/UnivalentPrecategory.lagda
	touch $@

_build/2.6.3/agda/source/Lifting/Miscelanea.agdai: source/Lifting/Miscelanea.lagda _build/2.6.3/agda/source/Lifting/Lifting.agdai
	agda --safe source/Lifting/Miscelanea.lagda
	touch $@

_build/2.6.3/agda/source/Lifting/Miscelanea-PropExt-FunExt.agdai: source/Lifting/Miscelanea-PropExt-FunExt.lagda _build/2.6.3/agda/source/Lifting/Monad.agdai  _build/2.6.3/agda/source/Lifting/UnivalentPrecategory.agdai  _build/2.6.3/agda/source/Lifting/Miscelanea.agdai
	agda --safe source/Lifting/Miscelanea-PropExt-FunExt.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Lifting/LiftingSet.agdai: source/DomainTheory/Lifting/LiftingSet.lagda _build/2.6.3/agda/source/Lifting/Miscelanea-PropExt-FunExt.agdai  _build/2.6.3/agda/source/DomainTheory/Basics/SupComplete.agdai
	agda --safe source/DomainTheory/Lifting/LiftingSet.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Lifting/LiftingSetAlgebraic.agdai: source/DomainTheory/Lifting/LiftingSetAlgebraic.lagda _build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/Bases.agdai  _build/2.6.3/agda/source/DomainTheory/Lifting/LiftingSet.agdai
	agda --safe source/DomainTheory/Lifting/LiftingSetAlgebraic.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Bilimits/Directed.agdai: source/DomainTheory/Bilimits/Directed.lagda _build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/Bases.agdai
	agda --safe source/DomainTheory/Bilimits/Directed.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Bilimits/Sequential.agdai: source/DomainTheory/Bilimits/Sequential.lagda _build/2.6.3/agda/source/DomainTheory/Bilimits/Directed.agdai  _build/2.6.3/agda/source/Naturals/Order.agdai
	agda --safe source/DomainTheory/Bilimits/Sequential.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Bilimits/Dinfinity.agdai: source/DomainTheory/Bilimits/Dinfinity.lagda _build/2.6.3/agda/source/DomainTheory/Lifting/LiftingSetAlgebraic.agdai  _build/2.6.3/agda/source/DomainTheory/Bilimits/Sequential.agdai  _build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/StepFunctions.agdai
	agda --safe source/DomainTheory/Bilimits/Dinfinity.lagda
	touch $@

_build/2.6.3/agda/source/DyadicsInductive/Dyadics.agdai: source/DyadicsInductive/Dyadics.lagda _build/2.6.3/agda/source/UF/DiscreteAndSeparated.agdai
	agda --safe source/DyadicsInductive/Dyadics.lagda
	touch $@

_build/2.6.3/agda/source/DyadicsInductive/DyadicOrder.agdai: source/DyadicsInductive/DyadicOrder.lagda _build/2.6.3/agda/source/DyadicsInductive/Dyadics.agdai
	agda --safe source/DyadicsInductive/DyadicOrder.lagda
	touch $@

_build/2.6.3/agda/source/DyadicsInductive/DyadicOrder-PropTrunc.agdai: source/DyadicsInductive/DyadicOrder-PropTrunc.lagda _build/2.6.3/agda/source/DyadicsInductive/DyadicOrder.agdai
	agda --safe source/DyadicsInductive/DyadicOrder-PropTrunc.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Examples/IdlDyadics.agdai: source/DomainTheory/Examples/IdlDyadics.lagda _build/2.6.3/agda/source/DomainTheory/IdealCompletion/Properties.agdai  _build/2.6.3/agda/source/DyadicsInductive/DyadicOrder-PropTrunc.agdai
	agda --safe source/DomainTheory/Examples/IdlDyadics.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Examples/Omega.agdai: source/DomainTheory/Examples/Omega.lagda _build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/Bases.agdai
	agda --safe source/DomainTheory/Examples/Omega.lagda
	touch $@

_build/2.6.3/agda/source/Factorial/Swap.agdai: source/Factorial/Swap.lagda _build/2.6.3/agda/source/UF/DiscreteAndSeparated.agdai
	agda --safe source/Factorial/Swap.lagda
	touch $@

_build/2.6.3/agda/source/Factorial/Law.agdai: source/Factorial/Law.lagda _build/2.6.3/agda/source/Factorial/Swap.agdai
	agda --safe source/Factorial/Law.lagda
	touch $@

_build/2.6.3/agda/source/Fin/Type.agdai: source/Fin/Type.lagda _build/2.6.3/agda/source/UF/Subsingletons.agdai
	agda --safe source/Fin/Type.lagda
	touch $@

_build/2.6.3/agda/source/Factorial/PlusOneLC.agdai: source/Factorial/PlusOneLC.lagda _build/2.6.3/agda/source/Factorial/Swap.agdai
	agda --safe source/Factorial/PlusOneLC.lagda
	touch $@

_build/2.6.3/agda/source/Fin/Properties.agdai: source/Fin/Properties.lagda _build/2.6.3/agda/source/Fin/Type.agdai  _build/2.6.3/agda/source/Factorial/PlusOneLC.agdai
	agda --safe source/Fin/Properties.lagda
	touch $@

_build/2.6.3/agda/source/Fin/Bishop.agdai: source/Fin/Bishop.lagda _build/2.6.3/agda/source/UF/UniverseEmbedding.agdai  _build/2.6.3/agda/source/Fin/Properties.agdai
	agda --safe source/Fin/Bishop.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/SpartanList.agdai: source/MLTT/SpartanList.lagda _build/2.6.3/agda/source/Fin/Type.agdai  _build/2.6.3/agda/source/UF/FunExt.agdai
	agda --safe source/MLTT/SpartanList.lagda
	touch $@

_build/2.6.3/agda/source/Fin/Topology.agdai: source/Fin/Topology.lagda _build/2.6.3/agda/source/Fin/Bishop.agdai  _build/2.6.3/agda/source/TypeTopology/CompactTypes.agdai  _build/2.6.3/agda/source/MLTT/SpartanList.agdai
	agda --safe source/Fin/Topology.lagda
	touch $@

_build/2.6.3/agda/source/Fin/ArithmeticViaEquivalence.agdai: source/Fin/ArithmeticViaEquivalence.lagda _build/2.6.3/agda/source/Factorial/Law.agdai  _build/2.6.3/agda/source/Fin/Topology.agdai
	agda --safe source/Fin/ArithmeticViaEquivalence.lagda
	touch $@

_build/2.6.3/agda/source/Fin/Kuratowski.agdai: source/Fin/Kuratowski.lagda _build/2.6.3/agda/source/Fin/Topology.agdai
	agda --safe source/Fin/Kuratowski.lagda
	touch $@

_build/2.6.3/agda/source/UF/Classifiers.agdai: source/UF/Classifiers.lagda _build/2.6.3/agda/source/UF/SubtypeClassifier-Properties.agdai  _build/2.6.3/agda/source/UF/ImageAndSurjection.agdai
	agda --safe source/UF/Classifiers.lagda
	touch $@

_build/2.6.3/agda/source/Posets/JoinSemiLattices.agdai: source/Posets/JoinSemiLattices.lagda _build/2.6.3/agda/source/Fin/Type.agdai  _build/2.6.3/agda/source/UF/Sets.agdai
	agda --safe source/Posets/JoinSemiLattices.lagda
	touch $@

_build/2.6.3/agda/source/UF/Powerset-Fin.agdai: source/UF/Powerset-Fin.lagda _build/2.6.3/agda/source/Fin/ArithmeticViaEquivalence.agdai  _build/2.6.3/agda/source/Fin/Kuratowski.agdai  _build/2.6.3/agda/source/UF/Classifiers.agdai  _build/2.6.3/agda/source/Posets/JoinSemiLattices.agdai  _build/2.6.3/agda/source/UF/Powerset.agdai  _build/2.6.3/agda/source/MLTT/List.agdai
	agda --safe source/UF/Powerset-Fin.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Examples/Powerset.agdai: source/DomainTheory/Examples/Powerset.lagda _build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/Bases.agdai  _build/2.6.3/agda/source/UF/Powerset-Fin.agdai
	agda --safe source/DomainTheory/Examples/Powerset.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Lifting/LiftingDcpo.agdai: source/DomainTheory/Lifting/LiftingDcpo.lagda _build/2.6.3/agda/source/DomainTheory/Lifting/LiftingSet.agdai
	agda --safe source/DomainTheory/Lifting/LiftingDcpo.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Combinatory/PCF.agdai: source/PCF/Combinatory/PCF.lagda _build/2.6.3/agda/source/UF/PropTrunc.agdai
	agda --safe source/PCF/Combinatory/PCF.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/ScottModelOfPCF/PCF.agdai: source/DomainTheory/ScottModelOfPCF/PCF.lagda _build/2.6.3/agda/source/PCF/Combinatory/PCF.agdai
	agda --safe source/DomainTheory/ScottModelOfPCF/PCF.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Combinatory/PCFCombinators.agdai: source/PCF/Combinatory/PCFCombinators.lagda _build/2.6.3/agda/source/DomainTheory/Basics/Exponential.agdai  _build/2.6.3/agda/source/DomainTheory/Lifting/LiftingSet.agdai
	agda --safe source/PCF/Combinatory/PCFCombinators.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/ScottModelOfPCF/PCFCombinators.agdai: source/DomainTheory/ScottModelOfPCF/PCFCombinators.lagda _build/2.6.3/agda/source/PCF/Combinatory/PCFCombinators.agdai
	agda --safe source/DomainTheory/ScottModelOfPCF/PCFCombinators.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Combinatory/ScottModelOfPCF.agdai: source/PCF/Combinatory/ScottModelOfPCF.lagda _build/2.6.3/agda/source/PCF/Combinatory/PCF.agdai  _build/2.6.3/agda/source/PCF/Combinatory/PCFCombinators.agdai  _build/2.6.3/agda/source/DomainTheory/Basics/LeastFixedPoint.agdai
	agda --safe source/PCF/Combinatory/ScottModelOfPCF.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/ScottModelOfPCF/ScottModelOfPCF.agdai: source/DomainTheory/ScottModelOfPCF/ScottModelOfPCF.lagda _build/2.6.3/agda/source/PCF/Combinatory/ScottModelOfPCF.agdai
	agda --safe source/DomainTheory/ScottModelOfPCF/ScottModelOfPCF.lagda
	touch $@

_build/2.6.3/agda/source/Slice/Family.agdai: source/Slice/Family.lagda _build/2.6.3/agda/source/MLTT/Spartan.agdai
	agda --safe source/Slice/Family.lagda
	touch $@

_build/2.6.3/agda/source/UF/Logic.agdai: source/UF/Logic.lagda _build/2.6.3/agda/source/UF/SubtypeClassifier.agdai  _build/2.6.3/agda/source/UF/PropTrunc.agdai
	agda --safe source/UF/Logic.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/Topology/ScottTopology.agdai: source/DomainTheory/Topology/ScottTopology.lagda _build/2.6.3/agda/source/Slice/Family.agdai  _build/2.6.3/agda/source/UF/Logic.agdai  _build/2.6.3/agda/source/DomainTheory/Basics/Dcpo.agdai  _build/2.6.3/agda/source/UF/Powerset.agdai
	agda --safe source/DomainTheory/Topology/ScottTopology.lagda
	touch $@

_build/2.6.3/agda/source/DomainTheory/index.agdai: source/DomainTheory/index.lagda _build/2.6.3/agda/source/DomainTheory/ScottModelOfPCF/ScottModelOfPCF.agdai  _build/2.6.3/agda/source/DomainTheory/Topology/ScottTopology.agdai  _build/2.6.3/agda/source/DomainTheory/Bilimits/Dinfinity.agdai  _build/2.6.3/agda/source/DomainTheory/Examples/Omega.agdai  _build/2.6.3/agda/source/DomainTheory/ScottModelOfPCF/PCFCombinators.agdai  _build/2.6.3/agda/source/DomainTheory/Examples/IdlDyadics.agdai  _build/2.6.3/agda/source/DomainTheory/Examples/Powerset.agdai  _build/2.6.3/agda/source/DomainTheory/BasesAndContinuity/ContinuityDiscussion.agdai  _build/2.6.3/agda/source/DomainTheory/Lifting/LiftingDcpo.agdai  _build/2.6.3/agda/source/DomainTheory/ScottModelOfPCF/PCF.agdai
	agda --safe source/DomainTheory/index.lagda
	touch $@

_build/2.6.3/agda/source/Dominance/Definition.agdai: source/Dominance/Definition.lagda _build/2.6.3/agda/source/UF/Subsingletons-FunExt.agdai
	agda --safe source/Dominance/Definition.lagda
	touch $@

_build/2.6.3/agda/source/Dominance/Decidable.agdai: source/Dominance/Decidable.lagda _build/2.6.3/agda/source/NotionsOfDecidability/Complemented.agdai  _build/2.6.3/agda/source/Dominance/Definition.agdai
	agda --safe source/Dominance/Decidable.lagda
	touch $@

_build/2.6.3/agda/source/W/Type.agdai: source/W/Type.lagda _build/2.6.3/agda/source/MLTT/Spartan.agdai
	agda --safe source/W/Type.lagda
	touch $@

_build/2.6.3/agda/source/Dominance/Lifting.agdai: source/Dominance/Lifting.lagda _build/2.6.3/agda/source/W/Type.agdai  _build/2.6.3/agda/source/UF/SIP.agdai  _build/2.6.3/agda/source/Dominance/Definition.agdai  _build/2.6.3/agda/source/UF/PairFun.agdai
	agda --safe source/Dominance/Lifting.lagda
	touch $@

_build/2.6.3/agda/source/Dominance/index.agdai: source/Dominance/index.lagda _build/2.6.3/agda/source/Dominance/Lifting.agdai  _build/2.6.3/agda/source/Dominance/Decidable.agdai
	agda --safe source/Dominance/index.lagda
	touch $@

_build/2.6.3/agda/source/Duploids/DeductiveSystem.agdai: source/Duploids/DeductiveSystem.lagda _build/2.6.3/agda/source/UF/Logic.agdai  _build/2.6.3/agda/source/Categories/Category.agdai
	agda --safe source/Duploids/DeductiveSystem.lagda
	touch $@

_build/2.6.3/agda/source/UF/HLevels.agdai: source/UF/HLevels.lagda _build/2.6.3/agda/source/UF/UA-FunExt.agdai
	agda --safe source/UF/HLevels.lagda
	touch $@

_build/2.6.3/agda/source/Duploids/Depolarization.agdai: source/Duploids/Depolarization.lagda _build/2.6.3/agda/source/Duploids/DeductiveSystem.agdai  _build/2.6.3/agda/source/UF/HLevels.agdai
	agda --safe source/Duploids/Depolarization.lagda
	touch $@

_build/2.6.3/agda/source/Duploids/Preduploid.agdai: source/Duploids/Preduploid.lagda _build/2.6.3/agda/source/Duploids/DeductiveSystem.agdai
	agda --safe source/Duploids/Preduploid.lagda
	touch $@

_build/2.6.3/agda/source/Duploids/Duploid.agdai: source/Duploids/Duploid.lagda _build/2.6.3/agda/source/Duploids/Preduploid.agdai  _build/2.6.3/agda/source/Categories/Functor.agdai
	agda --safe source/Duploids/Duploid.lagda
	touch $@

_build/2.6.3/agda/source/Duploids/index.agdai: source/Duploids/index.lagda _build/2.6.3/agda/source/Duploids/Depolarization.agdai  _build/2.6.3/agda/source/Duploids/Duploid.agdai
	agda --safe source/Duploids/index.lagda
	touch $@

_build/2.6.3/agda/source/Naturals/Exponentiation.agdai: source/Naturals/Exponentiation.lagda _build/2.6.3/agda/source/Naturals/Multiplication.agdai
	agda --safe source/Naturals/Exponentiation.lagda
	touch $@

_build/2.6.3/agda/source/Integers/Exponentiation.agdai: source/Integers/Exponentiation.lagda _build/2.6.3/agda/source/Integers/Multiplication.agdai  _build/2.6.3/agda/source/Naturals/Exponentiation.agdai
	agda --safe source/Integers/Exponentiation.lagda
	touch $@

_build/2.6.3/agda/source/Naturals/Parity.agdai: source/Naturals/Parity.lagda _build/2.6.3/agda/source/Naturals/Division.agdai  _build/2.6.3/agda/source/Naturals/Exponentiation.agdai
	agda --safe source/Naturals/Parity.lagda
	touch $@

_build/2.6.3/agda/source/Integers/Parity.agdai: source/Integers/Parity.lagda _build/2.6.3/agda/source/Naturals/Parity.agdai  _build/2.6.3/agda/source/Integers/Abs.agdai
	agda --safe source/Integers/Parity.lagda
	touch $@

_build/2.6.3/agda/source/Dyadics/Type.agdai: source/Dyadics/Type.lagda _build/2.6.3/agda/source/Rationals/Multiplication.agdai  _build/2.6.3/agda/source/Integers/Exponentiation.agdai  _build/2.6.3/agda/source/Integers/Parity.agdai
	agda --safe source/Dyadics/Type.lagda
	touch $@

_build/2.6.3/agda/source/Dyadics/Negation.agdai: source/Dyadics/Negation.lagda _build/2.6.3/agda/source/Dyadics/Type.agdai
	agda --safe source/Dyadics/Negation.lagda
	touch $@

_build/2.6.3/agda/source/Dyadics/Addition.agdai: source/Dyadics/Addition.lagda _build/2.6.3/agda/source/Dyadics/Negation.agdai
	agda --safe source/Dyadics/Addition.lagda
	touch $@

_build/2.6.3/agda/source/Dyadics/Multiplication.agdai: source/Dyadics/Multiplication.lagda _build/2.6.3/agda/source/Dyadics/Type.agdai
	agda --safe source/Dyadics/Multiplication.lagda
	touch $@

_build/2.6.3/agda/source/Dyadics/Order.agdai: source/Dyadics/Order.lagda _build/2.6.3/agda/source/Dyadics/Type.agdai
	agda --safe source/Dyadics/Order.lagda
	touch $@

_build/2.6.3/agda/source/Dyadics/index.agdai: source/Dyadics/index.lagda _build/2.6.3/agda/source/Dyadics/Addition.agdai  _build/2.6.3/agda/source/Dyadics/Multiplication.agdai  _build/2.6.3/agda/source/Dyadics/Order.agdai
	agda --safe source/Dyadics/index.lagda
	touch $@

_build/2.6.3/agda/source/DyadicsInductive/index.agdai: source/DyadicsInductive/index.lagda _build/2.6.3/agda/source/DyadicsInductive/DyadicOrder-PropTrunc.agdai
	agda --safe source/DyadicsInductive/index.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Maybe.agdai: source/MLTT/Maybe.lagda _build/2.6.3/agda/source/UF/DiscreteAndSeparated.agdai
	agda --safe source/MLTT/Maybe.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/Athenian.agdai: source/MLTT/Athenian.lagda _build/2.6.3/agda/source/MLTT/Vector.agdai  _build/2.6.3/agda/source/MLTT/Maybe.agdai
	agda --safe source/MLTT/Athenian.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Continuity.agdai: source/EffectfulForcing/MFPSAndVariations/Continuity.lagda _build/2.6.3/agda/source/Naturals/Order.agdai  _build/2.6.3/agda/source/MLTT/Athenian.agdai
	agda --safe source/EffectfulForcing/MFPSAndVariations/Continuity.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Combinators.agdai: source/EffectfulForcing/MFPSAndVariations/Combinators.lagda _build/2.6.3/agda/source/MLTT/Spartan.agdai
	agda --safe source/EffectfulForcing/MFPSAndVariations/Combinators.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/SystemT.agdai: source/EffectfulForcing/MFPSAndVariations/SystemT.lagda _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Continuity.agdai  _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Combinators.agdai
	agda --safe source/EffectfulForcing/MFPSAndVariations/SystemT.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/Internal/SystemT.agdai: source/EffectfulForcing/Internal/SystemT.lagda _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/SystemT.agdai
	agda --safe source/EffectfulForcing/Internal/SystemT.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Dialogue.agdai: source/EffectfulForcing/MFPSAndVariations/Dialogue.lagda _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Continuity.agdai
	agda --safe source/EffectfulForcing/MFPSAndVariations/Dialogue.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/LambdaCalculusVersionOfMFPS.agdai: source/EffectfulForcing/MFPSAndVariations/LambdaCalculusVersionOfMFPS.lagda _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/SystemT.agdai  _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Dialogue.agdai
	agda --safe source/EffectfulForcing/MFPSAndVariations/LambdaCalculusVersionOfMFPS.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/Internal/External.agdai: source/EffectfulForcing/Internal/External.lagda _build/2.6.3/agda/source/EffectfulForcing/Internal/SystemT.agdai  _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/LambdaCalculusVersionOfMFPS.agdai
	agda --safe source/EffectfulForcing/Internal/External.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Church.agdai: source/EffectfulForcing/MFPSAndVariations/Church.lagda _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/SystemT.agdai  _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Dialogue.agdai
	agda --safe source/EffectfulForcing/MFPSAndVariations/Church.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/Internal/Internal.agdai: source/EffectfulForcing/Internal/Internal.lagda _build/2.6.3/agda/source/EffectfulForcing/Internal/SystemT.agdai  _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Church.agdai
	agda --safe source/EffectfulForcing/Internal/Internal.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/Internal/Subst.agdai: source/EffectfulForcing/Internal/Subst.lagda _build/2.6.3/agda/source/EffectfulForcing/Internal/Internal.agdai
	agda --safe source/EffectfulForcing/Internal/Subst.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/Internal/Correctness.agdai: source/EffectfulForcing/Internal/Correctness.lagda _build/2.6.3/agda/source/EffectfulForcing/Internal/External.agdai  _build/2.6.3/agda/source/EffectfulForcing/Internal/Subst.agdai
	agda --safe source/EffectfulForcing/Internal/Correctness.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/Internal/FurtherThoughts.agdai: source/EffectfulForcing/Internal/FurtherThoughts.lagda _build/2.6.3/agda/source/EffectfulForcing/Internal/Correctness.agdai
	agda --safe source/EffectfulForcing/Internal/FurtherThoughts.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/Internal/InternalModCont.agdai: source/EffectfulForcing/Internal/InternalModCont.lagda _build/2.6.3/agda/source/EffectfulForcing/Internal/Correctness.agdai
	agda --safe source/EffectfulForcing/Internal/InternalModCont.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/Internal/index.agdai: source/EffectfulForcing/Internal/index.lagda _build/2.6.3/agda/source/EffectfulForcing/Internal/FurtherThoughts.agdai  _build/2.6.3/agda/source/EffectfulForcing/Internal/InternalModCont.agdai
	agda --safe source/EffectfulForcing/Internal/index.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/CombinatoryT.agdai: source/EffectfulForcing/MFPSAndVariations/CombinatoryT.lagda _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Continuity.agdai  _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Combinators.agdai
	agda --safe source/EffectfulForcing/MFPSAndVariations/CombinatoryT.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Dialogue-to-Brouwer.agdai: source/EffectfulForcing/MFPSAndVariations/Dialogue-to-Brouwer.lagda _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Dialogue.agdai
	agda --safe source/EffectfulForcing/MFPSAndVariations/Dialogue-to-Brouwer.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Internal.agdai: source/EffectfulForcing/MFPSAndVariations/Internal.lagda _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Church.agdai
	agda --safe source/EffectfulForcing/MFPSAndVariations/Internal.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/MFPS-XXIX.agdai: source/EffectfulForcing/MFPSAndVariations/MFPS-XXIX.lagda _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/CombinatoryT.agdai  _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Dialogue.agdai
	agda --safe source/EffectfulForcing/MFPSAndVariations/MFPS-XXIX.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/WithoutOracle.agdai: source/EffectfulForcing/MFPSAndVariations/WithoutOracle.lagda _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/MFPS-XXIX.agdai
	agda --safe source/EffectfulForcing/MFPSAndVariations/WithoutOracle.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/index.agdai: source/EffectfulForcing/MFPSAndVariations/index.lagda _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Internal.agdai  _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/Dialogue-to-Brouwer.agdai  _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/LambdaCalculusVersionOfMFPS.agdai  _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/WithoutOracle.agdai
	agda --safe source/EffectfulForcing/MFPSAndVariations/index.lagda
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/index.agdai: source/EffectfulForcing/index.lagda _build/2.6.3/agda/source/EffectfulForcing/MFPSAndVariations/index.agdai  _build/2.6.3/agda/source/EffectfulForcing/Internal/index.agdai
	agda --safe source/EffectfulForcing/index.lagda
	touch $@

_build/2.6.3/agda/source/Factorial/index.agdai: source/Factorial/index.lagda _build/2.6.3/agda/source/Factorial/Law.agdai  _build/2.6.3/agda/source/Factorial/PlusOneLC.agdai
	agda --safe source/Factorial/index.lagda
	touch $@

_build/2.6.3/agda/source/Field/Axioms.agdai: source/Field/Axioms.lagda _build/2.6.3/agda/source/UF/Sets.agdai
	agda --safe source/Field/Axioms.lagda
	touch $@

_build/2.6.3/agda/source/Field/DedekindReals.agdai: source/Field/DedekindReals.lagda _build/2.6.3/agda/source/Field/Axioms.agdai  _build/2.6.3/agda/source/DedekindReals/Order.agdai
	agda --safe source/Field/DedekindReals.lagda
	touch $@

_build/2.6.3/agda/source/Field/Rationals.agdai: source/Field/Rationals.lagda _build/2.6.3/agda/source/Field/Axioms.agdai  _build/2.6.3/agda/source/Rationals/Order.agdai
	agda --safe source/Field/Rationals.lagda
	touch $@

_build/2.6.3/agda/source/Field/index.agdai: source/Field/index.lagda _build/2.6.3/agda/source/Field/Rationals.agdai  _build/2.6.3/agda/source/Field/DedekindReals.agdai
	agda --safe source/Field/index.lagda
	touch $@

_build/2.6.3/agda/source/Fin/Variation.agdai: source/Fin/Variation.lagda _build/2.6.3/agda/source/Fin/Type.agdai  _build/2.6.3/agda/source/Naturals/Order.agdai
	agda --safe source/Fin/Variation.lagda
	touch $@

_build/2.6.3/agda/source/Fin/Embeddings.agdai: source/Fin/Embeddings.lagda _build/2.6.3/agda/source/Fin/Properties.agdai  _build/2.6.3/agda/source/Fin/Variation.agdai
	agda --safe source/Fin/Embeddings.lagda
	touch $@

_build/2.6.3/agda/source/Fin/Order.agdai: source/Fin/Order.lagda _build/2.6.3/agda/source/Fin/Topology.agdai  _build/2.6.3/agda/source/Fin/Embeddings.agdai
	agda --safe source/Fin/Order.lagda
	touch $@

_build/2.6.3/agda/source/Fin/ArgMinMax.agdai: source/Fin/ArgMinMax.lagda _build/2.6.3/agda/source/Fin/Order.agdai
	agda --safe source/Fin/ArgMinMax.lagda
	touch $@

_build/2.6.3/agda/source/Fin/Choice.agdai: source/Fin/Choice.lagda _build/2.6.3/agda/source/Fin/Order.agdai
	agda --safe source/Fin/Choice.lagda
	touch $@

_build/2.6.3/agda/source/Various/HiggsInvolutionTheorem.agdai: source/Various/HiggsInvolutionTheorem.lagda _build/2.6.3/agda/source/UF/ExcludedMiddle.agdai
	agda --safe source/Various/HiggsInvolutionTheorem.lagda
	touch $@

_build/2.6.3/agda/source/Fin/Dedekind.agdai: source/Fin/Dedekind.lagda _build/2.6.3/agda/source/CantorSchroederBernstein/CSB.agdai  _build/2.6.3/agda/source/Various/HiggsInvolutionTheorem.agdai
	agda --safe source/Fin/Dedekind.lagda
	touch $@

_build/2.6.3/agda/source/Fin/Omega.agdai: source/Fin/Omega.lagda _build/2.6.3/agda/source/Naturals/Order.agdai  _build/2.6.3/agda/source/Fin/Topology.agdai
	agda --safe source/Fin/Omega.lagda
	touch $@

_build/2.6.3/agda/source/Fin/Pigeonhole.agdai: source/Fin/Pigeonhole.lagda _build/2.6.3/agda/source/Fin/Choice.agdai
	agda --safe source/Fin/Pigeonhole.lagda
	touch $@

_build/2.6.3/agda/source/Fin/UniverseInvariance.agdai: source/Fin/UniverseInvariance.lagda _build/2.6.3/agda/source/Fin/Bishop.agdai
	agda --safe source/Fin/UniverseInvariance.lagda
	touch $@

_build/2.6.3/agda/source/Fin/index.agdai: source/Fin/index.lagda _build/2.6.3/agda/source/Fin/UniverseInvariance.agdai  _build/2.6.3/agda/source/Fin/ArithmeticViaEquivalence.agdai  _build/2.6.3/agda/source/Fin/Kuratowski.agdai  _build/2.6.3/agda/source/Fin/Pigeonhole.agdai  _build/2.6.3/agda/source/Fin/ArgMinMax.agdai  _build/2.6.3/agda/source/Fin/Dedekind.agdai  _build/2.6.3/agda/source/Fin/Omega.agdai
	agda --safe source/Fin/index.lagda
	touch $@

_build/2.6.3/agda/source/Games/Monad.agdai: source/Games/Monad.lagda _build/2.6.3/agda/source/UF/FunExt.agdai
	agda --safe source/Games/Monad.lagda
	touch $@

_build/2.6.3/agda/source/Games/K.agdai: source/Games/K.lagda _build/2.6.3/agda/source/Games/Monad.agdai
	agda --safe source/Games/K.lagda
	touch $@

_build/2.6.3/agda/source/Games/J.agdai: source/Games/J.lagda _build/2.6.3/agda/source/Games/K.agdai
	agda --safe source/Games/J.lagda
	touch $@

_build/2.6.3/agda/source/Games/JK.agdai: source/Games/JK.lagda _build/2.6.3/agda/source/Games/J.agdai
	agda --safe source/Games/JK.lagda
	touch $@

_build/2.6.3/agda/source/Games/TypeTrees.agdai: source/Games/TypeTrees.lagda _build/2.6.3/agda/source/UF/Subsingletons-FunExt.agdai  _build/2.6.3/agda/source/Games/Monad.agdai
	agda --safe source/Games/TypeTrees.lagda
	touch $@

_build/2.6.3/agda/source/Games/FiniteHistoryDependent.agdai: source/Games/FiniteHistoryDependent.lagda _build/2.6.3/agda/source/Games/JK.agdai  _build/2.6.3/agda/source/Games/TypeTrees.agdai
	agda --safe source/Games/FiniteHistoryDependent.lagda
	touch $@

_build/2.6.3/agda/source/Games/Constructor.agdai: source/Games/Constructor.lagda _build/2.6.3/agda/source/Games/FiniteHistoryDependent.agdai
	agda --safe source/Games/Constructor.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/ExtendedSumCompact.agdai: source/TypeTopology/ExtendedSumCompact.lagda _build/2.6.3/agda/source/TypeTopology/PropTychonoff.agdai
	agda --safe source/TypeTopology/ExtendedSumCompact.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/SquashedSum.agdai: source/TypeTopology/SquashedSum.lagda _build/2.6.3/agda/source/TypeTopology/ExtendedSumCompact.agdai  _build/2.6.3/agda/source/TypeTopology/SigmaDiscreteAndTotallySeparated.agdai
	agda --safe source/TypeTopology/SquashedSum.lagda
	touch $@

_build/2.6.3/agda/source/UF/SIP-Examples.agdai: source/UF/SIP-Examples.lagda _build/2.6.3/agda/source/UF/SIP.agdai  _build/2.6.3/agda/source/Naturals/Order.agdai  _build/2.6.3/agda/source/UF/Classifiers.agdai  _build/2.6.3/agda/source/UF/Powerset.agdai
	agda --safe source/UF/SIP-Examples.lagda
	touch $@

_build/2.6.3/agda/source/UF/PreUnivalence.agdai: source/UF/PreUnivalence.lagda _build/2.6.3/agda/source/UF/Embeddings.agdai
	agda --safe source/UF/PreUnivalence.lagda
	touch $@

_build/2.6.3/agda/source/UF/PreSIP.agdai: source/UF/PreSIP.lagda _build/2.6.3/agda/source/UF/PreUnivalence.agdai  _build/2.6.3/agda/source/UF/PairFun.agdai
	agda --safe source/UF/PreSIP.lagda
	touch $@

_build/2.6.3/agda/source/UF/PreSIP-Examples.agdai: source/UF/PreSIP-Examples.lagda _build/2.6.3/agda/source/UF/PreSIP.agdai
	agda --safe source/UF/PreSIP-Examples.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/Underlying.agdai: source/Ordinals/Underlying.lagda _build/2.6.3/agda/source/Ordinals/Notions.agdai
	agda --safe source/Ordinals/Underlying.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/Type.agdai: source/Ordinals/Type.lagda _build/2.6.3/agda/source/Ordinals/Underlying.agdai
	agda --safe source/Ordinals/Type.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/Maps.agdai: source/Ordinals/Maps.lagda _build/2.6.3/agda/source/Ordinals/Type.agdai  _build/2.6.3/agda/source/UF/Size.agdai  _build/2.6.3/agda/source/Notation/CanonicalMap.agdai
	agda --safe source/Ordinals/Maps.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/Equivalence.agdai: source/Ordinals/Equivalence.lagda _build/2.6.3/agda/source/UF/SIP-Examples.agdai  _build/2.6.3/agda/source/UF/PreSIP-Examples.agdai  _build/2.6.3/agda/source/Ordinals/Maps.agdai
	agda --safe source/Ordinals/Equivalence.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/OrdinalOfOrdinals.agdai: source/Ordinals/OrdinalOfOrdinals.lagda _build/2.6.3/agda/source/Ordinals/Equivalence.agdai
	agda --safe source/Ordinals/OrdinalOfOrdinals.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/LexicographicOrder.agdai: source/Ordinals/LexicographicOrder.lagda _build/2.6.3/agda/source/UF/Subsingletons.agdai
	agda --safe source/Ordinals/LexicographicOrder.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/WellOrderArithmetic.agdai: source/Ordinals/WellOrderArithmetic.lagda _build/2.6.3/agda/source/InjectiveTypes/Blackboard.agdai  _build/2.6.3/agda/source/Ordinals/LexicographicOrder.agdai  _build/2.6.3/agda/source/Ordinals/Notions.agdai
	agda --safe source/Ordinals/WellOrderArithmetic.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/InfProperty.agdai: source/TypeTopology/InfProperty.lagda _build/2.6.3/agda/source/TypeTopology/CompactTypes.agdai
	agda --safe source/TypeTopology/InfProperty.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/ToppedType.agdai: source/Ordinals/ToppedType.lagda _build/2.6.3/agda/source/Ordinals/Type.agdai  _build/2.6.3/agda/source/Notation/CanonicalMap.agdai  _build/2.6.3/agda/source/TypeTopology/InfProperty.agdai
	agda --safe source/Ordinals/ToppedType.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/Injectivity.agdai: source/Ordinals/Injectivity.lagda _build/2.6.3/agda/source/Ordinals/OrdinalOfOrdinals.agdai  _build/2.6.3/agda/source/Ordinals/WellOrderArithmetic.agdai  _build/2.6.3/agda/source/Ordinals/ToppedType.agdai
	agda --safe source/Ordinals/Injectivity.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/Arithmetic.agdai: source/Ordinals/Arithmetic.lagda _build/2.6.3/agda/source/Ordinals/Type.agdai  _build/2.6.3/agda/source/Ordinals/WellOrderArithmetic.agdai  _build/2.6.3/agda/source/CoNaturals/GenericConvergentSequence.agdai
	agda --safe source/Ordinals/Arithmetic.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/OrdinalOfTruthValues.agdai: source/Ordinals/OrdinalOfTruthValues.lagda _build/2.6.3/agda/source/Ordinals/Arithmetic.agdai  _build/2.6.3/agda/source/Ordinals/OrdinalOfOrdinals.agdai
	agda --safe source/Ordinals/OrdinalOfTruthValues.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/ToppedArithmetic.agdai: source/Ordinals/ToppedArithmetic.lagda _build/2.6.3/agda/source/TypeTopology/SquashedSum.agdai  _build/2.6.3/agda/source/Ordinals/Injectivity.agdai  _build/2.6.3/agda/source/Ordinals/OrdinalOfTruthValues.agdai
	agda --safe source/Ordinals/ToppedArithmetic.lagda
	touch $@

_build/2.6.3/agda/source/Taboos/LPO.agdai: source/Taboos/LPO.lagda _build/2.6.3/agda/source/TypeTopology/PropTychonoff.agdai  _build/2.6.3/agda/source/CoNaturals/GenericConvergentSequence.agdai
	agda --safe source/Taboos/LPO.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/ConvergentSequence.agdai: source/Ordinals/ConvergentSequence.lagda _build/2.6.3/agda/source/Ordinals/Arithmetic.agdai  _build/2.6.3/agda/source/Ordinals/OrdinalOfOrdinals.agdai  _build/2.6.3/agda/source/Taboos/LPO.agdai
	agda --safe source/Ordinals/ConvergentSequence.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/WellOrderTransport.agdai: source/Ordinals/WellOrderTransport.lagda _build/2.6.3/agda/source/Ordinals/WellOrderArithmetic.agdai  _build/2.6.3/agda/source/Ordinals/Equivalence.agdai
	agda --safe source/Ordinals/WellOrderTransport.lagda
	touch $@

_build/2.6.3/agda/source/Quotient/GivesSetReplacement.agdai: source/Quotient/GivesSetReplacement.lagda _build/2.6.3/agda/source/UF/Size.agdai  _build/2.6.3/agda/source/Quotient/GivesPropTrunc.agdai
	agda --safe source/Quotient/GivesSetReplacement.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/OrdinalOfOrdinalsSuprema.agdai: source/Ordinals/OrdinalOfOrdinalsSuprema.lagda _build/2.6.3/agda/source/Ordinals/OrdinalOfOrdinals.agdai  _build/2.6.3/agda/source/Ordinals/WellOrderTransport.agdai  _build/2.6.3/agda/source/Quotient/GivesSetReplacement.agdai
	agda --safe source/Ordinals/OrdinalOfOrdinalsSuprema.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/ArithmeticProperties.agdai: source/Ordinals/ArithmeticProperties.lagda _build/2.6.3/agda/source/Ordinals/ToppedArithmetic.agdai  _build/2.6.3/agda/source/Ordinals/ConvergentSequence.agdai  _build/2.6.3/agda/source/Ordinals/OrdinalOfOrdinalsSuprema.agdai
	agda --safe source/Ordinals/ArithmeticProperties.lagda
	touch $@

_build/2.6.3/agda/source/UF/CumulativeHierarchy.agdai: source/UF/CumulativeHierarchy.lagda _build/2.6.3/agda/source/UF/SubtypeClassifier-Properties.agdai
	agda --safe source/UF/CumulativeHierarchy.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/CumulativeHierarchy.agdai: source/Ordinals/CumulativeHierarchy.lagda _build/2.6.3/agda/source/Ordinals/ArithmeticProperties.agdai  _build/2.6.3/agda/source/UF/CumulativeHierarchy.agdai
	agda --safe source/Ordinals/CumulativeHierarchy.lagda
	touch $@

_build/2.6.3/agda/source/Games/Discussion.agdai: source/Games/Discussion.lagda _build/2.6.3/agda/source/Games/FiniteHistoryDependent.agdai  _build/2.6.3/agda/source/Ordinals/CumulativeHierarchy.agdai
	agda --safe source/Games/Discussion.lagda
	touch $@

_build/2.6.3/agda/source/Games/Examples.agdai: source/Games/Examples.lagda _build/2.6.3/agda/source/Games/FiniteHistoryDependent.agdai  _build/2.6.3/agda/source/MLTT/Athenian.agdai
	agda --safe source/Games/Examples.lagda
	touch $@

_build/2.6.3/agda/source/Games/FiniteHistoryDependentTransformer.agdai: source/Games/FiniteHistoryDependentTransformer.lagda _build/2.6.3/agda/source/Games/FiniteHistoryDependent.agdai
	agda --safe source/Games/FiniteHistoryDependentTransformer.lagda
	touch $@

_build/2.6.3/agda/source/Games/Reader.agdai: source/Games/Reader.lagda _build/2.6.3/agda/source/Games/Monad.agdai
	agda --safe source/Games/Reader.lagda
	touch $@

_build/2.6.3/agda/source/Games/TicTacToe0.agdai: source/Games/TicTacToe0.lagda _build/2.6.3/agda/source/TypeTopology/SigmaDiscreteAndTotallySeparated.agdai  _build/2.6.3/agda/source/Fin/ArgMinMax.agdai  _build/2.6.3/agda/source/Games/FiniteHistoryDependent.agdai  _build/2.6.3/agda/source/MLTT/Athenian.agdai
	agda --safe source/Games/TicTacToe0.lagda
	touch $@

_build/2.6.3/agda/source/Games/TicTacToe1.agdai: source/Games/TicTacToe1.lagda _build/2.6.3/agda/source/TypeTopology/SigmaDiscreteAndTotallySeparated.agdai  _build/2.6.3/agda/source/Games/Constructor.agdai  _build/2.6.3/agda/source/Fin/ArgMinMax.agdai  _build/2.6.3/agda/source/MLTT/Athenian.agdai
	agda --safe source/Games/TicTacToe1.lagda
	touch $@

_build/2.6.3/agda/source/Games/TicTacToe2.agdai: source/Games/TicTacToe2.lagda _build/2.6.3/agda/source/TypeTopology/SigmaDiscreteAndTotallySeparated.agdai  _build/2.6.3/agda/source/Games/Constructor.agdai  _build/2.6.3/agda/source/MLTT/Athenian.agdai
	agda --safe source/Games/TicTacToe2.lagda
	touch $@

_build/2.6.3/agda/source/Games/alpha-beta.agdai: source/Games/alpha-beta.lagda _build/2.6.3/agda/source/Games/Reader.agdai  _build/2.6.3/agda/source/Naturals/Order.agdai  _build/2.6.3/agda/source/Games/FiniteHistoryDependentTransformer.agdai  _build/2.6.3/agda/source/MLTT/Athenian.agdai
	agda --safe source/Games/alpha-beta.lagda
	touch $@

_build/2.6.3/agda/source/Games/index.agdai: source/Games/index.lagda _build/2.6.3/agda/source/Games/TicTacToe1.agdai  _build/2.6.3/agda/source/Games/TicTacToe0.agdai  _build/2.6.3/agda/source/Games/TicTacToe2.agdai  _build/2.6.3/agda/source/Games/alpha-beta.agdai  _build/2.6.3/agda/source/Games/Discussion.agdai  _build/2.6.3/agda/source/Games/Examples.agdai
	agda --safe source/Games/index.lagda
	touch $@

_build/2.6.3/agda/source/Groups/Aut.agdai: source/Groups/Aut.lagda _build/2.6.3/agda/source/Groups/Type.agdai
	agda --safe source/Groups/Aut.lagda
	touch $@

_build/2.6.3/agda/source/Relations/SRTclosure.agdai: source/Relations/SRTclosure.lagda _build/2.6.3/agda/source/Naturals/Addition.agdai  _build/2.6.3/agda/source/UF/PropTrunc.agdai
	agda --safe source/Relations/SRTclosure.lagda
	touch $@

_build/2.6.3/agda/source/Relations/ChurchRosser.agdai: source/Relations/ChurchRosser.lagda _build/2.6.3/agda/source/Relations/SRTclosure.agdai
	agda --safe source/Relations/ChurchRosser.lagda
	touch $@

_build/2.6.3/agda/source/UF/SmallnessProperties.agdai: source/UF/SmallnessProperties.lagda _build/2.6.3/agda/source/UF/Size.agdai  _build/2.6.3/agda/source/MLTT/List.agdai
	agda --safe source/UF/SmallnessProperties.lagda
	touch $@

_build/2.6.3/agda/source/Quotient/FromSetReplacement.agdai: source/Quotient/FromSetReplacement.lagda _build/2.6.3/agda/source/UF/Size.agdai  _build/2.6.3/agda/source/Quotient/Large.agdai
	agda --safe source/Quotient/FromSetReplacement.lagda
	touch $@

_build/2.6.3/agda/source/Groups/Free.agdai: source/Groups/Free.lagda _build/2.6.3/agda/source/Relations/ChurchRosser.agdai  _build/2.6.3/agda/source/UF/SmallnessProperties.agdai  _build/2.6.3/agda/source/Quotient/FromSetReplacement.agdai  _build/2.6.3/agda/source/Quotient/GivesSetReplacement.agdai  _build/2.6.3/agda/source/Groups/Type.agdai  _build/2.6.3/agda/source/Quotient/Effectivity.agdai
	agda --safe source/Groups/Free.lagda
	touch $@

_build/2.6.3/agda/source/Groups/Opposite.agdai: source/Groups/Opposite.lagda _build/2.6.3/agda/source/Groups/Type.agdai
	agda --safe source/Groups/Opposite.lagda
	touch $@

_build/2.6.3/agda/source/Groups/GroupActions.agdai: source/Groups/GroupActions.lagda _build/2.6.3/agda/source/Groups/Opposite.agdai  _build/2.6.3/agda/source/Groups/Aut.agdai
	agda --safe source/Groups/GroupActions.lagda
	touch $@

_build/2.6.3/agda/source/Groups/Large.agdai: source/Groups/Large.lagda _build/2.6.3/agda/source/Groups/Free.agdai
	agda --safe source/Groups/Large.lagda
	touch $@

_build/2.6.3/agda/source/Groups/Subgroups.agdai: source/Groups/Subgroups.lagda _build/2.6.3/agda/source/UF/Classifiers.agdai  _build/2.6.3/agda/source/Groups/Type.agdai  _build/2.6.3/agda/source/UF/Powerset.agdai
	agda --safe source/Groups/Subgroups.lagda
	touch $@

_build/2.6.3/agda/source/Groups/Torsors.agdai: source/Groups/Torsors.lagda _build/2.6.3/agda/source/Groups/GroupActions.agdai
	agda --safe source/Groups/Torsors.lagda
	touch $@

_build/2.6.3/agda/source/Groups/Type-Supplement.agdai: source/Groups/Type-Supplement.lagda _build/2.6.3/agda/source/Groups/Type.agdai
	agda --safe source/Groups/Type-Supplement.lagda
	touch $@

_build/2.6.3/agda/source/Groups/index.agdai: source/Groups/index.lagda _build/2.6.3/agda/source/Groups/Cokernel.agdai  _build/2.6.3/agda/source/Groups/Torsors.agdai  _build/2.6.3/agda/source/Groups/Large.agdai  _build/2.6.3/agda/source/Groups/Type-Supplement.agdai  _build/2.6.3/agda/source/Groups/Subgroups.agdai
	agda --safe source/Groups/index.lagda
	touch $@

_build/2.6.3/agda/source/InjectiveTypes/Article.agdai: source/InjectiveTypes/Article.lagda _build/2.6.3/agda/source/InjectiveTypes/Blackboard.agdai  _build/2.6.3/agda/source/UF/HLevels.agdai
	agda --safe source/InjectiveTypes/Article.lagda
	touch $@

_build/2.6.3/agda/source/InjectiveTypes/OverSmallMaps.agdai: source/InjectiveTypes/OverSmallMaps.lagda _build/2.6.3/agda/source/InjectiveTypes/Blackboard.agdai
	agda --safe source/InjectiveTypes/OverSmallMaps.lagda
	touch $@

_build/2.6.3/agda/source/Taboos/Decomposability.agdai: source/Taboos/Decomposability.lagda _build/2.6.3/agda/source/Ordinals/Arithmetic.agdai  _build/2.6.3/agda/source/InjectiveTypes/OverSmallMaps.agdai  _build/2.6.3/agda/source/Ordinals/Injectivity.agdai
	agda --safe source/Taboos/Decomposability.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/SimpleTypes.agdai: source/TypeTopology/SimpleTypes.lagda _build/2.6.3/agda/source/TypeTopology/WeaklyCompactTypes.agdai
	agda --safe source/TypeTopology/SimpleTypes.lagda
	touch $@

_build/2.6.3/agda/source/InjectiveTypes/CounterExamples.agdai: source/InjectiveTypes/CounterExamples.lagda _build/2.6.3/agda/source/Taboos/Decomposability.agdai  _build/2.6.3/agda/source/DedekindReals/Order.agdai  _build/2.6.3/agda/source/TypeTopology/SimpleTypes.agdai
	agda --safe source/InjectiveTypes/CounterExamples.lagda
	touch $@

_build/2.6.3/agda/source/InjectiveTypes/MathematicalStructures.agdai: source/InjectiveTypes/MathematicalStructures.lagda _build/2.6.3/agda/source/Taboos/Decomposability.agdai
	agda --safe source/InjectiveTypes/MathematicalStructures.lagda
	touch $@

_build/2.6.3/agda/source/InjectiveTypes/InhabitedTypesTaboo.agdai: source/InjectiveTypes/InhabitedTypesTaboo.lagda _build/2.6.3/agda/source/InjectiveTypes/MathematicalStructures.agdai
	agda --safe source/InjectiveTypes/InhabitedTypesTaboo.lagda
	touch $@

_build/2.6.3/agda/source/InjectiveTypes/Sigma.agdai: source/InjectiveTypes/Sigma.lagda _build/2.6.3/agda/source/InjectiveTypes/Blackboard.agdai
	agda --safe source/InjectiveTypes/Sigma.lagda
	touch $@

_build/2.6.3/agda/source/InjectiveTypes/MathematicalStructuresMoreGeneral.agdai: source/InjectiveTypes/MathematicalStructuresMoreGeneral.lagda _build/2.6.3/agda/source/InjectiveTypes/Sigma.agdai  _build/2.6.3/agda/source/Taboos/Decomposability.agdai
	agda --safe source/InjectiveTypes/MathematicalStructuresMoreGeneral.lagda
	touch $@

_build/2.6.3/agda/source/W/Properties.agdai: source/W/Properties.lagda _build/2.6.3/agda/source/W/Type.agdai  _build/2.6.3/agda/source/UF/EquivalenceExamples.agdai
	agda --safe source/W/Properties.lagda
	touch $@

_build/2.6.3/agda/source/Iterative/Multisets.agdai: source/Iterative/Multisets.lagda _build/2.6.3/agda/source/UF/Size.agdai  _build/2.6.3/agda/source/W/Properties.agdai
	agda --safe source/Iterative/Multisets.lagda
	touch $@

_build/2.6.3/agda/source/Iterative/Sets.agdai: source/Iterative/Sets.lagda _build/2.6.3/agda/source/Iterative/Multisets.agdai  _build/2.6.3/agda/source/Ordinals/Notions.agdai
	agda --safe source/Iterative/Sets.lagda
	touch $@

_build/2.6.3/agda/source/Iterative/Multisets-Addendum.agdai: source/Iterative/Multisets-Addendum.lagda _build/2.6.3/agda/source/Iterative/Sets.agdai  _build/2.6.3/agda/source/Taboos/Decomposability.agdai
	agda --safe source/Iterative/Multisets-Addendum.lagda
	touch $@

_build/2.6.3/agda/source/Iterative/Sets-Addendum.agdai: source/Iterative/Sets-Addendum.lagda _build/2.6.3/agda/source/Iterative/Multisets-Addendum.agdai
	agda --safe source/Iterative/Sets-Addendum.lagda
	touch $@

_build/2.6.3/agda/source/InjectiveTypes/Resizing.agdai: source/InjectiveTypes/Resizing.lagda _build/2.6.3/agda/source/InjectiveTypes/Article.agdai  _build/2.6.3/agda/source/Iterative/Sets-Addendum.agdai
	agda --safe source/InjectiveTypes/Resizing.lagda
	touch $@

_build/2.6.3/agda/source/Iterative/Ordinals.agdai: source/Iterative/Ordinals.lagda _build/2.6.3/agda/source/Iterative/Sets.agdai  _build/2.6.3/agda/source/Ordinals/OrdinalOfOrdinals.agdai  _build/2.6.3/agda/source/Ordinals/WellOrderTransport.agdai
	agda --safe source/Iterative/Ordinals.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/ConvergentSequenceHasInf.agdai: source/TypeTopology/ConvergentSequenceHasInf.lagda _build/2.6.3/agda/source/TypeTopology/InfProperty.agdai  _build/2.6.3/agda/source/CoNaturals/GenericConvergentSequence.agdai
	agda --safe source/TypeTopology/ConvergentSequenceHasInf.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/CantorSearch.agdai: source/TypeTopology/CantorSearch.lagda _build/2.6.3/agda/source/Naturals/Order.agdai
	agda --safe source/TypeTopology/CantorSearch.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/TheTopologyOfTheUniverse.agdai: source/TypeTopology/TheTopologyOfTheUniverse.lagda _build/2.6.3/agda/source/CoNaturals/GenericConvergentSequence.agdai
	agda --safe source/TypeTopology/TheTopologyOfTheUniverse.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/RicesTheoremForTheUniverse.agdai: source/TypeTopology/RicesTheoremForTheUniverse.lagda _build/2.6.3/agda/source/TypeTopology/TheTopologyOfTheUniverse.agdai  _build/2.6.3/agda/source/Taboos/BasicDiscontinuity.agdai
	agda --safe source/TypeTopology/RicesTheoremForTheUniverse.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/UniformSearch.agdai: source/TypeTopology/UniformSearch.lagda _build/2.6.3/agda/source/TypeTopology/CompactTypes.agdai
	agda --safe source/TypeTopology/UniformSearch.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/LexicographicCompactness.agdai: source/TypeTopology/LexicographicCompactness.lagda _build/2.6.3/agda/source/TypeTopology/InfProperty.agdai  _build/2.6.3/agda/source/Ordinals/LexicographicOrder.agdai
	agda --safe source/TypeTopology/LexicographicCompactness.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/ADecidableQuantificationOverTheNaturals.agdai: source/TypeTopology/ADecidableQuantificationOverTheNaturals.lagda _build/2.6.3/agda/source/TypeTopology/GenericConvergentSequenceCompactness.agdai
	agda --safe source/TypeTopology/ADecidableQuantificationOverTheNaturals.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/DecidabilityOfNonContinuity.agdai: source/TypeTopology/DecidabilityOfNonContinuity.lagda _build/2.6.3/agda/source/TypeTopology/ADecidableQuantificationOverTheNaturals.agdai
	agda --safe source/TypeTopology/DecidabilityOfNonContinuity.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/PropInfTychonoff.agdai: source/TypeTopology/PropInfTychonoff.lagda _build/2.6.3/agda/source/TypeTopology/InfProperty.agdai
	agda --safe source/TypeTopology/PropInfTychonoff.lagda
	touch $@

_build/2.6.3/agda/source/Naturals/Binary.agdai: source/Naturals/Binary.lagda _build/2.6.3/agda/source/UF/DiscreteAndSeparated.agdai
	agda --safe source/Naturals/Binary.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/SquashedCantor.agdai: source/TypeTopology/SquashedCantor.lagda _build/2.6.3/agda/source/TypeTopology/SquashedSum.agdai  _build/2.6.3/agda/source/Naturals/Binary.agdai
	agda --safe source/TypeTopology/SquashedCantor.lagda
	touch $@

_build/2.6.3/agda/source/TypeTopology/index.agdai: source/TypeTopology/index.lagda _build/2.6.3/agda/source/TypeTopology/ConvergentSequenceHasInf.agdai  _build/2.6.3/agda/source/TypeTopology/CantorSearch.agdai  _build/2.6.3/agda/source/TypeTopology/RicesTheoremForTheUniverse.agdai  _build/2.6.3/agda/source/TypeTopology/UniformSearch.agdai  _build/2.6.3/agda/source/TypeTopology/LexicographicCompactness.agdai  _build/2.6.3/agda/source/TypeTopology/DecidabilityOfNonContinuity.agdai  _build/2.6.3/agda/source/TypeTopology/PropInfTychonoff.agdai  _build/2.6.3/agda/source/TypeTopology/SimpleTypes.agdai  _build/2.6.3/agda/source/TypeTopology/SquashedCantor.agdai
	agda --safe source/TypeTopology/index.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/BuraliForti.agdai: source/Ordinals/BuraliForti.lagda _build/2.6.3/agda/source/Groups/Large.agdai  _build/2.6.3/agda/source/Ordinals/ArithmeticProperties.agdai
	agda --safe source/Ordinals/BuraliForti.lagda
	touch $@

_build/2.6.3/agda/source/UF/Choice.agdai: source/UF/Choice.lagda _build/2.6.3/agda/source/UF/Powerset.agdai
	agda --safe source/UF/Choice.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/WellOrderingTaboo.agdai: source/Ordinals/WellOrderingTaboo.lagda _build/2.6.3/agda/source/UF/Choice.agdai  _build/2.6.3/agda/source/Quotient/Large.agdai  _build/2.6.3/agda/source/Ordinals/Notions.agdai
	agda --safe source/Ordinals/WellOrderingTaboo.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/WellOrderingPrinciple.agdai: source/Ordinals/WellOrderingPrinciple.lagda _build/2.6.3/agda/source/Ordinals/BuraliForti.agdai  _build/2.6.3/agda/source/UF/Logic.agdai  _build/2.6.3/agda/source/Ordinals/WellOrderingTaboo.agdai
	agda --safe source/Ordinals/WellOrderingPrinciple.lagda
	touch $@

_build/2.6.3/agda/source/NotionsOfDecidability/DecidableClassifier.agdai: source/NotionsOfDecidability/DecidableClassifier.lagda _build/2.6.3/agda/source/UF/Powerset.agdai
	agda --safe source/NotionsOfDecidability/DecidableClassifier.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/Taboos.agdai: source/Ordinals/Taboos.lagda _build/2.6.3/agda/source/Ordinals/Arithmetic.agdai  _build/2.6.3/agda/source/NotionsOfDecidability/DecidableClassifier.agdai  _build/2.6.3/agda/source/Ordinals/OrdinalOfOrdinalsSuprema.agdai
	agda --safe source/Ordinals/Taboos.lagda
	touch $@

_build/2.6.3/agda/source/UF/CumulativeHierarchy-LocallySmall.agdai: source/UF/CumulativeHierarchy-LocallySmall.lagda _build/2.6.3/agda/source/UF/Size.agdai  _build/2.6.3/agda/source/UF/Logic.agdai  _build/2.6.3/agda/source/UF/CumulativeHierarchy.agdai
	agda --safe source/UF/CumulativeHierarchy-LocallySmall.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/CumulativeHierarchy-Addendum.agdai: source/Ordinals/CumulativeHierarchy-Addendum.lagda _build/2.6.3/agda/source/UF/CumulativeHierarchy-LocallySmall.agdai  _build/2.6.3/agda/source/Ordinals/CumulativeHierarchy.agdai
	agda --safe source/Ordinals/CumulativeHierarchy-Addendum.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/ShulmanTaboo.agdai: source/Ordinals/ShulmanTaboo.lagda _build/2.6.3/agda/source/Ordinals/OrdinalOfTruthValues.agdai
	agda --safe source/Ordinals/ShulmanTaboo.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/Closure.agdai: source/Ordinals/Closure.lagda _build/2.6.3/agda/source/TypeTopology/ConvergentSequenceHasInf.agdai  _build/2.6.3/agda/source/Ordinals/ToppedArithmetic.agdai  _build/2.6.3/agda/source/TypeTopology/LexicographicCompactness.agdai  _build/2.6.3/agda/source/TypeTopology/PropInfTychonoff.agdai  _build/2.6.3/agda/source/TypeTopology/SquashedCantor.agdai
	agda --safe source/Ordinals/Closure.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/NotationInterpretation2.agdai: source/Ordinals/NotationInterpretation2.lagda _build/2.6.3/agda/source/Taboos/LPO.agdai  _build/2.6.3/agda/source/Ordinals/Closure.agdai
	agda --safe source/Ordinals/NotationInterpretation2.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/TrichotomousType.agdai: source/Ordinals/TrichotomousType.lagda _build/2.6.3/agda/source/Ordinals/Type.agdai  _build/2.6.3/agda/source/Notation/CanonicalMap.agdai
	agda --safe source/Ordinals/TrichotomousType.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/TrichotomousArithmetic.agdai: source/Ordinals/TrichotomousArithmetic.lagda _build/2.6.3/agda/source/Ordinals/Arithmetic.agdai  _build/2.6.3/agda/source/Ordinals/TrichotomousType.agdai
	agda --safe source/Ordinals/TrichotomousArithmetic.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/SupSum.agdai: source/Ordinals/SupSum.lagda _build/2.6.3/agda/source/Ordinals/TrichotomousArithmetic.agdai  _build/2.6.3/agda/source/Ordinals/ArithmeticProperties.agdai
	agda --safe source/Ordinals/SupSum.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/Brouwer.agdai: source/Ordinals/Brouwer.lagda _build/2.6.3/agda/source/MLTT/Spartan.agdai
	agda --safe source/Ordinals/Brouwer.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/NotationInterpretation0.agdai: source/Ordinals/NotationInterpretation0.lagda _build/2.6.3/agda/source/Ordinals/SupSum.agdai  _build/2.6.3/agda/source/Ordinals/Brouwer.agdai
	agda --safe source/Ordinals/NotationInterpretation0.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/Codes.agdai: source/Ordinals/Codes.lagda _build/2.6.3/agda/source/MLTT/Spartan.agdai
	agda --safe source/Ordinals/Codes.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/NotationInterpretation1.agdai: source/Ordinals/NotationInterpretation1.lagda _build/2.6.3/agda/source/Ordinals/Codes.agdai  _build/2.6.3/agda/source/Ordinals/ArithmeticProperties.agdai  _build/2.6.3/agda/source/Ordinals/Closure.agdai
	agda --safe source/Ordinals/NotationInterpretation1.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/NotationInterpretation.agdai: source/Ordinals/NotationInterpretation.lagda _build/2.6.3/agda/source/Ordinals/NotationInterpretation2.agdai  _build/2.6.3/agda/source/Ordinals/NotationInterpretation0.agdai  _build/2.6.3/agda/source/Ordinals/NotationInterpretation1.agdai
	agda --safe source/Ordinals/NotationInterpretation.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/Indecomposable.agdai: source/Ordinals/Indecomposable.lagda _build/2.6.3/agda/source/Taboos/Decomposability.agdai
	agda --safe source/Ordinals/Indecomposable.lagda
	touch $@

_build/2.6.3/agda/source/Ordinals/index.agdai: source/Ordinals/index.lagda _build/2.6.3/agda/source/Ordinals/WellOrderingPrinciple.agdai  _build/2.6.3/agda/source/Ordinals/Taboos.agdai  _build/2.6.3/agda/source/Ordinals/CumulativeHierarchy-Addendum.agdai  _build/2.6.3/agda/source/Ordinals/ShulmanTaboo.agdai  _build/2.6.3/agda/source/Ordinals/NotationInterpretation.agdai  _build/2.6.3/agda/source/Ordinals/Indecomposable.agdai
	agda --safe source/Ordinals/index.lagda
	touch $@

_build/2.6.3/agda/source/InjectiveTypes/index.agdai: source/InjectiveTypes/index.lagda _build/2.6.3/agda/source/Iterative/Ordinals.agdai  _build/2.6.3/agda/source/TypeTopology/index.agdai  _build/2.6.3/agda/source/Ordinals/index.agdai  _build/2.6.3/agda/source/InjectiveTypes/MathematicalStructuresMoreGeneral.agdai  _build/2.6.3/agda/source/InjectiveTypes/InhabitedTypesTaboo.agdai  _build/2.6.3/agda/source/InjectiveTypes/CounterExamples.agdai  _build/2.6.3/agda/source/InjectiveTypes/Resizing.agdai
	agda --safe source/InjectiveTypes/index.lagda
	touch $@

_build/2.6.3/agda/source/Integers/index.agdai: source/Integers/index.lagda _build/2.6.3/agda/source/Integers/HCF.agdai  _build/2.6.3/agda/source/Integers/Exponentiation.agdai  _build/2.6.3/agda/source/Integers/Parity.agdai
	agda --safe source/Integers/index.lagda
	touch $@

_build/2.6.3/agda/source/Iterative/Ordinals-Addendum.agdai: source/Iterative/Ordinals-Addendum.lagda _build/2.6.3/agda/source/Iterative/Ordinals.agdai  _build/2.6.3/agda/source/Ordinals/Injectivity.agdai
	agda --safe source/Iterative/Ordinals-Addendum.lagda
	touch $@

_build/2.6.3/agda/source/Iterative/index.agdai: source/Iterative/index.lagda _build/2.6.3/agda/source/Iterative/Sets-Addendum.agdai  _build/2.6.3/agda/source/Iterative/Ordinals-Addendum.agdai
	agda --safe source/Iterative/index.lagda
	touch $@

_build/2.6.3/agda/source/Lifting/MonadVariation.agdai: source/Lifting/MonadVariation.lagda _build/2.6.3/agda/source/Lifting/EmbeddingDirectly.agdai
	agda --safe source/Lifting/MonadVariation.lagda
	touch $@

_build/2.6.3/agda/source/Lifting/Set.agdai: source/Lifting/Set.lagda _build/2.6.3/agda/source/Lifting/Lifting.agdai  _build/2.6.3/agda/source/UF/Sets-Properties.agdai
	agda --safe source/Lifting/Set.lagda
	touch $@

_build/2.6.3/agda/source/Lifting/index.agdai: source/Lifting/index.lagda _build/2.6.3/agda/source/Lifting/MonadVariation.agdai  _build/2.6.3/agda/source/Lifting/Miscelanea-PropExt-FunExt.agdai  _build/2.6.3/agda/source/Lifting/Set.agdai  _build/2.6.3/agda/source/Lifting/Algebras.agdai  _build/2.6.3/agda/source/Lifting/EmbeddingViaSIP.agdai  _build/2.6.3/agda/source/Lifting/Size.agdai
	agda --safe source/Lifting/index.lagda
	touch $@

_build/2.6.3/agda/source/Locales/Frame.agdai: source/Locales/Frame.lagda _build/2.6.3/agda/source/Slice/Family.agdai  _build/2.6.3/agda/source/UF/Logic.agdai  _build/2.6.3/agda/source/MLTT/List.agdai
	agda --safe source/Locales/Frame.lagda
	touch $@

_build/2.6.3/agda/source/Locales/GaloisConnection.agdai: source/Locales/GaloisConnection.lagda _build/2.6.3/agda/source/UF/SubtypeClassifier-Properties.agdai  _build/2.6.3/agda/source/Locales/Frame.agdai
	agda --safe source/Locales/GaloisConnection.lagda
	touch $@

_build/2.6.3/agda/source/Locales/AdjointFunctorTheoremForFrames.agdai: source/Locales/AdjointFunctorTheoremForFrames.lagda _build/2.6.3/agda/source/Locales/GaloisConnection.agdai
	agda --safe source/Locales/AdjointFunctorTheoremForFrames.lagda
	touch $@

_build/2.6.3/agda/source/Locales/HeytingImplication.agdai: source/Locales/HeytingImplication.lagda _build/2.6.3/agda/source/Locales/AdjointFunctorTheoremForFrames.agdai
	agda --safe source/Locales/HeytingImplication.lagda
	touch $@

_build/2.6.3/agda/source/Locales/InitialFrame.agdai: source/Locales/InitialFrame.lagda _build/2.6.3/agda/source/Locales/Frame.agdai
	agda --safe source/Locales/InitialFrame.lagda
	touch $@

_build/2.6.3/agda/source/Locales/CompactRegular.agdai: source/Locales/CompactRegular.lagda _build/2.6.3/agda/source/Locales/HeytingImplication.agdai  _build/2.6.3/agda/source/Locales/InitialFrame.agdai
	agda --safe source/Locales/CompactRegular.lagda
	touch $@

_build/2.6.3/agda/source/Locales/BooleanAlgebra.agdai: source/Locales/BooleanAlgebra.lagda _build/2.6.3/agda/source/Locales/CompactRegular.agdai
	agda --safe source/Locales/BooleanAlgebra.lagda
	touch $@

_build/2.6.3/agda/source/Locales/Nucleus.agdai: source/Locales/Nucleus.lagda _build/2.6.3/agda/source/Locales/HeytingImplication.agdai
	agda --safe source/Locales/Nucleus.lagda
	touch $@

_build/2.6.3/agda/source/Locales/PatchLocale.agdai: source/Locales/PatchLocale.lagda _build/2.6.3/agda/source/Locales/CompactRegular.agdai  _build/2.6.3/agda/source/Locales/Nucleus.agdai
	agda --safe source/Locales/PatchLocale.lagda
	touch $@

_build/2.6.3/agda/source/Locales/PatchOfOmega.agdai: source/Locales/PatchOfOmega.lagda _build/2.6.3/agda/source/Locales/PatchLocale.agdai
	agda --safe source/Locales/PatchOfOmega.lagda
	touch $@

_build/2.6.3/agda/source/Locales/PatchProperties.agdai: source/Locales/PatchProperties.lagda _build/2.6.3/agda/source/Locales/PatchLocale.agdai
	agda --safe source/Locales/PatchProperties.lagda
	touch $@

_build/2.6.3/agda/source/Locales/ScottLocale.agdai: source/Locales/ScottLocale.lagda _build/2.6.3/agda/source/DomainTheory/Topology/ScottTopology.agdai  _build/2.6.3/agda/source/Locales/Frame.agdai  _build/2.6.3/agda/source/DomainTheory/Lifting/LiftingSet.agdai
	agda --safe source/Locales/ScottLocale.lagda
	touch $@

_build/2.6.3/agda/source/Locales/UniversalPropertyOfPatch.agdai: source/Locales/UniversalPropertyOfPatch.lagda _build/2.6.3/agda/source/UF/Size.agdai  _build/2.6.3/agda/source/Locales/PatchProperties.agdai
	agda --safe source/Locales/UniversalPropertyOfPatch.lagda
	touch $@

_build/2.6.3/agda/source/Locales/index.agdai: source/Locales/index.lagda _build/2.6.3/agda/source/Locales/UniversalPropertyOfPatch.agdai  _build/2.6.3/agda/source/Locales/ScottLocale.agdai  _build/2.6.3/agda/source/Locales/BooleanAlgebra.agdai  _build/2.6.3/agda/source/Locales/PatchOfOmega.agdai
	agda --safe source/Locales/index.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Powerset.agdai: source/MGS/Powerset.lagda _build/2.6.3/agda/source/MGS/More-FunExt-Consequences.agdai
	agda --safe source/MGS/Powerset.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Subsingleton-Truncation.agdai: source/MGS/Subsingleton-Truncation.lagda _build/2.6.3/agda/source/MGS/Embeddings.agdai  _build/2.6.3/agda/source/MGS/Powerset.agdai
	agda --safe source/MGS/Subsingleton-Truncation.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Unique-Existence.agdai: source/MGS/Unique-Existence.lagda _build/2.6.3/agda/source/MGS/Subsingleton-Theorems.agdai
	agda --safe source/MGS/Unique-Existence.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Yoneda.agdai: source/MGS/Yoneda.lagda _build/2.6.3/agda/source/MGS/Unique-Existence.agdai  _build/2.6.3/agda/source/MGS/Embeddings.agdai
	agda --safe source/MGS/Yoneda.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Choice.agdai: source/MGS/Choice.lagda _build/2.6.3/agda/source/MGS/Subsingleton-Truncation.agdai  _build/2.6.3/agda/source/MGS/Universe-Lifting.agdai  _build/2.6.3/agda/source/MGS/Yoneda.agdai
	agda --safe source/MGS/Choice.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Map-Classifiers.agdai: source/MGS/Map-Classifiers.lagda _build/2.6.3/agda/source/MGS/FunExt-from-Univalence.agdai
	agda --safe source/MGS/Map-Classifiers.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Classifiers.agdai: source/MGS/Classifiers.lagda _build/2.6.3/agda/source/MGS/Map-Classifiers.agdai  _build/2.6.3/agda/source/MGS/Powerset.agdai  _build/2.6.3/agda/source/MGS/Universe-Lifting.agdai
	agda --safe source/MGS/Classifiers.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Function-Graphs.agdai: source/MGS/Function-Graphs.lagda _build/2.6.3/agda/source/MGS/Yoneda.agdai
	agda --safe source/MGS/Function-Graphs.lagda
	touch $@

_build/2.6.3/agda/source/MGS/More-Exercise-Solutions.agdai: source/MGS/More-Exercise-Solutions.lagda _build/2.6.3/agda/source/MGS/Subsingleton-Truncation.agdai  _build/2.6.3/agda/source/MGS/Classifiers.agdai
	agda --safe source/MGS/More-Exercise-Solutions.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Partial-Functions.agdai: source/MGS/Partial-Functions.lagda _build/2.6.3/agda/source/MGS/More-FunExt-Consequences.agdai
	agda --safe source/MGS/Partial-Functions.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Quotient.agdai: source/MGS/Quotient.lagda _build/2.6.3/agda/source/MGS/Subsingleton-Truncation.agdai  _build/2.6.3/agda/source/MGS/Unique-Existence.agdai
	agda --safe source/MGS/Quotient.lagda
	touch $@

_build/2.6.3/agda/source/MGS/SIP.agdai: source/MGS/SIP.lagda _build/2.6.3/agda/source/MGS/Subsingleton-Truncation.agdai  _build/2.6.3/agda/source/MGS/Classifiers.agdai  _build/2.6.3/agda/source/MGS/Yoneda.agdai
	agda --safe source/MGS/SIP.lagda
	touch $@

_build/2.6.3/agda/source/MGS/Size.agdai: source/MGS/Size.lagda _build/2.6.3/agda/source/MGS/Subsingleton-Truncation.agdai  _build/2.6.3/agda/source/MGS/Universe-Lifting.agdai
	agda --safe source/MGS/Size.lagda
	touch $@

_build/2.6.3/agda/source/MGS/index.agdai: source/MGS/index.lagda _build/2.6.3/agda/source/MGS/More-Exercise-Solutions.agdai  _build/2.6.3/agda/source/MGS/TypeTopology-Interface.agdai  _build/2.6.3/agda/source/MGS/Partial-Functions.agdai  _build/2.6.3/agda/source/MGS/Size.agdai  _build/2.6.3/agda/source/MGS/Choice.agdai  _build/2.6.3/agda/source/MGS/Function-Graphs.agdai  _build/2.6.3/agda/source/MGS/Quotient.agdai  _build/2.6.3/agda/source/MGS/SIP.agdai
	agda --safe source/MGS/index.lagda
	touch $@

_build/2.6.3/agda/source/MLTT/index.agdai: source/MLTT/index.lagda _build/2.6.3/agda/source/MLTT/SpartanList.agdai  _build/2.6.3/agda/source/MLTT/Athenian.agdai
	agda --safe source/MLTT/index.lagda
	touch $@

_build/2.6.3/agda/source/MetricSpaces/index.agdai: source/MetricSpaces/index.lagda _build/2.6.3/agda/source/MetricSpaces/DedekindReals.agdai
	agda --safe source/MetricSpaces/index.lagda
	touch $@

_build/2.6.3/agda/source/Modal/Homotopy.agdai: source/Modal/Homotopy.lagda _build/2.6.3/agda/source/UF/Embeddings.agdai
	agda --safe source/Modal/Homotopy.lagda
	touch $@

_build/2.6.3/agda/source/Slice/Slice.agdai: source/Slice/Slice.lagda _build/2.6.3/agda/source/UF/Size.agdai  _build/2.6.3/agda/source/UF/Classifiers.agdai
	agda --safe source/Slice/Slice.lagda
	touch $@

_build/2.6.3/agda/source/Modal/Subuniverse.agdai: source/Modal/Subuniverse.lagda _build/2.6.3/agda/source/UF/Univalence.agdai  _build/2.6.3/agda/source/UF/FunExt.agdai
	agda --safe source/Modal/Subuniverse.lagda
	touch $@

_build/2.6.3/agda/source/Modal/ReflectiveSubuniverse.agdai: source/Modal/ReflectiveSubuniverse.lagda _build/2.6.3/agda/source/Slice/Slice.agdai  _build/2.6.3/agda/source/Modal/Homotopy.agdai  _build/2.6.3/agda/source/Modal/Subuniverse.agdai
	agda --safe source/Modal/ReflectiveSubuniverse.lagda
	touch $@

_build/2.6.3/agda/source/Modal/index.agdai: source/Modal/index.lagda _build/2.6.3/agda/source/Modal/ReflectiveSubuniverse.agdai
	agda --safe source/Modal/index.lagda
	touch $@

_build/2.6.3/agda/source/Naturals/RootsTruncation.agdai: source/Naturals/RootsTruncation.lagda _build/2.6.3/agda/source/UF/KrausLemma.agdai  _build/2.6.3/agda/source/Naturals/Order.agdai
	agda --safe source/Naturals/RootsTruncation.lagda
	touch $@

_build/2.6.3/agda/source/Naturals/index.agdai: source/Naturals/index.lagda _build/2.6.3/agda/source/Naturals/Parity.agdai  _build/2.6.3/agda/source/Naturals/UniversalProperty.agdai  _build/2.6.3/agda/source/Naturals/Binary.agdai  _build/2.6.3/agda/source/Naturals/Sequence.agdai  _build/2.6.3/agda/source/Naturals/HCF.agdai  _build/2.6.3/agda/source/Naturals/RootsTruncation.agdai
	agda --safe source/Naturals/index.lagda
	touch $@

_build/2.6.3/agda/source/Notation/Plus.agdai: source/Notation/Plus.lagda _build/2.6.3/agda/source/MLTT/Universes.agdai
	agda --safe source/Notation/Plus.lagda
	touch $@

_build/2.6.3/agda/source/Notation/UnderlyingType.agdai: source/Notation/UnderlyingType.lagda _build/2.6.3/agda/source/MLTT/Spartan.agdai
	agda --safe source/Notation/UnderlyingType.lagda
	touch $@

_build/2.6.3/agda/source/Notation/index.agdai: source/Notation/index.lagda _build/2.6.3/agda/source/Notation/UnderlyingType.agdai  _build/2.6.3/agda/source/Notation/CanonicalMap.agdai  _build/2.6.3/agda/source/Notation/Plus.agdai  _build/2.6.3/agda/source/Notation/Order.agdai
	agda --safe source/Notation/index.lagda
	touch $@

_build/2.6.3/agda/source/NotionsOfDecidability/Digression.agdai: source/NotionsOfDecidability/Digression.lagda _build/2.6.3/agda/source/UF/Equiv.agdai
	agda --safe source/NotionsOfDecidability/Digression.lagda
	touch $@

_build/2.6.3/agda/source/UF/Powerset-Resizing.agdai: source/UF/Powerset-Resizing.lagda _build/2.6.3/agda/source/UF/Size.agdai  _build/2.6.3/agda/source/UF/Powerset.agdai
	agda --safe source/UF/Powerset-Resizing.lagda
	touch $@

_build/2.6.3/agda/source/Posets/Frame.agdai: source/Posets/Frame.lagda _build/2.6.3/agda/source/UF/SIP-Examples.agdai
	agda --safe source/Posets/Frame.lagda
	touch $@

_build/2.6.3/agda/source/Posets/sigma-sup-lattice.agdai: source/Posets/sigma-sup-lattice.lagda _build/2.6.3/agda/source/UF/SIP.agdai
	agda --safe source/Posets/sigma-sup-lattice.lagda
	touch $@

_build/2.6.3/agda/source/Posets/sigma-frame.agdai: source/Posets/sigma-frame.lagda _build/2.6.3/agda/source/Posets/Frame.agdai  _build/2.6.3/agda/source/Posets/sigma-sup-lattice.agdai
	agda --safe source/Posets/sigma-frame.lagda
	touch $@

_build/2.6.3/agda/source/NotionsOfDecidability/QuasiDecidable.agdai: source/NotionsOfDecidability/QuasiDecidable.lagda _build/2.6.3/agda/source/UF/Powerset-Resizing.agdai  _build/2.6.3/agda/source/Dominance/Definition.agdai  _build/2.6.3/agda/source/Posets/sigma-frame.agdai
	agda --safe source/NotionsOfDecidability/QuasiDecidable.lagda
	touch $@

_build/2.6.3/agda/source/NotionsOfDecidability/SemiDecidable.agdai: source/NotionsOfDecidability/SemiDecidable.lagda _build/2.6.3/agda/source/Notation/CanonicalMap.agdai  _build/2.6.3/agda/source/NotionsOfDecidability/DecidableClassifier.agdai  _build/2.6.3/agda/source/Naturals/Binary.agdai  _build/2.6.3/agda/source/Fin/Topology.agdai  _build/2.6.3/agda/source/Fin/Variation.agdai
	agda --safe source/NotionsOfDecidability/SemiDecidable.lagda
	touch $@

_build/2.6.3/agda/source/NotionsOfDecidability/index.agdai: source/NotionsOfDecidability/index.lagda _build/2.6.3/agda/source/NotionsOfDecidability/Digression.agdai  _build/2.6.3/agda/source/NotionsOfDecidability/QuasiDecidable.agdai  _build/2.6.3/agda/source/NotionsOfDecidability/SemiDecidable.agdai
	agda --safe source/NotionsOfDecidability/index.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Combinatory/index.agdai: source/PCF/Combinatory/index.lagda _build/2.6.3/agda/source/PCF/Combinatory/ScottModelOfPCF.agdai
	agda --safe source/PCF/Combinatory/index.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Lambda/AbstractSyntax.agdai: source/PCF/Lambda/AbstractSyntax.lagda _build/2.6.3/agda/source/UF/PropTrunc.agdai
	agda --safe source/PCF/Lambda/AbstractSyntax.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Lambda/Substitution.agdai: source/PCF/Lambda/Substitution.lagda _build/2.6.3/agda/source/PCF/Lambda/AbstractSyntax.agdai
	agda --safe source/PCF/Lambda/Substitution.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Lambda/ScottModelOfTypes.agdai: source/PCF/Lambda/ScottModelOfTypes.lagda _build/2.6.3/agda/source/DomainTheory/Basics/Exponential.agdai  _build/2.6.3/agda/source/PCF/Lambda/AbstractSyntax.agdai  _build/2.6.3/agda/source/DomainTheory/Lifting/LiftingSet.agdai
	agda --safe source/PCF/Lambda/ScottModelOfTypes.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Lambda/ScottModelOfContexts.agdai: source/PCF/Lambda/ScottModelOfContexts.lagda _build/2.6.3/agda/source/DomainTheory/Basics/Curry.agdai  _build/2.6.3/agda/source/PCF/Lambda/ScottModelOfTypes.agdai
	agda --safe source/PCF/Lambda/ScottModelOfContexts.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Lambda/ScottModelOfIfZero.agdai: source/PCF/Lambda/ScottModelOfIfZero.lagda _build/2.6.3/agda/source/PCF/Lambda/ScottModelOfContexts.agdai  _build/2.6.3/agda/source/PCF/Combinatory/PCFCombinators.agdai
	agda --safe source/PCF/Lambda/ScottModelOfIfZero.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Lambda/ScottModelOfTerms.agdai: source/PCF/Lambda/ScottModelOfTerms.lagda _build/2.6.3/agda/source/PCF/Lambda/ScottModelOfIfZero.agdai  _build/2.6.3/agda/source/DomainTheory/Basics/LeastFixedPoint.agdai
	agda --safe source/PCF/Lambda/ScottModelOfTerms.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Lambda/BigStep.agdai: source/PCF/Lambda/BigStep.lagda _build/2.6.3/agda/source/PCF/Lambda/AbstractSyntax.agdai
	agda --safe source/PCF/Lambda/BigStep.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Lambda/ApplicativeApproximation.agdai: source/PCF/Lambda/ApplicativeApproximation.lagda _build/2.6.3/agda/source/PCF/Lambda/BigStep.agdai
	agda --safe source/PCF/Lambda/ApplicativeApproximation.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Lambda/Adequacy.agdai: source/PCF/Lambda/Adequacy.lagda _build/2.6.3/agda/source/PCF/Lambda/Substitution.agdai  _build/2.6.3/agda/source/PCF/Lambda/ScottModelOfTerms.agdai  _build/2.6.3/agda/source/DomainTheory/Lifting/LiftingDcpo.agdai  _build/2.6.3/agda/source/PCF/Lambda/ApplicativeApproximation.agdai
	agda --safe source/PCF/Lambda/Adequacy.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Lambda/SubstitutionDenotational.agdai: source/PCF/Lambda/SubstitutionDenotational.lagda _build/2.6.3/agda/source/PCF/Lambda/ScottModelOfTerms.agdai
	agda --safe source/PCF/Lambda/SubstitutionDenotational.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Lambda/Correctness.agdai: source/PCF/Lambda/Correctness.lagda _build/2.6.3/agda/source/PCF/Lambda/SubstitutionDenotational.agdai  _build/2.6.3/agda/source/PCF/Lambda/BigStep.agdai
	agda --safe source/PCF/Lambda/Correctness.lagda
	touch $@

_build/2.6.3/agda/source/PCF/Lambda/index.agdai: source/PCF/Lambda/index.lagda _build/2.6.3/agda/source/PCF/Lambda/Correctness.agdai  _build/2.6.3/agda/source/PCF/Lambda/Adequacy.agdai
	agda --safe source/PCF/Lambda/index.lagda
	touch $@

_build/2.6.3/agda/source/PCF/index.agdai: source/PCF/index.lagda _build/2.6.3/agda/source/PCF/Lambda/index.agdai  _build/2.6.3/agda/source/PCF/Combinatory/index.agdai
	agda --safe source/PCF/index.lagda
	touch $@

_build/2.6.3/agda/source/Posets/FreeJoinSemiLattice.agdai: source/Posets/FreeJoinSemiLattice.lagda _build/2.6.3/agda/source/UF/Powerset-Fin.agdai
	agda --safe source/Posets/FreeJoinSemiLattice.lagda
	touch $@

_build/2.6.3/agda/source/Posets/FreeSupLattice.agdai: source/Posets/FreeSupLattice.lagda _build/2.6.3/agda/source/UF/Powerset.agdai
	agda --safe source/Posets/FreeSupLattice.lagda
	touch $@

_build/2.6.3/agda/source/Posets/index.agdai: source/Posets/index.lagda _build/2.6.3/agda/source/Posets/FreeJoinSemiLattice.agdai  _build/2.6.3/agda/source/Posets/Poset.agdai  _build/2.6.3/agda/source/Posets/PosetReflection.agdai  _build/2.6.3/agda/source/Posets/FreeSupLattice.agdai  _build/2.6.3/agda/source/Posets/sigma-frame.agdai
	agda --safe source/Posets/index.lagda
	touch $@

_build/2.6.3/agda/source/UF/PropTrunc-Variation.agdai: source/UF/PropTrunc-Variation.lagda _build/2.6.3/agda/source/UF/Subsingletons-FunExt.agdai
	agda --safe source/UF/PropTrunc-Variation.lagda
	touch $@

_build/2.6.3/agda/source/UF/ImageAndSurjection-Variation.agdai: source/UF/ImageAndSurjection-Variation.lagda _build/2.6.3/agda/source/UF/PropTrunc-Variation.agdai  _build/2.6.3/agda/source/UF/Embeddings.agdai
	agda --safe source/UF/ImageAndSurjection-Variation.lagda
	touch $@

_build/2.6.3/agda/source/Quotient/Large-Variation.agdai: source/Quotient/Large-Variation.lagda _build/2.6.3/agda/source/UF/SubtypeClassifier-Properties.agdai  _build/2.6.3/agda/source/UF/ImageAndSurjection-Variation.agdai
	agda --safe source/Quotient/Large-Variation.lagda
	touch $@

_build/2.6.3/agda/source/Quotient/index.agdai: source/Quotient/index.lagda _build/2.6.3/agda/source/Quotient/FromSetReplacement.agdai  _build/2.6.3/agda/source/Quotient/GivesSetReplacement.agdai  _build/2.6.3/agda/source/Quotient/Large-Variation.agdai  _build/2.6.3/agda/source/Quotient/Effectivity.agdai
	agda --safe source/Quotient/index.lagda
	touch $@

_build/2.6.3/agda/source/Rationals/Extension.agdai: source/Rationals/Extension.lagda _build/2.6.3/agda/source/DedekindReals/Order.agdai
	agda --safe source/Rationals/Extension.lagda
	touch $@

_build/2.6.3/agda/source/Rationals/index.agdai: source/Rationals/index.lagda _build/2.6.3/agda/source/Rationals/Limits.agdai  _build/2.6.3/agda/source/Rationals/Extension.agdai
	agda --safe source/Rationals/index.lagda
	touch $@

_build/2.6.3/agda/source/Relations/index.agdai: source/Relations/index.lagda _build/2.6.3/agda/source/Relations/ChurchRosser.agdai
	agda --safe source/Relations/index.lagda
	touch $@

_build/2.6.3/agda/source/Slice/IdentityViaSIP.agdai: source/Slice/IdentityViaSIP.lagda _build/2.6.3/agda/source/Slice/Slice.agdai  _build/2.6.3/agda/source/UF/StructureIdentityPrinciple.agdai
	agda --safe source/Slice/IdentityViaSIP.lagda
	touch $@

_build/2.6.3/agda/source/Slice/Monad.agdai: source/Slice/Monad.lagda _build/2.6.3/agda/source/Slice/IdentityViaSIP.agdai
	agda --safe source/Slice/Monad.lagda
	touch $@

_build/2.6.3/agda/source/Slice/Algebras.agdai: source/Slice/Algebras.lagda _build/2.6.3/agda/source/Slice/Monad.agdai
	agda --safe source/Slice/Algebras.lagda
	touch $@

_build/2.6.3/agda/source/Slice/Embedding.agdai: source/Slice/Embedding.lagda _build/2.6.3/agda/source/Slice/IdentityViaSIP.agdai
	agda --safe source/Slice/Embedding.lagda
	touch $@

_build/2.6.3/agda/source/Slice/index.agdai: source/Slice/index.lagda _build/2.6.3/agda/source/Slice/Family.agdai  _build/2.6.3/agda/source/Slice/Algebras.agdai  _build/2.6.3/agda/source/Slice/Embedding.agdai
	agda --safe source/Slice/index.lagda
	touch $@

_build/2.6.3/agda/source/TWA/BanachFixedPointTheorem.agdai: source/TWA/BanachFixedPointTheorem.lagda _build/2.6.3/agda/source/TWA/Closeness.agdai
	agda --safe source/TWA/BanachFixedPointTheorem.lagda
	touch $@

_build/2.6.3/agda/source/TWA/Escardo-Simpson-LICS2001.agdai: source/TWA/Escardo-Simpson-LICS2001.lagda _build/2.6.3/agda/source/Naturals/Sequence.agdai  _build/2.6.3/agda/source/UF/Sets.agdai
	agda --safe source/TWA/Escardo-Simpson-LICS2001.lagda
	touch $@

_build/2.6.3/agda/source/TWA/SIP-IntervalObject.agdai: source/TWA/SIP-IntervalObject.lagda _build/2.6.3/agda/source/UF/SIP-Examples.agdai  _build/2.6.3/agda/source/TWA/Escardo-Simpson-LICS2001.agdai
	agda --safe source/TWA/SIP-IntervalObject.lagda
	touch $@

_build/2.6.3/agda/source/TWA/index.agdai: source/TWA/index.lagda _build/2.6.3/agda/source/TWA/BanachFixedPointTheorem.agdai  _build/2.6.3/agda/source/TWA/SIP-IntervalObject.agdai
	agda --safe source/TWA/index.lagda
	touch $@

_build/2.6.3/agda/source/Taboos/P2.agdai: source/Taboos/P2.lagda _build/2.6.3/agda/source/UF/ExcludedMiddle.agdai
	agda --safe source/Taboos/P2.lagda
	touch $@

_build/2.6.3/agda/source/Taboos/index.agdai: source/Taboos/index.lagda _build/2.6.3/agda/source/Taboos/Decomposability.agdai  _build/2.6.3/agda/source/Taboos/P2.agdai  _build/2.6.3/agda/source/Taboos/LPO.agdai  _build/2.6.3/agda/source/Taboos/BasicDiscontinuity.agdai
	agda --safe source/Taboos/index.lagda
	touch $@

_build/2.6.3/agda/source/UF/Classifiers-Old.agdai: source/UF/Classifiers-Old.lagda _build/2.6.3/agda/source/UF/ImageAndSurjection.agdai
	agda --safe source/UF/Classifiers-Old.lagda
	touch $@

_build/2.6.3/agda/source/UF/FunExt-from-Naive-FunExt.agdai: source/UF/FunExt-from-Naive-FunExt.lagda _build/2.6.3/agda/source/UF/Yoneda.agdai
	agda --safe source/UF/FunExt-from-Naive-FunExt.lagda
	touch $@

_build/2.6.3/agda/source/UF/Groupoids.agdai: source/UF/Groupoids.lagda _build/2.6.3/agda/source/UF/HLevels.agdai  _build/2.6.3/agda/source/UF/Sets-Properties.agdai
	agda --safe source/UF/Groupoids.lagda
	touch $@

_build/2.6.3/agda/source/UF/HiddenSwap.agdai: source/UF/HiddenSwap.lagda _build/2.6.3/agda/source/UF/DiscreteAndSeparated.agdai
	agda --safe source/UF/HiddenSwap.lagda
	touch $@

_build/2.6.3/agda/source/UF/Knapp-UA.agdai: source/UF/Knapp-UA.lagda _build/2.6.3/agda/source/UF/FunExt-Properties.agdai
	agda --safe source/UF/Knapp-UA.lagda
	touch $@

_build/2.6.3/agda/source/UF/SemistrictIdentity.agdai: source/UF/SemistrictIdentity.lagda _build/2.6.3/agda/source/UF/IdentitySystems.agdai
	agda --safe source/UF/SemistrictIdentity.lagda
	touch $@

_build/2.6.3/agda/source/UF/SetTrunc.agdai: source/UF/SetTrunc.lagda _build/2.6.3/agda/source/UF/Sets.agdai
	agda --safe source/UF/SetTrunc.lagda
	touch $@

_build/2.6.3/agda/source/UF/index.agdai: source/UF/index.lagda _build/2.6.3/agda/source/UF/FunExt-from-Naive-FunExt.agdai  _build/2.6.3/agda/source/UF/Classifiers-Old.agdai  _build/2.6.3/agda/source/UF/HiddenSwap.agdai  _build/2.6.3/agda/source/UF/Choice.agdai  _build/2.6.3/agda/source/UF/SmallnessProperties.agdai  _build/2.6.3/agda/source/UF/Powerset-Resizing.agdai  _build/2.6.3/agda/source/UF/SIP-Examples.agdai  _build/2.6.3/agda/source/UF/Powerset-Fin.agdai  _build/2.6.3/agda/source/UF/PreSIP-Examples.agdai  _build/2.6.3/agda/source/UF/Connected.agdai  _build/2.6.3/agda/source/UF/ImageAndSurjection-Variation.agdai  _build/2.6.3/agda/source/UF/Groupoids.agdai  _build/2.6.3/agda/source/UF/CumulativeHierarchy-LocallySmall.agdai  _build/2.6.3/agda/source/UF/SemistrictIdentity.agdai  _build/2.6.3/agda/source/UF/Retracts-FunExt.agdai  _build/2.6.3/agda/source/UF/SetTrunc.agdai  _build/2.6.3/agda/source/UF/Knapp-UA.agdai
	agda --safe source/UF/index.lagda
	touch $@

_build/2.6.3/agda/source/Various/LawvereFPT.agdai: source/Various/LawvereFPT.lagda _build/2.6.3/agda/source/UF/ImageAndSurjection.agdai  _build/2.6.3/agda/source/W/Properties.agdai  _build/2.6.3/agda/source/UF/DiscreteAndSeparated.agdai
	agda --safe source/Various/LawvereFPT.lagda
	touch $@

_build/2.6.3/agda/source/Various/CantorTheoremForEmbeddings.agdai: source/Various/CantorTheoremForEmbeddings.lagda _build/2.6.3/agda/source/UF/Size.agdai  _build/2.6.3/agda/source/Various/LawvereFPT.agdai
	agda --safe source/Various/CantorTheoremForEmbeddings.lagda
	touch $@

_build/2.6.3/agda/source/Various/Dedekind.agdai: source/Various/Dedekind.lagda _build/2.6.3/agda/source/TypeTopology/CompactTypes.agdai  _build/2.6.3/agda/source/CoNaturals/GenericConvergentSequence.agdai  _build/2.6.3/agda/source/UF/Powerset.agdai
	agda --safe source/Various/Dedekind.lagda
	touch $@

_build/2.6.3/agda/source/Various/DummettDisjunction.agdai: source/Various/DummettDisjunction.lagda _build/2.6.3/agda/source/MLTT/Spartan.agdai
	agda --safe source/Various/DummettDisjunction.lagda
	touch $@

_build/2.6.3/agda/source/Various/Lumsdaine.agdai: source/Various/Lumsdaine.lagda _build/2.6.3/agda/source/MLTT/Universes.agdai
	agda --safe source/Various/Lumsdaine.lagda
	touch $@

_build/2.6.3/agda/source/Various/NonCollapsibleFamily.agdai: source/Various/NonCollapsibleFamily.lagda _build/2.6.3/agda/source/UF/KrausLemma.agdai  _build/2.6.3/agda/source/UF/DiscreteAndSeparated.agdai
	agda --safe source/Various/NonCollapsibleFamily.lagda
	touch $@

_build/2.6.3/agda/source/Various/RootsOfBooleanFunctions.agdai: source/Various/RootsOfBooleanFunctions.lagda _build/2.6.3/agda/source/TypeTopology/InfProperty.agdai
	agda --safe source/Various/RootsOfBooleanFunctions.lagda
	touch $@

_build/2.6.3/agda/source/Various/UnivalenceFromScratch.agdai: source/Various/UnivalenceFromScratch.lagda _build/2.6.3/agda/source/Agda/Primitive.agdai
	agda --safe source/Various/UnivalenceFromScratch.lagda
	touch $@

_build/2.6.3/agda/source/Various/index.agdai: source/Various/index.lagda _build/2.6.3/agda/source/Various/CantorTheoremForEmbeddings.agdai  _build/2.6.3/agda/source/Various/Dedekind.agdai  _build/2.6.3/agda/source/Various/DummettDisjunction.agdai  _build/2.6.3/agda/source/Various/NonCollapsibleFamily.agdai  _build/2.6.3/agda/source/Various/RootsOfBooleanFunctions.agdai  _build/2.6.3/agda/source/Various/UnivalenceFromScratch.agdai  _build/2.6.3/agda/source/Various/HiggsInvolutionTheorem.agdai  _build/2.6.3/agda/source/Various/Lumsdaine.agdai
	agda --safe source/Various/index.lagda
	touch $@

_build/2.6.3/agda/source/W/Numbers.agdai: source/W/Numbers.lagda _build/2.6.3/agda/source/UF/SubtypeClassifier-Properties.agdai  _build/2.6.3/agda/source/UF/ExcludedMiddle.agdai  _build/2.6.3/agda/source/Fin/Type.agdai  _build/2.6.3/agda/source/W/Properties.agdai
	agda --safe source/W/Numbers.lagda
	touch $@

_build/2.6.3/agda/source/W/Paths.agdai: source/W/Paths.lagda _build/2.6.3/agda/source/W/Numbers.agdai  _build/2.6.3/agda/source/UF/Logic.agdai
	agda --safe source/W/Paths.lagda
	touch $@

_build/2.6.3/agda/source/W/index.agdai: source/W/index.lagda _build/2.6.3/agda/source/W/Paths.agdai
	agda --safe source/W/index.lagda
	touch $@

_build/2.6.3/agda/source/index.agdai: source/index.lagda _build/2.6.3/agda/source/Categories/index.agdai  _build/2.6.3/agda/source/Taboos/index.agdai  _build/2.6.3/agda/source/Locales/index.agdai  _build/2.6.3/agda/source/Dyadics/index.agdai  _build/2.6.3/agda/source/Fin/index.agdai  _build/2.6.3/agda/source/Quotient/index.agdai  _build/2.6.3/agda/source/Field/index.agdai  _build/2.6.3/agda/source/Slice/index.agdai  _build/2.6.3/agda/source/Duploids/index.agdai  _build/2.6.3/agda/source/PCF/index.agdai  _build/2.6.3/agda/source/Iterative/index.agdai  _build/2.6.3/agda/source/MLTT/index.agdai  _build/2.6.3/agda/source/Relations/index.agdai  _build/2.6.3/agda/source/InjectiveTypes/index.agdai  _build/2.6.3/agda/source/TWA/index.agdai  _build/2.6.3/agda/source/Games/index.agdai  _build/2.6.3/agda/source/Lifting/index.agdai  _build/2.6.3/agda/source/Coslice/index.agdai  _build/2.6.3/agda/source/ContinuityAxiom/index.agdai  _build/2.6.3/agda/source/Naturals/index.agdai  _build/2.6.3/agda/source/EffectfulForcing/index.agdai  _build/2.6.3/agda/source/W/index.agdai  _build/2.6.3/agda/source/Rationals/index.agdai  _build/2.6.3/agda/source/Factorial/index.agdai  _build/2.6.3/agda/source/MGS/index.agdai  _build/2.6.3/agda/source/Circle/index.agdai  _build/2.6.3/agda/source/DedekindReals/index.agdai  _build/2.6.3/agda/source/Notation/index.agdai  _build/2.6.3/agda/source/Groups/index.agdai  _build/2.6.3/agda/source/MetricSpaces/index.agdai  _build/2.6.3/agda/source/BinarySystems/index.agdai  _build/2.6.3/agda/source/Modal/index.agdai  _build/2.6.3/agda/source/Dominance/index.agdai  _build/2.6.3/agda/source/Integers/index.agdai  _build/2.6.3/agda/source/CoNaturals/index.agdai  _build/2.6.3/agda/source/Various/index.agdai  _build/2.6.3/agda/source/CantorSchroederBernstein/index.agdai  _build/2.6.3/agda/source/DomainTheory/index.agdai  _build/2.6.3/agda/source/UF/index.agdai  _build/2.6.3/agda/source/Posets/index.agdai  _build/2.6.3/agda/source/DyadicsInductive/index.agdai  _build/2.6.3/agda/source/NotionsOfDecidability/index.agdai  _build/2.6.3/agda/source/CrossedModules/index.agdai
	agda --safe source/index.lagda
	touch $@
