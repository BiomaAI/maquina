# Operation Veiled Accord

Operation Veiled Accord is Maquina's imperfect-information strategy game. A
coalition commander and an opportunistic partner must move an evacuation convoy
through a contested corridor while a strategic asset creates an incentive to
defect.

The partner publicly promises to defend the corridor, but that message is cheap
talk. Command may answer with another unsupported claim, expose a unique
verified intelligence seal as a costly signal, or combine that evidence with a
two-token mutual-defense escrow. Both factions then commit their corridor orders
before either payload is revealed.

Command can cooperate by escorting the convoy or defect by attempting to seize
the asset. The same choice produces different outcomes depending on the prior
signal and agreement:

- cheap talk plus cooperation is exploited by the opportunistic partner;
- mutual defection collapses the corridor;
- verified evidence coordinates cooperation without guaranteeing it;
- evidence plus escrow supports a Pareto-improving accord;
- defection after inducing cooperation wins the asset but destroys credibility.

## What is generic Maquina semantics

- actor-safe command surfaces constructed only from declared observations;
- information sets and observation-consistent strategies;
- immutable audience-scoped messages whose payloads remain inert claims;
- commit/reveal bindings and actor-unique closed sealed rounds;
- exact multi-party consent;
- machine-independent account transactions used as escrow;
- deterministic command assessment, immutable forks, receipts, and replay.

## What remains game policy

Routes, threat truth, evidence meaning, partner nature, partner response,
mission phases, civilian outcomes, asset control, credibility, utilities, and
the interpretation of cooperation or betrayal are all defined downstream in
Veiled Accord.

Run the Lean-owned artifact with:

```sh
lake exe veiled-accord-demo
```

The Maquina Playground opens this showcase directly in Command Mode. It displays only
the commander's permitted messages and candidate surface before revealing both
sealed orders together.
