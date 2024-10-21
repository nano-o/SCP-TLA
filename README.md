This repository contains specifications related to the Stellar Consensus Protocol (SCP).

# The nomination protocol

The nomination protocol is a sub-protocol of the Stellar Consensus Protocol.

[`Nomination.tla`](Nomination.tla) is written in TLA+ and set up to check the main liveness properties of the protocol with the TLC model-checker.
This is best viewed or edited with the [TLA Toolbox](https://github.com/tlaplus/tlaplus/releases/tag/v1.7.1#latest-tla-files) or the [TLA+ extension for VS Code](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus).
[`Nomination.pdf`](Nomination.pdf) is a typeset version of the specification.

[`NominationPlusCal.tla`](NominationPlusCal.tla) is written in the PlusCal Algorithm Language, which transpiles to TLA+ (the transpiled code appears between the `\* BEGIN TRANSLATION` and `\* END TRANSLATION` markers).
Best viewed or edited with the [TLA Toolbox](https://github.com/tlaplus/tlaplus/releases/tag/v1.7.1#latest-tla-files).
[`NominationPlusCal.pdf`](NominationPlusCal.pdf) is a typeset version of the specification.

[`Nomination.qnt`](Nomination.qnt) is written in [quint](https://github.com/informalsystems/quint), a new language that also transpiles to TLA+ but also has its own tooling.
Best viewed or edited with the [quint extention for VS Code](https://marketplace.visualstudio.com/items?itemName=informal.quint-vscode).
Use the [quint REPL](https://github.com/informalsystems/quint/blob/main/tutorials/repl/repl.md) to run tests and random simulations.
For example, on my setup I can run `npx quint -r Nomination.qnt::Test`, which loads the Test module and starts the quint REPL. Then I can run `run1` (in the REPL), which prints `true` (which means `run1` is a valid behavior of the specification). Finally I can run (again in the REPL) `stateAsRecord` to print all the variables in the state reached at the end of `run1`.

# The balloting protocol

[`AbstractBalloting.tla`](AbstractBalloting.tla) contains a high-level specification of SCP's balloting protocol in terms of logical federate-voting messages.
It will be useful to prove that the concrete balloting protocol is correct by refinement.


[`Balloting.tla`](Balloting.tla) will eventually contain a specification of the concrete balloting protocol.
For now, it is work in progress.
