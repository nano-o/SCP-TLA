This repository contains three specifications of the nomination protocol (a sub-protocol of the Stellar Consensus Protocol).

[`Nomination.tla`](Nomination.tla) is written in TLA+ and set up to check the main liveness properties of the protocol with the TLC model-checker.
This is best viewed or edited with the [TLA Toolbox](https://github.com/tlaplus/tlaplus/releases/latest/) or the [TLA+ extension for VS Code](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus).

[`NominationPlusCal.tla`](NominationPlusCal.tla) is written in the PlusCal Algorithm Language, which transpiles to TLA+ (the transpiled code appears between the `\* BEGIN TRANSLATION` and `\* END TRANSLATION` markers).
Best viewed or edited with the [TLA Toolbox](https://github.com/tlaplus/tlaplus/releases/latest/).

[`Nomination.qnt`](Nomination.qnt) is written in quint, a new language that also transpiles to TLA+ but also has its own tooling.
Best viewed or edited with the [quint extention for VS Code](https://marketplace.visualstudio.com/items?itemName=informal.quint-vscode) (but as of 3.31.2023 there is a bug that affects `Nomination.qnt`; in the meantime there are vim and emacs syntax configs [here](https://github.com/informalsystems/quint/tree/main/editor-plugins)).
Use the [quint REPL](https://github.com/informalsystems/quint/blob/main/tutorials/repl/repl.md) to run tests and random simulations.

