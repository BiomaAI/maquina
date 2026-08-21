# Maquina authoring boundary

Game and composition-recipe code must use Maquina's declared execution model:

1. Declare resource changes in a `Process`.
2. Expose that process through a typed `Operation`.
3. Submit an `OperationProposal` to the generic simulator.

Do not apply account transactions, transfers, exchanges, inventory deltas, or
other world mutations directly from game or recipe code. Do not add helper
functions that reproduce those mutations outside the simulator. Import
`Maquina.Game` as the game-authoring surface; low-level modules are kernel
implementation details.

Use `GenesisPlan` and `applyGenesis` only to create initial holdings from the
canonical empty world. Genesis is not a runtime transition mechanism and must
never be used to replace or modify an existing world.
