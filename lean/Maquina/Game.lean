import Maquina.Genesis
import Maquina.Manifest
import Maquina.Simulator
import Maquina.Scheduler
import Maquina.Command
import Maquina.Strategic

/-!
# Maquina Game Authoring Surface

Games should import this module instead of the kernel root. Genesis is the
initial-allocation API; runtime resource changes should be declared by Processes
and invoked by typed Operations through the generic simulator. This module is a
recommended authoring surface, not a Lean visibility or security boundary.
-/
