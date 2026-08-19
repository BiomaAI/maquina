import Maquina.Simulator

/-!
# Maquina Multi-Machine Worlds

One authoritative resource world shared by uniquely identified machine
runtimes. Targeted operations reuse the single-machine interpreter, then lift
its checked successor back into the world while proving unrelated machines
were not mutated.
-/

namespace Maquina

/-- Stable identity of one machine inside an authoritative world. -/
structure MachineId where
  value : Nat
  deriving DecidableEq, Repr

/-- Computational machine-local state, excluding the shared authoritative world. -/
structure MachineRuntimeData
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  mode : language.Mode
  machine : Machine schema
  custody : MachineCustody machine.inventory
  nextProcessId : Nat

/-- One machine runtime whose custody invariants are indexed by the shared world. -/
structure WorldMachine
    (resourceCatalog : ResourceCatalog)
    (schema : MachineSchema)
    (language : OperationLanguage schema)
    (world : WorldState resourceCatalog) where
  id : MachineId
  mode : language.Mode
  machine : Machine schema
  custody : MachineCustody machine.inventory
  custodyBacked : MachineCustody.Backed world custody
  activeCustodyHeld : machine.ActiveDependenciesSatisfy
    (ActiveCustodyDependency.HeldBy custody)
  nextProcessId : Nat

namespace WorldMachine

def inventory
    (machine : WorldMachine resourceCatalog schema language world) : AccountId :=
  machine.machine.inventory

def runtimeData
    (machine : WorldMachine resourceCatalog schema language world) :
    MachineRuntimeData schema language where
  mode := machine.mode
  machine := machine.machine
  custody := machine.custody
  nextProcessId := machine.nextProcessId

def toSimulatorState
    (machine : WorldMachine resourceCatalog schema language world) :
    SimulatorState resourceCatalog schema language where
  world := world
  mode := machine.mode
  machine := machine.machine
  custody := machine.custody
  custodyBacked := machine.custodyBacked
  activeCustodyHeld := machine.activeCustodyHeld
  nextProcessId := machine.nextProcessId

def ofSimulatorState
    (id : MachineId)
    (state : SimulatorState resourceCatalog schema language) :
    WorldMachine resourceCatalog schema language state.world where
  id := id
  mode := state.mode
  machine := state.machine
  custody := state.custody
  custodyBacked := state.custodyBacked
  activeCustodyHeld := state.activeCustodyHeld
  nextProcessId := state.nextProcessId

@[simp]
theorem ofSimulatorState_runtimeData
    (id : MachineId)
    (state : SimulatorState resourceCatalog schema language) :
    (ofSimulatorState id state).runtimeData =
      { mode := state.mode
        machine := state.machine
        custody := state.custody
        nextProcessId := state.nextProcessId } := rfl

end WorldMachine

/--
The authoritative multi-machine state. Machine identities and inventory
accounts are unique, so a concrete inventory belongs to exactly one machine.
-/
structure MultiMachineState
    (resourceCatalog : ResourceCatalog)
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  world : WorldState resourceCatalog
  machines : List (WorldMachine resourceCatalog schema language world)
  machineIdsUnique : (machines.map WorldMachine.id).Nodup
  machineInventoriesUnique : (machines.map WorldMachine.inventory).Nodup

namespace MultiMachineState

private def findMachineIn?
    {world : WorldState resourceCatalog}
    (id : MachineId) :
    List (WorldMachine resourceCatalog schema language world) →
      Option (WorldMachine resourceCatalog schema language world)
  | [] => none
  | machine :: rest =>
      if machine.id = id then some machine else findMachineIn? id rest

def machine?
    (state : MultiMachineState resourceCatalog schema language)
    (id : MachineId) :
    Option (WorldMachine resourceCatalog schema language state.world) :=
  findMachineIn? id state.machines

private def runtimeDataIn?
    {world : WorldState resourceCatalog}
    (id : MachineId) :
    List (WorldMachine resourceCatalog schema language world) →
      Option (MachineRuntimeData schema language)
  | [] => none
  | machine :: rest =>
      if machine.id = id then some machine.runtimeData else runtimeDataIn? id rest

def machineRuntimeData?
    (state : MultiMachineState resourceCatalog schema language)
    (id : MachineId) : Option (MachineRuntimeData schema language) :=
  runtimeDataIn? id state.machines

theorem machineIds_unique
    (state : MultiMachineState resourceCatalog schema language) :
    (state.machines.map WorldMachine.id).Nodup :=
  state.machineIdsUnique

end MultiMachineState

namespace WorldEffectReceipt

/-- Whether a receipt changes any balance owned by one account. -/
def touchesAccount : WorldEffectReceipt → AccountId → Bool
  | .transfer receipt, account =>
      decide (receipt.source = account ∨ receipt.destination = account)
  | .transformation receipt, account =>
      decide (receipt.delta.account = account)

end WorldEffectReceipt

/-- A finite receipt list leaves an account untouched exactly when every item does. -/
def worldEffectsLeaveAccountUntouched
    (receipts : List WorldEffectReceipt)
    (account : AccountId) : Bool :=
  receipts.all fun receipt => !receipt.touchesAccount account

/-- Receipt replay preserves every balance of an account no receipt touches. -/
theorem replayWorldEffectReceipts_balance_untouched
    (receipts : List WorldEffectReceipt)
    (holdings : List (Holding AccountId))
    (account : AccountId)
    (resourceId : ResourceId)
    (untouched : ∀ receipt ∈ receipts,
      receipt.touchesAccount account = false) :
    balanceAtoms (replayWorldEffectReceipts receipts holdings)
        account resourceId =
      balanceAtoms holdings account resourceId := by
  induction receipts generalizing holdings with
  | nil => rfl
  | cons receipt rest ih =>
      cases receipt with
      | transfer moved =>
          change
            balanceAtoms
                (replayWorldEffectReceipts rest (replayReceipt moved holdings))
                account resourceId =
              balanceAtoms holdings account resourceId
          rw [ih]
          · change
              balanceAtoms
                  (transferEntriesHoldings moved.source moved.destination
                    (moved.lines.map TransferReceiptLine.toEntry) holdings)
                  account resourceId =
                balanceAtoms holdings account resourceId
            have notTouched :
                ¬(moved.source = account ∨ moved.destination = account) := by
              simpa only [WorldEffectReceipt.touchesAccount,
                decide_eq_false_iff_not] using
                untouched (.transfer moved) (by simp)
            exact transferEntriesHoldings_otherAccount
              moved.source moved.destination
              (moved.lines.map TransferReceiptLine.toEntry)
              holdings account resourceId
              (fun same => notTouched (Or.inl same))
              (fun same => notTouched (Or.inr same))
          · intro queried queriedMem
            exact untouched queried (by simp [queriedMem])
      | transformation changed =>
          change
            balanceAtoms
                (replayWorldEffectReceipts rest
                  (replayInventoryDeltaReceipt changed holdings))
                account resourceId =
              balanceAtoms holdings account resourceId
          rw [ih]
          · cases deltaEq : changed.delta with
            | debit target entry | credit target entry =>
                simp only [replayInventoryDeltaReceipt,
                  inventoryDeltaHoldings, deltaEq]
                apply balanceAtoms_setBalance_other
                have notTouched : target ≠ account := by
                  simpa only [WorldEffectReceipt.touchesAccount, deltaEq,
                    InventoryDelta.account, decide_eq_false_iff_not] using
                    untouched (.transformation changed) (by simp)
                exact Or.inl notTouched
          · intro queried queriedMem
            exact untouched queried (by simp [queriedMem])

/-- An operation proposal explicitly addressed to one machine identity. -/
structure TargetedOperationProposal
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  target : MachineId
  operation : OperationProposal schema language

/-- Structured rejection at the shared-world boundary. -/
inductive MultiMachineIssue where
  | machineMissing (target : MachineId)
  | operationRejected (target : MachineId) (issues : List SimulatorIssue)
  | unrelatedMachineTouched (machine : MachineId) (inventory : AccountId)
  | targetInventoryChanged
      (machine : MachineId) (before after : AccountId)
  | machineInventoryConflict
  deriving DecidableEq, Repr

private structure RetargetedMachines
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    {beforeWorld afterWorld : WorldState resourceCatalog}
    (target : MachineId)
    (before : List (WorldMachine resourceCatalog schema language beforeWorld)) where
  machines : List (WorldMachine resourceCatalog schema language afterWorld)
  idsExact : machines.map WorldMachine.id = before.map WorldMachine.id
  unrelatedRuntimeExact : ∀ id, id ≠ target →
    MultiMachineState.runtimeDataIn? id machines =
      MultiMachineState.runtimeDataIn? id before

private def retargetMachines
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    {beforeWorld afterWorld : WorldState resourceCatalog}
    (target : MachineId)
    (targetAfter : WorldMachine resourceCatalog schema language afterWorld)
    (targetIdExact : targetAfter.id = target)
    (worldEffects : List WorldEffectReceipt)
    (worldReplayExact :
      replayWorldEffectReceipts worldEffects beforeWorld.holdings =
        afterWorld.holdings) :
    (machines : List (WorldMachine resourceCatalog schema language beforeWorld)) →
      Except MultiMachineIssue
        (RetargetedMachines (afterWorld := afterWorld) target machines)
  | [] =>
      .ok
        { machines := []
          idsExact := rfl
          unrelatedRuntimeExact := by simp [MultiMachineState.runtimeDataIn?] }
  | current :: rest =>
      if currentTarget : current.id = target then
        match retargetMachines target targetAfter targetIdExact
            worldEffects worldReplayExact rest with
        | .error issue => .error issue
        | .ok updated =>
            .ok
              { machines := targetAfter :: updated.machines
                idsExact := by
                  simp only [List.map_cons]
                  rw [updated.idsExact, currentTarget, targetIdExact]
                unrelatedRuntimeExact := by
                  intro id different
                  simp only [MultiMachineState.runtimeDataIn?]
                  have targetDifferent : target ≠ id := Ne.symm different
                  simp [targetIdExact, currentTarget, targetDifferent,
                    updated.unrelatedRuntimeExact id different] }
      else
        if isolated :
            worldEffectsLeaveAccountUntouched worldEffects current.inventory = true then
          match retargetMachines target targetAfter targetIdExact
              worldEffects worldReplayExact rest with
          | .error issue => .error issue
          | .ok updated =>
              let preserved :
                  WorldMachine resourceCatalog schema language afterWorld :=
                { id := current.id
                  mode := current.mode
                  machine := current.machine
                  custody := current.custody
                  custodyBacked := by
                    intro resourceId
                    change current.custody.lockedAtoms resourceId ≤
                      (afterWorld.balance current.inventory resourceId).atoms
                    have everyUntouched : ∀ receipt ∈ worldEffects,
                        receipt.touchesAccount current.inventory = false := by
                      intro receipt receiptMem
                      have checked :=
                        (List.all_eq_true.mp isolated) receipt receiptMem
                      simpa [worldEffectsLeaveAccountUntouched] using checked
                    have balanceExact :
                        (afterWorld.balance current.inventory resourceId).atoms =
                          (beforeWorld.balance current.inventory resourceId).atoms := by
                      change balanceAtoms afterWorld.holdings current.inventory
                          resourceId =
                        balanceAtoms beforeWorld.holdings current.inventory resourceId
                      rw [← worldReplayExact]
                      exact replayWorldEffectReceipts_balance_untouched
                        worldEffects beforeWorld.holdings current.inventory
                        resourceId everyUntouched
                    rw [balanceExact]
                    change current.custody.lockedAtoms resourceId ≤
                      (beforeWorld.balance current.inventory resourceId).atoms
                    exact current.custodyBacked resourceId
                  activeCustodyHeld := current.activeCustodyHeld
                  nextProcessId := current.nextProcessId }
              .ok
                { machines := preserved :: updated.machines
                  idsExact := by
                    simp only [List.map_cons]
                    rw [updated.idsExact]
                  unrelatedRuntimeExact := by
                    intro id different
                    simp only [MultiMachineState.runtimeDataIn?]
                    have preservedData :
                        preserved.runtimeData = current.runtimeData := rfl
                    have preservedId : preserved.id = current.id := rfl
                    by_cases same : current.id = id
                    · rw [if_pos (preservedId.trans same), if_pos same]
                      exact congrArg some preservedData
                    · simp [preserved, same,
                        updated.unrelatedRuntimeExact id different] }
        else
          .error (.unrelatedMachineTouched current.id current.inventory)

/-- Proof-carrying application of one targeted operation to the shared world. -/
structure AppliedWorldOperation
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (before : MultiMachineState resourceCatalog schema language)
    (proposal : TargetedOperationProposal schema language) where
  after : MultiMachineState resourceCatalog schema language
  receipt : OperationReceipt schema language
  worldEffects : List WorldEffectReceipt
  worldReplayExact :
    replayWorldEffectReceipts worldEffects before.world.holdings =
      after.world.holdings
  machineIdsExact :
    after.machines.map WorldMachine.id = before.machines.map WorldMachine.id
  unrelatedMachinesExact : ∀ id, id ≠ proposal.target →
    after.machineRuntimeData? id = before.machineRuntimeData? id

/-- Apply one operation atomically to its addressed machine and the shared world. -/
def applyWorldOperation
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : MultiMachineState resourceCatalog schema language)
    (proposal : TargetedOperationProposal schema language) :
    Except (List MultiMachineIssue) (AppliedWorldOperation before proposal) :=
  match targetFound : before.machine? proposal.target with
  | none => .error [.machineMissing proposal.target]
  | some targetBefore =>
      match applyOperation evaluateGuard targetBefore.toSimulatorState
          proposal.operation with
      | .error issues => .error [.operationRejected proposal.target issues]
      | .ok applied =>
          let targetAfter := WorldMachine.ofSimulatorState proposal.target applied.after
          if inventoryExact : targetAfter.inventory = targetBefore.inventory then
            match retargetMachines proposal.target targetAfter rfl
                applied.worldEffects applied.worldReplayExact before.machines with
            | .error issue => .error [issue]
            | .ok updated =>
                if inventoriesUnique :
                    (updated.machines.map WorldMachine.inventory).Nodup then
                  let after : MultiMachineState resourceCatalog schema language :=
                    { world := applied.after.world
                      machines := updated.machines
                      machineIdsUnique := by
                        rw [updated.idsExact]
                        exact before.machineIdsUnique
                      machineInventoriesUnique := inventoriesUnique }
                  .ok
                    { after
                      receipt := applied.receipt
                      worldEffects := applied.worldEffects
                      worldReplayExact := applied.worldReplayExact
                      machineIdsExact := updated.idsExact
                      unrelatedMachinesExact := updated.unrelatedRuntimeExact }
                else
                  .error [.machineInventoryConflict]
          else
            .error [.targetInventoryChanged proposal.target
              targetBefore.inventory targetAfter.inventory]

def worldOperationSuccessor
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : MultiMachineState resourceCatalog schema language)
    (proposal : TargetedOperationProposal schema language) :
    Option (MultiMachineState resourceCatalog schema language) :=
  match applyWorldOperation evaluateGuard before proposal with
  | .error _ => none
  | .ok applied => some applied.after

/-- Every shared-world rejection exposes no successor. -/
theorem worldOperationSuccessor_rejected
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : MultiMachineState resourceCatalog schema language)
    (proposal : TargetedOperationProposal schema language)
    (issues : List MultiMachineIssue)
    (rejected : applyWorldOperation evaluateGuard before proposal = .error issues) :
    worldOperationSuccessor evaluateGuard before proposal = none := by
  simp [worldOperationSuccessor, rejected]

/-- A missing target is rejected structurally before local assessment. -/
theorem applyWorldOperation_machineMissing
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : MultiMachineState resourceCatalog schema language)
    (proposal : TargetedOperationProposal schema language)
    (missing : before.machine? proposal.target = none) :
    applyWorldOperation evaluateGuard before proposal =
      .error [.machineMissing proposal.target] := by
  unfold applyWorldOperation
  rw [missing]

/-- Successful targeted application preserves every unrelated machine runtime. -/
theorem AppliedWorldOperation.unrelatedMachine_unchanged
    {before : MultiMachineState resourceCatalog schema language}
    {proposal : TargetedOperationProposal schema language}
    (applied : AppliedWorldOperation before proposal)
    (id : MachineId)
    (different : id ≠ proposal.target) :
    applied.after.machineRuntimeData? id = before.machineRuntimeData? id :=
  applied.unrelatedMachinesExact id different

/-! ## Ordered, all-or-none world transactions -/

/-- One committed operation receipt retains the machine it explicitly targeted. -/
structure TargetedOperationReceipt
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  target : MachineId
  receipt : OperationReceipt schema language

/--
A transaction is an inert, explicitly ordered batch of world intents. Logical
time and scheduler policy are deliberately not part of this layer.
-/
structure WorldTransaction
    (schema : MachineSchema)
    (language : OperationLanguage schema) where
  intents : List (TargetedOperationProposal schema language)

/-- The exact intent index and target that prevented atomic commitment. -/
inductive WorldTransactionIssue where
  | intentRejected
      (intentIndex : Nat)
      (target : MachineId)
      (issues : List MultiMachineIssue)
  deriving DecidableEq, Repr

/-- Proof-carrying result of applying an ordered intent list atomically. -/
structure AppliedWorldTransactionRun
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (before : MultiMachineState resourceCatalog schema language)
    (intents : List (TargetedOperationProposal schema language)) where
  after : MultiMachineState resourceCatalog schema language
  receipts : List (TargetedOperationReceipt schema language)
  receiptTargetsExact :
    receipts.map TargetedOperationReceipt.target =
      intents.map TargetedOperationProposal.target
  worldEffects : List WorldEffectReceipt
  worldReplayExact :
    replayWorldEffectReceipts worldEffects before.world.holdings =
      after.world.holdings

private def applyWorldIntents
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language) :
    (intentIndex : Nat) →
    (before : MultiMachineState resourceCatalog schema language) →
    (intents : List (TargetedOperationProposal schema language)) →
      Except (List WorldTransactionIssue)
        (AppliedWorldTransactionRun before intents)
  | _, before, [] =>
      .ok
        { after := before
          receipts := []
          receiptTargetsExact := rfl
          worldEffects := []
          worldReplayExact := rfl }
  | intentIndex, before, intent :: rest =>
      match applyWorldOperation evaluateGuard before intent with
      | .error issues =>
          .error [.intentRejected intentIndex intent.target issues]
      | .ok applied =>
          match applyWorldIntents evaluateGuard (intentIndex + 1)
              applied.after rest with
          | .error issues => .error issues
          | .ok suffix =>
              .ok
                { after := suffix.after
                  receipts :=
                    { target := intent.target
                      receipt := applied.receipt } :: suffix.receipts
                  receiptTargetsExact := by
                    simp only [List.map_cons]
                    rw [suffix.receiptTargetsExact]
                  worldEffects := applied.worldEffects ++ suffix.worldEffects
                  worldReplayExact := by
                    rw [replayWorldEffectReceipts_append,
                      applied.worldReplayExact]
                    exact suffix.worldReplayExact }

abbrev AppliedWorldTransaction
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (before : MultiMachineState resourceCatalog schema language)
    (transaction : WorldTransaction schema language) :=
  AppliedWorldTransactionRun before transaction.intents

/-- Ordered transaction assessment and all-or-none application. -/
def applyWorldTransaction
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : MultiMachineState resourceCatalog schema language)
    (transaction : WorldTransaction schema language) :
    Except (List WorldTransactionIssue)
      (AppliedWorldTransaction before transaction) :=
  applyWorldIntents evaluateGuard 0 before transaction.intents

def worldTransactionSuccessor
    {resourceCatalog : ResourceCatalog}
    {schema : MachineSchema}
    {language : OperationLanguage schema}
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : MultiMachineState resourceCatalog schema language)
    (transaction : WorldTransaction schema language) :
    Option (MultiMachineState resourceCatalog schema language) :=
  match applyWorldTransaction evaluateGuard before transaction with
  | .error _ => none
  | .ok applied => some applied.after

/-- A failed intent discards every locally computed transaction prefix. -/
theorem worldTransactionSuccessor_rejected
    (evaluateGuard : GuardEvaluator resourceCatalog schema language)
    (before : MultiMachineState resourceCatalog schema language)
    (transaction : WorldTransaction schema language)
    (issues : List WorldTransactionIssue)
    (rejected :
      applyWorldTransaction evaluateGuard before transaction = .error issues) :
    worldTransactionSuccessor evaluateGuard before transaction = none := by
  simp [worldTransactionSuccessor, rejected]

private theorem nodupMap_ne_of_mem
    {Item Value : Type}
    (valueOf : Item → Value)
    {items : List Item}
    (unique : (items.map valueOf).Nodup)
    {left right : Item}
    (leftMem : left ∈ items)
    (rightMem : right ∈ items)
    (different : left ≠ right) :
    valueOf left ≠ valueOf right := by
  induction items with
  | nil => simp at leftMem
  | cons current rest ih =>
      have uniqueParts := List.nodup_cons.mp unique
      simp only [List.mem_cons] at leftMem rightMem
      rcases leftMem with leftHead | leftRest
      · subst left
        rcases rightMem with rightHead | rightRest
        · subst right
          exact False.elim (different rfl)
        · intro sameValue
          apply uniqueParts.1
          rw [sameValue]
          exact List.mem_map.mpr ⟨right, rightRest, rfl⟩
      · rcases rightMem with rightHead | rightRest
        · subst right
          intro sameValue
          apply uniqueParts.1
          rw [← sameValue]
          exact List.mem_map.mpr ⟨left, leftRest, rfl⟩
        · exact ih uniqueParts.2 leftRest rightRest

/-- Distinct machine identities own distinct authoritative inventory accounts. -/
theorem MultiMachineState.machineInventories_distinct
    (state : MultiMachineState resourceCatalog schema language)
    {left right : WorldMachine resourceCatalog schema language state.world}
    (leftMem : left ∈ state.machines)
    (rightMem : right ∈ state.machines)
    (different : left.id ≠ right.id) :
    left.inventory ≠ right.inventory :=
  nodupMap_ne_of_mem WorldMachine.inventory
    state.machineInventoriesUnique leftMem rightMem fun sameMachine =>
      different (congrArg WorldMachine.id sameMachine)

/-- A unique resource cannot simultaneously occupy two distinct machines. -/
theorem MultiMachineState.uniqueResource_not_held_by_distinctMachines
    (state : MultiMachineState resourceCatalog schema language)
    (header : ResourceHeader)
    (found :
      resourceCatalog.lookup header.id = some (ResourceSpec.unique header))
    (left right : WorldMachine resourceCatalog schema language state.world)
    (leftMem : left ∈ state.machines)
    (rightMem : right ∈ state.machines)
    (different : left.id ≠ right.id)
    (leftHeld : (state.world.balance left.inventory header.id).atoms = 1)
    (rightHeld : (state.world.balance right.inventory header.id).atoms = 1) :
    False :=
  state.world.unique_not_held_by_distinct_accounts header found
    left.inventory right.inventory
    (state.machineInventories_distinct leftMem rightMem different)
    leftHeld rightHeld

end Maquina
