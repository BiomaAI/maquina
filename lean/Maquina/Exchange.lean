import Maquina.CustodyTransformation

/-!
# Maquina Rates and Atomic Exchanges

Rates quote exact positive lot multiples. Exchanges are ordered finite lists of
ordinary transfers applied locally: rejection publishes no successor, while a
successful result carries exact receipts, replay, and conservation evidence.
-/

namespace Maquina

structure ExchangeLeg where
  source : AccountId
  destination : AccountId
  basket : Basket
  deriving Repr

namespace ExchangeLeg

def transfer (leg : ExchangeLeg) : Transfer where
  source := leg.source
  destination := leg.destination
  basket := leg.basket

def reverse (leg : ExchangeLeg) : ExchangeLeg where
  source := leg.destination
  destination := leg.source
  basket := leg.basket

@[simp]
theorem reverse_reverse (leg : ExchangeLeg) : leg.reverse.reverse = leg := by
  cases leg
  rfl

end ExchangeLeg

structure Exchange where
  legs : List ExchangeLeg
  deriving Repr

namespace Exchange

/-- Reverse settlement order as well as every transfer direction. -/
def reverse (exchange : Exchange) : Exchange where
  legs := exchange.legs.reverse.map ExchangeLeg.reverse

@[simp]
theorem reverse_reverse (exchange : Exchange) : exchange.reverse.reverse = exchange := by
  cases exchange with
  | mk legs =>
      simp only [reverse]
      rw [← List.map_reverse, List.reverse_reverse, List.map_map]
      congr
      induction legs with
      | nil => rfl
      | cons leg rest ih => simp [Function.comp_def]

end Exchange

/-- Two canonical baskets exchanged per positive lot. -/
structure Rate where
  leftPerLot : Basket
  rightPerLot : Basket
  deriving Repr

namespace Rate

def reverse (rate : Rate) : Rate where
  leftPerLot := rate.rightPerLot
  rightPerLot := rate.leftPerLot

@[simp]
theorem reverse_reverse (rate : Rate) : rate.reverse.reverse = rate := by
  cases rate
  rfl

/-- Quote an exact two-leg exchange between the two named accounts. -/
def quote
    (rate : Rate)
    (left right : AccountId)
    (lots : Nat)
    (positive : 0 < lots) : Exchange where
  legs :=
    [{ source := left
       destination := right
       basket := rate.leftPerLot.scale lots positive },
     { source := right
       destination := left
       basket := rate.rightPerLot.scale lots positive }]

@[simp]
theorem quote_length
    (rate : Rate)
    (left right : AccountId)
    (lots : Nat)
    (positive : 0 < lots) :
    (rate.quote left right lots positive).legs.length = 2 := rfl

@[simp]
theorem quote_reverse
    (rate : Rate)
    (left right : AccountId)
    (lots : Nat)
    (positive : 0 < lots) :
    (rate.quote left right lots positive).reverse =
      rate.reverse.quote left right lots positive := by
  cases rate
  rfl

end Rate

inductive ExchangeIssue where
  | legRejected (index : Nat) (issues : List TransferIssue)
  deriving DecidableEq, Repr

def ReceiptMatchesLeg (receipt : TransferReceipt) (leg : ExchangeLeg) : Prop :=
  receipt.source = leg.source ∧
  receipt.destination = leg.destination ∧
  receipt.lines.map TransferReceiptLine.toEntry = leg.basket.entries

inductive ExchangeReceiptsExact :
    List ExchangeLeg → List TransferReceipt → Prop where
  | nil : ExchangeReceiptsExact [] []
  | cons
      (exactHead : ReceiptMatchesLeg receipt leg)
      (rest : ExchangeReceiptsExact legs receipts) :
      ExchangeReceiptsExact (leg :: legs) (receipt :: receipts)

def replayExchangeReceipts
    (receipts : List TransferReceipt)
    (holdings : List (Holding AccountId)) : List (Holding AccountId) :=
  receipts.foldl (fun current receipt => replayReceipt receipt current) holdings

structure AppliedExchange
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (legs : List ExchangeLeg) where
  after : WorldState resourceCatalog
  receipts : List TransferReceipt
  receiptsExact : ExchangeReceiptsExact legs receipts
  replayExact : replayExchangeReceipts receipts before.holdings = after.holdings
  totalsPreserved :
    ∀ resourceId, (after.total resourceId).atoms = (before.total resourceId).atoms

private def applyExchangeLegs
    {resourceCatalog : ResourceCatalog}
    (index : Nat)
    (before : WorldState resourceCatalog) :
    (legs : List ExchangeLeg) →
      Except ExchangeIssue (AppliedExchange before legs)
  | [] =>
      .ok
        { after := before
          receipts := []
          receiptsExact := .nil
          replayExact := rfl
          totalsPreserved := by simp }
  | leg :: rest =>
      match assessTransfer before leg.transfer with
      | .rejected issues _ _ => .error (.legRejected index issues)
      | .accepted accepted =>
          let middle := applyTransferState accepted
          match applyExchangeLegs (index + 1) middle rest with
          | .error issue => .error issue
          | .ok suffix =>
              .ok
                { after := suffix.after
                  receipts := transferReceipt accepted :: suffix.receipts
                  receiptsExact := .cons
                    ⟨rfl, rfl, transferReceipt_entries accepted⟩
                    suffix.receiptsExact
                  replayExact := by
                    change replayExchangeReceipts suffix.receipts
                        (replayReceipt (transferReceipt accepted) before.holdings) =
                      suffix.after.holdings
                    rw [replay_transferReceipt accepted]
                    exact suffix.replayExact
                  totalsPreserved := by
                    intro resourceId
                    exact (suffix.totalsPreserved resourceId).trans
                      (applyTransferState_total accepted resourceId) }

/-- Apply all legs atomically; a failed suffix exposes no locally applied prefix. -/
def applyExchange
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (exchange : Exchange) :
    Except ExchangeIssue (AppliedExchange before exchange.legs) :=
  applyExchangeLegs 0 before exchange.legs

def exchangeSuccessor
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (exchange : Exchange) : Option (WorldState resourceCatalog) :=
  match applyExchange before exchange with
  | .error _ => none
  | .ok applied => some applied.after

def exchangeIssue?
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (exchange : Exchange) : Option ExchangeIssue :=
  match applyExchange before exchange with
  | .error issue => some issue
  | .ok _ => none

theorem exchangeSuccessor_rejected
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (exchange : Exchange)
    (issue : ExchangeIssue)
    (rejected : applyExchange before exchange = .error issue) :
    exchangeSuccessor before exchange = none := by
  simp [exchangeSuccessor, rejected]

structure AppliedCustodyExchange
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (legs : List ExchangeLeg) where
  after : WorldState resourceCatalog
  backedAfter : MachineCustody.Backed after custody
  receipts : List TransferReceipt
  receiptsExact : ExchangeReceiptsExact legs receipts
  replayExact : replayExchangeReceipts receipts before.holdings = after.holdings
  totalsPreserved :
    ∀ resourceId, (after.total resourceId).atoms = (before.total resourceId).atoms

private def applyCustodyExchangeLegs
    {resourceCatalog : ResourceCatalog}
    (index : Nat)
    (custody : MachineCustody inventory)
    (before : WorldState resourceCatalog)
    (backedBefore : MachineCustody.Backed before custody) :
    (legs : List ExchangeLeg) →
      Except ExchangeIssue (AppliedCustodyExchange before custody legs)
  | [] =>
      .ok
        { after := before
          backedAfter := backedBefore
          receipts := []
          receiptsExact := .nil
          replayExact := rfl
          totalsPreserved := by simp }
  | leg :: rest =>
      match MachineCustody.assessCustodyTransfer before custody leg.transfer with
      | .rejected issues _ _ => .error (.legRejected index issues)
      | .accepted accepted =>
          let ordinary := accepted.transferAccepted
          let middle := applyTransferState ordinary
          let backedMiddle := backedBefore.applyCustodyTransfer accepted
          match applyCustodyExchangeLegs (index + 1) custody middle backedMiddle
              rest with
          | .error issue => .error issue
          | .ok suffix =>
              .ok
                { after := suffix.after
                  backedAfter := suffix.backedAfter
                  receipts := transferReceipt ordinary :: suffix.receipts
                  receiptsExact := .cons
                    ⟨rfl, rfl, transferReceipt_entries ordinary⟩
                    suffix.receiptsExact
                  replayExact := by
                    change replayExchangeReceipts suffix.receipts
                        (replayReceipt (transferReceipt ordinary) before.holdings) =
                      suffix.after.holdings
                    rw [replay_transferReceipt ordinary]
                    exact suffix.replayExact
                  totalsPreserved := by
                    intro resourceId
                    exact (suffix.totalsPreserved resourceId).trans
                      (applyTransferState_total ordinary resourceId) }

def applyCustodyExchange
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (backedBefore : MachineCustody.Backed before custody)
    (exchange : Exchange) :
    Except ExchangeIssue
      (AppliedCustodyExchange before custody exchange.legs) :=
  applyCustodyExchangeLegs 0 custody before backedBefore exchange.legs

def custodyExchangeIssue?
    {resourceCatalog : ResourceCatalog}
    (before : WorldState resourceCatalog)
    (custody : MachineCustody inventory)
    (backedBefore : MachineCustody.Backed before custody)
    (exchange : Exchange) : Option ExchangeIssue :=
  match applyCustodyExchange before custody backedBefore exchange with
  | .error issue => some issue
  | .ok _ => none

end Maquina
