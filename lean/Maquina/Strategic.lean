import Maquina.Command
import Maquina.AccountTransaction

/-!
# Maquina Strategic Interaction

Game-independent protocol data for imperfect-information and cooperative games.
Maquina owns information boundaries, immutable communication, sealed command
rounds, consent, and account-level escrow. Games continue to own truth,
deception, trust, objectives, payoffs, and the meaning of every command.
-/

namespace Maquina

/-! ## Actor-safe command surfaces and information sets -/

/--
An actor-facing command surface is constructed only from that actor's declared
observation. Candidate labels, availability, and redacted explanations therefore
cannot inspect authoritative state through a second path.
-/
structure ActorSafeCommandPolicy
    (State Observation CandidateView : Type)
    (observation : ObservationPolicy State Observation) where
  present : ActorId → Observation → List CandidateView

def ActorSafeCommandPolicy.surface
    (policy : ActorSafeCommandPolicy State Observation CandidateView observation)
    (actor : ActorId)
    (state : State) : List CandidateView :=
  policy.present actor (observation.observe actor state)

/-- Observation-equivalent states expose exactly the same command surface. -/
theorem ActorSafeCommandPolicy.surface_noninterference
    (policy : ActorSafeCommandPolicy State Observation CandidateView observation)
    (equivalent : observation.observe actor left = observation.observe actor right) :
    policy.surface actor left = policy.surface actor right := by
  simp [ActorSafeCommandPolicy.surface, equivalent]

/--
An information set groups authoritative states that one actor cannot
distinguish. It is game-owned, but its indistinguishability claim is checked
against the ordinary Maquina observation policy.
-/
structure InformationSet
    (State Observation : Type)
    (policy : ObservationPolicy State Observation) where
  id : Nat
  actor : ActorId
  representative : State
  alternatives : List State
  representativeMember : representative ∈ alternatives
  indistinguishable : ∀ state ∈ alternatives,
    policy.observe actor state = policy.observe actor representative

theorem InformationSet.same_command_surface
    (informationSet : InformationSet State Observation observation)
    (commandPolicy :
      ActorSafeCommandPolicy State Observation CandidateView observation)
    (state : State)
    (member : state ∈ informationSet.alternatives) :
    commandPolicy.surface informationSet.actor state =
      commandPolicy.surface informationSet.actor informationSet.representative :=
  commandPolicy.surface_noninterference
    (informationSet.indistinguishable state member)

/-- A strategy can inspect an observation, never an authoritative state. -/
structure ObservationStrategy (Observation : Type) where
  actor : ActorId
  choose : Observation → CandidateId

def ObservationStrategy.chooseAt
    (strategy : ObservationStrategy Observation)
    (policy : ObservationPolicy State Observation)
    (state : State) : CandidateId :=
  strategy.choose (policy.observe strategy.actor state)

theorem ObservationStrategy.information_set_consistent
    (strategy : ObservationStrategy Observation)
    (policy : ObservationPolicy State Observation)
    (equivalent : policy.observe strategy.actor left =
      policy.observe strategy.actor right) :
    strategy.chooseAt policy left = strategy.chooseAt policy right := by
  simp [ObservationStrategy.chooseAt, equivalent]

/-! ## Audience-scoped immutable communication -/

inductive MessageAudience where
  | broadcast
  | privateTo (actor : ActorId)
  | coalition (actors : List ActorId)
  deriving DecidableEq, Repr

def MessageAudience.visibleTo
    (audience : MessageAudience)
    (actor : ActorId) : Bool :=
  match audience with
  | .broadcast => true
  | .privateTo recipient => decide (recipient = actor)
  | .coalition actors => decide (actor ∈ actors)

/--
Message payloads are inert claims. A game may separately attach evidence, but
Maquina never treats message content as authoritative truth.
-/
structure ScopedMessage (Payload : Type) where
  id : Nat
  sender : ActorId
  audience : MessageAudience
  payload : Payload
  deriving DecidableEq, Repr

def messagesFor
    (actor : ActorId)
    (messages : List (ScopedMessage Payload)) : List (ScopedMessage Payload) :=
  messages.filter fun message => message.audience.visibleTo actor

theorem messagesFor_visible
    (message : ScopedMessage Payload)
    (member : message ∈ messagesFor actor messages) :
    message.audience.visibleTo actor = true := by
  simpa [messagesFor] using (List.mem_filter.mp member).2

/-! ## Sealed simultaneous command rounds -/

/-- Opaque, game-constructed commitment identity. -/
structure CommitmentToken where
  value : Nat
  deriving DecidableEq, Repr

/-- The commit phase contains attribution and a token, but no command payload. -/
structure SealedCommitment where
  id : IntentId
  actor : ActorId
  arbitration : ArbitrationKey
  token : CommitmentToken
  deriving DecidableEq, Repr

/-- A reveal is accepted only when its payload reproduces the committed token. -/
structure RevealedOrder
    (Intent : Type)
    (commit : Intent → CommitmentToken) where
  sealed : SealedCommitment
  payload : Intent
  binding : commit payload = sealed.token

def RevealedOrder.commandOrder
    (reveal : RevealedOrder Intent commit) : CommandOrder Intent where
  id := reveal.sealed.id
  actor := reveal.sealed.actor
  arbitration := reveal.sealed.arbitration
  payload := reveal.payload

/--
A closed round contains one uniquely identified reveal per scheduled order.
Before closure, `SealedCommitment` structurally contains no intent payload.
-/
structure ClosedSealedRound
    (Intent : Type)
    (commit : Intent → CommitmentToken) where
  reveals : List (RevealedOrder Intent commit)
  idsUnique : (reveals.map fun reveal => reveal.sealed.id).Nodup
  actorsUnique : (reveals.map fun reveal => reveal.sealed.actor).Nodup

def ClosedSealedRound.orderSet
    (round : ClosedSealedRound Intent commit) : OrderSet Intent where
  orders := round.reveals.map RevealedOrder.commandOrder
  idsUnique := by
    simpa [RevealedOrder.commandOrder, List.map_map, Function.comp_def] using
      round.idsUnique

theorem ClosedSealedRound.order_actors_unique
    (round : ClosedSealedRound Intent commit) :
    ((round.orderSet.orders.map fun order => order.actor).Nodup) := by
  simpa [ClosedSealedRound.orderSet, RevealedOrder.commandOrder,
    List.map_map, Function.comp_def] using round.actorsUnique

/-! ## Multi-party consent and account-level escrow -/

/-- Game-owned terms with an exact, nonempty set of consenting actors. -/
structure JointAgreement (Terms : Type) where
  id : Nat
  parties : List ActorId
  partiesNonempty : parties ≠ []
  partiesUnique : parties.Nodup
  terms : Terms

/-- Ratification proves that exactly the declared parties approved the terms. -/
structure RatifiedAgreement
    (agreement : JointAgreement Terms) where
  approvals : List ActorId
  approvalsUnique : approvals.Nodup
  approvedExactly : ∀ actor, actor ∈ approvals ↔ actor ∈ agreement.parties

/--
Escrow is an ordinary machine-independent account transaction. The agreement
adds consent metadata; it does not introduce a machine-specific transaction.
-/
structure ResourceBackedAgreement (Terms : Type) where
  agreement : JointAgreement Terms
  ratified : RatifiedAgreement agreement
  escrow : AccountTransaction

theorem RatifiedAgreement.party_approved
    (ratified : RatifiedAgreement agreement)
    (member : actor ∈ agreement.parties) :
    actor ∈ ratified.approvals :=
  (ratified.approvedExactly actor).2 member

end Maquina
