import Std

/-!
# Maquina Queues

Generic proof-carrying FIFO queues with optional capacity and monotonic tickets.
Queues contain no machine or game vocabulary.
-/

namespace Maquina

/-- One admitted value and its stable, never-reused position. -/
structure QueueEntry (Value : Type) where
  ticket : Nat
  value : Value
  deriving DecidableEq, Repr

/-- The capacity proposition carried by every valid queue. -/
def WithinCapacity (capacity : Option Nat) (length : Nat) : Prop :=
  match capacity with
  | none => True
  | some maximum => length ≤ maximum

/--
A FIFO queue whose live entries have increasing tickets below `nextTicket`.
Removing entries never rewinds `nextTicket`, so a later admission cannot reuse
a position previously observed in a receipt.
-/
structure Queue (Value : Type) where
  capacity : Option Nat
  nextTicket : Nat
  entries : List (QueueEntry Value)
  withinCapacity : WithinCapacity capacity entries.length
  ticketsOrdered : entries.Pairwise fun left right => left.ticket < right.ticket
  ticketsBeforeNext : ∀ entry ∈ entries, entry.ticket < nextTicket

namespace Queue

/-- An empty queue may be unbounded or bounded, including at capacity zero. -/
def empty (capacity : Option Nat := none) : Queue Value where
  capacity := capacity
  nextTicket := 0
  entries := []
  withinCapacity := by cases capacity <;> simp [WithinCapacity]
  ticketsOrdered := by simp
  ticketsBeforeNext := by simp

def length (queue : Queue Value) : Nat := queue.entries.length

def values (queue : Queue Value) : List Value :=
  queue.entries.map QueueEntry.value

def front? (queue : Queue Value) : Option (QueueEntry Value) :=
  queue.entries.head?

@[simp]
theorem length_empty (capacity : Option Nat) :
    (empty capacity : Queue Value).length = 0 := rfl

@[simp]
theorem values_empty (capacity : Option Nat) :
    (empty capacity : Queue Value).values = [] := rfl

/-- Every bounded queue remains within its declared maximum. -/
theorem length_le_capacity
    (queue : Queue Value)
    {maximum : Nat}
    (bounded : queue.capacity = some maximum) :
    queue.length ≤ maximum := by
  simpa [length, WithinCapacity, bounded] using queue.withinCapacity

/-- Strict ticket ordering implies that every live ticket is unique. -/
theorem tickets_unique (queue : Queue Value) :
    (queue.entries.map QueueEntry.ticket).Nodup := by
  exact queue.ticketsOrdered.map QueueEntry.ticket
    (fun _ _ ordered => Nat.ne_of_lt ordered)

/-! ## Enqueue assessment and transition -/

inductive QueueIssue where
  | full (capacity : Nat) (length : Nat)
  | empty
  deriving DecidableEq, Repr

def enqueueIssues (queue : Queue Value) : List QueueIssue :=
  match queue.capacity with
  | none => []
  | some maximum =>
      if queue.length < maximum then []
      else [.full maximum queue.length]

structure AcceptedEnqueue (queue : Queue Value) : Prop where
  issuesEmpty : enqueueIssues queue = []

inductive EnqueueAssessment (queue : Queue Value) where
  | accepted (witness : AcceptedEnqueue queue)
  | rejected
      (issues : List QueueIssue)
      (issuesExact : issues = enqueueIssues queue)
      (nonempty : issues ≠ [])

def assessEnqueue (queue : Queue Value) : EnqueueAssessment queue :=
  let issues := enqueueIssues queue
  if emptyIssues : issues = [] then
    .accepted ⟨emptyIssues⟩
  else
    .rejected issues rfl emptyIssues

/-- Accepted admission has room for exactly one more entry. -/
theorem AcceptedEnqueue.hasRoom
    {queue : Queue Value}
    (accepted : AcceptedEnqueue queue) :
    match queue.capacity with
    | none => True
    | some maximum => queue.length < maximum := by
  cases bounded : queue.capacity with
  | none => trivial
  | some maximum =>
      by_cases room : queue.length < maximum
      · exact room
      · have issuesEmpty := accepted.issuesEmpty
        simp [enqueueIssues, bounded, room] at issuesEmpty

/-- The successful result records both the new queue and admitted entry. -/
structure EnqueueResult (Value : Type) where
  queue : Queue Value
  admitted : QueueEntry Value

def enqueue
    (queue : Queue Value)
    (value : Value)
    (accepted : AcceptedEnqueue queue) : EnqueueResult Value :=
  let admitted : QueueEntry Value :=
    { ticket := queue.nextTicket, value }
  let queueAfter : Queue Value :=
    { capacity := queue.capacity
      nextTicket := queue.nextTicket + 1
      entries := queue.entries ++ [admitted]
      withinCapacity := by
        cases bounded : queue.capacity with
        | none => trivial
        | some maximum =>
            have room := accepted.hasRoom
            simp [WithinCapacity, bounded, length] at room ⊢
            omega
      ticketsOrdered := by
        rw [List.pairwise_append]
        refine ⟨queue.ticketsOrdered, by simp, ?_⟩
        intro existing existingMem newEntry newEntryMem
        simp only [List.mem_singleton] at newEntryMem
        subst newEntry
        exact queue.ticketsBeforeNext existing existingMem
      ticketsBeforeNext := by
        intro entry entryMem
        simp only [List.mem_append, List.mem_singleton] at entryMem
        rcases entryMem with existingMem | admittedEq
        · have before := queue.ticketsBeforeNext entry existingMem
          omega
        · subst entry
          simp [admitted] }
  { queue := queueAfter, admitted }

def assessAndEnqueue
    (queue : Queue Value)
    (value : Value) : Option (EnqueueResult Value) :=
  match assessEnqueue queue with
  | .accepted accepted => some (enqueue queue value accepted)
  | .rejected _ _ _ => none

/-- A rejected admission produces no queue transition. -/
theorem assessAndEnqueue_rejected
    (queue : Queue Value)
    (value : Value)
    (issuesPresent : enqueueIssues queue ≠ []) :
    assessAndEnqueue queue value = none := by
  simp [assessAndEnqueue, assessEnqueue, issuesPresent]

@[simp]
theorem enqueue_admitted_ticket
    (queue : Queue Value)
    (value : Value)
    (accepted : AcceptedEnqueue queue) :
    (enqueue queue value accepted).admitted.ticket = queue.nextTicket := rfl

@[simp]
theorem enqueue_entries
    (queue : Queue Value)
    (value : Value)
    (accepted : AcceptedEnqueue queue) :
    (enqueue queue value accepted).queue.entries =
      queue.entries ++ [(enqueue queue value accepted).admitted] := rfl

@[simp]
theorem enqueue_values
    (queue : Queue Value)
    (value : Value)
    (accepted : AcceptedEnqueue queue) :
    (enqueue queue value accepted).queue.values = queue.values ++ [value] := by
  simp [enqueue, values]

@[simp]
theorem enqueue_nextTicket
    (queue : Queue Value)
    (value : Value)
    (accepted : AcceptedEnqueue queue) :
    (enqueue queue value accepted).queue.nextTicket = queue.nextTicket + 1 := rfl

/-! ## Dequeue assessment and transition -/

def dequeueIssues (queue : Queue Value) : List QueueIssue :=
  if queue.entries = [] then [.empty] else []

structure AcceptedDequeue (queue : Queue Value) : Prop where
  issuesEmpty : dequeueIssues queue = []

inductive DequeueAssessment (queue : Queue Value) where
  | accepted (witness : AcceptedDequeue queue)
  | rejected
      (issues : List QueueIssue)
      (issuesExact : issues = dequeueIssues queue)
      (nonempty : issues ≠ [])

def assessDequeue (queue : Queue Value) : DequeueAssessment queue :=
  let issues := dequeueIssues queue
  if emptyIssues : issues = [] then
    .accepted ⟨emptyIssues⟩
  else
    .rejected issues rfl emptyIssues

theorem AcceptedDequeue.nonempty
    {queue : Queue Value}
    (accepted : AcceptedDequeue queue) :
    queue.entries ≠ [] := by
  intro entriesEmpty
  have issuesEmpty := accepted.issuesEmpty
  simp [dequeueIssues, entriesEmpty] at issuesEmpty

structure DequeueResult (Value : Type) where
  queue : Queue Value
  removed : QueueEntry Value

def dequeue
    (queue : Queue Value)
    (accepted : AcceptedDequeue queue) : DequeueResult Value :=
  { removed := queue.entries.head accepted.nonempty
    queue :=
      { capacity := queue.capacity
        nextTicket := queue.nextTicket
        entries := queue.entries.tail
        withinCapacity := by
          cases bounded : queue.capacity with
          | none => trivial
          | some maximum =>
              have within := queue.withinCapacity
              simp [WithinCapacity, bounded, List.length_tail] at within ⊢
              omega
        ticketsOrdered := queue.ticketsOrdered.tail
        ticketsBeforeNext := by
          intro entry entryMem
          exact queue.ticketsBeforeNext entry (List.mem_of_mem_tail entryMem) } }

def assessAndDequeue
    (queue : Queue Value) : Option (DequeueResult Value) :=
  match assessDequeue queue with
  | .accepted accepted => some (dequeue queue accepted)
  | .rejected _ _ _ => none

/-- A rejected removal produces no queue transition. -/
theorem assessAndDequeue_rejected
    (queue : Queue Value)
    (issuesPresent : dequeueIssues queue ≠ []) :
    assessAndDequeue queue = none := by
  simp [assessAndDequeue, assessDequeue, issuesPresent]

@[simp]
theorem dequeue_front
    (queue : Queue Value)
    (accepted : AcceptedDequeue queue) :
    queue.front? = some (dequeue queue accepted).removed := by
  cases entriesEq : queue.entries with
  | nil => exact False.elim (accepted.nonempty entriesEq)
  | cons removed remaining => simp [front?, dequeue, entriesEq]

@[simp]
theorem dequeue_nextTicket
    (queue : Queue Value)
    (accepted : AcceptedDequeue queue) :
    (dequeue queue accepted).queue.nextTicket = queue.nextTicket := rfl

/-- Replace only the FIFO front value while preserving its stable ticket. -/
def replaceFront
    (queue : Queue Value)
    (accepted : AcceptedDequeue queue)
    (value : Value) : Queue Value := by
  cases entriesEq : queue.entries with
  | nil => exact False.elim (accepted.nonempty entriesEq)
  | cons front rest =>
      exact
        { capacity := queue.capacity
          nextTicket := queue.nextTicket
          entries := { ticket := front.ticket, value := value } :: rest
          withinCapacity := by
            simpa [entriesEq] using queue.withinCapacity
          ticketsOrdered := by
            simpa [entriesEq] using queue.ticketsOrdered
          ticketsBeforeNext := by
            intro entry entryMem
            simp only [List.mem_cons] at entryMem
            rcases entryMem with isFront | inRest
            · subst entry
              exact queue.ticketsBeforeNext front (by simp [entriesEq])
            · exact queue.ticketsBeforeNext entry
                (by simp [entriesEq, inRest]) }

@[simp]
theorem replaceFront_front
    (queue : Queue Value)
    (accepted : AcceptedDequeue queue)
    (value : Value) :
    (queue.replaceFront accepted value).front?.map QueueEntry.value = some value := by
  cases queue with
  | mk capacity nextTicket entries within ordered before =>
      cases entries with
      | nil =>
          have impossible := accepted.nonempty
          simp at impossible
      | cons front rest => rfl

@[simp]
theorem replaceFront_nextTicket
    (queue : Queue Value)
    (accepted : AcceptedDequeue queue)
    (value : Value) :
    (queue.replaceFront accepted value).nextTicket = queue.nextTicket := by
  cases queue with
  | mk capacity nextTicket entries within ordered before =>
      cases entries with
      | nil =>
          have impossible := accepted.nonempty
          simp at impossible
      | cons front rest => rfl

@[simp]
theorem assessAndEnqueue_full_zero
    (value : Value) :
    assessAndEnqueue (empty (some 0)) value = none := by
  simp [assessAndEnqueue, assessEnqueue, enqueueIssues, length, empty]

@[simp]
theorem assessAndDequeue_empty (capacity : Option Nat) :
    assessAndDequeue (empty capacity : Queue Value) = none := by
  simp [assessAndDequeue, assessDequeue, dequeueIssues, empty]

end Queue

end Maquina
