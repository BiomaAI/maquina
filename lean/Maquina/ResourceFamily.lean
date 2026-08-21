import Maquina.Resource

/-!
# Maquina Structured Resource Families

A family gives dynamically keyed Resources a reversible, namespace-safe
identity scheme and a canonical specification. Games use families for Bodies,
endpoints, Links, claims, and other parameterized Resource identities.
-/

namespace Maquina

structure ResourceFamily (Key : Type) where
  name : String
  encode : Key → ResourceId
  decode : ResourceId → Option Key
  decodeEncode : ∀ key, decode (encode key) = some key
  encodeDecode : ∀ {resourceId key}, decode resourceId = some key →
    encode key = resourceId
  spec : Key → ResourceSpec
  specId : ∀ key, (spec key).header.id = encode key

namespace ResourceFamily

/-- A reversible numeric offset for dynamically keyed Resources. -/
def offsetNat (base : Nat) (familyName : String) : ResourceFamily Nat where
  name := familyName
  encode := fun key => ⟨base + key⟩
  decode := fun resourceId =>
    if base ≤ resourceId.value then some (resourceId.value - base) else none
  decodeEncode := by
    intro key
    change (if base ≤ base + key then some (base + key - base) else none) =
      some key
    rw [if_pos (Nat.le_add_right base key)]
    simp
  encodeDecode := by
    intro resourceId key decoded
    change (if base ≤ resourceId.value then
      some (resourceId.value - base) else none) = some key at decoded
    split at decoded
    · rename_i inRange
      have keyExact := Option.some.inj decoded
      cases resourceId with
      | mk value =>
          change base ≤ value at inRange
          change value - base = key at keyExact
          change ResourceId.mk (base + key) = ResourceId.mk value
          congr
          omega
    · contradiction
  spec := fun key =>
    ResourceSpec.unique
      { id := ⟨base + key⟩, name := s!"{familyName}/{key}" }
  specId := by intro key; rfl

/--
One residue class of a numeric namespace. Families with the same positive
modulus and different in-range tags are provably disjoint.
-/
def modularNat
    (modulus tag : Nat)
    (modulusPositive : 0 < modulus)
    (tagInRange : tag < modulus)
    (familyName : String) : ResourceFamily Nat where
  name := familyName
  encode := fun key => ⟨modulus * key + tag⟩
  decode := fun resourceId =>
    if resourceId.value % modulus = tag then
      some (resourceId.value / modulus)
    else none
  decodeEncode := by
    intro key
    change (if (modulus * key + tag) % modulus = tag then
      some ((modulus * key + tag) / modulus) else none) = some key
    have remainderExact : (modulus * key + tag) % modulus = tag := by
      rw [Nat.mul_comm]
      exact Nat.mul_add_mod_of_lt tagInRange
    rw [if_pos remainderExact]
    congr
    rw [Nat.add_comm]
    simp [Nat.add_mul_div_left, modulusPositive, Nat.div_eq_of_lt tagInRange]
  encodeDecode := by
    intro resourceId key decoded
    change (if resourceId.value % modulus = tag then
      some (resourceId.value / modulus) else none) = some key at decoded
    split at decoded
    · rename_i remainderExact
      have quotientExact := Option.some.inj decoded
      cases resourceId with
      | mk value =>
          change value % modulus = tag at remainderExact
          change value / modulus = key at quotientExact
          change ResourceId.mk (modulus * key + tag) = ResourceId.mk value
          congr
          calc
            modulus * key + tag =
                modulus * (value / modulus) + value % modulus := by
                  rw [quotientExact, remainderExact]
            _ = value := Nat.div_add_mod value modulus
    · contradiction
  spec := fun key => ResourceSpec.unique
    { id := ⟨modulus * key + tag⟩, name := s!"{familyName}/{key}" }
  specId := by intro key; rfl

/-- Reversible encoding makes every family injective. -/
theorem encode_injective
    (family : ResourceFamily Key) : Function.Injective family.encode := by
  intro left right same
  have leftDecoded := family.decodeEncode left
  have rightDecoded := family.decodeEncode right
  rw [same] at leftDecoded
  exact Option.some.inj (leftDecoded.symm.trans rightDecoded)

/-- Exact evidence that one Resource ID belongs to a structured family. -/
structure Membership (family : ResourceFamily Key) (resourceId : ResourceId) where
  key : Key
  decoded : family.decode resourceId = some key

def member? [DecidableEq Key]
    (family : ResourceFamily Key)
    (resourceId : ResourceId) : Option Key :=
  family.decode resourceId

theorem membership_id
    {family : ResourceFamily Key}
    {resourceId : ResourceId}
    (member : Membership family resourceId) :
    family.encode member.key = resourceId :=
  family.encodeDecode member.decoded

/-- A family can serve as an authoritative algorithmic catalog. -/
def catalog (family : ResourceFamily Key) : ResourceCatalog where
  lookup := fun resourceId =>
    match family.decode resourceId with
    | none => none
    | some key => some (family.spec key)
  idMatches := by
    intro resourceId spec found
    cases decoded : family.decode resourceId with
    | none => simp [decoded] at found
    | some key =>
        simp only [decoded] at found
        have specExact := Option.some.inj found
        rw [← specExact, family.specId key, family.encodeDecode decoded]

/-- Two families are namespace-disjoint when no encoded IDs overlap. -/
def Disjoint
    (left : ResourceFamily LeftKey)
    (right : ResourceFamily RightKey) : Prop :=
  ∀ leftKey rightKey, left.encode leftKey ≠ right.encode rightKey

theorem modularNat_disjoint
    (modulus leftTag rightTag : Nat)
    (modulusPositive : 0 < modulus)
    (leftInRange : leftTag < modulus)
    (rightInRange : rightTag < modulus)
    (tagsDistinct : leftTag ≠ rightTag)
    (leftName rightName : String) :
    Disjoint
      (modularNat modulus leftTag modulusPositive leftInRange leftName)
      (modularNat modulus rightTag modulusPositive rightInRange rightName) := by
  intro leftKey rightKey same
  have values := congrArg ResourceId.value same
  have residues := congrArg (fun value => value % modulus) values
  simp only [modularNat] at residues
  have leftRemainder : (modulus * leftKey + leftTag) % modulus = leftTag := by
    rw [Nat.mul_comm]
    exact Nat.mul_add_mod_of_lt leftInRange
  have rightRemainder : (modulus * rightKey + rightTag) % modulus = rightTag := by
    rw [Nat.mul_comm]
    exact Nat.mul_add_mod_of_lt rightInRange
  rw [leftRemainder, rightRemainder] at residues
  exact tagsDistinct residues

theorem Disjoint.symm
    {left : ResourceFamily LeftKey}
    {right : ResourceFamily RightKey}
    (disjoint : Disjoint left right) : Disjoint right left := by
  intro rightKey leftKey same
  exact disjoint leftKey rightKey same.symm

/-- Decoding an ID in one disjoint family excludes membership in the other. -/
theorem Disjoint.decode_right_none
    {left : ResourceFamily LeftKey}
    {right : ResourceFamily RightKey}
    (disjoint : Disjoint left right)
    {resourceId : ResourceId}
    {leftKey : LeftKey}
    (decoded : left.decode resourceId = some leftKey) :
    right.decode resourceId = none := by
  cases rightDecoded : right.decode resourceId with
  | none => rfl
  | some rightKey =>
      have leftId := left.encodeDecode decoded
      have rightId := right.encodeDecode rightDecoded
      exact False.elim (disjoint leftKey rightKey (leftId.trans rightId.symm))

end ResourceFamily

end Maquina
