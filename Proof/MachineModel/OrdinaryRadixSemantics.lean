import Proof.MachineModel.OrdinaryRadixIteration
import Mathlib.Data.List.Rotate

/-! Correctness of the actual radix-loop record transformation. All bits of a
record are retained: after its fixed width many rounds the result is a sorted
permutation of the original low-bit-first words. -/
namespace NearCubicWires.RepairOrdinary.RadixSemantics
open StablePartition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word (r : Record) : List Bool := r.1 :: r.2

theorem word_injective : Function.Injective word := by
  rintro ⟨a, as⟩ ⟨b, bs⟩ h
  simpa [word] using h

theorem word_rotate (r : Record) : word (RecordRotate.rotate r) = r.2 ++ [r.1] := by
  rcases r with ⟨tag, bits⟩
  cases bits <;> rfl

theorem word_rotate_eq (r : Record) : word (RecordRotate.rotate r) = (word r).rotate 1 := by
  rw [word_rotate]
  simp [word]

@[simp] theorem word_rotate_length (r : Record) :
    (word (RecordRotate.rotate r)).length = (word r).length := by
  rw [word_rotate_eq, List.length_rotate]

def spin : ℕ → Record → Record
  | 0, r => r
  | n + 1, r => spin n (RecordRotate.rotate r)

theorem spin_word (n : ℕ) (r : Record) : word (spin n r) = (word r).rotate n := by
  induction n generalizing r with
  | zero => simp [spin]
  | succ n ih => simp [spin, ih, word_rotate_eq, Nat.add_comm]

theorem spin_width (r : Record) : spin (word r).length r = r := by
  apply word_injective
  rw [spin_word, List.rotate_length]

theorem ordered_perm (rs : List Record) : (PartitionPass.ordered rs).Perm rs := by
  simpa [PartitionPass.ordered, selected] using List.filter_append_perm (fun r : Record => !r.1) rs

theorem round_perm (rs : List Record) :
    (RadixRound.records rs).Perm (rs.map RecordRotate.rotate) :=
  (ordered_perm rs).map RecordRotate.rotate

theorem iterations_perm (n : ℕ) (rs : List Record) :
    (RadixIteration.records n rs).Perm (rs.map (spin n)) := by
  induction n generalizing rs with
  | zero => simp [RadixIteration.records, spin]
  | succ n ih =>
    have h := (ih (RadixRound.records rs)).trans ((round_perm rs).map (spin n))
    simpa [RadixIteration.records, spin, List.map_map, Function.comp_def] using h

theorem fixed_width_perm (width : ℕ) (rs : List Record)
    (hw : ∀ r ∈ rs, (word r).length = width) : (RadixIteration.records width rs).Perm rs := by
  have he : rs.map (spin width) = rs := by
    conv_rhs => rw [← List.map_id rs]
    apply List.map_congr_left
    intro r hr
    rw [← hw r hr]
    exact spin_width r
  simpa only [he] using iterations_perm width rs

def value : List Bool → ℕ
  | [] => 0
  | b :: bits => b.toNat + 2 * value bits

theorem value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    simp only [List.cons_append, List.length_cons, value, ih, pow_succ]
    ring

theorem value_lt (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    cases b <;> simp only [value, Bool.toNat_false, Bool.toNat_true,
      List.length_cons, pow_succ] <;> omega

def key (width processed : ℕ) (r : Record) : ℕ := value ((word r).drop (width - processed))

theorem key_lt {width processed : ℕ} (r : Record) (hw : (word r).length = width)
    (hp : processed ≤ width) : key width processed r < 2 ^ processed := by
  have h := value_lt ((word r).drop (width - processed))
  have hl : ((word r).drop (width - processed)).length = processed := by
    rw [List.length_drop, hw]
    omega
  simpa only [key, hl] using h

theorem key_rotate {width processed : ℕ} (r : Record) (hw : (word r).length = width)
    (hp : processed < width) :
    key width (processed + 1) (RecordRotate.rotate r) =
      key width processed r + 2 ^ processed * r.1.toNat := by
  have hlen : r.2.length + 1 = width := hw
  have hsub : width - processed = (width - (processed + 1)) + 1 := by omega
  have hdrop : ((word r).drop (width - processed)).length = processed := by
    rw [List.length_drop, hw]
    omega
  unfold key
  rw [word_rotate, List.drop_append_of_le_length (by omega : width - (processed + 1) ≤ r.2.length)]
  have he : r.2.drop (width - (processed + 1)) = (word r).drop (width - processed) := by
    rw [hsub]
    rfl
  rw [he, value_append, hdrop]
  simp [value]

theorem round_width {width : ℕ} {rs : List Record}
    (hw : ∀ r ∈ rs, (word r).length = width) :
    ∀ r ∈ RadixRound.records rs, (word r).length = width := by
  intro r hr
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ((round_perm rs).mem_iff.mp hr)
  rw [word_rotate_length, hw a ha]

theorem round_sorted {width processed : ℕ} {rs : List Record}
    (hw : ∀ r ∈ rs, (word r).length = width) (hp : processed < width)
    (hs : rs.Pairwise (fun a b => key width processed a ≤ key width processed b)) :
    (RadixRound.records rs).Pairwise
      (fun a b => key width (processed + 1) a ≤ key width (processed + 1) b) := by
  have group (tag : Bool) : (selected tag rs).Pairwise
      (fun a b => key width (processed + 1) (RecordRotate.rotate a) ≤
        key width (processed + 1) (RecordRotate.rotate b)) := by
    apply List.Pairwise.imp_of_mem (p := hs.filter (fun r => r.1 == tag))
    intro a b ha hb hab
    have ha' : a ∈ rs ∧ a.1 = tag := by simpa [selected] using ha
    have hb' : b ∈ rs ∧ b.1 = tag := by simpa [selected] using hb
    rw [key_rotate a (hw a ha'.1) hp, key_rotate b (hw b hb'.1) hp, ha'.2, hb'.2]
    omega
  rw [RadixRound.records, List.pairwise_map, PartitionPass.ordered, List.pairwise_append]
  refine ⟨group false, group true, ?_⟩
  intro a ha b hb
  have ha' : a ∈ rs ∧ a.1 = false := by simpa [selected] using ha
  have hb' : b ∈ rs ∧ b.1 = true := by simpa [selected] using hb
  rw [key_rotate a (hw a ha'.1) hp, key_rotate b (hw b hb'.1) hp, ha'.2, hb'.2]
  have hlt := key_lt a (hw a ha'.1) hp.le
  simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
  omega

theorem sorted_from (remaining : ℕ) {width processed : ℕ} {rs : List Record}
    (hw : ∀ r ∈ rs, (word r).length = width) (hp : processed + remaining = width)
    (hs : rs.Pairwise (fun a b => key width processed a ≤ key width processed b)) :
    (RadixIteration.records remaining rs).Pairwise
      (fun a b => value (word a) ≤ value (word b)) := by
  induction remaining generalizing processed rs with
  | zero =>
    have he : processed = width := by omega
    simpa [RadixIteration.records, he, key] using hs
  | succ remaining ih =>
    exact ih (round_width hw) (by omega : (processed + 1) + remaining = width)
      (round_sorted hw (by omega) hs)

theorem sorted_permutation (width : ℕ) (rs : List Record)
    (hw : ∀ r ∈ rs, (word r).length = width) :
    (RadixIteration.records width rs).Perm rs ∧
      (RadixIteration.records width rs).Pairwise
        (fun a b => value (word a) ≤ value (word b)) := by
  refine ⟨fixed_width_perm width rs hw, ?_⟩
  apply sorted_from width hw (by omega : 0 + width = width)
  apply List.Pairwise.imp_of_mem (p := List.pairwise_of_forall (l := rs)
    (fun _ _ => True.intro))
  intro a b ha hb _
  have ka : key width 0 a = 0 := by simp [key, ← hw a ha, value]
  have kb : key width 0 b = 0 := by simp [key, ← hw b hb, value]
  rw [ka, kb]

end NearCubicWires.RepairOrdinary.RadixSemantics
