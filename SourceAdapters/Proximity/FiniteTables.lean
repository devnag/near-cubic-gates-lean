import SourceAdapters.Code.Preparation
import SourceAdapters.Proximity.CanonicalHonest

/-!
Q02/Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": an actual ordinary finite-table compiler.
A fixed number of input bits is read by an explicit finite decision tree;
its leaves print literal output words. The language run and its cost are
proved before taking a uniform finite maximum. This is suitable for the
constant-query truth-table conversion, not for a variable-size PCPP compiler.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code.Parsing
open NearCubicGates.Published.CW19Proximity

/-- Read exactly `count` bits and print the corresponding literal table entry. -/
def lookupScript : ℕ → (List Bool → List Bool) → Script
  | 0, table => emitLiteral (table [])
  | count + 1, table => .seq (.op (.rdI 1))
      (.ite (.eq 0 1) (lookupScript count (fun bits => table (false :: bits)))
        (lookupScript count (fun bits => table (true :: bits))))

theorem lookupScript_run (C : Ctx) (count : ℕ) (table : List Bool → List Bool)
    (a : State) (hz : a.env 0 = 0) (bits pre suffix : List Bool)
    (hlen : bits.length = count) (hin : C.inp = pre ++ bits ++ suffix)
    (hip : a.ip = pre.length) :
    ∃ b : State, Ex C (lookupScript count table) a b (3 * count + 2 * (table bits).length + 1) ∧
      b.out = a.out ++ table bits := by
  induction count generalizing table a bits pre with
  | zero =>
    have hb : bits = [] := List.length_eq_zero_iff.mp hlen
    subst bits
    exact ⟨_, by simpa [lookupScript] using emit_literal C (table []) a hz, rfl⟩
  | succ count ih =>
    cases bits with
    | nil => simp at hlen
    | cons bit bits =>
      have ht : bits.length = count := by simpa using hlen
      have er := read_at_prefix C a pre bit (bits ++ suffix)
        (by simpa using hin) hip
      let a1 := readState a bit
      have hz1 : a1.env 0 = 0 := by simp [a1, readState, DS.set, hz]
      have hip1 : a1.ip = (pre ++ [bit]).length := by simp [a1, readState, hip]
      have hin1 : C.inp = (pre ++ [bit]) ++ bits ++ suffix := by simpa [List.append_assoc] using hin
      obtain ⟨b, eb, hb⟩ := ih (fun tail => table (bit :: tail)) a1 hz1 bits (pre ++ [bit]) ht hin1 hip1
      have ebranch : Ex C (.ite (.eq 0 1)
          (lookupScript count (fun tail => table (false :: tail)))
          (lookupScript count (fun tail => table (true :: tail)))) a1 b
          ((3 * count + 2 * (table (bit :: bits)).length + 1) + 1) := by
        cases bit
        · exact Ex.iteT (by norm_num [Cnd.wf])
            (by simp [Cnd.eval, a1, readState, DS.set, hz]) eb
        · exact Ex.iteF (by norm_num [Cnd.wf])
            (by simp [Cnd.eval, a1, readState, DS.set, hz]) eb
      refine ⟨b, ?_, hb⟩
      convert Ex.seq er ebranch using 1 <;> first | rfl | omega

def tableScript {count : ℕ} (table : BitInput count → List Bool) : Script :=
  lookupScript count (fun bits => table (fun i => bits.getD i.val false))

def tableCost {count : ℕ} (table : BitInput count → List Bool) (input : BitInput count) : ℕ :=
  3 * count + 2 * (table input).length + 1

def tableBudget {count : ℕ} (table : BitInput count → List Bool) (input : BitInput count) : ℕ :=
  langBudget copyCallee payloadSize 2 0 (List.ofFn input) (tableCost table input)

theorem tableScript_runs {count : ℕ} (table : BitInput count → List Bool) (input : BitInput count) :
    ∃ b n, Ex (ctxOf copyCallee payloadSize (List.ofFn input)) (tableScript table) (a0 : State) b n ∧
      b.out = table input ∧ n ≤ tableCost table input := by
  have heq : (fun i : Fin count => (List.ofFn input).getD i.val false) = input := by
    funext i
    simp [List.getD, i.isLt]
  obtain ⟨b, hb, hout⟩ := lookupScript_run
    (ctxOf copyCallee payloadSize (List.ofFn input)) count
    (fun bits => table (fun i => bits.getD i.val false)) (a0 : State) rfl
    (List.ofFn input) [] [] (by simp) (by simp [ctxOf]) rfl
  refine ⟨b, _, hb, ?_, ?_⟩
  · simpa only [a0, List.nil_append, heq] using hout
  · simp only [heq, tableCost, le_refl]

/-- Actual ordinary realization of any fixed finite table, including trailing zeros. -/
noncomputable def tableWordFunction {count : ℕ} (table : BitInput count → List Bool) :
    WordFunction (BitInput count) List.ofFn table (tableBudget table) :=
  wordFunction_of_lang List.ofFn table copyCallee payloadSize (tableScript table) (tableCost table)
    (tableScript_runs table) (fun _ => by simp [payloadSize, Sz.W])

/-- The finite constant is chosen after the fixed table and fixed input width. -/
theorem table_polynomial {count : ℕ} (table : BitInput count → List Bool) :
    SourcePolyTime (fun input : BitInput count => List.ofFn input) table := by
  classical
  let K := Finset.univ.sup (tableBudget table)
  refine ⟨K, 0, ⟨(tableWordFunction table).enlargeBudget (fun input => ?_)⟩⟩
  simp only [pow_zero, Nat.mul_one]
  exact Finset.le_sup (f := tableBudget table) (Finset.mem_univ input)

end NearCubicGates.Adapters.Proximity
