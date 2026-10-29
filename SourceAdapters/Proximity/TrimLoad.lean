import SourceAdapters.Proximity.TrimCounts
import SourceAdapters.Proximity.DescriptorParsing

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": actual input parsing and complete query-table loading.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins
open SourcePrinting (readInto read_into)

variable {C : Ctx}

def loadProgram : St VV MM := .seq (readInto arityReg)
  (.seq (readInto randomReg) (.seq countProgram (readF fieldsReg)))

def loadTemps : List (Fin VV) :=
  [arityReg, randomReg, rowsReg, countLoop, fieldsReg] ++ readT

structure TrimLoaded (a b : DS VV MM) {n : ℕ} (V : ThreeQueryVerifier n) : Prop where
  arity : b.env arityReg = n
  randomness : b.env randomReg = V.randomBits
  rows : b.env rowsReg = 2 ^ V.randomBits
  count : b.env fieldsReg = (fields V).length
  ram : b.ram = Function.update a.ram sN (a.ram sN ++ fields V)
  cursor : b.rc = Function.update a.rc sN ((a.ram sN).length + (fields V).length)
  input : b.ip = a.ip + (trimRequestWord ⟨n, V⟩).length
  other : (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc)
  vars : Fr a b loadTemps

theorem TrimLoaded.constants {a b : DS VV MM} {n : ℕ} {V : ThreeQueryVerifier n}
    (h : TrimLoaded a b V) (hc : Cst a) : Cst b :=
  Cst.of_fr hc h.vars (by decide)

theorem load_program {n : ℕ} (V : ThreeQueryVerifier n) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = trimRequestWord ⟨n, V⟩)
    (hrc : a.rc sN = (a.ram sN).length) (hW : inputSize V + 2 ≤ C.Wd) :
    Hs C loadProgram a (100 * (inputSize V + 1) ^ 2) (fun b => TrimLoaded a b V) := by
  have hn := arity_bits_le V
  have hr := random_bits_le V
  have hfcount := fields_count_le V
  have hrand := randomness_le V
  have hfit : (fields V).length < 2 ^ C.Wd :=
    lt_of_lt_of_le (by omega : (fields V).length < C.Wd) (Nat.lt_two_pow_self).le
  have hinput : C.inp.drop a.ip = natWord n ++
      (natWord V.randomBits ++ (fields V).flatMap natWord) := by
    simpa only [requestWord_eq, List.append_assoc] using hin
  obtain ⟨b, nb, eb, hb, rb⟩ := read_into arityReg (by decide) a hc n _ hinput (by omega)
  have htail1 := rb.tail _ hinput
  obtain ⟨d, nd, ed, hd, rd⟩ := read_into randomReg (by decide) b
    (rb.constants hc (by decide)) V.randomBits _ htail1 (by omega)
  have htail2 := rd.tail _ htail1
  obtain ⟨f, nf, ef, hf, hrows, hfields, hsh, hfc, hfr⟩ := count_program (C := C) d
    (rd.constants (rb.constants hc (by decide)) (by decide)) V.randomBits rd.value
    (by omega) (by simpa only [fields_length] using hfit)
  have hob := rb.other
  have hod := rd.other
  simp only [Prod.mk.injEq] at hob hod
  simp only [DS.sh, Prod.mk.injEq] at hsh
  have hfrc : f.rc sN = (f.ram sN).length := by
    rw [hsh.2.2.2.1, hsh.2.2.1, hod.2.2.1, hod.2.1, hob.2.2.1, hob.2.1]
    exact hrc
  obtain ⟨g, ng, eg, hg, lg, hgc, fg⟩ := readF_spec (C := C) fieldsReg (by decide) f hfc
    (fields V) [] (inputSize V)
    (by rw [hsh.1, List.append_nil]; exact htail2)
    (by rw [fields_length]; exact hfields)
    (fun x hx => field_bits_le V hx) hW hfit hfrc
  refine ⟨g, _, Ex.seq eb (Ex.seq ed (Ex.seq ef eg)), ?_, ?_⟩
  · have hmul := Nat.mul_le_mul_right (30 * inputSize V + 36) hfcount
    nlinarith
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [fg arityReg (by decide), hfr arityReg (by decide), rd.vars arityReg (by decide)]
      exact rb.value
    · rw [fg randomReg (by decide), hfr randomReg (by decide)]
      exact rd.value
    · rw [fg rowsReg (by decide)]
      exact hrows
    · rw [fg fieldsReg (by decide), fields_length]
      exact hfields
    · rw [lg.1, hsh.2.2.1, hod.2.1, hob.2.1]
    · rw [lg.2.1, hsh.2.2.2.1, hsh.2.2.1, hod.2.2.1, hod.2.1, hob.2.2.1, hob.2.1]
    · rw [lg.2.2.1, hsh.1, rd.cursor, rb.cursor, requestWord_eq]
      simp only [List.length_append]
      omega
    · rw [lg.2.2.2.1, lg.2.2.2.2.1, lg.2.2.2.2.2.1, lg.2.2.2.2.2.2,
        hsh.2.1, hsh.2.2.2.2.1, hsh.2.2.2.2.2.1, hsh.2.2.2.2.2.2,
        hod.1, hod.2.2.2.1, hod.2.2.2.2.1, hod.2.2.2.2.2,
        hob.1, hob.2.2.2.1, hob.2.2.2.2.1, hob.2.2.2.2.2]
    · exact Fr.trans (rb.vars.weaken (by decide))
        (Fr.trans (rd.vars.weaken (by decide))
          (Fr.trans (hfr.weaken (by decide)) (fg.weaken (by decide))))

end NearCubicGates.Adapters.Proximity.Trim
