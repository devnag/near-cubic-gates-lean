import Proof.Hierarchy.CompetitorRawCell

/-! Exact natural value and reusable zero workspace for the raw count-cell
loader. This is the physical input boundary consumed by the streaming sum. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRawCell
open LocalBitMultitape SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem widen_binary (b w x : ℕ) (hw : b≤w) (hx : x<2^b) :
    binary b x++List.replicate (w-b) false=binary w x := by
  have h := BoundedCounter.binary_of_value (binary b x++List.replicate (w-b) false)
  have hv : value (binary b x++List.replicate (w-b) false)=x := by
    simp [value_append,binary_value b x hx]
  have hl : (binary b x++List.replicate (w-b) false).length=w := by simp; omega
  rw [hv,hl] at h
  exact h.symm

def cfg (q : Fin 4) (source : List Bool) (pos b w : ℕ) (backing : List Bool) : Configuration 5 4 :=
  ⟨q,![pos,0,0,0,0],![source,List.replicate b true,List.replicate w true,backing,
    List.replicate (2*w+1) false]⟩
def capacity (w : ℕ) : Fin 5 → ℕ := ![0,0,0,0,2*w+1]

theorem raw_count_run (pre suffix backing : List Bool) (b w x : ℕ)
    (hw : b≤w) (hx : x<2^b) (hb : backing.length≤2*w+1) :
    ∃ r : ExecutionReceipt 5 4,
      runFrom machine (4*w+3)
        (cfg 0 (pre++binary b x++suffix) pre.length b w backing)=some r ∧
      r.final=cfg 3 (pre++binary b x++suffix) (pre.length+b) b w (frame (binary w x)) ∧
      r.steps=4*w+3 := by
  obtain ⟨base,hr,hf,hs⟩ := cell_run pre (binary b x) suffix backing (w-b) (by simpa [Nat.add_sub_of_le hw] using hb)
  have he : (binary b x).length+(w-b)=w := by simp; omega
  rw [he] at hr hf hs
  obtain ⟨r,hp,hpf,hps,_⟩ := ZeroPadding.run_config machine (capacity w) _ _ base hr
  have hin : ZeroPadding.config (capacity w)
      (scan 0 (pre++binary b x++suffix) pre.length (binary b x).length w 0 0 [] backing)=
      cfg 0 (pre++binary b x++suffix) pre.length b w backing := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,capacity,scan,cfg,
        StablePartition.Workspace.overlay,ZeroPadding.pad]
  rw [hin] at hp
  refine ⟨r,hp,?_,hps.trans hs⟩
  rw [hpf,hf,widen_binary b w x hw hx]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [ZeroPadding.config,reset,cfg]
  · funext i; fin_cases i <;> simp [ZeroPadding.config,capacity,reset,cfg,ZeroPadding.pad]

end NearCubicWires.RepairOrdinary.CompetitorRawCell
