module

public import LemmaB.Conclusion
public import Mathlib.Tactic.NormNum

/-!
# Positive control: the hypotheses of `no_psd_realisation_traces` are satisfiable

At the configuration `M` (all `o = 1/3`, all `R = 1/9`, all `t = 1/27`, so `ω = 1/27`) the trace
relation holds, `𝒜 = 4/19683 > 0`, `D̂ = 4`, and the normalised determinant is `-864`.
So the trace-form theorem is not vacuous.
-/

@[expose] public section

namespace LemmaB

noncomputable def traceM : Traces :=
  { oAB := 1/3, oAC := 1/3, oAD := 1/3, oBC := 1/3, oCD := 1/3, oBD := 1/3,
    RABC := 1/9, RABD := 1/9, RACD := 1/9, RBCD := 1/9, t1 := 1/27, t2 := 1/27, t3 := 1/27 }

theorem traceM_relation : traceM.TraceRelation := by
  norm_num [Traces.TraceRelation, traceM]

theorem traceM_Acal : traceM.Acal = 4 / 19683 := by
  norm_num [Traces.Acal, Traces.ω1, Traces.ω2, Traces.ω3, traceM]

theorem traceM_Dhat : traceM.toParams.Dhat = 4 := by
  rw [Traces.Dhat_toParams _ (by norm_num [traceM]) (by norm_num [traceM]) (by norm_num [traceM]),
    traceM_Acal]
  norm_num [Traces.toParams, Params.m, traceM]

theorem traceM_det :
    (Matrix.of fun x y => Q traceM.toParams ((2 * αv traceM.toParams x)⁻¹ • Xi traceM.toParams x)
        ((2 * αv traceM.toParams y)⁻¹ • Xi traceM.toParams y)).det = -864 := by
  rw [Traces.det_gram_normalised_traces _ traceM_relation (by norm_num [traceM])
    (by norm_num [traceM]) (by norm_num [traceM]) (by norm_num [traceM]) (by norm_num [traceM])
    (by norm_num [traceM]), traceM_Dhat]
  norm_num [traceM]

end LemmaB
