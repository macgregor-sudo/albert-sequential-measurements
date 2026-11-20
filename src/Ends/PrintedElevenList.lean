/- SPDX-License-Identifier: Apache-2.0 -/
module
public import BlockB.ElevenSupport

/-! Word codes extracted from the deposited tail table by tools/check_eleven_tail_source.py. -/
@[expose] public section
namespace AlbertSequential.Ends.Eleven.Printed
open AlbertSequential.Ends.Eleven
-- BEGIN deposited word codes
def prefix01Codes : List ℕ :=
  [2, 1838, 1856, 1982, 2018, 2144, 2162]
def prefix012Codes : List ℕ :=
  [2, 1838, 1856, 1982, 2018, 2144, 2162, 1340282, 1340300, 1340426, 1340462, 1340588, 1340606, 1353404, 1353422, 1353548, 1353584, 1353710, 1353728, 1445258, 1445276, 1445402, 1445438, 1445564, 1445582, 1471502, 1471520, 1471646, 1471682, 1471808, 1471826, 1563356, 1563374, 1563500, 1563536, 1563662, 1563680, 1576478, 1576496, 1576622, 1576658, 1576784, 1576802]
def tailBCodes : List ℕ :=
  [0, 4, 6, 8, 22, 24, 26, 42, 43, 44, 57, 58, 62, 76, 77, 78, 204, 206, 220, 224, 238, 240, 382, 400, 528, 564, 692, 710, 1758, 1840, 1940, 2022, 2068, 2150, 3120, 3122, 4594, 4598, 6070, 6072]
def tailDCodes : List ℕ :=
  [41, 61, 75, 376, 377, 385, 386, 392, 393, 401, 402, 520, 521, 529, 530, 552, 553, 561, 562, 680, 681, 689, 690, 696, 697, 705, 706, 1776, 1858, 1904, 1986, 2086, 2168, 142122, 142860, 143436, 144174, 148684, 149422, 149998, 150736, 153770, 154508, 156398, 157136, 160332, 161070, 162960, 163698, 166732, 167470, 168046, 168784, 173294, 174032, 174608, 175346]
def farFaceCodes : List ℕ :=
  [18182, 19478, 275276, 281918, 372476, 491870]
-- END deposited word codes

private theorem code_mem_iff (L : List (Word (Fin 4))) (S : List ℕ)
    (h : (L.map code).toFinset = S.toFinset) (w : Word (Fin 4)) :
    w ∈ L ↔ code w ∈ S := by
  have hh : code w ∈ (L.map code).toFinset ↔ code w ∈ S.toFinset := by rw [h]
  simpa [List.mem_map, code_injective.eq_iff] using hh

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem published_codes :
    (prefixes01.map code).toFinset = prefix01Codes.toFinset ∧
    (prefixes012.map code).toFinset = prefix012Codes.toFinset ∧
    (tailsB.map code).toFinset = tailBCodes.toFinset ∧
    (tailsD.map code).toFinset = tailDCodes.toFinset ∧
    (farFace.map code).toFinset = farFaceCodes.toFinset := by decide

/-- Membership in the eleven-step ledger, expressed using the two prefix families,
the two tail families, and the far-face words parsed from the deposited TeX. -/
theorem ledger_mem_iff_deposited (w : Word (Fin 4)) :
    w ∈ BlockB.elevenLedgerWords ↔
      ((∃ u, code u ∈ prefix012Codes ∧ ∃ v, code v ∈ tailBCodes ∧ u ++ v = w) ∨
       (∃ u, code u ∈ prefix01Codes ∧ ∃ v, code v ∈ tailDCodes ∧ u ++ v = w)) ∨
       code w ∈ farFaceCodes := by
  obtain ⟨h1,h2,hB,hD,hF⟩ := published_codes
  rw [BlockB.elevenLedgerWords_eq_elevenBase]
  simp only [elevenBase, elevenList, List.mem_toFinset, List.mem_append, List.mem_flatMap, List.mem_map,
    code_mem_iff _ _ h1, code_mem_iff _ _ h2, code_mem_iff _ _ hB, code_mem_iff _ _ hD,
    code_mem_iff _ _ hF]

end AlbertSequential.Ends.Eleven.Printed
