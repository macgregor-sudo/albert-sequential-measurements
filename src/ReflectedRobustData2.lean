/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ReflectedRobustRecipes

/-! Kernel-checked reflected Gram decomposition entries 81 through 161. -/

set_option autoImplicit false
set_option maxRecDepth 100000
@[expose] public section
namespace AlbertSequential.FiveTest
open LengthSeven LengthSeven.Robust

def reflectedGram81 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [2, 3, 1, 0] [2, 3, 1]
    reflectedRecipe251

theorem reflectedGram81_check : reflectedEntryCheck reflectedGram81.2 = true := by decide +kernel

def reflectedGram82 : ℚ × Entry :=
  reflectedGramEntry (-14 : ℚ) [2, 3, 1, 0] [3, 1, 2]
    reflectedRecipe254

theorem reflectedGram82_check : reflectedEntryCheck reflectedGram82.2 = true := by decide +kernel

def reflectedGram83 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [2, 3, 1, 0] [3, 2, 1]
    reflectedRecipe243

theorem reflectedGram83_check : reflectedEntryCheck reflectedGram83.2 = true := by decide +kernel

def reflectedGram84 : ℚ × Entry :=
  reflectedGramEntry (-20/9 : ℚ) [2, 3, 1, 0] [2, 3]
    reflectedRecipe73

theorem reflectedGram84_check : reflectedEntryCheck reflectedGram84.2 = true := by decide +kernel

def reflectedGram85 : ℚ × Entry :=
  reflectedGramEntry (1 : ℚ) [2, 3, 1, 0] [2, 1]
    reflectedRecipe194

theorem reflectedGram85_check : reflectedEntryCheck reflectedGram85.2 = true := by decide +kernel

def reflectedGram86 : ℚ × Entry :=
  reflectedGramEntry (20/9 : ℚ) [2, 3, 1, 0] [3, 2]
    reflectedRecipe264

theorem reflectedGram86_check : reflectedEntryCheck reflectedGram86.2 = true := by decide +kernel

def reflectedGram87 : ℚ × Entry :=
  reflectedGramEntry (-1 : ℚ) [2, 3, 1, 0] [3, 1]
    reflectedRecipe199

theorem reflectedGram87_check : reflectedEntryCheck reflectedGram87.2 = true := by decide +kernel

def reflectedGram88 : ℚ × Entry :=
  reflectedGramEntry (6 : ℚ) [3, 1, 2, 0] [1, 2, 3, 0]
    reflectedRecipe271

theorem reflectedGram88_check : reflectedEntryCheck reflectedGram88.2 = true := by decide +kernel

def reflectedGram89 : ℚ × Entry :=
  reflectedGramEntry (-6 : ℚ) [3, 1, 2, 0] [1, 3, 2, 0]
    reflectedRecipe272

theorem reflectedGram89_check : reflectedEntryCheck reflectedGram89.2 = true := by decide +kernel

def reflectedGram90 : ℚ × Entry :=
  reflectedGramEntry (-9 : ℚ) [3, 1, 2, 0] [2, 1, 3, 0]
    reflectedRecipe274

theorem reflectedGram90_check : reflectedEntryCheck reflectedGram90.2 = true := by decide +kernel

def reflectedGram91 : ℚ × Entry :=
  reflectedGramEntry (6 : ℚ) [3, 1, 2, 0] [2, 3, 1, 0]
    reflectedRecipe275

theorem reflectedGram91_check : reflectedEntryCheck reflectedGram91.2 = true := by decide +kernel

def reflectedGram92 : ℚ × Entry :=
  reflectedGramEntry (9 : ℚ) [3, 1, 2, 0] [3, 1, 2, 0]
    reflectedRecipe273

theorem reflectedGram92_check : reflectedEntryCheck reflectedGram92.2 = true := by decide +kernel

def reflectedGram93 : ℚ × Entry :=
  reflectedGramEntry (-6 : ℚ) [3, 1, 2, 0] [3, 2, 1, 0]
    reflectedRecipe265

theorem reflectedGram93_check : reflectedEntryCheck reflectedGram93.2 = true := by decide +kernel

def reflectedGram94 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [3, 1, 2, 0] [1, 2, 3, 1]
    reflectedRecipe276

theorem reflectedGram94_check : reflectedEntryCheck reflectedGram94.2 = true := by decide +kernel

def reflectedGram95 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [3, 1, 2, 0] [1, 3, 2, 1]
    reflectedRecipe216

theorem reflectedGram95_check : reflectedEntryCheck reflectedGram95.2 = true := by decide +kernel

def reflectedGram96 : ℚ × Entry :=
  reflectedGramEntry (-18 : ℚ) [3, 1, 2, 0] [2, 1, 3, 2]
    reflectedRecipe277

theorem reflectedGram96_check : reflectedEntryCheck reflectedGram96.2 = true := by decide +kernel

def reflectedGram97 : ℚ × Entry :=
  reflectedGramEntry (18 : ℚ) [3, 1, 2, 0] [2, 3, 1, 2]
    reflectedRecipe223

theorem reflectedGram97_check : reflectedEntryCheck reflectedGram97.2 = true := by decide +kernel

def reflectedGram98 : ℚ × Entry :=
  reflectedGramEntry (18 : ℚ) [3, 1, 2, 0] [3, 1, 2, 3]
    reflectedRecipe226

theorem reflectedGram98_check : reflectedEntryCheck reflectedGram98.2 = true := by decide +kernel

def reflectedGram99 : ℚ × Entry :=
  reflectedGramEntry (-18 : ℚ) [3, 1, 2, 0] [3, 2, 1, 3]
    reflectedRecipe278

theorem reflectedGram99_check : reflectedEntryCheck reflectedGram99.2 = true := by decide +kernel

def reflectedGram100 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [3, 1, 2, 0] [1, 2, 3]
    reflectedRecipe271

theorem reflectedGram100_check : reflectedEntryCheck reflectedGram100.2 = true := by decide +kernel

def reflectedGram101 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [3, 1, 2, 0] [1, 3, 2]
    reflectedRecipe272

theorem reflectedGram101_check : reflectedEntryCheck reflectedGram101.2 = true := by decide +kernel

def reflectedGram102 : ℚ × Entry :=
  reflectedGramEntry (21 : ℚ) [3, 1, 2, 0] [2, 1, 3]
    reflectedRecipe274

theorem reflectedGram102_check : reflectedEntryCheck reflectedGram102.2 = true := by decide +kernel

def reflectedGram103 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [3, 1, 2, 0] [2, 3, 1]
    reflectedRecipe275

theorem reflectedGram103_check : reflectedEntryCheck reflectedGram103.2 = true := by decide +kernel

def reflectedGram104 : ℚ × Entry :=
  reflectedGramEntry (-21 : ℚ) [3, 1, 2, 0] [3, 1, 2]
    reflectedRecipe273

theorem reflectedGram104_check : reflectedEntryCheck reflectedGram104.2 = true := by decide +kernel

def reflectedGram105 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [3, 1, 2, 0] [3, 2, 1]
    reflectedRecipe265

theorem reflectedGram105_check : reflectedEntryCheck reflectedGram105.2 = true := by decide +kernel

def reflectedGram106 : ℚ × Entry :=
  reflectedGramEntry (-10/3 : ℚ) [3, 1, 2, 0] [2, 3]
    reflectedRecipe279

theorem reflectedGram106_check : reflectedEntryCheck reflectedGram106.2 = true := by decide +kernel

def reflectedGram107 : ℚ × Entry :=
  reflectedGramEntry (3/2 : ℚ) [3, 1, 2, 0] [2, 1]
    reflectedRecipe280

theorem reflectedGram107_check : reflectedEntryCheck reflectedGram107.2 = true := by decide +kernel

def reflectedGram108 : ℚ × Entry :=
  reflectedGramEntry (10/3 : ℚ) [3, 1, 2, 0] [3, 2]
    reflectedRecipe240

theorem reflectedGram108_check : reflectedEntryCheck reflectedGram108.2 = true := by decide +kernel

def reflectedGram109 : ℚ × Entry :=
  reflectedGramEntry (-3/2 : ℚ) [3, 1, 2, 0] [3, 1]
    reflectedRecipe173

theorem reflectedGram109_check : reflectedEntryCheck reflectedGram109.2 = true := by decide +kernel

def reflectedGram110 : ℚ × Entry :=
  reflectedGramEntry (-4 : ℚ) [3, 2, 1, 0] [1, 2, 3, 0]
    reflectedRecipe288

theorem reflectedGram110_check : reflectedEntryCheck reflectedGram110.2 = true := by decide +kernel

def reflectedGram111 : ℚ × Entry :=
  reflectedGramEntry (4 : ℚ) [3, 2, 1, 0] [1, 3, 2, 0]
    reflectedRecipe290

theorem reflectedGram111_check : reflectedEntryCheck reflectedGram111.2 = true := by decide +kernel

def reflectedGram112 : ℚ × Entry :=
  reflectedGramEntry (6 : ℚ) [3, 2, 1, 0] [2, 1, 3, 0]
    reflectedRecipe292

theorem reflectedGram112_check : reflectedEntryCheck reflectedGram112.2 = true := by decide +kernel

def reflectedGram113 : ℚ × Entry :=
  reflectedGramEntry (-4 : ℚ) [3, 2, 1, 0] [2, 3, 1, 0]
    reflectedRecipe289

theorem reflectedGram113_check : reflectedEntryCheck reflectedGram113.2 = true := by decide +kernel

def reflectedGram114 : ℚ × Entry :=
  reflectedGramEntry (-6 : ℚ) [3, 2, 1, 0] [3, 1, 2, 0]
    reflectedRecipe291

theorem reflectedGram114_check : reflectedEntryCheck reflectedGram114.2 = true := by decide +kernel

def reflectedGram115 : ℚ × Entry :=
  reflectedGramEntry (4 : ℚ) [3, 2, 1, 0] [3, 2, 1, 0]
    reflectedRecipe281

theorem reflectedGram115_check : reflectedEntryCheck reflectedGram115.2 = true := by decide +kernel

def reflectedGram116 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [3, 2, 1, 0] [1, 2, 3, 1]
    reflectedRecipe293

theorem reflectedGram116_check : reflectedEntryCheck reflectedGram116.2 = true := by decide +kernel

def reflectedGram117 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [3, 2, 1, 0] [1, 3, 2, 1]
    reflectedRecipe47

theorem reflectedGram117_check : reflectedEntryCheck reflectedGram117.2 = true := by decide +kernel

def reflectedGram118 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [3, 2, 1, 0] [2, 1, 3, 2]
    reflectedRecipe294

theorem reflectedGram118_check : reflectedEntryCheck reflectedGram118.2 = true := by decide +kernel

def reflectedGram119 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [3, 2, 1, 0] [2, 3, 1, 2]
    reflectedRecipe76

theorem reflectedGram119_check : reflectedEntryCheck reflectedGram119.2 = true := by decide +kernel

def reflectedGram120 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [3, 2, 1, 0] [3, 1, 2, 3]
    reflectedRecipe295

theorem reflectedGram120_check : reflectedEntryCheck reflectedGram120.2 = true := by decide +kernel

def reflectedGram121 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [3, 2, 1, 0] [3, 2, 1, 3]
    reflectedRecipe89

theorem reflectedGram121_check : reflectedEntryCheck reflectedGram121.2 = true := by decide +kernel

def reflectedGram122 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [3, 2, 1, 0] [1, 2, 3]
    reflectedRecipe288

theorem reflectedGram122_check : reflectedEntryCheck reflectedGram122.2 = true := by decide +kernel

def reflectedGram123 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [3, 2, 1, 0] [1, 3, 2]
    reflectedRecipe290

theorem reflectedGram123_check : reflectedEntryCheck reflectedGram123.2 = true := by decide +kernel

def reflectedGram124 : ℚ × Entry :=
  reflectedGramEntry (-14 : ℚ) [3, 2, 1, 0] [2, 1, 3]
    reflectedRecipe292

theorem reflectedGram124_check : reflectedEntryCheck reflectedGram124.2 = true := by decide +kernel

def reflectedGram125 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [3, 2, 1, 0] [2, 3, 1]
    reflectedRecipe289

theorem reflectedGram125_check : reflectedEntryCheck reflectedGram125.2 = true := by decide +kernel

def reflectedGram126 : ℚ × Entry :=
  reflectedGramEntry (14 : ℚ) [3, 2, 1, 0] [3, 1, 2]
    reflectedRecipe291

theorem reflectedGram126_check : reflectedEntryCheck reflectedGram126.2 = true := by decide +kernel

def reflectedGram127 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [3, 2, 1, 0] [3, 2, 1]
    reflectedRecipe281

theorem reflectedGram127_check : reflectedEntryCheck reflectedGram127.2 = true := by decide +kernel

def reflectedGram128 : ℚ × Entry :=
  reflectedGramEntry (20/9 : ℚ) [3, 2, 1, 0] [2, 3]
    reflectedRecipe296

theorem reflectedGram128_check : reflectedEntryCheck reflectedGram128.2 = true := by decide +kernel

def reflectedGram129 : ℚ × Entry :=
  reflectedGramEntry (-1 : ℚ) [3, 2, 1, 0] [2, 1]
    reflectedRecipe104

theorem reflectedGram129_check : reflectedEntryCheck reflectedGram129.2 = true := by decide +kernel

def reflectedGram130 : ℚ × Entry :=
  reflectedGramEntry (-20/9 : ℚ) [3, 2, 1, 0] [3, 2]
    reflectedRecipe114

theorem reflectedGram130_check : reflectedEntryCheck reflectedGram130.2 = true := by decide +kernel

def reflectedGram131 : ℚ × Entry :=
  reflectedGramEntry (1 : ℚ) [3, 2, 1, 0] [3, 1]
    reflectedRecipe125

theorem reflectedGram131_check : reflectedEntryCheck reflectedGram131.2 = true := by decide +kernel

def reflectedGram132 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [1, 2, 3, 1] [1, 2, 3, 0]
    reflectedRecipe40

theorem reflectedGram132_check : reflectedEntryCheck reflectedGram132.2 = true := by decide +kernel

def reflectedGram133 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [1, 2, 3, 1] [1, 3, 2, 0]
    reflectedRecipe162

theorem reflectedGram133_check : reflectedEntryCheck reflectedGram133.2 = true := by decide +kernel

def reflectedGram134 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [1, 2, 3, 1] [2, 1, 3, 0]
    reflectedRecipe215

theorem reflectedGram134_check : reflectedEntryCheck reflectedGram134.2 = true := by decide +kernel

def reflectedGram135 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [1, 2, 3, 1] [2, 3, 1, 0]
    reflectedRecipe155

theorem reflectedGram135_check : reflectedEntryCheck reflectedGram135.2 = true := by decide +kernel

def reflectedGram136 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [1, 2, 3, 1] [3, 1, 2, 0]
    reflectedRecipe276

theorem reflectedGram136_check : reflectedEntryCheck reflectedGram136.2 = true := by decide +kernel

def reflectedGram137 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [1, 2, 3, 1] [3, 2, 1, 0]
    reflectedRecipe293

theorem reflectedGram137_check : reflectedEntryCheck reflectedGram137.2 = true := by decide +kernel

def reflectedGram138 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [1, 2, 3, 1] [1, 2, 3, 1]
    reflectedRecipe297

theorem reflectedGram138_check : reflectedEntryCheck reflectedGram138.2 = true := by decide +kernel

def reflectedGram139 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [1, 2, 3, 1] [1, 3, 2, 1]
    (appendRecipe reflectedRecipe298 (⟨[], [mkD (1) 1 [1, 2, 3, 1] [] 1 [3] (5) 18, mkD (-1) 1 [1, 2, 3, 1] [] 1 [6, 3] (5) 36, mkD (1) 1 [1, 2, 3, 1] [] 1 [2, 3] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram139_check : reflectedEntryCheck reflectedGram139.2 = true := by decide +kernel

def reflectedGram140 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [1, 2, 3, 1] [2, 1, 3, 2]
    (appendRecipe (appendRecipe reflectedRecipe26 reflectedRecipe300) (⟨[], [mkD (1) 1 [1, 2, 3, 1] [] 2 [1] (5) 18, mkD (-1) 1 [1, 2, 3, 1] [] 2 [7, 1] (5) 36, mkD (1) 1 [1, 2, 3, 1] [] 2 [3, 1] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram140_check : reflectedEntryCheck reflectedGram140.2 = true := by decide +kernel

def reflectedGram141 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [1, 2, 3, 1] [2, 3, 1, 2]
    reflectedRecipe299

theorem reflectedGram141_check : reflectedEntryCheck reflectedGram141.2 = true := by decide +kernel

def reflectedGram142 : ℚ × Entry :=
  reflectedGramEntry (24 : ℚ) [1, 2, 3, 1] [3, 1, 2, 3]
    reflectedRecipe301

theorem reflectedGram142_check : reflectedEntryCheck reflectedGram142.2 = true := by decide +kernel

def reflectedGram143 : ℚ × Entry :=
  reflectedGramEntry (-24 : ℚ) [1, 2, 3, 1] [3, 2, 1, 3]
    (appendRecipe (appendRecipe reflectedRecipe302 reflectedRecipe303) (⟨[], [mkD (1) 1 [1, 2, 3, 1] [] 3 [1] (5) 18, mkD (-1) 1 [1, 2, 3, 1] [] 3 [6, 1] (5) 36, mkD (1) 1 [1, 2, 3, 1] [] 3 [2, 1] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram143_check : reflectedEntryCheck reflectedGram143.2 = true := by decide +kernel

def reflectedGram144 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [1, 2, 3, 1] [1, 2, 3]
    reflectedRecipe297

theorem reflectedGram144_check : reflectedEntryCheck reflectedGram144.2 = true := by decide +kernel

def reflectedGram145 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [1, 2, 3, 1] [1, 3, 2]
    reflectedRecipe304

theorem reflectedGram145_check : reflectedEntryCheck reflectedGram145.2 = true := by decide +kernel

def reflectedGram146 : ℚ × Entry :=
  reflectedGramEntry (28 : ℚ) [1, 2, 3, 1] [2, 1, 3]
    reflectedRecipe305

theorem reflectedGram146_check : reflectedEntryCheck reflectedGram146.2 = true := by decide +kernel

def reflectedGram147 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [1, 2, 3, 1] [2, 3, 1]
    reflectedRecipe154

theorem reflectedGram147_check : reflectedEntryCheck reflectedGram147.2 = true := by decide +kernel

def reflectedGram148 : ℚ × Entry :=
  reflectedGramEntry (-28 : ℚ) [1, 2, 3, 1] [3, 1, 2]
    reflectedRecipe306

theorem reflectedGram148_check : reflectedEntryCheck reflectedGram148.2 = true := by decide +kernel

def reflectedGram149 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [1, 2, 3, 1] [3, 2, 1]
    reflectedRecipe307

theorem reflectedGram149_check : reflectedEntryCheck reflectedGram149.2 = true := by decide +kernel

def reflectedGram150 : ℚ × Entry :=
  reflectedGramEntry (-40/9 : ℚ) [1, 2, 3, 1] [2, 3]
    reflectedRecipe154

theorem reflectedGram150_check : reflectedEntryCheck reflectedGram150.2 = true := by decide +kernel

def reflectedGram151 : ℚ × Entry :=
  reflectedGramEntry (2 : ℚ) [1, 2, 3, 1] [2, 1]
    reflectedRecipe55

theorem reflectedGram151_check : reflectedEntryCheck reflectedGram151.2 = true := by decide +kernel

def reflectedGram152 : ℚ × Entry :=
  reflectedGramEntry (40/9 : ℚ) [1, 2, 3, 1] [3, 2]
    reflectedRecipe308

theorem reflectedGram152_check : reflectedEntryCheck reflectedGram152.2 = true := by decide +kernel

def reflectedGram153 : ℚ × Entry :=
  reflectedGramEntry (-2 : ℚ) [1, 2, 3, 1] [3, 1]
    reflectedRecipe309

theorem reflectedGram153_check : reflectedEntryCheck reflectedGram153.2 = true := by decide +kernel

def reflectedGram154 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [1, 3, 2, 1] [1, 2, 3, 0]
    reflectedRecipe54

theorem reflectedGram154_check : reflectedEntryCheck reflectedGram154.2 = true := by decide +kernel

def reflectedGram155 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [1, 3, 2, 1] [1, 3, 2, 0]
    reflectedRecipe163

theorem reflectedGram155_check : reflectedEntryCheck reflectedGram155.2 = true := by decide +kernel

def reflectedGram156 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [1, 3, 2, 1] [2, 1, 3, 0]
    reflectedRecipe217

theorem reflectedGram156_check : reflectedEntryCheck reflectedGram156.2 = true := by decide +kernel

def reflectedGram157 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [1, 3, 2, 1] [2, 3, 1, 0]
    reflectedRecipe255

theorem reflectedGram157_check : reflectedEntryCheck reflectedGram157.2 = true := by decide +kernel

def reflectedGram158 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [1, 3, 2, 1] [3, 1, 2, 0]
    reflectedRecipe216

theorem reflectedGram158_check : reflectedEntryCheck reflectedGram158.2 = true := by decide +kernel

def reflectedGram159 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [1, 3, 2, 1] [3, 2, 1, 0]
    reflectedRecipe47

theorem reflectedGram159_check : reflectedEntryCheck reflectedGram159.2 = true := by decide +kernel

def reflectedGram160 : ℚ × Entry :=
  reflectedGramEntry (-16 : ℚ) [1, 3, 2, 1] [1, 2, 3, 1]
    (appendRecipe reflectedRecipe311 (⟨[], [mkD (1) 1 [1, 3, 2, 1] [] 1 [2] (5) 18, mkD (-1) 1 [1, 3, 2, 1] [] 1 [7, 2] (5) 36, mkD (1) 1 [1, 3, 2, 1] [] 1 [3, 2] (5) 36]⟩ : ReflectedRecipe))

theorem reflectedGram160_check : reflectedEntryCheck reflectedGram160.2 = true := by decide +kernel

def reflectedGram161 : ℚ × Entry :=
  reflectedGramEntry (16 : ℚ) [1, 3, 2, 1] [1, 3, 2, 1]
    reflectedRecipe310

theorem reflectedGram161_check : reflectedEntryCheck reflectedGram161.2 = true := by decide +kernel

def reflectedGramBlock2 : List (ℚ × Entry) :=
  [reflectedGram81,
  reflectedGram82,
  reflectedGram83,
  reflectedGram84,
  reflectedGram85,
  reflectedGram86,
  reflectedGram87,
  reflectedGram88,
  reflectedGram89,
  reflectedGram90,
  reflectedGram91,
  reflectedGram92,
  reflectedGram93,
  reflectedGram94,
  reflectedGram95,
  reflectedGram96,
  reflectedGram97,
  reflectedGram98,
  reflectedGram99,
  reflectedGram100,
  reflectedGram101,
  reflectedGram102,
  reflectedGram103,
  reflectedGram104,
  reflectedGram105,
  reflectedGram106,
  reflectedGram107,
  reflectedGram108,
  reflectedGram109,
  reflectedGram110,
  reflectedGram111,
  reflectedGram112,
  reflectedGram113,
  reflectedGram114,
  reflectedGram115,
  reflectedGram116,
  reflectedGram117,
  reflectedGram118,
  reflectedGram119,
  reflectedGram120,
  reflectedGram121,
  reflectedGram122,
  reflectedGram123,
  reflectedGram124,
  reflectedGram125,
  reflectedGram126,
  reflectedGram127,
  reflectedGram128,
  reflectedGram129,
  reflectedGram130,
  reflectedGram131,
  reflectedGram132,
  reflectedGram133,
  reflectedGram134,
  reflectedGram135,
  reflectedGram136,
  reflectedGram137,
  reflectedGram138,
  reflectedGram139,
  reflectedGram140,
  reflectedGram141,
  reflectedGram142,
  reflectedGram143,
  reflectedGram144,
  reflectedGram145,
  reflectedGram146,
  reflectedGram147,
  reflectedGram148,
  reflectedGram149,
  reflectedGram150,
  reflectedGram151,
  reflectedGram152,
  reflectedGram153,
  reflectedGram154,
  reflectedGram155,
  reflectedGram156,
  reflectedGram157,
  reflectedGram158,
  reflectedGram159,
  reflectedGram160,
  reflectedGram161]

theorem reflectedGramBlock2_check :
    reflectedGramBlock2.all (fun p => reflectedEntryCheck p.2) = true := by
  simp only [reflectedGramBlock2, List.all_cons, List.all_nil, Bool.and_true,
    reflectedGram81_check,
    reflectedGram82_check,
    reflectedGram83_check,
    reflectedGram84_check,
    reflectedGram85_check,
    reflectedGram86_check,
    reflectedGram87_check,
    reflectedGram88_check,
    reflectedGram89_check,
    reflectedGram90_check,
    reflectedGram91_check,
    reflectedGram92_check,
    reflectedGram93_check,
    reflectedGram94_check,
    reflectedGram95_check,
    reflectedGram96_check,
    reflectedGram97_check,
    reflectedGram98_check,
    reflectedGram99_check,
    reflectedGram100_check,
    reflectedGram101_check,
    reflectedGram102_check,
    reflectedGram103_check,
    reflectedGram104_check,
    reflectedGram105_check,
    reflectedGram106_check,
    reflectedGram107_check,
    reflectedGram108_check,
    reflectedGram109_check,
    reflectedGram110_check,
    reflectedGram111_check,
    reflectedGram112_check,
    reflectedGram113_check,
    reflectedGram114_check,
    reflectedGram115_check,
    reflectedGram116_check,
    reflectedGram117_check,
    reflectedGram118_check,
    reflectedGram119_check,
    reflectedGram120_check,
    reflectedGram121_check,
    reflectedGram122_check,
    reflectedGram123_check,
    reflectedGram124_check,
    reflectedGram125_check,
    reflectedGram126_check,
    reflectedGram127_check,
    reflectedGram128_check,
    reflectedGram129_check,
    reflectedGram130_check,
    reflectedGram131_check,
    reflectedGram132_check,
    reflectedGram133_check,
    reflectedGram134_check,
    reflectedGram135_check,
    reflectedGram136_check,
    reflectedGram137_check,
    reflectedGram138_check,
    reflectedGram139_check,
    reflectedGram140_check,
    reflectedGram141_check,
    reflectedGram142_check,
    reflectedGram143_check,
    reflectedGram144_check,
    reflectedGram145_check,
    reflectedGram146_check,
    reflectedGram147_check,
    reflectedGram148_check,
    reflectedGram149_check,
    reflectedGram150_check,
    reflectedGram151_check,
    reflectedGram152_check,
    reflectedGram153_check,
    reflectedGram154_check,
    reflectedGram155_check,
    reflectedGram156_check,
    reflectedGram157_check,
    reflectedGram158_check,
    reflectedGram159_check,
    reflectedGram160_check,
    reflectedGram161_check]

end AlbertSequential.FiveTest
