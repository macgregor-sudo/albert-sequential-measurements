/- SPDX-License-Identifier: Apache-2.0 -/
module
public import ReflectedRobustRecipes

/-! Kernel-checked reflected Gram decomposition entries 0 through 80. -/

set_option autoImplicit false
set_option maxRecDepth 100000
@[expose] public section
namespace AlbertSequential.FiveTest
open LengthSeven LengthSeven.Robust

def reflectedGram0 : ℚ × Entry :=
  reflectedGramEntry (4 : ℚ) [1, 2, 3, 0] [1, 2, 3, 0]
    reflectedRecipe0

theorem reflectedGram0_check : reflectedEntryCheck reflectedGram0.2 = true := by decide +kernel

def reflectedGram1 : ℚ × Entry :=
  reflectedGramEntry (-4 : ℚ) [1, 2, 3, 0] [1, 3, 2, 0]
    reflectedRecipe21

theorem reflectedGram1_check : reflectedEntryCheck reflectedGram1.2 = true := by decide +kernel

def reflectedGram2 : ℚ × Entry :=
  reflectedGramEntry (-6 : ℚ) [1, 2, 3, 0] [2, 1, 3, 0]
    reflectedRecipe27

theorem reflectedGram2_check : reflectedEntryCheck reflectedGram2.2 = true := by decide +kernel

def reflectedGram3 : ℚ × Entry :=
  reflectedGramEntry (4 : ℚ) [1, 2, 3, 0] [2, 3, 1, 0]
    reflectedRecipe36

theorem reflectedGram3_check : reflectedEntryCheck reflectedGram3.2 = true := by decide +kernel

def reflectedGram4 : ℚ × Entry :=
  reflectedGramEntry (6 : ℚ) [1, 2, 3, 0] [3, 1, 2, 0]
    reflectedRecipe38

theorem reflectedGram4_check : reflectedEntryCheck reflectedGram4.2 = true := by decide +kernel

def reflectedGram5 : ℚ × Entry :=
  reflectedGramEntry (-4 : ℚ) [1, 2, 3, 0] [3, 2, 1, 0]
    reflectedRecipe39

theorem reflectedGram5_check : reflectedEntryCheck reflectedGram5.2 = true := by decide +kernel

def reflectedGram6 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [1, 2, 3, 0] [1, 2, 3, 1]
    reflectedRecipe40

theorem reflectedGram6_check : reflectedEntryCheck reflectedGram6.2 = true := by decide +kernel

def reflectedGram7 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [1, 2, 3, 0] [1, 3, 2, 1]
    reflectedRecipe54

theorem reflectedGram7_check : reflectedEntryCheck reflectedGram7.2 = true := by decide +kernel

def reflectedGram8 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [1, 2, 3, 0] [2, 1, 3, 2]
    reflectedRecipe63

theorem reflectedGram8_check : reflectedEntryCheck reflectedGram8.2 = true := by decide +kernel

def reflectedGram9 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [1, 2, 3, 0] [2, 3, 1, 2]
    reflectedRecipe83

theorem reflectedGram9_check : reflectedEntryCheck reflectedGram9.2 = true := by decide +kernel

def reflectedGram10 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [1, 2, 3, 0] [3, 1, 2, 3]
    reflectedRecipe86

theorem reflectedGram10_check : reflectedEntryCheck reflectedGram10.2 = true := by decide +kernel

def reflectedGram11 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [1, 2, 3, 0] [3, 2, 1, 3]
    reflectedRecipe96

theorem reflectedGram11_check : reflectedEntryCheck reflectedGram11.2 = true := by decide +kernel

def reflectedGram12 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [1, 2, 3, 0] [1, 2, 3]
    reflectedRecipe0

theorem reflectedGram12_check : reflectedEntryCheck reflectedGram12.2 = true := by decide +kernel

def reflectedGram13 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [1, 2, 3, 0] [1, 3, 2]
    reflectedRecipe21

theorem reflectedGram13_check : reflectedEntryCheck reflectedGram13.2 = true := by decide +kernel

def reflectedGram14 : ℚ × Entry :=
  reflectedGramEntry (14 : ℚ) [1, 2, 3, 0] [2, 1, 3]
    reflectedRecipe27

theorem reflectedGram14_check : reflectedEntryCheck reflectedGram14.2 = true := by decide +kernel

def reflectedGram15 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [1, 2, 3, 0] [2, 3, 1]
    reflectedRecipe36

theorem reflectedGram15_check : reflectedEntryCheck reflectedGram15.2 = true := by decide +kernel

def reflectedGram16 : ℚ × Entry :=
  reflectedGramEntry (-14 : ℚ) [1, 2, 3, 0] [3, 1, 2]
    reflectedRecipe38

theorem reflectedGram16_check : reflectedEntryCheck reflectedGram16.2 = true := by decide +kernel

def reflectedGram17 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [1, 2, 3, 0] [3, 2, 1]
    reflectedRecipe39

theorem reflectedGram17_check : reflectedEntryCheck reflectedGram17.2 = true := by decide +kernel

def reflectedGram18 : ℚ × Entry :=
  reflectedGramEntry (-20/9 : ℚ) [1, 2, 3, 0] [2, 3]
    reflectedRecipe100

theorem reflectedGram18_check : reflectedEntryCheck reflectedGram18.2 = true := by decide +kernel

def reflectedGram19 : ℚ × Entry :=
  reflectedGramEntry (1 : ℚ) [1, 2, 3, 0] [2, 1]
    reflectedRecipe111

theorem reflectedGram19_check : reflectedEntryCheck reflectedGram19.2 = true := by decide +kernel

def reflectedGram20 : ℚ × Entry :=
  reflectedGramEntry (20/9 : ℚ) [1, 2, 3, 0] [3, 2]
    reflectedRecipe122

theorem reflectedGram20_check : reflectedEntryCheck reflectedGram20.2 = true := by decide +kernel

def reflectedGram21 : ℚ × Entry :=
  reflectedGramEntry (-1 : ℚ) [1, 2, 3, 0] [3, 1]
    reflectedRecipe133

theorem reflectedGram21_check : reflectedEntryCheck reflectedGram21.2 = true := by decide +kernel

def reflectedGram22 : ℚ × Entry :=
  reflectedGramEntry (-4 : ℚ) [1, 3, 2, 0] [1, 2, 3, 0]
    reflectedRecipe135

theorem reflectedGram22_check : reflectedEntryCheck reflectedGram22.2 = true := by decide +kernel

def reflectedGram23 : ℚ × Entry :=
  reflectedGramEntry (4 : ℚ) [1, 3, 2, 0] [1, 3, 2, 0]
    reflectedRecipe136

theorem reflectedGram23_check : reflectedEntryCheck reflectedGram23.2 = true := by decide +kernel

def reflectedGram24 : ℚ × Entry :=
  reflectedGramEntry (6 : ℚ) [1, 3, 2, 0] [2, 1, 3, 0]
    reflectedRecipe149

theorem reflectedGram24_check : reflectedEntryCheck reflectedGram24.2 = true := by decide +kernel

def reflectedGram25 : ℚ × Entry :=
  reflectedGramEntry (-4 : ℚ) [1, 3, 2, 0] [2, 3, 1, 0]
    reflectedRecipe151

theorem reflectedGram25_check : reflectedEntryCheck reflectedGram25.2 = true := by decide +kernel

def reflectedGram26 : ℚ × Entry :=
  reflectedGramEntry (-6 : ℚ) [1, 3, 2, 0] [3, 1, 2, 0]
    reflectedRecipe142

theorem reflectedGram26_check : reflectedEntryCheck reflectedGram26.2 = true := by decide +kernel

def reflectedGram27 : ℚ × Entry :=
  reflectedGramEntry (4 : ℚ) [1, 3, 2, 0] [3, 2, 1, 0]
    reflectedRecipe152

theorem reflectedGram27_check : reflectedEntryCheck reflectedGram27.2 = true := by decide +kernel

def reflectedGram28 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [1, 3, 2, 0] [1, 2, 3, 1]
    reflectedRecipe162

theorem reflectedGram28_check : reflectedEntryCheck reflectedGram28.2 = true := by decide +kernel

def reflectedGram29 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [1, 3, 2, 0] [1, 3, 2, 1]
    reflectedRecipe163

theorem reflectedGram29_check : reflectedEntryCheck reflectedGram29.2 = true := by decide +kernel

def reflectedGram30 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [1, 3, 2, 0] [2, 1, 3, 2]
    reflectedRecipe166

theorem reflectedGram30_check : reflectedEntryCheck reflectedGram30.2 = true := by decide +kernel

def reflectedGram31 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [1, 3, 2, 0] [2, 3, 1, 2]
    reflectedRecipe168

theorem reflectedGram31_check : reflectedEntryCheck reflectedGram31.2 = true := by decide +kernel

def reflectedGram32 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [1, 3, 2, 0] [3, 1, 2, 3]
    reflectedRecipe176

theorem reflectedGram32_check : reflectedEntryCheck reflectedGram32.2 = true := by decide +kernel

def reflectedGram33 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [1, 3, 2, 0] [3, 2, 1, 3]
    reflectedRecipe184

theorem reflectedGram33_check : reflectedEntryCheck reflectedGram33.2 = true := by decide +kernel

def reflectedGram34 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [1, 3, 2, 0] [1, 2, 3]
    reflectedRecipe135

theorem reflectedGram34_check : reflectedEntryCheck reflectedGram34.2 = true := by decide +kernel

def reflectedGram35 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [1, 3, 2, 0] [1, 3, 2]
    reflectedRecipe136

theorem reflectedGram35_check : reflectedEntryCheck reflectedGram35.2 = true := by decide +kernel

def reflectedGram36 : ℚ × Entry :=
  reflectedGramEntry (-14 : ℚ) [1, 3, 2, 0] [2, 1, 3]
    reflectedRecipe149

theorem reflectedGram36_check : reflectedEntryCheck reflectedGram36.2 = true := by decide +kernel

def reflectedGram37 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [1, 3, 2, 0] [2, 3, 1]
    reflectedRecipe151

theorem reflectedGram37_check : reflectedEntryCheck reflectedGram37.2 = true := by decide +kernel

def reflectedGram38 : ℚ × Entry :=
  reflectedGramEntry (14 : ℚ) [1, 3, 2, 0] [3, 1, 2]
    reflectedRecipe142

theorem reflectedGram38_check : reflectedEntryCheck reflectedGram38.2 = true := by decide +kernel

def reflectedGram39 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [1, 3, 2, 0] [3, 2, 1]
    reflectedRecipe152

theorem reflectedGram39_check : reflectedEntryCheck reflectedGram39.2 = true := by decide +kernel

def reflectedGram40 : ℚ × Entry :=
  reflectedGramEntry (20/9 : ℚ) [1, 3, 2, 0] [2, 3]
    reflectedRecipe192

theorem reflectedGram40_check : reflectedEntryCheck reflectedGram40.2 = true := by decide +kernel

def reflectedGram41 : ℚ × Entry :=
  reflectedGramEntry (-1 : ℚ) [1, 3, 2, 0] [2, 1]
    reflectedRecipe195

theorem reflectedGram41_check : reflectedEntryCheck reflectedGram41.2 = true := by decide +kernel

def reflectedGram42 : ℚ × Entry :=
  reflectedGramEntry (-20/9 : ℚ) [1, 3, 2, 0] [3, 2]
    reflectedRecipe196

theorem reflectedGram42_check : reflectedEntryCheck reflectedGram42.2 = true := by decide +kernel

def reflectedGram43 : ℚ × Entry :=
  reflectedGramEntry (1 : ℚ) [1, 3, 2, 0] [3, 1]
    reflectedRecipe200

theorem reflectedGram43_check : reflectedEntryCheck reflectedGram43.2 = true := by decide +kernel

def reflectedGram44 : ℚ × Entry :=
  reflectedGramEntry (-6 : ℚ) [2, 1, 3, 0] [1, 2, 3, 0]
    reflectedRecipe201

theorem reflectedGram44_check : reflectedEntryCheck reflectedGram44.2 = true := by decide +kernel

def reflectedGram45 : ℚ × Entry :=
  reflectedGramEntry (6 : ℚ) [2, 1, 3, 0] [1, 3, 2, 0]
    reflectedRecipe210

theorem reflectedGram45_check : reflectedEntryCheck reflectedGram45.2 = true := by decide +kernel

def reflectedGram46 : ℚ × Entry :=
  reflectedGramEntry (9 : ℚ) [2, 1, 3, 0] [2, 1, 3, 0]
    reflectedRecipe211

theorem reflectedGram46_check : reflectedEntryCheck reflectedGram46.2 = true := by decide +kernel

def reflectedGram47 : ℚ × Entry :=
  reflectedGramEntry (-6 : ℚ) [2, 1, 3, 0] [2, 3, 1, 0]
    reflectedRecipe204

theorem reflectedGram47_check : reflectedEntryCheck reflectedGram47.2 = true := by decide +kernel

def reflectedGram48 : ℚ × Entry :=
  reflectedGramEntry (-9 : ℚ) [2, 1, 3, 0] [3, 1, 2, 0]
    reflectedRecipe213

theorem reflectedGram48_check : reflectedEntryCheck reflectedGram48.2 = true := by decide +kernel

def reflectedGram49 : ℚ × Entry :=
  reflectedGramEntry (6 : ℚ) [2, 1, 3, 0] [3, 2, 1, 0]
    reflectedRecipe214

theorem reflectedGram49_check : reflectedEntryCheck reflectedGram49.2 = true := by decide +kernel

def reflectedGram50 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [2, 1, 3, 0] [1, 2, 3, 1]
    reflectedRecipe215

theorem reflectedGram50_check : reflectedEntryCheck reflectedGram50.2 = true := by decide +kernel

def reflectedGram51 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [2, 1, 3, 0] [1, 3, 2, 1]
    reflectedRecipe217

theorem reflectedGram51_check : reflectedEntryCheck reflectedGram51.2 = true := by decide +kernel

def reflectedGram52 : ℚ × Entry :=
  reflectedGramEntry (18 : ℚ) [2, 1, 3, 0] [2, 1, 3, 2]
    reflectedRecipe218

theorem reflectedGram52_check : reflectedEntryCheck reflectedGram52.2 = true := by decide +kernel

def reflectedGram53 : ℚ × Entry :=
  reflectedGramEntry (-18 : ℚ) [2, 1, 3, 0] [2, 3, 1, 2]
    reflectedRecipe224

theorem reflectedGram53_check : reflectedEntryCheck reflectedGram53.2 = true := by decide +kernel

def reflectedGram54 : ℚ × Entry :=
  reflectedGramEntry (-18 : ℚ) [2, 1, 3, 0] [3, 1, 2, 3]
    reflectedRecipe233

theorem reflectedGram54_check : reflectedEntryCheck reflectedGram54.2 = true := by decide +kernel

def reflectedGram55 : ℚ × Entry :=
  reflectedGramEntry (18 : ℚ) [2, 1, 3, 0] [3, 2, 1, 3]
    reflectedRecipe237

theorem reflectedGram55_check : reflectedEntryCheck reflectedGram55.2 = true := by decide +kernel

def reflectedGram56 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [2, 1, 3, 0] [1, 2, 3]
    reflectedRecipe201

theorem reflectedGram56_check : reflectedEntryCheck reflectedGram56.2 = true := by decide +kernel

def reflectedGram57 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [2, 1, 3, 0] [1, 3, 2]
    reflectedRecipe210

theorem reflectedGram57_check : reflectedEntryCheck reflectedGram57.2 = true := by decide +kernel

def reflectedGram58 : ℚ × Entry :=
  reflectedGramEntry (-21 : ℚ) [2, 1, 3, 0] [2, 1, 3]
    reflectedRecipe211

theorem reflectedGram58_check : reflectedEntryCheck reflectedGram58.2 = true := by decide +kernel

def reflectedGram59 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [2, 1, 3, 0] [2, 3, 1]
    reflectedRecipe204

theorem reflectedGram59_check : reflectedEntryCheck reflectedGram59.2 = true := by decide +kernel

def reflectedGram60 : ℚ × Entry :=
  reflectedGramEntry (21 : ℚ) [2, 1, 3, 0] [3, 1, 2]
    reflectedRecipe213

theorem reflectedGram60_check : reflectedEntryCheck reflectedGram60.2 = true := by decide +kernel

def reflectedGram61 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [2, 1, 3, 0] [3, 2, 1]
    reflectedRecipe214

theorem reflectedGram61_check : reflectedEntryCheck reflectedGram61.2 = true := by decide +kernel

def reflectedGram62 : ℚ × Entry :=
  reflectedGramEntry (10/3 : ℚ) [2, 1, 3, 0] [2, 3]
    reflectedRecipe238

theorem reflectedGram62_check : reflectedEntryCheck reflectedGram62.2 = true := by decide +kernel

def reflectedGram63 : ℚ × Entry :=
  reflectedGramEntry (-3/2 : ℚ) [2, 1, 3, 0] [2, 1]
    reflectedRecipe60

theorem reflectedGram63_check : reflectedEntryCheck reflectedGram63.2 = true := by decide +kernel

def reflectedGram64 : ℚ × Entry :=
  reflectedGramEntry (-10/3 : ℚ) [2, 1, 3, 0] [3, 2]
    reflectedRecipe241

theorem reflectedGram64_check : reflectedEntryCheck reflectedGram64.2 = true := by decide +kernel

def reflectedGram65 : ℚ × Entry :=
  reflectedGramEntry (3/2 : ℚ) [2, 1, 3, 0] [3, 1]
    reflectedRecipe242

theorem reflectedGram65_check : reflectedEntryCheck reflectedGram65.2 = true := by decide +kernel

def reflectedGram66 : ℚ × Entry :=
  reflectedGramEntry (4 : ℚ) [2, 3, 1, 0] [1, 2, 3, 0]
    reflectedRecipe250

theorem reflectedGram66_check : reflectedEntryCheck reflectedGram66.2 = true := by decide +kernel

def reflectedGram67 : ℚ × Entry :=
  reflectedGramEntry (-4 : ℚ) [2, 3, 1, 0] [1, 3, 2, 0]
    reflectedRecipe252

theorem reflectedGram67_check : reflectedEntryCheck reflectedGram67.2 = true := by decide +kernel

def reflectedGram68 : ℚ × Entry :=
  reflectedGramEntry (-6 : ℚ) [2, 3, 1, 0] [2, 1, 3, 0]
    reflectedRecipe253

theorem reflectedGram68_check : reflectedEntryCheck reflectedGram68.2 = true := by decide +kernel

def reflectedGram69 : ℚ × Entry :=
  reflectedGramEntry (4 : ℚ) [2, 3, 1, 0] [2, 3, 1, 0]
    reflectedRecipe251

theorem reflectedGram69_check : reflectedEntryCheck reflectedGram69.2 = true := by decide +kernel

def reflectedGram70 : ℚ × Entry :=
  reflectedGramEntry (6 : ℚ) [2, 3, 1, 0] [3, 1, 2, 0]
    reflectedRecipe254

theorem reflectedGram70_check : reflectedEntryCheck reflectedGram70.2 = true := by decide +kernel

def reflectedGram71 : ℚ × Entry :=
  reflectedGramEntry (-4 : ℚ) [2, 3, 1, 0] [3, 2, 1, 0]
    reflectedRecipe243

theorem reflectedGram71_check : reflectedEntryCheck reflectedGram71.2 = true := by decide +kernel

def reflectedGram72 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [2, 3, 1, 0] [1, 2, 3, 1]
    reflectedRecipe155

theorem reflectedGram72_check : reflectedEntryCheck reflectedGram72.2 = true := by decide +kernel

def reflectedGram73 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [2, 3, 1, 0] [1, 3, 2, 1]
    reflectedRecipe255

theorem reflectedGram73_check : reflectedEntryCheck reflectedGram73.2 = true := by decide +kernel

def reflectedGram74 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [2, 3, 1, 0] [2, 1, 3, 2]
    reflectedRecipe262

theorem reflectedGram74_check : reflectedEntryCheck reflectedGram74.2 = true := by decide +kernel

def reflectedGram75 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [2, 3, 1, 0] [2, 3, 1, 2]
    reflectedRecipe167

theorem reflectedGram75_check : reflectedEntryCheck reflectedGram75.2 = true := by decide +kernel

def reflectedGram76 : ℚ × Entry :=
  reflectedGramEntry (12 : ℚ) [2, 3, 1, 0] [3, 1, 2, 3]
    reflectedRecipe263

theorem reflectedGram76_check : reflectedEntryCheck reflectedGram76.2 = true := by decide +kernel

def reflectedGram77 : ℚ × Entry :=
  reflectedGramEntry (-12 : ℚ) [2, 3, 1, 0] [3, 2, 1, 3]
    reflectedRecipe183

theorem reflectedGram77_check : reflectedEntryCheck reflectedGram77.2 = true := by decide +kernel

def reflectedGram78 : ℚ × Entry :=
  reflectedGramEntry (-8 : ℚ) [2, 3, 1, 0] [1, 2, 3]
    reflectedRecipe250

theorem reflectedGram78_check : reflectedEntryCheck reflectedGram78.2 = true := by decide +kernel

def reflectedGram79 : ℚ × Entry :=
  reflectedGramEntry (8 : ℚ) [2, 3, 1, 0] [1, 3, 2]
    reflectedRecipe252

theorem reflectedGram79_check : reflectedEntryCheck reflectedGram79.2 = true := by decide +kernel

def reflectedGram80 : ℚ × Entry :=
  reflectedGramEntry (14 : ℚ) [2, 3, 1, 0] [2, 1, 3]
    reflectedRecipe253

theorem reflectedGram80_check : reflectedEntryCheck reflectedGram80.2 = true := by decide +kernel

def reflectedGramBlock1 : List (ℚ × Entry) :=
  [reflectedGram0,
  reflectedGram1,
  reflectedGram2,
  reflectedGram3,
  reflectedGram4,
  reflectedGram5,
  reflectedGram6,
  reflectedGram7,
  reflectedGram8,
  reflectedGram9,
  reflectedGram10,
  reflectedGram11,
  reflectedGram12,
  reflectedGram13,
  reflectedGram14,
  reflectedGram15,
  reflectedGram16,
  reflectedGram17,
  reflectedGram18,
  reflectedGram19,
  reflectedGram20,
  reflectedGram21,
  reflectedGram22,
  reflectedGram23,
  reflectedGram24,
  reflectedGram25,
  reflectedGram26,
  reflectedGram27,
  reflectedGram28,
  reflectedGram29,
  reflectedGram30,
  reflectedGram31,
  reflectedGram32,
  reflectedGram33,
  reflectedGram34,
  reflectedGram35,
  reflectedGram36,
  reflectedGram37,
  reflectedGram38,
  reflectedGram39,
  reflectedGram40,
  reflectedGram41,
  reflectedGram42,
  reflectedGram43,
  reflectedGram44,
  reflectedGram45,
  reflectedGram46,
  reflectedGram47,
  reflectedGram48,
  reflectedGram49,
  reflectedGram50,
  reflectedGram51,
  reflectedGram52,
  reflectedGram53,
  reflectedGram54,
  reflectedGram55,
  reflectedGram56,
  reflectedGram57,
  reflectedGram58,
  reflectedGram59,
  reflectedGram60,
  reflectedGram61,
  reflectedGram62,
  reflectedGram63,
  reflectedGram64,
  reflectedGram65,
  reflectedGram66,
  reflectedGram67,
  reflectedGram68,
  reflectedGram69,
  reflectedGram70,
  reflectedGram71,
  reflectedGram72,
  reflectedGram73,
  reflectedGram74,
  reflectedGram75,
  reflectedGram76,
  reflectedGram77,
  reflectedGram78,
  reflectedGram79,
  reflectedGram80]

theorem reflectedGramBlock1_check :
    reflectedGramBlock1.all (fun p => reflectedEntryCheck p.2) = true := by
  simp only [reflectedGramBlock1, List.all_cons, List.all_nil, Bool.and_true,
    reflectedGram0_check,
    reflectedGram1_check,
    reflectedGram2_check,
    reflectedGram3_check,
    reflectedGram4_check,
    reflectedGram5_check,
    reflectedGram6_check,
    reflectedGram7_check,
    reflectedGram8_check,
    reflectedGram9_check,
    reflectedGram10_check,
    reflectedGram11_check,
    reflectedGram12_check,
    reflectedGram13_check,
    reflectedGram14_check,
    reflectedGram15_check,
    reflectedGram16_check,
    reflectedGram17_check,
    reflectedGram18_check,
    reflectedGram19_check,
    reflectedGram20_check,
    reflectedGram21_check,
    reflectedGram22_check,
    reflectedGram23_check,
    reflectedGram24_check,
    reflectedGram25_check,
    reflectedGram26_check,
    reflectedGram27_check,
    reflectedGram28_check,
    reflectedGram29_check,
    reflectedGram30_check,
    reflectedGram31_check,
    reflectedGram32_check,
    reflectedGram33_check,
    reflectedGram34_check,
    reflectedGram35_check,
    reflectedGram36_check,
    reflectedGram37_check,
    reflectedGram38_check,
    reflectedGram39_check,
    reflectedGram40_check,
    reflectedGram41_check,
    reflectedGram42_check,
    reflectedGram43_check,
    reflectedGram44_check,
    reflectedGram45_check,
    reflectedGram46_check,
    reflectedGram47_check,
    reflectedGram48_check,
    reflectedGram49_check,
    reflectedGram50_check,
    reflectedGram51_check,
    reflectedGram52_check,
    reflectedGram53_check,
    reflectedGram54_check,
    reflectedGram55_check,
    reflectedGram56_check,
    reflectedGram57_check,
    reflectedGram58_check,
    reflectedGram59_check,
    reflectedGram60_check,
    reflectedGram61_check,
    reflectedGram62_check,
    reflectedGram63_check,
    reflectedGram64_check,
    reflectedGram65_check,
    reflectedGram66_check,
    reflectedGram67_check,
    reflectedGram68_check,
    reflectedGram69_check,
    reflectedGram70_check,
    reflectedGram71_check,
    reflectedGram72_check,
    reflectedGram73_check,
    reflectedGram74_check,
    reflectedGram75_check,
    reflectedGram76_check,
    reflectedGram77_check,
    reflectedGram78_check,
    reflectedGram79_check,
    reflectedGram80_check]

end AlbertSequential.FiveTest
